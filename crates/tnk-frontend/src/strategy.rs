//! The strategy language interpreter (Pillar 2.4) — executes a parsed [`StratExpr`] against a subject term,
//! enumerating the solutions of `srewrite` (fair) / `dsrewrite` (depth-first).
//!
//! The surface [`StratExpr`] (with raw term bubbles) is first **resolved** against the module's grammar +
//! rule table into an [`RStrat`] (patterns parsed to [`Term`]s, rule labels resolved to their sides +
//! condition), then **executed** by a faithful port of Maude's strategic-search **process + task model**
//! ([`Search`]): a `VecDeque` of [`Process`]es, each a `(term, pending-strategy-stack, task)`. One step
//! *decomposes* the top strategy frame into successor processes (a decompose does **no** rewrite — it only
//! schedules); a rule application runs as a resumable [`AppState`] yielding **one** rewrite per step; a
//! process with an empty pending stack is a **solution** routed to its [`task`](Process::task). The fair
//! (`srewrite`) mode appends successors (FIFO, round-robin); `dsrewrite` prepends (LIFO, depth-first). The
//! **task tree** handles sub-searches that feed their solutions back to a continuation — `?:`/`try`/`not`/
//! `test`/`or-else` (branch), `one`, `!` (normalize): each spawns a child task whose sub-processes run **in
//! the same queue** (interleaved with the parent), with a per-task slave count detecting exhaustion (for the
//! branch's failure arm / a normal form). This reproduces Maude's exact solution **order** and per-solution
//! cumulative **rewrite count** (validated against Maude 3.5.1's C++ `StrategyLanguage/`).
//!
//! `matchrew`/`amatchrew` and **conditional-rule rewrite-condition substrategies** run their sub-searches
//! *eagerly within a step* (faithful values + order + reachability; their per-solution count can collapse
//! when interleaved with parallel unequal-depth work — Maude's `SubtermTask`/`rewriteTask` parallel-odometer
//! is the documented residual, `fable-audit.md`). `xmatchrew` and conditional `csd` error clearly at resolve.

use crate::build_term::VarIndex;
use crate::cfparser::compile::CompiledGrammar;
use crate::lex::{Interner, Token};
use crate::load::{LoadedModule, parse_build, parse_condition, term_var_indices};
use crate::surface::ast::{StratExpr, StratSugar, TestKind};
use std::collections::{BTreeSet, HashSet, VecDeque};
use std::rc::Rc;
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::sort::KindId;
use tnk_core::term::{ConditionFragment, Term};
use tnk_core::variant::term_from_dag_slots;

/// One solution of a strategy run: the (reduced) result term + the cumulative rewrite count at its emit.
pub struct StratSolution {
    pub term: DagId,
    pub rewrites: u64,
}

/// A resolved rule (its compiled-trace sides + condition) for strategy application.
#[derive(Clone)]
struct RRule {
    lhs: Term,
    rhs: Term,
    condition: Vec<ConditionFragment>,
    nr_vars: u32,
    var_names: Vec<String>,
}

/// A resolved strategy — recursive children are [`Rc`]'d so the pending stack can share them cheaply and the
/// cycle-pruning seen-set can key on their (stable) pointer identity.
enum RStrat {
    Idle,
    Fail,
    Apply {
        rules: Vec<RRule>,
        top: bool,
        subst: Vec<(String, Term)>,
        substrats: Vec<Rc<RStrat>>,
    },
    One(Rc<RStrat>),
    Seq(Rc<RStrat>, Rc<RStrat>),
    Union(Rc<RStrat>, Rc<RStrat>),
    Star(Rc<RStrat>),
    Plus(Rc<RStrat>),
    Normalize(Rc<RStrat>),
    Branch {
        test: Rc<RStrat>,
        success: Rc<RStrat>,
        failure: Rc<RStrat>,
    },
    Test {
        anywhere: bool,
        extension: bool,
        pattern: Term,
        nr_vars: u32,
        cond: Vec<ConditionFragment>,
    },
    MatchRew {
        anywhere: bool,
        pattern: Term,
        nr_vars: u32,
        cond: Vec<ConditionFragment>,
        by: Vec<(u32, Rc<RStrat>)>,
    },
    Call {
        name: String,
        args: Vec<Term>,
    },
    /// Runtime-only resumable definition enumerator. Each body runs as a child call task while the
    /// enumerator survives in the parent task, reproducing Maude's fair call-process interleaving.
    CallGenerator {
        bodies: Rc<Vec<Rc<RStrat>>>,
        next: usize,
    },
}

#[derive(Clone, PartialEq, Eq)]
struct ProfileKey {
    name: String,
    args: Vec<KindId>,
    subject: KindId,
}

struct DeclProfile {
    key: ProfileKey,
    origins: HashSet<String>,
}

struct RDef {
    key: ProfileKey,
    patterns: Vec<Term>,
    nr_vars: u32,
    body: Rc<RStrat>,
}

#[derive(Default)]
struct StrategyProgram {
    profiles: Vec<DeclProfile>,
    defs: Vec<RDef>,
}

/// The evaluation context: the engine, the compiled strategy-definition program, and the cumulative
/// rewrite count.
struct Cx<'a> {
    eng: &'a mut Engine,
    program: &'a StrategyProgram,
    count: u64,
}

/// A pending continuation: an immutable stack of resolved strategy frames (top = the next to decompose).
type Pending = Option<Rc<Frame>>;
struct Frame {
    strat: Rc<RStrat>,
    rest: Pending,
}

fn push(p: &Pending, s: Rc<RStrat>) -> Pending {
    Some(Rc::new(Frame {
        strat: s,
        rest: p.clone(),
    }))
}

/// Push `ss` so that `ss[0]` ends on top (decomposed first).
fn push_all(mut p: Pending, ss: &[Rc<RStrat>]) -> Pending {
    for s in ss.iter().rev() {
        p = push(&p, s.clone());
    }
    p
}

/// A structural key for a pending stack. Resolved nodes use their stable pointer identity; runtime call
/// generators use the persistent body-vector identity plus cursor because their short-lived node allocation
/// can otherwise reuse an address retained by the seen-set.
fn pending_key(p: &Pending) -> Vec<usize> {
    let mut key = Vec::new();
    let mut current = p.clone();
    while let Some(frame) = current {
        if let RStrat::CallGenerator { bodies, next } = &*frame.strat {
            key.push(0);
            key.push(Rc::as_ptr(bodies) as usize);
            key.push(*next);
        } else {
            key.push(Rc::as_ptr(&frame.strat) as *const () as usize);
        }
        current = frame.rest.clone();
    }
    key
}

/// A scheduled process: a term + its pending strategy stack + the task it belongs to, or — when `app` is set
/// — a resumable rule application yielding one rewrite per step.
struct Process {
    dag: DagId,
    pending: Pending,
    app: Option<AppState>,
    task: usize,
}

/// A resumable rule application: the remaining matches to fire (one per step) + the continuation per result.
struct AppState {
    rest: Pending,
    matches: VecDeque<OneMatch>,
}

struct OneMatch {
    path: Vec<usize>,
    result: DagId,
}

/// A task — a sub-computation whose solutions feed a continuation. `slaves` counts the live processes + live
/// child tasks belonging to it; when it reaches zero the task is **exhausted** (its failure / normal-form
/// action fires). Maude's `StrategicTask` slave-list.
struct TaskState {
    parent: usize,
    slaves: i32,
    alive: bool,
    kind: TaskKind,
}

enum TaskKind {
    /// The top-level task — its solutions are the command's results.
    Root,
    /// One named-strategy definition trial. Every body solution resumes the call's outer continuation in
    /// the parent task; exhaustion has no fallback action.
    Call { rest: Pending },
    /// `E ? success : failure` on `dag` (continuation `rest`): each `E`-solution → `success`; if `E` has none
    /// (exhausted with `!had_success`) → `failure` on `dag`.
    Branch {
        dag: DagId,
        success: Rc<RStrat>,
        failure: Rc<RStrat>,
        rest: Pending,
        had_success: bool,
    },
    /// `one(E)` (continuation `rest`): forward the **first** `E`-solution, then discard the rest.
    One { rest: Pending, taken: bool },
    /// `E !` on `dag` (continuation `rest`): each `E`-solution re-arms `E!`; if `E` has none, `dag` is a
    /// normal form → emit it.
    Normalize {
        dag: DagId,
        normalize: Rc<RStrat>,
        rest: Pending,
        had_success: bool,
    },
}

/// Run `srewrite`/`dsrewrite [in M :] term using strat` in Maude's order with per-solution cumulative counts.
pub fn srewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
    strat: &StratExpr,
    depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), String> {
    let mut vars = VarIndex::new();
    let subj_term = parse_build(term, &lm.grammar, &lm.built, i, &mut vars)?;
    if vars.count() != 0 {
        return Err("srewrite subject must be a ground term".to_string());
    }
    let subj = lm.built.engine.instantiate_bindings(&subj_term, &[]);
    srewrite_dag(lm, i, subj, strat, depth_first)
}

/// Run a strategy over an already-built ground subject. META-INTERPRETER uses this entry point after
/// down-translating its reflected `Term`, avoiding a print-and-reparse round trip.
pub fn srewrite_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    subj: DagId,
    strat: &StratExpr,
    depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), String> {
    let program = compile_strategy_program(lm, i);
    let rstrat = resolve(strat, lm, i)?;
    let mut cx = Cx {
        eng: &mut lm.built.engine,
        program: &program,
        count: 0,
    };
    cx.eng.reset_rewrites();
    let subj = cx.eng.reduce(subj);
    cx.count = cx.eng.rewrites();
    let sols = run_search(&mut cx, subj, rstrat, !depth_first);
    let total = cx.count;
    let out = dedup(
        cx.eng,
        sols.into_iter()
            .map(|(term, rewrites)| StratSolution { term, rewrites })
            .collect(),
    );
    Ok((out, total))
}

/// Render a strategy expression back to source text (the echo). Best-effort.
pub fn print_strategy(e: &StratExpr, i: &Interner) -> String {
    /// Maude's echo precedence (tightest first): atoms/calls/keyword forms (0), postfix
    /// iteration `* + !` (1), `;` (2), `|` (3), `? :` (4). A child prints parenthesized only
    /// when its precedence exceeds what the position admits; an iteration over an atomic child
    /// prints spaced (`r1 *`), over a compound child glued to the parens (`(r1 | r2)!`) —
    /// oracle-probed spellings.
    fn prec(e: &StratExpr) -> u8 {
        match e {
            StratExpr::Star(_) | StratExpr::Plus(_) | StratExpr::Normalize(_) => 1,
            StratExpr::Seq(..) => 2,
            StratExpr::Union(..) => 3,
            StratExpr::Branch { .. } => 4,
            _ => 0,
        }
    }
    fn child(e: &StratExpr, i: &Interner, max: u8) -> String {
        let s = print_strategy(e, i);
        if prec(e) > max { format!("({s})") } else { s }
    }
    fn iteration(a: &StratExpr, i: &Interner, op: &str) -> String {
        if prec(a) == 0 {
            format!("{} {op}", print_strategy(a, i))
        } else {
            format!("({}){op}", print_strategy(a, i))
        }
    }
    // Punctuation-aware token spacing, matching Maude's pattern echo (`f(X:S, Y:S)`, not
    // `f ( X:S , Y:S )`): no space after an opener or before a closer/comma.
    fn join(toks: &[Token], i: &Interner) -> String {
        let mut out = String::new();
        for t in toks {
            let s = i.resolve(t.sym);
            let no_space = out.is_empty()
                || out.ends_with(['(', '[', '{'])
                || matches!(s, ")" | "]" | "}" | ",")
                // application: `f(` glues when the preceding token is word-like (`f(X:S, Y:S)`),
                // while an operator keeps its space (`a + (b + c)`) — Maude's echo spacing.
                || (s == "(" && out.chars().last().is_some_and(|c| c.is_alphanumeric()));
            if !no_space {
                out.push(' ');
            }
            out.push_str(s);
        }
        out
    }
    match e {
        StratExpr::Idle => "idle".into(),
        StratExpr::Fail => "fail".into(),
        StratExpr::All => "all".into(),
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            let mut s = label.clone();
            if !subst.is_empty() {
                let sigma = subst
                    .iter()
                    .map(|(v, t)| format!("{} <- {}", join(v, i), join(t, i)))
                    .collect::<Vec<_>>()
                    .join(", ");
                s.push_str(&format!("[{sigma}]"));
            }
            if !substrats.is_empty() {
                let ss = substrats
                    .iter()
                    .map(|e| print_strategy(e, i))
                    .collect::<Vec<_>>()
                    .join(", ");
                s.push_str(&format!("{{{ss}}}"));
            }
            s
        }
        StratExpr::Top(a) => format!("top({})", print_strategy(a, i)),
        StratExpr::One(a) => format!("one({})", print_strategy(a, i)),
        StratExpr::Seq(a, b) => format!("{} ; {}", child(a, i, 2), child(b, i, 2)),
        StratExpr::Union(a, b) => format!("{} | {}", child(a, i, 3), child(b, i, 3)),
        StratExpr::Star(a) => iteration(a, i, "*"),
        StratExpr::Plus(a) => iteration(a, i, "+"),
        StratExpr::Normalize(a) => iteration(a, i, "!"),
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            format!(
                "{} ? {} : {}",
                child(test, i, 3),
                child(success, i, 3),
                child(failure, i, 3)
            )
        }
        StratExpr::Test {
            kind,
            pattern,
            cond,
        } => {
            let k = match kind {
                TestKind::Match => "match",
                TestKind::XMatch => "xmatch",
                TestKind::AMatch => "amatch",
            };
            let mut s = format!("{k} {}", join(pattern, i));
            if let Some(c) = cond {
                s.push_str(&format!(" such that {}", join(c, i)));
            }
            s
        }
        StratExpr::MatchRew {
            kind,
            pattern,
            cond,
            subs,
        } => {
            let kw = match kind {
                TestKind::Match => "matchrew",
                TestKind::XMatch => "xmatchrew",
                TestKind::AMatch => "amatchrew",
            };
            let by = subs
                .iter()
                .map(|(v, st)| {
                    // A by-clause substrategy binds tighter than the `,` separating clauses:
                    // `;`/`|`/`? :` need parens (oracle: `by X:S using (r1 | r2), …`).
                    let s = print_strategy(st, i);
                    let s = if prec(st) >= 2 { format!("({s})") } else { s };
                    format!("{} using {}", join(v, i), s)
                })
                .collect::<Vec<_>>()
                .join(", ");
            let st = cond
                .as_ref()
                .map(|c| format!(" such that {}", join(c, i)))
                .unwrap_or_default();
            format!("{kw} {}{st} by {by}", join(pattern, i))
        }
        StratExpr::Sugar { kind, args } => {
            let kw = match kind {
                StratSugar::Try => "try",
                StratSugar::NotS => "not",
                StratSugar::TestS => "test",
                StratSugar::OrElse => "or-else",
            };
            let a = args
                .iter()
                .map(|e| print_strategy(e, i))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{kw}({a})")
        }
        StratExpr::Call { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let a = args
                    .iter()
                    .map(|t| join(t, i))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({a})")
            }
        }
    }
}

/// Apply Maude's recoverable `top` rule to the surface tree before echoing/execution: the modifier
/// survives only around a direct rule application (`all` or a rule label). Named strategy calls are
/// deliberately tested before expansion, so `top(call)` is discarded even if the call body applies a rule.
pub fn discard_inapplicable_top(e: &mut StratExpr, lm: &LoadedModule) {
    match e {
        StratExpr::Top(inner) => {
            discard_inapplicable_top(inner, lm);
            let direct_application = match &**inner {
                StratExpr::All => true,
                StratExpr::Apply { label, .. } => !rules_labelled(lm, label).is_empty(),
                _ => false,
            };
            if !direct_application {
                *e = std::mem::replace(&mut **inner, StratExpr::Idle);
            }
        }
        StratExpr::Apply { substrats, .. } => {
            for child in substrats {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => discard_inapplicable_top(child, lm),
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            discard_inapplicable_top(left, lm);
            discard_inapplicable_top(right, lm);
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            discard_inapplicable_top(test, lm);
            discard_inapplicable_top(success, lm);
            discard_inapplicable_top(failure, lm);
        }
        StratExpr::MatchRew { subs, .. } => {
            for (_, child) in subs {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::Sugar { args, .. } => {
            for child in args {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::Idle
        | StratExpr::Fail
        | StratExpr::All
        | StratExpr::Test { .. }
        | StratExpr::Call { .. } => {}
    }
}

/// Resolve a surface [`StratExpr`] into an [`RStrat`] (shared via [`Rc`]). Named calls remain lazy and
/// recursive definitions are opened by the runtime call generator. `xmatchrew`/conditional `csd` error clearly.
fn resolve(e: &StratExpr, lm: &LoadedModule, i: &Interner) -> Result<Rc<RStrat>, String> {
    resolve_in(e, lm, &lm.grammar, i, &VarIndex::new())
}

/// Resolve in a particular source grammar with `seed` variables already bound by an enclosing strategy
/// definition. The grammar determines syntax; all semantic actions already point into `lm.built`.
fn resolve_in(
    e: &StratExpr,
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Rc<RStrat>, String> {
    let r = match e {
        StratExpr::Idle => RStrat::Idle,
        StratExpr::Fail => RStrat::Fail,
        StratExpr::All => RStrat::Apply {
            rules: all_rules(lm),
            top: false,
            subst: Vec::new(),
            substrats: Vec::new(),
        },
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            let rules = rules_labelled(lm, label);
            if !rules.is_empty() {
                let app_subst = resolve_subst(subst, lm, grammar, i, seed)?;
                let subs = substrats
                    .iter()
                    .map(|child| resolve_in(child, lm, grammar, i, seed))
                    .collect::<Result<Vec<_>, _>>()?;
                RStrat::Apply {
                    rules,
                    top: false,
                    subst: app_subst,
                    substrats: subs,
                }
            } else if subst.is_empty() && substrats.is_empty() {
                return resolve_call(label, &[], lm, grammar, i, seed);
            } else {
                return Err(format!(
                    "`{label}` is not a rule label (application `[…]{{…}}` needs a rule)"
                ));
            }
        }
        StratExpr::Top(inner) => {
            let resolved = resolve_in(inner, lm, grammar, i, seed)?;
            // Maude attaches `top` only to a direct rule application. A named strategy call is a
            // distinct surface node: the modifier is ignored before the call body is expanded, even
            // when that body happens to resolve to an application strategy.
            let direct_application = match &**inner {
                StratExpr::All => true,
                StratExpr::Apply { label, .. } => !rules_labelled(lm, label).is_empty(),
                _ => false,
            };
            if !direct_application {
                return Ok(resolved);
            }
            match &*resolved {
                RStrat::Apply {
                    rules,
                    subst,
                    substrats,
                    ..
                } => RStrat::Apply {
                    rules: rules.clone(),
                    top: true,
                    subst: subst.clone(),
                    substrats: substrats.clone(),
                },
                _ => unreachable!("a direct application must resolve to RStrat::Apply"),
            }
        }
        StratExpr::One(inner) => RStrat::One(resolve_in(inner, lm, grammar, i, seed)?),
        StratExpr::Seq(left, right) => RStrat::Seq(
            resolve_in(left, lm, grammar, i, seed)?,
            resolve_in(right, lm, grammar, i, seed)?,
        ),
        StratExpr::Union(left, right) => RStrat::Union(
            resolve_in(left, lm, grammar, i, seed)?,
            resolve_in(right, lm, grammar, i, seed)?,
        ),
        StratExpr::Star(child) => RStrat::Star(resolve_in(child, lm, grammar, i, seed)?),
        StratExpr::Plus(child) => RStrat::Plus(resolve_in(child, lm, grammar, i, seed)?),
        StratExpr::Normalize(child) => RStrat::Normalize(resolve_in(child, lm, grammar, i, seed)?),
        // Surface sugar desugars here (the parser preserves the spelling for the echo).
        StratExpr::Sugar { kind, args } => {
            let branch =
                |test: &StratExpr, success: StratExpr, failure: StratExpr| StratExpr::Branch {
                    test: Box::new(test.clone()),
                    success: Box::new(success),
                    failure: Box::new(failure),
                };
            let desugared = match kind {
                StratSugar::Try | StratSugar::TestS => {
                    branch(&args[0], StratExpr::Idle, StratExpr::Fail)
                }
                StratSugar::NotS => branch(&args[0], StratExpr::Fail, StratExpr::Idle),
                StratSugar::OrElse => branch(&args[0], StratExpr::Idle, args[1].clone()),
            };
            return resolve_in(&desugared, lm, grammar, i, seed);
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => RStrat::Branch {
            test: resolve_in(test, lm, grammar, i, seed)?,
            success: resolve_in(success, lm, grammar, i, seed)?,
            failure: resolve_in(failure, lm, grammar, i, seed)?,
        },
        StratExpr::Test {
            kind,
            pattern,
            cond,
        } => {
            let (anywhere, extension) = match kind {
                TestKind::Match => (false, false),
                TestKind::AMatch => (true, false),
                TestKind::XMatch => (false, true),
            };
            let mut vars = seed.clone();
            let pattern = parse_build(pattern, grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(
                cond.as_deref(),
                &pattern,
                &mut vars,
                lm,
                grammar,
                i,
                seed.count(),
                "test",
            )?;
            RStrat::Test {
                anywhere,
                extension,
                pattern,
                nr_vars: vars.count(),
                cond,
            }
        }
        StratExpr::MatchRew {
            kind,
            pattern,
            cond,
            subs,
        } => {
            let anywhere = match kind {
                TestKind::Match => false,
                TestKind::AMatch => true,
                TestKind::XMatch => {
                    return Err(
                        "xmatchrew (extension-match rewriting) reassembly is an engine follow-on"
                            .to_string(),
                    );
                }
            };
            let mut vars = seed.clone();
            let pattern = parse_build(pattern, grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(
                cond.as_deref(),
                &pattern,
                &mut vars,
                lm,
                grammar,
                i,
                seed.count(),
                "matchrew `such that`",
            )?;
            let mut by = Vec::new();
            for (variable, child) in subs {
                let name = token_text(variable, i);
                let index = (0..vars.count())
                    .find(|&slot| vars.name(slot) == name)
                    .ok_or_else(|| {
                        format!("matchrew variable `{name}` does not occur in the pattern")
                    })?;
                by.push((index, resolve_in(child, lm, grammar, i, seed)?));
            }
            RStrat::MatchRew {
                anywhere,
                pattern,
                nr_vars: vars.count(),
                cond,
                by,
            }
        }
        StratExpr::Call { name, args } => {
            return resolve_call(name, args, lm, grammar, i, seed);
        }
    };
    Ok(Rc::new(r))
}

/// Parse an optional `such that` condition for a test/matchrew, rejecting a rewrite (`=>`) fragment.
#[allow(clippy::too_many_arguments)]
fn resolve_test_cond(
    cond: Option<&[Token]>,
    pattern: &Term,
    vars: &mut VarIndex,
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    bound_prefix: u32,
    owner: &str,
) -> Result<Vec<ConditionFragment>, String> {
    let Some(cond) = cond else {
        return Ok(Vec::new());
    };
    let mut bound: BTreeSet<u32> = (0..bound_prefix).collect();
    let mut pattern_vars = Vec::new();
    term_var_indices(pattern, &mut pattern_vars);
    bound.extend(pattern_vars);
    let fragments = parse_condition(cond, grammar, &lm.built, i, vars, &mut bound)?;
    if fragments
        .iter()
        .any(|fragment| matches!(fragment, ConditionFragment::Rewrite { .. }))
    {
        return Err(format!(
            "a rewrite condition (`=>`) is not allowed in a {owner}"
        ));
    }
    Ok(fragments)
}

/// Resolve an application's initial substitution. Values may reference variables bound by an enclosing
/// strategy definition, but may not introduce new variables.
fn resolve_subst(
    subst: &[(Vec<Token>, Vec<Token>)],
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Vec<(String, Term)>, String> {
    let mut out = Vec::new();
    for (variable, value) in subst {
        let name = token_text(variable, i);
        let mut vars = seed.clone();
        let term = parse_build(value, grammar, &lm.built, i, &mut vars)?;
        if vars.count() != seed.count() {
            return Err(
                "an application substitution value contains an unbound strategy variable"
                    .to_string(),
            );
        }
        out.push((name, term));
    }
    Ok(out)
}

/// Resolve a named call without expanding it. Every definition remains a separately matchable candidate,
/// so recursion is naturally lazy and declaration-only strategies correctly yield no solutions.
fn resolve_call(
    name: &str,
    args: &[Vec<Token>],
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Rc<RStrat>, String> {
    let declared = lm
        .built
        .strat_decls
        .iter()
        .any(|decl| decl.name == name && decl.domain.len() == args.len());
    if !declared {
        return Err(format!(
            "`{name}` is neither a rule label nor a strategy of this module"
        ));
    }
    let has_unconditional = lm
        .built
        .strat_defs
        .iter()
        .any(|def| def.name == name && def.params.len() == args.len() && def.cond.is_none());
    let has_conditional = lm
        .built
        .strat_defs
        .iter()
        .any(|def| def.name == name && def.params.len() == args.len() && def.cond.is_some());
    if has_conditional && !has_unconditional {
        return Err(format!(
            "conditional strategy definition (`csd {name}`) is a follow-on"
        ));
    }
    let mut vars = seed.clone();
    let mut resolved_args = Vec::with_capacity(args.len());
    for arg in args {
        resolved_args.push(parse_build(arg, grammar, &lm.built, i, &mut vars)?);
    }
    if vars.count() != seed.count() {
        return Err(format!(
            "strategy call `{name}` contains an unbound argument variable"
        ));
    }
    Ok(Rc::new(RStrat::Call {
        name: name.to_string(),
        args: resolved_args,
    }))
}

fn compile_strategy_program(lm: &LoadedModule, i: &Interner) -> StrategyProgram {
    let mut program = StrategyProgram::default();
    let mut seen_declarations = HashSet::new();
    for decl in &lm.built.strat_decls {
        if let (Some(origin), Some(source_index)) = (&decl.origin, decl.source_index)
            && !seen_declarations.insert((origin.clone(), source_index))
        {
            continue;
        }
        let Some(args) = decl
            .domain
            .iter()
            .map(|sort| strategy_sort_kind(lm, sort))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let Some(subject) = strategy_sort_kind(lm, &decl.subject) else {
            continue;
        };
        let key = ProfileKey {
            name: decl.name.clone(),
            args,
            subject,
        };
        let origin = decl
            .origin
            .clone()
            .unwrap_or_else(|| format!("{}#local", lm.built.name));
        if let Some(profile) = program
            .profiles
            .iter_mut()
            .find(|profile| profile.key == key)
        {
            profile.origins.insert(origin);
        } else {
            program.profiles.push(DeclProfile {
                key,
                origins: HashSet::from([origin]),
            });
        }
    }

    let mut seen_definitions = HashSet::new();
    for def in &lm.built.strat_defs {
        if def.cond.is_some() {
            continue;
        }
        if let (Some(origin), Some(source_index)) = (&def.origin, def.source_index)
            && !seen_definitions.insert((origin.clone(), source_index))
        {
            continue;
        }
        let Some(grammar) = definition_grammar(lm, def.home.as_deref()) else {
            // A plain donor whose grammar cannot be remapped is not executable; never silently parse its
            // source bubbles in a different grammar.
            continue;
        };
        let mut vars = VarIndex::new();
        let mut patterns = Vec::with_capacity(def.params.len());
        let mut arg_kinds = Vec::with_capacity(def.params.len());
        let mut valid = true;
        for param in &def.params {
            match parse_build(param, grammar, &lm.built, i, &mut vars) {
                Ok(pattern) => {
                    arg_kinds.push(term_kind(&pattern, lm));
                    patterns.push(pattern);
                }
                Err(_) => {
                    valid = false;
                    break;
                }
            }
        }
        if !valid {
            continue;
        }
        let matching_profiles: Vec<ProfileKey> = program
            .profiles
            .iter()
            .filter(|profile| {
                profile.origins.len() == 1
                    && profile.key.name == def.name
                    && profile.key.args == arg_kinds
            })
            .map(|profile| profile.key.clone())
            .collect();
        if matching_profiles.is_empty() {
            continue;
        }
        let Ok(body) = resolve_in(&def.body, lm, grammar, i, &vars) else {
            continue;
        };
        let nr_vars = vars.count();
        for key in matching_profiles {
            program.defs.push(RDef {
                key,
                patterns: patterns.clone(),
                nr_vars,
                body: body.clone(),
            });
        }
    }
    program
}

fn strategy_sort_kind(lm: &LoadedModule, name: &str) -> Option<KindId> {
    lm.built
        .sorts
        .get(name)
        .map(|&sort| lm.built.engine.sorts().kind_of(sort))
}

fn term_kind(term: &Term, lm: &LoadedModule) -> KindId {
    match term {
        Term::Var(variable) => lm.built.engine.sorts().kind_of(variable.sort),
        _ => lm.built.engine.symbol_kind(
            term.top_symbol()
                .expect("non-variable term has a top symbol"),
        ),
    }
}

fn definition_grammar<'a>(lm: &'a LoadedModule, home: Option<&str>) -> Option<&'a CompiledGrammar> {
    match home {
        None => Some(&lm.grammar),
        Some(home) if home == lm.built.name => Some(&lm.grammar),
        Some(home) => lm.strategy_grammars.get(home),
    }
}

/// The concatenated text of a token bubble (a variable `X:S` is one token).
fn token_text(toks: &[Token], i: &Interner) -> String {
    toks.iter().map(|t| i.resolve(t.sym)).collect()
}

/// All rules of the module, as [`RRule`]s (conditional rules included).
fn all_rules(lm: &LoadedModule) -> Vec<RRule> {
    lm.built.rl_traces.iter().map(rrule).collect()
}

/// The rules labelled `label`.
fn rules_labelled(lm: &LoadedModule, label: &str) -> Vec<RRule> {
    lm.built
        .rl_traces
        .iter()
        .filter(|t| t.label.as_deref() == Some(label))
        .map(rrule)
        .collect()
}

fn rrule(t: &crate::sig::syntax::RlTrace) -> RRule {
    RRule {
        lhs: t.lhs.clone(),
        rhs: t.rhs.clone(),
        condition: t.condition.clone(),
        nr_vars: t.var_names.len() as u32,
        var_names: t.var_names.clone(),
    }
}

// ---- the process + task executor ----

/// Run a (sub-)search to exhaustion, returning every solution `(term, cumulative-count-at-emit)` in order.
fn run_search(cx: &mut Cx, dag: DagId, strat: Rc<RStrat>, fifo: bool) -> Vec<(DagId, u64)> {
    let mut s = Search {
        q: VecDeque::new(),
        tasks: vec![TaskState {
            parent: 0,
            slaves: 0,
            alive: true,
            kind: TaskKind::Root,
        }],
        seen: Vec::new(),
        fifo,
        out: Vec::new(),
    };
    s.schedule(vec![Process {
        dag,
        pending: push(&None, strat),
        app: None,
        task: 0,
    }]);
    while let Some(p) = s.q.pop_front() {
        s.run_one(cx, p);
    }
    s.out
}

/// The strategic search state — the process ring (as a `VecDeque`) + the task tree.
struct Search {
    q: VecDeque<Process>,
    tasks: Vec<TaskState>,
    /// Cycle-pruning seen-set: `(term, pending-key, task)`. Per-task (Maude's `alreadySeen`), which also
    /// de-duplicates re-reached solution states.
    seen: Vec<(DagId, Vec<usize>, usize)>,
    fifo: bool,
    out: Vec<(DagId, u64)>,
}

impl Search {
    /// Schedule successors: FIFO (append) for `srewrite`, LIFO (prepend, keeping order) for `dsrewrite`. Each
    /// scheduled process is a new live slave of its task.
    fn schedule(&mut self, succ: Vec<Process>) {
        for s in &succ {
            self.tasks[s.task].slaves += 1;
        }
        if self.fifo {
            for s in succ {
                self.q.push_back(s);
            }
        } else {
            for s in succ.into_iter().rev() {
                self.q.push_front(s);
            }
        }
    }

    /// Register a new child task of `parent` (itself a slave of `parent`), returning its id.
    fn new_task(&mut self, parent: usize, kind: TaskKind) -> usize {
        self.tasks[parent].slaves += 1;
        self.tasks.push(TaskState {
            parent,
            slaves: 0,
            alive: true,
            kind,
        });
        self.tasks.len() - 1
    }

    /// Account for one slave of `task` leaving; on reaching zero, the task is exhausted (its failure /
    /// normal-form action fires, then it leaves its parent's slave list — cascading).
    fn dec_slave(&mut self, task: usize) {
        self.tasks[task].slaves -= 1;
        if self.tasks[task].slaves == 0 && self.tasks[task].alive {
            self.exhaust(task);
        }
    }

    /// A task's sub-search exhausted: run its on-exhaust action, then detach it from its parent.
    fn exhaust(&mut self, task: usize) {
        let parent = self.tasks[task].parent;
        let succ = match &mut self.tasks[task].kind {
            TaskKind::Root | TaskKind::One { .. } | TaskKind::Call { .. } => Vec::new(),
            TaskKind::Branch {
                dag,
                failure,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process {
                        dag: *dag,
                        pending: push(rest, failure.clone()),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::Normalize {
                dag,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process {
                        dag: *dag,
                        pending: rest.clone(),
                        app: None,
                        task: parent,
                    }]
                }
            }
        };
        self.tasks[task].alive = false;
        self.schedule(succ);
        if task != parent {
            self.dec_slave(parent);
        }
    }

    /// Route a solution reached under `task` (a process with empty pending) to the task's continuation.
    fn emit(&mut self, task: usize, dag: DagId, count: u64) {
        let parent = self.tasks[task].parent;
        let succ = match &mut self.tasks[task].kind {
            TaskKind::Root => {
                self.out.push((dag, count));
                return;
            }
            TaskKind::Call { rest } => vec![Process {
                dag,
                pending: rest.clone(),
                app: None,
                task: parent,
            }],
            TaskKind::Branch {
                success,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    *had_success = true;
                    vec![Process {
                        dag,
                        pending: push(rest, success.clone()),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::One { rest, taken } => {
                if *taken {
                    Vec::new()
                } else {
                    *taken = true;
                    vec![Process {
                        dag,
                        pending: rest.clone(),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::Normalize {
                normalize,
                rest,
                had_success,
                ..
            } => {
                *had_success = true;
                vec![Process {
                    dag,
                    pending: push(rest, normalize.clone()),
                    app: None,
                    task: parent,
                }]
            }
        };
        let commit = matches!(
            self.tasks[task].kind,
            TaskKind::One { .. } | TaskKind::Branch { .. }
        );
        self.schedule(succ);
        // `one` and conditional branching commit to the first successful sub-search result.
        if commit {
            self.kill(task);
        }
    }

    /// Kill a task (and detach from its parent) — its still-queued processes are dropped when popped.
    fn kill(&mut self, task: usize) {
        if !self.tasks[task].alive {
            return;
        }
        self.tasks[task].alive = false;
        let parent = self.tasks[task].parent;
        if task != parent {
            self.dec_slave(parent);
        }
    }

    /// Run one process step.
    fn run_one(&mut self, cx: &mut Cx, mut p: Process) {
        let t = p.task;
        if !self.tasks[t].alive {
            // A process of a killed task (e.g. `one` past its first solution) — drop it.
            self.dec_slave(t);
            return;
        }
        // A resumable rule application: fire one match, spawn its result + survive, else die.
        if let Some(mut app) = p.app.take() {
            if let Some(m) = app.matches.pop_front() {
                let whole = replace_at(cx.eng, p.dag, &m.path, m.result);
                cx.eng.reset_rewrites();
                let whole = cx.eng.reduce(whole);
                cx.count += 1 + cx.eng.rewrites();
                let result = Process {
                    dag: whole,
                    pending: app.rest.clone(),
                    app: None,
                    task: t,
                };
                let again = Process {
                    dag: p.dag,
                    pending: None,
                    app: Some(app),
                    task: t,
                };
                self.schedule(vec![result, again]);
            }
            self.dec_slave(t);
            return;
        }
        // A decomposition process: prune on a (term, pending) revisit within this task.
        let key = pending_key(&p.pending);
        if self
            .seen
            .iter()
            .any(|(d, k, tt)| *tt == t && *k == key && cx.eng.deep_equal(*d, p.dag))
        {
            self.dec_slave(t);
            return;
        }
        self.seen.push((p.dag, key, t));
        let Some(frame) = p.pending.clone() else {
            self.emit(t, p.dag, cx.count);
            self.dec_slave(t);
            return;
        };
        let succ = self.decompose(cx, p.dag, &frame.strat, &frame.rest, t);
        self.schedule(succ);
        self.dec_slave(t);
    }

    /// Decompose the top strategy frame into successors (the core combinators) or spawn a child task (the
    /// sub-search combinators: branch / one / normalize). `t` is the running process's task.
    fn decompose(
        &mut self,
        cx: &mut Cx,
        dag: DagId,
        strat: &Rc<RStrat>,
        rest: &Pending,
        t: usize,
    ) -> Vec<Process> {
        match &**strat {
            RStrat::Idle => vec![Process {
                dag,
                pending: rest.clone(),
                app: None,
                task: t,
            }],
            RStrat::Fail => Vec::new(),
            RStrat::Test {
                anywhere,
                extension,
                pattern,
                nr_vars,
                cond,
            } => {
                if test_holds(cx, pattern, *nr_vars, dag, *anywhere, *extension, cond) {
                    vec![Process {
                        dag,
                        pending: rest.clone(),
                        app: None,
                        task: t,
                    }]
                } else {
                    Vec::new()
                }
            }
            RStrat::Seq(..) => {
                let mut frames = Vec::new();
                flatten_seq(strat, &mut frames);
                vec![Process {
                    dag,
                    pending: push_all(rest.clone(), &frames),
                    app: None,
                    task: t,
                }]
            }
            RStrat::Union(..) => {
                let mut alts = Vec::new();
                flatten_union(strat, &mut alts);
                alts.into_iter()
                    .map(|s| Process {
                        dag,
                        pending: push(rest, s),
                        app: None,
                        task: t,
                    })
                    .collect()
            }
            RStrat::Apply {
                rules,
                top,
                subst,
                substrats,
            } => {
                if substrats.is_empty() && rules.iter().all(|r| r.condition.is_empty()) {
                    let matches = precompute_matches(cx, dag, *top, rules, subst);
                    vec![Process {
                        dag,
                        pending: None,
                        app: Some(AppState {
                            rest: rest.clone(),
                            matches,
                        }),
                        task: t,
                    }]
                } else {
                    apply_eager(cx, dag, *top, rules, subst, substrats, self.fifo)
                        .into_iter()
                        .map(|r| Process {
                            dag: r,
                            pending: rest.clone(),
                            app: None,
                            task: t,
                        })
                        .collect()
                }
            }
            RStrat::Star(child) => {
                let zero = Process {
                    dag,
                    pending: rest.clone(),
                    app: None,
                    task: t,
                };
                let more = Process {
                    dag,
                    pending: push(&push(rest, strat.clone()), child.clone()),
                    app: None,
                    task: t,
                };
                vec![zero, more]
            }
            RStrat::Plus(child) => {
                let star = Rc::new(RStrat::Star(child.clone()));
                vec![Process {
                    dag,
                    pending: push(&push(rest, star), child.clone()),
                    app: None,
                    task: t,
                }]
            }
            RStrat::Branch {
                test,
                success,
                failure,
            } => {
                let nt = self.new_task(
                    t,
                    TaskKind::Branch {
                        dag,
                        success: success.clone(),
                        failure: failure.clone(),
                        rest: rest.clone(),
                        had_success: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, test.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::One(child) => {
                let nt = self.new_task(
                    t,
                    TaskKind::One {
                        rest: rest.clone(),
                        taken: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, child.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::Normalize(child) => {
                let nt = self.new_task(
                    t,
                    TaskKind::Normalize {
                        dag,
                        normalize: strat.clone(),
                        rest: rest.clone(),
                        had_success: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, child.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::MatchRew {
                anywhere,
                pattern,
                nr_vars,
                cond,
                by,
            } => matchrew_solutions(cx, dag, *anywhere, pattern, *nr_vars, cond, by, self.fifo)
                .into_iter()
                .map(|r| Process {
                    dag: r,
                    pending: rest.clone(),
                    app: None,
                    task: t,
                })
                .collect(),
            RStrat::Call { name, args } => {
                let bodies = Rc::new(call_bodies(cx, dag, name, args));
                if bodies.is_empty() {
                    Vec::new()
                } else {
                    vec![Process {
                        dag,
                        pending: push(rest, Rc::new(RStrat::CallGenerator { bodies, next: 0 })),
                        app: None,
                        task: t,
                    }]
                }
            }
            RStrat::CallGenerator { bodies, next } => {
                if *next >= bodies.len() {
                    Vec::new()
                } else {
                    let call_task = self.new_task(t, TaskKind::Call { rest: rest.clone() });
                    let body = Process {
                        dag,
                        pending: push(&None, bodies[*next].clone()),
                        app: None,
                        task: call_task,
                    };
                    let again = Process {
                        dag,
                        pending: push(
                            rest,
                            Rc::new(RStrat::CallGenerator {
                                bodies: bodies.clone(),
                                next: next + 1,
                            }),
                        ),
                        app: None,
                        task: t,
                    };
                    vec![body, again]
                }
            }
        }
    }
}

/// Match one named call against every compatible definition in donation order and specialize each body
/// with its match substitution. Calls remain lazy in the resolved tree; recursive bodies are opened only
/// when their call frame is decomposed.
fn call_bodies(cx: &mut Cx, dag: DagId, name: &str, args: &[Term]) -> Vec<Rc<RStrat>> {
    let subject_kind = cx.eng.sorts().kind_of(cx.eng.node(dag).sort());
    let arg_kinds: Vec<KindId> = args
        .iter()
        .map(|arg| match arg {
            Term::Var(variable) => cx.eng.sorts().kind_of(variable.sort),
            _ => cx
                .eng
                .symbol_kind(arg.top_symbol().expect("non-variable call argument")),
        })
        .collect();
    let mut arg_dags = Vec::with_capacity(args.len());
    for arg in args {
        let mut vars = Vec::new();
        term_var_indices(arg, &mut vars);
        if !vars.is_empty() {
            return Vec::new();
        }
        arg_dags.push(inst_reduce(cx, arg, &[]));
    }

    let mut bodies = Vec::new();
    for def in &cx.program.defs {
        if def.key.name != name || def.key.args != arg_kinds || def.key.subject != subject_kind {
            continue;
        }
        let mut substitutions = vec![vec![None; def.nr_vars as usize]];
        for (pattern, &arg) in def.patterns.iter().zip(&arg_dags) {
            let mut next = Vec::new();
            for substitution in substitutions {
                next.extend(match_extend(cx.eng, pattern, &substitution, arg, false));
            }
            substitutions = next;
            if substitutions.is_empty() {
                break;
            }
        }
        for substitution in substitutions {
            let terms: Vec<Option<Term>> = substitution
                .into_iter()
                .map(|binding| binding.map(|value| term_from_dag_slots(cx.eng, value)))
                .collect();
            bodies.push(specialize_strategy(&def.body, &terms));
        }
    }
    bodies
}

fn specialize_strategy(strategy: &Rc<RStrat>, bindings: &[Option<Term>]) -> Rc<RStrat> {
    let resolved = match &**strategy {
        RStrat::Idle => RStrat::Idle,
        RStrat::Fail => RStrat::Fail,
        RStrat::Apply {
            rules,
            top,
            subst,
            substrats,
        } => RStrat::Apply {
            rules: rules.clone(),
            top: *top,
            subst: subst
                .iter()
                .map(|(name, term)| (name.clone(), specialize_term(term, bindings)))
                .collect(),
            substrats: substrats
                .iter()
                .map(|child| specialize_strategy(child, bindings))
                .collect(),
        },
        RStrat::One(child) => RStrat::One(specialize_strategy(child, bindings)),
        RStrat::Seq(left, right) => RStrat::Seq(
            specialize_strategy(left, bindings),
            specialize_strategy(right, bindings),
        ),
        RStrat::Union(left, right) => RStrat::Union(
            specialize_strategy(left, bindings),
            specialize_strategy(right, bindings),
        ),
        RStrat::Star(child) => RStrat::Star(specialize_strategy(child, bindings)),
        RStrat::Plus(child) => RStrat::Plus(specialize_strategy(child, bindings)),
        RStrat::Normalize(child) => RStrat::Normalize(specialize_strategy(child, bindings)),
        RStrat::Branch {
            test,
            success,
            failure,
        } => RStrat::Branch {
            test: specialize_strategy(test, bindings),
            success: specialize_strategy(success, bindings),
            failure: specialize_strategy(failure, bindings),
        },
        RStrat::Test {
            anywhere,
            extension,
            pattern,
            nr_vars,
            cond,
        } => RStrat::Test {
            anywhere: *anywhere,
            extension: *extension,
            pattern: specialize_term(pattern, bindings),
            nr_vars: *nr_vars,
            cond: cond
                .iter()
                .map(|fragment| specialize_condition(fragment, bindings))
                .collect(),
        },
        RStrat::MatchRew {
            anywhere,
            pattern,
            nr_vars,
            cond,
            by,
        } => RStrat::MatchRew {
            anywhere: *anywhere,
            pattern: specialize_term(pattern, bindings),
            nr_vars: *nr_vars,
            cond: cond
                .iter()
                .map(|fragment| specialize_condition(fragment, bindings))
                .collect(),
            by: by
                .iter()
                .map(|(variable, child)| (*variable, specialize_strategy(child, bindings)))
                .collect(),
        },
        RStrat::Call { name, args } => RStrat::Call {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| specialize_term(arg, bindings))
                .collect(),
        },
        RStrat::CallGenerator { bodies, next } => RStrat::CallGenerator {
            bodies: Rc::new(
                bodies
                    .iter()
                    .map(|body| specialize_strategy(body, bindings))
                    .collect(),
            ),
            next: *next,
        },
    };
    Rc::new(resolved)
}

fn specialize_condition(
    fragment: &ConditionFragment,
    bindings: &[Option<Term>],
) -> ConditionFragment {
    match fragment {
        ConditionFragment::Equality { lhs, rhs } => ConditionFragment::Equality {
            lhs: specialize_term(lhs, bindings),
            rhs: specialize_term(rhs, bindings),
        },
        ConditionFragment::SortTest { term, sort } => ConditionFragment::SortTest {
            term: specialize_term(term, bindings),
            sort: *sort,
        },
        ConditionFragment::Matching {
            pattern,
            subject,
            fresh_vars,
        } => ConditionFragment::Matching {
            pattern: specialize_term(pattern, bindings),
            subject: specialize_term(subject, bindings),
            fresh_vars: fresh_vars
                .iter()
                .copied()
                .filter(|&slot| bindings.get(slot as usize).is_none_or(Option::is_none))
                .collect(),
        },
        ConditionFragment::Rewrite {
            lhs,
            pattern,
            fresh_vars,
        } => ConditionFragment::Rewrite {
            lhs: specialize_term(lhs, bindings),
            pattern: specialize_term(pattern, bindings),
            fresh_vars: fresh_vars
                .iter()
                .copied()
                .filter(|&slot| bindings.get(slot as usize).is_none_or(Option::is_none))
                .collect(),
        },
    }
}

fn specialize_term(term: &Term, bindings: &[Option<Term>]) -> Term {
    match term {
        Term::Var(variable) => bindings
            .get(variable.index as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_else(|| term.clone()),
        Term::Op { symbol, args } => Term::Op {
            symbol: *symbol,
            args: args
                .iter()
                .map(|arg| specialize_term(arg, bindings))
                .collect(),
        },
        Term::Iter { symbol, count, arg } => Term::Iter {
            symbol: *symbol,
            count: count.clone(),
            arg: Box::new(specialize_term(arg, bindings)),
        },
        Term::Na { .. } => term.clone(),
    }
}

/// Flatten a left-nested `_;_` spine into its element strategies (Maude's n-ary concatenation).
fn flatten_seq(s: &Rc<RStrat>, out: &mut Vec<Rc<RStrat>>) {
    if let RStrat::Seq(a, b) = &**s {
        flatten_seq(a, out);
        flatten_seq(b, out);
    } else {
        out.push(s.clone());
    }
}

/// Flatten a `_|_` spine into its alternatives (Maude's n-ary union — the decompose timing must match).
fn flatten_union(s: &Rc<RStrat>, out: &mut Vec<Rc<RStrat>>) {
    if let RStrat::Union(a, b) = &**s {
        flatten_union(a, out);
        flatten_union(b, out);
    } else {
        out.push(s.clone());
    }
}

/// All matches of `rules` against `dag` (positions pre-order × rules × match solutions), honouring `top` and
/// the application substitution — the resumable application's work-list (one rewrite fired per step).
fn precompute_matches(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    subst: &[(String, Term)],
) -> VecDeque<OneMatch> {
    let positions = if top {
        vec![Vec::new()]
    } else {
        all_positions(cx.eng, dag)
    };
    let mut out = VecDeque::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let Some(initial) = initial_bindings(cx, r, subst) else {
                continue;
            };
            let mut matching = cx.eng.rewrite_match_solutions_with_bindings(
                r.lhs.clone(),
                r.nr_vars,
                sub,
                &initial,
            );
            while matching.advance() {
                let result = matching.rewrite_result(&r.rhs);
                out.push_back(OneMatch {
                    path: path.clone(),
                    result,
                });
            }
        }
    }
    out
}

/// Build the caller-supplied bindings for a rule application. The matcher enforces these bindings
/// while enumerating, avoiding a second filter pass and retaining its theory-extension residue.
fn initial_bindings(
    cx: &mut Cx,
    r: &RRule,
    subst: &[(String, Term)],
) -> Option<Vec<Option<DagId>>> {
    let mut initial = vec![None; r.nr_vars as usize];
    for (name, term) in subst {
        let slot = r.var_names.iter().position(|candidate| candidate == name)?;
        let dag = inst(cx, term, &[]);
        initial[slot] = Some(cx.eng.reduce(dag));
    }
    Some(initial)
}

/// Apply rules whose conditions / rewrite-condition substrategies must be solved (the eager path).
fn apply_eager(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    subst: &[(String, Term)],
    substrats: &[Rc<RStrat>],
    fifo: bool,
) -> Vec<DagId> {
    let positions = if top {
        vec![Vec::new()]
    } else {
        all_positions(cx.eng, dag)
    };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let Some(initial) = initial_bindings(cx, r, subst) else {
                continue;
            };
            let mut matching = cx.eng.rewrite_match_solutions_with_bindings(
                r.lhs.clone(),
                r.nr_vars,
                sub,
                &initial,
            );
            let mut candidates = Vec::new();
            while matching.advance() {
                let bindings = (0..r.nr_vars).map(|slot| matching.binding(slot)).collect();
                let context = matching.rewrite_context();
                candidates.push((bindings, context));
            }
            for (bindings, context) in candidates {
                for bindings in solve_frags(cx, &r.condition, 0, bindings, substrats, 0, fifo) {
                    let bindings: Vec<DagId> = bindings
                        .into_iter()
                        .map(|binding| {
                            binding.expect("successful rule condition left an RHS variable unbound")
                        })
                        .collect();
                    let result = cx
                        .eng
                        .instantiate_rewrite_result(&r.rhs, &bindings, &context);
                    let whole = replace_at(cx.eng, dag, path, result);
                    cx.eng.reset_rewrites();
                    let whole = cx.eng.reduce(whole);
                    cx.count += 1 + cx.eng.rewrites();
                    out.push(whole);
                }
            }
        }
    }
    out
}

/// Solve a rule's / test's condition fragments `frags[i..]`, returning every completed binding vector.
fn solve_frags(
    cx: &mut Cx,
    frags: &[ConditionFragment],
    i: usize,
    bindings: Vec<Option<DagId>>,
    substrats: &[Rc<RStrat>],
    sub_idx: usize,
    fifo: bool,
) -> Vec<Vec<Option<DagId>>> {
    let Some(frag) = frags.get(i) else {
        return vec![bindings];
    };
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            let l = inst_reduce(cx, lhs, &bindings);
            let r = inst_reduce(cx, rhs, &bindings);
            if cx.eng.deep_equal(l, r) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx, fifo)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::SortTest { term, sort } => {
            let tt = inst_reduce(cx, term, &bindings);
            let ls = cx.eng.sort_of(tt);
            if cx.eng.sorts().same_kind(ls, *sort) && cx.eng.sorts().leq(ls, *sort) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx, fifo)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::Matching {
            pattern, subject, ..
        } => {
            let subj = inst_reduce(cx, subject, &bindings);
            let mut out = Vec::new();
            for nb in match_extend(cx.eng, pattern, &bindings, subj, false) {
                out.extend(solve_frags(cx, frags, i + 1, nb, substrats, sub_idx, fifo));
            }
            out
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            if sub_idx >= substrats.len() {
                return Vec::new();
            }
            let start = inst_reduce(cx, lhs, &bindings);
            let states = run_search(cx, start, substrats[sub_idx].clone(), fifo);
            let mut out = Vec::new();
            for (s, _) in states {
                for nb in match_extend(cx.eng, pattern, &bindings, s, false) {
                    out.extend(solve_frags(
                        cx,
                        frags,
                        i + 1,
                        nb,
                        substrats,
                        sub_idx + 1,
                        fifo,
                    ));
                }
            }
            out
        }
    }
}

/// `matchrew`/`amatchrew`: match the pattern, run each by-variable's substrategy, rebuild for every
/// combination (first by-variable varies fastest).
#[allow(clippy::too_many_arguments)]
fn matchrew_solutions(
    cx: &mut Cx,
    dag: DagId,
    anywhere: bool,
    pattern: &Term,
    nr_vars: u32,
    cond: &[ConditionFragment],
    by: &[(u32, Rc<RStrat>)],
    fifo: bool,
) -> Vec<DagId> {
    let positions = if anywhere {
        all_positions(cx.eng, dag)
    } else {
        vec![Vec::new()]
    };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, false) {
            for fb in solve_frags(cx, cond, 0, b, &[], 0, fifo) {
                let mut per: Vec<Vec<DagId>> = Vec::new();
                for (vi, st) in by {
                    let subterm =
                        fb[*vi as usize].expect("matchrew by-variable bound by the match");
                    per.push(
                        run_search(cx, subterm, st.clone(), fifo)
                            .into_iter()
                            .map(|(d, _)| d)
                            .collect(),
                    );
                }
                let counts: Vec<usize> = per.iter().map(|s| s.len()).collect();
                let total: usize = counts.iter().product();
                for n in 0..total {
                    let mut rem = n;
                    let mut bnd = fb.clone();
                    for (k, (vi, _)) in by.iter().enumerate() {
                        let choice = rem % counts[k];
                        rem /= counts[k];
                        bnd[*vi as usize] = Some(per[k][choice]);
                    }
                    let new_sub = inst(cx, pattern, &bnd);
                    let whole = replace_at(cx.eng, dag, path, new_sub);
                    cx.eng.reset_rewrites();
                    let whole = cx.eng.reduce(whole);
                    cx.count += cx.eng.rewrites();
                    out.push(whole);
                }
            }
        }
    }
    out
}

/// Whether `pattern` matches `dag` (top / extension / anywhere) with `cond` holding under the match.
#[allow(clippy::too_many_arguments)]
fn test_holds(
    cx: &mut Cx,
    pattern: &Term,
    nr_vars: u32,
    dag: DagId,
    anywhere: bool,
    extension: bool,
    cond: &[ConditionFragment],
) -> bool {
    let positions = if anywhere {
        all_positions(cx.eng, dag)
    } else {
        vec![Vec::new()]
    };
    for path in positions {
        let sub = subterm_at(cx.eng, dag, &path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, extension) {
            if cond.is_empty() || !solve_frags(cx, cond, 0, b, &[], 0, false).is_empty() {
                return true;
            }
        }
    }
    false
}

/// Match `pattern` against `subject`, extending `base`: unbound pattern variables bound, bound ones checked
/// for consistency. `extension` enables AC/AU/S sub-part matching.
fn match_extend(
    eng: &mut Engine,
    pattern: &Term,
    base: &[Option<DagId>],
    subject: DagId,
    extension: bool,
) -> Vec<Vec<Option<DagId>>> {
    let mut pvars = Vec::new();
    term_var_indices(pattern, &mut pvars);
    let rpat = renumber_term(pattern, &pvars);
    let m = pvars.len() as u32;
    let mut raw: Vec<Vec<DagId>> = Vec::new();
    {
        let mut sols = eng.match_solutions(rpat, m, subject, extension);
        while sols.advance() {
            let mut row = Vec::with_capacity(m as usize);
            let mut ok = true;
            for j in 0..m {
                match sols.binding(j) {
                    Some(d) => row.push(d),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                raw.push(row);
            }
        }
    }
    let mut out = Vec::new();
    for row in raw {
        let mut nb = base.to_vec();
        let mut ok = true;
        for (k, &v) in pvars.iter().enumerate() {
            let val = row[k];
            let idx = v as usize;
            match nb[idx] {
                Some(existing) => {
                    if !eng.deep_equal(existing, val) {
                        ok = false;
                        break;
                    }
                }
                None => nb[idx] = Some(val),
            }
        }
        if ok {
            out.push(nb);
        }
    }
    out
}

/// Rebuild `t` with its variables renumbered to their position in `pvars` (a compact space).
fn renumber_term(t: &Term, pvars: &[u32]) -> Term {
    match t {
        Term::Var(v) => {
            let j = pvars
                .iter()
                .position(|&x| x == v.index)
                .expect("variable collected by term_var_indices");
            Term::var(j as u32, v.sort)
        }
        Term::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
        Term::Iter { symbol, count, arg } => {
            Term::iter(*symbol, count.clone(), renumber_term(arg, pvars))
        }
        Term::Op { symbol, args } => Term::Op {
            symbol: *symbol,
            args: args.iter().map(|a| renumber_term(a, pvars)).collect(),
        },
    }
}

/// Build a DAG instance of `term` under `bindings` (a partial binding vector). Unbound slots are filled with
/// an arbitrary bound value (never read).
fn inst(cx: &mut Cx, term: &Term, bindings: &[Option<DagId>]) -> DagId {
    match bindings.iter().flatten().copied().next() {
        None => cx.eng.instantiate_bindings(term, &[]),
        Some(placeholder) => {
            let full: Vec<DagId> = bindings.iter().map(|b| b.unwrap_or(placeholder)).collect();
            cx.eng.instantiate_bindings(term, &full)
        }
    }
}

/// Instantiate `term` under `bindings` and reduce it, counting the reductions toward the running total.
fn inst_reduce(cx: &mut Cx, term: &Term, bindings: &[Option<DagId>]) -> DagId {
    let d = inst(cx, term, bindings);
    cx.eng.reset_rewrites();
    let r = cx.eng.reduce(d);
    cx.count += cx.eng.rewrites();
    r
}

/// All subterm positions of `dag` (child-index paths), pre-order (outermost first).
fn all_positions(eng: &Engine, dag: DagId) -> Vec<Vec<usize>> {
    fn go(eng: &Engine, node: DagId, path: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        out.push(path.clone());
        let kids: Vec<DagId> = eng.node(node).children().collect();
        for (k, c) in kids.into_iter().enumerate() {
            path.push(k);
            go(eng, c, path, out);
            path.pop();
        }
    }
    let mut out = Vec::new();
    go(eng, dag, &mut Vec::new(), &mut out);
    out
}

/// The subterm of `root` at child-index `path`.
fn subterm_at(eng: &Engine, root: DagId, path: &[usize]) -> DagId {
    let mut node = root;
    for &k in path {
        node = eng.node(node).children().nth(k).expect("valid position");
    }
    node
}

/// `root` with the subterm at `path` replaced by `new` (rebuilding the spine, theory-aware).
fn replace_at(eng: &mut Engine, root: DagId, path: &[usize], new: DagId) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        return new;
    };
    let sym = eng.node(root).symbol();
    let mut kids: Vec<DagId> = eng.node(root).children().collect();
    kids[head] = replace_at(eng, kids[head], rest, new);
    eng.make_node(sym, kids)
}

/// Deduplicate solutions by `deep_equal`, keeping the first occurrence + its count.
fn dedup(eng: &Engine, sols: Vec<StratSolution>) -> Vec<StratSolution> {
    let mut out: Vec<StratSolution> = Vec::new();
    for s in sols {
        if !out.iter().any(|k| eng.deep_equal(k.term, s.term)) {
            out.push(s);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::load::build_loaded_module;
    use crate::surface::parser::Parser;

    fn loaded_strategy_module(source: &str) -> (LoadedModule, Interner) {
        let mut interner = Interner::new();
        let tokens = tokenize(source, &mut interner);
        let mut source = Parser::new(&tokens, &interner)
            .parse_source()
            .expect("parse strategy module");
        assert_eq!(source.modules.len(), 1);
        let module = source.modules.remove(0);
        let loaded = build_loaded_module(&module, &mut interner).expect("build strategy module");
        (loaded, interner)
    }

    #[test]
    fn declaration_profiles_use_kinds_not_exact_sorts() {
        let (loaded, interner) = loaded_strategy_module(
            "smod STRAT-PROFILES is
               sorts K A B T .
               subsorts A B < K .
               ops a : -> A .
               op b : -> B .
               op t : -> T .
               strat same : A @ A .
               strat same : B @ B .
               strat same : T @ T .
               strat zero : @ A .
               strat zero : @ B .
             endsm",
        );
        let program = compile_strategy_program(&loaded, &interner);
        let same = program
            .profiles
            .iter()
            .filter(|profile| profile.key.name == "same")
            .collect::<Vec<_>>();
        assert_eq!(
            same.len(),
            2,
            "A/B declarations coalesce by their shared argument and subject kinds; T stays distinct"
        );
        assert_eq!(
            program
                .profiles
                .iter()
                .filter(|profile| profile.key.name == "zero")
                .count(),
            1,
            "zero-argument declarations ignore the exact A/B subject sort within one kind"
        );
    }

    #[test]
    fn definitions_keep_order_and_share_lhs_variable_slots() {
        let (loaded, interner) = loaded_strategy_module(
            "smod STRAT-DEFINITIONS is
               sort S .
               ops a b : -> S .
               var X : S .
               strat choose : S @ S .
               strat pair : S S @ S .
               sd choose(a) := idle .
               sd choose(b) := fail .
               sd pair(X, X) := match X .
             endsm",
        );
        let program = compile_strategy_program(&loaded, &interner);
        let choose = program
            .defs
            .iter()
            .filter(|definition| definition.key.name == "choose")
            .collect::<Vec<_>>();
        assert_eq!(choose.len(), 2);
        let pattern_name = |definition: &RDef| match &definition.patterns[0] {
            Term::Op { symbol, args } if args.is_empty() => {
                loaded.built.engine.symbol(*symbol).name()
            }
            pattern => panic!("expected constant definition pattern, got {pattern:?}"),
        };
        assert_eq!(
            choose
                .iter()
                .map(|definition| pattern_name(definition))
                .collect::<Vec<_>>(),
            ["a", "b"],
            "definition donation order is retained"
        );

        let pair = program
            .defs
            .iter()
            .find(|definition| definition.key.name == "pair")
            .expect("pair definition");
        assert_eq!(pair.nr_vars, 1);
        let [Term::Var(left), Term::Var(right)] = pair.patterns.as_slice() else {
            panic!("expected two variable patterns");
        };
        assert_eq!(
            left.index, right.index,
            "both lhs occurrences bind the same strategy variable slot"
        );
        let RStrat::Test {
            pattern: Term::Var(body),
            ..
        } = &*pair.body
        else {
            panic!("expected match test body");
        };
        assert_eq!(
            body.index, left.index,
            "the lhs binding is shared with the resolved definition body"
        );
    }
}
