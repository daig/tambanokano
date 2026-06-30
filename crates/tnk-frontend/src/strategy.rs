//! The strategy language interpreter (Pillar 2.4) — executes a parsed [`StratExpr`] against a subject term,
//! enumerating the solutions of `srewrite` (fair) / `dsrewrite` (depth-first).
//!
//! The surface [`StratExpr`] (with raw term bubbles) is first **resolved** against the module's grammar +
//! rule table into an [`RStrat`] (patterns parsed to [`Term`]s, rule labels resolved to their sides +
//! condition), then **executed** by a faithful port of Maude's strategic-search **process model**
//! ([`run_search`]): a `VecDeque` of [`Process`]es, each a `(term, pending-strategy-stack)`. One step
//! *decomposes* the top strategy frame into successor processes (a decompose does **no** rewrite — it only
//! schedules); a rule application runs as a resumable [`AppState`] that yields **one** rewrite per step; a
//! process with an empty pending stack is a **solution**. The fair/`srewrite` mode appends successors (FIFO,
//! round-robin); `dsrewrite` prepends them (LIFO, depth-first). This reproduces Maude's exact solution
//! **order** and per-solution cumulative **rewrite count** (validated against Maude 3.5.1's C++
//! `StrategyLanguage/`: the FIFO ring vs LIFO stack, the per-combinator decompose order, and the
//! cumulative count sampled at each solution). Cycle pruning is a per-search seen-set of `(term, pending)`,
//! which also gives Maude's solution de-duplication.
//!
//! Scope: `idle`/`fail`/`all`/application by label (with `L[σ]` and rewrite-condition substrategies
//! `L{E,…}`)/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+ `try`/`not`/`test`/`or-else`)/`match`/`xmatch`/`amatch`
//! tests/`matchrew`/`amatchrew`/strategy **calls** + **conditional rules**. The branch/`one`/`!`/`matchrew`
//! and conditional-rule/substrategy sub-searches run *eagerly within a step* (faithful values + sub-order;
//! their fair-interleave with parallel outer branches is the documented residual, `gaps.md`). `xmatchrew`
//! and conditional `csd` error clearly at resolve (engine/binding follow-ons).

use crate::build_term::VarIndex;
use crate::lex::{Interner, Token};
use crate::load::{parse_build, parse_condition, term_var_indices, LoadedModule};
use crate::surface::ast::{StratExpr, TestKind};
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::term::{ConditionFragment, Term};

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

/// A resolved strategy — the [`StratExpr`] with patterns parsed and rule labels resolved. Recursive children
/// are [`Rc`]'d so the pending stack can share them cheaply and the cycle-pruning seen-set can key on their
/// (stable) pointer identity.
enum RStrat {
    Idle,
    Fail,
    /// Apply one of `rules` (a label's rules, or all rules for `all`); `top` restricts to the top position.
    /// `subst` = the initial substitution `L[x<-t,…]`; `substrats` = the rewrite-condition substrategies.
    Apply { rules: Vec<RRule>, top: bool, subst: Vec<(String, Term)>, substrats: Vec<Rc<RStrat>> },
    One(Rc<RStrat>),
    Seq(Rc<RStrat>, Rc<RStrat>),
    Union(Rc<RStrat>, Rc<RStrat>),
    Star(Rc<RStrat>),
    Plus(Rc<RStrat>),
    Normalize(Rc<RStrat>),
    Branch { test: Rc<RStrat>, success: Rc<RStrat>, failure: Rc<RStrat> },
    Test { anywhere: bool, extension: bool, pattern: Term, nr_vars: u32, cond: Vec<ConditionFragment> },
    MatchRew { anywhere: bool, pattern: Term, nr_vars: u32, cond: Vec<ConditionFragment>, by: Vec<(u32, Rc<RStrat>)> },
    Call(String),
}

/// The evaluation context: the engine, the resolved `sd` definition table (call name → body), and the
/// running cumulative rewrite count.
struct Cx<'a> {
    eng: &'a mut Engine,
    defs: &'a HashMap<String, Rc<RStrat>>,
    count: u64,
}

/// A pending continuation: an immutable stack of resolved strategy frames (top = the next to decompose).
type Pending = Option<Rc<Frame>>;
struct Frame {
    strat: Rc<RStrat>,
    rest: Pending,
}

fn push(p: &Pending, s: Rc<RStrat>) -> Pending {
    Some(Rc::new(Frame { strat: s, rest: p.clone() }))
}

/// Push `ss` so that `ss[0]` ends on top (decomposed first) — concatenation's reverse-push.
fn push_all(mut p: Pending, ss: &[Rc<RStrat>]) -> Pending {
    for s in ss.iter().rev() {
        p = push(&p, s.clone());
    }
    p
}

/// A structural key for a pending stack — the sequence of strategy-node pointer identities (stable across a
/// command, since every frame is a shared `Rc` from the resolved tree). Used by the seen-set.
fn pending_key(p: &Pending) -> Vec<usize> {
    let mut k = Vec::new();
    let mut cur = p.clone();
    while let Some(f) = cur {
        k.push(Rc::as_ptr(&f.strat) as *const () as usize);
        cur = f.rest.clone();
    }
    k
}

/// A scheduled process: a term + its pending strategy stack, or — when `app` is set — a resumable rule
/// application yielding one rewrite per step.
struct Process {
    dag: DagId,
    pending: Pending,
    app: Option<AppState>,
}

/// A resumable rule application: the remaining matches to fire (one per step), and the continuation to give
/// each result.
struct AppState {
    rest: Pending,
    matches: VecDeque<OneMatch>,
}

struct OneMatch {
    path: Vec<usize>,
    rhs: Term,
    bindings: Vec<Option<DagId>>,
}

/// Run `srewrite`/`dsrewrite [in M :] term using strat` — resolve the strategy, build + reduce the subject,
/// and enumerate the solutions in Maude's order with the per-solution cumulative rewrite count. `depth_first`
/// selects `dsrewrite` (LIFO) over the fair `srewrite` (FIFO).
pub fn srewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
    strat: &StratExpr,
    depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), String> {
    let rstrat = resolve(strat, lm, i, 0)?;
    let mut vars = VarIndex::new();
    let subj_term = parse_build(term, &lm.grammar, &lm.built, i, &mut vars)?;
    if vars.count() != 0 {
        return Err("srewrite subject must be a ground term".to_string());
    }
    // Resolve the module's unconditional, parameterless strategy definitions into a call table.
    let mut defs = HashMap::new();
    for d in &lm.built.strat_defs {
        if d.cond.is_none() && d.params.is_empty() && let Ok(body) = resolve(&d.body, lm, i, 0) {
            defs.insert(d.name.clone(), body);
        }
    }
    let subj = lm.built.engine.instantiate_bindings(&subj_term, &[]);
    let mut cx = Cx { eng: &mut lm.built.engine, defs: &defs, count: 0 };
    cx.eng.reset_rewrites();
    let subj = cx.eng.reduce(subj);
    cx.count = cx.eng.rewrites();
    let sols = run_search(&mut cx, subj, rstrat, !depth_first);
    let total = cx.count;
    let out = dedup(cx.eng, sols.into_iter().map(|(term, rewrites)| StratSolution { term, rewrites }).collect());
    Ok((out, total))
}

/// Run a (sub-)search to exhaustion, returning every solution `(term, cumulative-count-at-emit)` in order.
/// `fifo` = the fair `srewrite` round-robin (append successors); `!fifo` = `dsrewrite` depth-first (prepend).
/// Each search has its own seen-set (Maude's per-task cycle pruning, which also de-duplicates solutions).
fn run_search(cx: &mut Cx, dag: DagId, strat: Rc<RStrat>, fifo: bool) -> Vec<(DagId, u64)> {
    let mut q: VecDeque<Process> = VecDeque::new();
    q.push_back(Process { dag, pending: push(&None, strat), app: None });
    let mut seen: Vec<(DagId, Vec<usize>)> = Vec::new();
    let mut out = Vec::new();
    while let Some(p) = q.pop_front() {
        let succ = step(cx, p, fifo, &mut seen, &mut |d, c| out.push((d, c)));
        schedule(&mut q, succ, fifo);
    }
    out
}

/// Run a (sub-)search, returning the **first** solution and stopping (`one(E)`'s / a test's semantics — the
/// rewrite count then reflects only the work up to that solution).
fn run_search_first(cx: &mut Cx, dag: DagId, strat: Rc<RStrat>, fifo: bool) -> Option<DagId> {
    let mut q: VecDeque<Process> = VecDeque::new();
    q.push_back(Process { dag, pending: push(&None, strat), app: None });
    let mut seen: Vec<(DagId, Vec<usize>)> = Vec::new();
    let mut found: Option<DagId> = None;
    while let Some(p) = q.pop_front() {
        let succ = step(cx, p, fifo, &mut seen, &mut |d, _| {
            if found.is_none() {
                found = Some(d);
            }
        });
        if found.is_some() {
            break;
        }
        schedule(&mut q, succ, fifo);
    }
    found
}

/// Schedule successor processes: FIFO (append) for the fair `srewrite`, LIFO (prepend, keeping their order)
/// for `dsrewrite`.
fn schedule(q: &mut VecDeque<Process>, succ: Vec<Process>, fifo: bool) {
    if fifo {
        for s in succ {
            q.push_back(s);
        }
    } else {
        for s in succ.into_iter().rev() {
            q.push_front(s);
        }
    }
}

/// Render a strategy expression back to source text (the `srewrite … using <here> .` echo). Best-effort.
pub fn print_strategy(e: &StratExpr, i: &Interner) -> String {
    fn join(toks: &[Token], i: &Interner) -> String {
        toks.iter().map(|t| i.resolve(t.sym)).collect::<Vec<_>>().join(" ")
    }
    match e {
        StratExpr::Idle => "idle".into(),
        StratExpr::Fail => "fail".into(),
        StratExpr::All => "all".into(),
        StratExpr::Apply { label, subst, substrats } => {
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
                let ss = substrats.iter().map(|e| print_strategy(e, i)).collect::<Vec<_>>().join(", ");
                s.push_str(&format!("{{{ss}}}"));
            }
            s
        }
        StratExpr::Top(a) => format!("top({})", print_strategy(a, i)),
        StratExpr::One(a) => format!("one({})", print_strategy(a, i)),
        StratExpr::Seq(a, b) => format!("{} ; {}", print_strategy(a, i), print_strategy(b, i)),
        StratExpr::Union(a, b) => format!("{} | {}", print_strategy(a, i), print_strategy(b, i)),
        StratExpr::Star(a) => format!("{} *", print_strategy(a, i)),
        StratExpr::Plus(a) => format!("{} +", print_strategy(a, i)),
        StratExpr::Normalize(a) => format!("{} !", print_strategy(a, i)),
        StratExpr::Branch { test, success, failure } => {
            format!("{} ? {} : {}", print_strategy(test, i), print_strategy(success, i), print_strategy(failure, i))
        }
        StratExpr::Test { kind, pattern, cond } => {
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
        StratExpr::MatchRew { kind, pattern, cond, subs } => {
            let kw = match kind {
                TestKind::Match => "matchrew",
                TestKind::XMatch => "xmatchrew",
                TestKind::AMatch => "amatchrew",
            };
            let by = subs
                .iter()
                .map(|(v, st)| format!("{} using {}", join(v, i), print_strategy(st, i)))
                .collect::<Vec<_>>()
                .join(", ");
            let st = cond.as_ref().map(|c| format!(" such that {}", join(c, i))).unwrap_or_default();
            format!("{kw} {}{st} by {by}", join(pattern, i))
        }
        StratExpr::Call { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let a = args.iter().map(|t| join(t, i)).collect::<Vec<_>>().join(", ");
                format!("{name}({a})")
            }
        }
    }
}

/// Resolve a surface [`StratExpr`] into an [`RStrat`] (shared via [`Rc`]). `depth` bounds parameterized-call
/// inline expansion. `xmatchrew` and conditional (`csd`) definitions error with a clear message (follow-ons).
fn resolve(e: &StratExpr, lm: &LoadedModule, i: &Interner, depth: u32) -> Result<Rc<RStrat>, String> {
    let r = match e {
        StratExpr::Idle => RStrat::Idle,
        StratExpr::Fail => RStrat::Fail,
        StratExpr::All => RStrat::Apply { rules: all_rules(lm), top: false, subst: Vec::new(), substrats: Vec::new() },
        StratExpr::Apply { label, subst, substrats } => {
            let rules = rules_labelled(lm, label);
            if !rules.is_empty() {
                let app_subst = resolve_subst(subst, lm, i)?;
                let subs = substrats.iter().map(|s| resolve(s, lm, i, depth)).collect::<Result<Vec<_>, _>>()?;
                RStrat::Apply { rules, top: false, subst: app_subst, substrats: subs }
            } else if subst.is_empty() && substrats.is_empty() {
                return resolve_call(label, &[], lm, i, depth);
            } else {
                return Err(format!("`{label}` is not a rule label (application `[…]{{…}}` needs a rule)"));
            }
        }
        StratExpr::Top(inner) => match &*resolve(inner, lm, i, depth)? {
            RStrat::Apply { rules, subst, substrats, .. } => RStrat::Apply {
                rules: rules.clone(),
                top: true,
                subst: subst.clone(),
                substrats: substrats.clone(),
            },
            _ => return Err("top(…) of a non-rule strategy is a follow-on".to_string()),
        },
        StratExpr::One(inner) => RStrat::One(resolve(inner, lm, i, depth)?),
        StratExpr::Seq(a, b) => RStrat::Seq(resolve(a, lm, i, depth)?, resolve(b, lm, i, depth)?),
        StratExpr::Union(a, b) => RStrat::Union(resolve(a, lm, i, depth)?, resolve(b, lm, i, depth)?),
        StratExpr::Star(a) => RStrat::Star(resolve(a, lm, i, depth)?),
        StratExpr::Plus(a) => RStrat::Plus(resolve(a, lm, i, depth)?),
        StratExpr::Normalize(a) => RStrat::Normalize(resolve(a, lm, i, depth)?),
        StratExpr::Branch { test, success, failure } => RStrat::Branch {
            test: resolve(test, lm, i, depth)?,
            success: resolve(success, lm, i, depth)?,
            failure: resolve(failure, lm, i, depth)?,
        },
        StratExpr::Test { kind, pattern, cond } => {
            let (anywhere, extension) = match kind {
                TestKind::Match => (false, false),
                TestKind::AMatch => (true, false),
                TestKind::XMatch => (false, true),
            };
            let mut vars = VarIndex::new();
            let pat = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(cond.as_deref(), &pat, &mut vars, lm, i, "test")?;
            RStrat::Test { anywhere, extension, pattern: pat, nr_vars: vars.count(), cond }
        }
        StratExpr::MatchRew { kind, pattern, cond, subs } => {
            let anywhere = match kind {
                TestKind::Match => false,
                TestKind::AMatch => true,
                TestKind::XMatch => {
                    return Err("xmatchrew (extension-match rewriting) reassembly is an engine follow-on".to_string())
                }
            };
            let mut vars = VarIndex::new();
            let pat = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(cond.as_deref(), &pat, &mut vars, lm, i, "matchrew `such that`")?;
            let mut by = Vec::new();
            for (vtoks, st) in subs {
                let name = token_text(vtoks, i);
                let idx = (0..vars.count())
                    .find(|&k| vars.name(k) == name)
                    .ok_or_else(|| format!("matchrew variable `{name}` does not occur in the pattern"))?;
                by.push((idx, resolve(st, lm, i, depth)?));
            }
            RStrat::MatchRew { anywhere, pattern: pat, nr_vars: vars.count(), cond, by }
        }
        StratExpr::Call { name, args } => return resolve_call(name, args, lm, i, depth),
    };
    Ok(Rc::new(r))
}

/// Parse an optional `such that` condition for a test/matchrew, rejecting a rewrite (`=>`) fragment.
fn resolve_test_cond(
    cond: Option<&[Token]>,
    pat: &Term,
    vars: &mut VarIndex,
    lm: &LoadedModule,
    i: &Interner,
    owner: &str,
) -> Result<Vec<ConditionFragment>, String> {
    let Some(c) = cond else { return Ok(Vec::new()) };
    let mut bound = BTreeSet::new();
    let mut pvars = Vec::new();
    term_var_indices(pat, &mut pvars);
    bound.extend(pvars);
    let frags = parse_condition(c, &lm.grammar, &lm.built, i, vars, &mut bound)?;
    if frags.iter().any(|f| matches!(f, ConditionFragment::Rewrite { .. })) {
        return Err(format!("a rewrite condition (`=>`) is not allowed in a {owner}"));
    }
    Ok(frags)
}

/// Resolve an application's initial substitution `[x <- t, …]` to `(var name, ground term)` pairs.
fn resolve_subst(
    subst: &[(Vec<Token>, Vec<Token>)],
    lm: &LoadedModule,
    i: &Interner,
) -> Result<Vec<(String, Term)>, String> {
    let mut out = Vec::new();
    for (var, val) in subst {
        let name = token_text(var, i);
        let mut vars = VarIndex::new();
        let t = parse_build(val, &lm.grammar, &lm.built, i, &mut vars)?;
        if vars.count() != 0 {
            return Err("a strategy application substitution value must be a ground term".to_string());
        }
        out.push((name, t));
    }
    Ok(out)
}

/// Resolve a strategy call `name(args…)`: parameterless → a lazy [`RStrat::Call`]; parameterized → expanded
/// inline by substituting parameter tokens with argument tokens (bounded by `MAX_PARAM_DEPTH`).
fn resolve_call(name: &str, args: &[Vec<Token>], lm: &LoadedModule, i: &Interner, depth: u32) -> Result<Rc<RStrat>, String> {
    if args.is_empty() {
        if lm.built.strat_defs.iter().any(|d| d.name == name && d.params.is_empty() && d.cond.is_none()) {
            return Ok(Rc::new(RStrat::Call(name.to_string())));
        }
        if lm.built.strat_defs.iter().any(|d| d.name == name && d.params.is_empty() && d.cond.is_some()) {
            return Err(format!("conditional strategy definition (`csd {name}`) is a follow-on"));
        }
        return Err(format!("`{name}` is neither a rule label nor a strategy of this module"));
    }
    const MAX_PARAM_DEPTH: u32 = 64;
    if depth >= MAX_PARAM_DEPTH {
        return Err("parameterized strategy-call expansion too deep (recursive parameterized calls are a follow-on)".to_string());
    }
    let found = lm
        .built
        .strat_defs
        .iter()
        .find(|d| d.name == name && d.params.len() == args.len())
        .map(|d| (d.params.clone(), d.body.clone(), d.cond.is_some()));
    let Some((params, body0, has_cond)) = found else {
        return Err(format!("no strategy `{name}` with {} argument(s) in this module", args.len()));
    };
    if has_cond {
        return Err(format!("conditional parameterized strategy definition (`csd {name}`) is a follow-on"));
    }
    let mut body = body0;
    for (p, a) in params.iter().zip(args.iter()) {
        body = subst_strat_tokens(&body, p, a);
    }
    resolve(&body, lm, i, depth + 1)
}

/// Substitute the token sequence `find` with `repl` in every raw token bubble of a strategy expression.
fn subst_strat_tokens(e: &StratExpr, find: &[Token], repl: &[Token]) -> StratExpr {
    match e {
        StratExpr::Idle => StratExpr::Idle,
        StratExpr::Fail => StratExpr::Fail,
        StratExpr::All => StratExpr::All,
        StratExpr::Apply { label, subst, substrats } => StratExpr::Apply {
            label: label.clone(),
            subst: subst.iter().map(|(v, t)| (replace_subseq(v, find, repl), replace_subseq(t, find, repl))).collect(),
            substrats: substrats.iter().map(|s| subst_strat_tokens(s, find, repl)).collect(),
        },
        StratExpr::Top(a) => StratExpr::Top(Box::new(subst_strat_tokens(a, find, repl))),
        StratExpr::One(a) => StratExpr::One(Box::new(subst_strat_tokens(a, find, repl))),
        StratExpr::Seq(a, b) => {
            StratExpr::Seq(Box::new(subst_strat_tokens(a, find, repl)), Box::new(subst_strat_tokens(b, find, repl)))
        }
        StratExpr::Union(a, b) => {
            StratExpr::Union(Box::new(subst_strat_tokens(a, find, repl)), Box::new(subst_strat_tokens(b, find, repl)))
        }
        StratExpr::Star(a) => StratExpr::Star(Box::new(subst_strat_tokens(a, find, repl))),
        StratExpr::Plus(a) => StratExpr::Plus(Box::new(subst_strat_tokens(a, find, repl))),
        StratExpr::Normalize(a) => StratExpr::Normalize(Box::new(subst_strat_tokens(a, find, repl))),
        StratExpr::Branch { test, success, failure } => StratExpr::Branch {
            test: Box::new(subst_strat_tokens(test, find, repl)),
            success: Box::new(subst_strat_tokens(success, find, repl)),
            failure: Box::new(subst_strat_tokens(failure, find, repl)),
        },
        StratExpr::Test { kind, pattern, cond } => StratExpr::Test {
            kind: *kind,
            pattern: replace_subseq(pattern, find, repl),
            cond: cond.as_ref().map(|c| replace_subseq(c, find, repl)),
        },
        StratExpr::MatchRew { kind, pattern, cond, subs } => StratExpr::MatchRew {
            kind: *kind,
            pattern: replace_subseq(pattern, find, repl),
            cond: cond.as_ref().map(|c| replace_subseq(c, find, repl)),
            subs: subs.iter().map(|(v, s)| (replace_subseq(v, find, repl), subst_strat_tokens(s, find, repl))).collect(),
        },
        StratExpr::Call { name, args } => StratExpr::Call {
            name: name.clone(),
            args: args.iter().map(|a| replace_subseq(a, find, repl)).collect(),
        },
    }
}

/// Replace each non-overlapping occurrence of `find` with `repl` (token identity by interned symbol).
fn replace_subseq(toks: &[Token], find: &[Token], repl: &[Token]) -> Vec<Token> {
    if find.is_empty() {
        return toks.to_vec();
    }
    let mut out = Vec::new();
    let mut k = 0;
    while k < toks.len() {
        if k + find.len() <= toks.len() && toks[k..k + find.len()].iter().zip(find).all(|(a, b)| a.sym == b.sym) {
            out.extend_from_slice(repl);
            k += find.len();
        } else {
            out.push(toks[k]);
            k += 1;
        }
    }
    out
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
    lm.built.rl_traces.iter().filter(|t| t.label.as_deref() == Some(label)).map(rrule).collect()
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

// ---- the process-model executor ----

/// Run one [`Process`] step: yields any solution to `emit`, returns the successor processes (front→back order
/// for the caller to schedule). `seen` is the per-search cycle-pruning set keyed on `(term, pending)`.
fn step(
    cx: &mut Cx,
    mut proc: Process,
    fifo: bool,
    seen: &mut Vec<(DagId, Vec<usize>)>,
    emit: &mut dyn FnMut(DagId, u64),
) -> Vec<Process> {
    // A resumable rule application: fire one match, spawn its result, survive (re-queue) for the rest.
    if let Some(mut app) = proc.app.take() {
        let Some(m) = app.matches.pop_front() else {
            return Vec::new(); // matches exhausted → DIE
        };
        let new_sub = inst(cx, &m.rhs, &m.bindings);
        let whole = replace_at(cx.eng, proc.dag, &m.path, new_sub);
        cx.eng.reset_rewrites();
        let whole = cx.eng.reduce(whole);
        cx.count += 1 + cx.eng.rewrites(); // the rule application (1) + its result's reductions
        let result = Process { dag: whole, pending: app.rest.clone(), app: None };
        let again = Process { dag: proc.dag, pending: proc.pending.clone(), app: Some(app) };
        return vec![result, again];
    }
    // A decomposition process: prune on a (term, pending) revisit (Maude's per-task seen-set; this also
    // de-duplicates re-reached solution states).
    let key = pending_key(&proc.pending);
    if seen.iter().any(|(d, k)| *k == key && cx.eng.deep_equal(*d, proc.dag)) {
        return Vec::new();
    }
    seen.push((proc.dag, key));
    // Empty pending ⇒ a solution.
    let Some(frame) = proc.pending.clone() else {
        emit(proc.dag, cx.count);
        return Vec::new();
    };
    decompose(cx, proc.dag, &frame.strat, &frame.rest, fifo)
}

/// Decompose the top strategy frame `strat` (applied to `dag`, with continuation `rest`) into successors.
fn decompose(cx: &mut Cx, dag: DagId, strat: &Rc<RStrat>, rest: &Pending, fifo: bool) -> Vec<Process> {
    match &**strat {
        RStrat::Idle => vec![Process { dag, pending: rest.clone(), app: None }],
        RStrat::Fail => Vec::new(),
        RStrat::Test { anywhere, extension, pattern, nr_vars, cond } => {
            if test_holds(cx, pattern, *nr_vars, dag, *anywhere, *extension, cond) {
                vec![Process { dag, pending: rest.clone(), app: None }]
            } else {
                Vec::new()
            }
        }
        RStrat::Seq(..) => {
            let mut frames = Vec::new();
            flatten_seq(strat, &mut frames);
            vec![Process { dag, pending: push_all(rest.clone(), &frames), app: None }]
        }
        RStrat::Union(..) => {
            let mut alts = Vec::new();
            flatten_union(strat, &mut alts);
            alts.into_iter().map(|s| Process { dag, pending: push(rest, s), app: None }).collect()
        }
        RStrat::Apply { rules, top, subst, substrats } => {
            if substrats.is_empty() && rules.iter().all(|r| r.condition.is_empty()) {
                // Faithful per-step application: one resumable process that fires one rewrite per step.
                let matches = precompute_matches(cx, dag, *top, rules, subst);
                vec![Process { dag, pending: None, app: Some(AppState { rest: rest.clone(), matches }) }]
            } else {
                // Conditional rules / rewrite-condition substrategies: solved eagerly (count folded now).
                apply_eager(cx, dag, *top, rules, subst, substrats, fifo)
                    .into_iter()
                    .map(|r| Process { dag: r, pending: rest.clone(), app: None })
                    .collect()
            }
        }
        RStrat::Star(child) => {
            let zero = Process { dag, pending: rest.clone(), app: None };
            let more = Process { dag, pending: push(&push(rest, strat.clone()), child.clone()), app: None };
            vec![zero, more]
        }
        RStrat::Plus(child) => {
            let star = Rc::new(RStrat::Star(child.clone()));
            vec![Process { dag, pending: push(&push(rest, star), child.clone()), app: None }]
        }
        RStrat::Normalize(child) => normal_forms(cx, dag, child, fifo)
            .into_iter()
            .map(|d| Process { dag: d, pending: rest.clone(), app: None })
            .collect(),
        RStrat::Branch { test, success, failure } => {
            // `not(E)` desugars to `E ? fail : …`: only the emptiness of `E` matters, so stop at its first
            // solution; otherwise forward every `E`-solution to the success branch.
            if matches!(&**success, RStrat::Fail) {
                if run_search_first(cx, dag, test.clone(), fifo).is_some() {
                    Vec::new()
                } else {
                    vec![Process { dag, pending: push(rest, failure.clone()), app: None }]
                }
            } else {
                let sols = run_search(cx, dag, test.clone(), fifo);
                if sols.is_empty() {
                    vec![Process { dag, pending: push(rest, failure.clone()), app: None }]
                } else {
                    sols.into_iter().map(|(s, _)| Process { dag: s, pending: push(rest, success.clone()), app: None }).collect()
                }
            }
        }
        RStrat::One(child) => match run_search_first(cx, dag, child.clone(), fifo) {
            Some(s) => vec![Process { dag: s, pending: rest.clone(), app: None }],
            None => Vec::new(),
        },
        RStrat::MatchRew { anywhere, pattern, nr_vars, cond, by } => {
            matchrew_solutions(cx, dag, *anywhere, pattern, *nr_vars, cond, by, fifo)
                .into_iter()
                .map(|r| Process { dag: r, pending: rest.clone(), app: None })
                .collect()
        }
        RStrat::Call(name) => match cx.defs.get(name) {
            Some(body) => {
                let body = body.clone();
                vec![Process { dag, pending: push(rest, body), app: None }]
            }
            None => Vec::new(),
        },
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

/// Flatten a `_|_` spine into its alternatives (Maude's n-ary union — the decompose-timing must match).
fn flatten_union(s: &Rc<RStrat>, out: &mut Vec<Rc<RStrat>>) {
    if let RStrat::Union(a, b) = &**s {
        flatten_union(a, out);
        flatten_union(b, out);
    } else {
        out.push(s.clone());
    }
}

/// All matches of `rules` against `dag` (positions pre-order × rules × match solutions), honouring `top` and
/// the application substitution `subst` — the resumable application's work-list (one rewrite fired per step).
fn precompute_matches(cx: &mut Cx, dag: DagId, top: bool, rules: &[RRule], subst: &[(String, Term)]) -> VecDeque<OneMatch> {
    let positions = if top { vec![Vec::new()] } else { all_positions(cx.eng, dag) };
    let mut out = VecDeque::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let base = vec![None; r.nr_vars as usize];
            for mut b in match_extend(cx.eng, &r.lhs, &base, sub, false) {
                if apply_subst(cx, r, subst, &mut b) {
                    out.push_back(OneMatch { path: path.clone(), rhs: r.rhs.clone(), bindings: b });
                }
            }
        }
    }
    out
}

/// Apply the initial substitution `[x<-t]` to a match's bindings: each named variable is checked (if the
/// match bound it) or bound (if not). Returns `false` if the constraint is inconsistent or names a non-variable.
fn apply_subst(cx: &mut Cx, r: &RRule, subst: &[(String, Term)], b: &mut [Option<DagId>]) -> bool {
    for (name, t) in subst {
        let Some(vi) = r.var_names.iter().position(|n| n == name) else { return false };
        let val = {
            let d = inst(cx, t, &[]);
            cx.eng.reduce(d)
        };
        match b[vi] {
            Some(existing) => {
                if !cx.eng.deep_equal(existing, val) {
                    return false;
                }
            }
            None => b[vi] = Some(val),
        }
    }
    true
}

/// Apply rules whose conditions / rewrite-condition substrategies must be solved (the eager path), returning
/// every result term. Mirrors [`precompute_matches`] + [`solve_frags`].
fn apply_eager(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    subst: &[(String, Term)],
    substrats: &[Rc<RStrat>],
    fifo: bool,
) -> Vec<DagId> {
    let positions = if top { vec![Vec::new()] } else { all_positions(cx.eng, dag) };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let base = vec![None; r.nr_vars as usize];
            for mut b in match_extend(cx.eng, &r.lhs, &base, sub, false) {
                if !apply_subst(cx, r, subst, &mut b) {
                    continue;
                }
                for fb in solve_frags(cx, &r.condition, 0, b, substrats, 0, fifo) {
                    let new_sub = inst(cx, &r.rhs, &fb);
                    let whole = replace_at(cx.eng, dag, path, new_sub);
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

/// Solve a rule's / test's condition fragments `frags[i..]` under `bindings`, returning every completed
/// binding vector. Rewrite (`=>`) fragments are driven by the application's next substrategy via a sub-search.
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
            let t = inst_reduce(cx, term, &bindings);
            let ls = cx.eng.sort_of(t);
            if cx.eng.sorts().same_kind(ls, *sort) && cx.eng.sorts().leq(ls, *sort) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx, fifo)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::Matching { pattern, subject, .. } => {
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
                    out.extend(solve_frags(cx, frags, i + 1, nb, substrats, sub_idx + 1, fifo));
                }
            }
            out
        }
    }
}

/// `matchrew`/`amatchrew`: match the pattern (top / anywhere), run each by-variable's substrategy on its
/// bound subterm, and rebuild the pattern for every combination (first by-variable varies fastest).
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
    let positions = if anywhere { all_positions(cx.eng, dag) } else { vec![Vec::new()] };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, false) {
            for fb in solve_frags(cx, cond, 0, b, &[], 0, fifo) {
                // Each by-variable's substrategy solutions, then the cartesian product (first fastest).
                let mut per: Vec<Vec<DagId>> = Vec::new();
                for (vi, st) in by {
                    let subterm = fb[*vi as usize].expect("matchrew by-variable bound by the match");
                    per.push(run_search(cx, subterm, st.clone(), fifo).into_iter().map(|(d, _)| d).collect());
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

/// The normal forms of `dag` under `child` (`E!`): apply `child` to a fixpoint; terms with no `child`-result
/// are normal forms. Reachable-set traversal with `deep_equal` cycle detection.
fn normal_forms(cx: &mut Cx, dag: DagId, child: &Rc<RStrat>, fifo: bool) -> Vec<DagId> {
    let mut out = Vec::new();
    let mut seen = vec![dag];
    let mut work = VecDeque::from([dag]);
    while let Some(d) = work.pop_front() {
        let succ = run_search(cx, d, child.clone(), fifo);
        if succ.is_empty() {
            out.push(d);
        } else {
            for (s, _) in succ {
                if !seen.iter().any(|&x| cx.eng.deep_equal(x, s)) {
                    seen.push(s);
                    work.push_back(s);
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
    let positions = if anywhere { all_positions(cx.eng, dag) } else { vec![Vec::new()] };
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

/// Match `pattern` against `subject`, extending `base`: unbound pattern variables are bound, already-bound
/// ones checked for consistency (`deep_equal`). `extension` enables AC/AU/S sub-part matching (`xmatch`).
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

/// Rebuild `t` with its variables renumbered to their position in `pvars` (a compact `0..pvars.len()` space).
fn renumber_term(t: &Term, pvars: &[u32]) -> Term {
    match t {
        Term::Var(v) => {
            let j = pvars.iter().position(|&x| x == v.index).expect("variable collected by term_var_indices");
            Term::var(j as u32, v.sort)
        }
        Term::Na { symbol, value } => Term::Na { symbol: *symbol, value: value.clone() },
        Term::Op { symbol, args } => {
            Term::Op { symbol: *symbol, args: args.iter().map(|a| renumber_term(a, pvars)).collect() }
        }
    }
}

/// Build a DAG instance of `term` under `bindings` (a partial binding vector). `term` references only bound
/// variables; unbound slots are filled with an arbitrary bound value (never read).
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
