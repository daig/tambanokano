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
//! is the documented residual, `gaps.md`). `xmatchrew` and conditional `csd` error clearly at resolve.

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

/// A resolved strategy — recursive children are [`Rc`]'d so the pending stack can share them cheaply and the
/// cycle-pruning seen-set can key on their (stable) pointer identity.
enum RStrat {
    Idle,
    Fail,
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

/// The evaluation context: the engine, the resolved `sd` definition table, and the cumulative rewrite count.
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

/// Push `ss` so that `ss[0]` ends on top (decomposed first).
fn push_all(mut p: Pending, ss: &[Rc<RStrat>]) -> Pending {
    for s in ss.iter().rev() {
        p = push(&p, s.clone());
    }
    p
}

/// A structural key for a pending stack — the sequence of strategy-node pointer identities (stable across a
/// command). Used by the seen-set.
fn pending_key(p: &Pending) -> Vec<usize> {
    let mut k = Vec::new();
    let mut cur = p.clone();
    while let Some(f) = cur {
        k.push(Rc::as_ptr(&f.strat) as *const () as usize);
        cur = f.rest.clone();
    }
    k
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
    rhs: Term,
    bindings: Vec<Option<DagId>>,
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
    /// `E ? success : failure` on `dag` (continuation `rest`): each `E`-solution → `success`; if `E` has none
    /// (exhausted with `!had_success`) → `failure` on `dag`.
    Branch { dag: DagId, success: Rc<RStrat>, failure: Rc<RStrat>, rest: Pending, had_success: bool },
    /// `one(E)` (continuation `rest`): forward the **first** `E`-solution, then discard the rest.
    One { rest: Pending, taken: bool },
    /// `E !` on `dag` (continuation `rest`): each `E`-solution re-arms `E!`; if `E` has none, `dag` is a
    /// normal form → emit it.
    Normalize { dag: DagId, normalize: Rc<RStrat>, rest: Pending, had_success: bool },
}

/// Run `srewrite`/`dsrewrite [in M :] term using strat` in Maude's order with per-solution cumulative counts.
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

/// Render a strategy expression back to source text (the echo). Best-effort.
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
/// inline expansion. `xmatchrew`/conditional `csd` error with a clear message (follow-ons).
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

// ---- the process + task executor ----

/// Run a (sub-)search to exhaustion, returning every solution `(term, cumulative-count-at-emit)` in order.
fn run_search(cx: &mut Cx, dag: DagId, strat: Rc<RStrat>, fifo: bool) -> Vec<(DagId, u64)> {
    let mut s = Search {
        q: VecDeque::new(),
        tasks: vec![TaskState { parent: 0, slaves: 0, alive: true, kind: TaskKind::Root }],
        seen: Vec::new(),
        fifo,
        out: Vec::new(),
    };
    s.schedule(vec![Process { dag, pending: push(&None, strat), app: None, task: 0 }]);
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
        self.tasks.push(TaskState { parent, slaves: 0, alive: true, kind });
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
            TaskKind::Root | TaskKind::One { .. } => Vec::new(),
            TaskKind::Branch { dag, failure, rest, had_success, .. } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process { dag: *dag, pending: push(rest, failure.clone()), app: None, task: parent }]
                }
            }
            TaskKind::Normalize { dag, rest, had_success, .. } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process { dag: *dag, pending: rest.clone(), app: None, task: parent }]
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
            TaskKind::Branch { success, rest, had_success, .. } => {
                *had_success = true;
                vec![Process { dag, pending: push(rest, success.clone()), app: None, task: parent }]
            }
            TaskKind::One { rest, taken } => {
                if *taken {
                    Vec::new()
                } else {
                    *taken = true;
                    vec![Process { dag, pending: rest.clone(), app: None, task: parent }]
                }
            }
            TaskKind::Normalize { normalize, rest, had_success, .. } => {
                *had_success = true;
                vec![Process { dag, pending: push(rest, normalize.clone()), app: None, task: parent }]
            }
        };
        let one = matches!(self.tasks[task].kind, TaskKind::One { .. });
        self.schedule(succ);
        // `one` discards the rest of its sub-search: kill the task so its queued processes are dropped.
        if one {
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
                let new_sub = inst(cx, &m.rhs, &m.bindings);
                let whole = replace_at(cx.eng, p.dag, &m.path, new_sub);
                cx.eng.reset_rewrites();
                let whole = cx.eng.reduce(whole);
                cx.count += 1 + cx.eng.rewrites();
                let result = Process { dag: whole, pending: app.rest.clone(), app: None, task: t };
                let again = Process { dag: p.dag, pending: None, app: Some(app), task: t };
                self.schedule(vec![result, again]);
            }
            self.dec_slave(t);
            return;
        }
        // A decomposition process: prune on a (term, pending) revisit within this task.
        let key = pending_key(&p.pending);
        if self.seen.iter().any(|(d, k, tt)| *tt == t && *k == key && cx.eng.deep_equal(*d, p.dag)) {
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
    fn decompose(&mut self, cx: &mut Cx, dag: DagId, strat: &Rc<RStrat>, rest: &Pending, t: usize) -> Vec<Process> {
        match &**strat {
            RStrat::Idle => vec![Process { dag, pending: rest.clone(), app: None, task: t }],
            RStrat::Fail => Vec::new(),
            RStrat::Test { anywhere, extension, pattern, nr_vars, cond } => {
                if test_holds(cx, pattern, *nr_vars, dag, *anywhere, *extension, cond) {
                    vec![Process { dag, pending: rest.clone(), app: None, task: t }]
                } else {
                    Vec::new()
                }
            }
            RStrat::Seq(..) => {
                let mut frames = Vec::new();
                flatten_seq(strat, &mut frames);
                vec![Process { dag, pending: push_all(rest.clone(), &frames), app: None, task: t }]
            }
            RStrat::Union(..) => {
                let mut alts = Vec::new();
                flatten_union(strat, &mut alts);
                alts.into_iter().map(|s| Process { dag, pending: push(rest, s), app: None, task: t }).collect()
            }
            RStrat::Apply { rules, top, subst, substrats } => {
                if substrats.is_empty() && rules.iter().all(|r| r.condition.is_empty()) {
                    let matches = precompute_matches(cx, dag, *top, rules, subst);
                    vec![Process { dag, pending: None, app: Some(AppState { rest: rest.clone(), matches }), task: t }]
                } else {
                    apply_eager(cx, dag, *top, rules, subst, substrats, self.fifo)
                        .into_iter()
                        .map(|r| Process { dag: r, pending: rest.clone(), app: None, task: t })
                        .collect()
                }
            }
            RStrat::Star(child) => {
                let zero = Process { dag, pending: rest.clone(), app: None, task: t };
                let more = Process { dag, pending: push(&push(rest, strat.clone()), child.clone()), app: None, task: t };
                vec![zero, more]
            }
            RStrat::Plus(child) => {
                let star = Rc::new(RStrat::Star(child.clone()));
                vec![Process { dag, pending: push(&push(rest, star), child.clone()), app: None, task: t }]
            }
            RStrat::Branch { test, success, failure } => {
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
                vec![Process { dag, pending: push(&None, test.clone()), app: None, task: nt }]
            }
            RStrat::One(child) => {
                let nt = self.new_task(t, TaskKind::One { rest: rest.clone(), taken: false });
                vec![Process { dag, pending: push(&None, child.clone()), app: None, task: nt }]
            }
            RStrat::Normalize(child) => {
                let nt = self.new_task(
                    t,
                    TaskKind::Normalize { dag, normalize: strat.clone(), rest: rest.clone(), had_success: false },
                );
                vec![Process { dag, pending: push(&None, child.clone()), app: None, task: nt }]
            }
            RStrat::MatchRew { anywhere, pattern, nr_vars, cond, by } => {
                matchrew_solutions(cx, dag, *anywhere, pattern, *nr_vars, cond, by, self.fifo)
                    .into_iter()
                    .map(|r| Process { dag: r, pending: rest.clone(), app: None, task: t })
                    .collect()
            }
            RStrat::Call(name) => match cx.defs.get(name) {
                Some(body) => vec![Process { dag, pending: push(rest, body.clone()), app: None, task: t }],
                None => Vec::new(),
            },
        }
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

/// Apply the initial substitution to a match's bindings (check if bound, bind if not). `false` on conflict.
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
    let positions = if anywhere { all_positions(cx.eng, dag) } else { vec![Vec::new()] };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, false) {
            for fb in solve_frags(cx, cond, 0, b, &[], 0, fifo) {
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
            let j = pvars.iter().position(|&x| x == v.index).expect("variable collected by term_var_indices");
            Term::var(j as u32, v.sort)
        }
        Term::Na { symbol, value } => Term::Na { symbol: *symbol, value: value.clone() },
        Term::Op { symbol, args } => {
            Term::Op { symbol: *symbol, args: args.iter().map(|a| renumber_term(a, pvars)).collect() }
        }
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
