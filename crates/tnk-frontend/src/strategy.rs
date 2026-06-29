//! The strategy language interpreter (Pillar 2.4) — executes a parsed [`StratExpr`] against a subject term,
//! enumerating the solutions of `srewrite`/`dsrewrite`.
//!
//! The surface [`StratExpr`] (with raw term bubbles) is first **resolved** against the module's grammar +
//! rule table into an [`RStrat`] (patterns parsed to [`Term`]s, rule labels resolved to their lhs/rhs), then
//! **evaluated** by a recursive solution enumerator [`eval`] over the engine. Each combinator maps to a set
//! of result terms; iteration (`*`/`+`/`!`) closes over the reachable set with cycle detection (dedup by
//! `deep_equal`). The reported rewrite count is the cumulative rule applications + equational reductions up
//! to each solution (a depth-first accounting — exact `srewrite` BFS-snapshot counts are a follow-on, see
//! `gaps.md`).
//!
//! Scope (Phase B core): `idle`/`fail`/`all`/application by label/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+ the
//! `try`/`not`/`test`/`or-else` sugar)/`match`/`amatch`. Strategy **calls** (`sd`/`csd`), `matchrew`, rule
//! **conditions** + application substitutions, and `xmatch` are later phases (resolution errors out clearly).

use crate::build_term::VarIndex;
use crate::lex::{Interner, Token};
use crate::load::{parse_build, LoadedModule};
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::term::Term;
use crate::surface::ast::{StratExpr, TestKind};

/// One solution of a strategy run: the (reduced) result term + the cumulative rewrite count at its emit.
pub struct StratSolution {
    pub term: DagId,
    pub rewrites: u64,
}

/// A resolved rule (its compiled-trace sides) for strategy application.
#[derive(Clone)]
struct RRule {
    lhs: Term,
    rhs: Term,
    nr_vars: u32,
}

/// A resolved strategy — the [`StratExpr`] with patterns parsed and rule labels resolved.
enum RStrat {
    Idle,
    Fail,
    /// Apply one of `rules` (a label's rules, or all rules for `all`); `top` restricts to the top position.
    Apply { rules: Vec<RRule>, top: bool },
    One(Box<RStrat>),
    Seq(Box<RStrat>, Box<RStrat>),
    Union(Box<RStrat>, Box<RStrat>),
    Star(Box<RStrat>),
    Plus(Box<RStrat>),
    Normalize(Box<RStrat>),
    Branch { test: Box<RStrat>, success: Box<RStrat>, failure: Box<RStrat> },
    /// `match`/`amatch P` — a test (no rewrite): succeed iff `pattern` matches at the top / anywhere.
    Test { anywhere: bool, pattern: Term, nr_vars: u32 },
}

/// Run `srewrite`/`dsrewrite [in M :] term using strat` — resolve the strategy against `lm`, build + reduce
/// the subject, and enumerate the solutions. `depth_first` is accepted but the enumeration order is the same
/// depth-first traversal for both today (the fair BFS ordering is a follow-on).
pub fn srewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
    strat: &StratExpr,
    _depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), String> {
    let rstrat = resolve(strat, lm, i)?;
    // Build + reduce the subject (its reductions count toward the first solution).
    let mut vars = VarIndex::new();
    let subj_term = parse_build(term, &lm.grammar, &lm.built, i, &mut vars)?;
    if vars.count() != 0 {
        return Err("srewrite subject must be a ground term".to_string());
    }
    let subj = lm.built.engine.instantiate_bindings(&subj_term, &[]);
    let eng = &mut lm.built.engine;
    eng.reset_rewrites();
    let subj = eng.reduce(subj);
    let mut count = eng.rewrites();
    let mut out = Vec::new();
    eval(&rstrat, subj, eng, &mut count, &mut out);
    Ok((dedup(eng, out), count))
}

/// Render a strategy expression back to source text (the `srewrite … using <here> .` echo). Best-effort —
/// the conformance harness pins the solution values, not the echo.
pub fn print_strategy(e: &StratExpr, i: &Interner) -> String {
    fn join(toks: &[Token], i: &Interner) -> String {
        toks.iter().map(|t| i.resolve(t.sym)).collect::<Vec<_>>().join(" ")
    }
    match e {
        StratExpr::Idle => "idle".into(),
        StratExpr::Fail => "fail".into(),
        StratExpr::All => "all".into(),
        StratExpr::Apply { label, .. } => label.clone(),
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
        StratExpr::MatchRew { pattern, subs, .. } => {
            let by = subs
                .iter()
                .map(|(v, st)| format!("{} using {}", join(v, i), print_strategy(st, i)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("matchrew {} by {by}", join(pattern, i))
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

/// Resolve a surface [`StratExpr`] into an [`RStrat`]: parse test patterns, resolve rule labels to their
/// (unconditional) sides. Unsupported constructs (calls, `matchrew`, conditions, application substitutions,
/// `xmatch`) error out with a clear message (their phases).
fn resolve(e: &StratExpr, lm: &LoadedModule, i: &Interner) -> Result<RStrat, String> {
    Ok(match e {
        StratExpr::Idle => RStrat::Idle,
        StratExpr::Fail => RStrat::Fail,
        StratExpr::All => RStrat::Apply { rules: all_rules(lm), top: false },
        StratExpr::Apply { label, subst, substrats } => {
            if !subst.is_empty() || !substrats.is_empty() {
                return Err("strategy application with substitution/condition substrategies: a follow-on (Phase D)".to_string());
            }
            let rules = rules_labelled(lm, label);
            if rules.is_empty() {
                return Err(format!(
                    "no (unconditional) rule labelled `{label}` (strategy calls `sd`/`csd` are a follow-on, Phase C)"
                ));
            }
            RStrat::Apply { rules, top: false }
        }
        StratExpr::Top(inner) => match resolve(inner, lm, i)? {
            RStrat::Apply { rules, .. } => RStrat::Apply { rules, top: true },
            _ => return Err("top(…) of a non-rule strategy is a follow-on".to_string()),
        },
        StratExpr::One(inner) => RStrat::One(Box::new(resolve(inner, lm, i)?)),
        StratExpr::Seq(a, b) => RStrat::Seq(Box::new(resolve(a, lm, i)?), Box::new(resolve(b, lm, i)?)),
        StratExpr::Union(a, b) => RStrat::Union(Box::new(resolve(a, lm, i)?), Box::new(resolve(b, lm, i)?)),
        StratExpr::Star(a) => RStrat::Star(Box::new(resolve(a, lm, i)?)),
        StratExpr::Plus(a) => RStrat::Plus(Box::new(resolve(a, lm, i)?)),
        StratExpr::Normalize(a) => RStrat::Normalize(Box::new(resolve(a, lm, i)?)),
        StratExpr::Branch { test, success, failure } => RStrat::Branch {
            test: Box::new(resolve(test, lm, i)?),
            success: Box::new(resolve(success, lm, i)?),
            failure: Box::new(resolve(failure, lm, i)?),
        },
        StratExpr::Test { kind, pattern, cond } => {
            if cond.is_some() {
                return Err("a test condition (`such that`) is a follow-on".to_string());
            }
            let anywhere = match kind {
                TestKind::Match => false,
                TestKind::AMatch => true,
                TestKind::XMatch => return Err("xmatch in a strategy is a follow-on".to_string()),
            };
            let mut vars = VarIndex::new();
            let pattern = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
            RStrat::Test { anywhere, pattern, nr_vars: vars.count() }
        }
        StratExpr::MatchRew { .. } => return Err("matchrew is a follow-on (Phase D)".to_string()),
        StratExpr::Call { .. } => return Err("strategy calls are a follow-on (Phase C)".to_string()),
    })
}

/// All (unconditional) rules of the module, as [`RRule`]s.
fn all_rules(lm: &LoadedModule) -> Vec<RRule> {
    lm.built
        .rl_traces
        .iter()
        .filter(|t| t.condition.is_empty())
        .map(|t| RRule { lhs: t.lhs.clone(), rhs: t.rhs.clone(), nr_vars: t.var_names.len() as u32 })
        .collect()
}

/// The (unconditional) rules labelled `label`.
fn rules_labelled(lm: &LoadedModule, label: &str) -> Vec<RRule> {
    lm.built
        .rl_traces
        .iter()
        .filter(|t| t.condition.is_empty() && t.label.as_deref() == Some(label))
        .map(|t| RRule { lhs: t.lhs.clone(), rhs: t.rhs.clone(), nr_vars: t.var_names.len() as u32 })
        .collect()
}

/// Enumerate the solutions of `strat` applied to `dag`, pushing each `(result, count-snapshot)` to `out`.
/// `count` is the running cumulative rewrite total (rule applications + equational reductions).
fn eval(strat: &RStrat, dag: DagId, eng: &mut Engine, count: &mut u64, out: &mut Vec<StratSolution>) {
    match strat {
        RStrat::Idle => out.push(StratSolution { term: dag, rewrites: *count }),
        RStrat::Fail => {}
        RStrat::Apply { rules, top } => {
            for r in one_step(eng, dag, rules, *top, count) {
                out.push(StratSolution { term: r, rewrites: *count });
            }
        }
        RStrat::Seq(a, b) => {
            let mut mid = Vec::new();
            eval(a, dag, eng, count, &mut mid);
            for s in mid {
                eval(b, s.term, eng, count, out);
            }
        }
        RStrat::Union(a, b) => {
            eval(a, dag, eng, count, out);
            eval(b, dag, eng, count, out);
        }
        RStrat::Star(a) => {
            // Zero-or-more: the reachable set under `a`, BFS from `dag` (idle path included), cycle-detected.
            let mut seen = vec![dag];
            out.push(StratSolution { term: dag, rewrites: *count });
            let mut frontier = vec![dag];
            while let Some(w) = frontier.pop() {
                let mut next = Vec::new();
                eval(a, w, eng, count, &mut next);
                for s in next {
                    if !seen.iter().any(|&x| eng.deep_equal(x, s.term)) {
                        seen.push(s.term);
                        frontier.push(s.term);
                        out.push(s);
                    }
                }
            }
        }
        RStrat::Plus(a) => {
            // One-or-more = a ; a*.
            let mut first = Vec::new();
            eval(a, dag, eng, count, &mut first);
            let star = RStrat::Star(Box::new(clone_rstrat(a)));
            for s in first {
                // a* includes the idle (s itself); emit s + its closure.
                eval(&star, s.term, eng, count, out);
            }
        }
        RStrat::Normalize(a) => {
            // Apply `a` to a fixpoint: a result with no `a`-successor is a normal form.
            let mut next = Vec::new();
            eval(a, dag, eng, count, &mut next);
            if next.is_empty() {
                out.push(StratSolution { term: dag, rewrites: *count });
            } else {
                for s in next {
                    eval(strat, s.term, eng, count, out);
                }
            }
        }
        RStrat::Branch { test, success, failure } => {
            let mut rs = Vec::new();
            eval(test, dag, eng, count, &mut rs);
            if rs.is_empty() {
                eval(failure, dag, eng, count, out);
            } else {
                for s in rs {
                    eval(success, s.term, eng, count, out);
                }
            }
        }
        RStrat::One(a) => {
            let mut all = Vec::new();
            eval(a, dag, eng, count, &mut all);
            if let Some(s) = all.into_iter().next() {
                out.push(s);
            }
        }
        RStrat::Test { anywhere, pattern, nr_vars } => {
            if test_matches(eng, pattern, *nr_vars, dag, *anywhere) {
                out.push(StratSolution { term: dag, rewrites: *count }); // a test: no rewrite, original subject
            }
        }
    }
}

/// Whether `pattern` matches `dag` at the top (or anywhere, if `anywhere`). A test only — no rewrite.
fn test_matches(eng: &mut Engine, pattern: &Term, nr_vars: u32, dag: DagId, anywhere: bool) -> bool {
    let positions = if anywhere { all_positions(eng, dag) } else { vec![Vec::new()] };
    positions.into_iter().any(|path| {
        let sub = subterm_at(eng, dag, &path);
        let mut sols = eng.match_solutions(pattern.clone(), nr_vars, sub, false);
        sols.advance()
    })
}

/// Every one-step rewrite of `dag` by one of `rules` (at the top only, if `top`), each reduced. `count` is
/// bumped by the equational reductions plus one per rule application (Maude's accounting).
fn one_step(eng: &mut Engine, dag: DagId, rules: &[RRule], top: bool, count: &mut u64) -> Vec<DagId> {
    let positions = if top { vec![Vec::new()] } else { all_positions(eng, dag) };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(eng, dag, path);
        for r in rules {
            // Collect this rule's matches at this position (bindings cloned out before mutating the engine).
            let mut binding_sets = Vec::new();
            {
                let mut sols = eng.match_solutions(r.lhs.clone(), r.nr_vars, sub, false);
                while sols.advance() {
                    binding_sets.push((0..r.nr_vars).map(|k| sols.binding(k).expect("bound")).collect::<Vec<_>>());
                }
            }
            for bindings in binding_sets {
                let new_sub = eng.instantiate_bindings(&r.rhs, &bindings);
                let whole = replace_at(eng, dag, path, new_sub);
                eng.reset_rewrites();
                let whole = eng.reduce(whole);
                *count += 1 + eng.rewrites(); // the rule application (1) + its result's reductions
                out.push(whole);
            }
        }
    }
    out
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

/// Deduplicate solutions by `deep_equal` (Maude hash-conses states), keeping the first occurrence + its count.
fn dedup(eng: &Engine, sols: Vec<StratSolution>) -> Vec<StratSolution> {
    let mut out: Vec<StratSolution> = Vec::new();
    for s in sols {
        if !out.iter().any(|k| eng.deep_equal(k.term, s.term)) {
            out.push(s);
        }
    }
    out
}

/// A structural clone of a resolved strategy (for unfolding `+` into `; *`).
fn clone_rstrat(s: &RStrat) -> RStrat {
    match s {
        RStrat::Idle => RStrat::Idle,
        RStrat::Fail => RStrat::Fail,
        RStrat::Apply { rules, top } => RStrat::Apply { rules: rules.clone(), top: *top },
        RStrat::One(a) => RStrat::One(Box::new(clone_rstrat(a))),
        RStrat::Seq(a, b) => RStrat::Seq(Box::new(clone_rstrat(a)), Box::new(clone_rstrat(b))),
        RStrat::Union(a, b) => RStrat::Union(Box::new(clone_rstrat(a)), Box::new(clone_rstrat(b))),
        RStrat::Star(a) => RStrat::Star(Box::new(clone_rstrat(a))),
        RStrat::Plus(a) => RStrat::Plus(Box::new(clone_rstrat(a))),
        RStrat::Normalize(a) => RStrat::Normalize(Box::new(clone_rstrat(a))),
        RStrat::Branch { test, success, failure } => RStrat::Branch {
            test: Box::new(clone_rstrat(test)),
            success: Box::new(clone_rstrat(success)),
            failure: Box::new(clone_rstrat(failure)),
        },
        RStrat::Test { anywhere, pattern, nr_vars } => {
            RStrat::Test { anywhere: *anywhere, pattern: pattern.clone(), nr_vars: *nr_vars }
        }
    }
}
