//! The strategy language interpreter (Pillar 2.4) — executes a parsed [`StratExpr`] against a subject term,
//! enumerating the solutions of `srewrite`/`dsrewrite`.
//!
//! The surface [`StratExpr`] (with raw term bubbles) is first **resolved** against the module's grammar +
//! rule table into an [`RStrat`] (patterns parsed to [`Term`]s, rule labels resolved to their lhs/rhs +
//! condition), then **evaluated** by a recursive solution enumerator [`eval`] over the engine. Each
//! combinator maps to a set of result terms; iteration (`*`/`+`/`!`) closes over the reachable set with
//! cycle detection (dedup by `deep_equal`). The reported rewrite count is the cumulative rule applications +
//! equational reductions up to each solution (a depth-first accounting — exact `srewrite` BFS-snapshot
//! counts are a follow-on, see `gaps.md`; the conformance harness pins solution *values + order + count*).
//!
//! Scope: `idle`/`fail`/`all`/application by label (with an initial substitution `L[σ]` and rewrite-
//! condition substrategies `L{E,…}`)/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+ the `try`/`not`/`test`/
//! `or-else` sugar)/`match`/`xmatch`/`amatch` tests (with `such that`)/`matchrew`/`amatchrew`/strategy
//! **calls** (`sd`, parameterless or parameterized) — and **conditional rules** (equality/sort/matching
//! fragments solved natively; rewrite fragments driven by the application's substrategies). Two narrow
//! features remain documented follow-ons (they error clearly at resolve): `xmatchrew` (extension-match
//! rewriting needs the engine's residue reassembly) and conditional (`csd`) strategy definitions (their
//! condition bindings must flow into the definition body at run time).

use crate::build_term::VarIndex;
use crate::lex::{Interner, Token};
use crate::load::{parse_build, parse_condition, term_var_indices, LoadedModule};
use crate::surface::ast::{StratExpr, TestKind};
use std::collections::{BTreeSet, HashMap};
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
    /// The rule's condition fragments (empty for an `rl`). Equality/sort/matching fragments are solved
    /// natively; a rewrite (`=>`) fragment is driven by the application's i-th substrategy.
    condition: Vec<ConditionFragment>,
    /// Total statement-local variables (lhs + rhs + condition), the binding-vector width.
    nr_vars: u32,
    /// Statement-local variable names (index → name) — resolves an application substitution's `x <- t`.
    var_names: Vec<String>,
}

/// A resolved strategy — the [`StratExpr`] with patterns parsed and rule labels resolved.
#[derive(Clone)]
enum RStrat {
    Idle,
    Fail,
    /// Apply one of `rules` (a label's rules, or all rules for `all`); `top` restricts to the top position.
    /// `subst` is the application's initial substitution `L[x <- t, …]` (var name → ground term); `substrats`
    /// are the substrategies `L{E, …}` controlling the rules' rewrite (`=>`) conditions, in order.
    Apply { rules: Vec<RRule>, top: bool, subst: Vec<(String, Term)>, substrats: Vec<RStrat> },
    One(Box<RStrat>),
    Seq(Box<RStrat>, Box<RStrat>),
    Union(Box<RStrat>, Box<RStrat>),
    Star(Box<RStrat>),
    Plus(Box<RStrat>),
    Normalize(Box<RStrat>),
    Branch { test: Box<RStrat>, success: Box<RStrat>, failure: Box<RStrat> },
    /// `match`/`xmatch`/`amatch P [such that C]` — a test (no rewrite): succeed iff `pattern` matches at the
    /// top / with extension / anywhere, and (if present) the condition `cond` holds under the match.
    Test { anywhere: bool, extension: bool, pattern: Term, nr_vars: u32, cond: Vec<ConditionFragment> },
    /// `matchrew`/`amatchrew P [such that C] by xᵢ using Eᵢ` — match `P` (top / anywhere), run each `Eᵢ` on
    /// the subterm bound to `xᵢ`, rebuild `P` from the (rewritten / matched) bindings. `by` is `(pattern var
    /// index, substrategy)`.
    MatchRew { anywhere: bool, pattern: Term, nr_vars: u32, cond: Vec<ConditionFragment>, by: Vec<(u32, RStrat)> },
    /// A parameterless strategy call `s` — resolved against the module's `sd` definition table at eval time
    /// (so a recursive definition is a finite reference, not an infinite inlining). Parameterized calls
    /// `s(args)` are expanded inline at resolve (see [`resolve_call`]).
    Call(String),
}

/// The evaluation context: the engine, the resolved `sd` definition table (call name → body), the running
/// cumulative rewrite count, and the current call path (for recursion cycle detection).
struct Cx<'a> {
    eng: &'a mut Engine,
    defs: &'a HashMap<String, RStrat>,
    count: u64,
    seen: Vec<(DagId, String)>,
}

/// The maximum inline-expansion depth for parameterized strategy calls — a guard against an unboundedly
/// recursive parameterized call (which inline expansion cannot resolve; see [`resolve_call`]).
const MAX_PARAM_DEPTH: u32 = 64;

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
    let rstrat = resolve(strat, lm, i, 0)?;
    // Build + reduce the subject (its reductions count toward the first solution).
    let mut vars = VarIndex::new();
    let subj_term = parse_build(term, &lm.grammar, &lm.built, i, &mut vars)?;
    if vars.count() != 0 {
        return Err("srewrite subject must be a ground term".to_string());
    }
    // Resolve the module's unconditional, parameterless strategy definitions into a call table; a
    // parameterized `sd`/conditional `csd` is handled at the call site (inline expansion / a clear error).
    let mut defs = HashMap::new();
    for d in &lm.built.strat_defs {
        if d.cond.is_none() && d.params.is_empty() && let Ok(body) = resolve(&d.body, lm, i, 0) {
            defs.insert(d.name.clone(), body);
        }
    }
    let subj = lm.built.engine.instantiate_bindings(&subj_term, &[]);
    let mut cx = Cx { eng: &mut lm.built.engine, defs: &defs, count: 0, seen: Vec::new() };
    cx.eng.reset_rewrites();
    let subj = cx.eng.reduce(subj);
    cx.count = cx.eng.rewrites();
    let mut out = Vec::new();
    eval(&rstrat, subj, &mut cx, &mut out);
    let total = cx.count;
    Ok((dedup(cx.eng, out), total))
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

/// Resolve a surface [`StratExpr`] into an [`RStrat`]: parse test/matchrew patterns + conditions, resolve
/// rule labels to their sides + condition, expand parameterized calls. `depth` bounds parameterized-call
/// inline expansion. The two genuine follow-ons (`xmatchrew`, `csd`) error with a clear message.
fn resolve(e: &StratExpr, lm: &LoadedModule, i: &Interner, depth: u32) -> Result<RStrat, String> {
    Ok(match e {
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
                // A bare name that is not a rule label: a parameterless strategy call.
                resolve_call(label, &[], lm, i, depth)?
            } else {
                return Err(format!("`{label}` is not a rule label (application `[…]{{…}}` needs a rule)"));
            }
        }
        StratExpr::Top(inner) => match resolve(inner, lm, i, depth)? {
            RStrat::Apply { rules, subst, substrats, .. } => RStrat::Apply { rules, top: true, subst, substrats },
            _ => return Err("top(…) of a non-rule strategy is a follow-on".to_string()),
        },
        StratExpr::One(inner) => RStrat::One(Box::new(resolve(inner, lm, i, depth)?)),
        StratExpr::Seq(a, b) => RStrat::Seq(Box::new(resolve(a, lm, i, depth)?), Box::new(resolve(b, lm, i, depth)?)),
        StratExpr::Union(a, b) => RStrat::Union(Box::new(resolve(a, lm, i, depth)?), Box::new(resolve(b, lm, i, depth)?)),
        StratExpr::Star(a) => RStrat::Star(Box::new(resolve(a, lm, i, depth)?)),
        StratExpr::Plus(a) => RStrat::Plus(Box::new(resolve(a, lm, i, depth)?)),
        StratExpr::Normalize(a) => RStrat::Normalize(Box::new(resolve(a, lm, i, depth)?)),
        StratExpr::Branch { test, success, failure } => RStrat::Branch {
            test: Box::new(resolve(test, lm, i, depth)?),
            success: Box::new(resolve(success, lm, i, depth)?),
            failure: Box::new(resolve(failure, lm, i, depth)?),
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
            // Resolve the by-list: each variable (named in the pattern/condition) + its substrategy.
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
        StratExpr::Call { name, args } => resolve_call(name, args, lm, i, depth)?,
    })
}

/// Parse an optional `such that` condition for a test/matchrew: shares the pattern's variable index (the
/// pattern's variables are already bound by the match), and rejects a rewrite (`=>`) fragment (legal only in
/// a rule condition).
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

/// Resolve a strategy call `name(args…)`. Parameterless calls become a lazy [`RStrat::Call`] (recursion is a
/// finite reference, cycle-detected at eval). Parameterized calls are **expanded inline** at resolve:
/// substitute each parameter's tokens with the argument's tokens in the definition body, then resolve it
/// (bounded by `MAX_PARAM_DEPTH` — an unboundedly recursive parameterized call cannot be inline-expanded).
fn resolve_call(name: &str, args: &[Vec<Token>], lm: &LoadedModule, i: &Interner, depth: u32) -> Result<RStrat, String> {
    if args.is_empty() {
        if lm.built.strat_defs.iter().any(|d| d.name == name && d.params.is_empty() && d.cond.is_none()) {
            return Ok(RStrat::Call(name.to_string()));
        }
        if lm.built.strat_defs.iter().any(|d| d.name == name && d.params.is_empty() && d.cond.is_some()) {
            return Err(format!("conditional strategy definition (`csd {name}`) is a follow-on"));
        }
        return Err(format!("`{name}` is neither a rule label nor a strategy of this module"));
    }
    if depth >= MAX_PARAM_DEPTH {
        return Err("parameterized strategy-call expansion too deep (recursive parameterized calls are a follow-on)".to_string());
    }
    // Find a matching definition by name + arity; clone what we need so the `lm` borrow ends here.
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

/// Substitute every occurrence of the token sequence `find` with `repl` in all of a strategy expression's
/// raw token bubbles (patterns, substitutions, conditions, call arguments) — the parameter→argument
/// substitution for an inline-expanded parameterized call. Recurses structurally; non-bubble parts pass
/// through unchanged.
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

/// Replace each non-overlapping occurrence of the `find` token sequence with `repl` (token identity is by
/// interned symbol, ignoring source position).
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

/// The concatenated text of a token bubble (a variable name `X:S` is one token; a spaced `X : S` concatenates
/// to the same `X:S`, matching how `build_term` records the variable name).
fn token_text(toks: &[Token], i: &Interner) -> String {
    toks.iter().map(|t| i.resolve(t.sym)).collect()
}

/// All rules of the module, as [`RRule`]s (conditional rules included — their conditions are solved at apply).
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

/// Enumerate the solutions of `strat` applied to `dag`, pushing each `(result, count-snapshot)` to `out`.
/// `count` is the running cumulative rewrite total (rule applications + equational reductions).
fn eval(strat: &RStrat, dag: DagId, cx: &mut Cx, out: &mut Vec<StratSolution>) {
    match strat {
        RStrat::Idle => out.push(StratSolution { term: dag, rewrites: cx.count }),
        RStrat::Fail => {}
        RStrat::Apply { rules, top, subst, substrats } => apply_rules(cx, dag, *top, rules, subst, substrats, out),
        RStrat::Seq(a, b) => {
            let mut mid = Vec::new();
            eval(a, dag, cx, &mut mid);
            for s in mid {
                eval(b, s.term, cx, out);
            }
        }
        RStrat::Union(a, b) => {
            eval(a, dag, cx, out);
            eval(b, dag, cx, out);
        }
        RStrat::Star(a) => {
            // Zero-or-more: the reachable set under `a`, BFS from `dag` (idle path included), cycle-detected.
            let mut seen = vec![dag];
            out.push(StratSolution { term: dag, rewrites: cx.count });
            let mut frontier = vec![dag];
            while let Some(w) = frontier.pop() {
                let mut next = Vec::new();
                eval(a, w, cx, &mut next);
                for s in next {
                    if !seen.iter().any(|&x| cx.eng.deep_equal(x, s.term)) {
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
            eval(a, dag, cx, &mut first);
            let star = RStrat::Star(a.clone());
            for s in first {
                eval(&star, s.term, cx, out);
            }
        }
        RStrat::Normalize(a) => {
            // Apply `a` to a fixpoint: a result with no `a`-successor is a normal form.
            let mut next = Vec::new();
            eval(a, dag, cx, &mut next);
            if next.is_empty() {
                out.push(StratSolution { term: dag, rewrites: cx.count });
            } else {
                for s in next {
                    eval(strat, s.term, cx, out);
                }
            }
        }
        RStrat::Branch { test, success, failure } => {
            let mut rs = Vec::new();
            eval(test, dag, cx, &mut rs);
            if rs.is_empty() {
                eval(failure, dag, cx, out);
            } else {
                for s in rs {
                    eval(success, s.term, cx, out);
                }
            }
        }
        RStrat::One(a) => {
            let mut all = Vec::new();
            eval(a, dag, cx, &mut all);
            if let Some(s) = all.into_iter().next() {
                out.push(s);
            }
        }
        RStrat::Test { anywhere, extension, pattern, nr_vars, cond } => {
            if test_holds(cx, pattern, *nr_vars, dag, *anywhere, *extension, cond) {
                out.push(StratSolution { term: dag, rewrites: cx.count }); // a test: no rewrite, original subject
            }
        }
        RStrat::MatchRew { anywhere, pattern, nr_vars, cond, by } => {
            let positions = if *anywhere { all_positions(cx.eng, dag) } else { vec![Vec::new()] };
            for path in &positions {
                let sub = subterm_at(cx.eng, dag, path);
                let base = vec![None; *nr_vars as usize];
                for b in match_extend(cx.eng, pattern, &base, sub, false) {
                    for fb in solve_frags(cx, cond, 0, b, &[], 0) {
                        matchrew_rebuild(cx, dag, path, pattern, &fb, by, out);
                    }
                }
            }
        }
        RStrat::Call(name) => {
            // Look up the definition body; cut on a (dag, name) cycle to terminate recursion.
            let key = (dag, name.clone());
            if cx.seen.contains(&key) {
                return;
            }
            if let Some(body) = cx.defs.get(name) {
                // `body` borrows `cx.defs`; eval needs `cx` mutably, so clone the (small) resolved body.
                let body = body.clone();
                cx.seen.push(key);
                eval(&body, dag, cx, out);
                cx.seen.pop();
            }
        }
    }
}

/// Apply any of `rules` (at the top only, if `top`) to `dag`, honouring the application substitution
/// `app_subst` and rewrite-condition substrategies `substrats`; push each (reduced) result to `out`.
#[allow(clippy::too_many_arguments)]
fn apply_rules(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    app_subst: &[(String, Term)],
    substrats: &[RStrat],
    out: &mut Vec<StratSolution>,
) {
    let positions = if top { vec![Vec::new()] } else { all_positions(cx.eng, dag) };
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let base = vec![None; r.nr_vars as usize];
            for mut b in match_extend(cx.eng, &r.lhs, &base, sub, false) {
                // Honour the initial substitution `[x <- t]`: each named variable is constrained (an lhs
                // variable is checked, an unmatched one is bound) before the condition is solved.
                let mut ok = true;
                for (name, t) in app_subst {
                    let Some(vi) = r.var_names.iter().position(|n| n == name) else {
                        ok = false;
                        break;
                    };
                    let val = inst_reduce(cx, t, &[]);
                    match b[vi] {
                        Some(existing) => {
                            if !cx.eng.deep_equal(existing, val) {
                                ok = false;
                                break;
                            }
                        }
                        None => b[vi] = Some(val),
                    }
                }
                if !ok {
                    continue;
                }
                for fb in solve_frags(cx, &r.condition, 0, b, substrats, 0) {
                    let new_sub = inst(cx, &r.rhs, &fb);
                    let whole = replace_at(cx.eng, dag, path, new_sub);
                    cx.eng.reset_rewrites();
                    let whole = cx.eng.reduce(whole);
                    cx.count += 1 + cx.eng.rewrites(); // the rule application (1) + its result's reductions
                    out.push(StratSolution { term: whole, rewrites: cx.count });
                }
            }
        }
    }
}

/// Solve a rule's / test's condition fragments `frags[i..]` under `bindings`, returning every completed
/// binding vector (the empty condition yields the bindings unchanged). Equality/sort-test fragments are
/// deterministic guards; a matching (`:=`) fragment branches over its solutions; a rewrite (`=>`) fragment is
/// driven by the next substrategy in `substrats` (no substrategy left ⇒ the fragment, hence the application,
/// fails — Maude's bare-label-on-a-rewrite-conditional-rule behaviour).
fn solve_frags(
    cx: &mut Cx,
    frags: &[ConditionFragment],
    i: usize,
    bindings: Vec<Option<DagId>>,
    substrats: &[RStrat],
    sub_idx: usize,
) -> Vec<Vec<Option<DagId>>> {
    let Some(frag) = frags.get(i) else {
        return vec![bindings];
    };
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            let l = inst_reduce(cx, lhs, &bindings);
            let r = inst_reduce(cx, rhs, &bindings);
            if cx.eng.deep_equal(l, r) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::SortTest { term, sort } => {
            let t = inst_reduce(cx, term, &bindings);
            let ls = cx.eng.sort_of(t);
            if cx.eng.sorts().same_kind(ls, *sort) && cx.eng.sorts().leq(ls, *sort) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::Matching { pattern, subject, .. } => {
            let subj = inst_reduce(cx, subject, &bindings);
            let mut out = Vec::new();
            for nb in match_extend(cx.eng, pattern, &bindings, subj, false) {
                out.extend(solve_frags(cx, frags, i + 1, nb, substrats, sub_idx));
            }
            out
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            // A rewrite condition is controlled by the application's next substrategy; absent one, it cannot
            // be solved (the rule does not apply).
            if sub_idx >= substrats.len() {
                return Vec::new();
            }
            let start = inst_reduce(cx, lhs, &bindings);
            let mut states = Vec::new();
            eval(&substrats[sub_idx], start, cx, &mut states);
            let mut out = Vec::new();
            for s in states {
                for nb in match_extend(cx.eng, pattern, &bindings, s.term, false) {
                    out.extend(solve_frags(cx, frags, i + 1, nb, substrats, sub_idx + 1));
                }
            }
            out
        }
    }
}

/// Run each by-variable's substrategy on its bound subterm and rebuild the matchrew pattern for every
/// combination (the first `by` variable varies fastest — Maude's enumeration order). `base` holds the match
/// (+ `such that`) bindings; each combination overwrites the by-variables with their rewritten subterms.
fn matchrew_rebuild(
    cx: &mut Cx,
    root: DagId,
    path: &[usize],
    pattern: &Term,
    base: &[Option<DagId>],
    by: &[(u32, RStrat)],
    out: &mut Vec<StratSolution>,
) {
    let mut sols_per: Vec<Vec<StratSolution>> = Vec::new();
    for (vi, st) in by {
        let subterm = base[*vi as usize].expect("matchrew by-variable bound by the match");
        let mut s = Vec::new();
        eval(st, subterm, cx, &mut s);
        sols_per.push(s);
    }
    let counts: Vec<usize> = sols_per.iter().map(|s| s.len()).collect();
    let total: usize = counts.iter().product();
    for n in 0..total {
        let mut rem = n;
        let mut bnd = base.to_vec();
        for (k, (vi, _)) in by.iter().enumerate() {
            let choice = rem % counts[k];
            rem /= counts[k];
            bnd[*vi as usize] = Some(sols_per[k][choice].term);
        }
        let new_sub = inst(cx, pattern, &bnd);
        let whole = replace_at(cx.eng, root, path, new_sub);
        cx.eng.reset_rewrites();
        let whole = cx.eng.reduce(whole);
        cx.count += cx.eng.rewrites(); // the rewrites came from the substrategies; rebuild adds reductions only
        out.push(StratSolution { term: whole, rewrites: cx.count });
    }
}

/// Whether `pattern` matches `dag` (at the top / with extension / anywhere) with the condition `cond`
/// holding under the match. A test only — no rewrite.
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
            if cond.is_empty() || !solve_frags(cx, cond, 0, b, &[], 0).is_empty() {
                return true;
            }
        }
    }
    false
}

/// Match `pattern` against `subject`, extending `base` (a binding vector over the surrounding variable
/// space): pattern variables not yet bound in `base` are bound; already-bound ones are checked for
/// consistency (`deep_equal`) — the linearize-then-post-check that gives non-linear matching without seeding
/// the kernel matcher. Returns one extended binding vector per solution. `extension` enables AC/AU/S
/// sub-part matching (for `xmatch`).
fn match_extend(
    eng: &mut Engine,
    pattern: &Term,
    base: &[Option<DagId>],
    subject: DagId,
    extension: bool,
) -> Vec<Vec<Option<DagId>>> {
    let mut pvars = Vec::new();
    term_var_indices(pattern, &mut pvars);
    let rpat = renumber_term(pattern, &pvars); // pattern variables → compact 0..pvars.len()
    let m = pvars.len() as u32;
    // Collect the raw (local index → binding) rows while the match stream is live (it borrows the engine).
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
    // Map each row back to the surrounding variable space, checking already-bound variables for consistency.
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
/// variables (admissibility); unbound slots are filled with an arbitrary bound value that is never read.
fn inst(cx: &mut Cx, term: &Term, bindings: &[Option<DagId>]) -> DagId {
    match bindings.iter().flatten().copied().next() {
        None => cx.eng.instantiate_bindings(term, &[]), // ground term
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
