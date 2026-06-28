//! META-LEVEL descent (Phase 3.1) — the [`DescentOps`] implementation.
//!
//! A descent redex (`metaReduce`/…) hands control here via the kernel's [`MetaCtx`] seam. [`MetaDescent`]
//! holds the module database + interner, so it can **down**-translate the meta-module argument into a real
//! object [`LoadedModule`] (a `PreModule` reconstructed from the meta-term, then the ordinary
//! flatten+build pipeline), down-translate the subject meta-term into that module, run the engine
//! operation, and **up**-translate the result back into the meta-level engine (via `ctx`).
//!
//! Scope (Stages 1–3): the whole **rewriting/matching/search family** computes over a down-translated
//! object module — `metaReduce`/`metaNormalize` (→ `ResultPair`), `metaRewrite`/`metaFrewrite` (rule-/
//! position-fair), `metaMatch`/`metaXmatch` (→ `Substitution?`/`MatchPair?` + the hole context),
//! `metaApply`/`metaXapply` (a labelled rule at the top / any position → `ResultTriple?`/`Result4Tuple?`),
//! `metaSearch`/`metaSearchPath` (BFS reachability → `ResultTriple?` / the witness `Trace`). The module
//! argument may be an **import expression** (`[Q]` = `sth Q is including Q . … endsth`) *or* a module with
//! **inline declarations** (sorts/subsorts/attributed ops/membs/eqs/rules) — `down_module` reconstructs the
//! full `PreModule`, runs the ordinary flatten+build, then installs the inline statements via
//! `down_term_to_term` (a `Term`-producing down-translation). Term-level up (`up_term`) and the first of
//! the declaration-level up maps (`up_pattern`/`up_rule`) live here; the rest of the `up*` family
//! (`upModule`/`upSorts`/…) + the sort/kind queries + `metaParse`/`metaPrettyPrint` are Stage 4. Symbolic/
//! SMT/strategy descent stay `MetaOp::Deferred` (Phase 3.2/3.3). Residuals (`gaps.md` / the roadmap):
//! conditional-rule `metaApply` + conditioned `metaMatch` (the condition solver), a non-empty partial
//! substitution, the AC-residue `metaXmatch` context, and `format`-attribute mixfix layout — values and
//! rewrite counts conform throughout.

use std::collections::BTreeSet;

use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::descent::{DescentOps, MetaCtx};
use tnk_core::engine::Engine;
use tnk_core::search::Arrow;
use tnk_core::symbol::{MetaHooks, MetaOp, SymbolId};
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};
use tnk_frontend::build_term::VarIndex;
use tnk_frontend::lex::{tokenize, Interner};
use tnk_frontend::load::{build_loaded_module, LoadedModule};
use tnk_frontend::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use tnk_frontend::surface::ast::{Attrs, Import, ImportMode, ModuleExpr, ModuleKind, OpDecl, PreModule};

use crate::db::ModuleDb;
use crate::flatten::flatten_pre;
use crate::view::ViewDb;

/// The descent handler: the module database/views (to resolve a meta-module's imports) and the interner
/// (to build the object module). Constructed per reduce command and threaded into `reduce_with`.
pub struct MetaDescent<'a> {
    pub interner: &'a mut Interner,
    pub db: &'a ModuleDb,
    pub views: &'a ViewDb,
}

impl DescentOps for MetaDescent<'_> {
    fn descend(
        &mut self,
        ctx: &mut MetaCtx,
        op: MetaOp,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        match op {
            // `metaReduce` and `metaNormalize` differ only in whether membership/sort computation runs;
            // our `reduce` already computes sorts, so both map to the same object reduction here.
            MetaOp::Reduce | MetaOp::Normalize => self.meta_reduce(ctx, hooks, redex),
            // The rewriting/matching/search family (Stage 3): down/up + the engine's rewrite/match/search.
            MetaOp::Rewrite => self.meta_rewrite(ctx, hooks, redex, false),
            MetaOp::Frewrite => self.meta_rewrite(ctx, hooks, redex, true),
            MetaOp::Match => self.meta_match(ctx, hooks, redex),
            MetaOp::Search => self.meta_search(ctx, hooks, redex),
            MetaOp::Apply => self.meta_apply(ctx, hooks, redex),
            MetaOp::Xmatch => self.meta_xmatch(ctx, hooks, redex),
            MetaOp::Xapply => self.meta_xapply(ctx, hooks, redex),
            MetaOp::SearchPath => self.meta_search_path(ctx, hooks, redex),
            _ => None, // Stage 4 (up*/sort queries/parse/print) + Deferred (symbolic/SMT/strategy)
        }
    }
}

impl MetaDescent<'_> {
    /// `metaReduce(M, T)` → `{up(t'), up(leastSort(t'))}` where `t'` is `down(T)` reduced in `down(M)`.
    /// The object reduction's rewrite count is folded into the current command's total (Maude's count).
    fn meta_reduce(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        let subj = down_term(ctx, hooks, kids[1], &mut loaded.built)?;
        loaded.built.engine.reset_rewrites();
        let result = loaded.built.engine.reduce(subj);
        ctx.add_rewrites(loaded.built.engine.rewrites());
        let ut = up_term(ctx, hooks, &loaded.built, result);
        let us = up_sort(ctx, hooks, &loaded.built, result);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// `metaRewrite(M, T, B)` / `metaFrewrite(M, T, B, gas)` → `{up(t'), up(leastSort(t'))}` where `t'` is
    /// `down(T)` rule-rewritten (rule-fair / position-fair) in `down(M)` for up to bound `B` rule steps.
    /// The object run's rewrites (equation reductions + rule applications) fold into the command count.
    fn meta_rewrite(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        position_fair: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let subj = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let bound = down_bound(ctx, hooks, *kids.get(2)?);
        loaded.built.engine.reset_rewrites();
        let result = if position_fair {
            // `metaFrewrite`'s 4th argument is the per-position gas (Maude's `frewrite`).
            let gas = down_nat64(ctx, *kids.get(3)?)?;
            let mut rw = loaded.built.engine.frewrite(subj, gas);
            rw.run(&mut loaded.built.engine, bound).term
        } else {
            let mut rw = loaded.built.engine.rewrite(subj);
            rw.run(&mut loaded.built.engine, bound).term
        };
        ctx.add_rewrites(loaded.built.engine.rewrites());
        let ut = up_term(ctx, hooks, &loaded.built, result);
        let us = up_sort(ctx, hooks, &loaded.built, result);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// `metaMatch(M, P, S, C, n)` → the `(n+1)`-th solution's `Substitution` of matching pattern `P`
    /// against the reduced subject `S` at the top, or `noMatch` (`Substitution?`). The condition `C`
    /// currently must be `nil` (an empty condition); a non-empty such-that is a follow-on.
    fn meta_match(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, &loaded.built, &mut vars)?;
        let subj = down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built)?;
        // The condition (such-that) is handled only when empty for now.
        if !is_nil_condition(ctx, hooks, *kids.get(3)?) {
            return None;
        }
        let sol_nr = down_nat64(ctx, *kids.get(4)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let subj = loaded.built.engine.reduce(subj); // Maude matches against the reduced subject
        ctx.add_rewrites(loaded.built.engine.rewrites());
        // Capture the (n+1)-th solution's bindings while the matcher stream borrows the engine.
        let bindings = nth_match(&mut loaded.built.engine, pattern, nr, subj, false, sol_nr);
        let result = match bindings {
            Some(b) => up_substitution(ctx, hooks, &loaded.built, &var_names(&vars), &b),
            None => ctx.app(*hooks.ops.get("noMatchSubstSymbol")?, vec![]),
        };
        Some(result)
    }

    /// `metaSearch(M, S, P, C, kind, B, n)` → the `(n+1)`-th solution `{up(state), up(type), subst}` of
    /// searching from `S` for a state matching `P` (such that `C`) under reachability `kind` (`'*`/`'+`/
    /// `'!`/`'1`) within depth bound `B`, or `failure` (`ResultTriple?`). The object search's rewrite count
    /// at that solution folds into the command count.
    fn meta_search(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let subj = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(2)?, &loaded.built, &mut vars)?;
        let mut bound_set: BTreeSet<u32> = (0..vars.count()).collect();
        let cond = down_condition(ctx, hooks, *kids.get(3)?, &loaded.built, &mut vars, &mut bound_set)?;
        let arrow = down_arrow(ctx, *kids.get(4)?)?;
        let max_depth = down_bound(ctx, hooks, *kids.get(5)?).map(|d| d as u32);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let mut search = loaded.built.engine.search(subj, pattern, nr, cond, arrow, max_depth);
        let mut sol = None;
        for _ in 0..=sol_nr {
            sol = search.next_solution(&mut loaded.built.engine);
            if sol.is_none() {
                break;
            }
        }
        let result = match sol {
            Some(s) => {
                // Maude reports the rewrite count *at* the solution state (the snapshot), not the total
                // exploration (BFS may have visited siblings first).
                ctx.add_rewrites(s.rewrites);
                let state = search.state_term(s.state)?;
                let ut = up_term(ctx, hooks, &loaded.built, state);
                let us = up_sort(ctx, hooks, &loaded.built, state);
                let subst = up_substitution(ctx, hooks, &loaded.built, &var_names(&vars), &s.bindings);
                ctx.app(*hooks.ops.get("resultTripleSymbol")?, vec![ut, us, subst])
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure3Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaApply(M, T, L, σ, n)` → the `(n+1)`-th application of a rule labelled `L` at the **top** of the
    /// reduced `T` (extending the partial substitution σ) → `{up(reduced rhs), up(type), up(σ ∪ match)}`,
    /// or `failure` (`ResultTriple?`). The rule application itself counts one rewrite (Maude's accounting),
    /// on top of the subject and result reductions. σ currently must be empty (`none`) and the labelled
    /// rules unconditional — a partial substitution and conditional-rule application are follow-ons (the
    /// latter needs the condition solver, shared with conditioned `metaMatch`).
    fn meta_apply(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let subj = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let label = match ctx.repr(*kids.get(2)?) {
            NodeRepr::Qid(s) => s.to_string(),
            _ => return None,
        };
        if !is_empty_subst(ctx, hooks, *kids.get(3)?) {
            return None; // a non-empty partial substitution is a follow-on
        }
        let sol_nr = down_nat64(ctx, *kids.get(4)?)? as usize;
        // The labelled rules (cloned out before mutating the engine). Conditional rules need the condition
        // solver — bail rather than misapply (a conditional rule whose condition fails must not fire).
        let rules: Vec<(Term, Term, Vec<String>, u32)> = loaded
            .built
            .rl_traces
            .iter()
            .filter(|t| t.label.as_deref() == Some(label.as_str()))
            .map(|t| (t.lhs.clone(), t.rhs.clone(), t.var_names.clone(), t.var_names.len() as u32))
            .collect();
        if loaded.built.rl_traces.iter().any(|t| {
            t.label.as_deref() == Some(label.as_str()) && !t.condition.is_empty()
        }) {
            return None;
        }
        loaded.built.engine.reset_rewrites();
        let subj = loaded.built.engine.reduce(subj);
        // Enumerate top matches across the labelled rules (in declaration order), pick the (n+1)-th.
        let mut all: Vec<(usize, Vec<DagId>)> = Vec::new();
        for (ri, (lhs, _, _, nr)) in rules.iter().enumerate() {
            let mut sols = loaded.built.engine.match_solutions(lhs.clone(), *nr, subj, false);
            while sols.advance() {
                let b: Vec<DagId> =
                    (0..*nr).map(|k| sols.binding(k).expect("matcher binds every var")).collect();
                all.push((ri, b));
            }
        }
        let result = match all.get(sol_nr) {
            Some((ri, bindings)) => {
                let (_, rhs, names, _) = &rules[*ri];
                let res = loaded.built.engine.instantiate_bindings(rhs, bindings);
                let res = loaded.built.engine.reduce(res);
                // subject reduce + result reduce + the rule application (1).
                ctx.add_rewrites(loaded.built.engine.rewrites() + 1);
                let ut = up_term(ctx, hooks, &loaded.built, res);
                let us = up_sort(ctx, hooks, &loaded.built, res);
                let subst = up_substitution(ctx, hooks, &loaded.built, names, bindings);
                ctx.app(*hooks.ops.get("resultTripleSymbol")?, vec![ut, us, subst])
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure3Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaXmatch(M, P, S, C, minD, maxD, n)` → the `(n+1)`-th **extension** match of `P` against the
    /// reduced `S` at the top → `{substitution, context}` (`MatchPair`), or `noMatch`. When the match
    /// consumes the whole subject (a free/iterated top, or every AC argument bound) the context is the bare
    /// hole `[]`; a *partial* AC match (a proper sub-multiset, leaving a residue context `op([], …)`) is a
    /// follow-on — it stays inert rather than report a wrong context. `C` must be `nil`.
    fn meta_xmatch(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, &loaded.built, &mut vars)?;
        let subj = down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built)?;
        if !is_nil_condition(ctx, hooks, *kids.get(3)?) {
            return None;
        }
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let subj = loaded.built.engine.reduce(subj);
        ctx.add_rewrites(loaded.built.engine.rewrites());
        match nth_xmatch(&mut loaded.built.engine, pattern, nr, subj, sol_nr) {
            Some((bindings, whole)) => {
                if !whole {
                    return None; // partial AC match — residue context is a follow-on
                }
                let subst = up_substitution(ctx, hooks, &loaded.built, &var_names(&vars), &bindings);
                let context = ctx.app(*hooks.ops.get("holeSymbol")?, vec![]);
                Some(ctx.app(*hooks.ops.get("matchPairSymbol")?, vec![subst, context]))
            }
            None => Some(ctx.app(*hooks.ops.get("noMatchPairSymbol")?, vec![])),
        }
    }

    /// `metaXapply(M, T, L, σ, minD, maxD, n)` → the `(n+1)`-th application of a rule labelled `L` at **any
    /// position** of the reduced `T` whose depth is in `[minD, maxD]` → `{up(whole result), up(type),
    /// up(match), context}` (`Result4Tuple`), or `failure`. The context is the subject with the rewritten
    /// position replaced by the hole `[]` (`'f[[]]`, …). Positions are enumerated outermost-first. σ must
    /// be `none` and the labelled rules unconditional (as for [`meta_apply`](Self::meta_apply)); the
    /// match at each position is exact (free-theory) — AC sub-multiset application is a follow-on.
    fn meta_xapply(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let subj0 = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let label = match ctx.repr(*kids.get(2)?) {
            NodeRepr::Qid(s) => s.to_string(),
            _ => return None,
        };
        if !is_empty_subst(ctx, hooks, *kids.get(3)?) {
            return None;
        }
        let min_d = down_nat64(ctx, *kids.get(4)?)? as usize;
        let max_d = down_bound(ctx, hooks, *kids.get(5)?);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let rules: Vec<(Term, Term, Vec<String>, u32)> = loaded
            .built
            .rl_traces
            .iter()
            .filter(|t| t.label.as_deref() == Some(label.as_str()))
            .map(|t| (t.lhs.clone(), t.rhs.clone(), t.var_names.clone(), t.var_names.len() as u32))
            .collect();
        if loaded.built.rl_traces.iter().any(|t| {
            t.label.as_deref() == Some(label.as_str()) && !t.condition.is_empty()
        }) {
            return None;
        }
        loaded.built.engine.reset_rewrites();
        let subj = loaded.built.engine.reduce(subj0);
        // Positions within the depth band, outermost-first; at each, every labelled rule's top matches.
        let mut positions = Vec::new();
        collect_positions(&loaded.built.engine, subj, 0, &mut Vec::new(), min_d, max_d, &mut positions);
        let mut all: Vec<(Vec<usize>, usize, Vec<DagId>)> = Vec::new();
        for path in &positions {
            let subterm = subterm_at(&loaded.built.engine, subj, path);
            for (ri, (lhs, _, _, nr)) in rules.iter().enumerate() {
                let mut sols = loaded.built.engine.match_solutions(lhs.clone(), *nr, subterm, false);
                while sols.advance() {
                    let b: Vec<DagId> =
                        (0..*nr).map(|k| sols.binding(k).expect("matcher binds every var")).collect();
                    all.push((path.clone(), ri, b));
                }
            }
        }
        let result = match all.get(sol_nr) {
            Some((path, ri, bindings)) => {
                let (_, rhs, names, _) = &rules[*ri];
                let new_sub = loaded.built.engine.instantiate_bindings(rhs, bindings);
                let whole = replace_at(&mut loaded.built.engine, subj, path, new_sub);
                let whole = loaded.built.engine.reduce(whole);
                ctx.add_rewrites(loaded.built.engine.rewrites() + 1);
                let ut = up_term(ctx, hooks, &loaded.built, whole);
                let us = up_sort(ctx, hooks, &loaded.built, whole);
                let subst = up_substitution(ctx, hooks, &loaded.built, names, bindings);
                let context = up_context(ctx, hooks, &loaded.built, subj, path);
                ctx.app(*hooks.ops.get("result4TupleSymbol")?, vec![ut, us, subst, context])
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure4Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaSearchPath(M, S, P, C, kind, B, n)` → the `Trace` of the breadth-first path to the `(n+1)`-th
    /// search solution: one `{up(state), up(type), up(rule)}` `TraceStep` per arc (the state and the rule
    /// that leaves it), joined by `__`, or `nil` for a zero-length path; `failure` (`Trace?`) when there is
    /// no such solution. Reuses the same search as [`meta_search`](Self::meta_search); the rules are
    /// up-translated by [`up_rule`] (unconditional here — see its note).
    fn meta_search_path(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let subj = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(2)?, &loaded.built, &mut vars)?;
        let mut bound_set: BTreeSet<u32> = (0..vars.count()).collect();
        let cond = down_condition(ctx, hooks, *kids.get(3)?, &loaded.built, &mut vars, &mut bound_set)?;
        let arrow = down_arrow(ctx, *kids.get(4)?)?;
        let max_depth = down_bound(ctx, hooks, *kids.get(5)?).map(|d| d as u32);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let mut search = loaded.built.engine.search(subj, pattern, nr, cond, arrow, max_depth);
        let mut sol = None;
        for _ in 0..=sol_nr {
            sol = search.next_solution(&mut loaded.built.engine);
            if sol.is_none() {
                break;
            }
        }
        let Some(s) = sol else {
            ctx.add_rewrites(loaded.built.engine.rewrites());
            return Some(ctx.app(*hooks.ops.get("failureTraceSymbol")?, vec![]));
        };
        ctx.add_rewrites(s.rewrites);
        let steps = search.path(s.state);
        // One TraceStep per arc: state `steps[i]` and the rule that produced its successor `steps[i+1]`.
        let mut trace_steps = Vec::new();
        for i in 0..steps.len().saturating_sub(1) {
            let rule_id = steps[i + 1].via? as usize;
            let ut = up_term(ctx, hooks, &loaded.built, steps[i].term);
            let us = up_sort(ctx, hooks, &loaded.built, steps[i].term);
            let rule = up_rule(ctx, hooks, &loaded.built, &loaded.built.rl_traces[rule_id])?;
            trace_steps.push(ctx.app(*hooks.ops.get("traceStepSymbol")?, vec![ut, us, rule]));
        }
        Some(match trace_steps.len() {
            0 => ctx.app(*hooks.ops.get("nilTraceSymbol")?, vec![]),
            1 => trace_steps.into_iter().next().unwrap(),
            _ => ctx.app(*hooks.ops.get("traceSymbol")?, trace_steps),
        })
    }

    /// Down-translate a meta-module term to an object [`LoadedModule`]: reconstruct its `PreModule`
    /// (imports + sorts + subsorts + ops), run the ordinary flatten (against the db) + build, then
    /// install its inline memberships/equations/rules by down-translating their meta-terms directly into
    /// the built engine. Handles both the **import-expression** form (`[Q]` — sorts/ops/equations all
    /// `none`) and a module with **inline declarations** (what `upModule` emits, or a hand-written one).
    fn down_module(
        &mut self,
        ctx: &MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
    ) -> Option<LoadedModule> {
        let ctor = ctx.name(ctx.top(m)).to_string();
        let (kind, is_theory) = module_kind(&ctor)?;
        let kids = ctx.children(m);
        // Constructor layout: [0]=Header(Qid), [1]=ImportList, [2]=SortSet, [3]=SubsortDeclSet,
        // [4]=OpDeclSet, [5]=MembAxSet, [6]=EquationSet, [7]=RuleSet (system only), [8,9]=Strat* (smod).
        let imports = down_imports(ctx, hooks, *kids.get(1)?)?;
        let sorts = down_sorts(ctx, hooks, *kids.get(2)?);
        let subsorts = down_subsorts(ctx, hooks, *kids.get(3)?);
        let mut ops = down_ops(ctx, hooks, *kids.get(4)?, self.interner)?;
        // Declare constants (arity 0) first: `build_module` resolves an `id(c)`/`left-id`/`right-id`
        // identity against the *already-declared* ops, but the meta `OpDeclSet` is an AU multiset whose
        // canonical order need not place the identity constant before the operator that names it (e.g.
        // `__`'s `id(nil)` with `__` ordered before `nil`). A stable constants-first sort guarantees every
        // identity constant exists when its operator is declared, without disturbing same-arity order.
        ops.sort_by_key(|o| !o.domain.is_empty());
        let pm = PreModule {
            name: "%META%".to_string(),
            kind,
            is_theory,
            params: Vec::new(),
            imports,
            sorts,
            subsorts,
            ops,
            vars: Vec::new(),
            statements: Vec::new(), // inline statements are down-translated post-build (below)
        };
        let flat = flatten_pre(&pm, self.db, self.views, self.interner).ok()?;
        let mut loaded = build_loaded_module(&flat, self.interner).ok()?;
        // Install this module's own inline declarations (the imports' statements came through `flatten`,
        // parsed by `build_loaded_module`; these are reconstructed straight from their meta-terms).
        install_membs(ctx, hooks, *kids.get(5)?, &mut loaded.built)?;
        install_eqs(ctx, hooks, *kids.get(6)?, &mut loaded.built)?;
        if kind == ModuleKind::System {
            install_rules(ctx, hooks, *kids.get(7)?, &mut loaded.built)?;
        }
        Some(loaded)
    }
}

/// The (kind, is_theory) of a module-constructor operator name (`fmod_is_sorts_.____endfm`, `sth_…`, …).
fn module_kind(ctor: &str) -> Option<(ModuleKind, bool)> {
    if ctor.starts_with("fmod") {
        Some((ModuleKind::Functional, false))
    } else if ctor.starts_with("fth") {
        Some((ModuleKind::Functional, true))
    } else if ctor.starts_with("smod") || ctor.starts_with("mod") {
        Some((ModuleKind::System, false))
    } else if ctor.starts_with("sth") || ctor.starts_with("th") {
        Some((ModuleKind::System, true))
    } else {
        None
    }
}

// ---- inline declaration down-translation (sorts / subsorts / ops / membs / eqs / rules) ----

/// The text of a `Qid` leaf (a meta sort/op/variable name), or `None` if `d` is not a `Qid`.
fn qid_text(ctx: &MetaCtx, d: DagId) -> Option<String> {
    match ctx.repr(d) {
        NodeRepr::Qid(s) => Some(s.to_string()),
        _ => None,
    }
}

/// Flatten a meta declaration set joined by a binary constructor `join` (`__`/`_;_`) into its element
/// DAGs in left-to-right order, dropping the `empty` constant (`none`/`nil`). A single element, the empty
/// constant, or a (AU/ACU-canonicalized) tree of `join` all collapse to a flat element list.
fn flatten_set(ctx: &MetaCtx, d: DagId, empty: Option<SymbolId>, join: Option<SymbolId>) -> Vec<DagId> {
    fn go(ctx: &MetaCtx, d: DagId, empty: Option<SymbolId>, join: Option<SymbolId>, out: &mut Vec<DagId>) {
        let sym = Some(ctx.top(d));
        if sym == empty {
            return;
        }
        if sym == join {
            for c in ctx.children(d) {
                go(ctx, c, empty, join, out);
            }
            return;
        }
        out.push(d);
    }
    let mut out = Vec::new();
    go(ctx, d, empty, join, &mut out);
    out
}

/// A meta `SortSet` (`none` | `_;_`-joined sort `Qid`s) → the sort name strings.
fn down_sorts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<String> {
    let empty = hooks.ops.get("emptySortSetSymbol").copied();
    let join = hooks.ops.get("sortSetSymbol").copied();
    flatten_set(ctx, d, empty, join).iter().filter_map(|&x| qid_text(ctx, x)).collect()
}

/// A meta `SubsortDeclSet` (`none` | `__`-joined `subsort A < B .`) → the surface chain form (each decl a
/// two-level chain `[[A], [B]]`).
fn down_subsorts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<Vec<Vec<String>>> {
    let empty = hooks.ops.get("emptySubsortDeclSetSymbol").copied();
    let join = hooks.ops.get("subsortDeclSetSymbol").copied();
    let subsort = hooks.ops.get("subsortSymbol").copied();
    let mut out = Vec::new();
    for decl in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(decl)) != subsort {
            continue;
        }
        let kids = ctx.children(decl);
        if let (Some(a), Some(b)) =
            (kids.first().and_then(|&x| qid_text(ctx, x)), kids.get(1).and_then(|&x| qid_text(ctx, x)))
        {
            out.push(vec![vec![a], vec![b]]);
        }
    }
    out
}

/// A meta `OpDeclSet` (`none` | `__`-joined `op N : D -> R [A] .`) → surface [`OpDecl`]s. `None` on an
/// unexpected element or an op-attribute we do not reconstruct for an own-op (see [`down_attrs`]).
fn down_ops(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, i: &mut Interner) -> Option<Vec<OpDecl>> {
    let empty = hooks.ops.get("emptyOpDeclSetSymbol").copied();
    let join = hooks.ops.get("opDeclSetSymbol").copied();
    let opdecl = hooks.ops.get("opDeclSymbol").copied();
    let mut out = Vec::new();
    for decl in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(decl)) != opdecl {
            return None;
        }
        let kids = ctx.children(decl); // [name, typelist, range, attrset]
        let name_str = qid_text(ctx, *kids.first()?)?;
        let domain = down_typelist(ctx, hooks, *kids.get(1)?);
        let range = qid_text(ctx, *kids.get(2)?)?;
        let attrs = down_attrs(ctx, hooks, *kids.get(3)?, i)?;
        out.push(OpDecl { name: tokenize(&name_str, i), domain, range, partial: false, attrs });
    }
    Some(out)
}

/// A meta `TypeList` (`nil` | `__`-joined type `Qid`s) → the sort/kind name strings.
fn down_typelist(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<String> {
    let empty = hooks.ops.get("nilQidListSymbol").copied();
    let join = hooks.ops.get("qidListSymbol").copied();
    flatten_set(ctx, d, empty, join).iter().filter_map(|&x| qid_text(ctx, x)).collect()
}

/// A meta `AttrSet` → surface [`Attrs`]. Reconstructs the structural attributes (`ctor`/`assoc`/`comm`/
/// `idem`/`iter`/`id:`/`prec`); drops the print/metadata-only ones; and returns `None` on a semantic
/// attribute we do not yet rebuild for a module's *own* op (`special`/`frozen`/`strat`/`poly`/… — which in
/// practice arrive through imports, already built). The statement attributes `owise`/`nonexec`/`label`
/// are read separately where the statement is installed.
fn down_attrs(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, i: &mut Interner) -> Option<Attrs> {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let mut a = Attrs::default();
    for attr in flatten_set(ctx, d, empty, join) {
        let sym = ctx.top(attr);
        let is = |name: &str| hooks.ops.get(name).copied() == Some(sym);
        if is("ctorSymbol") {
            a.ctor = true;
        } else if is("assocSymbol") {
            a.assoc = true;
        } else if is("commSymbol") {
            a.comm = true;
        } else if is("idemSymbol") {
            a.idem = true;
        } else if is("iterSymbol") {
            a.iter = true;
        } else if is("idSymbol") || is("leftIdSymbol") || is("rightIdSymbol") {
            // `id:`/`left-id:`/`right-id:` <term> — a single identity constant in practice; carry its name.
            a.id = Some(id_bubble(ctx, *ctx.children(attr).first()?, i)?);
        } else if is("precSymbol") {
            a.prec = down_nat(ctx, *ctx.children(attr).first()?);
        } else if is("gatherSymbol")
            || is("formatSymbol")
            || is("metadataSymbol")
            || is("latexSymbol")
            || is("memoSymbol")
            || is("printSymbol")
            || is("dittoSymbol")
        {
            // printing / metadata / memo — no effect on reduction; safe to drop.
        } else {
            return None; // a semantic attribute we do not yet reconstruct for an own-op
        }
    }
    Some(a)
}

/// The `id:`-attribute bubble for an identity constant `'name.Sort`: its name as a single token (what
/// `declare_op` resolves against `name_to_sym`).
fn id_bubble(ctx: &MetaCtx, t: DagId, i: &mut Interner) -> Option<Vec<tnk_frontend::lex::Token>> {
    let text = qid_text(ctx, t)?;
    let name = text.rsplit_once('.').map(|(n, _)| n).unwrap_or(&text);
    Some(tokenize(name, i))
}

/// A meta `Nat` (`'0.Zero`, `'s_^n['0.Zero]`, or a NAT numeral) → its `u32` value (for `prec`).
fn down_nat(ctx: &MetaCtx, d: DagId) -> Option<u32> {
    match ctx.repr(d) {
        NodeRepr::Iter { count, .. } => count.parse().ok(),
        _ => Some(0), // the zero constant
    }
}

/// Whether a meta `AttrSet` contains the attribute with hook purpose `hook` (`owiseSymbol`/`nonexecSymbol`).
fn attrset_has(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, hook: &str) -> bool {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let target = hooks.ops.get(hook).copied();
    target.is_some() && flatten_set(ctx, d, empty, join).iter().any(|&x| Some(ctx.top(x)) == target)
}

/// The `label(Q)` of a rule's meta `AttrSet`, if present.
fn attrset_label(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<String> {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let label = hooks.ops.get("labelSymbol").copied();
    for attr in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(attr)) == label {
            return qid_text(ctx, *ctx.children(attr).first()?);
        }
    }
    None
}

/// Install a meta `MembAxSet`'s memberships into the built engine (down-translating each `mb`/`cmb`).
fn install_membs(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, m: &mut BuiltModule) -> Option<()> {
    let empty = hooks.ops.get("emptyMembAxSetSymbol").copied();
    let join = hooks.ops.get("membAxSetSymbol").copied();
    let mb = hooks.ops.get("mbSymbol").copied();
    let cmb = hooks.ops.get("cmbSymbol").copied();
    for stmt in flatten_set(ctx, d, empty, join) {
        let sym = Some(ctx.top(stmt));
        let kids = ctx.children(stmt);
        let mut vars = VarIndex::new();
        let (lhs, sort_id, condition, attrs) = if sym == mb {
            // mb lhs : Sort [attrs]
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            (lhs, sort, Vec::new(), *kids.get(2)?)
        } else if sym == cmb {
            // cmb lhs : Sort if cond [attrs]
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
            (lhs, sort, cond, *kids.get(3)?)
        } else {
            return None;
        };
        if attrset_has(ctx, hooks, attrs, "nonexecSymbol") {
            continue;
        }
        let nr = vars.count();
        let var_names = (0..nr).map(|k| vars.name(k).to_string()).collect();
        let trace = MbTrace { lhs: lhs.clone(), sort: sort_id, condition: condition.clone(), var_names };
        let id = if condition.is_empty() {
            m.engine.add_membership(Membership { lhs, sort: sort_id, nr_vars: nr })
        } else {
            m.engine.add_conditional_membership(lhs, sort_id, nr, condition)
        };
        assert_eq!(id as usize, m.mb_traces.len(), "membership id is the dense mb_traces index");
        m.mb_traces.push(trace);
    }
    Some(())
}

/// Install a meta `EquationSet`'s equations into the built engine (down-translating each `eq`/`ceq`).
fn install_eqs(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, m: &mut BuiltModule) -> Option<()> {
    let empty = hooks.ops.get("emptyEquationSetSymbol").copied();
    let join = hooks.ops.get("equationSetSymbol").copied();
    let eq = hooks.ops.get("eqSymbol").copied();
    let ceq = hooks.ops.get("ceqSymbol").copied();
    for stmt in flatten_set(ctx, d, empty, join) {
        let sym = Some(ctx.top(stmt));
        let kids = ctx.children(stmt);
        let mut vars = VarIndex::new();
        // Build order lhs → condition → rhs, sharing one variable index (matches Maude's numbering).
        let (lhs, rhs, condition, attrs) = if sym == eq {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
            (lhs, rhs, Vec::new(), *kids.get(2)?)
        } else if sym == ceq {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
            (lhs, rhs, cond, *kids.get(3)?)
        } else {
            return None;
        };
        if attrset_has(ctx, hooks, attrs, "nonexecSymbol") {
            continue;
        }
        let owise = attrset_has(ctx, hooks, attrs, "owiseSymbol");
        let nr = vars.count();
        let var_names = (0..nr).map(|k| vars.name(k).to_string()).collect();
        let trace =
            EqTrace { lhs: lhs.clone(), rhs: rhs.clone(), condition: condition.clone(), var_names, owise };
        let id = if owise {
            m.engine.add_owise_equation(lhs, rhs, nr, condition)
        } else if condition.is_empty() {
            m.engine.add_equation(Equation { lhs, rhs, nr_vars: nr })
        } else {
            m.engine.add_conditional_equation(lhs, rhs, nr, condition)
        };
        assert_eq!(id as usize, m.eq_traces.len(), "equation id is the dense eq_traces index");
        m.eq_traces.push(trace);
    }
    Some(())
}

/// Install a meta `RuleSet`'s rules into the built engine (down-translating each `rl`/`crl`).
fn install_rules(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, m: &mut BuiltModule) -> Option<()> {
    let empty = hooks.ops.get("emptyRuleSetSymbol").copied();
    let join = hooks.ops.get("ruleSetSymbol").copied();
    let rl = hooks.ops.get("rlSymbol").copied();
    let crl = hooks.ops.get("crlSymbol").copied();
    for stmt in flatten_set(ctx, d, empty, join) {
        let sym = Some(ctx.top(stmt));
        let kids = ctx.children(stmt);
        let mut vars = VarIndex::new();
        let (lhs, rhs, condition, attrs) = if sym == rl {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
            (lhs, rhs, Vec::new(), *kids.get(2)?)
        } else if sym == crl {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
            (lhs, rhs, cond, *kids.get(3)?)
        } else {
            return None;
        };
        if attrset_has(ctx, hooks, attrs, "nonexecSymbol") {
            continue;
        }
        let label = attrset_label(ctx, hooks, attrs);
        let nr = vars.count();
        let var_names = (0..nr).map(|k| vars.name(k).to_string()).collect();
        let trace =
            RlTrace { lhs: lhs.clone(), rhs: rhs.clone(), condition: condition.clone(), var_names, label };
        let id = if condition.is_empty() {
            m.engine.add_rule(lhs, rhs, nr)
        } else {
            m.engine.add_conditional_rule(lhs, rhs, nr, condition)
        };
        assert_eq!(id as usize, m.rl_traces.len(), "rule id is the dense rl_traces index");
        m.rl_traces.push(trace);
    }
    Some(())
}

/// Down-translate a meta `Condition`/`EqCondition` into kernel [`ConditionFragment`]s. `nil` is the empty
/// condition; `_/\_` conjoins; each fragment is `_=_`/`_:_`/`_:=_`/`_=>_`. Shares the statement's `vars`;
/// a `:=`/`=>` fragment's fresh variables are those its pattern introduces (not already in `bound`).
fn down_condition(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    m: &BuiltModule,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Option<Vec<ConditionFragment>> {
    let nil = hooks.ops.get("noConditionSymbol").copied();
    let conj = hooks.ops.get("conjunctionSymbol").copied();
    let eq_c = hooks.ops.get("equalityConditionSymbol").copied();
    let sort_c = hooks.ops.get("sortTestConditionSymbol").copied();
    let match_c = hooks.ops.get("matchConditionSymbol").copied();
    let rw_c = hooks.ops.get("rewriteConditionSymbol").copied();
    let fragments = flatten_set(ctx, d, nil, conj);
    let mut out = Vec::with_capacity(fragments.len());
    for f in fragments {
        let sym = Some(ctx.top(f));
        let kids = ctx.children(f);
        let frag = if sym == eq_c {
            ConditionFragment::Equality {
                lhs: down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?,
                rhs: down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?,
            }
        } else if sym == sort_c {
            let term = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            ConditionFragment::SortTest { term, sort }
        } else if sym == match_c {
            let pattern = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let subject = down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?;
            let fresh = fresh_vars(&pattern, bound);
            ConditionFragment::Matching { pattern, subject, fresh_vars: fresh }
        } else if sym == rw_c {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?;
            let fresh = fresh_vars(&pattern, bound);
            ConditionFragment::Rewrite { lhs, pattern, fresh_vars: fresh }
        } else {
            return None;
        };
        out.push(frag);
    }
    Some(out)
}

/// The pattern's variable indices not already in `bound` (the fresh ones a `:=`/`=>` fragment binds);
/// extends `bound` with all of them.
fn fresh_vars(pat: &Term, bound: &mut BTreeSet<u32>) -> Vec<u32> {
    let mut idx = Vec::new();
    term_var_indices(pat, &mut idx);
    let fresh: Vec<u32> = idx.iter().copied().filter(|v| !bound.contains(v)).collect();
    bound.extend(idx);
    fresh
}

/// Collect a term's distinct variable indices, in first-seen order.
fn term_var_indices(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {}
        Term::Op { args, .. } => {
            for a in args {
                term_var_indices(a, out);
            }
        }
    }
}

/// Down-translate a meta-term into a kernel [`Term`] (a pattern / statement side) over `target`. Like
/// [`down_term`] but yields a static `Term`: a meta variable `'X:Sort` becomes an indexed `Term::Var`
/// (tracked in `vars`, keyed by the full meta name so `'X:Nat` and `'X:Int` stay distinct), a constant
/// `'c.S` an arity-0 `Term::Op`, an application `'f[args]` a `Term::Op`, and the iterated `'s_^n[t]` an
/// `n`-deep successor chain (the kernel folds it to a compact `s^n` node downstream).
fn down_term_to_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    t: DagId,
    target: &BuiltModule,
    vars: &mut VarIndex,
) -> Option<Term> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    match ctx.repr(t) {
        NodeRepr::Qid(text) => down_leaf_to_term(text, target, vars),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let head = qid_text(ctx, *kids.first()?)?;
            let args = down_arglist_to_term(ctx, hooks, *kids.get(1)?, target, vars)?;
            build_app_term(&head, args, target)
        }
        _ => None,
    }
}

/// A meta-term leaf `'X:Sort` (variable) or `'c.Sort` (constant) → a kernel [`Term`].
fn down_leaf_to_term(text: &str, target: &BuiltModule, vars: &mut VarIndex) -> Option<Term> {
    if let Some(colon) = text.find(':') {
        // Variable: a name can hold no `:` and a sort no `:`, so the first `:` splits name from sort.
        let sort = *target.sorts.get(&text[colon + 1..])?;
        Some(Term::var(vars.index_of(text, sort), sort))
    } else if let Some(dot) = text.rfind('.') {
        // Constant `name.Sort`: look up the arity-0 operator (literal NA constants are a follow-up).
        let sym = *target.ops.get(&(text[..dot].to_string(), 0))?;
        Some(Term::constant(sym))
    } else {
        None
    }
}

/// Down-translate a `metaTermSymbol` argument list (a `metaArgSymbol` `_,_` flattens to its elements;
/// anything else is a single argument) to kernel [`Term`]s.
fn down_arglist_to_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    list: DagId,
    target: &BuiltModule,
    vars: &mut VarIndex,
) -> Option<Vec<Term>> {
    let arg_sym = hooks.ops.get("metaArgSymbol").copied();
    if Some(ctx.top(list)) == arg_sym {
        ctx.children(list).into_iter().map(|c| down_term_to_term(ctx, hooks, c, target, vars)).collect()
    } else {
        Some(vec![down_term_to_term(ctx, hooks, list, target, vars)?])
    }
}

/// Build a kernel [`Term`] application from a meta op-name + down-translated args: an iterated name
/// `base^n` wraps the argument in `n` nested successor `Term::Op`s; otherwise the operator is `(name, arity)`.
fn build_app_term(head: &str, args: Vec<Term>, target: &BuiltModule) -> Option<Term> {
    if let Some((base, count)) = head.rsplit_once('^')
        && let Ok(n) = count.parse::<u64>()
    {
        let sym = *target.ops.get(&(base.to_string(), 1))?;
        let mut t = args.into_iter().next()?;
        for _ in 0..n {
            t = Term::op(sym, vec![t]);
        }
        return Some(t);
    }
    let sym = *target.ops.get(&(head.to_string(), args.len()))?;
    Some(Term::op(sym, args))
}

/// Down-translate an `ImportList` (`__`-flattened `including_.`/`protecting_.`/`extending_.` of a module
/// expression) to a list of [`Import`]s. Only a **named** module expression (a `Qid`) is handled.
fn down_imports(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Option<Vec<Import>> {
    let nil = hooks.ops.get("nilImportListSymbol").copied();
    let cons = hooks.ops.get("importListSymbol").copied();
    let mut out = Vec::new();
    let mut stack = vec![list];
    while let Some(d) = stack.pop() {
        let sym = ctx.top(d);
        if Some(sym) == nil {
            continue;
        }
        if Some(sym) == cons {
            // `__` import list — recurse into its elements (children are already flattened by the AU rep).
            stack.extend(ctx.children(d));
            continue;
        }
        out.push(down_import(ctx, hooks, d)?);
    }
    out.reverse();
    Some(out)
}

/// Down-translate one import `including_./protecting_./extending_.(ModuleExpr)`.
fn down_import(ctx: &MetaCtx, hooks: &MetaHooks, imp: DagId) -> Option<Import> {
    let sym = ctx.top(imp);
    let mode = if hooks.ops.get("protectingSymbol") == Some(&sym) {
        ImportMode::Protecting
    } else if hooks.ops.get("extendingSymbol") == Some(&sym) {
        ImportMode::Extending
    } else if hooks.ops.get("includingSymbol") == Some(&sym)
        || hooks.ops.get("generatedBySymbol") == Some(&sym)
    {
        ImportMode::Including
    } else {
        return None;
    };
    let expr = *ctx.children(imp).first()?;
    Some(Import { mode, expr: down_module_expr(ctx, expr)? })
}

/// Down-translate a module expression. Only a named module (a `Qid` leaf) is handled here.
fn down_module_expr(ctx: &MetaCtx, e: DagId) -> Option<ModuleExpr> {
    match ctx.repr(e) {
        NodeRepr::Qid(name) => Some(ModuleExpr::Named(name.to_string())),
        _ => None,
    }
}

// ---- down/up of terms ----

/// Down-translate a meta-term into a DAG in `target` (the object module). Handles a constant `'c.S`
/// (a `Qid` leaf), an application `'f[args]` (a `metaTermSymbol` node), and the iterated form `'s_^n[t]`.
fn down_term(ctx: &MetaCtx, hooks: &MetaHooks, t: DagId, target: &mut BuiltModule) -> Option<DagId> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    match ctx.repr(t) {
        NodeRepr::Qid(text) => down_constant(text, target),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let head = match ctx.repr(*kids.first()?) {
                NodeRepr::Qid(s) => s.to_string(),
                _ => return None,
            };
            let args = down_arglist(ctx, hooks, *kids.get(1)?, target)?;
            build_app(&head, args, target)
        }
        _ => None,
    }
}

/// Down-translate a `metaTermSymbol` argument list — a `metaArgSymbol` (`_,_`) AU node flattens to its
/// elements; anything else is a single argument.
fn down_arglist(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    list: DagId,
    target: &mut BuiltModule,
) -> Option<Vec<DagId>> {
    let arg_sym = hooks.ops.get("metaArgSymbol").copied();
    if Some(ctx.top(list)) == arg_sym {
        ctx.children(list).into_iter().map(|c| down_term(ctx, hooks, c, target)).collect()
    } else {
        Some(vec![down_term(ctx, hooks, list, target)?])
    }
}

/// Build a constant from a meta `'name.sort` (a `Qid` leaf): look up the arity-0 operator `name`.
fn down_constant(text: &str, target: &mut BuiltModule) -> Option<DagId> {
    let (name, _sort) = text.rsplit_once('.')?;
    let sym = *target.ops.get(&(name.to_string(), 0))?;
    Some(target.engine.make_const(sym))
}

/// Build an application from a meta op-name + down-translated args. An iterated name `base^n` builds the
/// `iter` successor `base^n(arg)`; otherwise the operator is looked up by `(name, arity)`.
fn build_app(head: &str, args: Vec<DagId>, target: &mut BuiltModule) -> Option<DagId> {
    if let Some((base, count)) = head.rsplit_once('^')
        && let Ok(n) = count.parse::<u64>()
    {
        let sym = *target.ops.get(&(base.to_string(), 1))?;
        return Some(target.engine.make_iter(sym, n, *args.first()?));
    }
    let sym = *target.ops.get(&(head.to_string(), args.len()))?;
    Some(target.engine.make_node(sym, args))
}

/// Up-translate an object DAG `t` (in `source`) into a meta-term built in `ctx`.
fn up_term(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match source.engine.node(t).repr() {
        NodeRepr::App => {
            let sym = source.engine.node(t).symbol();
            let name = source.engine.symbol(sym).name().to_string();
            let kids: Vec<DagId> = source.engine.node(t).children().collect();
            if kids.is_empty() {
                // a constant → `'name.sort`
                let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
                ctx.make_na(qid, NaValue::Qid(format!("{name}.{sort}").into()))
            } else {
                let up_args: Vec<DagId> = kids.iter().map(|&k| up_term(ctx, hooks, source, k)).collect();
                let arglist = up_arglist(ctx, hooks, up_args);
                let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
                ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
            }
        }
        NodeRepr::Iter { count, arg } => {
            // `'base^count[up(arg)]` — `^count` only when count > 1 (`s^1` is `'s_[…]`).
            let base = source.engine.symbol(source.engine.node(t).symbol()).name().to_string();
            let head = if count == "1" { base } else { format!("{base}^{count}") };
            let up_arg = up_term(ctx, hooks, source, arg);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
        // String/float constants up to `'"s".String` / `'f.Float`; bare qids to `''q.Sort` — these need
        // the value-dependent classification and are not reached by NAT/BOOL reduction (a follow-on).
        NodeRepr::Str(_) | NodeRepr::Qid(_) | NodeRepr::Float(_) => {
            let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
            ctx.make_na(qid, NaValue::Qid(format!("?.{sort}").into()))
        }
    }
}

/// Join up-translated arguments into a `metaTermSymbol` argument list: a single argument stays itself; two
/// or more become a `metaArgSymbol` (`_,_`) list.
fn up_arglist(ctx: &mut MetaCtx, hooks: &MetaHooks, args: Vec<DagId>) -> DagId {
    if args.len() == 1 {
        args.into_iter().next().unwrap()
    } else {
        ctx.app(hooks.ops["metaArgSymbol"], args)
    }
}

/// Up-translate the least sort of `t` (in `source`) to its meta `Type` — a `Qid` of the sort name.
fn up_sort(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
    ctx.make_na(qid, NaValue::Qid(sort.into()))
}

/// Up-translate a solution substitution: each bound variable `'X:Sort` to an assignment
/// `'X:Sort <- up(value)`, joined by `_;_`; an all-ground (no-variable) match is the empty `none`. The
/// variable's meta name is the full `X:Sort` text (a `VarIndex` key or a rule trace's `var_names`), so the
/// round-trip is exact. A binding with no value (`None`) is skipped (an unconstrained variable).
fn up_substitution(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    names: &[String],
    bindings: &[DagId],
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let assign = hooks.ops["assignmentSymbol"];
    let mut assigns = Vec::new();
    for (k, name) in names.iter().enumerate() {
        let Some(&val) = bindings.get(k) else { continue };
        let var_qid = ctx.make_na(qid, NaValue::Qid(name.as_str().into()));
        let up_val = up_term(ctx, hooks, source, val);
        assigns.push(ctx.app(assign, vec![var_qid, up_val]));
    }
    match assigns.len() {
        0 => ctx.app(hooks.ops["emptySubstitutionSymbol"], vec![]),
        1 => assigns.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["substitutionSymbol"], assigns),
    }
}

/// The `VarIndex`'s variable names as the `&[String]` [`up_substitution`] expects.
fn var_names(vars: &VarIndex) -> Vec<String> {
    (0..vars.count()).map(|k| vars.name(k).to_string()).collect()
}

/// Up-translate `node` (in `source`) into a meta `Context` — its [`up_term`], except the subterm at `path`
/// becomes the hole `[]` (`holeSymbol`). Handles the free-theory application spine (the path component is a
/// child index); the rewritten/hole position itself is reached when `path` is exhausted.
fn up_context(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    node: DagId,
    path: &[usize],
) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        return ctx.app(hooks.ops["holeSymbol"], vec![]);
    };
    let sym = source.engine.node(node).symbol();
    let name = source.engine.symbol(sym).name().to_string();
    let children: Vec<DagId> = source.engine.node(node).children().collect();
    let up_args: Vec<DagId> = children
        .iter()
        .enumerate()
        .map(|(i, &c)| {
            if i == head {
                up_context(ctx, hooks, source, c, rest)
            } else {
                up_term(ctx, hooks, source, c)
            }
        })
        .collect();
    let arglist = up_arglist(ctx, hooks, up_args);
    let opqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
    ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
}

/// Up-translate a kernel [`Term`] (a rule side, with variables) into a meta-term — the inverse of
/// [`down_term_to_term`], used to show a rule in a `metaSearchPath` trace. A `Var` becomes `'name:Sort`
/// (its trace name's base + sort), a constant `'c.Sort` (the operator's range sort), an application
/// `'f[args]`. (Iter-chain collapse to `'s_^n[…]` and built-in literals are refinements the `up*` family /
/// `upModule` adds — a search trace's rules here are over the free/constant fragment.)
fn up_pattern(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    term: &Term,
    names: &[String],
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match term {
        Term::Var(v) => {
            let base = names.get(v.index as usize).map_or("V", |s| s.split(':').next().unwrap_or(s));
            let sort = source.engine.sorts().name(v.sort);
            ctx.make_na(qid, NaValue::Qid(format!("{base}:{sort}").into()))
        }
        Term::Na { symbol, value } => {
            let rendered = match value {
                NaValue::Str(s) => format!("{s:?}"),
                NaValue::Qid(q) => format!("'{q}"),
                NaValue::Float(b) => format!("{}", f64::from_bits(*b)),
            };
            ctx.make_na(qid, NaValue::Qid(format!("{rendered}.{}", sort_name_of(source, *symbol)).into()))
        }
        Term::Op { symbol, args } if args.is_empty() => {
            let name = source.engine.symbol(*symbol).name();
            ctx.make_na(qid, NaValue::Qid(format!("{name}.{}", sort_name_of(source, *symbol)).into()))
        }
        Term::Op { symbol, args } => {
            let name = source.engine.symbol(*symbol).name().to_string();
            let up_args: Vec<DagId> =
                args.iter().map(|a| up_pattern(ctx, hooks, source, a, names)).collect();
            let arglist = up_arglist(ctx, hooks, up_args);
            let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
        }
    }
}

/// The declared range-sort name of operator `symbol` (its `SymbolSyntax`), for a constant's `'c.Sort`.
fn sort_name_of(source: &BuiltModule, symbol: SymbolId) -> String {
    source.syntax.get(&symbol).map(|s| source.engine.sorts().name(s.range).to_string()).unwrap_or_default()
}

/// Up-translate a rule (from its trace) to a meta `Rule` — `rl lhs => rhs [label] .` (unconditional). A
/// conditional rule needs the condition up-map (a `up*`-family follow-on) → `None`; such a rule does not
/// occur in the ground-rule search traces here.
fn up_rule(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, trace: &RlTrace) -> Option<DagId> {
    if !trace.condition.is_empty() {
        return None;
    }
    let up_lhs = up_pattern(ctx, hooks, source, &trace.lhs, &trace.var_names);
    let up_rhs = up_pattern(ctx, hooks, source, &trace.rhs, &trace.var_names);
    let attrs = match trace.label.as_deref() {
        Some(l) => {
            let lqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(l.into()));
            ctx.app(hooks.ops["labelSymbol"], vec![lqid])
        }
        None => ctx.app(hooks.ops["emptyAttrSetSymbol"], vec![]),
    };
    Some(ctx.app(hooks.ops["rlSymbol"], vec![up_lhs, up_rhs, attrs]))
}

/// Collect the subterm positions of `node` whose depth is in `[min_d, max_d]`, as child-index paths in
/// outermost-first (pre-order) order — `metaXapply`'s application-position enumeration.
fn collect_positions(
    engine: &Engine,
    node: DagId,
    depth: usize,
    path: &mut Vec<usize>,
    min_d: usize,
    max_d: Option<u64>,
    out: &mut Vec<Vec<usize>>,
) {
    if max_d.is_some_and(|m| depth as u64 > m) {
        return;
    }
    if depth >= min_d {
        out.push(path.clone());
    }
    let children: Vec<DagId> = engine.node(node).children().collect();
    for (i, &c) in children.iter().enumerate() {
        path.push(i);
        collect_positions(engine, c, depth + 1, path, min_d, max_d, out);
        path.pop();
    }
}

/// The subterm of `root` at child-index `path`.
fn subterm_at(engine: &Engine, root: DagId, path: &[usize]) -> DagId {
    let mut node = root;
    for &i in path {
        node = engine.node(node).children().nth(i).expect("valid position path");
    }
    node
}

/// `root` with the subterm at child-index `path` replaced by `new` (rebuilding the spine, theory-aware).
fn replace_at(engine: &mut Engine, root: DagId, path: &[usize], new: DagId) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        return new;
    };
    let sym = engine.node(root).symbol();
    let mut children: Vec<DagId> = engine.node(root).children().collect();
    children[head] = replace_at(engine, children[head], rest, new);
    engine.make_node(sym, children)
}

// ---- meta argument decoders (Bound / Nat / search arrow / empty condition) ----

/// A meta `Bound` (`unbounded` | a `Nat`) → the engine driver bound (`None` = unbounded, `Some(n)` = ≤ n).
fn down_bound(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<u64> {
    if Some(ctx.top(d)) == hooks.ops.get("unboundedSymbol").copied() {
        return None;
    }
    down_nat64(ctx, d)
}

/// A meta `Nat` (`'0.Zero`, `'s_^n['0.Zero]`, or a NAT numeral) → its `u64` value.
fn down_nat64(ctx: &MetaCtx, d: DagId) -> Option<u64> {
    match ctx.repr(d) {
        NodeRepr::Iter { count, .. } => count.parse().ok(),
        _ => Some(0), // the zero constant
    }
}

/// A meta search-type `Qid` (`'*`/`'+`/`'!`/`'1`) → the reachability [`Arrow`].
fn down_arrow(ctx: &MetaCtx, d: DagId) -> Option<Arrow> {
    match ctx.repr(d) {
        NodeRepr::Qid("*") => Some(Arrow::Star),
        NodeRepr::Qid("+") => Some(Arrow::Plus),
        NodeRepr::Qid("!") => Some(Arrow::Bang),
        NodeRepr::Qid("1") => Some(Arrow::One),
        _ => None,
    }
}

/// Whether a meta `Condition` is the empty `nil` (the only condition the matching descent handles so far).
fn is_nil_condition(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> bool {
    Some(ctx.top(d)) == hooks.ops.get("noConditionSymbol").copied()
}

/// Whether a meta `Substitution` is the empty `none` (the only partial substitution `metaApply` handles).
fn is_empty_subst(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> bool {
    Some(ctx.top(d)) == hooks.ops.get("emptySubstitutionSymbol").copied()
}

/// The `(n+1)`-th match solution's bindings (`0..nr`) of `pattern` against `subj`, or `None` if there are
/// fewer than `n+1`. `extension` allows the pattern to match a sub-part (`xmatch`).
fn nth_match(
    engine: &mut Engine,
    pattern: Term,
    nr: u32,
    subj: DagId,
    extension: bool,
    n: usize,
) -> Option<Vec<DagId>> {
    let mut sols = engine.match_solutions(pattern, nr, subj, extension);
    let mut count = 0;
    while sols.advance() {
        if count == n {
            return Some(
                (0..nr).map(|k| sols.binding(k).expect("the matcher binds every pattern variable")).collect(),
            );
        }
        count += 1;
    }
    None
}

/// The `(n+1)`-th **extension** match of `pattern` against `subj` — its bindings and whether the matched
/// portion is the *whole* subject (so the context is the bare hole `[]`). `None` if there are fewer than
/// `n+1` solutions.
fn nth_xmatch(
    engine: &mut Engine,
    pattern: Term,
    nr: u32,
    subj: DagId,
    n: usize,
) -> Option<(Vec<DagId>, bool)> {
    let mut found = None;
    {
        let mut sols = engine.match_solutions(pattern, nr, subj, true);
        let mut count = 0;
        while sols.advance() {
            if count == n {
                let bindings: Vec<DagId> =
                    (0..nr).map(|k| sols.binding(k).expect("the matcher binds every variable")).collect();
                found = Some((bindings, sols.matched_portion()));
                break;
            }
            count += 1;
        }
    }
    found.map(|(b, portion)| (b, engine.deep_equal(portion, subj)))
}
