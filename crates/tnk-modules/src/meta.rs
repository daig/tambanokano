//! META-LEVEL descent (Phase 3.1) — the [`DescentOps`] implementation.
//!
//! A descent redex (`metaReduce`/…) hands control here via the kernel's [`MetaCtx`] seam. [`MetaDescent`]
//! holds the module database + interner, so it can **down**-translate the meta-module argument into a real
//! object [`LoadedModule`] (a `PreModule` reconstructed from the meta-term, then the ordinary
//! flatten+build pipeline), down-translate the subject meta-term into that module, run the engine
//! operation, and **up**-translate the result back into the meta-level engine (via `ctx`).
//!
//! Scope (Stages 1–5 — the whole META-LEVEL surface; the symbolic/SMT/strategy descent is declared and
//! reduces inert until its backends land, Stage 5):
//!
//! * **The rewriting/matching/search family** (Stage 3) computes over a down-translated object module —
//!   `metaReduce`/`metaNormalize` (→ `ResultPair`), `metaRewrite`/`metaFrewrite` (rule-/position-fair),
//!   `metaMatch`/`metaXmatch` (→ `Substitution?`/`MatchPair?` + the hole context), `metaApply`/`metaXapply`
//!   (a labelled rule at the top / any position → `ResultTriple?`/`Result4Tuple?`),
//!   `metaSearch`/`metaSearchPath` (BFS reachability → `ResultTriple?` / the witness `Trace`). The module
//!   argument may be an **import expression** (`[Q]`) *or* a module with **inline declarations** —
//!   `down_module` reconstructs the full `PreModule`, runs the ordinary flatten+build, then installs the
//!   inline statements via `down_term_to_term` (a `Term`-producing down-translation).
//! * **The `up*` family** (Stage 4) decomposes a *named* built module back to its meta-rep:
//!   `upModule`/`upImports`/`upSorts`/`upSubsortDecls`/`upOpDecls`/`upMbs`/`upEqs`/`upRls` (mirroring
//!   `down_sorts`/`down_ops`/`install_*`), `upView`, and the term wrappers `upTerm`/`downTerm` (over the
//!   *current* module via the [`MetaCtx`](tnk_core::descent::MetaCtx) name resolver). `flat = true` inlines
//!   the whole import closure; `false` lists imports + only the module's own declarations (the suffix of the
//!   flat build's trace vectors). `up_pattern` collapses successor chains to `'s_^n[…]`; `up_rule`/
//!   `up_condition` reconstruct conditional rules/equations.
//! * **The sort/kind queries** (Stage 4) read the down-translated module's lattice: `sortLeq`/`sameKind`/
//!   `leastSort`/`lesserSorts`/`glbSorts`/`completeName`/`getKind(s)`/`maximal`/`minimalSorts`/
//!   `maximalAritySet`. **Syntax** (Stage 4): `metaParse` (reuse the grammar + Earley parser → `ResultPair?`/
//!   `noParse`), `metaPrettyPrint`/`metaPrintToString` (the format-aware `print_pretty` → `QidList`/`String`),
//!   and `metaWellFormed{Module,Term,Substitution}` (structural checks → `Bool`).
//!
//! Every implemented descent function conforms on **value, sort, rewrite count, *and* layout** (Stage 3.5
//! taught `print_pretty` the `format` attribute). The **symbolic** (unify/variant/narrow, Phase 3.2),
//! **SMT** (Phase 3.3), and **strategy-meta** (Phase 2.4 E) descent — `MetaOp::Deferred` plus the strategy-up
//! maps `UpStratDecls`/`UpSds` — are declared and parse (the tower is complete) but reduce to the kind level
//! via the [`descend`](MetaDescent::descend) match's single exhaustive inert arm (Stage 5: a new descent op now
//! forces a dispatch choice at compile time). The strategy *language* itself (`srewrite`/`dsrewrite`, the full
//! combinator + matchrew + conditional-rule surface) is **complete and conformant** in `tnk-frontend::strategy`
//! (Phase 2.4 A–D); only the strategy *meta-reflection* (`upStratDecls`/`upSds`/`metaParseStrategy`/
//! `metaPrettyPrintStrategy` — the Stage-5 strategy tail) stays inert here, pending sort-aware constructor
//! resolution + a non-desugaring parse + the StratExpr→Strategy up-translation/inverse (`fable-audit.md`). The residuals are orthogonal corners, each riding its own
//! subsystem (`fable-audit.md`): the Stage-3
//! compute corners (conditional-rule `metaApply`, conditioned `metaMatch`, the partial substitution, the
//! AC-residue `metaXmatch` context, the exhausted-search count); and the Stage-4 boundaries (flat-mode
//! builtin imports — `special`/`poly` op hooks *and* the imported builtin module's statements, both leaving
//! a flat `up*` over a builtin closure partial/inert, the inverse of [`down_attrs`]' boundary; the
//! multi-attribute `ctor`-order ACU divergence; non-`mixfix` print options; and structured
//! module-expression / op→term view maps). Own `[nonexec]` axioms + equation/membership labels *are* now
//! retained (parsed on demand — build installs no trace; see [`parse_statement_trace`](tnk_frontend::load)).

use std::collections::BTreeSet;

use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::descent::{DescentOps, MetaCtx};
use tnk_core::engine::Engine;
use tnk_core::search::Arrow;
use tnk_core::sort::SortId;
use tnk_core::symbol::{MetaHooks, MetaOp, SymbolId};
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};
use tnk_frontend::build_term::VarIndex;
use tnk_frontend::lex::{tokenize, Interner};
use tnk_frontend::load::{
    build_command_dag, build_loaded_module, command_parse_furthest, parse_statement_trace, LoadedModule, StmtTrace,
};
use tnk_frontend::pretty::print_pretty;
use tnk_frontend::sig::build_sig::canonical_name;
use tnk_frontend::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use tnk_frontend::surface::ast::{
    Attrs, GatherElem, Import, ImportMode, ModuleExpr, ModuleKind, OpDecl, OpMap, Parameter, PreModule,
    Statement,
};

use crate::db::ModuleDb;
use crate::flatten::{flatten, flatten_pre};
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
            // `metaReduce` runs the module's equations to normal form; `metaNormalize` normalizes modulo
            // the STRUCTURAL AXIOMS ONLY (AC order, id/idem collapse — no user equations).
            MetaOp::Reduce => self.meta_reduce(ctx, hooks, redex),
            MetaOp::Normalize => self.meta_normalize(ctx, hooks, redex),
            // The rewriting/matching/search family (Stage 3): down/up + the engine's rewrite/match/search.
            MetaOp::Rewrite => self.meta_rewrite(ctx, hooks, redex, false),
            MetaOp::Frewrite => self.meta_rewrite(ctx, hooks, redex, true),
            MetaOp::Match => self.meta_match(ctx, hooks, redex),
            MetaOp::Search => self.meta_search(ctx, hooks, redex),
            MetaOp::Apply => self.meta_apply(ctx, hooks, redex),
            MetaOp::Xmatch => self.meta_xmatch(ctx, hooks, redex),
            MetaOp::Xapply => self.meta_xapply(ctx, hooks, redex),
            MetaOp::SearchPath => self.meta_search_path(ctx, hooks, redex),
            // Stage 4 — the sort/kind queries (down the module, read the sort lattice).
            MetaOp::SortLeq => self.meta_sort_leq(ctx, hooks, redex),
            MetaOp::SameKind => self.meta_same_kind(ctx, hooks, redex),
            MetaOp::LeastSort => self.meta_least_sort(ctx, hooks, redex),
            MetaOp::LesserSorts => self.meta_lesser_sorts(ctx, hooks, redex),
            MetaOp::GlbSorts => self.meta_glb_sorts(ctx, hooks, redex),
            MetaOp::CompleteName => self.meta_complete_name(ctx, hooks, redex),
            MetaOp::GetKind => self.meta_get_kind(ctx, hooks, redex),
            MetaOp::GetKinds => self.meta_get_kinds(ctx, hooks, redex),
            MetaOp::MaximalSorts => self.meta_maximal_sorts(ctx, hooks, redex),
            MetaOp::MinimalSorts => self.meta_minimal_sorts(ctx, hooks, redex),
            MetaOp::MaximalAritySet => self.meta_maximal_arity_set(ctx, hooks, redex),
            // Stage 4 — wellformedness checks.
            MetaOp::WellFormedModule => self.meta_well_formed_module(ctx, hooks, redex),
            MetaOp::WellFormedTerm => self.meta_well_formed_term(ctx, hooks, redex),
            MetaOp::WellFormedSubstitution => self.meta_well_formed_subst(ctx, hooks, redex),
            // Stage 4 — the up* family (decompose a built module back to its meta-rep).
            MetaOp::UpModule => self.meta_up_module(ctx, hooks, redex),
            MetaOp::UpImports => self.meta_up_imports(ctx, hooks, redex),
            MetaOp::UpSorts => self.meta_up_part(ctx, hooks, redex, UpPart::Sorts),
            MetaOp::UpSubsortDecls => self.meta_up_part(ctx, hooks, redex, UpPart::Subsorts),
            MetaOp::UpOpDecls => self.meta_up_part(ctx, hooks, redex, UpPart::Ops),
            MetaOp::UpMbs => self.meta_up_part(ctx, hooks, redex, UpPart::Mbs),
            MetaOp::UpEqs => self.meta_up_part(ctx, hooks, redex, UpPart::Eqs),
            MetaOp::UpRls => self.meta_up_part(ctx, hooks, redex, UpPart::Rls),
            // Stage 4 — the term-level wrappers (over the *current* module, via the MetaCtx resolver).
            MetaOp::UpTerm => {
                let arg = *ctx.children(redex).first()?;
                Some(up_term_ctx(ctx, hooks, arg))
            }
            MetaOp::DownTerm => {
                let kids = ctx.children(redex);
                let meta = *kids.first()?;
                let default = *kids.get(1)?;
                Some(down_term_ctx(ctx, hooks, meta).unwrap_or(default))
            }
            MetaOp::UpView => self.meta_up_view(ctx, hooks, redex),
            // Stage 4 — syntax: parse a token list / pretty-print a term in a module's grammar.
            MetaOp::Parse => self.meta_parse(ctx, hooks, redex),
            MetaOp::PrettyPrint => self.meta_pretty_print(ctx, hooks, redex, false),
            MetaOp::PrintToString => self.meta_pretty_print(ctx, hooks, redex, true),
            // Stage 5 — declared but **inert**: the symbolic (unify/variant/narrow, Phase 3.2, D6 BDD),
            // SMT (Phase 3.3, D7 Z3), and strategy (Phase 2.4) descent. These ops parse and load (the tower
            // is complete) but reduce to the kind level — they never misfire — until their backends land.
            // `MetaOp::Deferred` is the symbolic/SMT/legacy set (`metaUnify`/`metaVariant*`/`metaNarrow*`/
            // `metaSmtSearch`/`metaCheck`/`metaSrewrite`/`metaParseStrategy`/…); `UpStratDecls`/`UpSds` are
            // the strategy-declaration up maps. The match is exhaustive so a new descent op forces a choice.
            // Strategy-meta up maps are structurally deferred (G1, §3.9.8) — but the EMPTY sets
            // need none of G1's prerequisites: a module with no strat declarations/definitions
            // up-translates to the empty-set constant ((none).StratDeclSet, 1 rewrite), as Maude
            // does. Nonempty sets stay inert until G1.
            MetaOp::UpStratDecls | MetaOp::UpSds => {
                let kids = ctx.children(redex);
                let name = qid_text(ctx, *kids.first()?)?;
                let _flat = down_bool(ctx, *kids.get(1)?)?;
                let pm = self.db.get(&name)?;
                let (empty_hook, is_empty) = match op {
                    MetaOp::UpStratDecls => ("emptyStratDeclSetSymbol", pm.strat_decls.is_empty()),
                    _ => ("emptyStratDefSetSymbol", pm.strat_defs.is_empty()),
                };
                if !is_empty {
                    return None; // nonempty strategy meta-reflection is G1
                }
                let sym = *hooks.ops.get(empty_hook)?;
                Some(ctx.app(sym, Vec::new()))
            }
            MetaOp::Deferred => None,
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

    /// `metaNormalize(M, T)` → `{up(t'), up(leastSort(t'))}` where `t'` is `down(T)` normalized modulo the
    /// module's **structural axioms only** — AC/ACU ordering, `id:`/`idem` collapse, `iter` fold — with **no
    /// user equations applied** (Maude's `Term::normalize(true)`, which `down_term`'s construction already
    /// performs). The inverse temptation is `meta_reduce`, which additionally runs the equations to normal
    /// form; `metaNormalize` must leave `g(a)` as `g(a)` even when `eq g(a) = b` exists. No object rewrites
    /// are counted (Maude does not `addInCount` here).
    fn meta_normalize(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        // `down_term` builds the canonical DAG (construction canonicalizes AC order / collapses id/idem /
        // folds iter) — that *is* the axiom-normal form; no `reduce` call, so no equation ever fires.
        let subj = down_term(ctx, hooks, kids[1], &mut loaded.built)?;
        let ut = up_term(ctx, hooks, &loaded.built, subj);
        let us = up_sort(ctx, hooks, &loaded.built, subj);
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

    // ---- Stage 4: sort/kind queries (down the module, read the sort lattice) ----

    /// `sortLeq(M, T1, T2)` → `Bool` — `T1 <= T2` (same kind *and* subsort, mirroring Maude's
    /// `s1->component() == s2->component() && leq(s1, s2)`).
    fn meta_sort_leq(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s1 = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let s2 = down_type(ctx, &loaded.built, *kids.get(2)?)?;
        let sorts = loaded.built.engine.sorts();
        let r = sorts.same_kind(s1, s2) && sorts.leq(s1, s2);
        up_bool(ctx, r)
    }

    /// `sameKind(M, T1, T2)` → `Bool` — whether the two types share a connected component.
    fn meta_same_kind(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s1 = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let s2 = down_type(ctx, &loaded.built, *kids.get(2)?)?;
        let r = loaded.built.engine.sorts().same_kind(s1, s2);
        up_bool(ctx, r)
    }

    /// `leastSort(M, T)` → the `Type` of the least sort of the down-translated term (no reduction —
    /// our `down_term` computes the sort at construction, Maude's `computeTrueSort`).
    fn meta_least_sort(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let t = down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built)?;
        let s = loaded.built.engine.sort_of(t);
        Some(up_type(ctx, hooks, &loaded.built, s))
    }

    /// `lesserSorts(M, T)` → the `SortSet` of sorts strictly below `T` in its component.
    fn meta_lesser_sorts(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        let kid = sorts.kind_of(s);
        let lesser: Vec<SortId> =
            sorts.kind(kid).members.iter().copied().filter(|&x| x != s && sorts.leq(x, s)).collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &lesser))
    }

    /// `glbSorts(M, T1, T2)` → the `TypeSet` of maximal common lower bounds (greatest lower bounds);
    /// empty when the two types are in different components.
    fn meta_glb_sorts(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s1 = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let s2 = down_type(ctx, &loaded.built, *kids.get(2)?)?;
        let sorts = loaded.built.engine.sorts();
        let glb: Vec<SortId> = if sorts.same_kind(s1, s2) {
            let kid = sorts.kind_of(s1);
            let lowers: Vec<SortId> = sorts
                .kind(kid)
                .members
                .iter()
                .copied()
                .filter(|&x| sorts.leq(x, s1) && sorts.leq(x, s2))
                .collect();
            // Keep the maximal elements of the lower set (the greatest lower bounds).
            lowers.iter().copied().filter(|&x| !lowers.iter().any(|&y| y != x && sorts.leq(x, y))).collect()
        } else {
            Vec::new()
        };
        Some(up_sort_set(ctx, hooks, &loaded.built, &glb))
    }

    /// `completeName(M, T)` → the resolved `Type` (a valid sort/kind name maps to itself; Maude's
    /// `downType`→`upType`). `None` if `T` is not a type of `M`.
    fn meta_complete_name(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        Some(up_type(ctx, hooks, &loaded.built, s))
    }

    /// `getKind(M, T)` → the `Kind` (error/top sort) of `T`'s connected component.
    fn meta_get_kind(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        let err = sorts.error_sort(sorts.kind_of(s));
        Some(up_type(ctx, hooks, &loaded.built, err))
    }

    /// `getKinds(M)` → the `KindSet` of every connected component's `Kind` (error sort).
    fn meta_get_kinds(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let sorts = loaded.built.engine.sorts();
        let errs: Vec<SortId> = sorts.kinds().map(|k| sorts.error_sort(k)).collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &errs))
    }

    /// `maximalSorts(M, K)` → the `SortSet` of `K`'s maximal sorts (those with no proper supersort).
    /// `None` unless `K` is a kind (Maude requires `k->index() == Sort::KIND`).
    fn meta_maximal_sorts(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let k = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        if !sorts.sort(k).is_error {
            return None; // not a kind
        }
        let members = &sorts.kind(sorts.kind_of(k)).members;
        let maximal: Vec<SortId> = members
            .iter()
            .copied()
            .filter(|&s| !members.iter().any(|&t| t != s && sorts.leq(s, t)))
            .collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &maximal))
    }

    /// `minimalSorts(M, K)` → the `SortSet` of `K`'s minimal sorts (those with no proper subsort).
    fn meta_minimal_sorts(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let k = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        if !sorts.sort(k).is_error {
            return None;
        }
        let members = &sorts.kind(sorts.kind_of(k)).members;
        let minimal: Vec<SortId> = members
            .iter()
            .copied()
            .filter(|&s| !members.iter().any(|&t| t != s && sorts.leq(t, s)))
            .collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &minimal))
    }

    /// `maximalAritySet(M, Q, D, S)` → the `TypeListSet` of maximal argument-sort lists of operator `Q`
    /// (arity = |D|, each argument in `D`'s component) whose range is `<= S` — Maude's `getMaximalOpDeclSet`.
    /// A domain is maximal when no other candidate's argument sorts are all `>=` it. `None` if `Q` is not an
    /// operator of that profile.
    fn meta_maximal_arity_set(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let op_name = qid_text(ctx, *kids.get(1)?)?;
        let dom_dags = flatten_set(
            ctx,
            *kids.get(2)?,
            hooks.ops.get("nilQidListSymbol").copied(),
            hooks.ops.get("qidListSymbol").copied(),
        );
        let dom_sorts: Vec<SortId> =
            dom_dags.iter().map(|&d| down_type(ctx, &loaded.built, d)).collect::<Option<_>>()?;
        let target = down_type(ctx, &loaded.built, *kids.get(3)?)?;
        let sym = *loaded.built.ops.get(&(op_name, dom_sorts.len()))?;
        let sorts = loaded.built.engine.sorts();
        // Candidate declarations: range <= target and each argument in the requested component.
        let candidates: Vec<Vec<SortId>> = loaded
            .built
            .engine
            .symbol_declarations(sym)
            .into_iter()
            .filter(|(dom, range)| {
                sorts.leq(*range, target)
                    && dom.len() == dom_sorts.len()
                    && dom.iter().zip(&dom_sorts).all(|(&d, &q)| sorts.same_kind(d, q))
            })
            .map(|(dom, _)| dom)
            .collect();
        // Keep the maximal domains (no other candidate dominates them argument-wise).
        let dominates = |big: &[SortId], small: &[SortId]| {
            big != small && big.iter().zip(small).all(|(&b, &s)| sorts.leq(s, b))
        };
        let maximal: Vec<Vec<SortId>> = candidates
            .iter()
            .filter(|d| !candidates.iter().any(|o| dominates(o, d)))
            .cloned()
            .collect();
        let type_lists: Vec<DagId> =
            maximal.iter().map(|dom| up_type_list(ctx, hooks, &loaded.built, dom)).collect();
        // A `TypeListSet` joins type-lists with `_;_`; a single list stays itself (always >= 1 here).
        Some(match type_lists.len() {
            1 => type_lists.into_iter().next().unwrap(),
            _ => ctx.app(hooks.ops["sortSetSymbol"], type_lists),
        })
    }

    /// `wellFormed(M)` → `Bool` — whether the module meta-term builds (Maude's `downModule != 0`).
    fn meta_well_formed_module(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let ok = self.down_module(ctx, hooks, *kids.first()?).is_some();
        up_bool(ctx, ok)
    }

    /// `wellFormed(M, T)` → `Bool` — whether `T` down-translates to a well-formed term of `M` (each
    /// application's argument kinds matching the operator's domain). The module itself must build (else
    /// inert, as Maude's `downModule == 0` path).
    fn meta_well_formed_term(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let ok = match down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built) {
            Some(t) => term_well_formed(&loaded.built, t),
            None => false,
        };
        up_bool(ctx, ok)
    }

    /// `wellFormed(M, S)` → `Bool` — whether every assignment `'X:Sort <- value` of substitution `S` has a
    /// well-formed value whose kind matches the variable's sort (Maude's `downSubstitution` +
    /// `dagifySubstitution`, including the kind-clash rejection). The module must build (else inert).
    fn meta_well_formed_subst(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let ok = subst_well_formed(ctx, hooks, &mut loaded.built, *kids.get(1)?);
        up_bool(ctx, ok)
    }

    // ---- Stage 4: the up* family (decompose a named, built module back to its meta-rep) ----

    /// `upModule(Q, flat)` → the `Module` meta-rep of the module named `Q`. `flat = true` inlines the whole
    /// import closure (a `nil` import list); `flat = false` lists the imports and emits only the module's
    /// own declarations (Maude's `getNrImported*` suffix). The argument order mirrors the module
    /// constructor `fmod_is_sorts_.____endfm` / `mod_is_sorts_._____endm`.
    fn meta_up_module(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let flat = down_bool(ctx, *kids.get(1)?)?;
        let p = self.module_pieces(&name, flat)?;
        let name_qid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
        // A parameterized module's header carries its parameter list (`'LIST{'X :: 'TRIV}`); the flat form
        // and a non-parameterized module use the bare name Qid (Maude's `upHeader`).
        let header = if flat || p.params.is_empty() {
            name_qid
        } else {
            up_header(ctx, hooks, name_qid, &p.params)?
        };
        let imports = up_imports(ctx, hooks, &p.imports)?;
        let sorts = up_sorts_dag(ctx, hooks, &p.sorts);
        let subsorts = up_subsorts_dag(ctx, hooks, &p.subsorts);
        let ops = up_ops_dag(ctx, hooks, &p.loaded.built, &p.ops)?;
        let mbs = up_membs_dag(ctx, hooks, &p.loaded.built, &p.mbs)?;
        let eqs = up_eqs_dag(ctx, hooks, &p.loaded.built, &p.eqs)?;
        let mut args = vec![header, imports, sorts, subsorts, ops, mbs, eqs];
        let ctor = if p.kind == ModuleKind::System {
            args.push(up_rls_dag(ctx, hooks, &p.loaded.built, &p.rls)?);
            if p.is_theory { "thSymbol" } else { "modSymbol" }
        } else if p.is_theory {
            "fthSymbol"
        } else {
            "fmodSymbol"
        };
        Some(ctx.app(*hooks.ops.get(ctor)?, args))
    }

    /// `upImports(Q)` → the `ImportList` of the module named `Q` (always the module's own imports).
    fn meta_up_imports(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let pm = self.db.get(&name)?;
        let imports = pm.imports.clone();
        up_imports(ctx, hooks, &imports)
    }

    /// `upView(Q)` → the `View` meta-rep of the view named `Q`: `view Q from <from> to <to> is <sort maps>
    /// <op maps> <strat maps> endv`. Sort maps and op→op maps are emitted; an op→term map and a structured
    /// (non-`Named`) `from`/`to` are follow-ons (`None`). Strategy maps are not modelled (empty).
    fn meta_up_view(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let v = self.views.get(&name)?.clone();
        // Pre-resolve op→op map names (need the interner); bail on an op→term map (a follow-on).
        let mut op_names = Vec::with_capacity(v.op_maps.len());
        for m in &v.op_maps {
            match m {
                OpMap::Op { from, to } => {
                    op_names.push((canonical_name(from, self.interner), canonical_name(to, self.interner)))
                }
                OpMap::Term { .. } => return None,
            }
        }
        let qid = hooks.ops["qidSymbol"];
        let header = ctx.make_na(qid, NaValue::Qid(name.into()));
        let from = up_module_expr(ctx, hooks, &v.from)?;
        let to = up_module_expr(ctx, hooks, &v.to)?;
        let mut sm = Vec::with_capacity(v.sort_maps.len());
        for (a, b) in &v.sort_maps {
            let aq = ctx.make_na(qid, NaValue::Qid(a.as_str().into()));
            let bq = ctx.make_na(qid, NaValue::Qid(b.as_str().into()));
            sm.push(ctx.app(hooks.ops["sortMappingSymbol"], vec![aq, bq]));
        }
        let sort_maps =
            up_set(ctx, sm, hooks.ops["emptySortMappingSetSymbol"], hooks.ops["sortMappingSetSymbol"]);
        let mut om = Vec::with_capacity(op_names.len());
        for (a, b) in &op_names {
            let aq = ctx.make_na(qid, NaValue::Qid(a.as_str().into()));
            let bq = ctx.make_na(qid, NaValue::Qid(b.as_str().into()));
            om.push(ctx.app(hooks.ops["opMappingSymbol"], vec![aq, bq]));
        }
        let op_maps =
            up_set(ctx, om, hooks.ops["emptyOpMappingSetSymbol"], hooks.ops["opMappingSetSymbol"]);
        let strat_maps = ctx.app(hooks.ops["emptyStratMappingSetSymbol"], vec![]);
        Some(ctx.app(hooks.ops["viewSymbol"], vec![header, from, to, sort_maps, op_maps, strat_maps]))
    }

    /// The individual declaration-set projections `upSorts`/`upSubsortDecls`/`upOpDecls`/`upMbs`/`upEqs`/
    /// `upRls` — each `(Qid, Bool) ~> <Set>`, the corresponding piece of [`meta_up_module`](Self::meta_up_module).
    fn meta_up_part(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        part: UpPart,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let flat = down_bool(ctx, *kids.get(1)?)?;
        let p = self.module_pieces(&name, flat)?;
        match part {
            UpPart::Sorts => Some(up_sorts_dag(ctx, hooks, &p.sorts)),
            UpPart::Subsorts => Some(up_subsorts_dag(ctx, hooks, &p.subsorts)),
            UpPart::Ops => up_ops_dag(ctx, hooks, &p.loaded.built, &p.ops),
            UpPart::Mbs => up_membs_dag(ctx, hooks, &p.loaded.built, &p.mbs),
            UpPart::Eqs => up_eqs_dag(ctx, hooks, &p.loaded.built, &p.eqs),
            UpPart::Rls => up_rls_dag(ctx, hooks, &p.loaded.built, &p.rls),
        }
    }

    /// `metaParse(M, VS, QL, T?)` → `{up(parsed term), up(least sort)}` (`ResultPair`) of parsing the
    /// token list `QL` in `M`'s grammar, or `noParse(n)` at the first unparseable token. The parse does not
    /// reduce. The variable set `VS` (on-the-fly variables) and a restricting `Type` are handled when
    /// empty/`anyType`; a non-empty variable set is a follow-on.
    fn meta_parse(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let texts = qidlist_texts(ctx, hooks, *kids.get(2)?)?;
        let tokens = tokenize(&texts.join(" "), self.interner);
        let result = match build_command_dag(&mut loaded, self.interner, &tokens) {
            Ok(dag) => {
                let ut = up_term(ctx, hooks, &loaded.built, dag);
                let us = up_sort(ctx, hooks, &loaded.built, dag);
                ctx.app(*hooks.ops.get("resultPairSymbol")?, vec![ut, us])
            }
            Err(_) => {
                // The unparseable-token position: the furthest token a valid partial parse reached
                // (Maude's `badTokenIndex`), so `'a 'b` over a module where `a` parses but nothing follows
                // reports `noParse(1)`, not `noParse(0)` (fable-audit.md §3.3 B4).
                let pos = command_parse_furthest(&loaded, self.interner, &tokens);
                let n = up_nat(ctx, pos as u64)?;
                ctx.app(*hooks.ops.get("noParseSymbol")?, vec![n])
            }
        };
        Some(result)
    }

    /// `metaPrettyPrint(M, VS, T, opts, Q)` → the `QidList` of tokens rendering `T` in `M`'s grammar, or (if
    /// `to_string`) `metaPrintToString` → the `String` of the rendered text. Honors the default
    /// `mixfix flat format number rat` options via the format-aware [`print_pretty`]; with `mixfix` **off**
    /// (the prefix `f(_,_)` rendering) the op stays inert — a separate, non-`print_pretty` renderer (the
    /// documented print-option boundary). `None` if `T` does not down-translate.
    fn meta_pretty_print(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        to_string: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        if !has_option(ctx, *kids.get(3)?, "mixfix") {
            return None; // non-mixfix (prefix) print options are a separate renderer — stay inert
        }
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let term = down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built)?;
        let printed = print_pretty(&loaded.built, self.interner, term, false);
        if to_string {
            // A string value is raw bytes; the printed ASCII text becomes those bytes.
            return Some(ctx.make_na(hooks.ops["stringSymbol"], NaValue::Str(printed.into_bytes().into())));
        }
        let tokens = tokenize(&printed, self.interner);
        let texts: Vec<String> = tokens.iter().map(|t| self.interner.resolve(t.sym).to_string()).collect();
        let qid = hooks.ops["qidSymbol"];
        let qids: Vec<DagId> =
            texts.iter().map(|w| ctx.make_na(qid, NaValue::Qid(w.as_str().into()))).collect();
        Some(up_set(ctx, qids, hooks.ops["nilQidListSymbol"], hooks.ops["qidListSymbol"]))
    }

    /// Build the decomposition pieces of module `name`: the (flat or own) surface sorts/subsorts/ops + the
    /// import list + the trace index ranges for memberships/equations/rules. `flat` selects the whole
    /// import closure (from the flattened `PreModule`) vs. the module's own declarations (`db.get(name)`)
    /// with imports listed separately; the own statement traces are the suffix of the flat build's trace
    /// vectors (flatten appends a module's own statements after its imports).
    fn module_pieces(&mut self, name: &str, flat: bool) -> Option<ModulePieces> {
        let pm = self.db.get(name)?.clone();
        let flat_pm = flatten(name, self.db, self.views, self.interner).ok()?;
        let loaded = build_loaded_module(&flat_pm, self.interner).ok()?;
        let (sorts, subsorts, raw_ops, imports) = if flat {
            (flat_pm.sorts.clone(), flat_pm.subsorts.clone(), flat_pm.ops.clone(), Vec::new())
        } else {
            (pm.sorts.clone(), pm.subsorts.clone(), pm.ops.clone(), pm.imports.clone())
        };
        // Pre-resolve each op's canonical name + identity-element name (both need the interner) so the
        // up-builders are interner-free.
        let ops: Vec<UpOp> = raw_ops
            .iter()
            .map(|od| UpOp {
                name: canonical_name(&od.name, self.interner),
                id_name: od.attrs.id.as_ref().map(|toks| canonical_name(toks, self.interner)),
                decl: od.clone(),
            })
            .collect();
        let (mbs, eqs, rls) = if flat {
            // The whole import closure: walk the flattened statement list, interleaving `[nonexec]` axioms
            // with the flat build's trace vectors (which cover every executable statement, from index 0).
            merge_statement_traces(&flat_pm.statements, &loaded, self.interner, (0, 0, 0))
        } else {
            // The module's own statements: executable ones are the trace PREFIX — the root's own
            // statements flatten FIRST (Maude's nrOriginal* leading slice; the flatten rotation and
            // this window are the A3b coupled pair and must stay in sync).
            merge_statement_traces(&pm.statements, &loaded, self.interner, (0, 0, 0))
        };
        Some(ModulePieces {
            kind: flat_pm.kind,
            is_theory: flat_pm.is_theory,
            params: pm.params.clone(),
            sorts,
            subsorts,
            ops,
            imports,
            mbs,
            eqs,
            rls,
            loaded,
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
            is_strategy: false,
            // Down-translated meta-modules install their statements post-build (not via the `is_object`-gated
            // `load_statements`), so object-pattern completion does not apply to the meta path.
            is_object: false,
            params: Vec::new(),
            imports,
            sorts,
            subsorts,
            ops,
            vars: Vec::new(),
            statements: Vec::new(), // inline statements are down-translated post-build (below)
            strat_decls: Vec::new(),
            strat_defs: Vec::new(),
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

/// A meta `QidList` (`nil` | `__`-joined `Qid`s, or a single `Qid`) → the token text strings, in order —
/// `metaParse`'s token sequence.
fn qidlist_texts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Vec<String>> {
    let empty = hooks.ops.get("nilQidListSymbol").copied();
    let join = hooks.ops.get("qidListSymbol").copied();
    flatten_set(ctx, d, empty, join).iter().map(|&x| qid_text(ctx, x)).collect()
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
        } else if is("configSymbol") {
            a.config = true;
        } else if is("objectSymbol") {
            a.object = true;
        } else if is("msgSymbol") {
            a.message = true;
        } else if is("portalSymbol") {
            a.portal = true;
        } else if is("idSymbol") || is("leftIdSymbol") || is("rightIdSymbol") {
            // `id:`/`left-id:`/`right-id:` <term> — a single identity constant in practice; carry its name.
            a.id = Some(id_bubble(ctx, *ctx.children(attr).first()?, i)?);
        } else if is("precSymbol") {
            a.prec = down_nat(ctx, *ctx.children(attr).first()?);
        } else if is("stratSymbol") {
            // `strat(<NatList>)` — the per-op evaluation strategy (1-based arg positions, `0` = whole
            // term). Reconstructed like an object-level `strat` declaration; `build_sig` applies it via
            // `set_strategy` when the down-translated module is built.
            a.strat = Some(down_nat_list(ctx, hooks, *ctx.children(attr).first()?)?);
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

/// A meta `NatList` (a single `Nat`, or `__`/`natListSymbol`-joined `Nat`s) → the `u32` position list —
/// the inverse of [`up_nat_list`] (a `strat(…)` op attribute's argument).
fn down_nat_list(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Vec<u32>> {
    if Some(ctx.top(d)) == hooks.ops.get("natListSymbol").copied() {
        ctx.children(d).iter().map(|&c| down_nat(ctx, c)).collect()
    } else {
        Some(vec![down_nat(ctx, d)?])
    }
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
        // Down-installed statements are executable (nonexec skipped above); retain the label from the meta
        // `AttrSet` (as the rule path does) so a down∘up round-trip preserves it.
        let label = attrset_label(ctx, hooks, attrs);
        let trace = MbTrace {
            lhs: lhs.clone(),
            sort: sort_id,
            condition: condition.clone(),
            var_names,
            label,
            nonexec: false,
        };
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
        let trace = EqTrace {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            condition: condition.clone(),
            var_names,
            owise,
            label: attrset_label(ctx, hooks, attrs), // executable (nonexec skipped above); retain the label
            nonexec: false,
        };
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
        let trace = RlTrace {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            condition: condition.clone(),
            var_names,
            label,
            nonexec: false,
        };
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
        let sym = *target.ops.get(&(strip_op_blanks(&text[..dot]), 0))?;
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

/// Resolve a meta op-name applied to `arity` args against `target`, honouring associativity: try the exact
/// `(name, arity)` operator; failing that, a flat (≥3-arg) application of an **associative** op resolves the
/// binary `(name, 2)` symbol (the op is declared binary, but a nested application denotes the same flattened
/// term — `make_node`/`Term::op` build the flattened ACU/AU form).
fn resolve_flat_assoc(name: &str, arity: usize, target: &BuiltModule) -> Option<SymbolId> {
    if let Some(&sym) = target.ops.get(&(name.to_string(), arity)) {
        return Some(sym);
    }
    if arity >= 3
        && let Some(&sym) = target.ops.get(&(name.to_string(), 2))
        && target.engine.symbol_is_assoc(sym)
    {
        return Some(sym);
    }
    None
}

/// Build a kernel [`Term`] application from a meta op-name + down-translated args: an iterated name
/// `base^n` wraps the argument in `n` nested successor `Term::Op`s; otherwise the operator is `(name, arity)`.
fn build_app_term(head: &str, args: Vec<Term>, target: &BuiltModule) -> Option<Term> {
    let head = strip_op_blanks(head); // normalize a meta Qid's backtick-blanks to the canonical op name
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
    let sym = resolve_flat_assoc(&head, args.len(), target)?;
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
    let sym = resolve_flat_assoc(head, args.len(), target)?;
    Some(target.engine.make_node(sym, args))
}

/// An operator's META name Qid string: its canonical name with a **backtick-blank** re-inserted before a
/// *split char* adjacent to a literal — Maude keeps the blank in a stored op name so that `bal :_` is
/// `` bal`:_ `` (else `bal:_` would re-tokenize as one token), while `_,_`/`<_:_|_>` (literals separated by
/// holes) are unchanged. A genuine inter-token blank between two *text* tokens (`op c d_`, `op a b`) is now
/// preserved by [`canonical_name`](tnk_frontend::sig::build_sig::canonical_name) itself (as a backtick), so
/// it is already present in `name` and passes through here unchanged — this function only adds the
/// split-char backtick that the canonical form omits. Mirrors [`split_mixfix`](tnk_frontend::lex::split_mixfix).
fn meta_op_name(name: &str) -> String {
    let is_punct = |c: char| matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',');
    let mut out = String::new();
    let mut in_literal = false; // accumulating a literal identifier run
    let mut prev_literal = false; // the previous emitted fragment was a literal token
    for ch in name.chars() {
        if ch == '`' {
            out.push('`'); // a pre-existing blank (tnk names normally have none) — pass through
            in_literal = false;
            prev_literal = false;
        } else if ch == '_' {
            out.push('_'); // a hole separates literal fragments (no blank needed)
            in_literal = false;
            prev_literal = false;
        } else if ch == ':' || is_punct(ch) {
            if in_literal || prev_literal {
                out.push('`'); // split char adjacent to a literal → blank
            }
            out.push(ch);
            in_literal = false;
            prev_literal = true;
        } else {
            if !in_literal && prev_literal {
                out.push('`'); // a new literal run adjacent to the previous literal → blank
            }
            out.push(ch);
            in_literal = true;
            prev_literal = true;
        }
    }
    out
}

/// The inverse of [`meta_op_name`] for resolving a **down**-translated operator name to its canonical op
/// table key: strip only the backtick-blanks a meta Qid carries *around a split char* (`` bal`:_ `` →
/// `bal:_`, `` _`,_ `` → `_,_`) — the ones [`meta_op_name`] synthesizes and the canonical name omits. A
/// backtick before a *normal* char is a genuine inter-token blank that [`canonical_name`] keeps in the key
/// (`` a`b ``, `` c`d_ ``), so it is preserved here rather than stripped.
fn strip_op_blanks(name: &str) -> String {
    let is_split = |c: char| matches!(c, '_' | ':' | '(' | ')' | '[' | ']' | '{' | '}' | ',');
    let mut out = String::new();
    let mut chars = name.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '`' {
            match chars.peek() {
                Some(&next) if is_split(next) => {
                    out.push(next); // a synthesized split-char blank — drop the backtick, keep the char
                    chars.next();
                }
                _ => out.push('`'), // a real text-text blank — part of the canonical key
            }
        } else {
            out.push(ch);
        }
    }
    out
}

/// Up-translate an object DAG `t` (in `source`) into a meta-term built in `ctx`.
fn up_term(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match source.engine.node(t).repr() {
        NodeRepr::App => {
            let sym = source.engine.node(t).symbol();
            let name = meta_op_name(source.engine.symbol(sym).name());
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
            let base = meta_op_name(source.engine.symbol(source.engine.node(t).symbol()).name());
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

// ---- Stage 4: upTerm / downTerm (over the *current* module, read/built via the MetaCtx resolver) ----

/// The snapshot of an object DAG node needed to up-translate it, taken with immutable `MetaCtx` reads
/// before the (mutable) result build — so `up_term_ctx` can recurse without a borrow conflict.
enum NodeShape {
    Leaf(String),               // a constant `'name.sort` or NA literal `'"s".String` / `''q.Qid` / `'f.Float`
    App(String, Vec<DagId>),    // an application `'name[args]`
    Iter(String, Vec<DagId>),   // the iter head `name`/`name^count` + the single argument
}

/// `upTerm`: up-translate an object DAG `t` of the **current** module into its meta-`Term`. Unlike
/// [`up_term`] (which reads a `BuiltModule`), this reads `t` straight from the engine `ctx` is reducing in
/// — the argument is already eagerly reduced by the ambient. Handles constants, applications, the `iter`
/// successor form, and NA literals (string/qid/float), exactly as the reference's `upTerm`.
fn up_term_ctx(ctx: &mut MetaCtx, hooks: &MetaHooks, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = ctx.sort_name(ctx.sort_of(t)).to_string();
    let shape = match ctx.repr(t) {
        NodeRepr::App => {
            let name = meta_op_name(ctx.name(ctx.top(t)));
            let kids = ctx.children(t);
            if kids.is_empty() {
                NodeShape::Leaf(format!("{name}.{sort}"))
            } else {
                NodeShape::App(name, kids)
            }
        }
        NodeRepr::Iter { count, arg } => {
            let base = meta_op_name(ctx.name(ctx.top(t)));
            let head = if count == "1" { base } else { format!("{base}^{count}") };
            NodeShape::Iter(head, vec![arg])
        }
        NodeRepr::Str(s) => NodeShape::Leaf(format!("{:?}.{sort}", String::from_utf8_lossy(s))),
        NodeRepr::Qid(q) => NodeShape::Leaf(format!("'{q}.{sort}")),
        NodeRepr::Float(f) => NodeShape::Leaf(format!("{f}.{sort}")),
    };
    match shape {
        NodeShape::Leaf(text) => ctx.make_na(qid, NaValue::Qid(text.into())),
        NodeShape::App(name, kids) => {
            let up_args: Vec<DagId> = kids.iter().map(|&k| up_term_ctx(ctx, hooks, k)).collect();
            let arglist = up_arglist(ctx, hooks, up_args);
            let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
        }
        NodeShape::Iter(head, arg) => {
            let up_arg = up_term_ctx(ctx, hooks, arg[0]);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
    }
}

/// `downTerm`: down-translate a meta-`Term` into a DAG in the **current** module (resolving operators by
/// name + arity via the [`MetaCtx`] resolver). The inverse of [`up_term_ctx`]: a constant `'c.S`, an
/// application `'f[args]`, the iterated `'s_^n[t]`. `None` if any operator/constant is unresolvable (the
/// caller falls back to `downTerm`'s default argument, as Maude does).
fn down_term_ctx(ctx: &mut MetaCtx, hooks: &MetaHooks, t: DagId) -> Option<DagId> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    // Snapshot the head + children with immutable reads before building.
    enum DShape {
        Const(String),
        App(String, Vec<DagId>),
    }
    let shape = match ctx.repr(t) {
        NodeRepr::Qid(text) => DShape::Const(text.to_string()),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let NodeRepr::Qid(head) = ctx.repr(*kids.first()?) else {
                return None;
            };
            DShape::App(head.to_string(), down_arg_dags_ctx(ctx, hooks, *kids.get(1)?))
        }
        _ => return None,
    };
    match shape {
        DShape::Const(text) => {
            let (name, _sort) = text.rsplit_once('.')?;
            let sym = ctx.resolve_op(&strip_op_blanks(name), 0)?;
            Some(ctx.app(sym, vec![]))
        }
        DShape::App(head, arg_dags) => {
            let args: Vec<DagId> =
                arg_dags.iter().map(|&a| down_term_ctx(ctx, hooks, a)).collect::<Option<_>>()?;
            if let Some((base, count)) = head.rsplit_once('^')
                && let Ok(n) = count.parse::<u64>()
            {
                let sym = ctx.resolve_op(&strip_op_blanks(base), 1)?;
                return Some(ctx.make_iter(sym, n, *args.first()?));
            }
            let name = strip_op_blanks(&head);
            // Resolve by (name, arity); if that fails on a flat (≥3-arg) application, resolve the binary
            // symbol of an associative op and fold the flat args onto it (`ctx.app` builds the flattened
            // ACU/AU node — tnk's internal rep is already flat).
            let sym = ctx.resolve_op(&name, args.len()).or_else(|| {
                (args.len() >= 3)
                    .then(|| ctx.resolve_op(&name, 2).filter(|&s| ctx.symbol_is_assoc(s)))
                    .flatten()
            })?;
            Some(ctx.app(sym, args))
        }
    }
}

/// The DAG children of a `metaTermSymbol` argument list (`metaArgSymbol` flattens to its elements; anything
/// else is a single argument) — the raw arg DAGs, down-translated by the caller.
fn down_arg_dags_ctx(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Vec<DagId> {
    if Some(ctx.top(list)) == hooks.ops.get("metaArgSymbol").copied() {
        ctx.children(list)
    } else {
        vec![list]
    }
}

/// Up-translate the least sort of `t` (in `source`) to its meta `Type` — a `Qid` of the sort name.
fn up_sort(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
    ctx.make_na(qid, NaValue::Qid(sort.into()))
}

// ---- Stage 4: sort/kind query helpers (down a meta `Type`, up a `Bool`/`Type`/`SortSet`) ----

/// Down-translate a meta `Type` (`'Sort` or `'[Kind]`) into the object module's [`SortId`]. A bracketed
/// `'[Max,…]` is a kind → the component's error sort (resolved from the first maximal sort named); a bare
/// name is a sort. `None` if the named sort is not in `m`.
fn down_type(ctx: &MetaCtx, m: &BuiltModule, d: DagId) -> Option<SortId> {
    let text = qid_text(ctx, d)?;
    if let Some(inner) = text.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
        // A kind name `[Max]` / `[A,B]` — resolve via the component of the first maximal sort named.
        let first = inner.split(',').next()?.trim();
        let s = *m.sorts.get(first)?;
        Some(m.engine.sorts().error_sort(m.engine.sorts().kind_of(s)))
    } else {
        m.sorts.get(&text).copied()
    }
}

/// Up-translate a [`SortId`] to its meta `Type` — a `Qid` of the sort name (an error sort's name is the
/// bracketed `[Kind]` form, which prints back-quoted).
fn up_type(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, s: SortId) -> DagId {
    let name = m.engine.sorts().name(s).to_string();
    ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()))
}

/// Up-translate a sort list to a meta `TypeList` (`__`-joined `Qid`s; a singleton stays a `Type`, empty is
/// `nil`) — `maximalAritySet`'s argument-sort lists.
fn up_type_list(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, sorts: &[SortId]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let elems: Vec<DagId> = sorts
        .iter()
        .map(|&s| ctx.make_na(qid, NaValue::Qid(m.engine.sorts().name(s).into())))
        .collect();
    up_set(ctx, elems, hooks.ops["nilQidListSymbol"], hooks.ops["qidListSymbol"])
}

/// Build a META-LEVEL `Bool` result (`true`/`false`), resolved by name in the current module. `None` if
/// the current module has no boolean (it always does — META-LEVEL imports `BOOL`).
fn up_bool(ctx: &mut MetaCtx, b: bool) -> Option<DagId> {
    let sym = ctx.resolve_op(if b { "true" } else { "false" }, 0)?;
    Some(ctx.app(sym, vec![]))
}

/// Up-translate a set of sorts to a meta `SortSet`/`KindSet`/`TypeSet` — each as a `Qid`, joined by the
/// `_;_` ACU constructor; an empty set is `none`. The sort names are sorted so the (commutative) result is
/// deterministic; the kernel's ACU canonicalization then fixes the printed order.
fn up_sort_set(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, sorts: &[SortId]) -> DagId {
    let mut names: Vec<String> = sorts.iter().map(|&s| m.engine.sorts().name(s).to_string()).collect();
    names.sort();
    let qids: Vec<DagId> =
        names.iter().map(|n| ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(n.as_str().into()))).collect();
    match qids.len() {
        0 => ctx.app(hooks.ops["emptySortSetSymbol"], vec![]),
        1 => qids.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["sortSetSymbol"], qids),
    }
}

/// Whether DAG `t` (in `m`) is a well-formed term: every application's argument-kinds match the operator's
/// declared domain. Our kernel builds permissively at the kind level, so this is the explicit check
/// `wellFormed(M, T)` needs (Maude's `downTerm` returning 0 on an ill-typed term).
fn term_well_formed(m: &BuiltModule, t: DagId) -> bool {
    let sym = m.engine.node(t).symbol();
    let kids: Vec<DagId> = m.engine.node(t).children().collect();
    if let Some(syntax) = m.syntax.get(&sym)
        && syntax.domain.len() == kids.len()
    {
        let sorts = m.engine.sorts();
        for (k, &dom) in kids.iter().zip(&syntax.domain) {
            if !sorts.same_kind(m.engine.sort_of(*k), dom) {
                return false;
            }
        }
    }
    kids.iter().all(|&k| term_well_formed(m, k))
}

/// Whether meta `Substitution` `d` is well-formed in `m`: every assignment `'X:Sort <- value` has a value
/// that down-translates to a well-formed term whose kind matches the variable's sort. `wellFormed(M, S)`.
fn subst_well_formed(ctx: &MetaCtx, hooks: &MetaHooks, m: &mut BuiltModule, d: DagId) -> bool {
    let empty = hooks.ops.get("emptySubstitutionSymbol").copied();
    let join = hooks.ops.get("substitutionSymbol").copied();
    let assign = hooks.ops.get("assignmentSymbol").copied();
    for a in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(a)) != assign {
            return false;
        }
        let kids = ctx.children(a);
        let Some((_, sort_name)) = kids.first().and_then(|&k| qid_text(ctx, k)).and_then(|t| {
            t.split_once(':').map(|(n, s)| (n.to_string(), s.to_string()))
        }) else {
            return false;
        };
        let Some(&var_sort) = m.sorts.get(&sort_name) else {
            return false;
        };
        let Some(&val) = kids.get(1) else {
            return false;
        };
        match down_term(ctx, hooks, val, m) {
            Some(value) => {
                if !term_well_formed(m, value)
                    || !m.engine.sorts().same_kind(m.engine.sort_of(value), var_sort)
                {
                    return false;
                }
            }
            None => return false,
        }
    }
    true
}

// ---- Stage 4: the up* family helpers (decompose surface decls + traces into the meta-rep) ----

/// Which declaration-set an individual `up*` projection emits.
#[derive(Clone, Copy)]
enum UpPart {
    Sorts,
    Subsorts,
    Ops,
    Mbs,
    Eqs,
    Rls,
}

/// The decomposition of a built module: the surface sorts/subsorts/ops to emit (the whole closure for the
/// flat form, the module's own for the non-flat form), the import list (non-flat only), and the
/// memberships/equations/rules to up-translate — the flat build's whole trace vectors for the flat form, or
/// the module's own statements in **declaration order** for the non-flat form (executable statements from
/// the trace suffix, interleaved with `[nonexec]` axioms parsed on demand — they carry no engine trace).
struct ModulePieces {
    kind: ModuleKind,
    is_theory: bool,
    /// Formal parameters `{X :: T, …}` of a parameterized module (empty otherwise) — emitted in the
    /// `upModule` header (`fmod 'LIST{'X :: 'TRIV} is`) for the non-flat form.
    params: Vec<Parameter>,
    sorts: Vec<String>,
    subsorts: Vec<Vec<Vec<String>>>,
    ops: Vec<UpOp>,
    imports: Vec<Import>,
    mbs: Vec<MbTrace>,
    eqs: Vec<EqTrace>,
    rls: Vec<RlTrace>,
    loaded: LoadedModule,
}

/// Up-translate a statement list to its per-kind traces, in **declaration order**, interleaving executable
/// statements (which carry an engine trace) with `[nonexec]` axioms (which do not — [`load_statements`]
/// (tnk_frontend::load) skips them, since a proof obligation is applied by neither reduction nor
/// completion). Each executable statement of a kind takes the next entry of its trace vector starting at
/// `starts` (the whole vector — `(0,0,0)` — for the flat closure, or the own-statement suffix for the
/// non-flat form, since flatten appends a module's own statements after its imports in order); each nonexec
/// axiom is parsed on demand from its bubble against the built module. A nonexec statement that fails to
/// parse is skipped (the up result omits it but stays otherwise faithful — the meta layer's inert-on-
/// failure contract).
fn merge_statement_traces(
    stmts: &[Statement],
    loaded: &LoadedModule,
    i: &Interner,
    starts: (usize, usize, usize),
) -> (Vec<MbTrace>, Vec<EqTrace>, Vec<RlTrace>) {
    let b = &loaded.built;
    let (mut mb_i, mut eq_i, mut rl_i) = starts;
    let (mut mbs, mut eqs, mut rls) = (Vec::new(), Vec::new(), Vec::new());
    for stmt in stmts {
        match stmt {
            Statement::Mb { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Mb(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i) {
                        mbs.push(t);
                    }
                } else {
                    mbs.push(b.mb_traces[mb_i].clone());
                    mb_i += 1;
                }
            }
            Statement::Eq { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Eq(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i) {
                        eqs.push(t);
                    }
                } else {
                    eqs.push(b.eq_traces[eq_i].clone());
                    eq_i += 1;
                }
            }
            Statement::Rule { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Rl(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i) {
                        rls.push(t);
                    }
                } else {
                    rls.push(b.rl_traces[rl_i].clone());
                    rl_i += 1;
                }
            }
        }
    }
    (mbs, eqs, rls)
}

/// One operator to up-translate: its canonical name + the (pre-joined) identity-element name + the surface
/// declaration carrying its types and attributes.
struct UpOp {
    name: String,
    id_name: Option<String>,
    decl: OpDecl,
}

/// A meta `Bool` (`true`/`false`) → its value, by the constant's operator name.
fn down_bool(ctx: &MetaCtx, d: DagId) -> Option<bool> {
    match ctx.name(ctx.top(d)) {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// Whether a meta `PrintOptionSet` (a `__`-joined tree of option constants) contains the option named
/// `name` (e.g. `mixfix`) — a structural walk over the option set.
fn has_option(ctx: &MetaCtx, d: DagId, name: &str) -> bool {
    ctx.name(ctx.top(d)) == name || ctx.children(d).iter().any(|&c| has_option(ctx, c, name))
}

/// Join meta-rep set elements with an ACU/AU constructor: an empty set is `empty`, a singleton stays
/// itself, two or more are joined by `join` (the kernel canonicalizes the assoc/comm order).
fn up_set(ctx: &mut MetaCtx, elems: Vec<DagId>, empty: SymbolId, join: SymbolId) -> DagId {
    match elems.len() {
        0 => ctx.app(empty, vec![]),
        1 => elems.into_iter().next().unwrap(),
        _ => ctx.app(join, elems),
    }
}

/// Up-translate a parameterized-module header to `_{_}(name, ParameterDeclList)` (`headerSymbol`): each
/// parameter `X :: T` becomes `_::_('X, upModuleExpr(T))` (`parameterDeclSymbol`), joined by `_,_`
/// (`parameterDeclListSymbol`) — Maude's `upHeader`/`upParameterDecls`. `None` if the header symbols are
/// absent (a META-LEVEL predating parameterized headers).
fn up_header(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    name_qid: DagId,
    params: &[Parameter],
) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let decl_sym = *hooks.ops.get("parameterDeclSymbol")?;
    let decls: Vec<DagId> = params
        .iter()
        .map(|p| {
            let pname = ctx.make_na(qid, NaValue::Qid(p.name.as_str().into()));
            let theory = ctx.make_na(qid, NaValue::Qid(p.theory.as_str().into()));
            ctx.app(decl_sym, vec![pname, theory])
        })
        .collect();
    let decl_list = match decls.len() {
        1 => decls.into_iter().next().unwrap(),
        _ => ctx.app(*hooks.ops.get("parameterDeclListSymbol")?, decls),
    };
    Some(ctx.app(*hooks.ops.get("headerSymbol")?, vec![name_qid, decl_list]))
}

/// Up-translate an import list (`including_./protecting_./extending_.` of each module expression, joined by
/// `__`). Only a **named** module expression is handled; a sum/renaming/instantiation import returns `None`.
fn up_imports(ctx: &mut MetaCtx, hooks: &MetaHooks, imports: &[Import]) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let mut elems = Vec::with_capacity(imports.len());
    for imp in imports {
        let ModuleExpr::Named(name) = &imp.expr else {
            return None; // structured import expression — a follow-on
        };
        let name_qid = ctx.make_na(qid, NaValue::Qid(name.as_str().into()));
        let ctor = match imp.mode {
            ImportMode::Protecting => "protectingSymbol",
            ImportMode::Extending => "extendingSymbol",
            ImportMode::Including => "includingSymbol",
        };
        elems.push(ctx.app(*hooks.ops.get(ctor)?, vec![name_qid]));
    }
    Some(up_set(ctx, elems, hooks.ops["nilImportListSymbol"], hooks.ops["importListSymbol"]))
}

/// Up-translate a module expression to a meta `ModuleExpression`. A named module is its `Qid`; a structured
/// expression (summation / renaming / instantiation) is a follow-on (`None`), so `upView`/`upImports` of a
/// structured `from`/`to`/import stays inert rather than emit a wrong shape.
fn up_module_expr(ctx: &mut MetaCtx, hooks: &MetaHooks, e: &ModuleExpr) -> Option<DagId> {
    match e {
        ModuleExpr::Named(name) => Some(ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.as_str().into()))),
        _ => None,
    }
}

/// Up-translate a sort-name list to a `SortSet` (`;`-joined `Qid`s, sorted for a deterministic ACU result).
fn up_sorts_dag(ctx: &mut MetaCtx, hooks: &MetaHooks, sorts: &[String]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let mut names: Vec<&str> = sorts.iter().map(|s| s.as_str()).collect();
    names.sort_unstable();
    let elems: Vec<DagId> = names.iter().map(|n| ctx.make_na(qid, NaValue::Qid((*n).into()))).collect();
    up_set(ctx, elems, hooks.ops["emptySortSetSymbol"], hooks.ops["sortSetSymbol"])
}

/// Up-translate the subsort chains to a `SubsortDeclSet` — one `subsort A < B .` per consecutive pair of a
/// chain `A … < B … < C` (every member of one group below every member of the next), joined by `__`.
fn up_subsorts_dag(ctx: &mut MetaCtx, hooks: &MetaHooks, chains: &[Vec<Vec<String>>]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let subsort = hooks.ops["subsortSymbol"];
    let mut elems = Vec::new();
    for chain in chains {
        for pair in chain.windows(2) {
            for sub in &pair[0] {
                for sup in &pair[1] {
                    let a = ctx.make_na(qid, NaValue::Qid(sub.as_str().into()));
                    let b = ctx.make_na(qid, NaValue::Qid(sup.as_str().into()));
                    elems.push(ctx.app(subsort, vec![a, b]));
                }
            }
        }
    }
    up_set(ctx, elems, hooks.ops["emptySubsortDeclSetSymbol"], hooks.ops["subsortDeclSetSymbol"])
}

/// Up-translate operator declarations to an `OpDeclSet` (`__`-joined `op N : D -> R [A] .`, sorted by
/// canonical name as Maude orders its symbol table). `None` if any op carries an attribute the up-map does
/// not yet reconstruct (`special`/`poly` — the builtin-hook surface, the inverse of `down_attrs`' boundary).
fn up_ops_dag(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, ops: &[UpOp]) -> Option<DagId> {
    let mut sorted: Vec<&UpOp> = ops.iter().collect();
    sorted.sort_by(|a, b| a.name.cmp(&b.name));
    let mut elems = Vec::with_capacity(sorted.len());
    for op in sorted {
        // `ditto` inherits the operator's full (symbol-wide) attribute set from its primary declaration —
        // the same-name non-`ditto` op. Maude's `upModule` emits the *expanded* attributes on every subsort
        // overload (`[assoc ctor id(…) prec(25)]`), not the bare `[ctor ditto]` the source carries.
        let attr_op = if op.decl.attrs.ditto {
            ops.iter().find(|o| o.name == op.name && !o.decl.attrs.ditto).unwrap_or(op)
        } else {
            op
        };
        elems.push(up_op_decl(ctx, hooks, m, op, attr_op)?);
    }
    Some(up_set(ctx, elems, hooks.ops["emptyOpDeclSetSymbol"], hooks.ops["opDeclSetSymbol"]))
}

/// Up-translate one operator declaration `op N : D -> R [A] .` (`opDeclSymbol`): the name `Qid`, the
/// domain as a `TypeList` (`__`-joined sort `Qid`s, `nil` for a constant), the range `Type`, the `AttrSet`.
/// `op` supplies the name/domain/range; `attr_op` supplies the attribute set (they differ only for a
/// `ditto` overload, whose attributes come from the operator's primary declaration).
fn up_op_decl(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    op: &UpOp,
    attr_op: &UpOp,
) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let name = ctx.make_na(qid, NaValue::Qid(meta_op_name(&op.name).into()));
    let dom_elems: Vec<DagId> =
        op.decl.domain.iter().map(|s| ctx.make_na(qid, NaValue::Qid(s.as_str().into()))).collect();
    let domain = up_set(ctx, dom_elems, hooks.ops["nilQidListSymbol"], hooks.ops["qidListSymbol"]);
    // A partial op (`~>`) ranges over its kind; render the kind name (`[Range]`) the engine assigned it.
    let range_name = if op.decl.partial {
        match m.sorts.get(&op.decl.range) {
            Some(&s) => m.engine.sorts().name(m.engine.sorts().error_sort(m.engine.sorts().kind_of(s))).to_string(),
            None => op.decl.range.clone(),
        }
    } else {
        op.decl.range.clone()
    };
    let range = ctx.make_na(qid, NaValue::Qid(range_name.into()));
    let attrs = up_attrs(ctx, hooks, m, attr_op)?;
    Some(ctx.app(hooks.ops["opDeclSymbol"], vec![name, domain, range, attrs]))
}

/// Up-translate an operator's surface [`Attrs`] to a meta `AttrSet`. Reconstructs the structural/parse
/// attributes (`ctor`/`assoc`/`comm`/`idem`/`iter`/`id:`/`prec`/`gather`/`format`/`frozen`/`strat`/`memo`);
/// `None` on `special`/`poly` (the builtin-hook surface — the inverse of [`down_attrs`]' boundary). The set
/// is ACU, so build order does not fix the printed order.
fn up_attrs(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, op: &UpOp) -> Option<DagId> {
    let a = &op.decl.attrs;
    if a.special.is_some() || a.poly.is_some() {
        return None; // builtin-hook / polymorph attribute surface — the documented boundary
    }
    let mut elems = Vec::new();
    let flag = |name: &str, on: bool, ctx: &mut MetaCtx, elems: &mut Vec<DagId>| {
        // Tolerant of a META-LEVEL that predates a given attribute symbol: skip rather than panic.
        if on && let Some(&s) = hooks.ops.get(name) {
            elems.push(ctx.app(s, vec![]));
        }
    };
    flag("ctorSymbol", a.ctor, ctx, &mut elems);
    flag("assocSymbol", a.assoc, ctx, &mut elems);
    flag("commSymbol", a.comm, ctx, &mut elems);
    flag("idemSymbol", a.idem, ctx, &mut elems);
    flag("iterSymbol", a.iter, ctx, &mut elems);
    // Object-system attributes (Pillar 2.5): `config`/`object`/`msg`/`portal`. An `omod`'s desugared ops
    // carry these (e.g. `msg` on message operators), and Maude's `upModule` emits them on the plain `mod`.
    flag("configSymbol", a.config, ctx, &mut elems);
    flag("objectSymbol", a.object, ctx, &mut elems);
    flag("msgSymbol", a.message, ctx, &mut elems);
    flag("portalSymbol", a.portal, ctx, &mut elems);
    if let Some(prec) = a.prec {
        let n = up_nat(ctx, prec as u64)?;
        elems.push(ctx.app(hooks.ops["precSymbol"], vec![n]));
    }
    if let Some(gather) = &a.gather {
        elems.push(up_gather(ctx, hooks, gather));
    }
    if let Some(format) = &a.format {
        let qid = hooks.ops["qidSymbol"];
        let words: Vec<DagId> =
            format.iter().map(|w| ctx.make_na(qid, NaValue::Qid(w.as_str().into()))).collect();
        let list = up_set(ctx, words, hooks.ops["nilQidListSymbol"], hooks.ops["qidListSymbol"]);
        elems.push(ctx.app(hooks.ops["formatSymbol"], vec![list]));
    }
    if let Some(name) = &op.id_name {
        // `id(c)` — the identity constant `'c.Sort` (resolved from the constant's range sort in `m`).
        let sort = m.ops.get(&(name.clone(), 0)).map(|&s| sort_name_of(m, s)).unwrap_or_default();
        let c = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(format!("{name}.{sort}").into()));
        elems.push(ctx.app(hooks.ops["idSymbol"], vec![c]));
    }
    if let Some(strat) = &a.strat {
        let n = up_nat_list(ctx, hooks, strat)?;
        elems.push(ctx.app(hooks.ops["stratSymbol"], vec![n]));
    }
    if let Some(frozen) = &a.frozen {
        let positions: Vec<u32> =
            if frozen.is_empty() { (1..=op.decl.domain.len() as u32).collect() } else { frozen.clone() };
        let n = up_nat_list(ctx, hooks, &positions)?;
        elems.push(ctx.app(hooks.ops["frozenSymbol"], vec![n]));
    }
    Some(up_set(ctx, elems, hooks.ops["emptyAttrSetSymbol"], hooks.ops["attrSetSymbol"]))
}

/// Up-translate a `gather (…)` pattern (`gatherSymbol` of a `QidList` of `'e`/`'E`/`'&`).
fn up_gather(ctx: &mut MetaCtx, hooks: &MetaHooks, gather: &[GatherElem]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let words: Vec<DagId> = gather
        .iter()
        .map(|g| {
            let s = match g {
                GatherElem::Weak => "e",
                GatherElem::Strong => "E",
                GatherElem::Any => "&",
            };
            ctx.make_na(qid, NaValue::Qid(s.into()))
        })
        .collect();
    let list = up_set(ctx, words, hooks.ops["nilQidListSymbol"], hooks.ops["qidListSymbol"]);
    ctx.app(hooks.ops["gatherSymbol"], vec![list])
}

/// Up-translate a `u64` to a meta `Nat` — `'0.Zero` for 0, else the `iter` successor `s_^n(0)`, built in
/// the current module (META-LEVEL imports `NAT`). `None` if `NAT`'s `0`/`s_` are not in scope.
fn up_nat(ctx: &mut MetaCtx, n: u64) -> Option<DagId> {
    let zero = ctx.app(ctx.resolve_op("0", 0)?, vec![]);
    if n == 0 {
        Some(zero)
    } else {
        Some(ctx.make_iter(ctx.resolve_op("s_", 1)?, n, zero))
    }
}

/// Up-translate a 1-based position list to a meta `NatList` (`__`-joined `Nat`s; a singleton stays a `Nat`).
fn up_nat_list(ctx: &mut MetaCtx, hooks: &MetaHooks, positions: &[u32]) -> Option<DagId> {
    let nats: Vec<DagId> = positions.iter().map(|&p| up_nat(ctx, p as u64)).collect::<Option<_>>()?;
    Some(match nats.len() {
        1 => nats.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["natListSymbol"], nats),
    })
}

/// Up-translate the membership traces in `range` to a `MembAxSet` (`mb`/`cmb` joined by `__`).
/// Build a statement `AttrSet` from its retained attributes — the `owise`/`nonexec` flags and an optional
/// `label(Q)` — joined ACU (`none` when empty, the `[none]` an unattributed statement prints). The set is
/// order-independent; Maude renders it in its own ACU order (a fixture pins the common `[nonexec label('l)]`).
fn stmt_attr_set(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    owise: bool,
    nonexec: bool,
    label: Option<&str>,
) -> DagId {
    let mut elems = Vec::new();
    if owise && let Some(&s) = hooks.ops.get("owiseSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if nonexec && let Some(&s) = hooks.ops.get("nonexecSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if let Some(l) = label {
        let lqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(l.into()));
        elems.push(ctx.app(hooks.ops["labelSymbol"], vec![lqid]));
    }
    up_set(ctx, elems, hooks.ops["emptyAttrSetSymbol"], hooks.ops["attrSetSymbol"])
}

fn up_membs_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    traces: &[MbTrace],
) -> Option<DagId> {
    let mut elems = Vec::new();
    for t in traces {
        let lhs = up_pattern(ctx, hooks, m, &t.lhs, &t.var_names);
        let sort = up_type(ctx, hooks, m, t.sort);
        let attrs = stmt_attr_set(ctx, hooks, false, t.nonexec, t.label.as_deref());
        let mb = if t.condition.is_empty() {
            ctx.app(hooks.ops["mbSymbol"], vec![lhs, sort, attrs])
        } else {
            let cond = up_condition(ctx, hooks, m, &t.condition, &t.var_names);
            ctx.app(hooks.ops["cmbSymbol"], vec![lhs, sort, cond, attrs])
        };
        elems.push(mb);
    }
    Some(up_set(ctx, elems, hooks.ops["emptyMembAxSetSymbol"], hooks.ops["membAxSetSymbol"]))
}

/// Up-translate the equation traces to an `EquationSet` (`eq`/`ceq` joined by `__`), each carrying its
/// `[owise]`/`[nonexec]`/`[label('l)]` attributes (`[none]` if plain).
fn up_eqs_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    traces: &[EqTrace],
) -> Option<DagId> {
    let mut elems = Vec::new();
    for t in traces {
        let lhs = up_pattern(ctx, hooks, m, &t.lhs, &t.var_names);
        let rhs = up_pattern(ctx, hooks, m, &t.rhs, &t.var_names);
        let attrs = stmt_attr_set(ctx, hooks, t.owise, t.nonexec, t.label.as_deref());
        let eq = if t.condition.is_empty() {
            ctx.app(hooks.ops["eqSymbol"], vec![lhs, rhs, attrs])
        } else {
            let cond = up_condition(ctx, hooks, m, &t.condition, &t.var_names);
            ctx.app(hooks.ops["ceqSymbol"], vec![lhs, rhs, cond, attrs])
        };
        elems.push(eq);
    }
    Some(up_set(ctx, elems, hooks.ops["emptyEquationSetSymbol"], hooks.ops["equationSetSymbol"]))
}

/// Up-translate the rule traces in `range` to a `RuleSet` (`rl`/`crl` joined by `__`); a labelled rule
/// carries `label(Q)`, others `[none]`.
fn up_rls_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    traces: &[RlTrace],
) -> Option<DagId> {
    let mut elems = Vec::new();
    for t in traces {
        elems.push(up_rule(ctx, hooks, m, t)?);
    }
    Some(up_set(ctx, elems, hooks.ops["emptyRuleSetSymbol"], hooks.ops["ruleSetSymbol"]))
}

/// Up-translate a condition (the inverse of [`down_condition`]): one fragment stays itself, several are
/// `_/\_`-conjoined. Each fragment is `_=_`/`_:_`/`_:=_`/`_=>_`.
fn up_condition(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    frags: &[ConditionFragment],
    names: &[String],
) -> DagId {
    let ups: Vec<DagId> = frags.iter().map(|f| up_condition_fragment(ctx, hooks, m, f, names)).collect();
    match ups.len() {
        1 => ups.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["conjunctionSymbol"], ups),
    }
}

/// Up-translate one condition fragment to its meta constructor.
fn up_condition_fragment(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    f: &ConditionFragment,
    names: &[String],
) -> DagId {
    match f {
        ConditionFragment::Equality { lhs, rhs } => {
            let l = up_pattern(ctx, hooks, m, lhs, names);
            let r = up_pattern(ctx, hooks, m, rhs, names);
            ctx.app(hooks.ops["equalityConditionSymbol"], vec![l, r])
        }
        ConditionFragment::SortTest { term, sort } => {
            let t = up_pattern(ctx, hooks, m, term, names);
            let s = up_type(ctx, hooks, m, *sort);
            ctx.app(hooks.ops["sortTestConditionSymbol"], vec![t, s])
        }
        ConditionFragment::Matching { pattern, subject, .. } => {
            let p = up_pattern(ctx, hooks, m, pattern, names);
            let s = up_pattern(ctx, hooks, m, subject, names);
            ctx.app(hooks.ops["matchConditionSymbol"], vec![p, s])
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            let l = up_pattern(ctx, hooks, m, lhs, names);
            let p = up_pattern(ctx, hooks, m, pattern, names);
            ctx.app(hooks.ops["rewriteConditionSymbol"], vec![l, p])
        }
    }
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
    let up_args: Vec<DagId> = if rest.is_empty() && source.engine.symbol_is_assoc(sym) {
        // AC/AU **extension** context: the matched subterm is a direct child of an associative node, so the
        // hole stands for the matched sub-multiset. Maude places the residue arguments first and the hole
        // LAST (`'_+_['b.S, []]`), independent of the matched child's canonical index — not the child's slot.
        let mut args: Vec<DagId> = children
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != head)
            .map(|(_, &c)| up_term(ctx, hooks, source, c))
            .collect();
        args.push(ctx.app(hooks.ops["holeSymbol"], vec![]));
        args
    } else {
        // Free (positional) node, or a rewrite strictly *inside* one associative argument (not an extension
        // at this node): keep every argument in its slot, recursing into the hole-carrying child.
        children
            .iter()
            .enumerate()
            .map(|(i, &c)| {
                if i == head {
                    up_context(ctx, hooks, source, c, rest)
                } else {
                    up_term(ctx, hooks, source, c)
                }
            })
            .collect()
    };
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
                NaValue::Str(s) => format!("{:?}", String::from_utf8_lossy(s)),
                NaValue::Qid(q) => format!("'{q}"),
                NaValue::Float(b) => format!("{}", f64::from_bits(*b)),
            };
            ctx.make_na(qid, NaValue::Qid(format!("{rendered}.{}", sort_name_of(source, *symbol)).into()))
        }
        Term::Op { symbol, args } if args.is_empty() => {
            let name = meta_op_name(source.engine.symbol(*symbol).name());
            ctx.make_na(qid, NaValue::Qid(format!("{name}.{}", sort_name_of(source, *symbol)).into()))
        }
        // Iter-chain collapse: a successor chain `s(s(…x))` (nested unary `iter` ops, as a rule side stores
        // it) prints as `'s_^n[up(x)]` — the compact `S`-symbol form, matching how `up_term` ups a DAG's
        // iter node and what the reference emits.
        Term::Op { symbol, args }
            if Some(*symbol) == source.nat_succ && args.len() == 1 =>
        {
            let mut count = 1u64;
            let mut inner = &args[0];
            while let Term::Op { symbol: s2, args: a2 } = inner {
                if Some(*s2) == source.nat_succ && a2.len() == 1 {
                    count += 1;
                    inner = &a2[0];
                } else {
                    break;
                }
            }
            let base = meta_op_name(source.engine.symbol(*symbol).name());
            let head = if count == 1 { base } else { format!("{base}^{count}") };
            let up_inner = up_pattern(ctx, hooks, source, inner, names);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_inner])
        }
        Term::Op { symbol, args } => {
            let name = meta_op_name(source.engine.symbol(*symbol).name());
            // Flatten a nested associative operator to Maude's `makeTerm` normal form (`__(a, __(b,c))` ->
            // `__(a,b,c)`) — tnk's parser stores ACU/AU patterns binary-nested. Associativity is irrelevant
            // to matching, so this normalizes only the meta form. We deliberately DON'T reorder ACU
            // arguments here: a user-written term (`N + M`) is stored in source order, which is already the
            // reference's order (Maude sorts by `Term::compare`, whose variable tie-break is interning-order
            // name codes — the same source order); an *added* attribute set is instead ordered at
            // construction (`oo_complete::canonicalize_attr_set`).
            let mut flat: Vec<&Term> = Vec::new();
            if source.engine.symbol_is_assoc(*symbol) {
                flatten_assoc_args(*symbol, args, &mut flat);
            } else {
                flat.extend(args.iter());
            }
            let up_args: Vec<DagId> =
                flat.iter().map(|a| up_pattern(ctx, hooks, source, a, names)).collect();
            let arglist = up_arglist(ctx, hooks, up_args);
            let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
        }
    }
}

/// Flatten a nested associative application `f(a, f(b, c), …)` into its argument sequence `[a, b, c, …]`
/// (Maude's `AU/ACU_Term` flat representation), recursing through same-symbol arguments.
fn flatten_assoc_args<'t>(symbol: SymbolId, args: &'t [Term], out: &mut Vec<&'t Term>) {
    for a in args {
        match a {
            Term::Op { symbol: s2, args: a2 } if *s2 == symbol => flatten_assoc_args(symbol, a2, out),
            _ => out.push(a),
        }
    }
}


/// The declared range-sort name of operator `symbol` (its `SymbolSyntax`), for a constant's `'c.Sort`.
fn sort_name_of(source: &BuiltModule, symbol: SymbolId) -> String {
    source.syntax.get(&symbol).map(|s| source.engine.sorts().name(s.range).to_string()).unwrap_or_default()
}

/// Up-translate a rule (from its trace) to a meta `Rule` — `rl lhs => rhs [label] .`, or `crl lhs => rhs if
/// cond [label] .` for a conditional rule (the condition up-mapped by [`up_condition`]).
fn up_rule(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, trace: &RlTrace) -> Option<DagId> {
    let up_lhs = up_pattern(ctx, hooks, source, &trace.lhs, &trace.var_names);
    let up_rhs = up_pattern(ctx, hooks, source, &trace.rhs, &trace.var_names);
    let attrs = stmt_attr_set(ctx, hooks, false, trace.nonexec, trace.label.as_deref());
    Some(if trace.condition.is_empty() {
        ctx.app(hooks.ops["rlSymbol"], vec![up_lhs, up_rhs, attrs])
    } else {
        let cond = up_condition(ctx, hooks, source, &trace.condition, &trace.var_names);
        ctx.app(hooks.ops["crlSymbol"], vec![up_lhs, up_rhs, cond, attrs])
    })
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
