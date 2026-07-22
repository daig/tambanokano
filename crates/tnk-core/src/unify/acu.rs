//! AC / ACU unification — Maude's `ACU_UnificationSubproblem2`
//! (`src/ACU_Theory/ACU_UnificationSubproblem2.cc`). Order-faithful, including the enumeration
//! order (which fixes the AC-unifier order and hence the `#n` numbering).
//!
//! Shape: each `f(…) =? f(…)` (or `f(…) =? X`) contributes a **signed-multiplicity multiset
//! equation** over distinct abstracted subterms (variables kept as chain representatives, never
//! substituted — the termination rule). The homogeneous Diophantine system's **Hilbert basis**
//! ([`crate::int_system`]) gives the building blocks; a **subset selection** over the basis (a
//! greedy include-first DFS with coverage/upper-bound pruning for pure AC; a BDD + `AllSat`
//! maximal-selection enumeration for ACU with identity) yields each unifier, materialized by
//! `build_solution`. ACU unification is **finitary** — it never flags incompleteness.

use super::{
    Marker, PendingStack, SavedSubst, UnifyContext, UnifyEnv, compute_solved_form,
    last_variable_in_chain, var_index,
};
use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::int_system::{IntSystem, UNBOUNDED};
use crate::sort_bdds::AllSat;
use crate::symbol::{SymbolClass, SymbolId};
use biodivine_lib_bdd::{Bdd, BddVariableSet};
use std::collections::BTreeSet;

/// One Hilbert-basis element (a minimal Diophantine solution accepted into the basis).
struct Entry {
    /// The solution vector: `element[i]` = how many of abstract-variable `i` this element assigns.
    element: Vec<i32>,
    /// Subterms covered by every element discovered **before** this one (= covered by the elements
    /// that follow it in `basis` iteration order) — the coverage-feasibility oracle for `next_selection`.
    remainder: BTreeSet<usize>,
    /// Discovery-order id (0,1,2,…) — the BDD variable / `AllSat` bit for the identity path.
    index: usize,
}

pub(crate) struct AcuSubproblem {
    top: SymbolId,
    has_identity: bool,
    /// Distinct abstracted subterms (chain-representative variables and aliens), first-encounter order.
    subterms: Vec<DagId>,
    /// Scratch multiplicity vector, reused per `add_unification`.
    multiplicities: Vec<i32>,
    /// The recorded multiset equations (each padded to `subterms.len()` at solve time).
    unifications: Vec<Vec<i32>>,
    marked_subterms: BTreeSet<usize>,
    /// Hilbert basis in iteration order (reverse discovery — Maude's `push_front` list).
    basis: Vec<Entry>,
    upper_bounds: Vec<i32>,
    need_to_cover: BTreeSet<usize>,
    accumulator: BTreeSet<usize>,
    totals: Vec<i32>,
    uncovered: BTreeSet<usize>,
    /// Selected basis-element indices (into `basis`).
    selection: Vec<usize>,
    /// `next_selection` cursor into `basis`.
    current: usize,
    pre_solve: SavedSubst,
    saved_subst: SavedSubst,
    saved_pending: Marker,
    /// Identity path: the maximal-selection enumerator over the basis-element BDD variables.
    maximal_selections: Option<AllSat>,
}

/// The `(element, multiplicity)` multiset of an ACU node in Maude's pre-index variable order.
/// Variables sharing a sort share a `VariableSymbol`, so their name codes order them.  Variables
/// of different sorts are ordered by distinct symbols created before indexing; their assigned slot
/// order records that comparison even when tnk's per-variable symbol ids do not.
fn acu_pairs(e: &Engine, id: DagId) -> Vec<(DagId, u32)> {
    let mut pairs = match &e.node(id).term {
        NodeTerm::Acu { args, .. } => args.clone(),
        _ => unreachable!("acu_pairs on a non-ACU node"),
    };
    pairs.sort_by(
        |&(a, _), &(b, _)| match (&e.node(a).term, &e.node(b).term) {
            (NodeTerm::Var { name: an, .. }, NodeTerm::Var { name: bn, .. }) => {
                if e.sort_of(a) == e.sort_of(b) {
                    an.cmp(bn)
                } else {
                    var_index(e, a).unwrap().cmp(&var_index(e, b).unwrap())
                }
            }
            _ => e.dag_compare(a, b),
        },
    );
    pairs
}

/// Maude's virtual `Symbol::isStable`: free, NA, and S symbols are stable; binary-theory symbols
/// are stable exactly when they have no identity collapse. Genuine variable symbols are unstable.
pub(super) fn is_stable(e: &Engine, sym: SymbolId) -> bool {
    let symbol = e.symbol(sym);
    !matches!(
        symbol.class,
        SymbolClass::Variable { .. } | SymbolClass::SortVariable
    ) && symbol.identity().is_none()
        && !symbol.one_sided_identity()
}

impl AcuSubproblem {
    pub(crate) fn new(e: &Engine, top: SymbolId) -> AcuSubproblem {
        AcuSubproblem {
            top,
            has_identity: e.symbol(top).identity().is_some(),
            subterms: Vec::new(),
            multiplicities: Vec::new(),
            unifications: Vec::new(),
            marked_subterms: BTreeSet::new(),
            basis: Vec::new(),
            upper_bounds: Vec::new(),
            need_to_cover: BTreeSet::new(),
            accumulator: BTreeSet::new(),
            totals: Vec::new(),
            uncovered: BTreeSet::new(),
            selection: Vec::new(),
            current: 0,
            pre_solve: Vec::new(),
            saved_subst: Vec::new(),
            saved_pending: 0,
            maximal_selections: None,
        }
    }

    pub(crate) fn gc_roots(&self) -> Vec<DagId> {
        self.subterms
            .iter()
            .copied()
            .chain(self.pre_solve.iter().copied().flatten())
            .chain(self.saved_subst.iter().copied().flatten())
            .collect()
    }

    /// Whether `id` is the operator's two-sided identity term.
    fn is_identity(&self, e: &Engine, id: DagId) -> bool {
        e.symbol(self.top)
            .identity()
            .is_some_and(|identity| e.is_identity(identity, id))
    }

    // ---- addUnification ------------------------------------------------------------------

    pub(crate) fn add_unification(
        &mut self,
        e: &Engine,
        ctx: &UnifyContext,
        lhs: DagId,
        rhs: DagId,
        marked: bool,
    ) {
        let n_old = self.subterms.len();
        // Ensure the scratch vector spans all existing subterms, reset to 0.
        self.multiplicities.resize(n_old, 0);
        for m in &mut self.multiplicities {
            *m = 0;
        }
        // RHS.
        if e.node(rhs).symbol() == self.top {
            for (elem, mult) in acu_pairs(e, rhs) {
                self.set_multiplicity(e, ctx, elem, -(mult as i32));
            }
        } else if !self.is_identity(e, rhs) {
            let idx = self.set_multiplicity(e, ctx, rhs, -1);
            if marked && let Some(i) = idx {
                self.marked_subterms.insert(i);
            }
        }
        // LHS (always our top symbol).
        for (elem, mult) in acu_pairs(e, lhs) {
            self.set_multiplicity(e, ctx, elem, mult as i32);
        }
        self.kill_cancelled_subterms(n_old);
        if self.multiplicities.iter().any(|&m| m != 0) {
            self.unifications.push(self.multiplicities.clone());
        }
    }

    /// `setMultiplicity`: resolve a variable to its chain representative (no eager substitution;
    /// identity binding ⇒ eliminated), then add `multiplicity` to that subterm's entry (creating it
    /// in first-encounter order). Returns the subterm index, or `None` for an identity variable.
    fn set_multiplicity(
        &mut self,
        e: &Engine,
        ctx: &UnifyContext,
        dag: DagId,
        multiplicity: i32,
    ) -> Option<usize> {
        let mut dag = dag;
        if var_index(e, dag).is_some() {
            let rep = last_variable_in_chain(e, ctx, dag);
            if self.has_identity
                && let Some(subject) = ctx.value(var_index(e, rep).unwrap() as usize)
                && self.is_identity(e, subject)
            {
                return None;
            }
            dag = rep;
        }
        for i in 0..self.subterms.len() {
            if e.deep_equal(dag, self.subterms[i]) {
                self.multiplicities[i] += multiplicity;
                return Some(i);
            }
        }
        self.subterms.push(dag);
        self.multiplicities.push(multiplicity);
        Some(self.subterms.len() - 1)
    }

    fn kill_cancelled_subterms(&mut self, n_old: usize) {
        let n = self.subterms.len();
        if n <= n_old {
            return;
        }
        let mut dest = n_old;
        for i in n_old..n {
            if self.multiplicities[i] != 0 {
                if dest < i {
                    self.subterms[dest] = self.subterms[i];
                    self.multiplicities[dest] = self.multiplicities[i];
                }
                dest += 1;
            }
        }
        self.subterms.truncate(dest);
        self.multiplicities.truncate(dest);
    }

    // ---- solve ---------------------------------------------------------------------------

    pub(crate) fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        if self.unifications.is_empty() {
            return find_first;
        }
        if find_first {
            self.pre_solve = ctx.clone_subst();
            // Unsolve in-theory bindings (X = f(…) → equation f(…) =? X) for termination.
            for i in 0..ctx.n_slots() {
                if let Some(value) = ctx.value(i)
                    && env.e.node(value).symbol() == self.top
                {
                    self.unsolve(env.e, ctx, i);
                }
            }
            if !self.build_and_solve_diophantine_system(env, ctx) {
                ctx.restore_from_clone(&self.pre_solve);
                return false;
            }
            if self.has_identity {
                self.maximal_selections = Some(self.compute_maximal_selections(env.e));
            }
            self.saved_subst = ctx.clone_subst();
            self.saved_pending = pending.checkpoint();
        } else {
            pending.restore(self.saved_pending);
            ctx.restore_from_clone(&self.saved_subst);
        }
        let mut find_first = find_first;
        loop {
            let more = if self.has_identity {
                self.next_selection_with_identity()
            } else {
                self.next_selection(find_first)
            };
            if !more {
                break;
            }
            find_first = false;
            if self.build_solution(env, ctx, pending) {
                return true;
            }
            pending.restore(self.saved_pending);
            ctx.restore_from_clone(&self.saved_subst);
        }
        ctx.restore_from_clone(&self.pre_solve);
        false
    }

    /// `unsolve`: turn an existing in-theory solved form `X = f(…)` at slot `index` back into an
    /// equation so it is solved simultaneously with the current batch.
    fn unsolve(&mut self, e: &Engine, ctx: &mut UnifyContext, index: usize) {
        let variable = ctx
            .variable_node(index)
            .expect("in-theory binding has a tracked variable");
        let value = ctx.value(index).expect("unsolving an unbound slot");
        ctx.bind(index, None);
        self.multiplicities.resize(self.subterms.len(), 0);
        for m in &mut self.multiplicities {
            *m = 0;
        }
        let n_old = self.subterms.len();
        for (elem, mult) in acu_pairs(e, value) {
            self.set_multiplicity(e, ctx, elem, mult as i32);
        }
        self.set_multiplicity(e, ctx, variable, -1);
        self.kill_cancelled_subterms(n_old);
        self.unifications.push(self.multiplicities.clone());
    }

    // ---- classify + Diophantine basis ----------------------------------------------------

    /// Per-subterm classification: `(can_take_identity, upper_bound, stable_symbol)`.
    fn classify(
        &self,
        e: &Engine,
        ctx: &UnifyContext,
        subterm_index: usize,
    ) -> (bool, i32, Option<SymbolId>) {
        let has_id = self.has_identity;
        let mut can_take_identity = has_id;
        let mut upper_bound = if self.marked_subterms.contains(&subterm_index) {
            1
        } else {
            UNBOUNDED
        };
        let mut subject = self.subterms[subterm_index];
        if var_index(e, subject).is_some() {
            let sort = e.sort_of(subject);
            let bound = e
                .signature()
                .acu_sort_bounds(self.top)
                .get(&sort)
                .copied()
                .unwrap_or(UNBOUNDED);
            if bound < upper_bound {
                upper_bound = bound;
            }
            can_take_identity =
                can_take_identity && e.signature().acu_take_identity(self.top, sort);
            let rep = last_variable_in_chain(e, ctx, subject);
            match ctx.value(var_index(e, rep).unwrap() as usize) {
                None => return (can_take_identity, upper_bound, None),
                Some(bound_to) => subject = bound_to,
            }
        }
        let symbol = e.node(subject).symbol();
        if super::is_ground(e, subject) {
            (false, 1, Some(symbol))
        } else if is_stable(e, symbol) {
            let identity_symbol = e.symbol(self.top).identity().map(|identity| {
                match e.signature().identity_term(identity) {
                    crate::term::Term::Var(_) => {
                        unreachable!("an identity term must be ground")
                    }
                    crate::term::Term::Na { symbol, .. }
                    | crate::term::Term::Op { symbol, .. }
                    | crate::term::Term::Iter { symbol, .. } => *symbol,
                }
            });
            (
                can_take_identity && identity_symbol == Some(symbol),
                1,
                Some(symbol),
            )
        } else {
            (can_take_identity, upper_bound, None)
        }
    }

    /// Build the homogeneous Diophantine system, extract its Hilbert basis (killing stable-symbol
    /// conflicts), and set up the selection state. `false` if a must-cover subterm can't be covered.
    fn build_and_solve_diophantine_system(&mut self, env: &UnifyEnv, ctx: &UnifyContext) -> bool {
        let n = self.subterms.len();
        let mut system = IntSystem::new(n);
        for eqn in &self.unifications {
            system.insert_eqn(eqn);
        }
        self.upper_bounds = vec![0; n];
        let mut bounds = vec![0; n];
        let mut stable_symbols: Vec<Option<SymbolId>> = vec![None; n];
        for i in 0..n {
            let (can_take_identity, upper_bound, stable) = self.classify(env.e, ctx, i);
            if !can_take_identity {
                self.need_to_cover.insert(i);
            }
            self.upper_bounds[i] = upper_bound;
            bounds[i] = upper_bound;
            stable_symbols[i] = stable;
        }
        system.set_upper_bounds(&bounds);

        // Basis extraction (discovery order); reversed into iteration order at the end.
        let mut disc: Vec<Entry> = Vec::new();
        let mut index = 0;
        while let Some(dio_sol) = system.find_next_minimal_solution() {
            // Stable-symbol conflict: two different stable tops forced to co-occur ⇒ impossible.
            let mut existing: Option<SymbolId> = None;
            let mut kill = false;
            for i in 0..n {
                if dio_sol[i] != 0
                    && let Some(s) = stable_symbols[i]
                {
                    match existing {
                        None => existing = Some(s),
                        Some(prev) if prev != s => {
                            kill = true;
                            break;
                        }
                        _ => {}
                    }
                }
            }
            if kill {
                continue;
            }
            let remainder = self.accumulator.clone();
            for i in 0..n {
                if dio_sol[i] != 0 {
                    self.accumulator.insert(i);
                }
            }
            disc.push(Entry {
                element: dio_sol,
                remainder,
                index,
            });
            index += 1;
        }
        if !self.need_to_cover.is_subset(&self.accumulator) {
            return false;
        }
        disc.reverse(); // push_front semantics: iteration order = reverse discovery
        self.basis = disc;
        self.totals = vec![0; n];
        self.uncovered = self.need_to_cover.clone();
        true
    }

    // ---- selection (no identity) ---------------------------------------------------------

    fn includable(&self, entry: usize) -> bool {
        let e = &self.basis[entry];
        (0..self.subterms.len()).all(|i| {
            self.upper_bounds[i] == UNBOUNDED
                || self.totals[i] + e.element[i] <= self.upper_bounds[i]
        })
    }

    /// Maude's `nextSelection`: greedy include-first DFS over the basis (reverse-discovery order),
    /// with coverage (`remainder`/`uncovered`) and upper-bound pruning.
    fn next_selection(&mut self, find_first: bool) -> bool {
        let n_sub = self.subterms.len();
        let mut forward = find_first;
        if find_first {
            self.current = 0;
        }
        loop {
            if forward {
                let mut backtrack = false;
                while self.current < self.basis.len() {
                    if self.includable(self.current) {
                        for i in 0..n_sub {
                            let v = self.basis[self.current].element[i];
                            if v != 0 {
                                self.totals[i] += v;
                                self.uncovered.remove(&i);
                            }
                        }
                        self.selection.push(self.current);
                    } else if !self
                        .uncovered
                        .is_subset(&self.basis[self.current].remainder)
                    {
                        backtrack = true;
                        break;
                    }
                    self.current += 1;
                }
                if !backtrack {
                    debug_assert!(self.uncovered.is_empty(), "reached end but not covered");
                    return true;
                }
                forward = false;
            } else {
                // Backtrack: peel included elements off the tail until one whose remainder can still
                // cover the regrown uncovered set; exclude it and resume forward.
                let mut resumed = false;
                for i in (0..self.selection.len()).rev() {
                    self.current = self.selection[i];
                    for j in 0..n_sub {
                        self.totals[j] -= self.basis[self.current].element[j];
                        if self.totals[j] == 0 {
                            self.uncovered.insert(j);
                        }
                    }
                    if self
                        .uncovered
                        .is_subset(&self.basis[self.current].remainder)
                    {
                        self.current += 1;
                        self.selection.truncate(i);
                        resumed = true;
                        break;
                    }
                }
                if resumed {
                    forward = true;
                    continue;
                }
                return false;
            }
        }
    }

    // ---- selection (identity) — BDD + AllSat --------------------------------------------

    /// Build the `maximal` selection BDD and its `AllSat` enumerator (identity path).
    fn compute_maximal_selections(&self, e: &Engine) -> AllSat {
        let nr = self.basis.len();
        let vars = BddVariableSet::new_anonymous(nr.max(1) as u16);
        let handles = vars.variables();
        let ithvar = |k: usize| vars.mk_literal(handles[k], true);
        let legal = self.compute_legal_selections(&vars, &ithvar);
        // When the left-identity collapse can change a sort, non-maximal selections may have
        // sortings the maximal one lacks — keep them all. Otherwise assume each fresh variable can
        // disappear by taking identity, so only maximal selections matter.
        let maximal = if unequal_left_identity_collapse(e, self.top).is_some() {
            legal
        } else {
            let mut m = legal.clone();
            for i in 0..nr {
                // notBigger = ithvar(i) OR NOT(legal restricted to ithvar(i)=true)
                let restricted = legal.var_restrict(handles[i], true);
                m = m.and(&ithvar(i).or(&restricted.not()));
            }
            m
        };
        // BuDDy's `AllSat(maximal, 0, -1)` treats an empty basis as one empty assignment. The BDD
        // crate needs a dummy variable to represent the constant formula; exclude it from the
        // assignment range (`first > last`) or its two values replay the same empty selection.
        let (first, last) = if nr == 0 {
            (1, 0)
        } else {
            (0, (nr - 1) as u16)
        };
        AllSat::new(maximal, first, last)
    }

    /// Maude's `computeLegalSelections`: upper-bound (bounded-sum) and need-to-cover constraints
    /// over the basis-element BDD variables.
    fn compute_legal_selections(
        &self,
        vars: &BddVariableSet,
        ithvar: &impl Fn(usize) -> Bdd,
    ) -> Bdd {
        let mut conjunction = vars.mk_true();
        for i in 0..self.subterms.len() {
            let ub = self.upper_bounds[i];
            if ub != UNBOUNDED {
                let ub = ub as usize;
                let mut bounds: Vec<Bdd> = vec![vars.mk_true(); ub + 1];
                for entry in &self.basis {
                    let value = entry.element[i] as usize;
                    if value != 0 {
                        for j in (0..=ub).rev() {
                            let then = if j >= value {
                                bounds[j - value].clone()
                            } else {
                                vars.mk_false()
                            };
                            bounds[j] = Bdd::if_then_else(&ithvar(entry.index), &then, &bounds[j]);
                        }
                    }
                }
                conjunction = conjunction.and(&bounds[ub]);
            }
            if self.need_to_cover.contains(&i) {
                let mut disjunction = vars.mk_false();
                for entry in &self.basis {
                    if entry.element[i] != 0 {
                        disjunction = disjunction.or(&ithvar(entry.index));
                    }
                }
                conjunction = conjunction.and(&disjunction);
            }
        }
        conjunction
    }

    /// Maude's `nextSelectionWithIdentity`: the next maximal assignment from `AllSat`, filtered onto
    /// the basis by element index.
    fn next_selection_with_identity(&mut self) -> bool {
        let all = self
            .maximal_selections
            .as_mut()
            .expect("identity selection enumerator");
        if !all.next_assignment() {
            return false;
        }
        let asg: Vec<i8> = all.assignment().to_vec();
        self.selection.clear();
        for k in 0..self.basis.len() {
            if asg[self.basis[k].index as usize] == 1 {
                self.selection.push(k);
            }
        }
        true
    }

    // ---- buildSolution -------------------------------------------------------------------

    /// If a variable subterm is assigned exactly this one basis element (multiplicity 1) and nothing
    /// else, reuse that original variable instead of a fresh one (`reuseVariable`).
    fn reuse_variable(&self, e: &Engine, selection_index: usize) -> Option<usize> {
        let b = self.selection[selection_index];
        for i in 0..self.subterms.len() {
            if self.basis[b].element[i] == 1 && var_index(e, self.subterms[i]).is_some() {
                let unique = (0..self.selection.len())
                    .all(|j| j == selection_index || self.basis[self.selection[j]].element[i] == 0);
                if unique {
                    return Some(i);
                }
            }
        }
        None
    }

    fn build_solution(
        &mut self,
        env: &mut UnifyEnv,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        // Fresh variables live at the operator's range component (kind level).
        let kind = env.e.sorts().kind_of(range_sort(env.e, self.top));
        let selection_size = self.selection.len();
        // A fresh variable per selected basis element (reuse where possible), in selection order.
        // This is ACU_UnificationSubproblem2::buildSolution's direct walk over `selection`; any
        // identity-path ordering difference belongs in basis/AllSat enumeration, not in a
        // post-selection permutation of fresh-variable slots.
        let mut fresh_variables: Vec<Option<DagId>> = vec![None; selection_size];
        let mut reused: BTreeSet<usize> = BTreeSet::new();
        for i in 0..selection_size {
            match self.reuse_variable(env.e, i) {
                Some(sub) => {
                    fresh_variables[i] = Some(self.subterms[sub]);
                    reused.insert(sub);
                }
                None => fresh_variables[i] = Some(ctx.make_fresh_variable(env, kind)),
            }
        }
        // Materialize each subterm's assignment.
        for i in 0..self.subterms.len() {
            if reused.contains(&i) {
                continue;
            }
            let mut in_theory = true;
            let mut n_elements = 0;
            let mut last_element = 0;
            for j in 0..selection_size {
                if self.basis[self.selection[j]].element[i] > 0 {
                    n_elements += 1;
                    last_element = j;
                }
            }
            let d = if n_elements == 0 {
                identity_dag(env.e, self.top)
            } else if n_elements == 1 && self.basis[self.selection[last_element]].element[i] == 1 {
                in_theory = false;
                fresh_variables[last_element].unwrap()
            } else {
                let mut pairs: Vec<(DagId, u32)> = Vec::new();
                for j in 0..selection_size {
                    let m = self.basis[self.selection[j]].element[i];
                    if m > 0 {
                        pairs.push((fresh_variables[j].unwrap(), m as u32));
                    }
                }
                env.e.make_acu(self.top, pairs) // canonicalizes (sortAndUniquize)
            };
            let subterm = self.subterms[i];
            if var_index(env.e, subterm).is_some() {
                let rep = last_variable_in_chain(env.e, ctx, subterm);
                if ctx.value(var_index(env.e, rep).unwrap() as usize).is_none() && in_theory {
                    ctx.unification_bind(env.e, rep, d);
                    continue;
                }
            }
            if !compute_solved_form(env, subterm, d, ctx, pending) {
                return false;
            }
        }
        true
    }
}

/// The range sort of an operator (its first declaration's range).
fn range_sort(e: &Engine, sym: SymbolId) -> crate::sort::SortId {
    e.symbol(sym).decls()[0].range
}

/// Maude's `BinarySymbol::hasUnequalLeftIdentityCollapse` (`leftIdentitySortCheck`): return
/// the first `(computed result, collapsed argument)` sort pair for which `f(e, x) = x`
/// changes sort. Besides gating ACU's maximal-selection optimization, the REPL uses the
/// pair for Maude's byte-visible `set verbose on` diagnostic.
pub fn unequal_left_identity_collapse(
    e: &Engine,
    top: SymbolId,
) -> Option<(crate::sort::SortId, crate::sort::SortId)> {
    let identity = e.symbol(top).identity()?;
    let sig = e.signature();
    let id_sort = sig.identity_sort(identity);
    let kind = sig.sorts().kind_of(range_sort(e, top));
    sig.sorts()
        .kind(kind)
        .members
        .clone()
        .into_iter()
        .find_map(|sort| {
            let result = sig.compute_sort(top, &[id_sort, sort]);
            (result != sort).then_some((result, sort))
        })
}

/// The operator's two-sided identity DAG (`getIdentityDag`).
fn identity_dag(e: &mut Engine, top: SymbolId) -> DagId {
    let identity = e
        .symbol(top)
        .identity()
        .expect("build_solution identity slot needs an identity");
    e.make_identity(identity)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_identity_basis_has_one_selection() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let unit = e.add_op("unit", vec![], nat);
        let product = e.add_op_ac("*", vec![nat, nat], nat, Some(unit));
        let mut solver = AcuSubproblem::new(&e, product);

        assert!(solver.basis.is_empty());
        solver.maximal_selections = Some(solver.compute_maximal_selections(&e));
        assert!(
            solver.next_selection_with_identity(),
            "the empty selection is a solution"
        );
        assert!(solver.selection.is_empty());
        assert!(
            !solver.next_selection_with_identity(),
            "the dummy BDD variable is not enumerated"
        );
    }

    #[test]
    fn acu_pairs_keep_pre_index_name_order() {
        let mut e = Engine::new();
        let set = e.add_sort("Set");
        e.close_sorts();
        let f = e.add_op_ac("f", vec![set, set], set, None);
        // Runtime AC canonicalization sees slot 0 before slot 1.  The unifier must instead recover
        // VariableTerm normalization, where the shared VariableSymbol compares the name codes.
        let x = e.make_var(set, 20, 0);
        let y = e.make_var(set, 10, 1);
        let term = e.make_ac(f, vec![x, y]);

        let pairs = acu_pairs(&e, term);
        assert_eq!(
            pairs
                .iter()
                .map(|&(id, _)| var_index(&e, id))
                .collect::<Vec<_>>(),
            [Some(1), Some(0)]
        );
    }

    #[test]
    fn stable_classifier_accepts_noncollapsing_theory_symbols() {
        let mut e = Engine::new();
        let sort = e.add_sort("S");
        e.close_sorts();
        let identity = e.add_op("id", vec![], sort);
        let free = e.add_op("g", vec![sort], sort);
        let pure_a = e.add_op_au("a", vec![sort, sort], sort, None);
        let pure_ac = e.add_op_ac("ac", vec![sort, sort], sort, None);
        let au_with_identity = e.add_op_au("au", vec![sort, sort], sort, Some(identity));
        let variable = e.make_var(sort, 0, 0);

        assert!(is_stable(&e, free));
        assert!(is_stable(&e, pure_a));
        assert!(is_stable(&e, pure_ac));
        assert!(!is_stable(&e, au_with_identity));
        assert!(!is_stable(&e, e.node(variable).symbol()));
    }
}
