//! Order-sorted unification core — the solved-form machinery under the `unify` command and the
//! `metaUnify` descent family (subsystems-goal.md phase S1).
//!
//! Ports the reference's layered protocol faithfully, **including enumeration order**:
//!
//! * [`UnifyContext`] — `src/Core/unificationContext.{hh,cc}`: the substitution (slot-indexed,
//!   originals first, mid-solve fresh variables appended), fresh-variable creation at the kind
//!   level, and the per-slot `VariableDagNode` tracking used for unsolving and cycle resolution.
//! * [`PendingStack`] — `src/Core/pendingUnificationStack.{hh,cc}`: pushed multi-solution theory
//!   problems, solved a whole theory at a time (termination requirement), theory choice by
//!   `unificationPriority`, checkpoint/restore backtracking, compound-cycle detection, and the
//!   incompleteness flag.
//! * [`compute_solved_form`] — `DagNode::computeSolvedForm` dispatch plus the per-theory
//!   `computeSolvedForm2` arms that resolve deterministically (variables, free, S/iter, and the
//!   ground backstop); multi-solution theories (C/CUI in [`cui`], AC/ACU and A/AU when their
//!   solvers land) push onto the pending stack instead.
//!
//! Everything takes `&mut Engine` — solving builds nodes and creates per-sort variable symbols in
//! Maude's demand order (observable through `dag_compare`). Fresh-variable *names* come from the
//! central [`FreshVariableGenerator`]; their interned codes come from the session's [`NameCodes`]
//! source, so name-code order matches the reference's token-encounter order.

// The solved-form core and per-theory solvers are complete but not yet wired to a caller: the
// UnificationProblem driver (S1d) and the `unify` command / `metaUnify` (S1e/S1f) consume them.
// Scoped dead-code allowance until then; removed when the driver lands (subsystems-goal §5 S1).
#![allow(dead_code)]

pub(crate) mod cui;
pub mod problem;

use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::fresh::{FreshVariableGenerator, VariableFamily};
use crate::num::Nat;
use crate::sort::{KindId, SortId};
use crate::symbol::{SymbolId, Theory};
use std::collections::BTreeSet;

/// Session name-code source: interns a fresh-variable name (`#1`, `%2`, …) and returns its code —
/// the same code space user variables' base names were interned into (the frontend's `Interner`),
/// so variable ordering (`dag_compare` on name codes) mirrors Maude's token-code order.
pub trait NameCodes {
    fn code(&mut self, name: &str) -> u32;
}

/// The engine + name-code pair threaded through every solver step (fresh variables need both).
pub struct UnifyEnv<'a> {
    pub e: &'a mut Engine,
    pub names: &'a mut dyn NameCodes,
}

/// A saved substitution snapshot (`Substitution::clone` in the reference) — restoring may shrink
/// the slot count, discarding fresh variables created since the snapshot.
pub(crate) type SavedSubst = Vec<Option<DagId>>;

// ======================================================================================
// UnifyContext — unificationContext.{hh,cc}
// ======================================================================================

/// The unification substitution: slots `0..n_original` are the problem's original variables,
/// higher slots are fresh variables created mid-solve (always at the **kind** level). `None` =
/// unbound. Mirrors `UnificationContext`.
pub(crate) struct UnifyContext {
    values: Vec<Option<DagId>>,
    n_original: usize,
    /// Kind error sort of each fresh variable (slot `n_original + i`).
    fresh_sorts: Vec<SortId>,
    /// The `Var` dag node recorded for each slot bound through [`unification_bind`]
    /// (`UnificationContext::variableDagNodes`) — needed to unsolve solved forms and to resolve
    /// compound cycles.
    variable_nodes: Vec<Option<DagId>>,
    family: VariableFamily,
    generator: FreshVariableGenerator,
}

impl UnifyContext {
    pub(crate) fn new(n_original: usize, family: VariableFamily) -> Self {
        UnifyContext {
            values: vec![None; n_original],
            n_original,
            fresh_sorts: Vec::new(),
            variable_nodes: Vec::new(),
            family,
            generator: FreshVariableGenerator::new(),
        }
    }

    /// A context whose fresh-variable numbering starts above `base` (`metaUnify`'s counter).
    pub(crate) fn with_base(n_original: usize, family: VariableFamily, base: Nat) -> Self {
        UnifyContext {
            generator: FreshVariableGenerator::with_base(base),
            ..Self::new(n_original, family)
        }
    }

    pub(crate) fn n_slots(&self) -> usize {
        self.values.len()
    }
    pub(crate) fn n_original(&self) -> usize {
        self.n_original
    }
    pub(crate) fn family(&self) -> VariableFamily {
        self.family
    }
    pub(crate) fn value(&self, slot: usize) -> Option<DagId> {
        self.values[slot]
    }
    /// Raw slot write (`Substitution::bind`) — `None` unbinds.
    pub(crate) fn bind(&mut self, slot: usize, value: Option<DagId>) {
        self.values[slot] = value;
    }

    /// The kind error sort a fresh slot was created at (`getFreshVariableSort`).
    pub(crate) fn fresh_variable_sort(&self, slot: usize) -> SortId {
        self.fresh_sorts[slot - self.n_original]
    }

    /// The tracked `Var` node for `slot`, if it was ever bound (`getVariableDagNode`).
    pub(crate) fn variable_node(&self, slot: usize) -> Option<DagId> {
        self.variable_nodes.get(slot).copied().flatten()
    }

    /// Create a fresh variable at `kind`'s error sort (`UnificationContext::makeFreshVariable`):
    /// appends an unbound slot, names it `<prefix><n>` from the central generator, and returns its
    /// `Var` node.
    pub(crate) fn make_fresh_variable(&mut self, env: &mut UnifyEnv, kind: KindId) -> DagId {
        let sort = env.e.sorts().error_sort(kind);
        let index = self.values.len();
        self.values.push(None);
        let fresh_nr = index - self.n_original;
        self.fresh_sorts.push(sort);
        let code = env.names.code(self.generator.fresh_name(fresh_nr, self.family));
        env.e.make_var(sort, code, index as u32)
    }

    /// Bind `variable` (a `Var` node, its own slot) to `value` and record the variable's dag for
    /// that slot (`unificationBind`).
    pub(crate) fn unification_bind(&mut self, e: &Engine, variable: DagId, value: DagId) {
        debug_assert!(variable != value, "variable bound to itself");
        let index = var_index(e, variable).expect("unification_bind on a non-variable") as usize;
        self.values[index] = Some(value);
        if index >= self.variable_nodes.len() {
            self.variable_nodes.resize(index + 1, None);
        }
        self.variable_nodes[index] = Some(variable);
    }

    /// Snapshot the substitution for backtracking (`savedSubstitution.clone(solution)`).
    pub(crate) fn clone_subst(&self) -> SavedSubst {
        self.values.clone()
    }

    /// Restore from a snapshot (`restoreFromClone`): the slot count may shrink; fresh-variable
    /// sorts and tracked variable dags accumulated since the snapshot are discarded.
    pub(crate) fn restore_from_clone(&mut self, saved: &SavedSubst) {
        self.values = saved.clone();
        let n = self.values.len();
        self.fresh_sorts.truncate(n - self.n_original);
        if self.variable_nodes.len() > n {
            self.variable_nodes.truncate(n);
        }
    }

    /// The raw binding slice (`Substitution` values), for `instantiate` and the driver's
    /// sorted-solution clone.
    pub(crate) fn values(&self) -> &[Option<DagId>] {
        &self.values
    }

    /// Every live dag the context holds (bindings + tracked variables) — the GC-root surface the
    /// owning problem must report.
    pub(crate) fn gc_roots(&self) -> impl Iterator<Item = DagId> + '_ {
        self.values
            .iter()
            .copied()
            .flatten()
            .chain(self.variable_nodes.iter().copied().flatten())
    }
}

// ======================================================================================
// Dag helpers over `Var` leaves
// ======================================================================================

/// The substitution slot of a `Var` node, or `None` for any other node.
pub(crate) fn var_index(e: &Engine, id: DagId) -> Option<u32> {
    match &e.node(id).term {
        NodeTerm::Var { index, .. } => Some(*index),
        _ => None,
    }
}

/// Variable identity (`VariableDagNode::equal`): per-sort symbol + name code.
fn var_key(e: &Engine, id: DagId) -> (SymbolId, u32) {
    match &e.node(id).term {
        NodeTerm::Var { symbol, name, .. } => (*symbol, *name),
        _ => unreachable!("var_key on a non-variable"),
    }
}

/// Follow a variable→variable binding chain to its representative
/// (`VariableDagNode::lastVariableInChain`).
pub(crate) fn last_variable_in_chain(e: &Engine, ctx: &UnifyContext, v: DagId) -> DagId {
    let mut v = v;
    loop {
        let index = var_index(e, v).expect("chain start must be a variable") as usize;
        match ctx.value(index) {
            Some(d) if var_index(e, d).is_some() => {
                debug_assert!(d != v, "variable bound to itself in chain");
                v = d;
            }
            _ => return v,
        }
    }
}

/// Whether `id` contains no `Var` leaf (`DagNode::isGround` for unification dags — tnk computes
/// it structurally instead of caching a flag; the walk is over problem-sized terms).
pub(crate) fn is_ground(e: &Engine, id: DagId) -> bool {
    let mut stack = vec![id];
    while let Some(n) = stack.pop() {
        let node = e.node(n);
        if matches!(node.term, NodeTerm::Var { .. }) {
            return false;
        }
        stack.extend(node.children());
    }
    true
}

/// Collect the slot indices of every variable occurring in `id` (`DagNode::insertVariables`).
/// `BTreeSet` mirrors the reference's ascending `NatSet` iteration order — the cycle DFS depends
/// on it.
pub(crate) fn insert_variables(e: &Engine, id: DagId, occurs: &mut BTreeSet<usize>) {
    let mut stack = vec![id];
    while let Some(n) = stack.pop() {
        let node = e.node(n);
        if let NodeTerm::Var { index, .. } = node.term {
            occurs.insert(index as usize);
        } else {
            stack.extend(node.children());
        }
    }
}

/// Instantiate `id` under the context (`DagNode::instantiate` with invariants maintained):
/// `None` = unchanged. Rebuilding goes through the canonical `make_*` builders, so collapse,
/// flattening, ordering, and base sorts are maintained exactly as at construction.
pub(crate) fn instantiate(e: &mut Engine, values: &[Option<DagId>], id: DagId) -> Option<DagId> {
    enum Rep {
        Free(SymbolId, Vec<DagId>),
        Acu(SymbolId, Vec<(DagId, u32)>),
        Au(SymbolId, Vec<DagId>),
        Cui(SymbolId, DagId, DagId),
        S(SymbolId, Nat, DagId),
    }
    let rep = match &e.node(id).term {
        NodeTerm::Var { index, .. } => return values.get(*index as usize).copied().flatten(),
        NodeTerm::Na { .. } => return None,
        NodeTerm::Free { symbol, args } => Rep::Free(*symbol, args.clone()),
        NodeTerm::Acu { symbol, args } => Rep::Acu(*symbol, args.clone()),
        NodeTerm::Au { symbol, args } => Rep::Au(*symbol, args.clone()),
        NodeTerm::Cui { symbol, args } => Rep::Cui(*symbol, args[0], args[1]),
        NodeTerm::S { symbol, count, arg } => Rep::S(*symbol, count.clone(), *arg),
    };
    match rep {
        Rep::Free(symbol, mut args) => {
            let mut changed = false;
            for a in &mut args {
                if let Some(n) = instantiate(e, values, *a) {
                    *a = n;
                    changed = true;
                }
            }
            changed.then(|| {
                let (sig, rt) = e.parts_mut();
                rt.make_free(sig, symbol, args)
            })
        }
        Rep::Acu(symbol, mut pairs) => {
            let mut changed = false;
            for (a, _) in &mut pairs {
                if let Some(n) = instantiate(e, values, *a) {
                    *a = n;
                    changed = true;
                }
            }
            changed.then(|| {
                let (sig, rt) = e.parts_mut();
                rt.make_acu(sig, symbol, pairs)
            })
        }
        Rep::Au(symbol, mut args) => {
            let mut changed = false;
            for a in &mut args {
                if let Some(n) = instantiate(e, values, *a) {
                    *a = n;
                    changed = true;
                }
            }
            changed.then(|| {
                let (sig, rt) = e.parts_mut();
                rt.make_au(sig, symbol, args)
            })
        }
        Rep::Cui(symbol, x, y) => {
            let nx = instantiate(e, values, x);
            let ny = instantiate(e, values, y);
            if nx.is_none() && ny.is_none() {
                return None;
            }
            let (sig, rt) = e.parts_mut();
            Some(rt.make_cui(sig, symbol, nx.unwrap_or(x), ny.unwrap_or(y)))
        }
        Rep::S(symbol, count, arg) => instantiate(e, values, arg).map(|n| {
            let (sig, rt) = e.parts_mut();
            rt.make_s(sig, symbol, count, n)
        }),
    }
}

// ======================================================================================
// Screening — DagNode::computeBaseSortForGroundSubterms
// ======================================================================================

/// Result of screening a unificand for unimplemented theories.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Screen {
    Ground,
    NonGround,
    /// A non-ground term sits under a top symbol whose unification theory is unimplemented.
    Unimplemented,
}

/// The symbol-level unification theory (Maude dispatches on the DagNode class; tnk's node rep for
/// a one-sided-identity operator is `Free` — the frontend withholds one-sided ids from kernel
/// collapse — so unification classifies by **symbol**, matching Maude's `CUI_Symbol` coverage).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnifyTheory {
    Free,
    /// C / CU / CUl / CUr / U / Ul / Ur (non-associative comm and/or identity and/or idem —
    /// idem is screened out as unimplemented, like the reference).
    Cui,
    Acu,
    Au,
    S,
}

pub(crate) fn unify_theory(e: &Engine, symbol: SymbolId) -> UnifyTheory {
    let sym = e.symbol(symbol);
    match sym.theory() {
        Theory::S => UnifyTheory::S,
        Theory::Acu => UnifyTheory::Acu,
        Theory::Au => UnifyTheory::Au,
        Theory::Cui => UnifyTheory::Cui,
        Theory::Free => {
            if sym.one_sided_identity() {
                UnifyTheory::Cui // one-sided-id op: Free node rep, CUI unification theory
            } else {
                UnifyTheory::Free
            }
        }
    }
}

/// Whether `symbol`'s unification theory is unimplemented (the `computeBaseSortForGroundSubterms`
/// backstop set): CUI with `idem`; associative with a one-sided identity. AC/ACU and A/AU are
/// TEMPORARILY in this set until their solvers land (S1c) — an honest refusal (warn, no unifiers)
/// rather than a misfiring partial answer.
fn unimplemented_theory(e: &Engine, symbol: SymbolId) -> bool {
    let sym = e.symbol(symbol);
    match sym.theory() {
        Theory::Cui => sym.axioms.idem,
        Theory::Au => sym.one_sided_identity() || true, // TEMPORARY: A/AU solver lands in S1c
        Theory::Acu => true,                            // TEMPORARY: AC/ACU solver lands in S1c
        _ => false,
    }
}

/// Screen a unificand (`computeBaseSortForGroundSubterms(true)`): find non-ground terms under
/// unimplemented-theory tops. `warned` collects each offending node in the reference's warning
/// order (a node warns after its children's screening, once per node).
pub fn screen_for_unification(e: &Engine, id: DagId, warned: &mut Vec<DagId>) -> Screen {
    match &e.node(id).term {
        NodeTerm::Var { .. } => Screen::NonGround,
        NodeTerm::Na { .. } => Screen::Ground,
        term => {
            let symbol = e.node(id).symbol();
            let children: Vec<DagId> = e.node(id).children().collect();
            // ACU children carry multiplicities; screening each distinct element once matches the
            // reference (it walks the pair array). The repeat-expanded walk is equivalent here
            // because screening is idempotent per subterm.
            let _ = term;
            let mut result = Screen::Ground;
            let mut warn_here = false;
            for c in children {
                let r = screen_for_unification(e, c, warned);
                if r > result {
                    result = r;
                }
                if r != Screen::Ground {
                    warn_here = true;
                }
            }
            if unimplemented_theory(e, symbol) {
                if warn_here {
                    warned.push(id);
                    return Screen::Unimplemented;
                }
                return result; // ground under an unimplemented top is fine
            }
            result
        }
    }
}

// ======================================================================================
// PendingStack — pendingUnificationStack.{hh,cc}
// ======================================================================================

/// `Symbol::unificationPriority` — governs which theory's problems are solved first, hence the
/// enumeration order of unifiers. Disjunctions (controlling symbol `None`) always win; then the
/// lowest number: CUI `comm + 2*(leftId + rightId)` (1–5), AC 10, ACU 20, everything else 100.
fn unification_priority(e: &Engine, symbol: SymbolId) -> i32 {
    let sym = e.symbol(symbol);
    match sym.theory() {
        Theory::Acu => 10 + 10 * i32::from(sym.identity().is_some()),
        Theory::Cui | Theory::Free => {
            if sym.axioms.idem {
                100 // unimplemented
            } else {
                i32::from(sym.axioms.comm)
                    + 2 * (i32::from(sym.left_identity().is_some())
                        + i32::from(sym.right_identity().is_some()))
            }
        }
        _ => 100,
    }
}

/// `Symbol::canResolveTheoryClash` — whether this theory can make its top disappear by collapse:
/// AC/ACU and A/AU with an identity; the CUI family with a left or right identity.
pub(crate) fn can_resolve_theory_clash(e: &Engine, symbol: SymbolId) -> bool {
    let sym = e.symbol(symbol);
    match sym.theory() {
        Theory::Acu | Theory::Au => sym.identity().is_some(),
        Theory::Cui | Theory::Free => {
            sym.left_identity().is_some() || sym.right_identity().is_some()
        }
        Theory::S => false,
    }
}

struct TheoryEntry {
    /// `None` is the reserved disjunction pseudo-theory (table slot 0, solved first).
    controlling: Option<SymbolId>,
    first_problem: Option<usize>,
}

struct PendingProblem {
    theory: usize,
    next_in_theory: Option<usize>,
    lhs: DagId,
    rhs: DagId,
    /// Force the lhs to collapse (theory-clash resolution).
    marked: bool,
}

/// Active-subproblem theory tag: a real theory-table index or the compound-cycle pseudo-theory.
enum ActiveTheory {
    Table(usize),
    CompoundCycle,
}

struct ActiveSubproblem {
    theory: ActiveTheory,
    saved_first: Option<usize>,
    /// `Option` so `solve` can temporarily move the subproblem out while it mutates the stack.
    sp: Option<UnifySubproblem>,
}

/// A checkpoint marker (`PendingUnificationStack::Marker`).
pub(crate) type Marker = usize;

pub(crate) struct PendingStack {
    theory_table: Vec<TheoryEntry>,
    stack: Vec<PendingProblem>,
    subproblems: Vec<ActiveSubproblem>,
    incomplete: BTreeSet<SymbolId>,
    variable_status: Vec<VarStatus>,
    variable_order: Vec<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum VarStatus {
    Unexplored,
    Explored,
    /// Currently exploring: holds the variable index being descended into.
    Exploring(usize),
}

impl PendingStack {
    pub(crate) fn new() -> Self {
        PendingStack {
            theory_table: vec![TheoryEntry { controlling: None, first_problem: None }],
            stack: Vec::new(),
            subproblems: Vec::new(),
            incomplete: BTreeSet::new(),
            variable_status: Vec::new(),
            variable_order: Vec::new(),
        }
    }

    /// Push a multi-solution problem under `controlling` (`None` = disjunction). LIFO within a
    /// theory via the intrusive `next_in_theory` list, exactly like the reference.
    pub(crate) fn push(
        &mut self,
        controlling: Option<SymbolId>,
        lhs: DagId,
        rhs: DagId,
        marked: bool,
    ) {
        let e = self.stack.len();
        for (i, t) in self.theory_table.iter_mut().enumerate() {
            if t.controlling == controlling {
                self.stack.push(PendingProblem {
                    theory: i,
                    next_in_theory: t.first_problem,
                    lhs,
                    rhs,
                    marked,
                });
                t.first_problem = Some(e);
                return;
            }
        }
        let i = self.theory_table.len();
        self.theory_table.push(TheoryEntry { controlling, first_problem: Some(e) });
        self.stack.push(PendingProblem { theory: i, next_in_theory: None, lhs, rhs, marked });
    }

    /// `resolveTheoryClash`: neither side's theory owns `lhs =? rhs`. If only one side can
    /// collapse away its top, it controls (marked); if both can, push a disjunction; if neither,
    /// fail.
    pub(crate) fn resolve_theory_clash(&mut self, e: &Engine, lhs: DagId, rhs: DagId) -> bool {
        let (mut lhs, mut rhs) = (lhs, rhs);
        let mut controlling = Some(e.node(lhs).symbol());
        if can_resolve_theory_clash(e, controlling.unwrap()) {
            if can_resolve_theory_clash(e, e.node(rhs).symbol()) {
                controlling = None; // both might collapse — try both via a disjunction
            }
        } else {
            let rsym = e.node(rhs).symbol();
            if !can_resolve_theory_clash(e, rsym) {
                return false; // unresolvable
            }
            controlling = Some(rsym);
            std::mem::swap(&mut lhs, &mut rhs);
        }
        self.push(controlling, lhs, rhs, true);
        true
    }

    pub(crate) fn checkpoint(&self) -> Marker {
        self.stack.len()
    }

    /// Blow away every problem pushed at or after `mark`, relinking theory lists.
    pub(crate) fn restore(&mut self, mark: Marker) {
        for i in (mark..self.stack.len()).rev() {
            let p = &self.stack[i];
            debug_assert_eq!(
                self.theory_table[p.theory].first_problem,
                Some(i),
                "retracting a problem that is not first in its theory"
            );
            self.theory_table[p.theory].first_problem = p.next_in_theory;
        }
        self.stack.truncate(mark);
    }

    /// Flag `symbol`'s theory as possibly incomplete (the A/AU depth bound). The warning *text*
    /// stays with the driver (phase E); the flag itself is part of the result protocol.
    pub(crate) fn flag_as_incomplete(&mut self, symbol: SymbolId) {
        self.incomplete.insert(symbol);
    }

    pub(crate) fn is_incomplete(&self) -> bool {
        !self.incomplete.is_empty()
    }

    /// The master loop (`PendingUnificationStack::solve`): drive the top subproblem; on success
    /// activate the next theory (all of its pending problems at once); on failure kill the top
    /// and backtrack into the one below.
    pub(crate) fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
    ) -> bool {
        let mut find_first = find_first;
        if if find_first { self.make_new_subproblem(env, ctx) } else { !self.subproblems.is_empty() }
        {
            loop {
                // Temporarily move the top subproblem out so it can mutate `self` while solving.
                let top = self.subproblems.len() - 1;
                let mut sp = self.subproblems[top].sp.take().expect("subproblem in use");
                find_first = sp.solve(env, find_first, ctx, self);
                self.subproblems[top].sp = Some(sp);
                if find_first {
                    if !self.make_new_subproblem(env, ctx) {
                        break; // all done
                    }
                } else {
                    self.kill_top_subproblem();
                    if self.subproblems.is_empty() {
                        break; // out of alternatives
                    }
                }
            }
        }
        find_first
    }

    /// `chooseTheoryToSolve`: disjunctions first, else the lowest `unificationPriority` with
    /// unsolved problems.
    fn choose_theory_to_solve(&self, e: &Engine) -> Option<usize> {
        let mut best: Option<(i32, usize)> = None;
        for (i, t) in self.theory_table.iter().enumerate() {
            if t.first_problem.is_some() {
                let Some(s) = t.controlling else {
                    return Some(i); // prioritize disjunctions
                };
                let p = unification_priority(e, s);
                if best.is_none_or(|(bp, _)| p < bp) {
                    best = Some((p, i));
                }
            }
        }
        best.map(|(_, i)| i)
    }

    /// `makeNewSubproblem`: activate the chosen theory's whole pending set as one subproblem; when
    /// no theory has problems, run the compound-cycle check and — if acyclic — instantiate all
    /// bindings in a safe order (the solved form is complete). Returns whether a new subproblem
    /// was pushed.
    fn make_new_subproblem(&mut self, env: &mut UnifyEnv, ctx: &mut UnifyContext) -> bool {
        if let Some(i) = self.choose_theory_to_solve(env.e) {
            let controlling = self.theory_table[i].controlling;
            let mut sp = match controlling {
                None => UnifySubproblem::Disjunction(DisjunctionSubproblem::default()),
                Some(s) => make_unification_subproblem(env.e, s),
            };
            let mut j = self.theory_table[i].first_problem;
            while let Some(k) = j {
                let (lhs, rhs, marked) = {
                    let p = &self.stack[k];
                    (p.lhs, p.rhs, p.marked)
                };
                sp.add_unification(env, ctx, self, lhs, rhs, marked);
                j = self.stack[k].next_in_theory;
            }
            let saved_first = self.theory_table[i].first_problem;
            self.subproblems.push(ActiveSubproblem {
                theory: ActiveTheory::Table(i),
                saved_first,
                sp: Some(sp),
            });
            self.theory_table[i].first_problem = None;
            return true;
        }
        // All unification problems solved — check for compound cycles.
        match self.find_cycle(env.e, ctx) {
            None => {
                // Complete: instantiate bound variables in dependency order (live — a later slot's
                // instantiation must see its already-instantiated dependencies, which precede it in
                // `variable_order`). The `values()` borrow ends when `instantiate` returns `d`.
                for index in self.variable_order.clone() {
                    let Some(v) = ctx.value(index) else { continue };
                    let d = instantiate(env.e, ctx.values(), v);
                    if let Some(d) = d {
                        ctx.bind(index, Some(d));
                    }
                }
                false
            }
            Some(cycle_start) => {
                // Build a compound-cycle subproblem from the cycle's non-variable components.
                let mut cycle = Vec::new();
                let mut i = cycle_start;
                loop {
                    let value = ctx.value(i).expect("cycle variable is bound");
                    if var_index(env.e, value).is_none() {
                        cycle.push(i);
                    }
                    let VarStatus::Exploring(next) = self.variable_status[i] else {
                        unreachable!("cycle variable not in exploring state");
                    };
                    i = next;
                    if i == cycle_start {
                        break;
                    }
                }
                self.subproblems.push(ActiveSubproblem {
                    theory: ActiveTheory::CompoundCycle,
                    saved_first: None,
                    sp: Some(UnifySubproblem::CompoundCycle(CompoundCycleSubproblem::new(cycle))),
                });
                true
            }
        }
    }

    /// `killTopSubproblem`: pop and relink its problems back as unsolved.
    fn kill_top_subproblem(&mut self) {
        let a = self.subproblems.pop().expect("kill on empty subproblem stack");
        if let ActiveTheory::Table(i) = a.theory {
            debug_assert!(
                self.theory_table[i].first_problem.is_none(),
                "newer problems not retracted"
            );
            self.theory_table[i].first_problem = a.saved_first;
        }
    }

    /// `findCycle`: DFS from each original variable over binding occurrences; returns a variable
    /// on a dependency cycle, or fills `variable_order` with a safe instantiation order.
    fn find_cycle(&mut self, e: &Engine, ctx: &UnifyContext) -> Option<usize> {
        let n = ctx.n_slots();
        self.variable_status.clear();
        self.variable_status.resize(n, VarStatus::Unexplored);
        self.variable_order.clear();
        for i in 0..ctx.n_original() {
            if let Some(c) = self.find_cycle_from(e, ctx, i) {
                return Some(c);
            }
        }
        None
    }

    fn find_cycle_from(&mut self, e: &Engine, ctx: &UnifyContext, index: usize) -> Option<usize> {
        match self.variable_status[index] {
            VarStatus::Unexplored => {
                let Some(d) = ctx.value(index) else {
                    self.variable_status[index] = VarStatus::Explored;
                    return None;
                };
                let mut occurs = BTreeSet::new();
                insert_variables(e, d, &mut occurs);
                for vi in occurs {
                    self.variable_status[index] = VarStatus::Exploring(vi);
                    if let Some(c) = self.find_cycle_from(e, ctx, vi) {
                        return Some(c);
                    }
                }
                self.variable_status[index] = VarStatus::Explored;
                self.variable_order.push(index);
                None
            }
            VarStatus::Explored => None,
            // Hit while being explored — a cycle.
            VarStatus::Exploring(_) => Some(index),
        }
    }

    /// GC-root surface: every dag held by pending problems.
    pub(crate) fn gc_roots(&self) -> impl Iterator<Item = DagId> + '_ {
        self.stack
            .iter()
            .flat_map(|p| [p.lhs, p.rhs])
            .chain(self.subproblems.iter().flat_map(|a| {
                a.sp.as_ref().map(|sp| sp.gc_roots()).unwrap_or_default()
            }))
    }
}

/// `Symbol::makeUnificationSubproblem` — one subproblem per controlling theory. AC/ACU and A/AU
/// arrive with S1c; until then their tops are screened as unimplemented, so no problem can be
/// pushed under them.
fn make_unification_subproblem(e: &Engine, symbol: SymbolId) -> UnifySubproblem {
    match unify_theory(e, symbol) {
        UnifyTheory::Cui => {
            let sym = e.symbol(symbol);
            if sym.left_identity().is_some() || sym.right_identity().is_some() {
                UnifySubproblem::CuiWithId(cui::CuiIdSubproblem::default())
            } else {
                UnifySubproblem::C(cui::CSubproblem::default())
            }
        }
        UnifyTheory::Acu | UnifyTheory::Au => {
            unreachable!("AC/ACU and A/AU tops are screened until their solvers land (S1c)")
        }
        UnifyTheory::Free | UnifyTheory::S => {
            unreachable!("free and S theories never push subproblems")
        }
    }
}

// ======================================================================================
// Subproblems: closed enum (D3 house style)
// ======================================================================================

pub(crate) enum UnifySubproblem {
    Disjunction(DisjunctionSubproblem),
    CompoundCycle(CompoundCycleSubproblem),
    C(cui::CSubproblem),
    CuiWithId(cui::CuiIdSubproblem),
}

impl UnifySubproblem {
    fn add_unification(
        &mut self,
        env: &mut UnifyEnv,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
        lhs: DagId,
        rhs: DagId,
        marked: bool,
    ) {
        match self {
            UnifySubproblem::Disjunction(d) => d.add_unification(lhs, rhs),
            UnifySubproblem::CompoundCycle(_) => {
                unreachable!("compound-cycle subproblems take no unifications")
            }
            UnifySubproblem::C(c) => c.add_unification(lhs, rhs, marked),
            UnifySubproblem::CuiWithId(c) => c.add_unification(env, ctx, pending, lhs, rhs, marked),
        }
    }

    fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        match self {
            UnifySubproblem::Disjunction(d) => d.solve(env, find_first, pending),
            UnifySubproblem::CompoundCycle(c) => c.solve(env, find_first, ctx, pending),
            UnifySubproblem::C(c) => c.solve(env, find_first, ctx, pending),
            UnifySubproblem::CuiWithId(c) => c.solve(env, find_first, ctx, pending),
        }
    }

    fn gc_roots(&self) -> Vec<DagId> {
        match self {
            UnifySubproblem::Disjunction(d) => {
                d.problems.iter().flat_map(|p| [p.lhs, p.rhs]).collect()
            }
            UnifySubproblem::CompoundCycle(c) => {
                c.pre_break_substitution.iter().copied().flatten().collect()
            }
            UnifySubproblem::C(c) => c.gc_roots(),
            UnifySubproblem::CuiWithId(c) => c.gc_roots(),
        }
    }
}

// --------------------------------------------------------------------------------------
// UnificationSubproblemDisjunction — unificationSubproblemDisjunction.cc
// --------------------------------------------------------------------------------------

/// A theory clash both sides might resolve: try lhs-controlling for every problem, then on
/// backtrack flip each (rightmost-first) to rhs-controlling. Touches only the pending stack.
#[derive(Default)]
pub(crate) struct DisjunctionSubproblem {
    problems: Vec<TheoryClash>,
}

struct TheoryClash {
    lhs: DagId,
    rhs: DagId,
    lhs_controlling: bool,
    saved_pending_state: Marker,
}

impl DisjunctionSubproblem {
    fn add_unification(&mut self, lhs: DagId, rhs: DagId) {
        self.problems.push(TheoryClash {
            lhs,
            rhs,
            lhs_controlling: false,
            saved_pending_state: 0,
        });
    }

    fn solve(&mut self, env: &mut UnifyEnv, find_first: bool, pending: &mut PendingStack) -> bool {
        let n = self.problems.len();
        let mut i;
        if find_first {
            i = 0;
        } else {
            let mut j = n - 1;
            loop {
                let p = &mut self.problems[j];
                if p.lhs_controlling {
                    pending.restore(p.saved_pending_state);
                    p.lhs_controlling = false;
                    let rsym = env.e.node(p.rhs).symbol();
                    let (rhs, lhs) = (p.rhs, p.lhs);
                    pending.push(Some(rsym), rhs, lhs, true); // swap sides
                    i = j + 1;
                    break;
                }
                if j == 0 {
                    pending.restore(self.problems[0].saved_pending_state);
                    return false; // all combinations exhausted
                }
                j -= 1;
            }
        }
        while i < n {
            let p = &mut self.problems[i];
            p.saved_pending_state = pending.checkpoint();
            p.lhs_controlling = true;
            let lsym = env.e.node(p.lhs).symbol();
            let (lhs, rhs) = (p.lhs, p.rhs);
            pending.push(Some(lsym), lhs, rhs, true);
            i += 1;
        }
        true
    }
}

// --------------------------------------------------------------------------------------
// CompoundCycleSubproblem — compoundCycleSubproblem.cc
// --------------------------------------------------------------------------------------

/// Break a cross-theory dependency cycle by collapsing one of its non-variable edges (an
/// assignment whose top can resolve to a subterm via identity). The reference's second phase —
/// unifying an edge against a *cyclic identity* — is unreachable in tnk: identities are constant
/// symbols (`Symbol::identity` docs), and a constant identity can never contain another
/// identity-bearing operator, so `BinarySymbol::hasCyclicIdentity` is identically false.
pub(crate) struct CompoundCycleSubproblem {
    cycle: Vec<usize>,
    pre_break_substitution: SavedSubst,
    pre_break_pending_state: Marker,
    current_edge_index: usize,
}

impl CompoundCycleSubproblem {
    fn new(cycle: Vec<usize>) -> Self {
        CompoundCycleSubproblem {
            cycle,
            pre_break_substitution: Vec::new(),
            pre_break_pending_state: 0,
            current_edge_index: 0,
        }
    }

    fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        if find_first {
            self.pre_break_substitution = ctx.clone_subst();
            self.pre_break_pending_state = pending.checkpoint();
            self.current_edge_index = 0;
        } else {
            ctx.restore_from_clone(&self.pre_break_substitution);
            pending.restore(self.pre_break_pending_state);
        }
        let n = self.cycle.len();
        while self.current_edge_index < n {
            let variable_index = self.cycle[self.current_edge_index];
            let variable =
                ctx.variable_node(variable_index).expect("cycle variable has a tracked dag");
            let assignment = ctx.value(variable_index).expect("cycle variable is bound");
            self.current_edge_index += 1;
            let controlling = env.e.node(assignment).symbol();
            if can_resolve_theory_clash(env.e, controlling) {
                pending.push(Some(controlling), assignment, variable, true);
                // The binding is back on the stack as a problem; drop it from the solution.
                ctx.bind(variable_index, None);
                return true;
            }
        }
        false
    }
}

// ======================================================================================
// computeSolvedForm — dagNode.cc dispatch + the deterministic theory arms
// ======================================================================================

/// `DagNode::computeSolvedForm`: dispatch to the non-ground side's theory; two ground terms just
/// compare equal.
pub(crate) fn compute_solved_form(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    if !is_ground(env.e, lhs) {
        return compute_solved_form2(env, lhs, rhs, ctx, pending);
    }
    if !is_ground(env.e, rhs) {
        return compute_solved_form2(env, rhs, lhs, ctx, pending);
    }
    env.e.deep_equal(lhs, rhs)
}

/// The per-theory `computeSolvedForm2` — `lhs` is non-ground. Dispatch mirrors the reference's
/// virtual dispatch on the dag class, with the symbol-level correction for one-sided-identity
/// operators (Free node rep, CUI unification theory).
pub(crate) fn compute_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    match &env.e.node(lhs).term {
        NodeTerm::Var { .. } => variable_solved_form2(env, lhs, rhs, ctx, pending),
        NodeTerm::S { .. } => s_solved_form2(env, lhs, rhs, ctx, pending),
        NodeTerm::Acu { .. } | NodeTerm::Au { .. } => {
            // Same-symbol problems and variable rhs both become pending problems, solved a whole
            // theory at a time (ACU_DagNode::computeSolvedForm2 shape; AU identical). Unreachable
            // until S1c lifts the screening, but written to the reference shape.
            let symbol = env.e.node(lhs).symbol();
            if symbol == env.e.node(rhs).symbol() {
                pending.push(Some(symbol), lhs, rhs, false);
                return true;
            }
            if let Some(v) = as_variable_rep(env.e, ctx, rhs) {
                match v {
                    VarRep::Bound(value) => compute_solved_form2(env, lhs, value, ctx, pending),
                    VarRep::Free(_) => {
                        pending.push(Some(symbol), lhs, rhs, false);
                        true
                    }
                }
            } else {
                pending.resolve_theory_clash(env.e, lhs, rhs)
            }
        }
        NodeTerm::Cui { .. } => cui::cui_solved_form2(env, lhs, rhs, ctx, pending),
        NodeTerm::Free { .. } => {
            if unify_theory(env.e, env.e.node(lhs).symbol()) == UnifyTheory::Cui {
                // A one-sided-identity operator: Free rep, CUI theory.
                cui::cui_solved_form2(env, lhs, rhs, ctx, pending)
            } else {
                free_solved_form2(env, lhs, rhs, ctx, pending)
            }
        }
        // The backstop (dagNode.cc `computeSolvedForm2`): only reachable with a ground lhs —
        // non-ground unimplemented tops were screened out — so the sole live case is
        // `<ground> =? X`.
        NodeTerm::Na { .. } => backstop_solved_form2(env, lhs, rhs, ctx, pending),
    }
}

/// A variable rhs, resolved through its chain: bound (to a non-variable value) or free (the
/// representative). The recurring "get representative variable" prelude of every theory arm.
enum VarRep {
    Bound(DagId),
    Free(DagId),
}

fn as_variable_rep(e: &Engine, ctx: &UnifyContext, rhs: DagId) -> Option<VarRep> {
    if var_index(e, rhs).is_none() {
        return None;
    }
    let rep = last_variable_in_chain(e, ctx, rhs);
    let index = var_index(e, rep).unwrap() as usize;
    Some(match ctx.value(index) {
        Some(value) => VarRep::Bound(value),
        None => VarRep::Free(rep),
    })
}

/// `DagNode::computeSolvedForm2` backstop: `<ground> =? X` binds X's representative to the ground
/// term (unpurified).
fn backstop_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    debug_assert!(is_ground(env.e, lhs), "backstop with a non-ground lhs escaped screening");
    let _ = pending;
    match as_variable_rep(env.e, ctx, rhs) {
        Some(VarRep::Bound(value)) => compute_solved_form(env, lhs, value, ctx, pending),
        Some(VarRep::Free(rep)) => {
            ctx.unification_bind(env.e, rep, lhs);
            true
        }
        None => unreachable!("backstop: ground lhs vs non-variable rhs escaped the dispatcher"),
    }
}

// --------------------------------------------------------------------------------------
// Variable theory — variableDagNode.cc
// --------------------------------------------------------------------------------------

fn variable_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    if var_index(env.e, rhs).is_some() {
        let mut lv = last_variable_in_chain(env.e, ctx, lhs);
        let mut rv = last_variable_in_chain(env.e, ctx, rhs);
        if var_key(env.e, lv) == var_key(env.e, rv) {
            return true;
        }
        // Bind lv |-> rv, preferring the retained variable (rv) to be the most constrained: it
        // keeps the LARGEST per-kind sort index (most constrained sort in the linear extension).
        let l_sort_index = env.e.sorts().component_index(env.e.node(lv).sort());
        let r_sort_index = env.e.sorts().component_index(env.e.node(rv).sort());
        if l_sort_index > r_sort_index {
            std::mem::swap(&mut lv, &mut rv);
        }
        let lt = ctx.value(var_index(env.e, lv).unwrap() as usize);
        if lt.is_none() {
            return safe_virtual_replacement(env, lv, rv, ctx, pending);
        }
        let rt = ctx.value(var_index(env.e, rv).unwrap() as usize);
        if rt.is_none() {
            return safe_virtual_replacement(env, rv, lv, ctx, pending);
        }
        // Both bound.
        return safe_virtual_replacement(env, lv, rv, ctx, pending)
            && compute_solved_form(env, lt.unwrap(), rt.unwrap(), ctx, pending);
    }
    // Non-variable rhs: kick to its theory (calling compute_solved_form would bounce back here
    // when rhs is ground).
    compute_solved_form2(env, rhs, lhs, ctx, pending)
}

/// `VariableDagNode::safeVirtualReplacement`: bind `old_var |-> new_var`, then resolve the
/// implicit occurs-check problem if `new_var`'s existing binding contains `old_var`.
fn safe_virtual_replacement(
    env: &mut UnifyEnv,
    old_var: DagId,
    new_var: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    ctx.unification_bind(env.e, old_var, new_var);
    let new_index = var_index(env.e, new_var).unwrap() as usize;
    let Some(new_binding) = ctx.value(new_index) else {
        return true;
    };
    if is_ground(env.e, new_binding) {
        return true;
    }
    let mut occurs = BTreeSet::new();
    insert_variables(env.e, new_binding, &mut occurs);
    for index in occurs {
        if let Some(v) = ctx.value(index)
            && var_index(env.e, v).is_some()
        {
            let rep = last_variable_in_chain(env.e, ctx, v);
            if var_key(env.e, rep) == var_key(env.e, new_var) {
                // Implicit occurs-check issue: unsolve new_var |-> new_binding and re-solve.
                ctx.bind(new_index, None);
                return compute_solved_form2(env, new_binding, new_var, ctx, pending);
            }
        }
    }
    true
}

// --------------------------------------------------------------------------------------
// Free theory — freeDagNode.cc
// --------------------------------------------------------------------------------------

fn free_args(e: &Engine, id: DagId) -> Vec<DagId> {
    match &e.node(id).term {
        NodeTerm::Free { args, .. } => args.clone(),
        _ => unreachable!("free_args on a non-free node"),
    }
}

fn free_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    let s = env.e.node(lhs).symbol();
    if s == env.e.node(rhs).symbol() {
        let largs = free_args(env.e, lhs);
        let rargs = free_args(env.e, rhs);
        debug_assert!(!largs.is_empty(), "constants are ground and never reach here");
        for (l, r) in largs.into_iter().zip(rargs) {
            if !compute_solved_form(env, l, r, ctx, pending) {
                return false;
            }
        }
        return true;
    }
    match as_variable_rep(env.e, ctx, rhs) {
        Some(VarRep::Bound(value)) => compute_solved_form(env, lhs, value, ctx, pending),
        Some(VarRep::Free(rep)) => {
            let purified = match purify_and_occur_check(env, lhs, rep, ctx, pending) {
                Purification::OccursCheckFail => return false,
                Purification::PureAsIs => lhs,
                Purification::Purified(d) => d,
            };
            ctx.unification_bind(env.e, rep, purified);
            true
        }
        None => pending.resolve_theory_clash(env.e, lhs, rhs),
    }
}

enum Purification {
    OccursCheckFail,
    PureAsIs,
    Purified(DagId),
}

/// `FreeDagNode::purifyAndOccurCheck`: occurs-check `rep_var` through the free skeleton and
/// variable-abstract alien (non-free, non-variable) subterms. Ground subterms may stay impure
/// (they can't take part in cycles). Note the reference's asymmetry, preserved here: an alien met
/// *before* any rebuild started is solved against its abstraction variable (it may be impure —
/// binding directly could loop); an alien met *after* the rebuild started is bound directly.
fn purify_and_occur_check(
    env: &mut UnifyEnv,
    this: DagId,
    rep_var: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> Purification {
    if is_ground(env.e, this) {
        return Purification::PureAsIs;
    }
    let s = env.e.node(this).symbol();
    let args = free_args(env.e, this);
    let rep_key = var_key(env.e, rep_var);

    let mut i = 0;
    while i < args.len() {
        let arg = args[i];
        if var_index(env.e, arg).is_some() {
            // Variable — occurs check only.
            let rep = last_variable_in_chain(env.e, ctx, arg);
            if var_key(env.e, rep) == rep_key {
                return Purification::OccursCheckFail;
            }
            i += 1;
            continue;
        }
        if is_free_theory_node(env.e, arg) {
            match purify_and_occur_check(env, arg, rep_var, ctx, pending) {
                Purification::OccursCheckFail => return Purification::OccursCheckFail,
                Purification::PureAsIs => {
                    i += 1;
                    continue;
                }
                Purification::Purified(d) => {
                    return finish_purified(env, s, args, i, d, rep_var, ctx, pending);
                }
            }
        } else {
            // Alien — abstract it. Solving (not binding) because arg may be impure.
            let kind = domain_kind(env.e, s, i);
            let abstraction = ctx.make_fresh_variable(env, kind);
            compute_solved_form(env, arg, abstraction, ctx, pending);
            return finish_purified(env, s, args, i, abstraction, rep_var, ctx, pending);
        }
    }
    Purification::PureAsIs
}

/// The kind of `s`'s `i`-th argument position (Maude's `Symbol::domainComponent`).
fn domain_kind(e: &Engine, s: SymbolId, i: usize) -> KindId {
    e.sorts().kind_of(e.symbol(s).decls[0].domain[i])
}

/// The rebuild tail of `purifyAndOccurCheck`: argument `i` was replaced by `replacement`; process
/// the remaining arguments (aliens now bound **directly** — the reference's second loop is
/// deliberately asymmetric to the first) and rebuild.
fn finish_purified(
    env: &mut UnifyEnv,
    s: SymbolId,
    args: Vec<DagId>,
    i: usize,
    replacement: DagId,
    rep_var: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> Purification {
    let rep_key = var_key(env.e, rep_var);
    let mut new_args = args.clone();
    new_args[i] = replacement;
    for j in (i + 1)..args.len() {
        let arg = args[j];
        if var_index(env.e, arg).is_some() {
            let rep = last_variable_in_chain(env.e, ctx, arg);
            if var_key(env.e, rep) == rep_key {
                return Purification::OccursCheckFail;
            }
        } else if is_free_theory_node(env.e, arg) {
            match purify_and_occur_check(env, arg, rep_var, ctx, pending) {
                Purification::OccursCheckFail => return Purification::OccursCheckFail,
                Purification::PureAsIs => {}
                Purification::Purified(d) => new_args[j] = d,
            }
        } else {
            let kind = domain_kind(env.e, s, j);
            let abstraction = ctx.make_fresh_variable(env, kind);
            ctx.unification_bind(env.e, abstraction, arg);
            new_args[j] = abstraction;
        }
    }
    let (sig, rt) = env.e.parts_mut();
    Purification::Purified(rt.make_free(sig, s, new_args))
}

/// Whether `id` is a plain free-theory application for purification purposes (a one-sided-id
/// operator's Free rep is an alien here — its theory is CUI).
fn is_free_theory_node(e: &Engine, id: DagId) -> bool {
    matches!(e.node(id).term, NodeTerm::Free { .. })
        && unify_theory(e, e.node(id).symbol()) == UnifyTheory::Free
}

// --------------------------------------------------------------------------------------
// S theory — S_DagNode.cc
// --------------------------------------------------------------------------------------

fn s_parts(e: &Engine, id: DagId) -> (SymbolId, Nat, DagId) {
    match &e.node(id).term {
        NodeTerm::S { symbol, count, arg } => (*symbol, count.clone(), *arg),
        _ => unreachable!("s_parts on a non-S node"),
    }
}

fn s_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    let (s, lc, larg) = s_parts(env.e, lhs);
    if s == env.e.node(rhs).symbol() {
        let (_, rc, rarg) = s_parts(env.e, rhs);
        // Decompose by peeling the side with the greater iteration count.
        return match rc.cmp(&lc) {
            std::cmp::Ordering::Equal => compute_solved_form(env, larg, rarg, ctx, pending),
            std::cmp::Ordering::Greater => {
                let diff = rc.checked_sub(&lc).unwrap();
                let d = {
                    let (sig, rt) = env.e.parts_mut();
                    rt.make_s(sig, s, diff, rarg)
                };
                compute_solved_form(env, larg, d, ctx, pending)
            }
            std::cmp::Ordering::Less => {
                let diff = lc.checked_sub(&rc).unwrap();
                let d = {
                    let (sig, rt) = env.e.parts_mut();
                    rt.make_s(sig, s, diff, larg)
                };
                compute_solved_form(env, rarg, d, ctx, pending)
            }
        };
    }
    match as_variable_rep(env.e, ctx, rhs) {
        Some(VarRep::Bound(value)) => compute_solved_form2(env, lhs, value, ctx, pending),
        Some(VarRep::Free(rep)) => {
            // Normal form: the argument is a variable or an alien; only aliens need abstraction.
            let purified = if var_index(env.e, larg).is_some() {
                let arep = last_variable_in_chain(env.e, ctx, larg);
                if var_key(env.e, arep) == var_key(env.e, rep) {
                    return false; // occurs check fail
                }
                lhs
            } else {
                let kind = domain_kind(env.e, s, 0);
                let abstraction = ctx.make_fresh_variable(env, kind);
                // Solving (not binding): larg may be impure.
                compute_solved_form(env, larg, abstraction, ctx, pending);
                let (sig, rt) = env.e.parts_mut();
                rt.make_s(sig, s, lc, abstraction)
            };
            ctx.unification_bind(env.e, rep, purified);
            true
        }
        None => pending.resolve_theory_clash(env.e, lhs, rhs),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;
    use crate::symbol::{IdentitySide, SymbolClass};
    use std::collections::HashMap;

    /// A test name-code source: interns any name into a dense code space (the frontend's `Interner`
    /// role). User-variable base names and fresh `#n` names share the space, as in the real session.
    #[derive(Default)]
    struct TestNames {
        map: HashMap<String, u32>,
        next: u32,
    }
    impl NameCodes for TestNames {
        fn code(&mut self, name: &str) -> u32 {
            if let Some(&c) = self.map.get(name) {
                return c;
            }
            let c = self.next;
            self.next += 1;
            self.map.insert(name.to_string(), c);
            c
        }
    }

    /// Drive a full unsorted-solved-form enumeration (the pre-order-sorted driver skeleton): solve
    /// each equation into one context, then stream solved forms via `pending.solve`. Returns one
    /// snapshot of the ORIGINAL-variable bindings per solved form (empty if there is no unifier).
    fn all_solved_forms(
        env: &mut UnifyEnv,
        n_original: usize,
        equations: &[(DagId, DagId)],
    ) -> Vec<Vec<Option<DagId>>> {
        let mut ctx = UnifyContext::new(n_original, VariableFamily::Unify);
        let mut pending = PendingStack::new();
        for &(l, r) in equations {
            if !compute_solved_form(env, l, r, &mut ctx, &mut pending) {
                return Vec::new(); // viable = false: no unifier
            }
        }
        let mut results = Vec::new();
        let mut first = true;
        loop {
            if !pending.solve(env, first, &mut ctx) {
                break;
            }
            results.push((0..n_original).map(|i| ctx.value(i)).collect());
            first = false;
        }
        results
    }

    fn mkvar(env: &mut UnifyEnv, name: &str, sort: SortId, slot: u32) -> DagId {
        let code = env.names.code(name);
        env.e.make_var(sort, code, slot)
    }

    #[test]
    fn free_unification_binds_arguments() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", nat, 0);
        let y = mkvar(&mut env, "Y", nat, 1);
        let ac = env.e.make_const(a);
        let bc = env.e.make_const(b);
        let lhs = env.e.make_free(f, vec![x, y]);
        let rhs = env.e.make_free(f, vec![ac, bc]);

        let forms = all_solved_forms(&mut env, 2, &[(lhs, rhs)]);
        assert_eq!(forms.len(), 1, "free unification is unitary");
        assert!(env.e.deep_equal(forms[0][0].unwrap(), ac), "X --> a");
        assert!(env.e.deep_equal(forms[0][1].unwrap(), bc), "Y --> b");
    }

    #[test]
    fn free_occurs_check_fails() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let f = e.add_op("f", vec![nat], nat);
        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", nat, 0);
        let fx = env.e.make_free(f, vec![x]);
        // X =? f(X): occurs check must fail — no unifier.
        let forms = all_solved_forms(&mut env, 1, &[(x, fx)]);
        assert!(forms.is_empty(), "X =? f(X) has no unifier");
    }

    #[test]
    fn variable_variable_unifies() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", nat, 0);
        let y = mkvar(&mut env, "Y", nat, 1);
        let forms = all_solved_forms(&mut env, 2, &[(x, y)]);
        assert_eq!(forms.len(), 1);
        // One variable is bound to the other (same sort → X |-> Y by orientation).
        let bx = forms[0][0];
        let by = forms[0][1];
        assert!(
            (bx.is_some() && by.is_none()) || (by.is_some() && bx.is_none()),
            "exactly one of X, Y is bound to the other"
        );
        let bound = bx.or(by).unwrap();
        assert!(var_index(env.e, bound).is_some(), "bound to a variable");
    }

    #[test]
    fn s_theory_peels_and_binds() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op_iter("s", vec![nat], nat);
        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", nat, 0);
        let z = env.e.make_const(zero);
        let lhs = env.e.make_iter(s, 3, x); // s^3(X)
        let rhs = env.e.make_iter(s, 5, z); // s^5(0)
        let forms = all_solved_forms(&mut env, 1, &[(lhs, rhs)]);
        assert_eq!(forms.len(), 1, "S-theory unification is unitary here");
        // X --> s^2(0)
        let expected = {
            let z2 = env.e.make_const(zero);
            env.e.make_iter(s, 2, z2)
        };
        assert!(env.e.deep_equal(forms[0][0].unwrap(), expected), "X --> s^2(0)");
    }

    #[test]
    fn s_theory_count_mismatch_on_ground_fails() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op_iter("s", vec![nat], nat);
        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", nat, 0);
        let z1 = env.e.make_const(zero);
        let z2 = env.e.make_const(zero);
        // s^2(0) =? s^2(X) → X = 0 (unitary); but s^2(0) =? s^3(X) → s^2 vs s^3(X): peel X = ... no,
        // check a genuine ground clash: s^2(0) =? s^3(0) is ground-unequal → no unifier.
        let lhs = env.e.make_iter(s, 2, z1);
        let rhs = env.e.make_iter(s, 3, z2);
        let forms = all_solved_forms(&mut env, 1, &[(lhs, rhs)]);
        assert!(forms.is_empty(), "s^2(0) =? s^3(0) is a ground clash");
        // sanity: X still an original slot, unused
        let _ = x;
    }

    /// CUI with a one-sided `left id:` — the U-ch13-10 shape. The operator is a **Free** node in
    /// tnk (identity withheld from the kernel) but a CUI-unification-theory symbol, so this also
    /// exercises the generic (Free-node) CUI arg/rebuild path. Two unsorted solved forms, matching
    /// the reference's two unifiers (one via the free decomposition, one via the id collapse).
    #[test]
    fn cui_left_id_enumerates_two_forms() {
        let mut e = Engine::new();
        let magma = e.add_sort("Magma");
        let elem = e.add_sort("Elem");
        e.add_subsort(elem, magma);
        e.close_sorts();
        // op __ : Magma Magma -> Magma  (one-sided left id: e) — Free node rep in tnk.
        let junc = e.add_op("__", vec![magma, magma], magma);
        let ec = e.add_op("e", vec![], elem);
        let ac = e.add_op("a", vec![], elem);
        e.set_one_sided_identity(junc, IdentitySide::Left, ec);
        // Screening treats it as a CUI-unification symbol; sanity-check the classification.
        assert_eq!(unify_theory(&e, junc), UnifyTheory::Cui);
        let _ = SymbolClass::Standard;

        let mut names = TestNames::default();
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let x = mkvar(&mut env, "X", magma, 0);
        let y = mkvar(&mut env, "Y", magma, 1);
        let a_l = env.e.make_const(ac);
        let a_r1 = env.e.make_const(ac);
        let a_r2 = env.e.make_const(ac);
        // X a =? Y a a  ==  __(X, a) =? __(__(Y, a), a)
        let lhs = env.e.make_free(junc, vec![x, a_l]);
        let ya = env.e.make_free(junc, vec![y, a_r1]);
        let rhs = env.e.make_free(junc, vec![ya, a_r2]);

        let forms = all_solved_forms(&mut env, 2, &[(lhs, rhs)]);
        assert_eq!(forms.len(), 2, "left-id CUI gives two unsorted solved forms");
    }
}
