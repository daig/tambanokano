//! The order-sorted unification driver — Maude's `UnificationProblem`
//! (`src/Higher/unificationProblem.cc`): it drives the solved-form core ([`super`]) and the
//! sort-solving BDDs ([`crate::sort_bdds`]) to enumerate order-sorted unifiers **in reference
//! order**.
//!
//! Enumeration is two-level, exactly as `findNextUnifier`:
//!   * **outer** — distinct unsorted solved forms from the pending stack (`pending.solve`);
//!   * **inner** — distinct maximal sort assignments per unsorted form (`AllSat` over the
//!     `maximal` BDD).
//!
//! Per unsorted form (`findOrderSortedUnifiers`): collect the free variables, give each a BDD
//! block, build the `unifier` BDD (each free variable's sort ≤ its declared sort; each bound
//! variable's *generalized sort* ≤ its declared sort), restrict to maximal assignments, and rename
//! the free variables to the `#1,#2,…` family (slot order, reset per form). Per assignment
//! (`bindFreeVariables`): decode each free variable's sort and instantiate.

use super::{
    PendingStack, Screen, UnifyContext, UnifyEnv, compute_solved_form, instantiate, is_ground,
    screen_for_unification,
};
use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::fresh::{FreshVariableGenerator, VariableFamily};
use crate::num::Nat;
use crate::sort::{KindId, SortId};
use crate::sort_bdds::{AllSat, SortBdds};
use biodivine_lib_bdd::Bdd;

/// The declared sort and interned base-name code of one original problem variable, reordered after
/// each unificand is theory-normalized (Maude's `Term::normalize(true)` → `indexVariables` order).
#[derive(Clone, Copy)]
pub struct VarSpec {
    pub sort: SortId,
    pub name: u32,
}

/// A resumable order-sorted unification problem.
pub struct UnifyProblem {
    equations: Vec<(DagId, DagId)>,
    n_original: usize,
    /// Declared metadata by absolute original substitution slot. `None` is an inactive layout gap:
    /// it occupies a slot (and therefore shifts fresh variables) but is not a problem variable.
    var_specs: Vec<Option<VarSpec>>,
    family: VariableFamily,
    /// Fresh-variable base number (the `metaUnify` counter; 0 for the object-level command). A
    /// `Nat` internally (Maude's is a bignum), constructed from the `u64` API parameter.
    base: Nat,
    /// New slot → caller's pre-normalization slot. Maude assigns original slots only after
    /// theory-normalizing each unificand; callers use this to render substitution keys in that order.
    original_order: Vec<usize>,
    ctx: UnifyContext,
    pending: PendingStack,
    /// `false` if a unificand sits under an unimplemented-theory top (the screen); the driver yields
    /// no unifiers and the caller suppresses the `Decision time`/unifier output (warning only).
    problem_okay: bool,
    /// `false` if the many-sorted solve failed outright (no unifier at all).
    viable: bool,
    order_sorted: Option<OrderSorted>,
}

/// The order-sorted state for one unsorted solved form. `AllSat` owns its `Bdd`, so the `SortBdds`
/// instance is not retained past `find_order_sorted_unifiers`.
struct OrderSorted {
    all_sat: AllSat,
    /// The unsorted solved form (bound slots fully instantiated over the free variables).
    template: Vec<Option<DagId>>,
    /// One entry per free variable, in ascending slot order.
    free: Vec<FreeVar>,
}

#[derive(Clone, Copy)]
struct FreeVar {
    slot: usize,
    first_real: u16,
    kind: KindId,
    /// The `#k` name code assigned to this free variable (slot order, reset per form).
    name: u32,
}

/// Normalize each unificand before assigning its visible variable slots. Commutative normalization
/// can reorder a term's variables (`c(f(X,Y), Z)` visits `Z` before `Y`), and Maude performs exactly
/// this pass in `UnificationProblem` before it creates the substitution.
fn normalize_and_reindex(
    e: &mut Engine,
    mut equations: Vec<(DagId, DagId)>,
    specs: Vec<VarSpec>,
) -> (Vec<(DagId, DagId)>, Vec<VarSpec>, Vec<usize>) {
    // Variable symbols are instantiated while the parser builds a term bottom-up. Consequently,
    // the first variable sort seen by a right-to-left postorder walk fixes the relative symbol
    // order of variables of different sorts. Recover that order before normalization, then let the
    // engine reconcile it with VariableSymbols materialized by earlier commands in this module.
    let mut variable_sort_order = Vec::new();
    for &(lhs, rhs) in &equations {
        for root in [lhs, rhs] {
            let mut work = vec![root];
            while let Some(id) = work.pop() {
                let node = e.node(id);
                if matches!(node.term, NodeTerm::Var { .. }) {
                    let sort = e.sort_of(id);
                    if !variable_sort_order.contains(&sort) {
                        variable_sort_order.push(sort);
                    }
                    continue;
                }
                // LIFO + source/canonical child order gives the parser's right-to-left construction
                // order.  This is used only to rank VariableSymbols, not to assign slots.
                work.extend(node.children());
            }
        }
    }
    // Freeze and recover the module-level per-sort VariableSymbol order before canonical
    // normalization and before the solver creates kind-level fresh variables. This order also
    // governs original slot assignment and final AC/ACU substitution element order.
    e.rank_variable_sorts(&mut variable_sort_order);

    for (lhs, rhs) in &mut equations {
        *lhs = e.normalize_for_unify(*lhs);
        *rhs = e.normalize_for_unify(*rhs);
    }

    let mut seen = vec![false; specs.len()];
    let mut order = Vec::with_capacity(specs.len());
    for &(lhs, rhs) in &equations {
        for root in [lhs, rhs] {
            let mut work = vec![root];
            while let Some(id) = work.pop() {
                let node = e.node(id);
                if let NodeTerm::Var { index, .. } = node.term {
                    let old = index as usize;
                    if !seen[old] {
                        seen[old] = true;
                        order.push(old);
                    }
                    continue;
                }
                let mut children: Vec<DagId> = node.children().collect();
                let reorder_variables = matches!(node.term, NodeTerm::Acu { .. })
                    || matches!(node.term, NodeTerm::Cui { .. })
                        && e.symbol(node.symbol()).axioms.comm;
                if reorder_variables {
                    children.sort_by(|&a, &b| {
                        let (NodeTerm::Var { index: ai, .. }, NodeTerm::Var { index: bi, .. }) =
                            (&e.node(a).term, &e.node(b).term)
                        else {
                            return std::cmp::Ordering::Equal;
                        };
                        let (ai, bi) = (*ai as usize, *bi as usize);
                        let (asort, bsort) = (e.sort_of(a), e.sort_of(b));
                        if asort == bsort {
                            // CUI_Term/ACU_Term normalize variables by their Maude token-name codes
                            // before `indexVariables`. The frontend supplies ranks from the standing
                            // prelude token table; meta/core callers naturally pass their own codes.
                            return specs[ai].name.cmp(&specs[bi].name);
                        }
                        let ra = variable_sort_order
                            .iter()
                            .position(|&sort| sort == asort)
                            .expect("variable sort was ranked before normalization");
                        let rb = variable_sort_order
                            .iter()
                            .position(|&sort| sort == bsort)
                            .expect("variable sort was ranked before normalization");
                        ra.cmp(&rb)
                    });
                }
                work.extend(children.into_iter().rev());
            }
        }
    }
    assert_eq!(
        order.len(),
        specs.len(),
        "every original variable must occur in a unificand"
    );

    if order.iter().copied().ne(0..specs.len()) {
        let mut new_slots = vec![0; specs.len()];
        for (new, &old) in order.iter().enumerate() {
            new_slots[old] = new as u32;
        }
        for (lhs, rhs) in &mut equations {
            *lhs = e.remap_variable_slots(*lhs, &new_slots);
            *rhs = e.remap_variable_slots(*rhs, &new_slots);
        }
    }
    let specs = order.iter().map(|&old| specs[old]).collect();
    (equations, specs, order)
}

impl UnifyProblem {
    /// Build a problem from `equations` (already-built dags with `Var` leaves at the original
    /// slots) and their `var_specs` (declared sort + base-name code per slot). `family`/`base`
    /// select the fresh-variable family and starting number (`#`/0 for the object-level command;
    /// the `metaUnify` counter otherwise). Screens for unimplemented theories and runs the
    /// many-sorted solve, mirroring the reference constructor.
    pub fn new(
        env: &mut UnifyEnv,
        equations: Vec<(DagId, DagId)>,
        var_specs: Vec<VarSpec>,
        family: VariableFamily,
        base: &str,
    ) -> UnifyProblem {
        // The fresh-variable base counter — a decimal string so `metaUnify`'s bignum `Nat` base
        // (Maude's `mpz`) survives; the object command and the current-signature descent pass "0".
        let (equations, var_specs, original_order) =
            normalize_and_reindex(env.e, equations, var_specs);
        let n_original = var_specs.len();
        let base = Nat::from_decimal(base).unwrap_or_else(Nat::zero);
        let mut prob = UnifyProblem {
            equations,
            n_original,
            var_specs: var_specs.into_iter().map(Some).collect(),
            family,
            base: base.clone(),
            ctx: UnifyContext::with_base(n_original, family, base),
            original_order,
            pending: PendingStack::new(),
            problem_okay: true,
            viable: false,
            order_sorted: None,
        };

        // Screen every unificand for non-ground unimplemented-theory tops (the reference bails on
        // UNIMPLEMENTED). The warning text is phase-E; the effect (no unifiers) is what matters.
        let mut warned = Vec::new();
        for &(l, r) in &prob.equations {
            if screen_for_unification(env.e, l, &mut warned) == Screen::Unimplemented
                || screen_for_unification(env.e, r, &mut warned) == Screen::Unimplemented
            {
                prob.problem_okay = false;
                return prob;
            }
        }

        // Many-sorted solve: each equation into the shared context; any failure ⇒ no unifier.
        for &(l, r) in &prob.equations {
            if !compute_solved_form(env, l, r, &mut prob.ctx, &mut prob.pending) {
                prob.viable = false;
                return prob;
            }
        }
        prob.viable = true;
        prob
    }

    /// Build a narrowing unification problem whose variable slots were already assigned by the
    /// caller. Unlike ordinary command unification, narrowing must preserve the equation-variable
    /// prefix followed by the current state's term-first variable order.
    pub fn new_preserving_order(
        env: &mut UnifyEnv,
        mut equations: Vec<(DagId, DagId)>,
        var_specs: Vec<VarSpec>,
        family: VariableFamily,
        base: &str,
    ) -> UnifyProblem {
        for (lhs, rhs) in &mut equations {
            *lhs = env.e.normalize_for_unify(*lhs);
            *rhs = env.e.normalize_for_unify(*rhs);
        }
        let n_original = var_specs.len();
        let base = Nat::from_decimal(base).unwrap_or_else(Nat::zero);
        let mut prob = UnifyProblem {
            equations,
            n_original,
            var_specs: var_specs.into_iter().map(Some).collect(),
            family,
            base: base.clone(),
            ctx: UnifyContext::with_base(n_original, family, base),
            original_order: (0..n_original).collect(),
            pending: PendingStack::new(),
            problem_okay: true,
            viable: false,
            order_sorted: None,
        };
        let mut warned = Vec::new();
        for &(l, r) in &prob.equations {
            if screen_for_unification(env.e, l, &mut warned) == Screen::Unimplemented
                || screen_for_unification(env.e, r, &mut warned) == Screen::Unimplemented
            {
                prob.problem_okay = false;
                return prob;
            }
        }
        for &(l, r) in &prob.equations {
            if !compute_solved_form(env, l, r, &mut prob.ctx, &mut prob.pending) {
                return prob;
            }
        }
        prob.viable = true;
        prob
    }

    /// Build a narrowing-only problem over an absolute substitution layout.
    ///
    /// `active_specs` gives `(absolute_slot, spec)` pairs for variables that occur in the already
    /// remapped unificands. Slots not listed are inactive gaps: they remain unbound, take no part in
    /// free-variable or sort processing, but count in `n_original` so solver-created variables begin
    /// at the same module-wide index as Maude's `NarrowingUnificationProblem`.
    pub fn new_for_variant(
        env: &mut UnifyEnv,
        mut equations: Vec<(DagId, DagId)>,
        active_specs: Vec<(usize, VarSpec)>,
        n_original: usize,
        family: VariableFamily,
        base: &str,
    ) -> UnifyProblem {
        let mut var_specs = vec![None; n_original];
        for (slot, spec) in active_specs {
            assert!(
                slot < n_original,
                "active variable slot {slot} is outside layout size {n_original}"
            );
            assert!(
                var_specs[slot].replace(spec).is_none(),
                "duplicate active variable slot {slot}"
            );
        }
        for (lhs, rhs) in &mut equations {
            *lhs = env.e.normalize_for_unify(*lhs);
            *rhs = env.e.normalize_for_unify(*rhs);
        }
        let base = Nat::from_decimal(base).unwrap_or_else(Nat::zero);
        let mut prob = UnifyProblem {
            equations,
            n_original,
            var_specs,
            family,
            base: base.clone(),
            ctx: UnifyContext::with_base(n_original, family, base),
            original_order: (0..n_original).collect(),
            pending: PendingStack::new(),
            problem_okay: true,
            viable: false,
            order_sorted: None,
        };
        let mut warned = Vec::new();
        for &(l, r) in &prob.equations {
            if screen_for_unification(env.e, l, &mut warned) == Screen::Unimplemented
                || screen_for_unification(env.e, r, &mut warned) == Screen::Unimplemented
            {
                prob.problem_okay = false;
                return prob;
            }
        }
        for &(l, r) in &prob.equations {
            if !compute_solved_form(env, l, r, &mut prob.ctx, &mut prob.pending) {
                return prob;
            }
        }
        prob.viable = true;
        prob
    }

    /// Whether the problem passed screening (implemented theories only). When `false` the caller
    /// prints only the (stripped) warning — no `Decision time`, no unifier lines.
    pub fn problem_okay(&self) -> bool {
        self.problem_okay
    }

    /// Original-variable order after theory normalization (new slot → caller slot).
    pub fn original_variable_order(&self) -> &[usize] {
        &self.original_order
    }

    /// Whether any theory flagged possibly-incomplete unification (the A/AU depth bound).
    pub fn is_incomplete(&self) -> bool {
        self.pending.is_incomplete()
    }

    /// The number of free variables in the current unifier (for the `irredundant` filter later).
    pub fn nr_free_variables(&self) -> usize {
        self.order_sorted.as_ref().map_or(0, |os| os.free.len())
    }

    /// The **next** fresh-variable index as a decimal string — `base + nrFreeVariables` — Maude's
    /// `lastVarIndex` for the legacy `metaUnify`/`metaDisjointUnify` result's `Nat` component. A string
    /// (not a `u64`) because the base is an unbounded `Nat`.
    pub fn last_var_index_decimal(&self) -> String {
        self.base
            .add(&Nat::from_u64(self.nr_free_variables() as u64))
            .to_decimal()
    }

    /// The next unifier as the value of each original variable (slot order), or `None` when
    /// exhausted. Ordinary problems have no inactive slots, so every entry is present.
    pub fn find_next(&mut self, env: &mut UnifyEnv) -> Option<Vec<DagId>> {
        self.find_next_full(env).map(|solution| {
            solution
                .into_iter()
                .map(|value| value.expect("ordinary unification has no inactive slots"))
                .collect()
        })
    }

    /// The next unifier in the absolute original substitution layout. Active slots are `Some`;
    /// inactive narrowing gaps remain `None`. Fresh solver variables are instantiated into the
    /// active values but are not appended to this vector.
    pub fn find_next_full(&mut self, env: &mut UnifyEnv) -> Option<Vec<Option<DagId>>> {
        if !self.viable || !self.problem_okay {
            return None;
        }
        let mut first = self.order_sorted.is_none();
        if !first {
            if self
                .order_sorted
                .as_mut()
                .unwrap()
                .all_sat
                .next_assignment()
            {
                return Some(self.bind_free_variables_full(env));
            }
            self.order_sorted = None;
        }
        loop {
            if !self.pending.solve(env, first, &mut self.ctx) {
                return None;
            }
            self.find_order_sorted_unifiers(env);
            first = false;
            if self.order_sorted.is_some() {
                break;
            }
        }
        self.order_sorted
            .as_mut()
            .unwrap()
            .all_sat
            .next_assignment(); // can't fail
        Some(self.bind_free_variables_full(env))
    }

    /// `findOrderSortedUnifiers`: build the `unifier`/`maximal` BDDs for the current unsorted solved
    /// form and set `order_sorted` (or leave it `None` if this form has no order-sorted unifier).
    fn find_order_sorted_unifiers(&mut self, env: &mut UnifyEnv) {
        let template = self.ctx.values().to_vec();
        let n_actual = template.len();
        let sorts = env.e.signature().sorts();

        // Collect free slots (ascending) with their kind and bit width; assign real blocks.
        struct Raw {
            slot: usize,
            sort: SortId,
            kind: KindId,
            bits: u16,
        }
        let mut raws: Vec<Raw> = Vec::new();
        let mut total_bits: u16 = 0;
        for slot in 0..n_actual {
            if template[slot].is_none() {
                let sort = if slot < self.n_original {
                    let Some(spec) = self.var_specs[slot] else {
                        continue;
                    };
                    spec.sort
                } else {
                    self.ctx.fresh_variable_sort(slot)
                };
                let kind = sorts.kind_of(sort);
                let bits = calc_bits(sorts.kind(kind).index_order.len());
                total_bits += bits;
                raws.push(Raw {
                    slot,
                    sort,
                    kind,
                    bits,
                });
            }
        }

        let mut sb = SortBdds::new(env.e.signature(), total_bits);
        let real0 = sb.real0();
        // real block per free slot (ascending order).
        let mut real_to_bdd: Vec<Option<u16>> = vec![None; n_actual];
        let mut cursor = real0;
        for r in &raws {
            real_to_bdd[r.slot] = Some(cursor);
            cursor += r.bits;
        }

        let sig = env.e.signature();
        // unifier: fresh free variables constrained to their kind's valid range (≤ their fresh sort).
        let mut unifier: Option<Bdd> = None;
        let and_in = |unifier: &mut Option<Bdd>, b: Bdd| {
            *unifier = Some(match unifier.take() {
                Some(u) => u.and(&b),
                None => b,
            });
        };
        for r in &raws {
            if r.slot >= self.n_original {
                let b = sb.get_remapped_leq_relation(sig, r.sort, real_to_bdd[r.slot].unwrap());
                and_in(&mut unifier, b);
            }
        }
        // Active original variables: bound ⇒ generalized-sort ≤ declared sort; free ⇒ ≤ declared
        // sort. Inactive layout gaps deliberately contribute no BDD block or constraint.
        for i in 0..self.n_original {
            let Some(spec) = self.var_specs[i] else {
                continue;
            };
            let sort = spec.sort;
            let kind = sig.sorts().kind_of(sort);
            // A bound variable declared at the kind/error sort is source-general: every
            // generalized sort in this kind satisfies it. Besides avoiding a useless BDD, this
            // prevents composing very large static terms merely to prove a tautology.
            if template[i].is_some() && sort == sig.sorts().error_sort(kind) {
                continue;
            }
            let li = sig.sorts().component_index(sort);
            let b = match template[i] {
                Some(d) => {
                    let gen_sort = generalized_sort(env.e, sig, &mut sb, &real_to_bdd, d);
                    sb.apply_leq_relation(kind, li, &gen_sort)
                }
                None => sb.get_remapped_leq_relation(sig, sort, real_to_bdd[i].unwrap()),
            };
            and_in(&mut unifier, b);
            if unifier.as_ref().unwrap().is_false() {
                self.order_sorted = None;
                return;
            }
        }
        let unifier = unifier.unwrap_or_else(|| sb_true(&sb));

        if unifier.is_false() {
            self.order_sorted = None;
            return;
        }

        let free_blocks: Vec<(KindId, u16)> = raws
            .iter()
            .map(|r| (r.kind, real_to_bdd[r.slot].unwrap()))
            .collect();
        let maximal = sb.maximal_from_unifier(&unifier, &free_blocks);
        // AllSat over [real0, real0 + total_bits - 1] (reference `secondBase .. nextBddVariable-1`).
        // With no free variables the range is empty (real0 ≥ 2 for any module with sorts, so no
        // underflow) — AllSat then yields exactly one empty assignment (the ground unifier).
        let last_real = real0 + total_bits - 1;
        let all_sat = AllSat::new(maximal, real0, last_real);

        // Assign `#k` names to the free variables in slot order (reset per form).
        let mut generator = FreshVariableGenerator::with_base(self.base.clone());
        let free: Vec<FreeVar> = raws
            .iter()
            .enumerate()
            .map(|(k, r)| {
                let name = env.names.code(generator.fresh_name(k, self.family));
                FreeVar {
                    slot: r.slot,
                    first_real: real_to_bdd[r.slot].unwrap(),
                    kind: r.kind,
                    name,
                }
            })
            .collect();

        self.order_sorted = Some(OrderSorted {
            all_sat,
            template,
            free,
        });
    }

    /// `bindFreeVariables`: decode each free variable's assigned sort from the current AllSat
    /// assignment, build the `#k` variable of that sort, and instantiate the bound active slots.
    fn bind_free_variables_full(&mut self, env: &mut UnifyEnv) -> Vec<Option<DagId>> {
        let os = self.order_sorted.as_ref().unwrap();
        let asg = os.all_sat.assignment();
        let mut subst = os.template.clone();

        // Decode and materialize each free variable directly. Keeping the assignment and free-slot
        // metadata borrowed avoids cloning both vectors for every order-sorted solution.
        for fv in &os.free {
            let new_sort = {
                let sorts = env.e.signature().sorts();
                let order = &sorts.kind(fv.kind).index_order;
                let bits = calc_bits(order.len());
                let mut local = 0u32;
                for k in 0..bits {
                    if asg[(fv.first_real + k) as usize] == 1 {
                        local |= 1 << k;
                    }
                }
                order[local as usize]
            };
            subst[fv.slot] = Some(env.e.make_var(new_sort, fv.name, fv.slot as u32));
        }

        // Instantiate bound active originals (free originals already hold their `#k` variable).
        for i in 0..self.n_original {
            if self.var_specs[i].is_none() || os.free.iter().any(|free| free.slot == i) {
                continue;
            }
            if let Some(v) = subst[i]
                && let Some(d) = instantiate(env.e, &subst, v)
            {
                subst[i] = Some(d);
            }
        }
        subst.truncate(self.n_original);
        subst
    }

    /// GC roots: the original equations, the context, and the pending stack. The caller roots these
    /// while a problem is live (unification builds many transient nodes).
    pub fn gc_roots(&self) -> Vec<DagId> {
        let mut roots: Vec<DagId> = self.equations.iter().flat_map(|&(l, r)| [l, r]).collect();
        roots.extend(self.ctx.gc_roots());
        roots.extend(self.pending.gc_roots());
        if let Some(os) = &self.order_sorted {
            roots.extend(os.template.iter().copied().flatten());
        }
        roots
    }
}

/// `DagNode::computeGeneralizedSort2`: the sort of `id` as a BDD bit-vector over the free
/// variables' real blocks. Ground subterms use their concrete sort; a free variable uses its
/// block; applications compose; the S successor case-splits on the argument sort. A free function
/// over `&Engine` (not `&mut UnifyEnv`) so it can run while the driver holds `sig` borrowed.
fn generalized_sort(
    e: &Engine,
    sig: &crate::engine::Signature,
    sb: &mut SortBdds,
    real_to_bdd: &[Option<u16>],
    id: DagId,
) -> Vec<Bdd> {
    if is_ground(e, id) {
        let sort = e.sort_of(id);
        let kind = sig.sorts().kind_of(sort);
        let bits = calc_bits(sig.sorts().kind(kind).index_order.len());
        return sb.make_index_vector(bits, sig.sorts().component_index(sort));
    }
    match &e.node(id).term {
        NodeTerm::Var { index, .. } => {
            let slot = *index as usize;
            let first = real_to_bdd[slot].expect("free variable has a BDD block");
            let sort = e.sort_of(id);
            let kind = sig.sorts().kind_of(sort);
            let bits = calc_bits(sig.sorts().kind(kind).index_order.len());
            sb.make_variable_bdd(first, bits)
        }
        NodeTerm::S { symbol, count, arg } => {
            let (symbol, count, arg) = (*symbol, count.clone(), *arg);
            s_generalized_sort(e, sig, sb, real_to_bdd, symbol, &count, arg)
        }
        // ACU / AU applications are N-ary but the sort function is binary: left-fold
        // `operator_compose` over the flattened element sequence (children() expands ACU
        // multiplicities). The AC sort function is symmetric, so the fold direction is immaterial.
        NodeTerm::Acu { .. } | NodeTerm::Au { .. } => {
            let symbol = e.node(id).symbol();
            let children: Vec<DagId> = e.node(id).children().collect();
            let mut acc = generalized_sort(e, sig, sb, real_to_bdd, children[0]);
            for &c in &children[1..] {
                let cs = generalized_sort(e, sig, sb, real_to_bdd, c);
                let mut inputs = acc;
                inputs.extend(cs);
                acc = sb.operator_compose(sig, symbol, &inputs);
            }
            acc
        }
        // Free / CUI (and one-sided-id Free) applications: arity matches the sort function; compose
        // all children's sorts at once.
        _ => {
            let symbol = e.node(id).symbol();
            let children: Vec<DagId> = e.node(id).children().collect();
            let mut inputs = Vec::new();
            for c in children {
                inputs.extend(generalized_sort(e, sig, sb, real_to_bdd, c));
            }
            sb.operator_compose(sig, symbol, &inputs)
        }
    }
}

/// `S_Symbol::computeGeneralizedSort2`: for each possible argument sort index `i`, compute the
/// ground iterated output sort (`compute_s_sort` for the count) and case-split symbolically.
fn s_generalized_sort(
    e: &Engine,
    sig: &crate::engine::Signature,
    sb: &mut SortBdds,
    real_to_bdd: &[Option<u16>],
    symbol: crate::symbol::SymbolId,
    count: &Nat,
    arg: DagId,
) -> Vec<Bdd> {
    let input = generalized_sort(e, sig, sb, real_to_bdd, arg);
    let n_bits = input.len();
    let negated: Vec<Bdd> = input.iter().map(|b| b.not()).collect();
    let kind = sig.sorts().kind_of(sig.symbol(symbol).decls[0].range);
    let order = sig.sorts().kind(kind).index_order.clone();

    let mut result: Vec<Bdd> = (0..n_bits).map(|_| sb.mk_false()).collect();
    for (i, &in_sort) in order.iter().enumerate() {
        // equal := (input == i)
        let mut equal = sb.mk_true();
        let mut in_idx = i;
        for j in 0..n_bits {
            equal = equal.and(if in_idx & 1 == 1 {
                &input[j]
            } else {
                &negated[j]
            });
            in_idx >>= 1;
        }
        let out_sort = sig.compute_s_sort(symbol, in_sort, count);
        let mut out_idx = sig.sorts().component_index(out_sort);
        for r in result.iter_mut().take(n_bits) {
            if out_idx & 1 == 1 {
                *r = r.or(&equal);
            }
            out_idx >>= 1;
        }
    }
    result
}

/// Bits to index `n` values (mirror of `sort_bdds::calculate_nr_bits`, kept local so the driver
/// can size blocks without a SortBdds instance).
fn calc_bits(n: usize) -> u16 {
    let mut bits = 1u16;
    let mut representable = 2usize;
    while representable < n {
        bits += 1;
        representable <<= 1;
    }
    bits
}

/// A `true` BDD in `sb`'s universe (for a problem with no constraints — all variables ground).
fn sb_true(sb: &SortBdds) -> Bdd {
    sb.mk_true()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;
    use crate::unify::NameCodes;
    use std::collections::HashMap;

    #[derive(Default)]
    struct TestNames {
        map: HashMap<String, u32>,
        rev: Vec<String>,
    }
    impl NameCodes for TestNames {
        fn code(&mut self, name: &str) -> u32 {
            if let Some(&c) = self.map.get(name) {
                return c;
            }
            let c = self.rev.len() as u32;
            self.map.insert(name.to_string(), c);
            self.rev.push(name.to_string());
            c
        }
    }
    /// Decode a value dag to (name code, sort name) if it is a variable leaf, for assertions.
    fn as_var(e: &Engine, id: DagId) -> Option<(u32, String)> {
        match &e.node(id).term {
            NodeTerm::Var { name, .. } => Some((*name, e.sorts().name(e.sort_of(id)).to_string())),
            _ => None,
        }
    }

    /// `U-probe-01-maximal-sorts` first problem: `X:S1 =? Y:S2` with `A B < S1`, `A B < S2`,
    /// `S1 S2 < T`. Two unifiers, one per maximal lower bound (A, B), each binding X and Y to the
    /// same fresh `#1` variable of that sort. End-to-end: var-var solve → generalized sort →
    /// antichain maximality → fresh naming → instantiate.
    #[test]
    fn antichain_two_unifiers() {
        let mut e = Engine::new();
        let a = e.add_sort("A");
        let b = e.add_sort("B");
        let s1 = e.add_sort("S1");
        let s2 = e.add_sort("S2");
        let t = e.add_sort("T");
        e.add_subsort(a, s1);
        e.add_subsort(b, s1);
        e.add_subsort(a, s2);
        e.add_subsort(b, s2);
        e.add_subsort(s1, t);
        e.add_subsort(s2, t);
        e.close_sorts();
        let mut names = TestNames::default();
        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };

        let xname = env.names.code("X");
        let yname = env.names.code("Y");
        let x = env.e.make_var(s1, xname, 0);
        let y = env.e.make_var(s2, yname, 1);
        let specs = vec![
            VarSpec {
                sort: s1,
                name: xname,
            },
            VarSpec {
                sort: s2,
                name: yname,
            },
        ];

        let mut prob = UnifyProblem::new(&mut env, vec![(x, y)], specs, VariableFamily::Unify, "0");
        assert!(prob.problem_okay());

        let hash1 = env.names.code("#1");
        let mut sorts: Vec<String> = Vec::new();
        while let Some(binding) = prob.find_next(&mut env) {
            assert_eq!(binding.len(), 2);
            let vx = as_var(env.e, binding[0]).expect("X --> variable");
            let vy = as_var(env.e, binding[1]).expect("Y --> variable");
            assert_eq!(vx, vy, "X and Y unify to the same variable");
            assert_eq!(vx.0, hash1, "the free variable is renamed #1");
            sorts.push(vx.1);
        }
        assert_eq!(sorts.len(), 2, "one unifier per maximal lower bound");
        sorts.sort();
        assert_eq!(sorts, vec!["A", "B"], "the two maximal lower bounds");
    }

    /// A ground clash yields no unifier; a trivial ground equality yields exactly one (empty)
    /// unifier — the zero-free-variable path through the order-sorted machinery.
    #[test]
    fn ground_cases() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let one = e.add_op("1", vec![], nat);
        let mut names = TestNames::default();
        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };

        let z1 = env.e.make_const(zero);
        let z2 = env.e.make_const(zero);
        let mut ok =
            UnifyProblem::new(&mut env, vec![(z1, z2)], vec![], VariableFamily::Unify, "0");
        let mut n = 0;
        while let Some(b) = ok.find_next(&mut env) {
            assert!(b.is_empty());
            n += 1;
        }
        assert_eq!(n, 1, "0 =? 0 has exactly one (empty) unifier");

        let o = env.e.make_const(one);
        let z = env.e.make_const(zero);
        let mut clash =
            UnifyProblem::new(&mut env, vec![(o, z)], vec![], VariableFamily::Unify, "0");
        assert!(clash.find_next(&mut env).is_none(), "1 =? 0 has no unifier");
    }
    #[test]
    fn million_iter_compound_identity_collapse_is_order_sorted() {
        let mut e = Engine::new();
        let small = e.add_sort("Small");
        let big = e.add_sort("Big");
        e.add_subsort(small, big);
        e.close_sorts();
        let a = e.add_op("a", vec![], small);
        let g = e.add_op_iter("g", vec![big], big);
        let f = e.add_op_ac("f", vec![big, big], big, None);
        e.add_op_decl(f, vec![small, small], small);
        e.reserve_identity(f, big);
        e.set_identity_term(
            f,
            crate::term::Term::Iter {
                symbol: g,
                count: Nat::from_u64(1_000_000),
                arg: Box::new(crate::term::Term::constant(a)),
            },
        );
        e.prepare_identities();

        let mut names = TestNames::default();
        let xname = names.code("X");
        let yname = names.code("Y");
        let zname = names.code("Z");
        let x = e.make_var(small, xname, 0);
        let y = e.make_var(big, yname, 1);
        let z = e.make_var(small, zname, 2);
        let gy = e.make_iter(g, 1, y);
        let lhs = e.make_acu(f, vec![(gy, 1), (z, 1)]);
        let specs = vec![
            VarSpec {
                sort: small,
                name: xname,
            },
            VarSpec {
                sort: big,
                name: yname,
            },
            VarSpec {
                sort: small,
                name: zname,
            },
        ];
        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let mut problem =
            UnifyProblem::new(&mut env, vec![(x, lhs)], specs, VariableFamily::Unify, "0");
        assert!(problem.problem_okay());
        let order = problem.original_variable_order().to_vec();
        let binding = problem.find_next(&mut env).expect("collapse unifier");
        let mut original = vec![None; 3];
        for (new_slot, old_slot) in order.into_iter().enumerate() {
            original[old_slot] = Some(binding[new_slot]);
        }

        let bx = original[0].expect("X binding");
        let by = original[1].expect("Y binding");
        let bz = original[2].expect("Z binding");
        assert!(
            env.e.deep_equal(bx, bz),
            "X and Z share the same Small variable"
        );
        assert_eq!(env.e.sort_of(bx), small);
        let expected_y = {
            let a = env.e.make_const(a);
            env.e.make_iter(g, 999_999, a)
        };
        assert!(env.e.deep_equal(by, expected_y), "Y --> g^999999(a)");
        assert!(
            problem.find_next(&mut env).is_none(),
            "only the sortable collapse remains"
        );
    }

    /// CUI normalization happens before `indexVariables`: a commutative node whose name-code order
    /// differs from parser encounter order must determine the visible substitution slots. This is
    /// the object-level `f(X, Y) =? f(U, V)` CU case with the standing-prelude name order
    /// `X < Y` and `V < U`; Maude therefore prints/binds the keys as `X, Y, V, U`.
    #[test]
    fn cui_normalization_defines_original_variable_slots() {
        let mut e = Engine::new();
        let foo = e.add_sort("Foo");
        e.close_sorts();
        let unit = e.add_op("e", vec![], foo);
        let f = e.add_op_cui("f", vec![foo, foo], foo, true, false, Some(unit));

        let mut names = TestNames::default();
        let xname = names.code("X");
        let yname = names.code("Y");
        let vname = names.code("V");
        let uname = names.code("U");
        let x = e.make_var(foo, xname, 0);
        let y = e.make_var(foo, yname, 1);
        let u = e.make_var(foo, uname, 2);
        let v = e.make_var(foo, vname, 3);
        let lhs = e.make_cui(f, x, y);
        let rhs = e.make_cui(f, u, v);
        let specs = vec![
            VarSpec {
                sort: foo,
                name: xname,
            },
            VarSpec {
                sort: foo,
                name: yname,
            },
            VarSpec {
                sort: foo,
                name: uname,
            },
            VarSpec {
                sort: foo,
                name: vname,
            },
        ];

        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let mut problem = UnifyProblem::new(
            &mut env,
            vec![(lhs, rhs)],
            specs,
            VariableFamily::Unify,
            "0",
        );
        assert_eq!(problem.original_variable_order(), &[0, 1, 3, 2]);
        assert_eq!(
            problem
                .var_specs
                .iter()
                .map(|spec| spec.unwrap().name)
                .collect::<Vec<_>>(),
            vec![xname, yname, vname, uname]
        );

        let first = problem.find_next(&mut env).expect("first CU unifier");
        let fresh_names: Vec<u32> = first
            .iter()
            .map(|&id| {
                as_var(env.e, id)
                    .expect("first CU unifier is variable-only")
                    .0
            })
            .collect();
        let hash1 = env.names.code("#1");
        let hash2 = env.names.code("#2");
        assert_eq!(fresh_names, vec![hash1, hash2, hash1, hash2]);
    }

    /// A noncommutative identity operator is represented by the CUI theory too, but its arguments
    /// remain positional: name-code order must not swap the rhs variables before indexing.
    #[test]
    fn noncommutative_identity_preserves_positional_variable_slots() {
        let mut e = Engine::new();
        let foo = e.add_sort("Foo");
        e.close_sorts();
        let unit = e.add_op("e", vec![], foo);
        let f = e.add_op_cui("f", vec![foo, foo], foo, false, false, Some(unit));

        let mut names = TestNames::default();
        let xname = names.code("X");
        let yname = names.code("Y");
        let vname = names.code("V");
        let uname = names.code("U");
        let x = e.make_var(foo, xname, 0);
        let y = e.make_var(foo, yname, 1);
        let u = e.make_var(foo, uname, 2);
        let v = e.make_var(foo, vname, 3);
        let lhs = e.make_cui(f, x, y);
        let rhs = e.make_cui(f, u, v);
        let specs = vec![
            VarSpec {
                sort: foo,
                name: xname,
            },
            VarSpec {
                sort: foo,
                name: yname,
            },
            VarSpec {
                sort: foo,
                name: uname,
            },
            VarSpec {
                sort: foo,
                name: vname,
            },
        ];

        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let problem = UnifyProblem::new(
            &mut env,
            vec![(lhs, rhs)],
            specs,
            VariableFamily::Unify,
            "0",
        );
        assert_eq!(problem.original_variable_order(), &[0, 1, 2, 3]);
    }

    #[test]
    fn ac_cross_sort_normalization_defines_slots_and_first_selection() {
        let mut e = Engine::new();
        let elt = e.add_sort("Elt");
        let set = e.add_sort("Set");
        e.add_subsort(elt, set);
        e.close_sorts();
        let f = e.add_op_ac("f", vec![set, set], set, None);

        let mut names = TestNames::default();
        let xname = names.code("X");
        let aname = names.code("A");
        let yname = names.code("Y");
        let bname = names.code("B");
        // Deliberately instantiate Set's VariableSymbol first.  Maude's bottom-up parser creates
        // Elt's symbol first for f(X, A), and normalization must recover A, X, B, Y slot order.
        let x = e.make_var(set, xname, 0);
        let a = e.make_var(elt, aname, 1);
        let y = e.make_var(set, yname, 2);
        let b = e.make_var(elt, bname, 3);
        let lhs = e.make_ac(f, vec![x, a]);
        let rhs = e.make_ac(f, vec![y, b]);
        let specs = vec![
            VarSpec {
                sort: set,
                name: xname,
            },
            VarSpec {
                sort: elt,
                name: aname,
            },
            VarSpec {
                sort: set,
                name: yname,
            },
            VarSpec {
                sort: elt,
                name: bname,
            },
        ];

        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let mut problem = UnifyProblem::new(
            &mut env,
            vec![(lhs, rhs)],
            specs,
            VariableFamily::Unify,
            "0",
        );
        assert_eq!(problem.original_variable_order(), &[1, 0, 3, 2]);

        let first = problem
            .find_next(&mut env)
            .expect("direct Elt/Set covering");
        let hash1 = env.names.code("#1");
        let hash2 = env.names.code("#2");
        assert_eq!(as_var(env.e, first[0]), Some((hash1, "Elt".to_string())));
        assert_eq!(as_var(env.e, first[1]), Some((hash2, "Set".to_string())));
        assert_eq!(as_var(env.e, first[2]), Some((hash1, "Elt".to_string())));
        assert_eq!(as_var(env.e, first[3]), Some((hash2, "Set".to_string())));
    }
}
