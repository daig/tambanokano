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
    compute_solved_form, instantiate, is_ground, screen_for_unification, PendingStack, Screen,
    UnifyContext, UnifyEnv,
};
use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::fresh::{FreshVariableGenerator, VariableFamily};
use crate::num::Nat;
use crate::sort::{KindId, SortId};
use crate::sort_bdds::{AllSat, SortBdds};
use biodivine_lib_bdd::Bdd;

/// The declared sort and interned base-name code of one original problem variable, in slot order
/// (first-encounter order across `lhs[0], rhs[0], lhs[1], …` — the observable order).
#[derive(Clone, Copy)]
pub struct VarSpec {
    pub sort: SortId,
    pub name: u32,
}

/// A resumable order-sorted unification problem.
pub struct UnifyProblem {
    equations: Vec<(DagId, DagId)>,
    n_original: usize,
    var_specs: Vec<VarSpec>,
    family: VariableFamily,
    /// Fresh-variable base number (the `metaUnify` counter; 0 for the object-level command). A
    /// `Nat` internally (Maude's is a bignum), constructed from the `u64` API parameter.
    base: Nat,
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
        base: u64,
    ) -> UnifyProblem {
        let n_original = var_specs.len();
        let base = Nat::from_u64(base);
        let mut prob = UnifyProblem {
            equations,
            n_original,
            var_specs,
            family,
            base: base.clone(),
            ctx: UnifyContext::with_base(n_original, family, base),
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

    /// Whether the problem passed screening (implemented theories only). When `false` the caller
    /// prints only the (stripped) warning — no `Decision time`, no unifier lines.
    pub fn problem_okay(&self) -> bool {
        self.problem_okay
    }

    /// Whether any theory flagged possibly-incomplete unification (the A/AU depth bound).
    pub fn is_incomplete(&self) -> bool {
        self.pending.is_incomplete()
    }

    /// The number of free variables in the current unifier (for the `irredundant` filter later).
    pub fn nr_free_variables(&self) -> usize {
        self.order_sorted.as_ref().map_or(0, |os| os.free.len())
    }

    /// The next unifier as the value of each original variable (slot order), or `None` when
    /// exhausted. Mirror of `findNextUnifier`.
    pub fn find_next(&mut self, env: &mut UnifyEnv) -> Option<Vec<DagId>> {
        if !self.viable || !self.problem_okay {
            return None;
        }
        let mut first = self.order_sorted.is_none();
        if !first {
            if self.order_sorted.as_mut().unwrap().all_sat.next_assignment() {
                return Some(self.bind_free_variables(env));
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
        self.order_sorted.as_mut().unwrap().all_sat.next_assignment(); // can't fail
        Some(self.bind_free_variables(env))
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
                    self.var_specs[slot].sort
                } else {
                    self.ctx.fresh_variable_sort(slot)
                };
                let kind = sorts.kind_of(sort);
                let bits = calc_bits(sorts.kind(kind).index_order.len());
                total_bits += bits;
                raws.push(Raw { slot, sort, kind, bits });
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
        // original variables: bound ⇒ generalized-sort ≤ declared sort; free ⇒ ≤ declared sort.
        for i in 0..self.n_original {
            let sort = self.var_specs[i].sort;
            let kind = sig.sorts().kind_of(sort);
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

        let free_blocks: Vec<(KindId, u16)> =
            raws.iter().map(|r| (r.kind, real_to_bdd[r.slot].unwrap())).collect();
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
                FreeVar { slot: r.slot, first_real: real_to_bdd[r.slot].unwrap(), kind: r.kind, name }
            })
            .collect();

        self.order_sorted = Some(OrderSorted { all_sat, template, free });
    }

    /// `bindFreeVariables`: decode each free variable's assigned sort from the current AllSat
    /// assignment, build the `#k` variable of that sort, and instantiate the bound original slots.
    fn bind_free_variables(&mut self, env: &mut UnifyEnv) -> Vec<DagId> {
        let os = self.order_sorted.as_ref().unwrap();
        let asg: Vec<i8> = os.all_sat.assignment().to_vec();
        let mut subst = os.template.clone();
        let free = os.free.clone();

        // Pass 1 (immutable sorts): decode each free variable's assigned sort.
        let decoded: Vec<(usize, SortId, u32)> = {
            let sorts = env.e.signature().sorts();
            free.iter()
                .map(|fv| {
                    let order = &sorts.kind(fv.kind).index_order;
                    let bits = calc_bits(order.len());
                    let mut local = 0u32;
                    for k in 0..bits {
                        if asg[(fv.first_real + k) as usize] == 1 {
                            local |= 1 << k;
                        }
                    }
                    (fv.slot, order[local as usize], fv.name)
                })
                .collect()
        };
        // Pass 2 (mutable engine): build the `#k` variable of each assigned sort.
        for (slot, new_sort, name) in decoded {
            subst[slot] = Some(env.e.make_var(new_sort, name, slot as u32));
        }

        // Instantiate the bound original slots (free originals already hold their `#k` variable).
        let free_slots: Vec<usize> = free.iter().map(|f| f.slot).collect();
        for i in 0..self.n_original {
            if free_slots.contains(&i) {
                continue;
            }
            if let Some(v) = subst[i] {
                let d = instantiate(env.e, &subst, v);
                if let Some(d) = d {
                    subst[i] = Some(d);
                }
            }
        }
        (0..self.n_original).map(|i| subst[i].expect("original slot bound")).collect()
    }

    /// GC roots: the original equations, the context, and the pending stack. The caller roots these
    /// while a problem is live (unification builds many transient nodes).
    pub fn gc_roots(&self) -> Vec<DagId> {
        let mut roots: Vec<DagId> =
            self.equations.iter().flat_map(|&(l, r)| [l, r]).collect();
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
            equal = equal.and(if in_idx & 1 == 1 { &input[j] } else { &negated[j] });
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
            NodeTerm::Var { name, .. } => {
                Some((*name, e.sorts().name(e.sort_of(id)).to_string()))
            }
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
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let xname = env.names.code("X");
        let yname = env.names.code("Y");
        let x = env.e.make_var(s1, xname, 0);
        let y = env.e.make_var(s2, yname, 1);
        let specs = vec![VarSpec { sort: s1, name: xname }, VarSpec { sort: s2, name: yname }];

        let mut prob =
            UnifyProblem::new(&mut env, vec![(x, y)], specs, VariableFamily::Unify, 0);
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
        let mut env = UnifyEnv { e: &mut e, names: &mut names };

        let z1 = env.e.make_const(zero);
        let z2 = env.e.make_const(zero);
        let mut ok =
            UnifyProblem::new(&mut env, vec![(z1, z2)], vec![], VariableFamily::Unify, 0);
        let mut n = 0;
        while let Some(b) = ok.find_next(&mut env) {
            assert!(b.is_empty());
            n += 1;
        }
        assert_eq!(n, 1, "0 =? 0 has exactly one (empty) unifier");

        let o = env.e.make_const(one);
        let z = env.e.make_const(zero);
        let mut clash =
            UnifyProblem::new(&mut env, vec![(o, z)], vec![], VariableFamily::Unify, 0);
        assert!(clash.find_next(&mut env).is_none(), "1 =? 0 has no unifier");
    }
}
