//! Reduced ordered binary decision diagram (ROBDD) reasoning for order-sorted unification.
//!
//! This module builds per-symbol sort functions, composes generalized sorts, constrains maximal sort
//! assignments, and enumerates satisfying assignments with `biodivine-lib-bdd`.
//!
//! Core operations:
//! - [`SortBdds::shift_block`] performs an order-preserving upward variable-block remap using
//!   `rename_variables`; its safety precondition requires the target block to sit above every
//!   variable in the input BDD's support.
//! - Downward remapping for maximality uses
//!   `exists B . (f ∧ (B ↔ B'))` through `binary_op_with_exists`.
//! - Operator composition substitutes functions sequentially; substituted functions never mention a
//!   pending scratch variable.
//! - Universal relation checks use the fused `Bdd::binary_op_with_for_all`.
//!
//! **Ownership and layout.** biodivine variable sets are fixed-size, so each unification problem owns a
//! `SortBdds` (relations plus lazy sort functions) sized after the driver has collected its free
//! variables. Rebuilding the relations affects only performance, not results: the `maximal` BDD contains
//! only real per-free-variable variables, and canonical ROBDDs make AllSat order layout-independent.
//! The variable layout is
//! `[scratch1: maxbits][scratch2: maxbits][domain: maxdom][real: real_capacity]`; `maxdom`, the widest
//! operator domain, is computed up front through `Signature::symbols_iter`.
//!
//! The unification driver walks each solved DAG to compute generalized sorts and collect free
//! variables, builds the per-problem maximality BDD, then owns [`AllSat`] while emitting maximal
//! order-sorted refinements. This module supplies [`SortBdds::make_variable_bdd`],
//! [`SortBdds::operator_compose`], [`SortBdds::apply_leq_relation`],
//! [`SortBdds::get_remapped_leq_relation`], [`SortBdds::make_index_vector`], and
//! [`SortBdds::maximal_from_unifier`] for that flow.

use crate::engine::Signature;
use crate::sort::{KindId, SortId};
use crate::symbol::SymbolId;
use biodivine_lib_bdd::{
    Bdd, BddPartialValuation, BddPointer, BddVariable, BddVariableSet, op_function,
};
use std::collections::HashMap;

/// Bits needed to index `nr_indices` values (`0..nr_indices`), with a minimum of one bit.
fn calculate_nr_bits(nr_indices: usize) -> u16 {
    let mut nr_bits = 1u16;
    let mut representable = 2usize;
    while representable < nr_indices {
        nr_bits += 1;
        representable <<= 1;
    }
    nr_bits
}

/// Precomputed per-kind BDD relations, indexed by [`KindId`] (position in the module's kind list).
struct KindBdds {
    /// Bit width of a sort index in this kind.
    bits: u16,
    /// `valid(s1) ∧ valid(s2) ∧ s1 > s2` with s1's block at scratch1 and s2's at scratch2 (the
    /// strict-subsort relation over local sort indices).
    gt: Bdd,
    /// Per local sort index `li`: `valid(x) ∧ x ≤ sort(li)` over scratch1.
    leq: Vec<Bdd>,
}

/// Sort relations and lazy operator sort functions sized for one unification problem.
pub(crate) struct SortBdds {
    universe: BddVariableSet,
    vars: Vec<BddVariable>,
    /// Widest sort-index bit count over all kinds — the scratch block size.
    maxbits: u16,
    /// First variable of the sort-function domain block.
    domain0: u16,
    /// First real (per-free-variable) variable.
    real0: u16,
    /// Per kind (by `KindId.index()`).
    kinds: Vec<KindBdds>,
    /// Lazy per-symbol sort function (`Vec<Bdd>` over the domain block), built on first use.
    sort_fns: HashMap<SymbolId, Vec<Bdd>>,
    /// Cache of remapped `≤` relations keyed by declared sort and first real bit.
    remapped_leq: HashMap<(SortId, u16), Bdd>,
    /// Cache of remapped gt relations (second argument shifted to a real block), keyed by
    /// (kind index, first real bit).
    remapped_gt: HashMap<(usize, u16), Bdd>,
}

impl SortBdds {
    /// Build the per-kind gt/leq relations and reserve `real_capacity` real variables (the driver
    /// passes the total bit width of the problem's free variables). Sort functions are built lazily.
    pub(crate) fn new(sig: &Signature, real_capacity: u16) -> SortBdds {
        let sorts = sig.sorts();
        let n_kinds = sorts.num_kinds();

        // Per-kind bit widths and local leq sets (ascending local indices, subsorts-first order).
        let mut bits = vec![0u16; n_kinds];
        let mut leq_local: Vec<Vec<Vec<u32>>> = vec![Vec::new(); n_kinds];
        for kid in sorts.kinds() {
            let order = &sorts.kind(kid).index_order;
            let n = order.len();
            bits[kid.index()] = calculate_nr_bits(n);
            let per_sort: Vec<Vec<u32>> = order
                .iter()
                .map(|&sort_li| {
                    // leq[li] = ascending local indices lj with sort(lj) <= sort(li). Index order is
                    // supersorts-first, so sort(lj) <= sort(li) implies lj >= li; ascending lj is natural.
                    (0..n as u32)
                        .filter(|&lj| sorts.leq(order[lj as usize], sort_li))
                        .collect()
                })
                .collect();
            leq_local[kid.index()] = per_sort;
        }

        let maxbits = bits.iter().copied().max().unwrap_or(1);
        // Widest operator domain (Σ argument-kind bits) over all symbols — the domain block width.
        let maxdom = sig
            .symbols_iter()
            .map(|(_, sym)| {
                sym.decls[0]
                    .domain
                    .iter()
                    .map(|&d| bits[sorts.kind_of(d).index()])
                    .sum::<u16>()
            })
            .max()
            .unwrap_or(0);

        let domain0 = 2 * maxbits;
        let real0 = domain0 + maxdom;
        let universe = BddVariableSet::new_anonymous(real0 + real_capacity);
        let all_vars = universe.variables();

        let mut sb = SortBdds {
            universe,
            vars: all_vars,
            maxbits,
            domain0,
            real0,
            kinds: Vec::with_capacity(n_kinds),
            sort_fns: HashMap::new(),
            remapped_leq: HashMap::new(),
            remapped_gt: HashMap::new(),
        };

        // Build gt (arg1 scratch1, arg2 scratch2) and per-sort leq (at scratch1) for each kind.
        for kid in sorts.kinds() {
            let ki = kid.index();
            let kbits = bits[ki];
            let gt = sb.gt_relation(&leq_local[ki], kbits);
            let leq: Vec<Bdd> = (0..leq_local[ki].len())
                .map(|li| sb.leq_at(&leq_local[ki], kbits, li as u32, 0))
                .collect();
            sb.kinds.push(KindBdds {
                bits: kbits,
                gt,
                leq,
            });
        }
        sb
    }

    /// The bit width of a sort index in `kind`.
    #[cfg(test)]
    pub(crate) fn nr_variables(&self, kind: KindId) -> u16 {
        self.kinds[kind.index()].bits
    }

    /// The first real variable (AllSat runs over `[real0, ..]`).
    pub(crate) fn real0(&self) -> u16 {
        self.real0
    }

    /// A `true`/`false` BDD in this instance's universe (the driver's unifier seed / sort-fn zero).
    pub(crate) fn mk_true(&self) -> Bdd {
        self.universe.mk_true()
    }
    pub(crate) fn mk_false(&self) -> Bdd {
        self.universe.mk_false()
    }

    fn set_index_bits(&self, cube: &mut BddPartialValuation, first: u16, bits: u16, index: u32) {
        for k in 0..bits {
            cube.set_value(self.vars[(first + k) as usize], index >> k & 1 == 1);
        }
    }

    /// A constant-bit BDD vector encoding a local sort index.
    pub(crate) fn make_index_vector(&self, bits: u16, index: u32) -> Vec<Bdd> {
        (0..bits)
            .map(|k| {
                if index >> k & 1 == 1 {
                    self.universe.mk_true()
                } else {
                    self.universe.mk_false()
                }
            })
            .collect()
    }

    /// `valid(x) ∧ x ≤ sort(li)` with `x` at variables `first..first+bits`.
    fn leq_at(&self, leq_local: &[Vec<u32>], bits: u16, sort_li: u32, first: u16) -> Bdd {
        let cubes: Vec<BddPartialValuation> = leq_local[sort_li as usize]
            .iter()
            .map(|&t| {
                let mut cube = BddPartialValuation::empty();
                self.set_index_bits(&mut cube, first, bits, t);
                cube
            })
            .collect();
        self.universe.mk_dnf(&cubes)
    }

    /// The gt relation with arg1 at scratch1 (position 0) and arg2 at scratch2 (position maxbits).
    fn gt_relation(&self, leq_local: &[Vec<u32>], bits: u16) -> Bdd {
        let n = leq_local.len() as u32;
        let mut cubes: Vec<BddPartialValuation> = Vec::new();
        for s1 in 0..n {
            for &s2 in &leq_local[s1 as usize] {
                if s2 != s1 {
                    // s2 <= s1 and s2 != s1  ⇒  s1 > s2.
                    let mut cube = BddPartialValuation::empty();
                    self.set_index_bits(&mut cube, 0, bits, s1);
                    self.set_index_bits(&mut cube, self.maxbits, bits, s2);
                    cubes.push(cube);
                }
            }
        }
        self.universe.mk_dnf(&cubes)
    }

    /// Shift one BDD variable block upward with an order-preserving relabel. Real blocks sit above
    /// scratch and domain blocks, so this preserves variable order and canonical form.
    #[allow(unsafe_code)]
    fn shift_block(&self, b: &Bdd, from: u16, bits: u16, to: u16) -> Bdd {
        let mut b = b.clone();
        let map: HashMap<BddVariable, BddVariable> = (0..bits)
            .map(|j| (self.vars[(from + j) as usize], self.vars[(to + j) as usize]))
            .collect();
        // SAFETY: `to` is above the BDD support, so this block relabel preserves variable order.
        unsafe { b.rename_variables(&map) };
        b
    }

    /// Build or reuse `valid(x) ∧ x ≤ sort` over a free variable's real block.
    pub(crate) fn get_remapped_leq_relation(
        &mut self,
        sig: &Signature,
        sort: SortId,
        first_real: u16,
    ) -> Bdd {
        if let Some(b) = self.remapped_leq.get(&(sort, first_real)) {
            return b.clone();
        }
        let kind = sig.sorts().kind_of(sort);
        let li = sig.sorts().component_index(sort);
        let bits = self.kinds[kind.index()].bits;
        let base = self.kinds[kind.index()].leq[li as usize].clone();
        let remapped = self.shift_block(&base, 0, bits, first_real);
        self.remapped_leq
            .insert((sort, first_real), remapped.clone());
        remapped
    }

    /// The gt relation with its SECOND argument shifted to a real block (first stays at scratch1) —
    /// the maximality step's `gt(Y, X_fv)` with the candidate `Y` in scratch1 and the free variable
    /// `X_fv` at its real block. Cached per (kind, first real).
    fn get_remapped_gt(&mut self, kind: KindId, first_real: u16) -> Bdd {
        if let Some(b) = self.remapped_gt.get(&(kind.index(), first_real)) {
            return b.clone();
        }
        let bits = self.kinds[kind.index()].bits;
        let base = self.kinds[kind.index()].gt.clone();
        let remapped = self.shift_block(&base, self.maxbits, bits, first_real);
        self.remapped_gt
            .insert((kind.index(), first_real), remapped.clone());
        remapped
    }

    /// Substitute `args` into `leq[kind][li]`, whose variables occupy the first scratch block.
    /// Sequential substitution is sound because `args` never mention that block.
    pub(crate) fn apply_leq_relation(&self, kind: KindId, li: u32, args: &[Bdd]) -> Bdd {
        let mut b = self.kinds[kind.index()].leq[li as usize].clone();
        for (i, g) in args.iter().enumerate() {
            b = b.substitute(self.vars[i], g);
        }
        b
    }

    /// Lazily build the result-sort function for `symbol` as BDDs over its domain-sort indices.
    pub(crate) fn sort_function(&mut self, sig: &Signature, symbol: SymbolId) -> &[Bdd] {
        if !self.sort_fns.contains_key(&symbol) {
            let f = self.build_sort_fn(sig, symbol);
            self.sort_fns.insert(symbol, f);
        }
        &self.sort_fns[&symbol]
    }

    fn build_sort_fn(&self, sig: &Signature, symbol: SymbolId) -> Vec<Bdd> {
        let sorts = sig.sorts();
        let sym = sig.symbol(symbol);
        let range_kind = sorts.kind_of(sym.decls[0].range);
        let rbits = self.kinds[range_kind.index()].bits;
        let arity = sym.decls[0].domain.len();

        if arity == 0 {
            // A constant selects its least non-error declared range through a domain-free fold.
            let mut least = sorts.error_sort(range_kind);
            for decl in sym.decls.iter().rev() {
                if !sorts.leq(least, decl.range) {
                    least = decl.range;
                }
            }
            return self.make_index_vector(rbits, sorts.component_index(least));
        }

        // Per-argument domain kinds (all declarations share kinds per position).
        let arg_kinds: Vec<KindId> = sym.decls[0]
            .domain
            .iter()
            .map(|&d| sorts.kind_of(d))
            .collect();
        // Start with the error sort (local index 0) as the constant result function.
        let mut f = self.make_index_vector(rbits, 0);
        for decl in sym.decls.iter().rev() {
            // All arguments ≤ the declaration's domain sorts.
            let mut cond = self.universe.mk_true();
            let mut pos = self.domain0;
            for (j, &d) in decl.domain.iter().enumerate() {
                let kbits = self.kinds[arg_kinds[j].index()].bits;
                let leq = self.leq_at_domain(arg_kinds[j], sorts.component_index(d), pos);
                cond = cond.and(&leq);
                pos += kbits;
            }
            // ... and the currently computed sort is NOT ≤ this range sort.
            let cur_leq_range =
                self.apply_leq_relation(range_kind, sorts.component_index(decl.range), &f);
            cond = cond.and_not(&cur_leq_range);
            let range_bits = self.make_index_vector(rbits, sorts.component_index(decl.range));
            for k in 0..rbits as usize {
                f[k] = Bdd::if_then_else(&cond, &range_bits[k], &f[k]);
            }
        }
        f
    }

    /// `valid(x) ∧ x ≤ sort(li)` for `kind`, with `x` at a domain-block position `first`.
    fn leq_at_domain(&self, kind: KindId, li: u32, first: u16) -> Bdd {
        // The stored leq[kind][li] is over scratch1 (position 0); shift it to `first`.
        let bits = self.kinds[kind.index()].bits;
        self.shift_block(&self.kinds[kind.index()].leq[li as usize], 0, bits, first)
    }

    /// Compose an operator's sort function with argument bit vectors over real variables by
    /// substituting each domain-block variable with its corresponding input bit.
    pub(crate) fn operator_compose(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        input_bits: &[Bdd],
    ) -> Vec<Bdd> {
        let domain0 = self.domain0 as usize;
        // Clone the sort function out of the cache to release the borrow before substituting.
        let f: Vec<Bdd> = self.sort_function(sig, symbol).to_vec();
        f.iter()
            .map(|b| {
                let mut b = b.clone();
                for (i, g) in input_bits.iter().enumerate() {
                    b = b.substitute(self.vars[domain0 + i], g);
                }
                b
            })
            .collect()
    }

    /// The literal bit vector for a free variable's real block.
    pub(crate) fn make_variable_bdd(&self, first_real: u16, bits: u16) -> Vec<Bdd> {
        (0..bits)
            .map(|k| {
                self.universe
                    .mk_literal(self.vars[(first_real + k) as usize], true)
            })
            .collect()
    }

    /// Restrict `unifier` to assignments where no free variable's sort can be raised through the
    /// strict-subsort relation while preserving satisfiability. `free_blocks` lists each free
    /// variable's `(kind, first_real_bit)`.
    pub(crate) fn maximal_from_unifier(
        &mut self,
        unifier: &Bdd,
        free_blocks: &[(KindId, u16)],
    ) -> Bdd {
        let scratch1: Vec<BddVariable> = (0..self.maxbits as usize).map(|i| self.vars[i]).collect();
        let mut maximal = unifier.clone();
        for &(kind, first) in free_blocks {
            let bits = self.kinds[kind.index()].bits as usize;
            // gt with the free variable's block at `first`, the "greater candidate" Y at scratch1.
            let gt = self.get_remapped_gt(kind, first);
            // unifier with this variable's block functionally renamed to scratch1:
            //   exists block . (unifier ∧ (block ↔ scratch1))
            let mut iff_conj = self.universe.mk_true();
            let mut block_vars = Vec::with_capacity(bits);
            for (j, &scratch) in scratch1.iter().take(bits).enumerate() {
                let bv = self.vars[first as usize + j];
                block_vars.push(bv);
                let l = self.universe.mk_literal(bv, true);
                let r = self.universe.mk_literal(scratch, true);
                iff_conj = iff_conj.and(&l.iff(&r));
            }
            let renamed =
                Bdd::binary_op_with_exists(unifier, &iff_conj, op_function::and, &block_vars);
            // forall Y in scratch1 . not( gt(Y, X_fv) ∧ unifier[X_fv := Y] )
            maximal = maximal.and(&Bdd::binary_op_with_for_all(
                &gt,
                &renamed,
                nand_op,
                &scratch1[..bits],
            ));
        }
        maximal
    }

    /// Test helper: the BDD's satisfying-count over `[real0, last_real]` (its total cardinality
    /// shifted down by the variables outside that range — the `maximal` BDD is real-only, so this
    /// equals the number of enumerated assignments).
    #[cfg(test)]
    fn cardinality_over_real_range(&self, bdd: &Bdd, last_real: u16) -> num_bigint::BigInt {
        let range = (last_real - self.real0 + 1) as usize;
        let outside = self.universe.num_vars() as usize - range;
        bdd.exact_cardinality() >> outside
    }
}

/// Three-valued NAND used by the universal maximality check.
fn nand_op(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), _) | (_, Some(false)) => Some(true),
        (Some(true), Some(true)) => Some(false),
        _ => None,
    }
}

// AllSat

const UNDEFINED: i8 = -1;

/// Enumerate satisfying assignments over the selected variable range using low-branch-first DFS,
/// ordered don't-cares, binary expansion, and stack backtracking. This order determines unifier order.
pub(crate) struct AllSat {
    formula: Bdd,
    first_variable: usize,
    last_variable: usize,
    node_stack: Vec<BddPointer>,
    dont_care_set: Vec<usize>,
    assignment: Vec<i8>,
    first_assignment: bool,
}

impl AllSat {
    /// Owns `formula` so a caller (the unification driver) can hold the enumerator across the
    /// solved form's lifetime without a self-referential borrow.
    pub(crate) fn new(formula: Bdd, first_variable: u16, last_variable: u16) -> AllSat {
        AllSat {
            formula,
            first_variable: first_variable as usize,
            last_variable: last_variable as usize,
            node_stack: Vec::new(),
            dont_care_set: Vec::new(),
            assignment: Vec::new(),
            first_assignment: true,
        }
    }

    /// Advance to the next satisfying assignment; `false` when exhausted. After it returns `true`,
    /// [`assignment`](Self::assignment) holds concrete 0/1 values for every variable in range.
    pub(crate) fn next_assignment(&mut self) -> bool {
        if self.first_assignment {
            if self.formula.is_false() {
                return false;
            }
            self.assignment = vec![UNDEFINED; self.last_variable + 1];
            self.forward(self.formula.root_pointer());
            self.first_assignment = false;
            return true;
        }
        // Try another way of assigning the don't-care variables (binary counting).
        let nr_dont_cares = self.dont_care_set.len();
        for i in (0..nr_dont_cares).rev() {
            let var = self.dont_care_set[i];
            if self.assignment[var] == 0 {
                self.assignment[var] = 1;
                for j in i + 1..nr_dont_cares {
                    self.assignment[self.dont_care_set[j]] = 0;
                }
                return true;
            }
        }
        for &dc in &self.dont_care_set {
            self.assignment[dc] = UNDEFINED;
        }
        self.dont_care_set.clear();
        // Try another route to true through the BDD.
        let node_depth = self.node_stack.len();
        for i in (0..node_depth).rev() {
            let b = self.node_stack[i];
            let var = self.formula.var_of(b).to_index();
            if self.assignment[var] == 0 {
                let n = self.formula.high_link_of(b);
                if !n.is_zero() {
                    self.assignment[var] = 1;
                    self.node_stack.truncate(i + 1);
                    self.forward(n);
                    return true;
                }
            }
            self.assignment[var] = UNDEFINED;
        }
        false
    }

    /// The current assignment (index 0 = variable 0; only `[first_variable, last_variable]` are
    /// meaningful): 0 or 1 per variable after a successful [`next_assignment`](Self::next_assignment).
    pub(crate) fn assignment(&self) -> &[i8] {
        &self.assignment
    }

    fn forward(&mut self, mut b: BddPointer) {
        assert!(!b.is_zero(), "false BDD");
        // There is at least one path to true from b; take the least (low-branch-first).
        while !b.is_one() {
            self.node_stack.push(b);
            let var = self.formula.var_of(b).to_index();
            let low = self.formula.low_link_of(b);
            if low.is_zero() {
                self.assignment[var] = 1;
                b = self.formula.high_link_of(b);
            } else {
                self.assignment[var] = 0;
                b = low;
            }
        }
        // Variables of interest not assigned on this path are don't cares.
        for i in self.first_variable..=self.last_variable {
            if self.assignment[i] == UNDEFINED {
                self.assignment[i] = 0;
                self.dont_care_set.push(i);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;
    use crate::sort::SortId;

    /// Build the test number tower through the engine:
    /// `[K] Rat Int NzRat Nat NzInt Zero NzNat` with `+` subsort-overloaded, and return the engine
    /// plus the sort ids and the `+` symbol.
    fn number_tower() -> (Engine, Vec<SortId>, SymbolId) {
        let mut e = Engine::new();
        let rat = e.add_sort("Rat");
        let int = e.add_sort("Int");
        let nzrat = e.add_sort("NzRat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(int, rat);
        e.add_subsort(nzrat, rat);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.add_subsort(nzint, nzrat);
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.close_sorts();
        // Subsort overloads are declared most-specific first.
        let plus = e.add_op("+", vec![nznat, nznat], nznat);
        e.add_op_decl(plus, vec![nat, nat], nat);
        e.add_op_decl(plus, vec![int, int], int);
        e.add_op_decl(plus, vec![rat, rat], rat);
        (e, vec![rat, int, nzrat, nat, nzint, zero, nznat], plus)
    }

    /// The BDD sort function returns [`Signature::compute_sort`] for every argument-sort
    /// combination.
    #[test]
    fn sort_function_matches_compute_sort() {
        let (e, _sorts, plus) = number_tower();
        let sig = e.signature();
        let mut sb = SortBdds::new(sig, 32);
        let kind = sig.sorts().kind_of(sig.symbol(plus).decls[0].range);
        let bits = sb.nr_variables(kind);

        let order = sig.sorts().kind(kind).index_order.clone();
        for &a in &order {
            for &b in &order {
                let inputs: Vec<Bdd> = {
                    let mut v = sb.make_index_vector(bits, sig.sorts().component_index(a));
                    v.extend(sb.make_index_vector(bits, sig.sorts().component_index(b)));
                    v
                };
                let composed = sb.operator_compose(sig, plus, &inputs);
                let mut actual_local = 0u32;
                for (k, bit) in composed.iter().enumerate() {
                    assert!(bit.is_true() || bit.is_false(), "non-constant sort-fn bit");
                    if bit.is_true() {
                        actual_local |= 1 << k;
                    }
                }
                let actual = sig.sorts().kind(kind).index_order[actual_local as usize];
                let expected = sig.compute_sort(plus, &[a, b]);
                assert_eq!(
                    sig.sorts().name(actual),
                    sig.sorts().name(expected),
                    "sort fn vs compute_sort for + on {}, {}",
                    sig.sorts().name(a),
                    sig.sorts().name(b),
                );
            }
        }
    }

    /// A non-lattice sort shape: `A B < S1`, `A B < S2`, `S1 S2 < T`. A fresh variable
    /// constrained by `≤ S1 ∧ ≤ S2` has no greatest lower bound: A and B are both maximal lower
    /// bounds. The unifier-to-maximal-to-AllSat flow must enumerate exactly those two assignments.
    #[test]
    fn maximal_enumeration_antichain() {
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
        let sig = e.signature();
        let kind = sig.sorts().kind_of(t);

        let mut sb = SortBdds::new(sig, 64);
        let vbits = sb.nr_variables(kind);
        let real0 = sb.real0();
        let block = (kind, real0);

        // unifier = (x ≤ S1) ∧ (x ≤ S2) at the fresh variable's block.
        let unifier = {
            let r1 = sb.get_remapped_leq_relation(sig, s1, block.1);
            let r2 = sb.get_remapped_leq_relation(sig, s2, block.1);
            r1.and(&r2)
        };
        let maximal = sb.maximal_from_unifier(&unifier, &[block]);

        let last_real = real0 + vbits - 1;
        let mut got: Vec<String> = Vec::new();
        let mut all = AllSat::new(maximal.clone(), real0, last_real);
        while all.next_assignment() {
            let asg = all.assignment();
            let mut li = 0u32;
            for k in 0..vbits {
                if asg[(real0 + k) as usize] == 1 {
                    li |= 1 << k;
                }
            }
            got.push(
                sig.sorts()
                    .name(sig.sorts().kind(kind).index_order[li as usize])
                    .to_string(),
            );
        }
        let mut got_sorted = got.clone();
        got_sorted.sort();

        // Direct: valid iff ≤ S1 and ≤ S2; maximal iff no other valid sort strictly above it.
        let order = &sig.sorts().kind(kind).index_order;
        let valid = |li: usize| sig.sorts().leq(order[li], s1) && sig.sorts().leq(order[li], s2);
        let mut expected: Vec<String> = (0..order.len())
            .filter(|&li| {
                valid(li)
                    && !(0..order.len())
                        .any(|lj| lj != li && valid(lj) && sig.sorts().leq(order[li], order[lj]))
            })
            .map(|li| sig.sorts().name(order[li]).to_string())
            .collect();
        expected.sort();
        assert_eq!(got_sorted, expected, "maximal antichain set mismatch");
        assert_eq!(got.len(), 2, "two maximal lower bounds: A and B");

        let count = sb.cardinality_over_real_range(&maximal, last_real);
        assert_eq!(
            count,
            num_bigint::BigInt::from(got.len()),
            "AllSat count vs cardinality"
        );
    }

    /// Order-preserving block renaming preserves the relation's canonical BDD representation.
    #[test]
    fn rename_remap_is_canonical() {
        let (e, sorts, _) = number_tower();
        let sig = e.signature();
        let mut sb = SortBdds::new(sig, 32);
        let nat = sorts[3];
        let kind = sig.sorts().kind_of(nat);
        let bits = sb.nr_variables(kind);
        let first = sb.real0();
        let remapped = sb.get_remapped_leq_relation(sig, nat, first);
        // Direct build at `first`.
        let order = &sig.sorts().kind(kind).index_order;
        let cubes: Vec<BddPartialValuation> = (0..order.len() as u32)
            .filter(|&lj| sig.sorts().leq(order[lj as usize], nat))
            .map(|lj| {
                let mut cube = BddPartialValuation::empty();
                for k in 0..bits {
                    cube.set_value(sb.vars[(first + k) as usize], lj >> k & 1 == 1);
                }
                cube
            })
            .collect();
        let direct = sb.universe.mk_dnf(&cubes);
        assert_eq!(remapped, direct, "shift_block diverges from direct build");
    }

    /// AllSat expands a don't-care variable into both concrete assignments, low-first.
    #[test]
    fn allsat_dont_care_low_first() {
        let universe = BddVariableSet::new_anonymous(1);
        let t = universe.mk_true();
        let mut all = AllSat::new(t.clone(), 0, 0);
        let mut seq = Vec::new();
        while all.next_assignment() {
            seq.push(all.assignment()[0]);
        }
        assert_eq!(
            seq,
            vec![0, 1],
            "don't-care expands low (0) first, then high (1)"
        );
    }
}
