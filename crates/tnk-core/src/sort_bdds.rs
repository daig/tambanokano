//! Order-sorted unification's **sort-solving BDDs**: Maude's `SortBdds` + `AllSat` on
//! `biodivine-lib-bdd` (decision **D6**; S0 spike GO — `docs/migration/reports/S0-bdd-spike.md`).
//!
//! What is ported, and from where:
//! - [`SortBdds`]: `Core/sortBdds.{hh,cc}` — per-kind sort-index bit encodings, the per-kind `gt`
//!   relation (`valid(s1) ∧ valid(s2) ∧ s1 > s2`), the per-sort `leq` relations
//!   (`valid(x) ∧ x <= s`), index/variable bit-vectors, `applyLeqRelation`,
//!   `getRemappedLeqRelation`, `operatorCompose`, and the lazy per-symbol sort-function cache.
//! - The per-symbol **sort functions**: `Core/sortTable.cc` `linearComputeSortFunctionBdds`
//!   (sortTable.cc:459-508). Maude computes *both* the recursive (sort-diagram) and the linear
//!   version on every symbol, uses the recursive result, and debug-compares them
//!   (`computeSortFunctionBdds`, sortTable.cc:392-437, a `DebugAdvisory` on mismatch). ROBDDs are
//!   canonical — same boolean function, same variable order ⇒ identical BDD — so building the
//!   linear one alone is behaviorally identical; the S1 oracle fixtures are the empirical check.
//! - The **maximality** step of `UnificationProblem::findOrderSortedUnifiers`
//!   (`Higher/unificationProblem.cc:305-476`): [`SortBdds::gt_relation_remapped`] +
//!   [`SortBdds::maximal_from_unifier`].
//! - [`AllSat`]: `Utility/allSat.{hh,cc}` — a line-for-line port of the enumeration walk over
//!   biodivine's node representation (low-branch-first DFS, don't-care set in variable-index
//!   order, binary counting over don't-cares, node-stack backtrack). The walk order is
//!   **load-bearing**: it fixes the observable unifier enumeration order.
//!
//! # Deliberate deviations from the reference (all result-invisible)
//!
//! - **Per-problem instance.** Maude keeps one `SortBdds` per module (BuDDy is a global manager,
//!   so caches must be shared). Here a `SortBdds` is built per unification problem: biodivine is
//!   manager-less, and relation/sort-function construction is microseconds at realistic scale
//!   (S0 report §4-5). Pure perf structure — nothing about the cache lifetime is observable.
//! - **Variable layout** `[scratch1: maxbits][scratch2: maxbits][real: real_capacity]`
//!   `[domain: domain_capacity]`. Maude overlays everything low (its real variables start at
//!   `maxNrVariables`, on top of the gt second-argument block, and sort-function domains start at
//!   variable 0); the spike used `[scratch1][scratch2][domain][real]`. The layout is invisible in
//!   results because every *answer* BDD (the `maximal` unifier constraint) contains only the real
//!   variables — scratch and domain are always substituted or quantified away — and the real
//!   blocks are allocated in the same ascending order as Maude's, so the canonical BDD over them,
//!   and hence the `AllSat` walk, is layout-independent (S0 report §3). The domain region sits at
//!   the **top** (unlike the spike) because its needed width — max over symbols of Σ per-argument
//!   kind bits — is unknowable at construction (`Signature` has no symbol iteration; sort
//!   functions are lazy) and must grow on demand: at the top it grows by *appending* variables, so
//!   every existing variable index — including the real blocks the driver holds positions for —
//!   stays put under both [`ensure_real_capacity`](SortBdds::ensure_real_capacity) and domain
//!   growth.
//! - **`bdd_replace`/`bdd_veccompose`/`bdd_appall` replacements** as validated by the spike
//!   (S0 report §2): upward block remaps are an order-preserving in-place relabel
//!   ([`shift_block`](SortBdds::shift_block), the module's one `unsafe` seam); the one downward
//!   remap (maximality) is the functional `exists B . (f ∧ (B ↔ B'))` via a fused
//!   `binary_op_with_exists`; `veccompose` is a sequential `substitute` chain, sound because the
//!   substituted-in functions never mention a pending substitution variable (the regions are
//!   disjoint); `bdd_appall(_, _, nand, cube)` is `binary_op_with_for_all(_, _, nand, vars)`.
//!
//! # Driver protocol (the UnificationProblem driver — a later task — must follow this)
//!
//! Growing either region rebuilds the universe; internal caches are relabeled consistently, but a
//! `Bdd` held *outside* this struct keeps its old variable count and biodivine **panics** on any
//! later mixed-width operation (fail-loud, never silent corruption). So, per problem: construct;
//! allocate free-variable blocks from [`first_available_variable`](SortBdds::first_available_variable)
//! and call [`ensure_real_capacity`](SortBdds::ensure_real_capacity); prefetch
//! [`sort_function`](SortBdds::sort_function) for every symbol occurring in bound terms (domain
//! growth happens there); only then start building and holding constraint BDDs.
//!
//! # findOrderSortedUnifiers coverage map (unificationProblem.cc:305-476)
//!
//! | reference step | primitive here |
//! |---|---|
//! | `setNrVariables(nextBddVariable)` (:345) | `ensure_real_capacity` |
//! | free-variable `getRemappedLeqRelation(sort, realToBdd[i])` (:355, :388) | `get_remapped_leq_relation` |
//! | bound-variable `computeGeneralizedSort` per-node ops (:379) | `make_variable_bdd` (leaves), `operator_compose` (applications) |
//! | bound-variable `applyLeqRelation(sort, genSort)` (:380) | `apply_leq_relation` |
//! | gt relocation + `bdd_appall(…, bddop_nand, …)` maximality (:408-440) | `gt_relation_remapped`, `maximal_from_unifier` |
//! | `AllSat(maximal, secondBase, nextBddVariable - 1)` (:442) | `AllSat::new(maximal, first_available_variable(), last_real)` |
//!
//! **Not in this module** (they land with the UnificationProblem driver): the
//! `computeGeneralizedSort` term walk itself (`Interface/dagNode.cc`), free-variable collection
//! and real-block allocation (`realToBdd`, :317-339), the unifier conjunction loop (:349-395),
//! and the fresh-variable binding/instantiation of solutions (:444-475).

use crate::engine::Signature;
use crate::sort::{KindId, SortId, Sorts};
use crate::symbol::SymbolId;
use biodivine_lib_bdd::{
    Bdd, BddPartialValuation, BddPointer, BddVariable, BddVariableSet, op_function,
};
use std::collections::HashMap;

/// Default initial width of the real-variable region (bits). The driver grows it per problem via
/// [`SortBdds::ensure_real_capacity`]; 64 bits covers ~10 free variables of a 64-sort kind
/// without a rebuild.
pub(crate) const DEFAULT_REAL_CAPACITY: u16 = 64;

/// Default initial width of the sort-function domain region (bits). Grown on demand inside
/// [`SortBdds::sort_function`] when a symbol's summed per-argument kind bits exceed it.
const DEFAULT_DOMAIN_CAPACITY: u16 = 64;

/// Port of `SortBdds::calculateNrBits` (sortBdds.cc:217-227): bits needed to represent the sort
/// indices `0..nr_indices-1`, minimum 1.
fn calculate_nr_bits(nr_indices: usize) -> u16 {
    let mut nr_bits = 1u16;
    let mut representable = 2usize;
    while representable < nr_indices {
        nr_bits += 1;
        representable <<= 1;
    }
    nr_bits
}

/// BuDDy's `bddop_nand` as a biodivine op function (no `nand` in `op_function`); the maximality
/// quantifier's operator (unificationProblem.cc:437).
fn nand(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), _) | (_, Some(false)) => Some(true),
        (Some(true), Some(true)) => Some(false),
        _ => None,
    }
}

/// Extend `b`'s tracked variable count to `total` (a universe that grew by appending variables at
/// the top). Preserves the node array exactly — `set_num_vars` only rewrites the two terminal
/// nodes' variable counter — so a widened BDD is *canonically identical* to the same function
/// built directly in the wider universe (asserted by the `capacity_regrowth` test).
#[expect(unsafe_code, reason = "biodivine's set_num_vars is `unsafe` (universe compatibility); \
    it still panics rather than corrupt if a node references a variable >= total")]
fn widen(b: &mut Bdd, total: u16) {
    debug_assert!(total >= b.num_vars());
    unsafe { b.set_num_vars(total) };
}

/// Per-kind data: Maude's `ComponentInfo` (sortBdds.hh:57-61) plus that kind's slice of the
/// per-sort `leqRelations` vector (indexed here by **local** sort index, i.e. the position in
/// [`crate::sort::Kind::index_order`]; Maude indexes by module-global sort index).
struct KindBdds {
    /// Bits to encode one sort index of this kind (`ComponentInfo::nrVariables`).
    bits: u16,
    /// `valid(s1) ∧ valid(s2) ∧ s1 > s2` with `s1` over scratch1 and `s2` over scratch2
    /// (`ComponentInfo::gtRelation`, sortBdds.cc:60-91).
    gt: Bdd,
    /// Per local sort index `s`: `valid(x) ∧ x <= s` with `x` over scratch1
    /// (`leqRelations`, sortBdds.cc:94-114).
    leq: Vec<Bdd>,
}

/// The BDD side of order-sorted unification's sort computation — Maude's `SortBdds`
/// (`Core/sortBdds.{hh,cc}`), one instance **per unification problem** (see the module doc's
/// deviation list). All eager relations are built at construction; sort functions fill in lazily.
pub(crate) struct SortBdds {
    /// The fixed-size variable universe; recreated (wider) by capacity growth.
    universe: BddVariableSet,
    /// Handle per variable index (`universe.variables()`), refreshed on rebuild.
    vars: Vec<BddVariable>,
    /// Max `bits` over all kinds — the width of each scratch block (Maude's `maxNrVariables`).
    maxbits: u16,
    /// Current width of the real-variable region `[real0, real0 + real_capacity)`.
    real_capacity: u16,
    /// Current width of the sort-function domain region `[domain0, domain0 + domain_capacity)`.
    domain_capacity: u16,
    /// Per kind, indexed by `KindId::index()`.
    kinds: Vec<KindBdds>,
    /// Lazy per-symbol sort functions over the domain region (Maude's `sortFunctions` +
    /// `getSortFunction`, sortBdds.cc:117-139), one BDD per range-kind bit.
    sort_fns: HashMap<SymbolId, Vec<Bdd>>,
    /// `getRemappedLeqRelation` results keyed by `(sort, first_variable)`. Maude rebuilds these
    /// per call through a cached BuDDy pairing (sortBdds.cc:229-247); caching the result BDD is
    /// strictly a memo — the relabel is deterministic.
    leq_remap: HashMap<(SortId, u16), Bdd>,
    /// gt relations with the second argument relocated to a real block, keyed by
    /// `(kind, first_real)` — the `secondArgToReal` `bdd_replace` of unificationProblem.cc:422-433.
    gt_remap: HashMap<(KindId, u16), Bdd>,
}

impl SortBdds {
    /// Port of the `SortBdds` constructor (sortBdds.cc:41-115): compute per-kind bit widths, then
    /// build every kind's `gt` relation (over scratch1 × scratch2) and every sort's `leq`
    /// relation (over scratch1) eagerly. `real_capacity` is the initial real-region width
    /// ([`DEFAULT_REAL_CAPACITY`]); [`ensure_real_capacity`](Self::ensure_real_capacity) grows it.
    pub(crate) fn new(sorts: &Sorts, real_capacity: u16) -> SortBdds {
        let max_sorts =
            sorts.kinds().map(|k| sorts.kind(k).index_order.len()).max().unwrap_or(0);
        let maxbits = calculate_nr_bits(max_sorts);
        let total = 2 * maxbits + real_capacity + DEFAULT_DOMAIN_CAPACITY;
        let universe = BddVariableSet::new_anonymous(total);
        let vars = universe.variables();
        let mut sb = SortBdds {
            universe,
            vars,
            maxbits,
            real_capacity,
            domain_capacity: DEFAULT_DOMAIN_CAPACITY,
            kinds: Vec::with_capacity(sorts.num_kinds()),
            sort_fns: HashMap::new(),
            leq_remap: HashMap::new(),
            gt_remap: HashMap::new(),
        };
        for kid in sorts.kinds() {
            let kind = sorts.kind(kid);
            let bits = calculate_nr_bits(kind.index_order.len());
            let gt = sb.gt_relation_at(sorts, kid, sb.scratch2());
            let leq =
                kind.index_order.iter().map(|&s| sb.leq_relation_at(sorts, s, 0)).collect();
            sb.kinds.push(KindBdds { bits, gt, leq });
        }
        sb
    }

    // ---- layout ----

    /// First variable of the second scratch block (the gt relation's second argument).
    fn scratch2(&self) -> u16 {
        self.maxbits
    }

    /// First variable of the sort-function domain region (above the real region — module doc).
    fn domain0(&self) -> u16 {
        self.first_available_variable() + self.real_capacity
    }

    /// The first real variable — where the driver starts allocating per-free-variable blocks, and
    /// the `AllSat` range start. Maude's `getFirstAvailableVariable` (sortBdds.hh:82-86) returns
    /// `maxNrVariables` (its real region overlays the gt second-argument block); ours is disjoint
    /// at `2 * maxbits`, which is invisible in results (module doc).
    pub(crate) fn first_available_variable(&self) -> u16 {
        2 * self.maxbits
    }

    /// Bits used to encode one sort index of `kind` — Maude's `getNrVariables` (sortBdds.hh:88-92).
    pub(crate) fn nr_variables(&self, kind: KindId) -> u16 {
        self.kinds[kind.index()].bits
    }

    /// The constant-true BDD of this instance's universe (`bddtrue` — the driver's initial
    /// `unifier`, unificationProblem.cc:349).
    pub(crate) fn mk_true(&self) -> Bdd {
        self.universe.mk_true()
    }

    // ---- relation construction (DNF over sort-index cubes) ----

    /// Set the `bits`-wide cube `first..first+bits` to the binary encoding of `index` (LSB at
    /// `first`) — the loop body of Maude's `makeIndexBdd` (sortBdds.cc:185-198).
    fn set_index_bits(&self, cube: &mut BddPartialValuation, first: u16, bits: u16, index: u32) {
        for k in 0..bits {
            cube.set_value(self.vars[(first + k) as usize], index >> k & 1 == 1);
        }
    }

    /// `valid(x) ∧ x <= sort` with `x` encoded at `first..first+bits` — the `leqRelations`
    /// construction of sortBdds.cc:100-113, built from [`crate::sort::Kind::index_order`]
    /// filtered by [`Sorts::leq`] (ascending local indices — Maude's `getLeqSorts` `NatSet`
    /// order). Positioned construction doubles as the direct-build oracle for the
    /// `shift_block` remap tests.
    fn leq_relation_at(&self, sorts: &Sorts, sort: SortId, first: u16) -> Bdd {
        let kind = sorts.kind(sorts.kind_of(sort));
        let bits = calculate_nr_bits(kind.index_order.len());
        let cubes: Vec<BddPartialValuation> = kind
            .index_order
            .iter()
            .enumerate()
            .filter(|&(_, &t)| sorts.leq(t, sort))
            .map(|(i, _)| {
                let mut cube = BddPartialValuation::empty();
                self.set_index_bits(&mut cube, first, bits, i as u32);
                cube
            })
            .collect();
        self.universe.mk_dnf(&cubes)
    }

    /// `valid(s1) ∧ valid(s2) ∧ s1 > s2` with `s1` over scratch1 and `s2` at
    /// `second_first..second_first+bits` — the `gtRelation` construction of sortBdds.cc:70-91
    /// (`s1 > s2` ⇔ `s2 <= s1 ∧ s2 != s1`).
    fn gt_relation_at(&self, sorts: &Sorts, kind: KindId, second_first: u16) -> Bdd {
        let k = sorts.kind(kind);
        let bits = calculate_nr_bits(k.index_order.len());
        let mut cubes: Vec<BddPartialValuation> = Vec::new();
        for (s1, &t1) in k.index_order.iter().enumerate() {
            for (s2, &t2) in k.index_order.iter().enumerate() {
                if s1 != s2 && sorts.leq(t2, t1) {
                    let mut cube = BddPartialValuation::empty();
                    self.set_index_bits(&mut cube, 0, bits, s1 as u32);
                    self.set_index_bits(&mut cube, second_first, bits, s2 as u32);
                    cubes.push(cube);
                }
            }
        }
        self.universe.mk_dnf(&cubes)
    }

    // ---- bit-vector constructors ----

    /// A vector of `bits` constant BDDs encoding `local_index` (LSB first) — Maude's
    /// `makeIndexVector` (sortBdds.cc:141-155); the BDD encoding of a known sort.
    pub(crate) fn make_index_vector(&self, bits: u16, local_index: u32) -> Vec<Bdd> {
        (0..bits)
            .map(|k| {
                if local_index >> k & 1 == 1 {
                    self.universe.mk_true()
                } else {
                    self.universe.mk_false()
                }
            })
            .collect()
    }

    /// A vector of `bits` positive literals for the block at `first_variable` — the undetermined
    /// sort of a free variable, Maude's `makeVariableVector`/`appendVariableVector`
    /// (sortBdds.cc:157-183). (Maude's *`makeVariableBdd`* proper builds the quantification
    /// *cube* for `bdd_appall`; biodivine quantifiers take variable lists, so the cube form has
    /// no counterpart here — the spec-chosen name is kept for the vector.)
    pub(crate) fn make_variable_bdd(&self, first_variable: u16, bits: u16) -> Vec<Bdd> {
        (0..bits)
            .map(|k| self.universe.mk_literal(self.vars[(first_variable + k) as usize], true))
            .collect()
    }

    // ---- remaps and composition ----

    /// Clone `b` and relabel the `bits`-wide block at `from` to start at `to` — the production
    /// replacement for BuDDy's `bdd_replace` on upward block remaps (S0 report §2/§6 delta 1).
    ///
    /// Precondition (order preservation): the move must keep `b`'s support strictly sorted —
    /// here always satisfied because blocks move **as units** from a scratch position to a
    /// region above every other support variable (scratch1 → real/domain with scratch2 unused,
    /// or scratch2 → real with only scratch1 below). biodivine asserts the sorted-support
    /// property internally, so a violated precondition panics rather than corrupts.
    #[expect(unsafe_code, reason = "biodivine's rename_variables is `unsafe` (non-semantic \
        relabel); sound here by the documented order-preservation precondition, which the \
        library re-checks with asserts")]
    fn shift_block(&self, b: &Bdd, from: u16, bits: u16, to: u16) -> Bdd {
        let mut b = b.clone();
        let map: HashMap<BddVariable, BddVariable> = (0..bits)
            .map(|j| (self.vars[(from + j) as usize], self.vars[(to + j) as usize]))
            .collect();
        unsafe { b.rename_variables(&map) };
        b
    }

    /// `valid(x) ∧ x <= sort` with `x` relocated to `first_variable..` — Maude's
    /// `getRemappedLeqRelation` (sortBdds.cc:229-247). Used for the per-free-variable constraints
    /// (real positions, unificationProblem.cc:355/388) and the sort-function domain constraints
    /// (domain positions, sortTable.cc:486). Results are memoized per `(sort, first_variable)`.
    pub(crate) fn get_remapped_leq_relation(
        &mut self,
        sorts: &Sorts,
        sort: SortId,
        first_variable: u16,
    ) -> Bdd {
        if let Some(b) = self.leq_remap.get(&(sort, first_variable)) {
            return b.clone();
        }
        let kind = sorts.kind_of(sort);
        let bits = self.kinds[kind.index()].bits;
        let local = sorts.component_index(sort) as usize;
        let b = self.shift_block(&self.kinds[kind.index()].leq[local], 0, bits, first_variable);
        self.leq_remap.insert((sort, first_variable), b.clone());
        b
    }

    /// The `leq` relation for the sort with local index `local_sort_index` in `kind`, applied to
    /// an `x` given as a bit-vector of BDDs — Maude's `applyLeqRelation` (sortBdds.cc:249-271,
    /// a `bdd_veccompose`). The sequential `substitute` chain is sound because `args` never
    /// mention scratch1 (they are over real or domain variables only).
    pub(crate) fn apply_leq_relation(
        &self,
        kind: KindId,
        local_sort_index: u32,
        args: &[Bdd],
    ) -> Bdd {
        let kb = &self.kinds[kind.index()];
        assert_eq!(args.len(), kb.bits as usize, "wrong number of BDD arguments");
        let mut b = kb.leq[local_sort_index as usize].clone();
        for (i, g) in args.iter().enumerate() {
            b = b.substitute(self.vars[i], g);
        }
        b
    }

    /// The sort function of `symbol`: one BDD per range-kind bit, over consecutive domain blocks
    /// starting at `domain0` (one block per argument, sized by that argument's **kind** bits).
    /// Built on demand and cached — Maude's `getSortFunction` (sortBdds.cc:117-139); the
    /// construction is `linearComputeSortFunctionBdds` only (module doc).
    pub(crate) fn sort_function(&mut self, sig: &Signature, symbol: SymbolId) -> &[Bdd] {
        if !self.sort_fns.contains_key(&symbol) {
            let f = self.build_sort_function(sig, symbol);
            self.sort_fns.insert(symbol, f);
        }
        self.sort_fns[&symbol].as_slice()
    }

    /// Port of `SortTable::linearComputeSortFunctionBdds` (sortTable.cc:459-508): start from the
    /// constant `ERROR_SORT` (local index 0) function and, walking the declarations **in reverse**
    /// (the algorithm breaks toward later declarations, so reverse order reproduces the standard
    /// non-preregular tie-break toward *earlier* ones), ite-replace with a declaration's range
    /// wherever all arguments fit its domain and the current sort is not already `<=` that range.
    fn build_sort_function(&mut self, sig: &Signature, symbol: SymbolId) -> Vec<Bdd> {
        let sorts = sig.sorts();
        let sym = sig.symbol(symbol);
        let decls = sym.decls();
        let range_kind = sorts.kind_of(decls[0].range);
        let rbits = self.nr_variables(range_kind);
        if sym.arity() == 0 {
            // Constant operator: Maude emits `makeIndexVector(nrVariables,
            // singleNonErrorSort->index())` (sortTable.cc:399-410). tnk has no
            // `singleNonErrorSort` precomputation; for a constant every declaration is
            // applicable, so its diagram entry is exactly `compute_sort(symbol, [])` — the least
            // declared range with tnk's (= Maude's `findMinSortIndex`) earliest-declaration
            // tie-break. An ad-hoc-overloaded constant with *incomparable* ranges is pathological
            // (Maude warns about non-preregularity); the S1 oracle fixtures judge that edge.
            let least = sig.compute_sort(symbol, &[]);
            return self.make_index_vector(rbits, sorts.component_index(least));
        }
        // One domain block per argument, sized by the argument's kind (all declarations of a
        // symbol agree on per-argument kinds).
        let arg_bits: Vec<u16> =
            decls[0].domain.iter().map(|&d| self.nr_variables(sorts.kind_of(d))).collect();
        self.ensure_domain_capacity(arg_bits.iter().sum());
        let domain0 = self.domain0();
        // The constant ERROR_SORT function (sortTable.cc:469).
        let mut f = self.make_index_vector(rbits, 0);
        for decl in decls.iter().rev() {
            debug_assert_eq!(sorts.kind_of(decl.range), range_kind);
            // All arguments <= the declaration's domain sorts (sortTable.cc:482-489).
            let mut cond = self.universe.mk_true();
            let mut pos = domain0;
            for (j, &d) in decl.domain.iter().enumerate() {
                cond = cond.and(&self.get_remapped_leq_relation(sorts, d, pos));
                pos += arg_bits[j];
            }
            // ... and the currently computed sort is NOT <= our range sort — so our sort wins in
            // the incomparable and the > cases (sortTable.cc:491-497).
            let cur_leq_range =
                self.apply_leq_relation(range_kind, sorts.component_index(decl.range), &f);
            let cond = cond.and_not(&cur_leq_range);
            // ite update per output bit (sortTable.cc:499-506).
            let range_bits = self.make_index_vector(rbits, sorts.component_index(decl.range));
            for k in 0..rbits as usize {
                f[k] = Bdd::if_then_else(&cond, &range_bits[k], &f[k]);
            }
        }
        f
    }

    /// Compose `symbol`'s sort function with the given argument bit-vectors — Maude's
    /// `operatorCompose` (sortBdds.cc:292-320, a `bdd_veccompose` per output bit). `input_bits`
    /// is the concatenation of the arguments' generalized-sort vectors (over real variables
    /// only, which is what makes the sequential `substitute` chain sound — no input mentions a
    /// pending domain variable).
    pub(crate) fn operator_compose(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        input_bits: &[Bdd],
    ) -> Vec<Bdd> {
        self.sort_function(sig, symbol); // ensure cached (may grow the domain region)
        let f = &self.sort_fns[&symbol];
        let domain0 = self.domain0() as usize;
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

    // ---- maximality (unificationProblem.cc:396-442) ----

    /// The gt relation of `kind` with its **second** argument (the lesser sort) relocated to the
    /// real block at `first_real`, the first argument (the quantified greater candidate `Y`)
    /// staying on scratch1 — exactly Maude's `secondArgToReal` `bdd_replace`
    /// (unificationProblem.cc:422-433: `bdd_setpair(secondArgToReal, j, j)` keeps arg 1 at
    /// `0..bits`, `bdd_setpair(secondArgToReal, secondBase + j, firstVar + j)` moves arg 2).
    /// Memoized per `(kind, first_real)`.
    pub(crate) fn gt_relation_remapped(&mut self, kind: KindId, first_real: u16) -> Bdd {
        if let Some(b) = self.gt_remap.get(&(kind, first_real)) {
            return b.clone();
        }
        let bits = self.kinds[kind.index()].bits;
        let b = self.shift_block(&self.kinds[kind.index()].gt, self.scratch2(), bits, first_real);
        self.gt_remap.insert((kind, first_real), b.clone());
        b
    }

    /// The maximality constraint over a satisfiable `unifier` — the BDD half of
    /// unificationProblem.cc:396-440:
    ///
    /// ```text
    /// maximal(X1,…,Xn) = unifier(X1,…,Xn) ∧
    ///   ⋀ᵢ ∀ Y . ¬( gt(Y, Xi) ∧ unifier(X1,…,Y,…,Xn) )     (the not pushed inside as NAND)
    /// ```
    ///
    /// `free_blocks` lists each free variable's kind and real-block start, in allocation order
    /// (Maude iterates its `freeVariables` `NatSet` ascending; conjunction order is invisible in
    /// the canonical result). Per variable: `gt` arrives with arg 2 on the variable's real block
    /// ([`gt_relation_remapped`](Self::gt_relation_remapped)); the unifier's real block is moved
    /// *down* to scratch1 with the functional replace `exists block . (unifier ∧ (block ↔
    /// scratch1))` in one fused `binary_op_with_exists` (the downward move is not
    /// order-preserving, so `shift_block` is inapplicable — S0 report §2); then one fused
    /// `binary_op_with_for_all(gt, renamed, nand, scratch1)` is Maude's
    /// `bdd_appall(…, bddop_nand, makeVariableBdd(0, bits))`.
    pub(crate) fn maximal_from_unifier(
        &mut self,
        unifier: &Bdd,
        free_blocks: &[(KindId, u16)],
    ) -> Bdd {
        let mut maximal = unifier.clone();
        for &(kind, first) in free_blocks {
            let bits = self.kinds[kind.index()].bits;
            let gt = self.gt_relation_remapped(kind, first);
            let mut iff_conj = self.universe.mk_true();
            let mut block_vars = Vec::with_capacity(bits as usize);
            for j in 0..bits as usize {
                let bv = self.vars[first as usize + j];
                block_vars.push(bv);
                let l = self.universe.mk_literal(bv, true);
                let r = self.universe.mk_literal(self.vars[j], true);
                iff_conj = iff_conj.and(&l.iff(&r));
            }
            let renamed =
                Bdd::binary_op_with_exists(unifier, &iff_conj, op_function::and, &block_vars);
            let scratch1: Vec<BddVariable> = self.vars[..bits as usize].to_vec();
            maximal = maximal.and(&Bdd::binary_op_with_for_all(&gt, &renamed, nand, &scratch1));
            // Maude's (debug-only) Assert at unificationProblem.cc:439.
            debug_assert!(
                unifier.is_false() || !maximal.is_false(),
                "maximal false even though unifier isn't"
            );
        }
        maximal
    }

    // ---- capacity growth ----

    /// Make sure the real region holds at least `real_bits_needed` bits (the driver's
    /// `nextBddVariable - firstAvailable` after block allocation — Maude grows the global BuDDy
    /// pool with `BddUser::setNrVariables`, unificationProblem.cc:345). Growing rebuilds the
    /// universe; see the module doc's driver protocol — call this before holding any BDDs.
    pub(crate) fn ensure_real_capacity(&mut self, real_bits_needed: u16) {
        if real_bits_needed > self.real_capacity {
            let new_cap = real_bits_needed.max(self.real_capacity.saturating_mul(2));
            self.rebuild(new_cap, self.domain_capacity);
        }
    }

    /// Make sure the domain region holds at least `domain_bits_needed` bits. Called by
    /// [`sort_function`](Self::sort_function); the domain region sits at the top of the universe,
    /// so growth appends variables and no existing index moves.
    fn ensure_domain_capacity(&mut self, domain_bits_needed: u16) {
        if domain_bits_needed > self.domain_capacity {
            let new_cap = domain_bits_needed.max(self.domain_capacity.saturating_mul(2));
            self.rebuild(self.real_capacity, new_cap);
        }
    }

    /// Recreate the universe with the given region widths and carry every cached BDD across.
    /// Widening appends variables at the top, so all *existing* variable indices are preserved
    /// and a cached BDD only needs its variable count extended ([`widen`], node structure
    /// untouched) — except that growing the **real** region moves the domain region up, so sort
    /// functions get their domain blocks [`shift_block`](Self::shift_block)ed (order-preserving:
    /// their support is domain-only and shifts as one unit), and remap-cache entries keyed at
    /// old *domain* positions are dropped (their old keys could now alias real positions;
    /// they are cheap to rebuild on demand).
    fn rebuild(&mut self, real_capacity: u16, domain_capacity: u16) {
        let old_domain0 = self.domain0();
        let old_domain_capacity = self.domain_capacity;
        self.real_capacity = real_capacity;
        self.domain_capacity = domain_capacity;
        let total = u32::from(self.first_available_variable())
            + u32::from(real_capacity)
            + u32::from(domain_capacity);
        // biodivine substitution needs a spare proxy variable below u16::MAX.
        assert!(total < u32::from(u16::MAX), "BDD variable universe overflow ({total} bits)");
        let total = total as u16;
        self.universe = BddVariableSet::new_anonymous(total);
        self.vars = self.universe.variables();
        let new_domain0 = self.domain0();

        for kb in &mut self.kinds {
            widen(&mut kb.gt, total);
            for b in &mut kb.leq {
                widen(b, total);
            }
        }
        let mut sort_fns = std::mem::take(&mut self.sort_fns);
        for f in sort_fns.values_mut() {
            for b in f.iter_mut() {
                widen(b, total);
                if new_domain0 != old_domain0 {
                    *b = self.shift_block(b, old_domain0, old_domain_capacity, new_domain0);
                }
            }
        }
        self.sort_fns = sort_fns;
        self.leq_remap.retain(|&(_, pos), b| {
            if new_domain0 != old_domain0 && pos >= old_domain0 {
                return false; // stale domain-position entry
            }
            widen(b, total);
            true
        });
        self.gt_remap.retain(|&(_, pos), b| {
            if new_domain0 != old_domain0 && pos >= old_domain0 {
                return false; // defensive; gt remaps target real positions only
            }
            widen(b, total);
            true
        });
    }
}

// ======================================================================================
// AllSat — line-for-line port of Utility/allSat.{hh,cc}
// ======================================================================================

/// Enumerate all satisfying assignments of `formula` over the variables
/// `first_variable..=last_variable` — Maude's `AllSat` (`Utility/allSat.{hh,cc}`), ported
/// verbatim over biodivine's node array ([`BddPointer`] traversal, not biodivine's own
/// iterators, to preserve the reference walk exactly). The enumeration order is observable
/// (unifier order), fixed by: low-branch-first DFS to the first path (`forward`), don't-care
/// variables collected in ascending variable order and stepped by binary counting (low flips
/// fastest at the **highest**-indexed don't-care), then node-stack backtracking to the next path.
///
/// Assignments are fully concrete over the range after a successful
/// [`next_assignment`](Self::next_assignment) — don't-cares carry the counter's current bits,
/// exactly like the reference (allSat.cc:58-74).
///
/// Precondition (as in Maude): `formula`'s support lies within `0..=last_variable` — a higher
/// variable on a path would index out of bounds (a panic here; UB in the C++).
pub(crate) struct AllSat {
    formula: Bdd,
    first_variable: u16,
    last_variable: u16,
    /// Current path to true through the BDD (allSat.hh:46).
    node_stack: Vec<BddPointer>,
    /// Variables of interest not mentioned on the current path, ascending (allSat.hh:47).
    dont_care_set: Vec<usize>,
    /// Current assignment, indexed by absolute variable index; `None` is the reference's
    /// `UNDEFINED` byte (allSat.hh:48).
    assignment: Vec<Option<bool>>,
    first_assignment: bool,
}

impl AllSat {
    /// Port of the constructor (allSat.cc:30-38). `first_variable > last_variable` is the legal
    /// empty range (a unification problem with no free variables): a satisfiable formula then
    /// yields exactly one empty assignment.
    pub(crate) fn new(formula: Bdd, first_variable: u16, last_variable: u16) -> AllSat {
        let span = (last_variable as usize + 1).saturating_sub(first_variable as usize);
        AllSat {
            formula,
            first_variable,
            last_variable,
            node_stack: Vec::with_capacity(span),
            dont_care_set: Vec::with_capacity(span),
            assignment: Vec::new(),
            first_assignment: true,
        }
    }

    /// The current assignment over the range; index 0 is `first_variable`. Only meaningful after
    /// [`next_assignment`](Self::next_assignment) returned `true` (every entry is then `Some`).
    pub(crate) fn current_assignment(&self) -> &[Option<bool>] {
        &self.assignment[self.first_variable as usize..self.last_variable as usize + 1]
    }

    /// Advance to the next satisfying assignment — port of `AllSat::nextAssignment`
    /// (allSat.cc:40-97).
    pub(crate) fn next_assignment(&mut self) -> bool {
        if self.first_assignment {
            // First solution (allSat.cc:43-56).
            if self.formula.is_false() {
                return false;
            }
            self.assignment = vec![None; self.last_variable as usize + 1];
            self.forward(self.formula.root_pointer());
            self.first_assignment = false;
            return true;
        }
        // Try to find another way of assigning to don't-care variables (allSat.cc:57-71).
        let nr_dont_cares = self.dont_care_set.len();
        for i in (0..nr_dont_cares).rev() {
            let var = self.dont_care_set[i];
            if self.assignment[var] == Some(false) {
                self.assignment[var] = Some(true);
                for j in i + 1..nr_dont_cares {
                    self.assignment[self.dont_care_set[j]] = Some(false);
                }
                return true;
            }
        }
        for i in 0..nr_dont_cares {
            self.assignment[self.dont_care_set[i]] = None;
        }
        self.dont_care_set.clear();
        // Try to find another route to true through the BDD (allSat.cc:75-96).
        let node_depth = self.node_stack.len();
        for i in (0..node_depth).rev() {
            let b = self.node_stack[i];
            let var = self.formula.var_of(b).to_index();
            if self.assignment[var] == Some(false) {
                let n = self.formula.high_link_of(b);
                if !n.is_zero() {
                    self.assignment[var] = Some(true);
                    self.node_stack.truncate(i + 1);
                    self.forward(n);
                    return true;
                }
            }
            self.assignment[var] = None;
        }
        false
    }

    /// Follow the least (low-branch-first) path from `b` to true, then collect the don't-cares —
    /// port of `AllSat::forward` (allSat.cc:99-131).
    fn forward(&mut self, mut b: BddPointer) {
        debug_assert!(!b.is_zero(), "false BDD");
        while !b.is_one() {
            self.node_stack.push(b);
            let var = self.formula.var_of(b).to_index();
            let low = self.formula.low_link_of(b);
            if low.is_zero() {
                self.assignment[var] = Some(true);
                b = self.formula.high_link_of(b);
            } else {
                self.assignment[var] = Some(false);
                b = low;
            }
        }
        // Any variables of interest not assigned on this path are don't-cares.
        for i in self.first_variable as usize..=self.last_variable as usize {
            if self.assignment[i].is_none() {
                self.assignment[i] = Some(false);
                self.dont_care_set.push(i);
            }
        }
    }
}

// ======================================================================================
// Tests
// ======================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// A bound term for the emulated driver (the real `computeGeneralizedSort` walk lands with
    /// the UnificationProblem driver).
    enum TTerm {
        Var(usize),
        App(SymbolId, Vec<TTerm>),
    }

    /// The spike's simplified prelude number tower — one kind of 8 sorts (incl. error) with
    /// subsort diamonds — plus `+` (4 decls), unary `-` (2 decls), `*` (6 decls).
    fn tower() -> (Engine, Vec<SortId>, SymbolId, SymbolId, SymbolId) {
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
        let plus = e.add_op("_+_", vec![nznat, nznat], nznat);
        e.add_op_decl(plus, vec![nat, nat], nat);
        e.add_op_decl(plus, vec![int, int], int);
        e.add_op_decl(plus, vec![rat, rat], rat);
        let minus = e.add_op("-_", vec![int], int);
        e.add_op_decl(minus, vec![rat], rat);
        let times = e.add_op("_*_", vec![nznat, nznat], nznat);
        e.add_op_decl(times, vec![nat, nat], nat);
        e.add_op_decl(times, vec![nzint, nzint], nzint);
        e.add_op_decl(times, vec![int, int], int);
        e.add_op_decl(times, vec![nzrat, nzrat], nzrat);
        e.add_op_decl(times, vec![rat, rat], rat);
        (e, vec![rat, int, nzrat, nat, nzint, zero, nznat], plus, minus, times)
    }

    /// One top sort with `m` pairwise-incomparable sorts below it, and a unary `g` with a
    /// declaration `g : Ai -> Ai` per antichain sort — the AllSat stress shape (the constraint
    /// `sortOf(g(X)) <= T` forces `X` into the antichain: `m` maximal solutions per variable).
    fn diamond(m: usize) -> (Engine, SortId, Vec<SortId>, SymbolId) {
        let mut e = Engine::new();
        let top = e.add_sort("T");
        let mids: Vec<SortId> = (0..m).map(|i| e.add_sort(format!("A{i}"))).collect();
        for &a in &mids {
            e.add_subsort(a, top);
        }
        e.close_sorts();
        let g = e.add_op("g", vec![mids[0]], mids[0]);
        for &a in &mids[1..] {
            e.add_op_decl(g, vec![a], a);
        }
        (e, top, mids, g)
    }

    /// Generalized sort of a bound term over the free variables' real blocks — the driver-side
    /// `computeGeneralizedSort` recursion, emulated with this module's primitives.
    fn generalized_sort(
        sb: &mut SortBdds,
        sig: &Signature,
        t: &TTerm,
        blocks: &[u16],
        bits: u16,
    ) -> Vec<Bdd> {
        match t {
            TTerm::Var(v) => sb.make_variable_bdd(blocks[*v], bits),
            TTerm::App(sym, kids) => {
                let mut inputs = Vec::new();
                for kid in kids {
                    inputs.extend(generalized_sort(sb, sig, kid, blocks, bits));
                }
                sb.operator_compose(sig, *sym, &inputs)
            }
        }
    }

    fn prefetch_sort_functions(sb: &mut SortBdds, sig: &Signature, t: &TTerm) {
        if let TTerm::App(sym, kids) = t {
            sb.sort_function(sig, *sym);
            for kid in kids {
                prefetch_sort_functions(sb, sig, kid);
            }
        }
    }

    /// Emulate the findOrderSortedUnifiers BDD steps for `k` free variables of one kind
    /// (declared sorts `var_sorts`) plus `bound` constraints `sortOf(term) <= sort`; return the
    /// enumerated maximal assignments (local sort indices, in AllSat order) and the maximal BDD.
    fn solve(
        sb: &mut SortBdds,
        sig: &Signature,
        var_sorts: &[SortId],
        bound: &[(SortId, TTerm)],
    ) -> (Vec<Vec<u32>>, Bdd) {
        let sorts = sig.sorts();
        let kind = sorts.kind_of(var_sorts[0]);
        let bits = sb.nr_variables(kind);
        let k = var_sorts.len() as u16;
        let real0 = sb.first_available_variable();
        // Driver protocol: capacity + sort-function prefetch before holding any BDDs.
        sb.ensure_real_capacity(k * bits);
        for (_, term) in bound {
            prefetch_sort_functions(sb, sig, term);
        }
        let blocks: Vec<u16> = (0..k).map(|v| real0 + v * bits).collect();
        let mut unifier = sb.mk_true();
        for (v, &s) in var_sorts.iter().enumerate() {
            unifier = unifier.and(&sb.get_remapped_leq_relation(sorts, s, blocks[v]));
        }
        for (bsort, term) in bound {
            let gen = generalized_sort(sb, sig, term, &blocks, bits);
            unifier = unifier.and(&sb.apply_leq_relation(
                sorts.kind_of(*bsort),
                sorts.component_index(*bsort),
                &gen,
            ));
        }
        let free: Vec<(KindId, u16)> = blocks.iter().map(|&b| (kind, b)).collect();
        let maximal = sb.maximal_from_unifier(&unifier, &free);
        let mut all_sat = AllSat::new(maximal.clone(), real0, real0 + k * bits - 1);
        let mut out = Vec::new();
        while all_sat.next_assignment() {
            let a = all_sat.current_assignment();
            let tuple: Vec<u32> = (0..k)
                .map(|v| {
                    (0..bits).fold(0u32, |x, j| {
                        x | (u32::from(a[(v * bits + j) as usize] == Some(true)) << j)
                    })
                })
                .collect();
            out.push(tuple);
        }
        (out, maximal)
    }

    fn pointwise_term_sort(sig: &Signature, t: &TTerm, var_sorts: &[SortId]) -> SortId {
        match t {
            TTerm::Var(v) => var_sorts[*v],
            TTerm::App(sym, kids) => {
                let args: Vec<SortId> =
                    kids.iter().map(|k| pointwise_term_sort(sig, k, var_sorts)).collect();
                sig.compute_sort(*sym, &args)
            }
        }
    }

    /// Brute-force maximal solutions over one kind (in no particular order): all local-index
    /// tuples that satisfy every constraint and where no single coordinate can be raised
    /// (strictly, per `Sorts::leq`) while remaining satisfying.
    fn brute_force_maximal(
        sig: &Signature,
        var_sorts: &[SortId],
        bound: &[(SortId, TTerm)],
    ) -> Vec<Vec<u32>> {
        let sorts = sig.sorts();
        let order = &sorts.kind(sorts.kind_of(var_sorts[0])).index_order;
        let n = order.len() as u32;
        let k = var_sorts.len();
        let mut all: Vec<Vec<u32>> = vec![vec![]];
        for _ in 0..k {
            all = all
                .into_iter()
                .flat_map(|t| {
                    (0..n).map(move |s| {
                        let mut t2 = t.clone();
                        t2.push(s);
                        t2
                    })
                })
                .collect();
        }
        let satisfies = |tuple: &[u32]| -> bool {
            let assigned: Vec<SortId> =
                tuple.iter().map(|&li| order[li as usize]).collect();
            assigned.iter().zip(var_sorts).all(|(&a, &declared)| sorts.leq(a, declared))
                && bound.iter().all(|(bsort, term)| {
                    sorts.leq(pointwise_term_sort(sig, term, &assigned), *bsort)
                })
        };
        all.into_iter()
            .filter(|t| satisfies(t))
            .filter(|t| {
                !(0..k).any(|v| {
                    (0..n).any(|y| {
                        y != t[v] && sorts.leq(order[t[v] as usize], order[y as usize]) && {
                            let mut t2 = t.clone();
                            t2[v] = y;
                            satisfies(&t2)
                        }
                    })
                })
            })
            .collect()
    }

    /// Evaluate `sym`'s sort-function BDD vector on every tuple of valid argument indices and
    /// compare the decoded result against the engine's own least-sort computation.
    fn check_sort_function_pointwise(sb: &mut SortBdds, sig: &Signature, sym: SymbolId) {
        let sorts = sig.sorts();
        let domain = sig.symbol(sym).decls()[0].domain.clone();
        let arg_orders: Vec<Vec<SortId>> =
            domain.iter().map(|&d| sorts.kind(sorts.kind_of(d)).index_order.clone()).collect();
        let range_kind = sorts.kind_of(sig.symbol(sym).decls()[0].range);
        let rbits = sb.nr_variables(range_kind);
        let mut tuples: Vec<Vec<u32>> = vec![vec![]];
        for order in &arg_orders {
            tuples = tuples
                .into_iter()
                .flat_map(|t| {
                    (0..order.len() as u32).map(move |s| {
                        let mut t2 = t.clone();
                        t2.push(s);
                        t2
                    })
                })
                .collect();
        }
        for tuple in tuples {
            let mut inputs = Vec::new();
            for (j, &li) in tuple.iter().enumerate() {
                let bits = sb.nr_variables(sorts.kind_of(domain[j]));
                inputs.extend(sb.make_index_vector(bits, li));
            }
            let composed = sb.operator_compose(sig, sym, &inputs);
            let mut actual = 0u32;
            for (k, bit) in composed.iter().enumerate() {
                assert!(bit.is_true() || bit.is_false(), "non-constant sort-function bit");
                if bit.is_true() {
                    actual |= 1 << k;
                }
            }
            assert_eq!(actual, actual & ((1 << rbits) - 1));
            let args: Vec<SortId> = tuple
                .iter()
                .enumerate()
                .map(|(j, &li)| arg_orders[j][li as usize])
                .collect();
            let expected = sorts.component_index(sig.compute_sort(sym, &args));
            assert_eq!(
                actual, expected,
                "sort fn mismatch: {} args {tuple:?}",
                sig.symbol(sym).name()
            );
        }
    }

    /// Set + sequence comparison against brute force, plus the cardinality cross-check the spike
    /// ran (`maximal` depends only on the real range, so its total cardinality is
    /// `solutions * 2^outside`).
    fn check_solve(
        sb: &mut SortBdds,
        sig: &Signature,
        var_sorts: &[SortId],
        bound: &[(SortId, TTerm)],
        label: &str,
    ) -> Vec<Vec<u32>> {
        let (enumerated, maximal) = solve(sb, sig, var_sorts, bound);
        let mut got = enumerated.clone();
        let mut expected = brute_force_maximal(sig, var_sorts, bound);
        got.sort();
        expected.sort();
        assert_eq!(got, expected, "maximal solution set mismatch ({label})");
        let sorts = sig.sorts();
        let bits = sb.nr_variables(sorts.kind_of(var_sorts[0]));
        let range = var_sorts.len() * bits as usize;
        let outside = sb.universe.num_vars() as usize - range;
        let count = maximal.exact_cardinality() >> outside;
        assert_eq!(
            count.to_string(),
            enumerated.len().to_string(),
            "AllSat count vs cardinality ({label})"
        );
        enumerated
    }

    /// Spec test 1: number-tower sort functions match `Signature::compute_sort` pointwise,
    /// exhaustively over all argument-index combinations (incl. the error sort, index 0).
    #[test]
    fn tower_sort_functions_match_compute_sort() {
        let (e, _, plus, minus, times) = tower();
        let sig = e.signature();
        let mut sb = SortBdds::new(sig.sorts(), DEFAULT_REAL_CAPACITY);
        for sym in [plus, minus, times] {
            check_sort_function_pointwise(&mut sb, sig, sym);
        }
    }

    /// Spec test 2a: maximal-solution enumeration vs brute force on the tower — a bound-term
    /// constraint that prunes (X + Y must fit in Nat although Y is declared Int) and the free
    /// case where maximality collapses everything to the declared sorts.
    #[test]
    fn tower_maximal_solutions_match_brute_force() {
        let (e, s, plus, _, _) = tower();
        let (rat, int, nat) = (s[0], s[1], s[3]);
        let sig = e.signature();
        let sorts = sig.sorts();

        // X:Nat, Y:Int, Z:Rat with sortOf(X + Y) <= Nat: Y = Int would give Int, so the
        // maximality step must settle Y at Nat. Expect the single tuple (Nat, Nat, Rat).
        let mut sb = SortBdds::new(sorts, DEFAULT_REAL_CAPACITY);
        let bound = vec![(nat, TTerm::App(plus, vec![TTerm::Var(0), TTerm::Var(1)]))];
        let got = check_solve(&mut sb, sig, &[nat, int, rat], &bound, "tower k=3 + bound");
        let local = |x: SortId| sorts.component_index(x);
        assert_eq!(got, vec![vec![local(nat), local(nat), local(rat)]]);

        // Free case: two Rat variables; the unique maximal assignment is (Rat, Rat).
        let mut sb = SortBdds::new(sorts, DEFAULT_REAL_CAPACITY);
        let got = check_solve(&mut sb, sig, &[rat, rat], &[], "tower k=2 free");
        assert_eq!(got, vec![vec![local(rat), local(rat)]]);
    }

    /// Spec test 2b: the 3-antichain diamond — 3 incomparable maximal sorts per variable, k = 2
    /// free variables ⇒ 3² = 9 maximal solutions; set and count vs brute force.
    #[test]
    fn diamond_antichain_maximal_solutions() {
        let (e, top, _, g) = diamond(3);
        let sig = e.signature();
        let mut sb = SortBdds::new(sig.sorts(), DEFAULT_REAL_CAPACITY);
        let bound = vec![
            (top, TTerm::App(g, vec![TTerm::Var(0)])),
            (top, TTerm::App(g, vec![TTerm::Var(1)])),
        ];
        let got = check_solve(&mut sb, sig, &[top, top], &bound, "diamond m=3 k=2");
        assert_eq!(got.len(), 9);
    }

    /// Spec test 2c: the enumeration **sequence** pinned literally on a hand-derived case. Kind
    /// {error, T, A, B} (2 bits; locals err=0, T=1, A=2, B=3), X and Y forced into the antichain
    /// {A, B}: `maximal = x_bit1 ∧ y_bit1`, so bit0 of X and bit0 of Y are don't-cares collected
    /// ascending — binary counting flips Y first. Expected order: (A,A), (A,B), (B,A), (B,B).
    #[test]
    fn enumeration_order_is_pinned() {
        let (e, top, mids, g) = diamond(2);
        let sig = e.signature();
        let sorts = sig.sorts();
        // Pin the premise: Maude's per-component index order for this declaration order.
        assert_eq!(sorts.component_index(top), 1);
        assert_eq!(sorts.component_index(mids[0]), 2);
        assert_eq!(sorts.component_index(mids[1]), 3);
        let mut sb = SortBdds::new(sorts, DEFAULT_REAL_CAPACITY);
        let bound = vec![
            (top, TTerm::App(g, vec![TTerm::Var(0)])),
            (top, TTerm::App(g, vec![TTerm::Var(1)])),
        ];
        let got = check_solve(&mut sb, sig, &[top, top], &bound, "diamond m=2 k=2 order");
        assert_eq!(got, vec![vec![2, 2], vec![2, 3], vec![3, 2], vec![3, 3]]);
    }

    /// Spec test 3: the `shift_block` remap produces the *canonically identical* BDD to building
    /// the same relation directly at the target position (the spike's B4 validation) — for both
    /// the leq relations and the gt relation.
    #[test]
    fn remap_equals_direct_construction() {
        let (e, s, ..) = tower();
        let sorts = e.sorts();
        let mut sb = SortBdds::new(sorts, DEFAULT_REAL_CAPACITY);
        let kind = sorts.kind_of(s[0]);
        let bits = sb.nr_variables(kind);
        let real0 = sb.first_available_variable();
        for &sort in &s {
            for first in [real0, real0 + bits, real0 + 5 * bits] {
                let remapped = sb.get_remapped_leq_relation(sorts, sort, first);
                let direct = sb.leq_relation_at(sorts, sort, first);
                assert_eq!(remapped, direct, "leq remap diverges ({sort:?} @ {first})");
            }
        }
        for first in [real0, real0 + 2 * bits] {
            let remapped = sb.gt_relation_remapped(kind, first);
            let direct = sb.gt_relation_at(sorts, kind, first);
            assert_eq!(remapped, direct, "gt remap diverges (@ {first})");
        }
    }

    /// Spec test 4: capacity regrowth. Populate every cache with a deliberately tiny real
    /// region, force a rebuild past it, and check that (a) a relation remapped pre-widening is
    /// canonically equal to one built directly in the wide universe, (b) the relocated
    /// sort-function cache still matches `compute_sort` pointwise, and (c) a full solve in the
    /// widened instance matches brute force.
    #[test]
    fn capacity_regrowth_preserves_caches() {
        let (e, s, plus, _, _) = tower();
        let (rat, int, nat) = (s[0], s[1], s[3]);
        let sig = e.signature();
        let sorts = sig.sorts();
        let mut sb = SortBdds::new(sorts, 8); // 3-bit kind: fits 2 blocks, not 3
        let kind = sorts.kind_of(nat);
        let real0 = sb.first_available_variable();
        // Populate caches at the small width.
        sb.sort_function(sig, plus);
        let _ = sb.get_remapped_leq_relation(sorts, nat, real0);
        let _ = sb.gt_relation_remapped(kind, real0);
        let small_width = sb.universe.num_vars();

        sb.ensure_real_capacity(64);
        assert!(sb.universe.num_vars() > small_width);
        // (a) widened cached remap == direct build in the wide universe (cache-hit path).
        assert_eq!(
            sb.get_remapped_leq_relation(sorts, nat, real0),
            sb.leq_relation_at(sorts, nat, real0)
        );
        assert_eq!(sb.gt_relation_remapped(kind, real0), sb.gt_relation_at(sorts, kind, real0));
        // (b) the sort function survived the domain-region relocation.
        check_sort_function_pointwise(&mut sb, sig, plus);
        // (c) end-to-end solve in the regrown instance.
        let bound = vec![(nat, TTerm::App(plus, vec![TTerm::Var(0), TTerm::Var(1)]))];
        check_solve(&mut sb, sig, &[nat, int, rat], &bound, "regrown tower k=3");
    }

    /// A too-small initial capacity grown by `solve` itself (the driver-protocol path) gives the
    /// same solution set as a comfortably sized instance.
    #[test]
    fn solve_grows_real_capacity_on_demand() {
        let (e, s, plus, _, _) = tower();
        let (rat, int, nat) = (s[0], s[1], s[3]);
        let sig = e.signature();
        let bound = vec![(int, TTerm::App(plus, vec![TTerm::Var(0), TTerm::Var(1)]))];
        let mut small = SortBdds::new(sig.sorts(), 4);
        let mut big = SortBdds::new(sig.sorts(), DEFAULT_REAL_CAPACITY);
        let (got_small, _) = solve(&mut small, sig, &[nat, int, rat], &bound);
        let (got_big, _) = solve(&mut big, sig, &[nat, int, rat], &bound);
        assert_eq!(got_small, got_big);
    }

    /// Spec test 5: AllSat don't-care expansion — a don't-care variable inside the range yields
    /// every concrete completion, low-first; binary counting order pinned on a constant-true
    /// formula; the false formula and the empty-range edge behave like the reference.
    #[test]
    fn all_sat_dont_care_expansion() {
        let universe = BddVariableSet::new_anonymous(4);
        let v = universe.variables();
        // f = v0 ∧ v2 over [0, 2]: v1 is a don't-care on the single path.
        let f = universe.mk_literal(v[0], true).and(&universe.mk_literal(v[2], true));
        let mut all_sat = AllSat::new(f, 0, 2);
        let mut seq = Vec::new();
        while all_sat.next_assignment() {
            seq.push(all_sat.current_assignment().to_vec());
        }
        assert_eq!(
            seq,
            vec![
                vec![Some(true), Some(false), Some(true)],
                vec![Some(true), Some(true), Some(true)],
            ]
        );

        // Constant true over [0, 1]: all four assignments by binary counting, 00 01 10 11.
        let mut all_sat = AllSat::new(universe.mk_true(), 0, 1);
        let mut seq = Vec::new();
        while all_sat.next_assignment() {
            seq.push(all_sat.current_assignment().to_vec());
        }
        assert_eq!(
            seq,
            vec![
                vec![Some(false), Some(false)],
                vec![Some(false), Some(true)],
                vec![Some(true), Some(false)],
                vec![Some(true), Some(true)],
            ]
        );

        // False formula: no assignments.
        let mut all_sat = AllSat::new(universe.mk_false(), 0, 3);
        assert!(!all_sat.next_assignment());

        // Empty range (no free variables): exactly one empty assignment.
        let mut all_sat = AllSat::new(universe.mk_true(), 3, 2);
        assert!(all_sat.next_assignment());
        assert!(all_sat.current_assignment().is_empty());
        assert!(!all_sat.next_assignment());
    }

    /// The eager relations mirror `Sorts::leq` membership: each leq relation accepts exactly the
    /// down-set's local indices, evaluated by plugging constant index vectors into
    /// `apply_leq_relation`.
    #[test]
    fn leq_relations_match_sorts_leq() {
        let (e, s, ..) = tower();
        let sorts = e.sorts();
        let sb = SortBdds::new(sorts, DEFAULT_REAL_CAPACITY);
        let kind_id = sorts.kind_of(s[0]);
        let kind = sorts.kind(kind_id);
        let bits = sb.nr_variables(kind_id);
        for (si, &target) in kind.index_order.iter().enumerate() {
            for (ti, &t) in kind.index_order.iter().enumerate() {
                let args = sb.make_index_vector(bits, ti as u32);
                let b = sb.apply_leq_relation(kind_id, si as u32, &args);
                assert!(b.is_true() || b.is_false());
                assert_eq!(b.is_true(), sorts.leq(t, target), "leq({t:?}, {target:?})");
            }
        }
    }
}
