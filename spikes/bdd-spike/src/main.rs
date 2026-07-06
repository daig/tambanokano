//! S0 BDD spike (subsystems-goal.md, phase S step 0).
//!
//! Prototypes the order-sorted-unification sort computation — Maude's `SortBdds`
//! (src/Core/sortBdds.cc), the per-symbol sort functions (src/Core/sortTable.cc,
//! linear algorithm), generalized-sort composition (`operatorCompose` /
//! `computeGeneralizedSort`), the maximal-sort-assignment constraint
//! (src/Higher/unificationProblem.cc findOrderSortedUnifiers) and the `AllSat`
//! enumeration walk (src/Utility/allSat.cc) — on `biodivine-lib-bdd`.
//!
//! BuDDy-isms and their biodivine replacements (all safe ops, no `unsafe` renames):
//!   * bdd_replace (block remap):   relations are built DIRECTLY at the needed
//!     variable positions from the subsort bitsets (they are cheap DNFs), or the
//!     remap is done functionally: exists B . (f /\ (B <-> B')).
//!   * bdd_veccompose:              sequential `Bdd::substitute`, sound here
//!     because substituted functions never mention any pending scratch variable.
//!   * bdd_appall(op=nand, vars):   `Bdd::binary_op_with_for_all(_, _, nand, vars)`.
//!
//! Variable layout per problem instance (scratch low, real variables high, like
//! Maude; `maximal` never contains scratch vars, so the canonical BDD over the
//! real variables — and hence the AllSat enumeration order — is layout-independent):
//!   [scratch1: maxbits][scratch2: maxbits][domain: maxdom][real blocks ...]

use biodivine_lib_bdd::*;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::time::Instant;

// ---------------------------------------------------------------------------
// Signature model
// ---------------------------------------------------------------------------

/// A connected component of sorts. Sort index 0 is the error (kind) sort; the
/// index order is a linear extension with supersorts first, so leq[s] only
/// contains indices >= s, matching Maude.
struct Component {
    n_sorts: usize,
    bits: u16,
    /// leq[s] = ascending sort indices t with t <= s (including s itself);
    /// leq[0] = all sorts.
    leq: Vec<Vec<u32>>,
}

struct OpDecl {
    domain: Vec<u32>, // sort index per argument (component fixed by the symbol)
    range: u32,
}

struct Symbol {
    arg_comps: Vec<usize>,
    range_comp: usize,
    decls: Vec<OpDecl>,
}

struct Module {
    comps: Vec<Component>,
    syms: Vec<Symbol>,
}

fn calculate_nr_bits(nr_indices: usize) -> u16 {
    // Port of SortBdds::calculateNrBits: bits needed for 0..nr_indices-1, min 1.
    let mut nr_bits = 1u16;
    let mut representable = 2usize;
    while representable < nr_indices {
        nr_bits += 1;
        representable <<= 1;
    }
    nr_bits
}

impl Component {
    /// Build a component from parent lists: parents[i-1] = indices of direct
    /// supersorts of sort i (all >= 1, all < i). Sort 0 is the error sort.
    fn from_parents(n_sorts: usize, parents: &[Vec<u32>]) -> Component {
        assert!(n_sorts <= 128, "spike uses u128 bitsets");
        let mut below = vec![0u128; n_sorts]; // below[s] = bitset of t <= s
        for i in (1..n_sorts).rev() {
            below[i] |= 1u128 << i;
            let snapshot = below[i];
            for &p in &parents[i - 1] {
                below[p as usize] |= snapshot;
            }
        }
        below[0] = if n_sorts == 128 {
            u128::MAX
        } else {
            (1u128 << n_sorts) - 1
        };
        let leq = below
            .iter()
            .map(|&b| (0..n_sorts as u32).filter(|&t| b >> t & 1 == 1).collect())
            .collect();
        Component {
            n_sorts,
            bits: calculate_nr_bits(n_sorts),
            leq,
        }
    }

    fn random(n_sorts: usize, rng: &mut SmallRng) -> Component {
        // Each proper sort after the first gets 1-2 supersorts among earlier ones.
        let mut parents: Vec<Vec<u32>> = Vec::new();
        for i in 1..n_sorts {
            let mut ps = Vec::new();
            if i >= 2 {
                ps.push(rng.gen_range(1..i) as u32);
                if rng.gen_bool(0.3) {
                    let p2 = rng.gen_range(1..i) as u32;
                    if !ps.contains(&p2) {
                        ps.push(p2);
                    }
                }
            }
            parents.push(ps);
        }
        Component::from_parents(n_sorts, &parents)
    }
}

// ---------------------------------------------------------------------------
// SortBdds
// ---------------------------------------------------------------------------

struct SortBdds {
    universe: BddVariableSet,
    vars: Vec<BddVariable>,
    maxbits: u16,
    scratch2: u16, // first variable of the gt second-argument block
    domain0: u16,  // first variable of the sort-function domain block
    real0: u16,    // first real variable
    /// Per component: valid(s1) /\ valid(s2) /\ s1 > s2 over scratch1 x scratch2.
    gt: Vec<Bdd>,
    /// Per component, per sort s: valid(x) /\ x <= s over scratch1.
    leq: Vec<Vec<Bdd>>,
    /// Per symbol: range-component-bits BDDs over the domain block (built on
    /// demand in Maude; built eagerly here so construction cost is measured).
    sort_fns: Vec<Vec<Bdd>>,
}

impl SortBdds {
    fn new(module: &Module, real_capacity: u16) -> SortBdds {
        let maxbits = module.comps.iter().map(|c| c.bits).max().unwrap_or(1);
        let maxdom = module
            .syms
            .iter()
            .map(|s| {
                s.arg_comps
                    .iter()
                    .map(|&c| module.comps[c].bits)
                    .sum::<u16>()
            })
            .max()
            .unwrap_or(0);
        let scratch2 = maxbits;
        let domain0 = 2 * maxbits;
        let real0 = domain0 + maxdom;
        let universe = BddVariableSet::new_anonymous(real0 + real_capacity);
        let vars = universe.variables();

        let mut sb = SortBdds {
            universe,
            vars,
            maxbits,
            scratch2,
            domain0,
            real0,
            gt: Vec::new(),
            leq: Vec::new(),
            sort_fns: Vec::new(),
        };

        // gt relation per component (SortBdds constructor part 1).
        for comp in &module.comps {
            let b = sb.gt_second_arg_at(comp, sb.scratch2);
            sb.gt.push(b);
        }

        // leq relation per sort (SortBdds constructor part 2).
        for comp in &module.comps {
            let per_sort: Vec<Bdd> = (0..comp.n_sorts)
                .map(|s| sb.leq_at(comp, s as u32, 0))
                .collect();
            sb.leq.push(per_sort);
        }

        // Sort function per symbol (SortTable::linearComputeSortFunctionBdds).
        for sym in &module.syms {
            let f = sb.build_sort_fn(module, sym);
            sb.sort_fns.push(f);
        }
        sb
    }

    fn set_index_bits(&self, cube: &mut BddPartialValuation, first: u16, bits: u16, index: u32) {
        for k in 0..bits {
            cube.set_value(self.vars[(first + k) as usize], index >> k & 1 == 1);
        }
    }

    /// makeIndexVector: constant-bit BDD vector encoding a sort index.
    fn index_vector(&self, bits: u16, index: u32) -> Vec<Bdd> {
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

    /// valid(x) /\ x <= sort with x encoded at variables first..first+bits-1.
    /// Direct construction replaces BuDDy's cached-relation + bdd_replace.
    fn leq_at(&self, comp: &Component, sort: u32, first: u16) -> Bdd {
        let cubes: Vec<BddPartialValuation> = comp.leq[sort as usize]
            .iter()
            .map(|&t| {
                let mut cube = BddPartialValuation::empty();
                self.set_index_bits(&mut cube, first, comp.bits, t);
                cube
            })
            .collect();
        self.universe.mk_dnf(&cubes)
    }

    /// gt relation for a component with its second argument at block `first`
    /// (replaces the secondArgToReal bdd_replace in findOrderSortedUnifiers).
    fn gt_second_arg_at(&self, comp: &Component, first: u16) -> Bdd {
        let mut cubes: Vec<BddPartialValuation> = Vec::new();
        for s1 in 0..comp.n_sorts as u32 {
            for &s2 in &comp.leq[s1 as usize] {
                if s2 != s1 {
                    let mut cube = BddPartialValuation::empty();
                    self.set_index_bits(&mut cube, 0, comp.bits, s1);
                    self.set_index_bits(&mut cube, first, comp.bits, s2);
                    cubes.push(cube);
                }
            }
        }
        self.universe.mk_dnf(&cubes)
    }

    /// Production path for per-free-variable relation remaps (BuDDy's
    /// bdd_replace): clone the cached relation and shift one block upward.
    /// The shift is order-preserving — the target block lies above every
    /// variable of the source BDD — so the O(nodes) in-place relabel is sound.
    /// Validated against direct DNF construction in main().
    fn shift_block(&self, b: &Bdd, from: u16, bits: u16, to: u16) -> Bdd {
        let mut b = b.clone();
        let map: std::collections::HashMap<BddVariable, BddVariable> = (0..bits)
            .map(|j| (self.vars[(from + j) as usize], self.vars[(to + j) as usize]))
            .collect();
        unsafe { b.rename_variables(&map) };
        b
    }

    /// bdd_veccompose(leq[comp][sort] over scratch1, args): sequential substitute,
    /// sound because args never mention scratch1 (SortBdds::applyLeqRelation).
    fn apply_leq_relation(&self, comp_idx: usize, sort: u32, args: &[Bdd]) -> Bdd {
        let mut b = self.leq[comp_idx][sort as usize].clone();
        for (i, g) in args.iter().enumerate() {
            b = b.substitute(self.vars[i], g);
        }
        b
    }

    /// SortTable::linearComputeSortFunctionBdds (production also runs the
    /// recursive sort-diagram version; same output, comparable op profile).
    fn build_sort_fn(&self, module: &Module, sym: &Symbol) -> Vec<Bdd> {
        let rcomp = &module.comps[sym.range_comp];
        let rbits = rcomp.bits;
        if sym.arg_comps.is_empty() {
            // Constant: its single non-error sort (spike: first declaration).
            let s = sym.decls.first().map(|d| d.range).unwrap_or(0);
            return self.index_vector(rbits, s);
        }
        // Start with the constant ERROR_SORT (index 0) function.
        let mut f = self.index_vector(rbits, 0);
        for decl in sym.decls.iter().rev() {
            // All arguments <= the declaration's domain sorts.
            let mut cond = self.universe.mk_true();
            let mut pos = self.domain0;
            for (j, &d) in decl.domain.iter().enumerate() {
                let comp = &module.comps[sym.arg_comps[j]];
                cond = cond.and(&self.leq_at(comp, d, pos));
                pos += comp.bits;
            }
            // ... and the currently computed sort is NOT <= our range sort.
            let cur_leq_range = self.apply_leq_relation(sym.range_comp, decl.range, &f);
            cond = cond.and_not(&cur_leq_range);
            // ite update per output bit.
            let range_bits = self.index_vector(rbits, decl.range);
            for k in 0..rbits as usize {
                f[k] = Bdd::if_then_else(&cond, &range_bits[k], &f[k]);
            }
        }
        f
    }

    /// SortBdds::operatorCompose — bdd_veccompose of the sort function with the
    /// argument bit-vectors (which are over real variables only).
    fn operator_compose(&self, sym_idx: usize, input_bits: &[Bdd]) -> Vec<Bdd> {
        self.sort_fns[sym_idx]
            .iter()
            .map(|b| {
                let mut b = b.clone();
                for (i, g) in input_bits.iter().enumerate() {
                    b = b.substitute(self.vars[self.domain0 as usize + i], g);
                }
                b
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Terms and generalized sorts (DagNode::computeGeneralizedSort)
// ---------------------------------------------------------------------------

enum Term {
    Var(usize),            // free variable index
    App(usize, Vec<Term>), // symbol index, children
}

struct Problem<'a> {
    module: &'a Module,
    sb: &'a SortBdds,
    /// (component, declared sort, first real variable) per free variable.
    var_blocks: Vec<(usize, u32, u16)>,
}

impl<'a> Problem<'a> {
    fn new(module: &'a Module, sb: &'a SortBdds, var_sorts: &[(usize, u32)]) -> Problem<'a> {
        let mut next = sb.real0;
        let mut var_blocks = Vec::new();
        for &(comp, sort) in var_sorts {
            var_blocks.push((comp, sort, next));
            next += module.comps[comp].bits;
        }
        Problem {
            module,
            sb,
            var_blocks,
        }
    }

    fn last_real_var(&self) -> u16 {
        let &(comp, _, first) = self.var_blocks.last().unwrap();
        first + self.module.comps[comp].bits - 1
    }

    /// Bit-vector for the (as yet unknown) sort of a term over the free
    /// variables' real blocks.
    fn generalized_sort(&self, t: &Term) -> Vec<Bdd> {
        match t {
            Term::Var(v) => {
                let (comp, _, first) = self.var_blocks[*v];
                (0..self.module.comps[comp].bits)
                    .map(|k| {
                        self.sb
                            .universe
                            .mk_literal(self.sb.vars[(first + k) as usize], true)
                    })
                    .collect()
            }
            Term::App(sym, children) => {
                let mut inputs = Vec::new();
                for c in children {
                    inputs.extend(self.generalized_sort(c));
                }
                self.sb.operator_compose(*sym, &inputs)
            }
        }
    }

    /// findOrderSortedUnifiers: the `unifier` BDD (free-variable leq constraints
    /// plus bound-variable constraints term-sort <= bound var's sort), then the
    /// `maximal` BDD, both over the real variables only.
    fn build_maximal(&self, bound: &[(u32, usize, Term)]) -> (Bdd, Bdd) {
        self.build_maximal_with(bound, false)
    }

    fn build_maximal_with(&self, bound: &[(u32, usize, Term)], use_rename: bool) -> (Bdd, Bdd) {
        let sb = self.sb;
        let mut unifier = sb.universe.mk_true();
        for &(comp, sort, first) in &self.var_blocks {
            let leq = if use_rename {
                let c = &self.module.comps[comp];
                sb.shift_block(&sb.leq[comp][sort as usize], 0, c.bits, first)
            } else {
                sb.leq_at(&self.module.comps[comp], sort, first)
            };
            unifier = unifier.and(&leq);
        }
        for (sort, comp, term) in bound {
            let gen = self.generalized_sort(term);
            unifier = unifier.and(&sb.apply_leq_relation(*comp, *sort, &gen));
        }
        if unifier.is_false() {
            return (unifier.clone(), unifier);
        }

        let mut maximal = unifier.clone();
        let scratch1: Vec<BddVariable> = (0..sb.maxbits as usize).map(|i| sb.vars[i]).collect();
        for &(comp_idx, _, first) in &self.var_blocks {
            let comp = &self.module.comps[comp_idx];
            let bits = comp.bits as usize;
            // gt with its second argument on this variable's real block.
            let gt = if use_rename {
                sb.shift_block(&sb.gt[comp_idx], sb.scratch2, comp.bits, first)
            } else {
                sb.gt_second_arg_at(comp, first)
            };
            // unifier with this variable's block functionally renamed to scratch1:
            //   exists block . (unifier /\ (block <-> scratch1))
            let mut iff_conj = sb.universe.mk_true();
            let mut block_vars = Vec::with_capacity(bits);
            for j in 0..bits {
                let bv = sb.vars[first as usize + j];
                block_vars.push(bv);
                let l = sb.universe.mk_literal(bv, true);
                let r = sb.universe.mk_literal(scratch1[j], true);
                iff_conj = iff_conj.and(&l.iff(&r));
            }
            let renamed =
                Bdd::binary_op_with_exists(&unifier, &iff_conj, op_function::and, &block_vars);
            // forall Y in scratch1 . not(gt(Y, X_fv) /\ unifier[X_fv := Y])
            let nand = |l: Option<bool>, r: Option<bool>| match (l, r) {
                (Some(false), _) | (_, Some(false)) => Some(true),
                (Some(true), Some(true)) => Some(false),
                _ => None,
            };
            maximal = maximal.and(&Bdd::binary_op_with_for_all(
                &gt,
                &renamed,
                nand,
                &scratch1[..bits],
            ));
            assert!(!maximal.is_false(), "maximal false though unifier isn't");
        }
        (unifier, maximal)
    }

    /// Decode an AllSat assignment (over the real variables) to sort indices.
    fn decode(&self, assignment: &[i8]) -> Vec<u32> {
        self.var_blocks
            .iter()
            .map(|&(comp, _, first)| {
                let bits = self.module.comps[comp].bits;
                let mut s = 0u32;
                for k in 0..bits {
                    if assignment[(first + k) as usize] == 1 {
                        s |= 1 << k;
                    }
                }
                s
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// AllSat — verbatim port of src/Utility/allSat.cc
// ---------------------------------------------------------------------------

const UNDEFINED: i8 = -1;

struct AllSat<'a> {
    formula: &'a Bdd,
    first_variable: usize,
    last_variable: usize,
    node_stack: Vec<BddPointer>,
    dont_care_set: Vec<usize>,
    assignment: Vec<i8>,
    first_assignment: bool,
}

impl<'a> AllSat<'a> {
    fn new(formula: &'a Bdd, first_variable: usize, last_variable: usize) -> AllSat<'a> {
        AllSat {
            formula,
            first_variable,
            last_variable,
            node_stack: Vec::with_capacity(last_variable - first_variable + 1),
            dont_care_set: Vec::with_capacity(last_variable - first_variable + 1),
            assignment: Vec::new(),
            first_assignment: true,
        }
    }

    fn next_assignment(&mut self) -> bool {
        if self.first_assignment {
            if self.formula.is_false() {
                return false;
            }
            self.assignment = vec![UNDEFINED; self.last_variable + 1];
            self.forward(self.formula.root_pointer());
            self.first_assignment = false;
            return true;
        }
        // Try to find another way of assigning to don't care variables.
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
        for i in 0..nr_dont_cares {
            self.assignment[self.dont_care_set[i]] = UNDEFINED;
        }
        self.dont_care_set.clear();
        // Try to find another route to true through the BDD.
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

    fn forward(&mut self, mut b: BddPointer) {
        assert!(!b.is_zero(), "false BDD");
        // There must be at least one path to true from b; find the least one.
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
        // Any variables of interest not assigned on this path are don't cares.
        for i in self.first_variable..=self.last_variable {
            if self.assignment[i] == UNDEFINED {
                self.assignment[i] = 0;
                self.dont_care_set.push(i);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Pointwise reference evaluators (validation)
// ---------------------------------------------------------------------------

fn leq_contains(comp: &Component, sub: u32, sup: u32) -> bool {
    comp.leq[sup as usize].contains(&sub)
}

/// Pointwise evaluation of the linear sort-function algorithm.
fn pointwise_sort(module: &Module, sym: &Symbol, args: &[u32]) -> u32 {
    let rcomp = &module.comps[sym.range_comp];
    let mut result = 0u32; // ERROR_SORT
    for decl in sym.decls.iter().rev() {
        let fits = decl
            .domain
            .iter()
            .enumerate()
            .all(|(j, &d)| leq_contains(&module.comps[sym.arg_comps[j]], args[j], d));
        if fits && !leq_contains(rcomp, result, decl.range) {
            result = decl.range;
        }
    }
    result
}

fn pointwise_term_sort(module: &Module, t: &Term, var_sorts: &[u32]) -> u32 {
    match t {
        Term::Var(v) => var_sorts[*v],
        Term::App(sym_idx, children) => {
            let sym = &module.syms[*sym_idx];
            let args: Vec<u32> = children
                .iter()
                .map(|c| pointwise_term_sort(module, c, var_sorts))
                .collect();
            pointwise_sort(module, sym, &args)
        }
    }
}

// ---------------------------------------------------------------------------
// Scenario construction
// ---------------------------------------------------------------------------

/// The prelude number tower: [K] Rat Int NzRat Nat NzInt Zero NzNat (simplified).
fn number_tower() -> Module {
    // index:      0    1    2    3      4    5      6     7
    // sort:      [K]  Rat  Int  NzRat  Nat  NzInt  Zero  NzNat
    let parents = vec![
        vec![],     // Rat (1)
        vec![1],    // Int   < Rat
        vec![1],    // NzRat < Rat
        vec![2],    // Nat   < Int
        vec![2, 3], // NzInt < Int, NzRat
        vec![4],    // Zero  < Nat
        vec![4, 5], // NzNat < Nat, NzInt
    ];
    let comp = Component::from_parents(8, &parents);
    let plus = Symbol {
        arg_comps: vec![0, 0],
        range_comp: 0,
        decls: vec![
            OpDecl { domain: vec![7, 7], range: 7 }, // NzNat NzNat -> NzNat
            OpDecl { domain: vec![4, 4], range: 4 }, // Nat Nat -> Nat
            OpDecl { domain: vec![2, 2], range: 2 }, // Int Int -> Int
            OpDecl { domain: vec![1, 1], range: 1 }, // Rat Rat -> Rat
        ],
    };
    let minus = Symbol {
        arg_comps: vec![0],
        range_comp: 0,
        decls: vec![
            OpDecl { domain: vec![2], range: 2 }, // - : Int -> Int
            OpDecl { domain: vec![1], range: 1 }, // - : Rat -> Rat
        ],
    };
    let times = Symbol {
        arg_comps: vec![0, 0],
        range_comp: 0,
        decls: vec![
            OpDecl { domain: vec![7, 7], range: 7 },
            OpDecl { domain: vec![4, 4], range: 4 },
            OpDecl { domain: vec![5, 5], range: 5 }, // NzInt NzInt -> NzInt
            OpDecl { domain: vec![2, 2], range: 2 },
            OpDecl { domain: vec![3, 3], range: 3 }, // NzRat NzRat -> NzRat
            OpDecl { domain: vec![1, 1], range: 1 },
        ],
    };
    Module {
        comps: vec![comp],
        syms: vec![plus, minus, times],
    }
}

fn random_symbol(
    module_comps: &[Component],
    arity: usize,
    n_decls: usize,
    rng: &mut SmallRng,
) -> Symbol {
    let n_comps = module_comps.len();
    let range_comp = rng.gen_range(0..n_comps);
    let arg_comps: Vec<usize> = (0..arity).map(|_| rng.gen_range(0..n_comps)).collect();
    let decls = (0..n_decls)
        .map(|_| OpDecl {
            domain: arg_comps
                .iter()
                .map(|&c| rng.gen_range(1..module_comps[c].n_sorts.max(2)) as u32)
                .collect(),
            range: rng.gen_range(1..module_comps[range_comp].n_sorts.max(2)) as u32,
        })
        .collect();
    Symbol {
        arg_comps,
        range_comp,
        decls,
    }
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

fn validate_sort_functions(module: &Module, sb: &SortBdds, samples: usize, rng: &mut SmallRng) {
    for (si, sym) in module.syms.iter().enumerate() {
        let arity = sym.arg_comps.len();
        if arity == 0 {
            continue;
        }
        let exhaustive: usize = sym
            .arg_comps
            .iter()
            .map(|&c| module.comps[c].n_sorts)
            .product();
        let tuples: Vec<Vec<u32>> = if exhaustive <= 4096 {
            let mut all = vec![vec![]];
            for &c in &sym.arg_comps {
                let n = module.comps[c].n_sorts as u32;
                all = all
                    .into_iter()
                    .flat_map(|t: Vec<u32>| {
                        (0..n).map(move |s| {
                            let mut t2 = t.clone();
                            t2.push(s);
                            t2
                        })
                    })
                    .collect();
            }
            all
        } else {
            (0..samples)
                .map(|_| {
                    sym.arg_comps
                        .iter()
                        .map(|&c| rng.gen_range(0..module.comps[c].n_sorts) as u32)
                        .collect()
                })
                .collect()
        };
        for args in tuples {
            let expected = pointwise_sort(module, sym, &args);
            // Plug constant index vectors into the sort function.
            let mut inputs = Vec::new();
            for (j, &a) in args.iter().enumerate() {
                inputs.extend(sb.index_vector(module.comps[sym.arg_comps[j]].bits, a));
            }
            let composed = sb.operator_compose(si, &inputs);
            let mut actual = 0u32;
            for (k, bit) in composed.iter().enumerate() {
                assert!(bit.is_true() || bit.is_false(), "non-constant bit");
                if bit.is_true() {
                    actual |= 1 << k;
                }
            }
            assert_eq!(expected, actual, "sort fn mismatch: sym {si} args {args:?}");
        }
    }
}

/// Brute-force maximal order-sorted solutions, in no particular order.
fn brute_force_maximal(
    module: &Module,
    problem: &Problem,
    bound: &[(u32, usize, Term)],
) -> Vec<Vec<u32>> {
    let k = problem.var_blocks.len();
    let mut all: Vec<Vec<u32>> = vec![vec![]];
    for &(comp, _, _) in &problem.var_blocks {
        let n = module.comps[comp].n_sorts as u32;
        all = all
            .into_iter()
            .flat_map(|t: Vec<u32>| {
                (0..n).map(move |s| {
                    let mut t2 = t.clone();
                    t2.push(s);
                    t2
                })
            })
            .collect();
    }
    let satisfies = |tuple: &[u32]| -> bool {
        for (v, &(comp, declared, _)) in problem.var_blocks.iter().enumerate() {
            if !leq_contains(&module.comps[comp], tuple[v], declared) {
                return false;
            }
        }
        for (sort, comp, term) in bound {
            let ts = pointwise_term_sort(module, term, tuple);
            if !leq_contains(&module.comps[*comp], ts, *sort) {
                return false;
            }
        }
        true
    };
    let sat: Vec<Vec<u32>> = all.into_iter().filter(|t| satisfies(t)).collect();
    sat.iter()
        .filter(|t| {
            // maximal: no single coordinate can be raised (strictly, per gt)
            // while remaining satisfying.
            !(0..k).any(|v| {
                let (comp, _, _) = problem.var_blocks[v];
                let c = &module.comps[comp];
                (0..c.n_sorts as u32).any(|y| {
                    y != t[v] && leq_contains(c, t[v], y) && {
                        let mut t2 = (*t).clone();
                        t2[v] = y;
                        satisfies(&t2)
                    }
                })
            })
        })
        .cloned()
        .collect()
}

fn validate_unification(
    module: &Module,
    sb: &SortBdds,
    var_sorts: &[(usize, u32)],
    bound: Vec<(u32, usize, Term)>,
    label: &str,
) -> usize {
    let problem = Problem::new(module, sb, var_sorts);
    let (_unifier, maximal) = problem.build_maximal(&bound);
    // The unsafe-rename remap path must produce the identical canonical BDD.
    let (_u2, maximal2) = problem.build_maximal_with(&bound, true);
    assert_eq!(maximal, maximal2, "rename path diverges ({label})");
    let mut enumerated = Vec::new();
    let mut all_sat = AllSat::new(&maximal, sb.real0 as usize, problem.last_real_var() as usize);
    while all_sat.next_assignment() {
        enumerated.push(problem.decode(&all_sat.assignment));
    }
    // Set-compare against brute force.
    let mut expected = brute_force_maximal(module, &problem, &bound);
    let mut got = enumerated.clone();
    expected.sort();
    got.sort();
    assert_eq!(expected, got, "maximal solution set mismatch ({label})");
    // Cross-check the count against the BDD's cardinality over the real range
    // (maximal depends only on real variables, so its total cardinality is
    // count-over-range * 2^outside).
    let range = problem.last_real_var() as usize - sb.real0 as usize + 1;
    let outside = sb.universe.num_vars() as usize - range;
    let count = maximal.exact_cardinality() >> outside;
    assert_eq!(
        count,
        num_bigint::BigInt::from(enumerated.len()),
        "AllSat count vs cardinality ({label})"
    );
    enumerated.len()
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

fn time_it<F: FnMut()>(mut f: F) -> f64 {
    // Median-of-5 wall time in microseconds.
    let mut runs = Vec::new();
    for _ in 0..5 {
        let t = Instant::now();
        f();
        runs.push(t.elapsed().as_secs_f64() * 1e6);
    }
    runs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    runs[2]
}

fn bench_construction() {
    println!("\n== B1: SortBdds relation construction (gt + all leq, per component) ==");
    for &n in &[8usize, 16, 32, 64, 128] {
        let mut rng = SmallRng::seed_from_u64(42);
        let comp = Component::random(n, &mut rng);
        let module = Module {
            comps: vec![comp],
            syms: vec![],
        };
        let mut nodes = (0usize, 0usize);
        let us = time_it(|| {
            let sb = SortBdds::new(&module, 64);
            nodes = (sb.gt[0].size(), sb.leq[0].iter().map(|b| b.size()).sum());
        });
        println!(
            "  {n:>3} sorts ({} bits): {us:>9.1} us   gt nodes {} | leq nodes total {}",
            module.comps[0].bits, nodes.0, nodes.1
        );
    }
}

fn bench_sort_functions() {
    println!("\n== B2: per-symbol sort functions (linear algorithm) ==");
    for &(n_sorts, arity, n_decls) in &[
        (16usize, 1usize, 4usize),
        (16, 2, 4),
        (16, 3, 4),
        (16, 2, 8),
        (32, 2, 4),
        (32, 4, 8),
    ] {
        let mut rng = SmallRng::seed_from_u64(7);
        let comp = Component::random(n_sorts, &mut rng);
        let comps = vec![comp];
        let sym = random_symbol(&comps, arity, n_decls, &mut rng);
        let module = Module {
            comps,
            syms: vec![sym],
        };
        let sb_base = SortBdds::new(
            &Module {
                comps: module.comps.iter().map(clone_component).collect(),
                syms: vec![],
            },
            64,
        );
        let mut nodes = 0usize;
        let us = time_it(|| {
            let f = sb_base.build_sort_fn(&module, &module.syms[0]);
            nodes = f.iter().map(|b| b.size()).sum();
        });
        println!(
            "  {n_sorts:>3} sorts, arity {arity}, {n_decls} decls: {us:>9.1} us (sort fn only)   fn nodes {nodes}"
        );
    }
}

fn clone_component(c: &Component) -> Component {
    Component {
        n_sorts: c.n_sorts,
        bits: c.bits,
        leq: c.leq.clone(),
    }
}

fn prelude_scale_module(rng: &mut SmallRng) -> Module {
    // Modeled on the flattened prelude/META-LEVEL: ~25 components, mostly tiny,
    // a few mid-sized; ~300 symbols, mostly low arity with 1-4 declarations.
    let sizes = [
        2usize, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 6, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 9,
    ];
    let comps: Vec<Component> = sizes.iter().map(|&n| Component::random(n, rng)).collect();
    let mut syms = Vec::new();
    for _ in 0..100 {
        syms.push(random_symbol(&comps, 0, 1, rng));
    }
    for _ in 0..60 {
        syms.push(random_symbol(&comps, 1, rng.gen_range(1..4), rng));
    }
    for _ in 0..100 {
        syms.push(random_symbol(&comps, 2, rng.gen_range(1..5), rng));
    }
    for _ in 0..30 {
        syms.push(random_symbol(&comps, 3, rng.gen_range(1..4), rng));
    }
    for _ in 0..10 {
        syms.push(random_symbol(&comps, 4, rng.gen_range(1..3), rng));
    }
    Module { comps, syms }
}

fn bench_prelude_scale() {
    println!("\n== B3: prelude-scale module (25 components, 300 symbols, eager) ==");
    let mut rng = SmallRng::seed_from_u64(2026);
    let module = prelude_scale_module(&mut rng);
    let mut total_nodes = 0usize;
    let us = time_it(|| {
        let sb = SortBdds::new(&module, 128);
        total_nodes = sb.sort_fns.iter().flatten().map(|b| b.size()).sum::<usize>()
            + sb.gt.iter().map(|b| b.size()).sum::<usize>()
            + sb.leq.iter().flatten().map(|b| b.size()).sum::<usize>();
    });
    println!(
        "  full SortBdds + all 300 sort functions: {:.2} ms   total nodes {}",
        us / 1e3,
        total_nodes
    );
    println!("  (Maude builds sort functions lazily per symbol; this is the worst case.)");
}

fn bench_unification() {
    println!("\n== B4/B6: unification sort-solving (constraints + maximality + AllSat) ==");
    for &(n_sorts, k) in &[(16usize, 2usize), (16, 5), (16, 10), (32, 5), (128, 5)] {
        // Search seeds for a satisfiable instance so the maximality machinery
        // actually runs (random declared sorts + a bound constraint are often
        // contradictory, which only exercises the cheap early-out).
        let mut chosen = None;
        for seed in 0..200u64 {
            let mut rng = SmallRng::seed_from_u64(seed);
            let comp = Component::random(n_sorts, &mut rng);
            let comps = vec![comp];
            let plus = random_symbol(&comps, 2, 4, &mut rng);
            let module = Module {
                comps,
                syms: vec![plus],
            };
            let var_sorts: Vec<(usize, u32)> = (0..k)
                .map(|_| (0usize, rng.gen_range(1..n_sorts as u32)))
                .collect();
            let bound: Vec<(u32, usize, Term)> = if k >= 2 {
                vec![(
                    rng.gen_range(1..n_sorts as u32),
                    0,
                    Term::App(0, vec![Term::Var(0), Term::Var(1)]),
                )]
            } else {
                vec![]
            };
            let sb = SortBdds::new(&module, 128);
            let problem = Problem::new(&module, &sb, &var_sorts);
            let (u, _m) = problem.build_maximal(&bound);
            if !u.is_false() {
                chosen = Some((module, var_sorts, bound));
                break;
            }
            if seed == 199 {
                // Random bound constraints stay unsatisfiable at this scale
                // (random declarations almost always compute the error sort);
                // fall back to the always-satisfiable free-variable-only case.
                chosen = Some((module, var_sorts, vec![]));
            }
        }
        let (module, var_sorts, bound) = chosen.expect("no satisfiable instance found");
        let sb = SortBdds::new(&module, 128);
        let problem = Problem::new(&module, &sb, &var_sorts);
        let mut n_solutions = 0usize;
        let mut max_nodes = 0usize;
        let build_us = time_it(|| {
            let (_u, m) = problem.build_maximal(&bound);
            max_nodes = m.size();
        });
        let rename_us = time_it(|| {
            let (_u, m) = problem.build_maximal_with(&bound, true);
            max_nodes = m.size();
        });
        let (_u, maximal) = problem.build_maximal(&bound);
        let enum_us = time_it(|| {
            let mut all_sat = AllSat::new(
                &maximal,
                sb.real0 as usize,
                problem.last_real_var() as usize,
            );
            n_solutions = 0;
            while all_sat.next_assignment() {
                n_solutions += 1;
            }
        });
        println!(
            "  {n_sorts:>3} sorts, {k:>2} free vars: build {build_us:>9.1} us (direct DNF) / {rename_us:>9.1} us (rename) | enumerate {n_solutions:>5} maximal solutions in {enum_us:>9.1} us | maximal nodes {max_nodes}"
        );
    }
}

/// A component with one top sort and m incomparable sorts below it, plus a
/// unary symbol g with one declaration per mid sort (g : Ai -> Ai). The
/// constraint sortOf(g(X)) <= top forces X into the antichain, giving exactly
/// m maximal solutions per variable — m^k for k variables. This is the AllSat
/// stress shape (many incomparable maximal assignments).
fn diamond_module(m: usize) -> Module {
    // sorts: 0 = error, 1 = top T, 2..2+m = A1..Am (all < T, pairwise incomparable)
    let mut ps: Vec<Vec<u32>> = vec![vec![]]; // T has no parents
    for _ in 0..m {
        ps.push(vec![1]);
    }
    let comp = Component::from_parents(2 + m, &ps);
    let g = Symbol {
        arg_comps: vec![0],
        range_comp: 0,
        decls: (0..m)
            .map(|i| OpDecl {
                domain: vec![2 + i as u32],
                range: 2 + i as u32,
            })
            .collect(),
    };
    Module {
        comps: vec![comp],
        syms: vec![g],
    }
}

fn bench_many_solutions() {
    println!("\n== B7: many maximal solutions (antichain; AllSat enumeration throughput) ==");
    for &(m, k) in &[(4usize, 5usize), (4, 6), (8, 4), (14, 4)] {
        let module = diamond_module(m);
        let sb = SortBdds::new(&module, 128);
        let var_sorts: Vec<(usize, u32)> = (0..k).map(|_| (0usize, 1u32)).collect();
        let bound: Vec<(u32, usize, Term)> = (0..k)
            .map(|v| (1u32, 0usize, Term::App(0, vec![Term::Var(v)])))
            .collect();
        let problem = Problem::new(&module, &sb, &var_sorts);
        let mut max_nodes = 0usize;
        let build_us = time_it(|| {
            let (_u, mx) = problem.build_maximal(&bound);
            max_nodes = mx.size();
        });
        let (_u, maximal) = problem.build_maximal(&bound);
        let mut n_solutions = 0usize;
        let enum_us = time_it(|| {
            let mut all_sat = AllSat::new(
                &maximal,
                sb.real0 as usize,
                problem.last_real_var() as usize,
            );
            n_solutions = 0;
            while all_sat.next_assignment() {
                n_solutions += 1;
            }
        });
        assert_eq!(n_solutions, m.pow(k as u32), "expected m^k solutions");
        println!(
            "  antichain {m:>2}, {k} vars: build {build_us:>9.1} us | enumerate {n_solutions:>6} solutions in {enum_us:>9.1} us ({:.1} ns/solution) | maximal nodes {max_nodes}",
            enum_us * 1e3 / n_solutions as f64
        );
    }
}

fn bench_deep_compose() {
    println!("\n== B5: generalized sort of a deep term (veccompose chain) ==");
    // Use the number tower's `+` so the composed sort function stays
    // non-degenerate at every depth.
    let module = number_tower();
    let sb = SortBdds::new(&module, 128);
    fn make(depth: usize) -> Term {
        if depth == 0 {
            Term::Var(0)
        } else if depth == 1 {
            Term::App(0, vec![Term::Var(0), Term::Var(1)])
        } else {
            Term::App(0, vec![make(depth - 1), make(depth - 1)])
        }
    }
    for &depth in &[3usize, 6, 8] {
        let term = make(depth);
        let var_sorts = vec![(0usize, 1u32), (0, 2)];
        let problem = Problem::new(&module, &sb, &var_sorts);
        let mut nodes = 0usize;
        let us = time_it(|| {
            let bits = problem.generalized_sort(&term);
            nodes = bits.iter().map(|b| b.size()).sum();
        });
        println!(
            "  depth {depth} ({} applications): {us:>9.1} us   result bits nodes {nodes}",
            (1usize << depth) - 1
        );
    }
}

// ---------------------------------------------------------------------------

fn main() {
    println!("bdd-spike: S0 gate — SortBdds + AllSat on biodivine-lib-bdd 0.5.27");

    // ---- Validation ----
    println!("\n== validation ==");
    let tower = number_tower();
    let sb = SortBdds::new(&tower, 64);
    let mut rng = SmallRng::seed_from_u64(1);
    validate_sort_functions(&tower, &sb, 200, &mut rng);
    println!("  number tower: sort functions match pointwise semantics (exhaustive)");

    // X:Nat, Y:Int, Z:Rat free; a bound constraint (X + Y) must fit in Int.
    let n1 = validate_unification(
        &tower,
        &sb,
        &[(0, 4), (0, 2), (0, 1)],
        vec![(2, 0, Term::App(0, vec![Term::Var(0), Term::Var(1)]))],
        "tower k=3 + bound",
    );
    println!("  number tower: {n1} maximal solutions match brute force + cardinality");

    let n2 = validate_unification(&tower, &sb, &[(0, 1), (0, 1)], vec![], "tower k=2 free");
    println!("  number tower: {n2} maximal solutions (free case) match brute force");

    // Random modules: sort functions + unification end-to-end.
    for seed in 0..10u64 {
        let mut rng = SmallRng::seed_from_u64(seed);
        let n_sorts = rng.gen_range(4..24);
        let comp = Component::random(n_sorts, &mut rng);
        let comps = vec![comp];
        let s1 = random_symbol(&comps, 2, rng.gen_range(1..5), &mut rng);
        let s2 = random_symbol(&comps, 1, rng.gen_range(1..4), &mut rng);
        let module = Module {
            comps,
            syms: vec![s1, s2],
        };
        let sb = SortBdds::new(&module, 64);
        validate_sort_functions(&module, &sb, 100, &mut rng);
        let k = rng.gen_range(2..5);
        let var_sorts: Vec<(usize, u32)> = (0..k)
            .map(|_| (0usize, rng.gen_range(0..n_sorts as u32)))
            .collect();
        let bound = vec![(
            rng.gen_range(1..n_sorts as u32),
            0usize,
            Term::App(0, vec![Term::App(1, vec![Term::Var(0)]), Term::Var(1)]),
        )];
        validate_unification(&module, &sb, &var_sorts, bound, &format!("random seed {seed}"));
    }
    println!("  10 random modules: sort functions + maximal solution sets all match");

    // Diamond antichain: many incomparable maximal solutions — exercises the
    // AllSat backtracking and don't-care paths for real.
    let diamond = diamond_module(3);
    let dsb = SortBdds::new(&diamond, 64);
    let n3 = validate_unification(
        &diamond,
        &dsb,
        &[(0, 1), (0, 1)],
        vec![
            (1, 0, Term::App(0, vec![Term::Var(0)])),
            (1, 0, Term::App(0, vec![Term::Var(1)])),
        ],
        "diamond m=3 k=2",
    );
    assert_eq!(n3, 9);
    println!("  diamond antichain: {n3} maximal solutions (3^2) match brute force");

    // ---- Benchmarks ----
    bench_construction();
    bench_sort_functions();
    bench_prelude_scale();
    bench_unification();
    bench_many_solutions();
    bench_deep_compose();

    println!("\ndone.");
}
