//! The [`Engine`] — the instantiable owner of all runtime state (decision **D1**: no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! Internally it is split (Stage A4 / review R3 H1) into an immutable-during-reduction `Signature`
//! (sorts, symbols, compiled equations) and a mutable `Runtime` (the GC'd DAG arena, roots, and
//! rewrite statistics): matching and instantiation hold a *shared* borrow of the signature while
//! mutating the runtime, so a rewrite instantiates an equation's right-hand side straight out of
//! the still-borrowed equation table — no defensive clone. [`Engine`] is a thin facade that
//! re-exposes the same public API over the two halves.
//!
//! It computes each node's least sort at construction and runs garbage collection (decision **D2**:
//! non-moving mark-sweep) over the DAG from an explicit root set.

use crate::arena::Arena;
use crate::dag::{DagId, DagNode, NaValue, NodeTerm};
use crate::num::Nat;
use crate::root::{RootGuard, Roots};
use crate::sort::{SortId, Sorts};
use crate::symbol::{Axioms, OpDeclaration, SpecialOp, Symbol, SymbolId, Theory};
use crate::term::{ConditionFragment, Equation, Membership, Subst, Term};
use crate::theory::LhsAutomaton;
use std::cmp::Ordering;
use std::collections::HashMap;

/// An equation as stored in the engine: its left-hand side compiled to a theory [`LhsAutomaton`]
/// (decision D3 / review R3 C1), with the right-hand side and variable count kept for instantiation.
/// The public [`Equation`] (lhs as a [`Term`]) is compiled into this by [`Engine::add_equation`].
struct CompiledEquation {
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    /// Condition fragments (empty for an unconditional `eq`); all must hold for the equation to apply,
    /// and a failed condition backtracks into the next matcher solution (B2.3).
    condition: Vec<CompiledFragment>,
    /// `[owise]`: this equation is tried only if no non-owise equation of the symbol applies (B2.3b).
    owise: bool,
}

/// A membership axiom `mb lhs : sort` compiled for the engine: its lhs as a theory [`LhsAutomaton`]
/// plus the target sort and variable count. The public [`Membership`] is compiled into this by
/// [`Signature::add_membership`]. (Conditional `cmb` gains a condition in B2.3.)
struct SortConstraint {
    lhs: LhsAutomaton,
    sort: SortId,
    nr_vars: u32,
    /// Condition fragments (empty for an unconditional `mb`); checked under the membership match's
    /// substitution before the sort is lowered (B2.3c `cmb`).
    condition: Vec<CompiledFragment>,
}

/// A condition fragment compiled for evaluation: like the public [`ConditionFragment`] but with the
/// matching fragment's pattern compiled to an [`LhsAutomaton`]. Built by
/// [`Signature::compile_condition`]. The `fresh_vars` of a matching fragment are unbound before each
/// match attempt so backtracking re-binds cleanly.
enum CompiledFragment {
    Equality { lhs: Term, rhs: Term },
    SortTest { term: Term, sort: SortId },
    Matching { pattern: LhsAutomaton, subject: Term, fresh_vars: Vec<u32> },
}

/// One pending node-normalization on the iterative [`Engine::reduce`] work-stack.
///
/// A frame mirrors one activation of the old recursive `reduce`/`reduce_args` pair: it reduces the
/// arguments selected by the operator's evaluation strategy (the standard one is every argument
/// left-to-right; `cursor` walks the strategy via [`Signature::strat_position`]), replacing each in
/// `args`, then drives the top-rewrite fixpoint by *reusing its own slot* for each rewritten term.
///
/// **A2 safe-point-GC contract** (the reason this is an explicit heap stack). The frames hold most
/// in-flight `DagId`s of an in-progress reduction — but *not all*: at the [`Engine::reduce`] loop
/// head a just-completed child sits only in the `child_result` local until it is delivered into its
/// parent's `args` on the next iteration. So the complete root set at the loop head is
/// `walk(stack) ∪ child_result`. GC must therefore be confined to the loop head:
/// `try_rewrite_top`/`instantiate`/`make_free` build fresh nodes whose ids live only in native-stack
/// locals (`instantiate`'s `arg_ids`, the `Subst` bindings, the `rebuilt` node mid-rewrite) and are
/// *not* discoverable by a stack walk, so they must not be safe points.
struct ReduceFrame {
    /// The node this frame started from; returned unchanged when no child changed (preserves the
    /// shared DAG id rather than rebuilding an identical node).
    original: DagId,
    symbol: SymbolId,
    /// The original children of `original`, copied out so the spine can be walked across the `&mut
    /// self` reductions that may grow (and thus reallocate) the arena. The change test is `args != orig`.
    orig: Vec<DagId>,
    /// Current arguments: `orig` with each strategy-reduced position replaced by its normal form;
    /// positions the strategy leaves unreduced keep their `orig` value (lazy). The node is rebuilt from
    /// this.
    args: Vec<DagId>,
    /// Strategy steps taken so far — the cursor into the operator's strategy (or `0..arity` for the
    /// standard strategy); [`Signature::strat_position`] maps it to the argument position to reduce.
    cursor: usize,
}

/// The immutable-during-reduction half of the engine: the sort poset, the symbol table, and the
/// compiled equation set. Matching, instantiation, and reduction take this by shared reference, so
/// the [`Runtime`] can mutate the DAG arena while the equation table stays borrowed.
pub(crate) struct Signature {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    /// Unconditional equations (LHS compiled to a theory automaton), indexed by lhs top symbol.
    equations: HashMap<SymbolId, Vec<CompiledEquation>>,
    /// Membership axioms (`mb`), indexed by lhs top symbol; applied to lower a node's least sort at
    /// construction (B2.2). Empty in modules without memberships — the construction hot path checks
    /// `memberships.is_empty()` before doing any per-node work, so the free reduce path is untouched.
    memberships: HashMap<SymbolId, Vec<SortConstraint>>,
    /// Bumped whenever the equation set changes; stamped into nodes when they are proved canonical,
    /// so `add_equation` invalidates stale "reduced" results (review R2 H2). `0` is the "never
    /// reduced" sentinel stored on nodes, so this starts at `1`.
    eq_epoch: u32,
}

/// The mutable half of the engine: the garbage-collected DAG arena, the GC root registry, and the
/// rewrite statistics. Operations that consult the signature (sorts/symbols/equations) take a
/// `&Signature`; everything else is pure arena work.
#[derive(Default)]
pub(crate) struct Runtime {
    dags: Arena<DagNode>,
    /// Count of equational rewrites applied (Maude's `rewrites` statistic).
    rewrite_count: u64,
    /// Persistent GC roots held by live [`RootGuard`]s (decision D2 amendment). `gc` always marks
    /// from here; the shared `Rc<RefCell<…>>` lets a guard outlive a `&mut self` call.
    roots: Roots,
    /// If `Some(n)`, [`reduce`](Engine::reduce) collects at its loop head once this many DAG nodes
    /// have been allocated since the last collection — letting one large reduction run in bounded
    /// memory. `None` (default) disables in-reduction GC (callers collect between reductions).
    gc_interval: Option<u64>,
    /// DAG nodes allocated since the last collection (drives `gc_interval`).
    allocs_since_gc: u64,
}

#[derive(Default)]
pub struct Engine {
    sig: Signature,
    rt: Runtime,
}

impl Default for Signature {
    fn default() -> Self {
        Signature {
            sorts: Sorts::default(),
            symbols: Arena::default(),
            equations: HashMap::default(),
            memberships: HashMap::default(),
            eq_epoch: 1, // 0 is the "never reduced" sentinel stored on nodes
        }
    }
}

// ======================================================================================
// Signature: sorts, symbols, equations (immutable during a reduction)
// ======================================================================================

impl Signature {
    pub(crate) fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.add_sort(name)
    }
    pub(crate) fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sorts.add_subsort(sub, sup);
    }
    pub(crate) fn close_sorts(&mut self) {
        self.sorts.close();
    }
    pub(crate) fn sorts(&self) -> &Sorts {
        &self.sorts
    }

    pub(crate) fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms::default(),
            identity: None,
            strategy: None,
            special: None,
        })
    }

    /// Register an **ACU** operator (`assoc comm`, optionally with a two-sided `id:`). The operator
    /// must be binary (Maude requires associative operators to be binary); its arguments are stored
    /// flattened as a multiset and matched modulo AC(+U). `identity` is the constant symbol declared
    /// as `id: <const>`, or `None`.
    pub(crate) fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc comm` operator must be binary");
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: true, comm: true, idem: false, iter: false },
            identity,
            strategy: None,
            special: None,
        });
        self.commutative_sort_completion(id); // an asymmetric initial decl needs its swap
        id
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; its arguments are stored as a flattened ordered sequence and matched modulo
    /// associativity (with extension).
    pub(crate) fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc` operator must be binary");
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: true, comm: false, idem: false, iter: false },
            identity,
            strategy: None,
            special: None,
        })
    }

    /// Register a **CUI** operator (`comm`, not associative, optionally `idem` and/or `id:`). Must be
    /// binary; its two arguments are stored in canonical order and matched modulo commutativity
    /// (idempotence and identity collapse `f(a,a)`/`f(a,e)` to a single element at construction).
    pub(crate) fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "a `comm` operator must be binary");
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: false, comm: true, idem, iter: false },
            identity,
            strategy: None,
            special: None,
        });
        self.commutative_sort_completion(id); // an asymmetric initial decl needs its swap
        id
    }

    /// Register an **S** (`iter`) operator: a unary stacked successor `s_` (Maude's `[iter]`). Its nodes
    /// store the iteration count compactly as `s^count(arg)` and match modulo the successor extension.
    /// Must be unary; not commutative, so no declaration completion.
    pub(crate) fn add_op_iter(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        assert_eq!(domain.len(), 1, "an `iter` operator must be unary");
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { iter: true, ..Default::default() },
            identity: None,
            strategy: None,
            special: None,
        })
    }
    pub(crate) fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading). All
    /// declarations of an operator must agree on arity; least-sort resolution walks them in the order
    /// added, so the *original* `add_op*` declaration stays first (the tie-break favours it). Must be
    /// called before any node of `sym` is built (sorts are cached at construction). The parser (B4) is
    /// the eventual real source; this is the hand-built-module entry point.
    pub(crate) fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        {
            let s = self.symbols.get_mut(sym);
            assert_eq!(
                s.decls[0].domain.len(),
                domain.len(),
                "overloaded declarations of `{}` must agree on arity",
                s.name()
            );
            s.decls.push(OpDeclaration { domain, range, ctor: false });
        }
        // Keep a commutative operator's declaration set complete under argument swap (no-op for free
        // and AU operators, whose declarations stay positional).
        self.commutative_sort_completion(sym);
    }

    /// Maude's `BinarySymbol::commutativeSortCompletion` (`Interface/binarySymbol.cc`): a commutative
    /// operator's declaration set is completed so that every **asymmetric** declaration `[a, b] -> r`
    /// also carries its swapped form `[b, a] -> r` (same range, same `ctor`), unless one is already
    /// present.
    ///
    /// Maude builds a *positional* sort diagram from the declarations and folds it left-to-right over
    /// an ACU multiset / CUI pair (`ACU_DagNode::argVecComputeBaseSort` → `computeMultSortIndex`);
    /// [`compute_sort`](Self::compute_sort) likewise checks `arg_sorts[i] <= decl.domain[i]`
    /// **positionally**. Commutativity requires either argument order to yield the same least sort,
    /// but the canonical element order (by [`dag_compare`](Runtime::dag_compare)) can present the
    /// lower-sorted element first — so without the swapped declaration an asymmetric overload such as
    /// NAT's `_+_ : NzNat Nat -> NzNat` would compute an argument-order-dependent (wrong) least sort
    /// (e.g. `z + nz : Nat` instead of `NzNat`). Completing the set restores order-independence
    /// without changing the fold. Idempotent (a swap's swap is the original, already present), so it is
    /// safe to run after each declaration is registered. AU (associative, non-commutative) and free
    /// operators are left untouched — their argument order is significant.
    fn commutative_sort_completion(&mut self, sym: SymbolId) {
        let s = self.symbols.get(sym);
        if !matches!(s.theory(), Theory::Acu | Theory::Cui) {
            return; // only commutative theories complete; AU / free stay positional
        }
        // Snapshot the current declarations so the shared borrow ends before the mutable push below
        // (the sort ids are `Copy`, so this clone is cheap and small).
        let decls: Vec<OpDeclaration> = s.decls.clone();
        let mut to_add: Vec<OpDeclaration> = Vec::new();
        for d in &decls {
            if d.domain.len() != 2 || d.domain[0] == d.domain[1] {
                continue; // a symmetric (or non-binary) declaration is its own swap
            }
            let swapped = vec![d.domain[1], d.domain[0]];
            let present = decls
                .iter()
                .chain(to_add.iter())
                .any(|e| e.domain == swapped && e.range == d.range && e.ctor == d.ctor);
            if !present {
                to_add.push(OpDeclaration { domain: swapped, range: d.range, ctor: d.ctor });
            }
        }
        self.symbols.get_mut(sym).decls.extend(to_add);
    }

    /// Mark every declaration of `sym` as a constructor (`[ctor]`, B2.4). Metadata only — it does not
    /// change reduction; recorded for the later constructor analysis.
    pub(crate) fn set_ctor(&mut self, sym: SymbolId) {
        for decl in &mut self.symbols.get_mut(sym).decls {
            decl.ctor = true;
        }
    }

    /// Set an evaluation strategy `strat (raw…)` on `sym` (B2.4). `raw` is the user sequence of 1-based
    /// argument positions ending in a single trailing `0` (reduce at top) — e.g. `[1, 0]` for a lazy
    /// `if_then_else_fi`. Stored as the 0-based positions to reduce, in order; arguments not listed are
    /// left unreduced. The general strategy (interleaved or absent `0`) is a follow-up — loud-assert.
    pub(crate) fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        let arity = self.symbols.get(sym).arity();
        assert_eq!(
            raw.last(),
            Some(&0),
            "evaluation strategy {raw:?} for `{}` must end in a single trailing 0 (reduce at top); \
             interleaved or absent top rewrites are a B-follow-up",
            self.symbols.get(sym).name()
        );
        let positions = &raw[..raw.len() - 1];
        assert!(
            positions.iter().all(|&p| p >= 1 && p as usize <= arity),
            "evaluation strategy {raw:?} for `{}` references an argument outside 1..={arity} (or has a \
             non-trailing 0)",
            self.symbols.get(sym).name()
        );
        self.symbols.get_mut(sym).strategy = Some(positions.iter().map(|&p| p - 1).collect());
    }

    /// Attach a built-in reduction rule (`special (id-hook …)`, B3) to `sym`. The op-hook/term-hook
    /// references are passed already resolved to [`SymbolId`]s (the future parser does the resolution;
    /// for now the hand-built module supplies them). A [`SpecialOp::Branch`] is intrinsically lazy, so
    /// this installs its `strat (1 0)` (condition eager, branches lazy) — the real `if_then_else_fi`
    /// carries no user `strat`, so the seam wires it here (cf. the B2.4 lazy-strat mechanism).
    pub(crate) fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        if let SpecialOp::Branch { .. } = op {
            assert!(
                self.symbols.get(sym).strategy.is_none(),
                "`{}` is a Branch operator; its laziness is installed by the seam — it must not also \
                 carry a user strat",
                self.symbols.get(sym).name()
            );
            self.set_strategy(sym, &[1, 0]); // reduce the condition (arg 1) only, then the top rewrite
        }
        self.symbols.get_mut(sym).special = Some(op);
    }

    /// The argument position to reduce at strategy step `cursor` for `symbol` (B2.4), or `None` once the
    /// strategy is exhausted (→ attempt the top rewrite). The standard strategy reduces every argument
    /// left-to-right; a custom strategy reduces only its listed positions, in order.
    pub(crate) fn strat_position(&self, symbol: SymbolId, cursor: usize, arity: usize) -> Option<usize> {
        match &self.symbols.get(symbol).strategy {
            None => (cursor < arity).then_some(cursor),
            Some(positions) => positions.get(cursor).map(|&p| p as usize),
        }
    }

    /// Least sort of `symbol(args…)` whose arguments have sorts `arg_sorts`, under multi-declaration
    /// overloading — Maude's `findMinSortIndex` (sortTable.cc:369). The least sort is the minimum of
    /// the *applicable* declarations' range sorts (a declaration is applicable iff every `arg_sorts[i]
    /// <= decl.domain[i]`), breaking incomparable (non-preregular) ties toward the **earliest**
    /// declaration. Reproduced directly by intersecting range **down-sets** in declaration order
    /// (correctness-first; the flattened sort-diagram decision table is a later perf step). No
    /// applicable declaration → the error sort of the range's kind.
    pub(crate) fn compute_sort(&self, symbol: SymbolId, arg_sorts: &[SortId]) -> SortId {
        self.compute_sort_uniq(symbol, arg_sorts).0
    }

    /// [`compute_sort`](Self::compute_sort) plus the **preregularity** bit: `true` iff the least sort
    /// is unique (the running down-set intersection equals the chosen range's down-set — Maude's
    /// `unique` flag). Maude *warns* when this is false; we compute it but defer the user-facing
    /// warning (no diagnostics sink yet) — the tie-break itself is exercised by conformance.
    pub(crate) fn compute_sort_uniq(&self, symbol: SymbolId, arg_sorts: &[SortId]) -> (SortId, bool) {
        let decls = self.symbols.get(symbol).decls();
        assert_eq!(
            arg_sorts.len(),
            decls[0].domain.len(),
            "arity mismatch building `{}`",
            self.symbols.get(symbol).name()
        );
        // Fast path: a single declaration (no overloading — every free/theory op in practice). Its
        // range is the unique least sort when applicable, else the kind's error sort. Avoids the
        // per-node down-set clone the general path does, keeping the reduce hot path allocation-free.
        if let [only] = decls {
            let applicable =
                arg_sorts.iter().zip(&only.domain).all(|(&a, &dom)| self.sorts.leq(a, dom));
            return if applicable {
                (only.range, true)
            } else {
                (self.sorts.error_sort(self.sorts.kind_of(only.range)), true)
            };
        }
        debug_assert!(
            decls.iter().all(|d| self.sorts.kind_of(d.range) == self.sorts.kind_of(decls[0].range)),
            "cross-kind ad-hoc overloading of `{}` is not yet supported (a B2 follow-up): the args, \
             not the range, would select the declaration group",
            self.symbols.get(symbol).name()
        );
        // Walk declarations in order, intersecting applicable range down-sets. `running` is the
        // down-set of the GLB so far; `min_range` is the earliest range that is <= everything so far.
        let mut min_range: Option<SortId> = None;
        let mut running: Option<std::collections::BTreeSet<SortId>> = None;
        for d in decls {
            if !arg_sorts.iter().zip(&d.domain).all(|(&a, &dom)| self.sorts.leq(a, dom)) {
                continue; // declaration not applicable to these argument sorts
            }
            let down = self.sorts.down_set(d.range);
            match &mut running {
                None => {
                    running = Some(down.clone());
                    min_range = Some(d.range);
                }
                Some(r) => {
                    r.retain(|x| down.contains(x)); // intersect with this range's down-set
                    if *r == *down {
                        min_range = Some(d.range); // d.range <= everything so far ⇒ new minimum
                    }
                }
            }
        }
        match min_range {
            // unique iff the GLB's down-set (`running`) equals the chosen min's down-set ⇒ min is the GLB.
            Some(r) => (r, running.as_ref() == Some(self.sorts.down_set(r))),
            None => (self.sorts.error_sort(self.sorts.kind_of(decls[0].range)), true),
        }
    }

    /// Least sort of a theory (ACU/AU/CUI) node, folding the **binary** [`compute_sort`](Self::compute_sort)
    /// left-to-right over the canonical element sorts (Maude's `traverse(traverse(0, i1), i2)`). For the
    /// single binary declaration `[D, D] -> R` every B1 / conformance operator carries, this returns `R`
    /// iff all elements `<= D` (else the kind's error sort) — identical to the old per-theory
    /// `compute_*_sort` — and extends to subsort-overloaded AC later with no reshape. `elem_sorts` is
    /// non-empty (a canonical theory node holds ≥ 2 elements).
    pub(crate) fn compute_sort_fold(&self, symbol: SymbolId, elem_sorts: &[SortId]) -> SortId {
        let mut acc = elem_sorts[0];
        for &e in &elem_sorts[1..] {
            acc = self.compute_sort(symbol, &[acc, e]);
        }
        acc
    }

    /// Least sort of an **S** node `s^count(arg)` (Maude's `S_Symbol::computeBaseSort` /
    /// `SortPath::computeSortIndex`). The successor's unary sort function, iterated over the argument
    /// sort, is eventually periodic (it maps a finite kind into itself), so the sort follows a **lead**
    /// prefix then a **cycle**: `count` in the lead indexes the prefix directly, beyond it indexes into
    /// the cycle. For NAT (`s_ : Nat -> NzNat`) the path is `Zero ↦ NzNat ↦ NzNat …`, so `s^n(0)` is
    /// `NzNat` for every `n >= 1`. Correctness-first: the path is recomputed per call (Maude precomputes
    /// a `sortPathTable` per argument sort — a perf follow-up).
    pub(crate) fn compute_s_sort(&self, symbol: SymbolId, arg_sort: SortId, count: &Nat) -> SortId {
        let (seq, lead) = self.s_sort_path(symbol, arg_sort);
        let path_len = seq.len();
        // An S node always has count >= 1. The first `path_len` successors index the path directly.
        if let Some(c) = count.to_usize()
            && c <= path_len
        {
            return seq[c - 1];
        }
        // Past the lead: index into the cycle (Maude's `computeSortIndex` tail arithmetic).
        let cycle = path_len - lead;
        let steps =
            count.checked_sub(&Nat::from_u64((lead + 1) as u64)).expect("count > path_len >= lead+1");
        seq[lead + steps.rem_usize(cycle)]
    }

    /// The successor sort path from `arg_sort`: `seq[k]` = least sort of `s^(k+1)(arg)`, iterating the
    /// unary [`compute_sort`](Self::compute_sort) until a sort repeats; returns `(seq, lead)` where
    /// `lead` is the index at which the cycle begins. Pigeonhole-terminating (finite kind).
    fn s_sort_path(&self, symbol: SymbolId, arg_sort: SortId) -> (Vec<SortId>, usize) {
        let mut seq: Vec<SortId> = Vec::new();
        let mut cur = arg_sort;
        loop {
            cur = self.compute_sort(symbol, &[cur]);
            if let Some(p) = seq.iter().position(|&s| s == cur) {
                return (seq, p);
            }
            seq.push(cur);
        }
    }

    /// Register an unconditional equation, compiling its lhs to a theory `LhsAutomaton` once, and
    /// advance the equation epoch (see [`Engine::add_equation`]).
    pub(crate) fn add_equation(&mut self, eq: Equation) {
        self.push_equation(eq.lhs, eq.rhs, eq.nr_vars, Vec::new(), false);
    }

    /// Register a conditional equation `ceq lhs = rhs if condition` (B2.3): the condition is a list of
    /// [`ConditionFragment`]s (equality / sort-test), all of which must hold; a failure backtracks into
    /// the next matcher solution. `eq` stays the unconditional entry point (empty condition).
    pub(crate) fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.push_equation(lhs, rhs, nr_vars, condition, false);
    }

    /// Register an `[owise]` equation (optionally conditional): tried only if no non-owise equation of
    /// the symbol applies (Maude's `applyReplaceNoOwise` two-phase matching, B2.3b).
    pub(crate) fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.push_equation(lhs, rhs, nr_vars, condition, true);
    }

    fn push_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        owise: bool,
    ) {
        let top = lhs.top_symbol().expect("equation lhs must be an application");
        let compiled = CompiledEquation {
            lhs: LhsAutomaton::compile(lhs, self),
            rhs,
            nr_vars,
            condition: self.compile_condition(condition),
            owise,
        };
        self.equations.entry(top).or_default().push(compiled);
        // A term canonical under the old equation set may now be reducible: invalidate every
        // node's cached "reduced" stamp by advancing the epoch (review R2 H2).
        self.eq_epoch += 1;
    }

    /// Compile a condition (public [`ConditionFragment`]s) for evaluation: equality / sort-test
    /// fragments are stored as-is; a matching fragment's pattern is compiled to an [`LhsAutomaton`]
    /// (B2.3d) through the same A3 seam (and F-A guard) as an equation lhs.
    fn compile_condition(&self, condition: Vec<ConditionFragment>) -> Vec<CompiledFragment> {
        condition
            .into_iter()
            .map(|frag| match frag {
                ConditionFragment::Equality { lhs, rhs } => CompiledFragment::Equality { lhs, rhs },
                ConditionFragment::SortTest { term, sort } => CompiledFragment::SortTest { term, sort },
                ConditionFragment::Matching { pattern, subject, fresh_vars } => {
                    CompiledFragment::Matching {
                        pattern: LhsAutomaton::compile(pattern, self),
                        subject,
                        fresh_vars,
                    }
                }
            })
            .collect()
    }

    /// Register an (unconditional) membership axiom `mb lhs : sort`, compiling its lhs to a theory
    /// [`LhsAutomaton`] and indexing it by the lhs top symbol. A node's least sort is constrained at
    /// construction, so — like overload declarations — **memberships must be declared before any node
    /// of their lhs's symbol is built** (a node built earlier keeps its un-constrained sort). Does not
    /// bump `eq_epoch`: memberships refine sorts, not the `reduced` cache.
    pub(crate) fn add_membership(&mut self, mb: Membership) {
        self.push_membership(mb.lhs, mb.sort, mb.nr_vars, Vec::new());
    }

    /// Register a conditional membership `cmb lhs : sort if condition` (B2.3c): the sort is lowered
    /// only when the condition (the same [`ConditionFragment`]s as `ceq`) holds under the membership
    /// match's substitution. `mb` stays the unconditional entry point (empty condition).
    pub(crate) fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.push_membership(lhs, sort, nr_vars, condition);
    }

    fn push_membership(&mut self, lhs: Term, sort: SortId, nr_vars: u32, condition: Vec<ConditionFragment>) {
        let top = lhs.top_symbol().expect("membership lhs must be an application");
        let compiled = SortConstraint {
            lhs: LhsAutomaton::compile(lhs, self),
            sort,
            nr_vars,
            condition: self.compile_condition(condition),
        };
        let sorts = &self.sorts;
        let v = self.memberships.entry(top).or_default();
        v.push(compiled);
        // Order smallest-target-sort first (subsorts before supersorts), so the constrain pass lowers
        // a node straight to its smallest applicable sort in ONE application — matching the membership
        // count Maude reports (Maude also tries smallest-sort-first).
        v.sort_by(|x, y| {
            if x.sort == y.sort {
                Ordering::Equal
            } else if sorts.leq(x.sort, y.sort) {
                Ordering::Less
            } else if sorts.leq(y.sort, x.sort) {
                Ordering::Greater
            } else {
                x.sort.cmp(&y.sort) // incomparable: deterministic tie-break (non-confluent is a follow-up)
            }
        });
    }

    /// The current equation-set epoch (stamped into nodes proved canonical; see [`DagNode`]).
    pub(crate) fn eq_epoch(&self) -> u32 {
        self.eq_epoch
    }
}

// ======================================================================================
// Runtime: the DAG arena, GC, and the reduction subsystem (mutates; borrows the Signature)
// ======================================================================================

impl Runtime {
    // ---- DAG construction ----

    /// Allocate a node with a precomputed sort, accounting it against the safe-point-GC interval.
    /// (Shared by `make_free`/`make_acu`; the alloc counter only matters when `gc_interval` is set,
    /// so the default path is a no-op increment. Reset by `safe_point_gc`, so it can't overflow.)
    fn alloc_node(&mut self, sort: SortId, term: NodeTerm) -> DagId {
        if self.gc_interval.is_some() {
            self.allocs_since_gc += 1;
        }
        self.dags.alloc(DagNode { sort, reduced_epoch: 0, term })
    }

    /// Allocate a node, then apply the module's membership axioms (`mb`) to lower its least sort
    /// (B2.2). Skips all per-node work when the module declares no memberships (the free reduce hot
    /// path is untouched). The node must exist for a membership lhs to match against, so this runs
    /// post-alloc, on the constructed node.
    fn alloc_node_constrained(&mut self, sig: &Signature, sort: SortId, term: NodeTerm) -> DagId {
        let id = self.alloc_node(sort, term);
        if !sig.memberships.is_empty() {
            self.constrain_to_smaller_sort(sig, id);
        }
        id
    }

    /// Lower `id`'s cached least sort by the membership axioms of its top symbol (Maude's
    /// `constrainToSmallerSort`): repeatedly find the first membership — they are ordered
    /// **smallest-target-sort first** by [`add_membership`](Signature::add_membership) — whose target
    /// is strictly below the node's current sort and whose lhs matches, lower the node's sort to it,
    /// and retry from the top, to a fixpoint. **Each lowering counts as one rewrite** (Maude counts
    /// membership applications in its `rewrites` total); the smallest-first order means a node drops
    /// straight to its smallest applicable sort in one application, matching Maude's count. Non-confluent
    /// membership sets (incomparable applicable targets) and matching modulo AC/`iter` are follow-ups.
    fn constrain_to_smaller_sort(&mut self, sig: &Signature, id: DagId) {
        let symbol = self.node(id).symbol();
        let Some(constraints) = sig.memberships.get(&symbol) else { return };
        loop {
            let current = self.node(id).sort;
            let mut lowered = false;
            for sc in constraints {
                // Only a membership whose target is *strictly below* the current sort can refine it.
                if sc.sort == current || !sig.sorts().leq(sc.sort, current) {
                    continue;
                }
                if self.membership_applies(sig, sc, id) {
                    self.dags.get_mut(id).sort = sc.sort;
                    self.rewrite_count += 1; // a membership application counts as a rewrite (Maude)
                    lowered = true;
                    break; // restart the scan with the new, smaller sort
                }
            }
            if !lowered {
                break;
            }
        }
    }

    /// Whether the membership applies to node `id`: its compiled lhs matches *and* (for a `cmb`) its
    /// condition holds under that match. Reads through the A3 matcher seam, so a free lhs uses the
    /// recursive matcher and a theory lhs its own automaton. A condition that fails for one match
    /// solution backtracks into the next (B2.3c); the condition's own reductions count toward the
    /// rewrite total whether or not it ends up holding. (AC/`iter` membership matching is a follow-up.)
    fn membership_applies(&mut self, sig: &Signature, sc: &SortConstraint, id: DagId) -> bool {
        let mut subst = Subst::new();
        subst.reset(sc.nr_vars);
        let Some(mut sp) = sc.lhs.match_(self, sig, id, &mut subst, false) else {
            return false;
        };
        while sp.next(self, sig, &mut subst) {
            if sc.condition.is_empty() || self.condition_holds(sig, &sc.condition, &mut subst) {
                return true;
            }
        }
        false
    }

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub(crate) fn make_free(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        args: Vec<DagId>,
    ) -> DagId {
        // Keep the old `compute_free_sort` theory guard verbatim — its message must still name
        // `make_acu` (see `make_free_on_ac_operator_panics`); the arity check now lives in `compute_sort`.
        assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Free,
            "`{}` is an ACU operator — build it with make_acu/make_ac, not make_free",
            sig.symbol(symbol).name()
        );
        let sort = self.free_sort(sig, symbol, &args);
        self.alloc_node_constrained(sig, sort, NodeTerm::Free { symbol, args })
    }

    /// Least sort of a free node `symbol(args…)`. The common case — a single declaration, no
    /// overloading — is computed **inline** with no allocation (the equivalent of the old
    /// `compute_free_sort`), keeping the reduce hot path fast; only an overloaded free operator falls
    /// back to the general [`Signature::compute_sort`], which needs the argument sorts as a slice.
    fn free_sort(&self, sig: &Signature, symbol: SymbolId, args: &[DagId]) -> SortId {
        let decls = sig.symbol(symbol).decls();
        if let [only] = decls {
            assert_eq!(
                args.len(),
                only.domain.len(),
                "arity mismatch building `{}`",
                sig.symbol(symbol).name()
            );
            let well_sorted = only
                .domain
                .iter()
                .zip(args)
                .all(|(&dom, &arg)| sig.sorts().leq(self.dags.get(arg).sort, dom));
            return if well_sorted {
                only.range
            } else {
                sig.sorts().error_sort(sig.sorts().kind_of(only.range))
            };
        }
        let arg_sorts: Vec<SortId> = args.iter().map(|&a| self.dags.get(a).sort).collect();
        sig.compute_sort(symbol, &arg_sorts)
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub(crate) fn make_const(&mut self, sig: &Signature, symbol: SymbolId) -> DagId {
        self.make_free(sig, symbol, Vec::new())
    }

    /// Build a canonical **ACU** node for `symbol` from `raw_args` (`(element, multiplicity)` pairs).
    /// Canonicalizes to the AC(+U) normal form (Maude's `normalizeAtTop` → `insertAlien` →
    /// `sortAndUniquize`): (1) flatten arguments that are themselves `symbol`-rooted ACU nodes (scaling
    /// their multiplicities), (2) drop identity elements when the operator has `id:`, (3) merge equal
    /// elements (summing multiplicities) and sort by [`dag_compare`](Self::dag_compare), (4) collapse —
    /// an empty multiset is the identity element, a single element of multiplicity 1 is that element
    /// itself, otherwise an [`NodeTerm::Acu`] node. So the result is in normal form and equal ACU terms
    /// are structurally identical through the [`children`](crate::dag::DagNode::children) visitor.
    pub(crate) fn make_acu(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<(DagId, u32)>,
    ) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Acu, "make_acu on a non-ACU symbol");
        let identity = sig.symbol(symbol).identity();

        // (1) flatten nested same-symbol nodes + (2) drop identity elements.
        let mut flat: Vec<(DagId, u32)> = Vec::with_capacity(raw_args.len());
        for (arg, mult) in raw_args {
            if mult == 0 {
                continue;
            }
            if identity.is_some_and(|id_sym| self.is_constant(arg, id_sym)) {
                continue; // an identity argument vanishes
            }
            match &self.dags.get(arg).term {
                NodeTerm::Acu { symbol: inner, args } if *inner == symbol => {
                    for &(e, m) in args {
                        flat.push((e, m * mult));
                    }
                }
                _ => flat.push((arg, mult)),
            }
        }

        // (3) sort by the total order, then merge structurally-equal neighbours (summing mults).
        flat.sort_by(|&(x, _), &(y, _)| self.dag_compare(x, y));
        let mut args: Vec<(DagId, u32)> = Vec::with_capacity(flat.len());
        for (e, m) in flat {
            match args.last_mut() {
                Some(last) if self.dag_compare(last.0, e) == Ordering::Equal => last.1 += m,
                _ => args.push((e, m)),
            }
        }

        // (4) collapse to the canonical representative.
        let total: u64 = args.iter().map(|&(_, m)| u64::from(m)).sum();
        match total {
            0 => {
                let id_sym = identity.expect("an empty ACU multiset requires an identity element");
                self.make_const(sig, id_sym)
            }
            1 => args[0].0, // exactly one element, multiplicity 1 — never wrap a lone argument
            _ => {
                // Fold the binary least-sort over the multiset elements (with multiplicity repeats),
                // mirroring Maude's `traverse(traverse(0, i1), i2)` over the flattened arguments.
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
                    .collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node_constrained(sig, sort, NodeTerm::Acu { symbol, args })
            }
        }
    }

    /// Build a canonical **AU** node for `symbol` from `raw_args` (an ordered argument list). Mirrors
    /// [`make_acu`](Self::make_acu) for the associative-only theory: flatten arguments that are
    /// themselves `symbol`-rooted AU nodes (preserving order), drop identity elements, then collapse —
    /// empty → the identity, a single argument → that argument, else an [`NodeTerm::Au`] node. Order is
    /// significant, so there is **no** sorting or multiplicity merging.
    pub(crate) fn make_au(&mut self, sig: &Signature, symbol: SymbolId, raw_args: Vec<DagId>) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Au, "make_au on a non-AU symbol");
        let identity = sig.symbol(symbol).identity();
        let mut args: Vec<DagId> = Vec::with_capacity(raw_args.len());
        for arg in raw_args {
            if identity.is_some_and(|id_sym| self.is_constant(arg, id_sym)) {
                continue; // an identity argument vanishes
            }
            match &self.dags.get(arg).term {
                NodeTerm::Au { symbol: inner, args: inner_args } if *inner == symbol => {
                    args.extend_from_slice(inner_args);
                }
                _ => args.push(arg),
            }
        }
        match args.len() {
            0 => {
                let id_sym = identity.expect("an empty AU sequence requires an identity element");
                self.make_const(sig, id_sym)
            }
            1 => args[0],
            _ => {
                let elem_sorts: Vec<SortId> = args.iter().map(|&e| self.dags.get(e).sort).collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node_constrained(sig, sort, NodeTerm::Au { symbol, args })
            }
        }
    }

    /// Build a canonical **CUI** node for `symbol` from its two arguments. Applies the collapse axioms
    /// at construction (Maude keeps CUI terms in normal form): an identity argument (`id:`) drops the
    /// node to the other argument; idempotence (`idem`) drops `f(a, a)` to `a`; otherwise the two
    /// arguments are placed in canonical (sorted) order for commutativity. So `f(b, a)` and `f(a, b)`
    /// are the same node, and `f(a, a)`/`f(a, e)` collapse away for free (0 rewrites).
    pub(crate) fn make_cui(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        mut x: DagId,
        mut y: DagId,
    ) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Cui, "make_cui on a non-CUI symbol");
        let identity = sig.symbol(symbol).identity;
        let idem = sig.symbol(symbol).axioms.idem;
        if let Some(id_sym) = identity {
            if self.is_constant(x, id_sym) {
                return y;
            }
            if self.is_constant(y, id_sym) {
                return x;
            }
        }
        if idem && self.dag_compare(x, y) == Ordering::Equal {
            return x;
        }
        if self.dag_compare(x, y) == Ordering::Greater {
            std::mem::swap(&mut x, &mut y); // canonical order for commutativity
        }
        let sort = sig.compute_sort(symbol, &[self.dags.get(x).sort, self.dags.get(y).sort]);
        self.alloc_node_constrained(sig, sort, NodeTerm::Cui { symbol, args: vec![x, y] })
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)` (Maude's `S_DagNode::normalizeAtTop`):
    /// `count == 0` collapses to `arg` (`s^0(x) = x`); a nested same-symbol successor flattens
    /// (`s^j(s^k(x)) = s^(j+k)(x)` — one level suffices, the inner node is already normalized); otherwise
    /// an [`NodeTerm::S`] with the periodic least sort ([`compute_s_sort`](Signature::compute_s_sort)).
    pub(crate) fn make_s(&mut self, sig: &Signature, symbol: SymbolId, count: Nat, arg: DagId) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::S, "make_s on a non-S symbol");
        if count.is_zero() {
            return arg;
        }
        let (count, arg) = match &self.dags.get(arg).term {
            NodeTerm::S { symbol: inner, count: k, arg: inner_arg } if *inner == symbol => {
                (count.add(k), *inner_arg)
            }
            _ => (count, arg),
        };
        let arg_sort = self.dags.get(arg).sort;
        let sort = sig.compute_s_sort(symbol, arg_sort, &count);
        self.alloc_node_constrained(sig, sort, NodeTerm::S { symbol, count, arg })
    }

    /// Build an atomic **NA** constant node carrying `value` (a string/qid/float). The sort is
    /// `symbol`'s range (`symbol` is an arity-0 NA-constant symbol — Maude's `StringSymbol` etc.).
    pub(crate) fn make_na(&mut self, sig: &Signature, symbol: SymbolId, value: NaValue) -> DagId {
        let sort = sig.compute_sort(symbol, &[]);
        self.alloc_node_constrained(sig, sort, NodeTerm::Na { symbol, value })
    }

    /// Rebuild a node for `symbol` from `children` (the flattened child sequence), dispatching on the
    /// operator's theory: a free node directly, or a canonical ACU/AU/CUI/S node. Used by `reduce` when a
    /// child changed and by `instantiate`, so neither hard-codes the free constructor (which rejects
    /// theory symbols).
    pub(crate) fn rebuild(&mut self, sig: &Signature, symbol: SymbolId, children: Vec<DagId>) -> DagId {
        match sig.symbol(symbol).theory() {
            Theory::Free => self.make_free(sig, symbol, children),
            Theory::Acu => self.make_acu(sig, symbol, children.into_iter().map(|d| (d, 1)).collect()),
            Theory::Au => self.make_au(sig, symbol, children),
            Theory::Cui => {
                debug_assert_eq!(children.len(), 2, "a CUI node is binary");
                self.make_cui(sig, symbol, children[0], children[1])
            }
            // An iter `Op` layer (from `instantiate`) is one successor; `make_s` flattening folds nested
            // layers into a single `s^k`. `reduce` re-seats existing S nodes with their preserved count
            // directly (not through here), so this `s^1` semantics is only ever what `instantiate` wants.
            Theory::S => {
                debug_assert_eq!(children.len(), 1, "an S successor is unary");
                self.make_s(sig, symbol, Nat::one(), children[0])
            }
        }
    }

    /// Whether `arg` is the constant `id_sym()` (an arity-0 free node). Used to recognise identity
    /// arguments during ACU canonicalization.
    fn is_constant(&self, arg: DagId, id_sym: SymbolId) -> bool {
        matches!(
            &self.dags.get(arg).term,
            NodeTerm::Free { symbol, args } if *symbol == id_sym && args.is_empty()
        )
    }

    /// A **total order** on DAG nodes, consistent with structural (modulo-AC) equality — i.e.
    /// `dag_compare(a, b) == Equal` iff [`deep_equal`](Self::deep_equal)`(a, b)`. Mirrors C++
    /// `DagNode::compare`: order by top symbol first, then lexicographically by arguments (ACU nodes
    /// compare their canonical `(element, multiplicity)` sequences). This is the key the ACU
    /// canonicalizer sorts and uniquizes by. Recurses on *element* depth (like `match_pattern`,
    /// author-/data-shallow for the canonical subterms it compares); an iterative form is a follow-up
    /// if deep ACU elements ever appear.
    pub(crate) fn dag_compare(&self, a: DagId, b: DagId) -> Ordering {
        if a == b {
            return Ordering::Equal; // same node id — identical, prune
        }
        let (na, nb) = (self.dags.get(a), self.dags.get(b));
        match na.symbol().cmp(&nb.symbol()) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Equal top symbols ⇒ the same theory ⇒ the same `NodeTerm` arm.
        match (&na.term, &nb.term) {
            (NodeTerm::Free { args: xa, .. }, NodeTerm::Free { args: ya, .. }) => {
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(x, y) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal // same symbol ⇒ same arity ⇒ all pairs compared
            }
            (NodeTerm::Acu { args: xa, .. }, NodeTerm::Acu { args: ya, .. }) => {
                for (&(xe, xm), &(ye, ym)) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(xe, ye) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                    match xm.cmp(&ym) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                xa.len().cmp(&ya.len()) // a proper prefix orders before the longer sequence
            }
            // AU (ordered sequence) and CUI (canonically-ordered pair) compare the same way: an equal
            // top symbol means the same arm, so the cross cases can't arise.
            (NodeTerm::Au { args: xa, .. }, NodeTerm::Au { args: ya, .. })
            | (NodeTerm::Cui { args: xa, .. }, NodeTerm::Cui { args: ya, .. }) => {
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(x, y) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                xa.len().cmp(&ya.len()) // lexicographic, then by length
            }
            // S successor: the scalar `count` is part of identity (not a child), so compare it first,
            // then the argument (Maude's `S_DagNode::compareArguments`). This keeps the order consistent
            // with the `deep_equal` S-arm, so `s^2(0)` and `s^3(0)` order correctly inside an ACU subject.
            (NodeTerm::S { count: xc, arg: xa, .. }, NodeTerm::S { count: yc, arg: ya, .. }) => {
                match xc.cmp(yc) {
                    Ordering::Equal => self.dag_compare(*xa, *ya),
                    ord => ord,
                }
            }
            // An NA constant orders by its scalar value (consistent with the `deep_equal` Na arm).
            (NodeTerm::Na { value: xv, .. }, NodeTerm::Na { value: yv, .. }) => xv.cmp(yv),
            _ => unreachable!("equal top symbols must share a NodeTerm arm"),
        }
    }

    pub(crate) fn node(&self, id: DagId) -> &DagNode {
        self.dags.get(id)
    }
    pub(crate) fn sort_of(&self, id: DagId) -> SortId {
        self.dags.get(id).sort
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub(crate) fn live_nodes(&self) -> usize {
        self.dags.len()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub(crate) fn node_capacity(&self) -> usize {
        self.dags.capacity()
    }

    // ---- garbage collection (D2) ----

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives (see [`Engine::root`]).
    pub(crate) fn root(&self, id: DagId) -> RootGuard {
        RootGuard::new(&self.roots, id)
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`] or from `extra_roots`
    /// (see [`Engine::gc`]); returns the number reclaimed.
    pub(crate) fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.dags.clear_marks();
        self.mark_registered_roots();
        for root in extra_roots {
            self.mark_reachable(root);
        }
        self.dags.sweep(|_| {})
    }

    /// Mark (transitively) every root currently pinned by a [`RootGuard`].
    fn mark_registered_roots(&mut self) {
        // Collect first so the registry borrow is released before the `&mut self` mark walk.
        let pinned: Vec<DagId> = self.roots.borrow().live_roots().collect();
        for r in pinned {
            self.mark_reachable(r);
        }
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Engine::reduce) (see
    /// [`Engine::set_gc_interval`] for the rooting contract).
    pub(crate) fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.gc_interval = interval;
    }

    /// Collect at a `reduce` safe point, rooting the in-flight working set: the registry, plus every
    /// frame's term (`original`, which transitively covers its unreduced `orig` children) and its
    /// current `args` (the strategy-reduced positions are fresh nodes not reachable from `original`),
    /// plus the `child_result` not yet delivered into a frame. This is the complete loop-head root set
    /// (see the [`ReduceFrame`] safe-point contract); collecting anywhere else would miss fresh nodes
    /// living only in native-stack locals.
    fn safe_point_gc(&mut self, frames: &[ReduceFrame], child_result: Option<DagId>) {
        self.dags.clear_marks();
        self.mark_registered_roots();
        for frame in frames {
            self.mark_reachable(frame.original);
            for &r in &frame.args {
                self.mark_reachable(r);
            }
        }
        if let Some(r) = child_result {
            self.mark_reachable(r);
        }
        self.dags.sweep(|_| {});
    }

    /// Iterative (stack-based) transitive marker. Marks each node **on push** (using the
    /// "newly-marked" result of [`Arena::mark`]) so a node shared by *k* parents is pushed once,
    /// keeping the work stack O(nodes) rather than O(edges); it also terminates on shared/cyclic
    /// structure.
    fn mark_reachable(&mut self, root: DagId) {
        let mut stack = Vec::new();
        // Children are collected (via the `children()` visitor) into this reused scratch buffer, then
        // marked: enumerating borrows the node (hence the arena) immutably, while marking needs the
        // arena mutably, so the two phases can't overlap. `extend` from the iterator hits a slice
        // fast-path for the free rep; a non-slice arm still works, just without the memcpy.
        let mut kids: Vec<DagId> = Vec::new();
        if self.dags.mark(root) {
            stack.push(root);
        }
        while let Some(id) = stack.pop() {
            kids.clear();
            kids.extend(self.dags.get(id).children());
            for &child in &kids {
                if self.dags.mark(child) {
                    stack.push(child);
                }
            }
        }
    }

    // ---- statistics ----

    /// Total equational rewrites applied so far.
    pub(crate) fn rewrites(&self) -> u64 {
        self.rewrite_count
    }
    pub(crate) fn reset_rewrites(&mut self) {
        self.rewrite_count = 0;
    }

    // ---- reduction ----

    /// The reduction core; see [`Engine::reduce`] for the contract and the iterative-vs-recursive
    /// rationale. Reads `sig.eq_epoch()`, builds nodes via `self.make_free(sig, ..)`, and rewrites
    /// the top via `self.try_rewrite_top(sig, ..)` — all while holding only a shared borrow of `sig`.
    #[must_use]
    pub(crate) fn reduce(&mut self, sig: &Signature, root: DagId) -> DagId {
        if self.node(root).reduced_epoch == sig.eq_epoch() {
            return root;
        }

        let mut stack: Vec<ReduceFrame> = Vec::new();
        stack.push(self.new_reduce_frame(root));
        // Carries a just-completed child's normal form up to the parent frame waiting on it.
        let mut child_result: Option<DagId> = None;

        loop {
            // Invariant: `stack` is non-empty throughout the body. It starts with the root frame and
            // the only `pop` (below) is immediately followed by a `return` when it empties, so the
            // loop never re-enters with an empty stack — the `expect`s below are therefore unreachable.

            // Safe-point GC (A2): the loop head is the *only* point during a reduction where every
            // in-flight node is discoverable (the frame stack + `child_result`); collect here when
            // allocation pressure crosses the configured interval so a large reduction stays bounded.
            if let Some(interval) = self.gc_interval
                && self.allocs_since_gc >= interval
            {
                self.safe_point_gc(&stack, child_result);
                self.allocs_since_gc = 0;
            }

            // Deliver a completed child into its strategy position and advance the strategy cursor.
            if let Some(r) = child_result.take() {
                let f = stack.last_mut().expect("child result with empty reduce stack");
                let pos = sig
                    .strat_position(f.symbol, f.cursor, f.orig.len())
                    .expect("delivering a child means a strategy step was in progress");
                f.args[pos] = r;
                f.cursor += 1;
            }

            // Phase 1: reduce the next argument the strategy selects (the standard strategy walks them
            // left-to-right; a custom strategy reduces only its listed positions). Already-reduced
            // children (shared subterms, cached by epoch) are delivered without pushing a frame.
            {
                let f = stack.last().expect("empty reduce stack");
                if let Some(pos) = sig.strat_position(f.symbol, f.cursor, f.orig.len()) {
                    let child = f.args[pos];
                    if self.node(child).reduced_epoch == sig.eq_epoch() {
                        child_result = Some(child);
                    } else {
                        let frame = self.new_reduce_frame(child);
                        stack.push(frame);
                    }
                    continue;
                }
            }

            // Phase 1 complete (strategy exhausted): rebuild iff some argument changed, else keep the id.
            let (symbol, original, args, changed) = {
                let f = stack.last_mut().expect("empty reduce stack");
                let changed = f.args != f.orig;
                // `mem::take` moves the args out (no clone) — the frame is about to be reused or popped,
                // so its `args` is no longer needed.
                let args = if changed { std::mem::take(&mut f.args) } else { Vec::new() };
                (f.symbol, f.original, args, changed)
            };
            let rebuilt = if !changed {
                original
            } else if matches!(sig.symbol(symbol).theory(), Theory::S) {
                // An S node's `count` is non-child state `rebuild` cannot recover (it would re-wrap as
                // `s^1`); preserve the original count and re-seat it over the reduced argument.
                let count = match &self.node(original).term {
                    NodeTerm::S { count, .. } => count.clone(),
                    _ => unreachable!("a Theory::S node is NodeTerm::S"),
                };
                self.make_s(sig, symbol, count, args[0])
            } else {
                self.rebuild(sig, symbol, args)
            };

            // Phase 2: rewrite the top while an equation applies, re-reducing each result by reusing
            // this frame's slot for the rewritten term.
            if let Some(next) = self.try_rewrite_top(sig, rebuilt) {
                self.rewrite_count += 1;
                let frame = self.new_reduce_frame(next);
                *stack.last_mut().expect("empty reduce stack") = frame;
                continue;
            }

            // `rebuilt` is a normal form: stamp it canonical and hand it up (or return it as root).
            self.dags.get_mut(rebuilt).reduced_epoch = sig.eq_epoch();
            stack.pop();
            if stack.is_empty() {
                return rebuilt;
            }
            child_result = Some(rebuilt);
        }
    }

    /// Build a fresh [`ReduceFrame`] positioned at the start of `id`'s children.
    fn new_reduce_frame(&self, id: DagId) -> ReduceFrame {
        let node = self.node(id);
        let orig: Vec<DagId> = node.children().collect();
        ReduceFrame {
            original: id,
            symbol: node.symbol(),
            args: orig.clone(),
            orig,
            cursor: 0,
        }
    }

    /// Apply the first matching equation at the top of `id`, returning the instantiated rhs (or
    /// `None` if no equation applies).
    ///
    /// Driven as a **solution stream** through the A3 matcher seam: each equation's compiled
    /// [`LhsAutomaton`] yields a [`Subproblem`](crate::theory::Subproblem) whose `next` enumerates
    /// solutions into `subst`. Phase 1 equations are unconditional, so the *first* solution of the
    /// first matching equation wins; the `while sp.next(..)` loop is where a conditional equation will
    /// evaluate its condition and, on failure, fall through to the next solution — and where an AC
    /// subproblem will surface its several solutions. (Free matching yields exactly one.)
    ///
    /// The A4 borrow split is what lets this avoid cloning the rhs: `eqs` (and thus `&eq.rhs`) is a
    /// shared borrow of `sig`, disjoint from the `&mut self` runtime, so the matched rhs is
    /// instantiated straight out of the still-borrowed equation table.
    fn try_rewrite_top(&mut self, sig: &Signature, id: DagId) -> Option<DagId> {
        let symbol = self.node(id).symbol();
        // Built-in operators (`special`) are the symbol's primary reduction rule (Maude's `eqRewrite`);
        // they are tried before user equations and fall through (`None`) on no-match. The `&SpecialOp`
        // borrowed from `sig` coexists with `&mut self` (the A4 split).
        if let Some(op) = sig.symbol(symbol).special()
            && let Some(r) = self.try_special(sig, id, op)
        {
            return Some(r);
        }
        // ACU/AU/S rewriting matches *modulo* the axioms with extension: a pattern may match a
        // sub-multiset (ACU), a contiguous sub-sequence (AU), or a successor prefix `s^k` of an `s^n`
        // subject (S), leaving a residue to splice back. The free/CUI theories match the whole node.
        let ext_allowed = matches!(sig.symbol(symbol).theory(), Theory::Acu | Theory::Au | Theory::S);
        let eqs = sig.equations.get(&symbol)?;
        // Non-owise equations first; an `[owise]` equation applies only if no non-owise one does
        // (Maude's two-phase `applyReplaceNoOwise` / `applyReplace`, B2.3b). The second pass is reached
        // only when the first found nothing — for a node with no equations the early `?` above skips both.
        if let Some(r) = self.try_equations(sig, id, eqs, ext_allowed, false) {
            return Some(r);
        }
        self.try_equations(sig, id, eqs, ext_allowed, true)
    }

    /// Try the equations of one phase (`owise == false` → the normal equations; `owise == true` → the
    /// `[owise]` fallbacks) against `id`, returning the first applicable rewrite. Drives each equation
    /// as a **solution stream** through the A3 matcher seam: the compiled [`LhsAutomaton`] yields a
    /// [`Subproblem`](crate::theory::Subproblem) whose `next` enumerates solutions into `subst`; a
    /// conditional equation accepts a solution only if its condition holds, else backtracks into the
    /// next solution (Maude's `solveCondition` retry). The A4 borrow split lets the matched `&eq.rhs`
    /// (a shared borrow of `sig`) instantiate in place without a defensive clone.
    fn try_equations(
        &mut self,
        sig: &Signature,
        id: DagId,
        eqs: &[CompiledEquation],
        ext_allowed: bool,
        owise: bool,
    ) -> Option<DagId> {
        let mut subst = Subst::new();
        for eq in eqs {
            if eq.owise != owise {
                continue; // wrong phase
            }
            subst.reset(eq.nr_vars);
            let Some(mut sp) = eq.lhs.match_(self, sig, id, &mut subst, ext_allowed) else {
                continue;
            };
            while sp.next(self, sig, &mut subst) {
                // Unconditional equations short-circuit (no call) — the free reduce hot path.
                if !eq.condition.is_empty() && !self.condition_holds(sig, &eq.condition, &mut subst) {
                    continue;
                }
                let rhs = self.instantiate(sig, &eq.rhs, &subst);
                // The subproblem splices the rhs into the matched position — a whole match is just the
                // rhs; an extension match re-assembles the residue around it in the theory's normal
                // form (ACU multiset, AU ordered prefix/suffix — Maude's `partialConstruct`).
                return Some(sp.build_result(self, sig, rhs));
            }
        }
        None
    }

    /// Whether every fragment of `condition` holds under the matched substitution `subst` — the B2.3
    /// condition check the rewrite driver runs before accepting a solution (empty condition ⇒ `true`).
    ///
    /// Each fragment is evaluated by **re-entrant reduction** of its instantiated term(s). **F-2
    /// mitigation:** safe-point GC is disabled for the duration — a nested `reduce`'s safe points
    /// cannot see the *outer* reduction's in-flight frames / `Subst` / AC residue, so collecting here
    /// would sweep them; not collecting during this window eliminates the hazard. (Bounded-memory
    /// condition reduction via an engine-global active-frame root set is the remaining follow-up; the
    /// temporaries are reclaimed at the next outer safe point once GC is restored.)
    fn condition_holds(&mut self, sig: &Signature, condition: &[CompiledFragment], subst: &mut Subst) -> bool {
        if condition.is_empty() {
            return true;
        }
        let saved_gc = self.gc_interval;
        self.gc_interval = None;
        let holds = self.solve_condition(sig, condition, 0, subst);
        self.gc_interval = saved_gc;
        holds
    }

    /// Satisfy `condition[i..]` under `subst`, backtracking (Maude's `solveCondition`): an **equality**
    /// fragment reduces both sides and compares modulo the axioms; a **sort-test** reduces the term and
    /// checks its least sort; a **matching** (`:=`) fragment reduces the subject and enumerates the
    /// pattern's solutions, recursing into the remaining fragments for each and retrying the next on
    /// failure. The re-entrant reductions are what make a condition's rewrites count toward the total.
    /// A matching fragment's `fresh_vars` are unbound before each attempt so backtracking re-binds
    /// cleanly; on overall success the accepted bindings remain in `subst` for the rhs.
    fn solve_condition(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        i: usize,
        subst: &mut Subst,
    ) -> bool {
        let Some(frag) = condition.get(i) else {
            return true; // every fragment satisfied
        };
        match frag {
            CompiledFragment::Equality { lhs, rhs } => {
                let l = self.instantiate(sig, lhs, subst);
                let l = self.reduce(sig, l);
                let r = self.instantiate(sig, rhs, subst);
                let r = self.reduce(sig, r);
                self.deep_equal(l, r) && self.solve_condition(sig, condition, i + 1, subst)
            }
            CompiledFragment::SortTest { term, sort } => {
                let t = self.instantiate(sig, term, subst);
                let t = self.reduce(sig, t);
                sig.sorts().leq(self.node(t).sort, *sort)
                    && self.solve_condition(sig, condition, i + 1, subst)
            }
            CompiledFragment::Matching { pattern, subject, fresh_vars } => {
                let subj = self.instantiate(sig, subject, subst);
                let subj = self.reduce(sig, subj);
                for &fv in fresh_vars {
                    subst.unbind(fv); // fresh slate, so a backtracking re-entry rebinds cleanly
                }
                let satisfied = match pattern.match_(self, sig, subj, subst, false) {
                    Some(mut sp) => {
                        let mut ok = false;
                        while sp.next(self, sig, subst) {
                            if self.solve_condition(sig, condition, i + 1, subst) {
                                ok = true;
                                break;
                            }
                        }
                        ok
                    }
                    None => false,
                };
                if !satisfied {
                    for &fv in fresh_vars {
                        subst.unbind(fv);
                    }
                }
                satisfied
            }
        }
    }
}

// ======================================================================================
// Engine: the thin public facade over Signature + Runtime
// ======================================================================================

impl Engine {
    pub fn new() -> Self {
        Self::default()
    }

    /// Shared access to the immutable signature half (sorts/symbols/equations). Used by the matcher
    /// seam's tests to drive [`LhsAutomaton`](crate::theory) directly over the two halves.
    #[cfg(test)]
    pub(crate) fn signature(&self) -> &Signature {
        &self.sig
    }
    /// Shared access to the mutable runtime half (DAG arena/GC/statistics). Test-only counterpart of
    /// [`signature`](Self::signature).
    #[cfg(test)]
    pub(crate) fn runtime(&self) -> &Runtime {
        &self.rt
    }
    /// Both halves borrowed disjointly, for tests that drive the matcher seam's `next` (which needs
    /// `&mut Runtime` + `&Signature` at once — the A4 split).
    #[cfg(test)]
    pub(crate) fn parts_mut(&mut self) -> (&Signature, &mut Runtime) {
        (&self.sig, &mut self.rt)
    }

    // ---- sort signature ----

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sig.add_sort(name)
    }
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sig.add_subsort(sub, sup);
    }
    /// Finish the sort poset (compute kinds + subsort closure). Call before building DAG nodes.
    pub fn close_sorts(&mut self) {
        self.sig.close_sorts();
    }
    pub fn sorts(&self) -> &Sorts {
        self.sig.sorts()
    }

    // ---- symbols ----

    pub fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.sig.add_op(name, domain, range)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading); the
    /// least sort of an application is then resolved across all of them. Declarations must agree on
    /// arity and are tried in the order added (the original `add_op*` declaration stays first — the
    /// tie-break favours it). Add all declarations before building any node of `sym` (sorts cache at
    /// construction).
    pub fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        self.sig.add_op_decl(sym, domain, range);
    }

    /// Mark an operator as a constructor (`[ctor]`, B2.4) — metadata that does not affect reduction.
    pub fn set_ctor(&mut self, sym: SymbolId) {
        self.sig.set_ctor(sym);
    }

    /// Whether every declaration of `sym` is a constructor (`[ctor]`).
    pub fn is_constructor(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_constructor()
    }

    /// Set an evaluation strategy `strat (raw…)` on `sym` (B2.4): `raw` is the 1-based argument
    /// positions to reduce, in order, ending in a single `0` (reduce at top). Arguments not listed are
    /// left unreduced (lazy) — e.g. `if_then_else_fi` with `[1, 0]`.
    pub fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        self.sig.set_strategy(sym, raw);
    }

    /// Attach a built-in reduction rule (`special (id-hook …)`, B3) to `sym` — tried before user
    /// equations. Hook references are passed already resolved to [`SymbolId`]s (the future parser does
    /// the name resolution; hand-built modules supply them directly, as with [`add_equation`]). A
    /// [`SpecialOp::Branch`](crate::symbol::SpecialOp) auto-installs its lazy `strat (1 0)`.
    pub fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        self.sig.set_special(sym, op);
    }

    /// Register an **ACU** operator (`assoc comm`, optionally with a two-sided `id:`). Must be binary;
    /// `identity` is the constant symbol declared as `id: <const>`, or `None`. The operator's
    /// arguments are stored flattened as a canonical multiset and matched/rewritten modulo AC(+U).
    pub fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_ac(name, domain, range, identity)
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; arguments are stored as a flattened ordered sequence and matched modulo associativity.
    pub fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_au(name, domain, range, identity)
    }

    /// Register a **CUI** operator (`comm`, not associative, optionally `idem` and/or `id:`). Must be
    /// binary; the two arguments are stored in canonical order, and `idem`/`id:` collapse `f(a,a)` /
    /// `f(a,e)` to a single element at construction.
    pub fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_cui(name, domain, range, idem, identity)
    }

    /// Register an **S** (`iter`) operator: a unary stacked successor `s_` (Maude's `[iter]`). Must be
    /// unary; its nodes (built via [`make_iter`](Self::make_iter)) store `s^count(arg)` compactly.
    pub fn add_op_iter(&mut self, name: impl Into<String>, domain: Vec<SortId>, range: SortId) -> SymbolId {
        self.sig.add_op_iter(name, domain, range)
    }
    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.sig.symbol(id)
    }

    // ---- DAG construction ----

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub fn make_free(&mut self, symbol: SymbolId, args: Vec<DagId>) -> DagId {
        self.rt.make_free(&self.sig, symbol, args)
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub fn make_const(&mut self, symbol: SymbolId) -> DagId {
        self.rt.make_const(&self.sig, symbol)
    }

    /// Build a canonical **ACU** node for an `assoc comm [id:]` operator from `(element, multiplicity)`
    /// pairs (see [`Runtime::make_acu`]). The result is in AC(+U) normal form — flattened, identity
    /// dropped, equal elements merged, canonically ordered — and may collapse to a single element or
    /// the identity. `symbol` must be ACU (declared via [`add_op_ac`](Self::add_op_ac)).
    pub fn make_acu(&mut self, symbol: SymbolId, args: Vec<(DagId, u32)>) -> DagId {
        self.rt.make_acu(&self.sig, symbol, args)
    }
    /// Convenience for [`make_acu`](Self::make_acu) from a flat list of elements (each multiplicity 1):
    /// `make_ac(plus, vec![a, b, c])` builds the canonical `a + b + c`.
    pub fn make_ac(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.rt.make_acu(&self.sig, symbol, elements.into_iter().map(|e| (e, 1)).collect())
    }

    /// Build a canonical **AU** node for an `assoc [id:]` operator from an ordered element list (see
    /// [`Runtime::make_au`]): `make_au(concat, vec![a, b, c])` builds the canonical `a b c`. Flattened
    /// and identity-dropped, order preserved; may collapse to a single element or the identity.
    pub fn make_au(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.rt.make_au(&self.sig, symbol, elements)
    }

    /// Build a canonical **CUI** node for a `comm [idem] [id:]` operator from its two arguments (see
    /// [`Runtime::make_cui`]): commutatively ordered, with `f(a,a)`/`f(a,e)` collapsed.
    pub fn make_cui(&mut self, symbol: SymbolId, x: DagId, y: DagId) -> DagId {
        self.rt.make_cui(&self.sig, symbol, x, y)
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)` for an `iter` operator (see
    /// [`Runtime::make_s`]): `count == 0` collapses to `arg`, nested same-symbol successors flatten.
    /// `symbol` must be an `iter` operator (declared via [`add_op_iter`](Self::add_op_iter)).
    pub fn make_iter(&mut self, symbol: SymbolId, count: u64, arg: DagId) -> DagId {
        self.rt.make_s(&self.sig, symbol, Nat::from_u64(count), arg)
    }

    /// Build a string-literal NA node (the `<Strings>` `StringSymbol`, B3.6); `symbol` is an arity-0
    /// string-constant operator.
    pub fn make_string(&mut self, symbol: SymbolId, value: &str) -> DagId {
        self.rt.make_na(&self.sig, symbol, NaValue::Str(value.into()))
    }
    /// Build a quoted-identifier NA node (the `<Qids>` `QuotedIdentifierSymbol`, B3.6).
    pub fn make_qid(&mut self, symbol: SymbolId, value: &str) -> DagId {
        self.rt.make_na(&self.sig, symbol, NaValue::Qid(value.into()))
    }

    pub fn node(&self, id: DagId) -> &DagNode {
        self.rt.node(id)
    }
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.rt.sort_of(id)
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub fn live_nodes(&self) -> usize {
        self.rt.live_nodes()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub fn node_capacity(&self) -> usize {
        self.rt.node_capacity()
    }

    // ---- garbage collection (D2) ----

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives (decision D2 amendment).
    /// The guard registers the root on construction and releases it on `Drop`; it holds a shared
    /// handle to the registry rather than borrowing the engine, so the caller can keep it alive
    /// across `&mut self` calls like [`reduce`](Self::reduce).
    ///
    /// Bind the guard to a named local (`let _g = engine.root(id);`). `let _ = engine.root(id)` drops
    /// it immediately, releasing the root on the same line — and `#[must_use]` does *not* flag the
    /// discarding `let _` form. `id` is not validated here; a stale or cross-engine handle surfaces at
    /// the next collection, not at this call.
    pub fn root(&self, id: DagId) -> RootGuard {
        self.rt.root(id)
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`] or from `extra_roots`; returns
    /// the number reclaimed. Roots pinned by guards are *always* included, so callers normally pass
    /// `[]`; `extra_roots` is the advanced entry point for roots not (yet) held by a guard — e.g. the
    /// `examples/peano` benchmark, which roots a term inline.
    pub fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.rt.gc(extra_roots)
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Self::reduce). `Some(interval)` collects
    /// at the reduce loop head once `interval` DAG nodes have been allocated since the last
    /// collection; `None` (default) disables it, so callers collect between reductions instead.
    ///
    /// **Rooting contract.** Once this is enabled, a collection can run *during* `reduce`. Any `DagId`
    /// you keep across a later allocation or `reduce` call — including the result of an *earlier*
    /// `reduce` — must be pinned with [`root`](Self::root), or that collection may reclaim it (it is
    /// not reachable from the in-progress reduction's working set). Using an unrooted, reclaimed
    /// handle panics in debug (the generational check) and is a silent wrong answer in release.
    pub fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.rt.set_gc_interval(interval);
    }

    // ---- equations + reduction ----

    /// Register an unconditional equation, indexed by its left-hand side's top symbol. The lhs is
    /// compiled to a theory `LhsAutomaton` (the A3 matcher seam) here, once. A term canonical under
    /// the old equation set may now be reducible, so this advances the equation epoch, invalidating
    /// every node's cached "reduced" stamp (review R2 H2).
    pub fn add_equation(&mut self, eq: Equation) {
        self.sig.add_equation(eq);
    }

    /// Register a conditional equation `ceq lhs = rhs if condition` (B2.3). The condition is a list of
    /// [`ConditionFragment`](crate::term::ConditionFragment)s (equality / sort-test); all must hold for
    /// the equation to fire, and a failed condition backtracks into the next matcher solution.
    pub fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.sig.add_conditional_equation(lhs, rhs, nr_vars, condition);
    }

    /// Register an `[owise]` equation (optionally conditional): applied only when no non-owise equation
    /// of the symbol matches (B2.3b). Pass an empty `condition` for a plain `eq ... [owise]`.
    pub fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.sig.add_owise_equation(lhs, rhs, nr_vars, condition);
    }

    /// Register an (unconditional) membership axiom `mb lhs : sort` (the lhs compiled to the A3
    /// matcher seam). Memberships lower a node's least sort at construction, so declare them before
    /// building any node of the lhs's symbol (cf. the overload add-declarations-first contract).
    pub fn add_membership(&mut self, mb: Membership) {
        self.sig.add_membership(mb);
    }

    /// Register a conditional membership `cmb lhs : sort if condition` (B2.3c): the sort is lowered
    /// only when the condition holds under the membership match. Pass an empty `condition` for a plain
    /// `mb` (or use [`add_membership`](Self::add_membership)).
    pub fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) {
        self.sig.add_conditional_membership(lhs, sort, nr_vars, condition);
    }

    /// Total equational rewrites applied so far.
    pub fn rewrites(&self) -> u64 {
        self.rt.rewrites()
    }
    pub fn reset_rewrites(&mut self) {
        self.rt.reset_rewrites();
    }

    /// Reduce `root` to canonical form by innermost, eager equational simplification (Phase 0:
    /// unconditional free-theory equations). A node already stamped canonical at the current epoch is
    /// returned unchanged, so a *shared, already-reduced* subterm is never re-normalized. (A shared
    /// subterm that is still *reducible* is normalized once per occurrence — Phase 0 has no
    /// hash-consing/forwarding — exactly as the recursive reducer did.)
    ///
    /// Iterative (explicit `ReduceFrame` work-stack) rather than recursive: the recursion depth of
    /// the old `reduce`/`reduce_args` grew with *subject* depth — unbounded user data — and aborted
    /// the process on deep terms (review R2 C1). This is a faithful simulation: children are reduced
    /// left-to-right before the top is rewritten, and each rewrite result is itself re-reduced, so
    /// the sequence of redexes — and thus the rewrite count — is identical to the recursive version.
    #[must_use]
    pub fn reduce(&mut self, root: DagId) -> DagId {
        self.rt.reduce(&self.sig, root)
    }

    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success; on failure
    /// `subst` may hold partial bindings, so callers reset before each attempt.
    #[must_use]
    pub fn match_pattern(&self, pat: &Term, subject: DagId, subst: &mut Subst) -> bool {
        self.rt.match_pattern(&self.sig, pat, subject, subst)
    }

    /// Structural equality of two DAG nodes (Phase 0 has no hash-consing, so this is a deep walk).
    #[must_use]
    pub fn deep_equal(&self, a: DagId, b: DagId) -> bool {
        self.rt.deep_equal(a, b)
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    pub fn instantiate(&mut self, term: &Term, subst: &Subst) -> DagId {
        self.rt.instantiate(&self.sig, term, subst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ConditionFragment, Equation, Membership, Term};

    /// `f(a, g(a))` over a single sort `Nat`, with `a` shared (a true DAG). Returns engine + root.
    fn fixture() -> (Engine, DagId, SortId) {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        let root = e.make_free(f, vec![a1, ga]);
        (e, root, nat)
    }

    #[test]
    fn gc_keeps_reachable_shared_structure() {
        let (mut e, root, _nat) = fixture();
        assert_eq!(e.live_nodes(), 3);
        assert_eq!(e.gc([root]), 0);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_collects_unreachable() {
        let (mut e, root, nat) = fixture();
        let h = e.add_op("h", vec![], nat);
        let _garbage = e.make_const(h);
        assert_eq!(e.live_nodes(), 4);
        assert_eq!(e.gc([root]), 1);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_with_no_roots_collects_all() {
        let (mut e, _root, _nat) = fixture();
        assert_eq!(e.gc(Vec::new()), 3);
        assert_eq!(e.live_nodes(), 0);
    }

    #[test]
    fn computes_node_sorts_through_subsorts() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        let n0 = e.make_const(z); // 0 : Zero
        let n1 = e.make_free(s, vec![n0]); // s(0): Zero <= Nat  =>  NzNat
        let sum = e.make_free(plus, vec![n0, n1]); // Zero,NzNat <= Nat  =>  Nat

        assert_eq!(e.sort_of(n0), zero);
        assert_eq!(e.sort_of(n1), nznat);
        assert_eq!(e.sort_of(sum), nat);
    }

    /// B2.1 least sort under multi-declaration overloading (== reference binary,
    /// `conformance/overload.maude` OVERLOAD-SORT): `_+_` is overloaded `Nat Nat -> Nat` *and*
    /// `NzNat NzNat -> NzNat`; the least sort of an application is resolved across both declarations.
    #[test]
    fn overloaded_operator_least_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat); // decl 0: Nat Nat -> Nat
        e.add_op_decl(plus, vec![nznat, nznat], nznat); // decl 1: NzNat NzNat -> NzNat

        let n0 = e.make_const(z); // 0 : Zero
        let s0 = e.make_free(s, vec![n0]); // s 0 : NzNat
        assert_eq!(e.sort_of(n0), zero, "0 : Zero");
        assert_eq!(e.sort_of(s0), nznat, "s 0 : NzNat");
        // s0 / n0 are reused as shared children below (a genuine DAG share).
        let s0_plus_s0 = e.make_free(plus, vec![s0, s0]);
        assert_eq!(e.sort_of(s0_plus_s0), nznat, "s 0 + s 0 : NzNat (both args NzNat)");
        let zero_plus_s0 = e.make_free(plus, vec![n0, s0]);
        assert_eq!(e.sort_of(zero_plus_s0), nat, "0 + s 0 : Nat (Zero is not <= NzNat)");
        let zero_plus_zero = e.make_free(plus, vec![n0, n0]);
        assert_eq!(e.sort_of(zero_plus_zero), nat, "0 + 0 : Nat");
    }

    /// B2.1 (== reference binary, OVERLOAD-RED): overloading + equations — the result's least sort and
    /// the rewrite count co-vary. `s 0 + s 0` → `s s 0 : NzNat` (2 rewrites); `0 + 0` → `0 : Zero`
    /// (1 rewrite, the result re-sorts *down* from Nat to Zero).
    #[test]
    fn overloaded_operator_reduce_and_resort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_op_decl(plus, vec![nznat, nznat], nznat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let sum = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 2, "s 0 + s 0 = s s 0 in 2 rewrites");
        assert_eq!(e.sort_of(r), nznat, "result s s 0 : NzNat");
        assert_eq!(e.node(r).symbol(), s, "result is an s_ application");

        e.reset_rewrites();
        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0
        assert_eq!(e.sort_of(zz), nat, "0 + 0 : Nat before reduction");
        let r2 = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "0 + 0 = 0 in 1 rewrite");
        assert_eq!(e.sort_of(r2), zero, "result 0 : Zero (re-sorted down)");
    }

    /// B2.1 (== reference binary, OVERLOAD-ERR): no applicable declaration → the kind's error sort
    /// (and the ill-sorted term does not rewrite). Only `_+_ : NzNat NzNat -> NzNat` is declared, so
    /// `0 + 0` (Zero arguments) has no applicable declaration.
    #[test]
    fn overloaded_operator_no_applicable_decl_is_error_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nznat, nznat], nznat); // ONLY NzNat NzNat -> NzNat

        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0 : no decl applies
        assert!(e.sorts().sort(e.sort_of(zz)).is_error, "0 + 0 lands in the error sort");

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let ss = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0 : NzNat
        assert_eq!(e.sort_of(ss), nznat, "s 0 + s 0 : NzNat (the one declaration applies)");
    }

    /// B2.1 (== reference binary, OVERLOAD-PREREG): a non-preregular operator (`f : A -> A` and
    /// `f : A -> B` with A, B incomparable) — Maude warns and assigns the least sort by the **earliest
    /// declaration**. We reproduce the tie-break (the warning itself is deferred): `f(c) : A`.
    #[test]
    fn non_preregular_overload_breaks_toward_earliest_declaration() {
        let mut e = Engine::new();
        let a = e.add_sort("A");
        let b = e.add_sort("B");
        let top = e.add_sort("Top");
        e.add_subsort(a, top);
        e.add_subsort(b, top);
        e.close_sorts();
        let c = e.add_op("c", vec![], a);
        let f = e.add_op("f", vec![a], a); // decl 0: A -> A
        e.add_op_decl(f, vec![a], b); // decl 1: A -> B (incomparable range)

        let c0 = e.make_const(c);
        let fc = e.make_free(f, vec![c0]);
        assert_eq!(e.sort_of(fc), a, "f(c) : A — the earliest of the two incomparable declarations");
    }

    /// B2.1 / audit-F-B regression (== reference binary, `conformance/acu-overload.maude` ACU-OVERLOAD):
    /// an **asymmetric** overloaded declaration on a **commutative** operator must give an
    /// argument-order-independent least sort. `_+_ : NzNat Nat -> NzNat [assoc comm]` overloaded
    /// `Nat Nat -> Nat`: `z + nz : NzNat` whichever element the canonical multiset order puts first
    /// (Maude's `commutativeSortCompletion` adds the swapped `Nat NzNat -> NzNat` declaration). The
    /// pre-fix positional fold gave `Nat` whenever the Zero element sorted first.
    #[test]
    fn acu_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let plus = e.add_op_ac("+", vec![nznat, nat], nznat, None); // decl0: NzNat Nat -> NzNat
        e.add_op_decl(plus, vec![nat, nat], nat); // decl1: Nat Nat -> Nat

        let sum = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_ac(plus, vec![x, y]);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(sum(&mut e, z, nz), "NzNat", "z + nz : NzNat (order-independent)");
        assert_eq!(sum(&mut e, nz, z), "NzNat", "nz + z : NzNat");
        assert_eq!(sum(&mut e, z, z), "Nat", "z + z : Nat");
        assert_eq!(sum(&mut e, nz, nz), "NzNat", "nz + nz : NzNat");
        // Ternary: the left-to-right multiset fold stays order-independent.
        let tern = {
            let (x, y, w) = (e.make_const(z), e.make_const(nz), e.make_const(z));
            e.make_ac(plus, vec![x, y, w])
        };
        assert_eq!(e.sorts().name(e.sort_of(tern)), "NzNat", "z + z + nz : NzNat");
    }

    /// B1/B2.1 / audit-F-B regression (== reference binary, CUI-OVERLOAD): the same order-independence
    /// for a **commutative non-associative** operator. `make_cui` orders its pair canonically (Zero
    /// before NzNat), so `g(z, nz) : NzNat` needs the swapped `Nat NzNat -> NzNat` declaration too.
    #[test]
    fn cui_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let g = e.add_op_cui("g", vec![nznat, nat], nznat, false, None); // NzNat Nat -> NzNat
        e.add_op_decl(g, vec![nat, nat], nat); // Nat Nat -> Nat

        let gg = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_cui(g, x, y);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(gg(&mut e, z, nz), "NzNat", "g(z, nz) : NzNat (order-independent)");
        assert_eq!(gg(&mut e, nz, z), "NzNat", "g(nz, z) : NzNat");
        assert_eq!(gg(&mut e, z, z), "Nat", "g(z, z) : Nat");
    }

    /// B2.2 membership axioms (== reference binary, `conformance/membership.maude` MB-PAIR): a
    /// non-linear `mb < N, N > : SymPair` lowers a pair's least sort, and **each membership application
    /// counts as a rewrite** (Maude's accounting). The lowered sort then drives which equations fire:
    /// `eq f(P) = z` with `P : SymPair` reduces `f(< z, z >)` but not `f(< z, s z >)`. Memberships are
    /// applied at construction, so each case resets the counter *before* building its query term.
    #[test]
    fn membership_lowers_sort_and_counts_as_rewrite() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let sympair = e.add_sort("SymPair");
        e.add_subsort(sympair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let f = e.add_op("f", vec![pair], nat);
        e.add_membership(Membership {
            lhs: Term::op(pairop, vec![Term::var(0, nat), Term::var(0, nat)]), // < N, N > (non-linear)
            sort: sympair,
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, sympair)]), // f(P), P : SymPair
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        // < z, z > : SymPair — one membership application.
        e.reset_rewrites();
        let (z0, z1) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(pairop, vec![z0, z1]);
        assert_eq!(e.sort_of(zz), sympair, "< z, z > : SymPair");
        let r = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "one membership application");
        assert_eq!(e.sort_of(r), sympair);

        // < z, s z > : Pair — components differ, no membership applies.
        e.reset_rewrites();
        let zc = e.make_const(z);
        let sz = {
            let z2 = e.make_const(z);
            e.make_free(s, vec![z2])
        };
        let zsz = e.make_free(pairop, vec![zc, sz]);
        assert_eq!(e.sort_of(zsz), pair, "< z, s z > : Pair");
        let _ = e.reduce(zsz);
        assert_eq!(e.rewrites(), 0, "no membership applies");

        // f(< z, z >) : Nat — membership (1) + equation (1) = 2 rewrites.
        e.reset_rewrites();
        let (z3, z4) = (e.make_const(z), e.make_const(z));
        let zz2 = e.make_free(pairop, vec![z3, z4]); // membership fires here
        let fzz = e.make_free(f, vec![zz2]);
        let r2 = e.reduce(fzz); // equation fires here
        assert_eq!(e.rewrites(), 2, "membership + equation");
        assert_eq!(e.node(r2).symbol(), z, "f(< z, z >) = z");

        // f(< z, s z >) : Nat — arg is only Pair, so f(P : SymPair) does not match.
        e.reset_rewrites();
        let zc2 = e.make_const(z);
        let sz2 = {
            let z5 = e.make_const(z);
            e.make_free(s, vec![z5])
        };
        let zsz2 = e.make_free(pairop, vec![zc2, sz2]);
        let fzsz = e.make_free(f, vec![zsz2]);
        let r3 = e.reduce(fzsz);
        assert_eq!(e.rewrites(), 0, "no membership, no equation");
        assert_eq!(e.node(r3).symbol(), f, "f(< z, s z >) is its own normal form");
    }

    /// B2.2 (== reference binary, MB-CHAIN): two memberships lower a sort two levels. The constrain
    /// pass is **smallest-target-sort first**, so `g(g(a))` drops straight to C (one application on the
    /// outer node), giving 2 applications total (inner `g(a) : B`, outer `g(g(a)) : C`) — not 3.
    #[test]
    fn membership_chain_lowers_two_levels() {
        let mut e = Engine::new();
        let sa = e.add_sort("A");
        let sb = e.add_sort("B");
        let sc = e.add_sort("C");
        e.add_subsort(sc, sb);
        e.add_subsort(sb, sa);
        e.close_sorts();
        let a = e.add_op("a", vec![], sa);
        let g = e.add_op("g", vec![sa], sa);
        e.add_membership(Membership { lhs: Term::op(g, vec![Term::var(0, sa)]), sort: sb, nr_vars: 1 }); // g(X) : B
        e.add_membership(Membership {
            lhs: Term::op(g, vec![Term::op(g, vec![Term::var(0, sa)])]), // g(g(X)) : C
            sort: sc,
            nr_vars: 1,
        });

        e.reset_rewrites();
        let a0 = e.make_const(a);
        assert_eq!(e.sort_of(a0), sa, "a : A");
        let _ = e.reduce(a0);
        assert_eq!(e.rewrites(), 0);

        e.reset_rewrites();
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        assert_eq!(e.sort_of(ga), sb, "g(a) : B");
        let _ = e.reduce(ga);
        assert_eq!(e.rewrites(), 1, "one membership application g(X):B");

        e.reset_rewrites();
        let a2 = e.make_const(a);
        let ga2 = e.make_free(g, vec![a2]);
        let gga = e.make_free(g, vec![ga2]);
        assert_eq!(e.sort_of(gga), sc, "g(g(a)) : C");
        let _ = e.reduce(gga);
        assert_eq!(e.rewrites(), 2, "inner g(a):B then outer g(g(a)):C — smallest-first, 2 not 3");
    }

    /// B2.3a conditional equations with equality conditions (== reference binary,
    /// `conformance/conditional.maude` CEQ-MAX): `max` via `ceq max(M,N)=N if M<=N=tt` /
    /// `ceq max(M,N)=M if M<=N=ff`. The condition `M<=N` itself reduces (re-entrant), its rewrites
    /// count, and a failed first condition backtracks to the second equation — re-reducing the
    /// condition (Maude caches nothing): `max(2,1)` is 5 rewrites, not 3.
    #[test]
    fn conditional_equation_with_equality_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let max = e.add_op("max", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N .
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq max(M, N) = N if M <= N = tt .   /   ceq max(M, N) = M if M <= N = ff .
        let le_mn = || Term::op(le, vec![v(0), v(1)]);
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(1),
            2,
            vec![ConditionFragment::Equality { lhs: le_mn(), rhs: Term::constant(tt) }],
        );
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(0),
            2,
            vec![ConditionFragment::Equality { lhs: le_mn(), rhs: Term::constant(ff) }],
        );

        // max(1, 2) = 2 in 3 rewrites: condition `1<=2` reduces to tt (2), then max→N (1).
        e.reset_rewrites();
        let (n1, n2) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let m = e.make_free(max, vec![n1, n2]);
        let r = e.reduce(m);
        assert_eq!(e.rewrites(), 3, "max(1,2): condition reduce (2) + max (1)");
        assert_eq!(decode(&e, r, z, s), 2, "max(1,2) = 2");

        // max(2, 1) = 2 in 5 rewrites: first condition `2<=1`→ff fails tt (2), backtrack, second
        // condition re-reduces `2<=1`→ff (2), matches ff, then max→M (1).
        e.reset_rewrites();
        let (n2b, n1b) = (numeral(&mut e, z, s, 2), numeral(&mut e, z, s, 1));
        let m2 = e.make_free(max, vec![n2b, n1b]);
        let r2 = e.reduce(m2);
        assert_eq!(e.rewrites(), 5, "max(2,1): cond fails (2) + cond re-reduced (2) + max (1)");
        assert_eq!(decode(&e, r2, z, s), 2, "max(2,1) = 2 (backtracked to the second equation)");

        // max(0, 0) = 0 in 2 rewrites.
        e.reset_rewrites();
        let (z1, z2) = (numeral(&mut e, z, s, 0), numeral(&mut e, z, s, 0));
        let m3 = e.make_free(max, vec![z1, z2]);
        let r3 = e.reduce(m3);
        assert_eq!(e.rewrites(), 2, "max(0,0): condition reduce (1) + max (1)");
        assert_eq!(decode(&e, r3, z, s), 0, "max(0,0) = 0");
    }

    /// B2.3a conditional equation with a sort-test condition (== reference binary, CEQ-SORT):
    /// `ceq nz?(N) = s z if N : NzNat` fires only when the argument's least sort is `<= NzNat`.
    #[test]
    fn conditional_equation_with_sort_test_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nznat); // s_ : Nat -> NzNat
        let nzq = e.add_op("nz?", vec![nat], nat);
        e.add_conditional_equation(
            Term::op(nzq, vec![Term::var(0, nat)]),
            Term::op(s, vec![Term::constant(z)]), // = s z
            1,
            vec![ConditionFragment::SortTest { term: Term::var(0, nat), sort: nznat }],
        );

        // nz?(s z) : the argument is NzNat → condition holds → s z, 1 rewrite.
        e.reset_rewrites();
        let s0 = {
            let z0 = e.make_const(z);
            e.make_free(s, vec![z0])
        };
        let q1 = e.make_free(nzq, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1, "condition N : NzNat holds for s z");
        assert_eq!(e.sort_of(r1), nznat, "result s z : NzNat");
        assert_eq!(e.node(r1).symbol(), s);

        // nz?(z) : z is only Nat → condition fails → no rewrite.
        e.reset_rewrites();
        let z1 = e.make_const(z);
        let q2 = e.make_free(nzq, vec![z1]);
        let r2 = e.reduce(q2);
        assert_eq!(e.rewrites(), 0, "condition N : NzNat fails for z");
        assert_eq!(e.node(r2).symbol(), nzq, "nz?(z) is its own normal form");
    }

    /// B2.3a audit-F-2 mitigation: a conditional equation whose condition reduces re-entrantly stays
    /// correct with safe-point GC enabled. GC is disabled *during* condition evaluation, so the nested
    /// reduce can't sweep the outer reduction's in-flight state; the result and rewrite count are
    /// identical to the GC-off run. (`ceq f(N) = z if g(N) = tt`, with `g(s^k z)` reducing in `k+1`.)
    #[test]
    fn conditional_reduce_is_stable_under_safe_point_gc() {
        fn run(interval: Option<u64>) -> (SymbolId, u64) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            let truth = e.add_sort("Truth");
            e.close_sorts();
            let z = e.add_op("z", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let tt = e.add_op("tt", vec![], truth);
            let g = e.add_op("g", vec![nat], truth);
            let f = e.add_op("f", vec![nat], nat);
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::op(s, vec![Term::var(0, nat)])]), // g(s N) = g(N)
                rhs: Term::op(g, vec![Term::var(0, nat)]),
                nr_vars: 1,
            });
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::constant(z)]), // g(z) = tt
                rhs: Term::constant(tt),
                nr_vars: 0,
            });
            e.add_conditional_equation(
                Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = z if g(N) = tt
                Term::constant(z),
                1,
                vec![ConditionFragment::Equality {
                    lhs: Term::op(g, vec![Term::var(0, nat)]),
                    rhs: Term::constant(tt),
                }],
            );
            e.set_gc_interval(interval);
            let n = numeral(&mut e, z, s, 20); // condition g(20) reduces in 21 rewrites
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        }
        let off = run(None);
        let on = run(Some(4)); // aggressive collection around (not during) the condition reduce
        assert_eq!(off.1, 22, "f(20) → z in 22 rewrites (21 condition + 1 equation)");
        assert_eq!(on, off, "conditional reduce identical with safe-point GC on — F-2 mitigation holds");
    }

    /// B2.3b `owise` equations (== reference binary, `conformance/owise.maude` OWISE-EQ): an `[owise]`
    /// equation fires only when no non-owise equation of the symbol matches.
    #[test]
    fn owise_equation_applies_when_no_normal_equation_matches() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let iszero = e.add_op("iszero", vec![nat], truth);
        // eq iszero(z) = tt .   eq iszero(N) = ff [owise] .
        e.add_equation(Equation {
            lhs: Term::op(iszero, vec![Term::constant(z)]),
            rhs: Term::constant(tt),
            nr_vars: 0,
        });
        e.add_owise_equation(Term::op(iszero, vec![Term::var(0, nat)]), Term::constant(ff), 1, Vec::new());

        // iszero(z): the specific non-owise equation matches.
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let q0 = e.make_free(iszero, vec![z0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r0).symbol(), tt, "iszero(z) = tt");

        // iszero(s z): nothing else matches → owise applies.
        e.reset_rewrites();
        let s0 = {
            let z1 = e.make_const(z);
            e.make_free(s, vec![z1])
        };
        let q1 = e.make_free(iszero, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r1).symbol(), ff, "iszero(s z) = ff via owise");
    }

    /// B2.3b (== reference binary, OWISE-COND): `owise` applies even when a non-owise *conditional*
    /// equation matched structurally but its condition failed. `ceq clamp(N)=z if N<=s z=tt` /
    /// `eq clamp(N)=s z [owise]`: clamp(0)=0 (2 rw), clamp(1)=0 (3 rw), clamp(2)=s z via owise (3 rw).
    #[test]
    fn owise_applies_when_conditional_equation_condition_fails() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let clamp = e.add_op("clamp", vec![nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq clamp(N) = z if N <= s z = tt .   eq clamp(N) = s z [owise] .
        e.add_conditional_equation(
            Term::op(clamp, vec![v(0)]),
            Term::constant(z),
            1,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), s_of(Term::constant(z))]),
                rhs: Term::constant(tt),
            }],
        );
        e.add_owise_equation(Term::op(clamp, vec![v(0)]), s_of(Term::constant(z)), 1, Vec::new());

        for (input, expected, rewrites) in [(0u32, 0u32, 2u64), (1, 0, 3), (2, 1, 3)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let c = e.make_free(clamp, vec![n]);
            let r = e.reduce(c);
            assert_eq!(e.rewrites(), rewrites, "clamp({input}) rewrite count");
            assert_eq!(decode(&e, r, z, s), expected, "clamp({input}) value");
        }
    }

    /// B2.3c conditional membership (== reference binary, `conformance/cmb.maude`):
    /// `cmb < M, N > : GoodPair if M <= N = tt` lowers a pair's sort only when its condition holds —
    /// and the condition's reductions count (`<z,sz>` is 2 rewrites: condition 1 + membership 1; the
    /// failing `<sz,z>` is 1, the condition reduce alone).
    #[test]
    fn conditional_membership_lowers_sort_when_condition_holds() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let goodpair = e.add_sort("GoodPair");
        let truth = e.add_sort("Truth");
        e.add_subsort(goodpair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let _ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(_ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // cmb < M, N > : GoodPair if M <= N = tt .
        e.add_conditional_membership(
            Term::op(pairop, vec![v(0), v(1)]),
            goodpair,
            2,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), v(1)]),
                rhs: Term::constant(tt),
            }],
        );

        // Build < a, b > (resetting the counter first) and read back its least sort + rewrite count.
        let build = |e: &mut Engine, a: u32, b: u32| -> (SortId, u64) {
            e.reset_rewrites();
            let na = numeral(e, z, s, a);
            let nb = numeral(e, z, s, b);
            let p = e.make_free(pairop, vec![na, nb]);
            (e.sort_of(p), e.rewrites())
        };
        assert_eq!(build(&mut e, 0, 1), (goodpair, 2), "< z, s z > : GoodPair, 2 rewrites");
        assert_eq!(build(&mut e, 1, 0), (pair, 1), "< s z, z > : Pair (condition fails), 1 rewrite");
        assert_eq!(build(&mut e, 0, 0), (goodpair, 2), "< z, z > : GoodPair, 2 rewrites");
        assert_eq!(build(&mut e, 1, 1), (goodpair, 3), "< s z, s z > : GoodPair, 3 rewrites");
    }

    /// B2.3d matching condition `:=` (== reference binary, `conformance/match-cond.maude` MATCH-COND):
    /// `ceq pred(N) = M if s M := N` binds the fresh `M` by matching the pattern `s M` against `N`. The
    /// `:=` match itself is not a rewrite (only the rhs application is); a non-matching subject (`z`)
    /// fails the condition.
    #[test]
    fn matching_condition_binds_fresh_variable() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pred = e.add_op("pred", vec![nat], nat);
        // ceq pred(N) = M if s M := N .   (N = var 0, M = var 1, introduced fresh by the `:=`)
        e.add_conditional_equation(
            Term::op(pred, vec![Term::var(0, nat)]),
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::var(0, nat),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(2u32, 1u32), (1, 0)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(pred, vec![n]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1, "pred({input}): one rewrite (the := match is not counted)");
            assert_eq!(decode(&e, r, z, s), expected, "pred({input}) = {expected}");
        }

        // pred(z): `s M := z` has no match → condition fails → no rewrite.
        e.reset_rewrites();
        let n0 = numeral(&mut e, z, s, 0);
        let q0 = e.make_free(pred, vec![n0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 0, "pred(z): the matching condition fails");
        assert_eq!(e.node(r0).symbol(), pred, "pred(z) is its own normal form");
    }

    /// B2.3d (== reference binary, MATCH-COND2): the matching subject itself reduces before the pattern
    /// is matched. `ceq f(N) = M if s M := g(N)` with `eq g(N) = s s N`: f(0)=1 and f(1)=2, each 2
    /// rewrites (g reduces once, then f→M).
    #[test]
    fn matching_condition_reduces_subject_first() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::var(0, nat)]), // g(N) = s s N
            rhs: Term::op(s, vec![Term::op(s, vec![Term::var(0, nat)])]),
            nr_vars: 1,
        });
        e.add_conditional_equation(
            Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = M if s M := g(N)
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::op(g, vec![Term::var(0, nat)]),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(0u32, 1u32), (1, 2)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 2, "f({input}): g reduces (1) + f→M (1)");
            assert_eq!(decode(&e, r, z, s), expected, "f({input}) = {expected}");
        }
    }

    /// B2.4 `[ctor]` (== reference binary): a constructor declaration is recorded but does **not**
    /// affect functional reduction — `s 0 + s s 0` is `s s s 0` in 3 rewrites either way.
    #[test]
    fn ctor_is_recorded_and_inert_for_reduction() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.set_ctor(z);
        e.set_ctor(s);
        assert!(e.is_constructor(z), "z is a constructor");
        assert!(e.is_constructor(s), "s is a constructor");
        assert!(!e.is_constructor(plus), "+ is a defined function, not a constructor");
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        let (a, b) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 3, "[ctor] does not change the rewrite count");
        assert_eq!(decode(&e, r, z, s), 3, "s 0 + s s 0 = s s s 0");
    }

    /// B2.4 evaluation strategy (== reference binary, `conformance/strat.maude`): `if_then_else_fi` with
    /// `strat (1 0)` reduces the condition then the top, leaving the unused branch unreduced. The chosen
    /// branch *is* reduced (it becomes the result), so `if tt then big else z` costs the `big` reduction
    /// while `if tt then z else big` does not.
    #[test]
    fn evaluation_strategy_is_lazy() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let big = e.add_op("big", vec![], nat);
        let ite = e.add_op("if", vec![truth, nat, nat], nat);
        e.set_strategy(ite, &[1, 0]); // reduce arg 1 (the condition), then top; branches lazy
        let v = |i| Term::var(i, nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s z
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(tt), v(0), v(1)]), // if tt then X else Y = X
            rhs: v(0),
            nr_vars: 2,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(ff), v(0), v(1)]), // if ff then X else Y = Y
            rhs: v(1),
            nr_vars: 2,
        });

        // big = s s z (sanity).
        e.reset_rewrites();
        let bnode = e.make_const(big);
        let rb = e.reduce(bnode);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(decode(&e, rb, z, s), 2, "big = s s z");

        // Each case: build if(cond, then, else) and reduce. (cond_is_tt, then_big, expected, rewrites)
        let cases = [
            (true, false, 0u32, 1u64),  // if tt then z   else big -> z      (else not reduced)
            (false, true, 0, 1),        // if ff then big else z   -> z      (then not reduced)
            (true, true, 2, 2),         // if tt then big else z   -> s s z  (chosen big IS reduced)
        ];
        for (cond_tt, then_big, expected, rewrites) in cases {
            e.reset_rewrites();
            let cond = if cond_tt { e.make_const(tt) } else { e.make_const(ff) };
            let then_arg = if then_big { e.make_const(big) } else { e.make_const(z) };
            let else_arg = if then_big { e.make_const(z) } else { e.make_const(big) };
            let q = e.make_free(ite, vec![cond, then_arg, else_arg]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), rewrites, "rewrite count for case {cond_tt}/{then_big}");
            assert_eq!(decode(&e, r, z, s), expected, "result for case {cond_tt}/{then_big}");
        }
    }

    #[test]
    #[should_panic]
    fn arity_mismatch_panics() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let f = e.add_op("f", vec![nat, nat], nat);
        let _ = e.make_free(f, Vec::new());
    }

    /// B1.1: an `assoc comm` operator classifies as the ACU theory and carries its axioms +
    /// identity; a plain operator stays Free. (The free hot path must be untouched by AC ops.)
    #[test]
    fn ac_operator_is_classified_acu() {
        use crate::symbol::Theory;
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let empty = e.add_op("empty", vec![], nat);
        let union = e.add_op_ac("union", vec![nat, nat], nat, Some(empty));
        let plus = e.add_op("+", vec![nat, nat], nat); // a free op, for contrast

        let u = e.symbol(union);
        assert_eq!(u.theory(), Theory::Acu);
        assert_eq!(u.identity(), Some(empty));
        assert_eq!(e.symbol(plus).theory(), Theory::Free, "a plain op is free");
        assert_eq!(e.symbol(empty).theory(), Theory::Free, "a constant is free");
    }

    #[test]
    #[should_panic(expected = "must be binary")]
    fn ac_operator_must_be_binary() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let _ = e.add_op_ac("bad", vec![nat, nat, nat], nat, None);
    }

    /// Engine with constants `a`,`b`,`c` and an `assoc comm` `+` (no identity) over sort `S`.
    fn ac_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        (e, s, a, b, c, plus)
    }

    /// B1.2: ACU construction is canonical modulo commutativity and associativity — `a+b == b+a`,
    /// and `(a+b)+c == a+(b+c) == a+b+c` (flattened to a 3-element multiset).
    #[test]
    fn acu_canonical_modulo_ac() {
        let (mut e, _s, a, b, c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        };
        let ba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y])
        };
        assert!(e.deep_equal(ab, ba), "a+b == b+a");
        assert_eq!(
            e.runtime().dag_compare(ab, ba),
            std::cmp::Ordering::Equal,
            "and the total order agrees"
        );

        let abc_left = {
            // (a+b)+c — the left arg is itself an ACU node, must flatten
            let (x, y) = (e.make_const(a), e.make_const(b));
            let ab = e.make_ac(plus, vec![x, y]);
            let z = e.make_const(c);
            e.make_ac(plus, vec![ab, z])
        };
        let abc_right = {
            let (y, z) = (e.make_const(b), e.make_const(c));
            let bc = e.make_ac(plus, vec![y, z]);
            let x = e.make_const(a);
            e.make_ac(plus, vec![x, bc])
        };
        let abc_flat = {
            let (x, y, z) = (e.make_const(a), e.make_const(b), e.make_const(c));
            e.make_ac(plus, vec![x, y, z])
        };
        assert!(e.deep_equal(abc_left, abc_right), "(a+b)+c == a+(b+c)");
        assert!(e.deep_equal(abc_left, abc_flat), "(a+b)+c == a+b+c");
        assert_eq!(e.node(abc_flat).children().count(), 3, "flattened to 3 children");
    }

    /// B1.2: identity (`id:`) elements vanish and the multiset collapses — `a+e == a`, `e+e == e`,
    /// `a+e+b == a+b`.
    #[test]
    fn acu_identity_collapses() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, Some(unit));

        let a_plus_e = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_ac(plus, vec![x, u])
        };
        assert_eq!(e.node(a_plus_e).symbol(), a, "a + e collapses to a");

        let e_plus_e = {
            let (u1, u2) = (e.make_const(unit), e.make_const(unit));
            e.make_ac(plus, vec![u1, u2])
        };
        assert_eq!(e.node(e_plus_e).symbol(), unit, "e + e collapses to e");

        let aeb = {
            let (x, u, y) = (e.make_const(a), e.make_const(unit), e.make_const(b));
            e.make_ac(plus, vec![x, u, y])
        };
        assert_eq!(e.node(aeb).children().count(), 2, "a + e + b == a + b (2 children)");
    }

    /// B1.2: equal elements merge into a multiplicity (`a+a` keeps two children via one `(a,2)` pair),
    /// and a lone element never gets wrapped (`make_ac` of one element is that element).
    #[test]
    fn acu_merges_multiplicity_and_never_wraps_singleton() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let aa = {
            let (x, y) = (e.make_const(a), e.make_const(a)); // distinct ids, structurally equal
            e.make_ac(plus, vec![x, y])
        };
        assert_eq!(e.node(aa).children().count(), 2, "a + a has two children (multiplicity 2)");
        assert_eq!(e.node(aa).symbol(), plus, "a + a is an ACU node");

        let lone = e.make_const(a);
        let wrapped = e.make_ac(plus, vec![lone]);
        assert_eq!(wrapped, lone, "make_ac of a single element collapses to it");
    }

    /// B1.2: GC traces an ACU DAG through the visitor (reachable kept, rest reclaimed) and `deep_equal`
    /// is modulo-AC across *distinct* element ids.
    #[test]
    fn acu_gc_and_modulo_equality() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        }; // ab + a0 + b0 = 3 nodes
        let _garbage = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y]) // structurally equal to ab but distinct ids
        };
        assert!(e.deep_equal(ab, _garbage), "b+a == a+b across distinct ids");
        assert_eq!(e.gc([ab]), 3, "the unreachable b+a subgraph (3 nodes) is reclaimed");
        assert_eq!(e.node(ab).children().count(), 2, "ab survives intact");
    }

    #[test]
    #[should_panic(expected = "make_acu")]
    fn make_free_on_ac_operator_panics() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let a0 = e.make_const(a);
        let _ = e.make_free(plus, vec![a0, a0]); // building an ACU op as a free node is a bug
    }

    fn s_of_zero(e: &mut Engine, zero: SymbolId, s: SymbolId) -> DagId {
        let z = e.make_const(zero);
        e.make_free(s, vec![z])
    }

    /// B1.5 reduce lock (== reference binary): `op _+_ [assoc comm]`, `eq X + 0 = X`;
    /// `red s 0 + 0 + s 0 + s 0` → `s 0 + s 0 + s 0` in **1** rewrite (X absorbs the rest; the ground
    /// `0` is consumed and spliced away as residue).
    #[test]
    fn ac_reduce_ground_consumed_with_extension() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op_ac("+", vec![nat, nat], nat, None);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        let (s0a, s0b, s0c) =
            (s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s));
        let z = e.make_const(zero);
        let subject = e.make_ac(plus, vec![s0a, z, s0b, s0c]); // s0 + 0 + s0 + s0
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "one rewrite removes the 0");
        let kids: Vec<_> = e.node(r).children().collect();
        assert_eq!(kids.len(), 3, "result is s0 + s0 + s0");
        assert!(kids.iter().all(|&k| e.node(k).symbol() == s), "all three are successors");
    }

    /// B1.5 reduce lock: ground AC pattern needing a residue splice — `eq a + a = a` on `a + a + b`
    /// → `a + b` in **1** rewrite (the matched `{a,a}` is replaced by `a`, residue `b` spliced).
    #[test]
    fn ac_reduce_ground_pattern_residue_splice() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::constant(a)]),
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (a0, a1, b0) = (e.make_const(a), e.make_const(a), e.make_const(b));
        let subject = e.make_ac(plus, vec![a0, a1, b0]); // a + a + b
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + a = a fires once");
        let mut kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        kids.sort_by_key(|s| format!("{s:?}"));
        assert_eq!(kids, vec![a, b], "result is a + b");
    }

    /// B1.5 reduce lock (the subtle one — non-linear AC variable + identity): `op _;_ [assoc comm
    /// id: empty]`, `eq N ; N = N`; `red 0 ; s0 ; 0 ; s0` → `0 ; s0` in **2** rewrites. Reproducing
    /// the count needs minimal-first solution order + skipping the empty (no-op) binding.
    #[test]
    fn ac_reduce_set_idempotency_two_rewrites() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let empty = e.add_op("empty", vec![], nat);
        let set = e.add_op_ac(";", vec![nat, nat], nat, Some(empty));
        e.add_equation(Equation {
            lhs: Term::op(set, vec![Term::var(0, nat), Term::var(0, nat)]), // N ; N
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        let (z0, z1) = (e.make_const(zero), e.make_const(zero));
        let (s0a, s0b) = (s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s));
        let subject = e.make_ac(set, vec![z0, s0a, z1, s0b]); // 0 ; s0 ; 0 ; s0
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 2, "two duplicate-removals (== reference binary)");
        assert_eq!(e.node(r).children().count(), 2, "result is 0 ; s0");
    }

    /// B1.5 reduce lock: non-linear pure-AC idempotency `eq X + X = X` on `a+a+a+a` → `a` in **3**
    /// rewrites (X binds a single `a` each step — minimal binding, not the whole half).
    #[test]
    fn ac_reduce_nonlinear_idempotency_three_rewrites() {
        let (mut e, s, a, _b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, s), Term::var(0, s)]), // X + X
            rhs: Term::var(0, s),
            nr_vars: 1,
        });
        let (a0, a1, a2, a3) =
            (e.make_const(a), e.make_const(a), e.make_const(a), e.make_const(a));
        let subject = e.make_ac(plus, vec![a0, a1, a2, a3]); // a + a + a + a
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 3, "X binds a single `a` each step (== reference binary)");
        assert_eq!(e.node(r).symbol(), a, "result collapses to the constant a");
    }

    /// B1.5 reduce lock (lone-variable collector strategy, == reference binary): `eq a + X = b` on
    /// `a + c + c` → `b` in 1 rewrite. X absorbs `c + c` (a whole match), NOT a minimal binding that
    /// would leave `b + c` — the system is non-confluent under extension and Maude takes the collector
    /// match. (Regression for the latent bug where a lone linear variable bound minimally.)
    #[test]
    fn ac_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::var(0, s)]), // a + X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, c0, c1]); // a + c + c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + X = b fires once");
        assert_eq!(e.node(r).symbol(), b, "result is b (X absorbed c + c), not b + c");
    }

    /// Audit F-A guard: a theory-rooted (AC) subterm under a *free* operator in a pattern is rejected
    /// **loudly** — the recursive free matcher would otherwise silently fail to match it, leaving the
    /// equation quietly dead. Cross-theory pattern composition (the `Sequence` arm) is a B1 follow-up.
    #[test]
    #[should_panic(expected = "theory-rooted")]
    fn free_pattern_over_theory_subterm_is_rejected() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let c = e.add_op("cc", vec![], s);
        let f = e.add_op("f", vec![s], s); // free, unary
        // eq f(a + b) = cc   — `a + b` is an AC subterm under the free `f`.
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::op(plus, vec![Term::constant(a), Term::constant(b)])]),
            rhs: Term::constant(c),
            nr_vars: 0,
        });
    }

    /// The guard's boundary: a *variable* over a theory subject is fine (it binds the whole AC node),
    /// so `eq f(X) = g(X)` compiles and fires on `f(a + b)`. Only a *structured* theory sub-pattern is
    /// rejected — not a variable that happens to bind a theory term.
    #[test]
    fn free_pattern_with_variable_over_theory_subject_is_allowed() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let g = e.add_op("g", vec![s], s);
        let f = e.add_op("f", vec![s], s);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, s)]), // f(X)
            rhs: Term::op(g, vec![Term::var(0, s)]), // g(X)
            nr_vars: 1,
        });
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let ab = e.make_ac(plus, vec![a0, b0]); // a + b
        let subject = e.make_free(f, vec![ab]); // f(a + b)
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "f(X) = g(X) fires once on f(a + b)");
        assert_eq!(e.node(r).symbol(), g, "result is g(a + b)");
    }

    /// The symmetric case the same guard closes: a theory-rooted *ground* subterm under a *theory*
    /// operator (an ACU `+` term as a ground argument of the ACU `;`) is handed to the free matcher as
    /// a "ground" and would fail silently — so it too is rejected loudly.
    #[test]
    #[should_panic(expected = "theory-rooted")]
    fn theory_ground_subterm_under_theory_operator_is_rejected() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let semi = e.add_op_ac(";", vec![s, s], s, None);
        // eq (a + b) ; c = d   — `(a + b)` is a theory-rooted ground subterm under the ACU `;`.
        let ab = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        e.add_equation(Equation {
            lhs: Term::op(semi, vec![ab, Term::constant(c)]),
            rhs: Term::constant(d),
            nr_vars: 0,
        });
    }

    /// Engine with constants `a`,`b`,`c`,`d` and an `assoc` (not comm) `__` over sort `E`.
    fn au_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let cat = e.add_op_au("__", vec![s, s], s, None);
        (e, s, a, b, c, d, cat)
    }

    /// B1 AU reduce lock (extension on both ends, == reference binary): `op __ [assoc]`, `eq b c = a`;
    /// `red d b c d` → `d a d` in 1 rewrite (the contiguous `b c` is matched, prefix `d` and suffix
    /// `d` are spliced back around the rhs — order preserved).
    #[test]
    fn au_reduce_ground_pattern_extension_both_ends() {
        let (mut e, _s, a, b, c, d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(b), Term::constant(c)]), // b c
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (d0, b0, c0, d1) =
            (e.make_const(d), e.make_const(b), e.make_const(c), e.make_const(d));
        let subject = e.make_au(cat, vec![d0, b0, c0, d1]); // d b c d
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "b c = a fires once");
        let kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        assert_eq!(kids, vec![d, a, d], "result is the ordered sequence d a d");
    }

    /// B1 AU reduce lock (lone-variable collector, == reference binary): `eq a X = b` on `a c c` → `b`
    /// in 1 rewrite (X absorbs the ordered tail `c c`; not `b c` from a minimal binding).
    #[test]
    fn au_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, _d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(a), Term::var(0, s)]), // a X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_au(cat, vec![a0, c0, c1]); // a c c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a X = b fires once");
        assert_eq!(e.node(r).symbol(), b, "result is b (X absorbed c c)");
    }

    /// B1 CUI canonicalization (== reference binary): `comm` orders the pair (`f(b,a) == f(a,b)`);
    /// `idem` collapses `g(a,a)` to `a`; `id:` collapses `h(a,e)` to `a` — all at construction.
    #[test]
    fn cui_canonical_comm_idem_identity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, false, None);
        let g = e.add_op_cui("g", vec![s, s], s, true, None); // idem
        let h = e.add_op_cui("h", vec![s, s], s, false, Some(unit)); // id: e

        let fab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_cui(f, x, y)
        };
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a) → canonical f(a, b)
        };
        assert!(e.deep_equal(fab, fba), "f(a, b) == f(b, a) (comm)");

        let gaa = {
            let (x, y) = (e.make_const(a), e.make_const(a));
            e.make_cui(g, x, y)
        };
        assert_eq!(e.node(gaa).symbol(), a, "g(a, a) collapses to a (idem)");

        let hae = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_cui(h, x, u)
        };
        assert_eq!(e.node(hae).symbol(), a, "h(a, e) collapses to a (id:)");
    }

    /// B1 CUI reduce lock (== reference binary): `eq f(a, b) = c` matches `f(b, a)` modulo
    /// commutativity → `c` in 1 rewrite.
    #[test]
    fn cui_reduce_modulo_commutativity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, false, None);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::constant(a), Term::constant(b)]), // f(a, b)
            rhs: Term::constant(c),
            nr_vars: 0,
        });
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a)
        };
        let r = e.reduce(fba);
        assert_eq!(e.rewrites(), 1, "f(a,b)=c matches f(b,a) modulo comm");
        assert_eq!(e.node(r).symbol(), c, "result is c");
    }

    /// Engine with sorts `Zero NzNat < Nat`, `0 : Zero`, and a unary `iter` successor `s_ : Nat -> NzNat`.
    fn iter_ctx() -> (Engine, SortId, SortId, SortId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        (e, zero, nznat, nat, z, s)
    }

    /// Build `s^n(0)` (a fresh `0` each call, so subjects don't alias).
    fn iter_num(e: &mut Engine, z: SymbolId, s: SymbolId, n: u64) -> DagId {
        let z0 = e.make_const(z);
        e.make_iter(s, n, z0)
    }

    /// Decode an `s^n(0)` numeral (or the `0` constant) back to `n`.
    fn decode_nat(e: &Engine, id: DagId) -> u64 {
        match &e.node(id).term {
            NodeTerm::S { count, .. } => count.to_usize().expect("small numeral") as u64,
            _ => 0,
        }
    }

    /// B3.2 S-theory construction + sort (== reference binary, `conformance/iter.maude` ITER): `s^n(0)`
    /// stores the count compactly, `s^0(x)` collapses to `x`, nested successors flatten, and the sort
    /// follows the successor's declaration (`s^n(0) : NzNat` for n >= 1, `0 : Zero`).
    #[test]
    fn iter_node_construction_and_sort() {
        let (mut e, zero, nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        assert_eq!(e.sort_of(z0), zero, "0 : Zero");
        let s1 = e.make_iter(s, 1, z0);
        assert_eq!(e.sort_of(s1), nznat, "s 0 : NzNat");
        let s5 = e.make_iter(s, 5, z0);
        assert_eq!(e.sort_of(s5), nznat, "s^5 0 : NzNat");

        let collapse = e.make_iter(s, 0, z0);
        assert_eq!(collapse, z0, "s^0(0) collapses to 0");

        let s3 = e.make_iter(s, 3, z0);
        let s2_s3 = e.make_iter(s, 2, s3); // s^2(s^3(0))
        assert!(e.deep_equal(s2_s3, s5), "s^2(s^3(0)) flattens to s^5(0)");
        assert_eq!(e.node(s2_s3).children().count(), 1, "an S node has one child (the base)");
    }

    /// B3.2 THE soundness gate (the audit's #1 B3 trap): the S `count` is scalar payload, not a child,
    /// so `deep_equal`/`dag_compare` must compare it — else `s^2(0)` and `s^3(0)` (both child `[0]`)
    /// would compare equal.
    #[test]
    fn iter_equality_and_order_use_the_count() {
        let (mut e, _zero, _nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        let (s2a, s2b, s3) = (e.make_iter(s, 2, z0), e.make_iter(s, 2, z0), e.make_iter(s, 3, z0));
        assert!(e.deep_equal(s2a, s2b), "s^2(0) == s^2(0) (distinct ids, equal count)");
        assert!(!e.deep_equal(s2a, s3), "s^2(0) != s^3(0) — count distinguishes them");
        assert_eq!(e.runtime().dag_compare(s2a, s3), Ordering::Less, "s^2 < s^3 by count");
        assert_eq!(e.runtime().dag_compare(s3, s2a), Ordering::Greater);
        assert_eq!(e.runtime().dag_compare(s2a, s2b), Ordering::Equal);
    }

    /// B3.2 S-theory reduce, ground equation (== reference binary, ITER): `eq s s 0 = 0` rewrites
    /// `s^5(0)` modulo the successor extension — `s^5 -> s^3 -> s^1`, 2 rewrites, result `s 0 : NzNat`.
    #[test]
    fn iter_reduce_ground_equation() {
        let (mut e, _zero, nznat, _nat, z, s) = iter_ctx();
        e.add_equation(Equation {
            lhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]), // s s 0
            rhs: Term::constant(z),
            nr_vars: 0,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1 (2 rewrites)");
        assert_eq!(e.sort_of(r), nznat, "result s 0 : NzNat");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "result is s 0");
    }

    /// B3.2 S-theory reduce, variable equation (== reference binary, ITER-VAR): `eq s s s X = s X`
    /// rewrites `s^5(0) -> s 0` (2 rewrites) and `s^3(0) -> s 0` (1) — the variable absorbs the
    /// successor surplus (the extension's first/whole solution).
    #[test]
    fn iter_reduce_variable_equation() {
        let (mut e, _zero, _nznat, nat, z, s) = iter_ctx();
        let sx = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: sx(sx(sx(Term::var(0, nat)))), // s s s X
            rhs: sx(Term::var(0, nat)),         // s X
            nr_vars: 1,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "s^5 -> s 0");

        e.reset_rewrites();
        let s3 = iter_num(&mut e, z, s, 3);
        let r2 = e.reduce(s3);
        assert_eq!(e.rewrites(), 1, "s^3 -> s 0");
        let s1b = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r2, s1b));
    }

    /// B3.3 built-in seam (== reference binary, `conformance/bool.maude`): `EqualitySymbol` (`_~_`)
    /// reduces to `tt`/`ff` by structural equality (1 rewrite); the lazy `BranchSymbol` (`myif`) selects
    /// a branch and leaves the dead branch **unreduced** (`myif(tt,0,big)` = 0 in 1 rewrite, while
    /// `myif(tt,big,0)` reduces the chosen `big` = `s s 0` for 2). Attached via `set_special`.
    #[test]
    fn builtin_equality_and_branch_over_bool() {
        use crate::symbol::SpecialOp;
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let big = e.add_op("big", vec![], nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s 0
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        let eq = e.add_op("~", vec![nat, nat], truth);
        e.set_special(eq, SpecialOp::Equality { eq: tt, neq: ff });
        let myif = e.add_op("myif", vec![truth, nat, nat], nat);
        e.set_special(myif, SpecialOp::Branch { tests: vec![tt, ff] });

        // _~_ over (reduced) Nat numerals: structural equality → tt/ff, 1 rewrite each.
        let mut eqtest = |a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(&mut e, z, s, a), iter_num(&mut e, z, s, b));
            let q = e.make_free(eq, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(eqtest(2, 2), (tt, 1), "s^2 0 ~ s^2 0 = tt");
        assert_eq!(eqtest(2, 3), (ff, 1), "s^2 0 ~ s^3 0 = ff");
        assert_eq!(eqtest(0, 0), (tt, 1), "0 ~ 0 = tt");

        // myif(tt, 0, big) -> 0, 1 rewrite (dead `big` never reduced).
        e.reset_rewrites();
        let (c, t0, ebig) = (e.make_const(tt), iter_num(&mut e, z, s, 0), e.make_const(big));
        let q = e.make_free(myif, vec![c, t0, ebig]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(tt, 0, big) = 0");
        assert_eq!(e.rewrites(), 1, "selection only — big unreduced");

        // myif(tt, big, 0) -> s s 0, 2 rewrites (selection + big reduces).
        e.reset_rewrites();
        let (c, tbig, e0) = (e.make_const(tt), e.make_const(big), iter_num(&mut e, z, s, 0));
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 2, "selection + big = s s 0");
        let s2 = iter_num(&mut e, z, s, 2);
        assert!(e.deep_equal(r, s2), "myif(tt, big, 0) = s s 0");

        // myif(ff, big, 0) -> 0, 1 rewrite (else branch; big unreduced).
        e.reset_rewrites();
        let (c, tbig, e0) = (e.make_const(ff), e.make_const(big), iter_num(&mut e, z, s, 0));
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(ff, big, 0) = 0");
        assert_eq!(e.rewrites(), 1, "else branch — big unreduced");
    }

    /// B3.4 NAT built-in number ops (== reference binary, `conformance/nat.maude`): `_+_`/`_*_`/`gcd`
    /// (ACU_NumberOp, fold the multiset with multiplicity) and `_quo_`/`_rem_`/`_^_`/`_<_`/`_<=_`
    /// (NumberOp). Each is 1 rewrite; the result sort follows the value (`s^n(0) : NzNat`); a
    /// non-numeric operand survives as ACU residue (`x + 2 + 3 = x + 5`).
    #[test]
    fn builtin_nat_arithmetic_and_comparisons() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let nh = NatHooks { succ: s, zero: z, minus: None }; // NAT: no negatives
        let bh = BoolHooks { true_: tt, false_: ff };
        // ACU ops: NzNat Nat -> NzNat overloaded Nat Nat -> Nat (the prelude shape; F-B-completed).
        let acu_op = |e: &mut Engine, name: &'static str, op: NumOp| -> SymbolId {
            let o = e.add_op_ac(name, vec![nznat, nat], nznat, None);
            e.add_op_decl(o, vec![nat, nat], nat);
            e.set_special(o, SpecialOp::AcuNumberOp { op, nat: nh });
            o
        };
        let plus = acu_op(&mut e, "+", NumOp::Add);
        let times = acu_op(&mut e, "*", NumOp::Mul);
        let gcd = acu_op(&mut e, "gcd", NumOp::Gcd);
        // free arithmetic → Nat, and relational → Truth.
        let num_op = |e: &mut Engine, name: &'static str, op: NumOp, b: Option<BoolHooks>| -> SymbolId {
            let rng = if b.is_some() { truth } else { nat };
            let o = e.add_op(name, vec![nat, nat], rng);
            e.set_special(o, SpecialOp::NumberOp { op, nat: nh, bool_: b });
            o
        };
        let quo = num_op(&mut e, "quo", NumOp::Quo, None);
        let rem = num_op(&mut e, "rem", NumOp::Rem, None);
        let pow = num_op(&mut e, "^", NumOp::Pow, None);
        let lt = num_op(&mut e, "<", NumOp::Lt, Some(bh));
        let le = num_op(&mut e, "<=", NumOp::Le, Some(bh));
        let x = e.add_op("x", vec![], nat);

        // ACU op of two numerals → (decoded value, sort, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, SortId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.sort_of(r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, 3), (5, nznat, 1), "2 + 3 = 5");
        assert_eq!(acu(&mut e, plus, 2, 2), (4, nznat, 1), "2 + 2 = 4 (multiplicity fold)");
        assert_eq!(acu(&mut e, plus, 0, 5), (5, nznat, 1), "0 + 5 = 5");
        assert_eq!(acu(&mut e, times, 3, 4), (12, nznat, 1), "3 * 4 = 12");
        assert_eq!(acu(&mut e, times, 2, 2), (4, nznat, 1), "2 * 2 = 4");
        assert_eq!(acu(&mut e, gcd, 12, 18), (6, nznat, 1), "gcd(12, 18) = 6");

        // Free arithmetic op of two numerals → (decoded value, rewrites).
        let arith = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.rewrites())
        };
        assert_eq!(arith(&mut e, quo, 7, 2), (3, 1), "7 quo 2 = 3");
        assert_eq!(arith(&mut e, rem, 7, 2), (1, 1), "7 rem 2 = 1");
        assert_eq!(arith(&mut e, pow, 2, 10), (1024, 1), "2 ^ 10 = 1024");

        // Relational op → Truth constant.
        let cmp = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(cmp(&mut e, lt, 2, 3), (tt, 1), "2 < 3 = tt");
        assert_eq!(cmp(&mut e, lt, 3, 2), (ff, 1), "3 < 2 = ff");
        assert_eq!(cmp(&mut e, le, 3, 3), (tt, 1), "3 <= 3 = tt");

        // Residue: x + 2 + 3 = x + 5 (the non-numeric x survives), NzNat, 1 rewrite.
        e.reset_rewrites();
        let (xn, n2, n3) = (e.make_const(x), iter_num(&mut e, z, s, 2), iter_num(&mut e, z, s, 3));
        let q = e.make_ac(plus, vec![xn, n2, n3]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 1, "x + 2 + 3 = x + 5 in 1 rewrite");
        assert_eq!(e.sort_of(r), nznat, "x + 5 : NzNat (asymmetric overload, F-B)");
        assert_eq!(e.node(r).symbol(), plus, "result is still a + node");
        let kids: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(kids.len(), 2, "x + 5 has two operands");
        let mut has_x = false;
        let mut has_5 = false;
        for k in kids {
            if e.node(k).symbol() == x {
                has_x = true;
            } else if decode_nat(&e, k) == 5 {
                has_5 = true;
            }
        }
        assert!(has_x && has_5, "x + 5 = {{x, s^5(0)}}");
    }

    /// B3.5 INT signed arithmetic (== reference binary, `conformance/int.maude`): negatives are
    /// `-(s^n(0))` via `MinusSymbol` (a negative numeral is canonical — 0 rewrites; `-(-x)` and `-0`
    /// reduce in 1). The same ACU/Number ops as NAT, lifted to signed via the `minus` hook; `quo`/`rem`
    /// truncate toward zero. The result sort follows the value (`NzInt`/`NzNat`/`Zero`).
    #[test]
    fn builtin_int_signed_arithmetic() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint); // -_ : NzNat -> NzInt
        e.add_op_decl(minus, vec![int], int); //          -_ : Int -> Int
        let nh = NatHooks { succ: s, zero: z, minus: Some(minus) };
        let bh = BoolHooks { true_: tt, false_: ff };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let plus = e.add_op_ac("+", vec![int, int], int, None);
        e.set_special(plus, SpecialOp::AcuNumberOp { op: NumOp::Add, nat: nh });
        let times = e.add_op_ac("*", vec![int, int], int, None);
        e.set_special(times, SpecialOp::AcuNumberOp { op: NumOp::Mul, nat: nh });
        let sub = e.add_op("-bin", vec![int, int], int);
        e.set_special(sub, SpecialOp::NumberOp { op: NumOp::Sub, nat: nh, bool_: None });
        let quo = e.add_op("quo", vec![int, nzint], int);
        e.set_special(quo, SpecialOp::NumberOp { op: NumOp::Quo, nat: nh, bool_: None });
        let rem = e.add_op("rem", vec![int, nzint], int);
        e.set_special(rem, SpecialOp::NumberOp { op: NumOp::Rem, nat: nh, bool_: None });
        let lt = e.add_op("<", vec![int, int], truth);
        e.set_special(lt, SpecialOp::NumberOp { op: NumOp::Lt, nat: nh, bool_: Some(bh) });

        // Build a signed numeral `v` (`s^v(0)`, or `-(s^|v|(0))`).
        let mk = |e: &mut Engine, v: i64| -> DagId {
            if v >= 0 {
                iter_num(e, z, s, v as u64)
            } else {
                let p = iter_num(e, z, s, (-v) as u64);
                e.make_free(minus, vec![p])
            }
        };
        // Decode a signed numeral.
        let di = |e: &Engine, id: DagId| -> i64 {
            match &e.node(id).term {
                NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                    -(decode_nat(e, args[0]) as i64)
                }
                _ => decode_nat(e, id) as i64,
            }
        };

        // Negation: `- 3` is canonical (0 rewrites); `- - 3` and `- 0` reduce in 1.
        e.reset_rewrites();
        let m3 = mk(&mut e, -3);
        let r = e.reduce(m3);
        assert_eq!((di(&e, r), e.rewrites()), (-3, 0), "- 3 = -3 (canonical)");
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzInt", "-3 : NzInt");
        e.reset_rewrites();
        let p3 = mk(&mut e, 3);
        let m3a = e.make_free(minus, vec![p3]);
        let mm3 = e.make_free(minus, vec![m3a]);
        let r = e.reduce(mm3);
        assert_eq!((di(&e, r), e.rewrites()), (3, 1), "- - 3 = 3");
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let m0 = e.make_free(minus, vec![z0]);
        let r = e.reduce(m0);
        assert_eq!((di(&e, r), e.rewrites()), (0, 1), "- 0 = 0");

        // Binary ops over an ACU operator (+, *) → (decoded value, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, -5), (-3, 1), "2 + -5 = -3");
        assert_eq!(acu(&mut e, plus, -2, -3), (-5, 1), "-2 + -3 = -5");
        assert_eq!(acu(&mut e, times, 3, -2), (-6, 1), "3 * -2 = -6");
        assert_eq!(acu(&mut e, times, -2, -3), (6, 1), "-2 * -3 = 6");

        // Binary free arithmetic (-, quo, rem) → (decoded value, rewrites).
        let bin = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(bin(&mut e, sub, 2, 5), (-3, 1), "2 - 5 = -3");
        assert_eq!(bin(&mut e, sub, 5, 2), (3, 1), "5 - 2 = 3");
        assert_eq!(bin(&mut e, quo, 7, -2), (-3, 1), "7 quo -2 = -3 (toward zero)");
        assert_eq!(bin(&mut e, rem, -7, 2), (-1, 1), "-7 rem 2 = -1 (dividend's sign)");

        // Comparison → Truth.
        let cmp = |e: &mut Engine, a: i64, b: i64| -> SymbolId {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(lt, vec![na, nb]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, -2, 3), tt, "-2 < 3 = tt");
        assert_eq!(cmp(&mut e, 3, -2), ff, "3 < -2 = ff");
    }

    /// B3.6 NA theory + STRING + QID (== reference binary, `conformance/string.maude`): strings/qids
    /// are atomic `NodeTerm::Na` constants. `StringOpSymbol` does concat / length / substr /
    /// comparisons; quoted-ids match only themselves via the Na equality arm (through `EqualitySymbol`).
    #[test]
    fn builtin_string_and_qid() {
        use crate::dag::NaValue;
        use crate::symbol::{BoolHooks, NatHooks, SpecialOp, StrOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let str_s = e.add_sort("Str");
        let qid_s = e.add_sort("Qid");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let strsym = e.add_op("<Strings>", vec![], str_s);
        let qidsym = e.add_op("<Qids>", vec![], qid_s);
        let nh = NatHooks { succ: s, zero: z, minus: None };
        let bh = BoolHooks { true_: tt, false_: ff };
        let concat = e.add_op(".", vec![str_s, str_s], str_s);
        e.set_special(concat, SpecialOp::StringOp { op: StrOp::Concat, str_sym: strsym, nat: None, bool_: None });
        let len = e.add_op("len", vec![str_s], nat);
        e.set_special(len, SpecialOp::StringOp { op: StrOp::Length, str_sym: strsym, nat: Some(nh), bool_: None });
        let sub = e.add_op("sub", vec![str_s, nat, nat], str_s);
        e.set_special(sub, SpecialOp::StringOp { op: StrOp::Substr, str_sym: strsym, nat: Some(nh), bool_: None });
        let lt = e.add_op("lt", vec![str_s, str_s], truth);
        e.set_special(lt, SpecialOp::StringOp { op: StrOp::Lt, str_sym: strsym, nat: None, bool_: Some(bh) });
        let se = e.add_op("se", vec![str_s, str_s], truth);
        e.set_special(se, SpecialOp::Equality { eq: tt, neq: ff });
        let qe = e.add_op("qe", vec![qid_s, qid_s], truth);
        e.set_special(qe, SpecialOp::Equality { eq: tt, neq: ff });

        let dstr = |e: &Engine, id: DagId| -> String {
            match &e.node(id).term {
                NodeTerm::Na { value: NaValue::Str(v), .. } => v.to_string(),
                _ => panic!("not a string node"),
            }
        };

        // concat
        e.reset_rewrites();
        let (a, b) = (e.make_string(strsym, "ab"), e.make_string(strsym, "cd"));
        let q = e.make_free(concat, vec![a, b]);
        let r = e.reduce(q);
        assert_eq!((dstr(&e, r), e.rewrites()), ("abcd".into(), 1), "\"ab\" . \"cd\" = \"abcd\"");

        // length → Nat (sort follows the value)
        e.reset_rewrites();
        let h = e.make_string(strsym, "hello");
        let q = e.make_free(len, vec![h]);
        let r = e.reduce(q);
        assert_eq!((decode_nat(&e, r), e.rewrites()), (5, 1), "len(\"hello\") = 5");
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzNat");
        let empty = e.make_string(strsym, "");
        let q = e.make_free(len, vec![empty]);
        let r = e.reduce(q);
        assert_eq!(decode_nat(&e, r), 0, "len(\"\") = 0");
        assert_eq!(e.sorts().name(e.sort_of(r)), "Zero");

        // substr(s, start, len)
        e.reset_rewrites();
        let (hh, n1, n3) = (e.make_string(strsym, "hello"), iter_num(&mut e, z, s, 1), iter_num(&mut e, z, s, 3));
        let q = e.make_free(sub, vec![hh, n1, n3]);
        let r = e.reduce(q);
        assert_eq!((dstr(&e, r), e.rewrites()), ("ell".into(), 1), "sub(\"hello\", 1, 3) = \"ell\"");

        // string comparison + NA equality (string + qid)
        let cmp = |e: &mut Engine, op: SymbolId, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (e.make_string(strsym, x), e.make_string(strsym, y));
            let q = e.make_free(op, vec![a, b]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, lt, "abc", "abd"), tt, "\"abc\" < \"abd\"");
        assert_eq!(cmp(&mut e, lt, "b", "abc"), ff, "\"b\" < \"abc\" is false");
        assert_eq!(cmp(&mut e, se, "abc", "abc"), tt, "\"abc\" == \"abc\"");
        assert_eq!(cmp(&mut e, se, "abc", "abd"), ff, "\"abc\" == \"abd\" is false");

        // quoted-id NA equality (matches only itself)
        let qcmp = |e: &mut Engine, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (e.make_qid(qidsym, x), e.make_qid(qidsym, y));
            let q = e.make_free(qe, vec![a, b]);
            let r = e.reduce(q);
            e.node(r).symbol()
        };
        assert_eq!(qcmp(&mut e, "foo", "foo"), tt, "'foo == 'foo");
        assert_eq!(qcmp(&mut e, "foo", "bar"), ff, "'foo == 'bar is false");
    }

    #[test]
    fn reduces_peano_addition() {
        // sorts Nat; ops 0, s_, _+_; eqs  N + 0 = N  and  N + s M = s (N + M)
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        // peano(n): build s^n(0)
        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let two_a = peano(&mut e, zero, s, 2);
        let two_b = peano(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]); // 2 + 2

        let result = e.reduce(sum);
        let four = peano(&mut e, zero, s, 4);
        assert!(e.deep_equal(result, four), "2 + 2 should reduce to s s s s 0");
        assert_eq!(e.rewrites(), 3, "rewrite count matches reference Maude");
    }

    #[test]
    fn reduces_peano_multiplication() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let times = e.add_op("*", vec![nat, nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // N + 0 = N ; N + s M = s (N + M)
        e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), Term::constant(zero)]), rhs: v(0), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        // N * 0 = 0 ; N * s M = (N * M) + N
        e.add_equation(Equation { lhs: Term::op(times, vec![v(0), Term::constant(zero)]), rhs: Term::constant(zero), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(times, vec![v(0), s_of(v(1))]),
            rhs: Term::op(plus, vec![Term::op(times, vec![v(0), v(1)]), v(0)]),
            nr_vars: 2,
        });

        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let three = peano(&mut e, zero, s, 3);
        let four = peano(&mut e, zero, s, 4);
        let prod = e.make_free(times, vec![three, four]); // 3 * 4
        let result = e.reduce(prod);
        let twelve = peano(&mut e, zero, s, 12);
        assert!(e.deep_equal(result, twelve), "3 * 4 should reduce to s^12 0");
        assert_eq!(e.rewrites(), 21, "rewrite count matches reference Maude");
    }

    #[test]
    fn reduced_flag_invalidated_by_new_equation() {
        // Regression for review R2 H2: a node reduced before an equation is added must not stay
        // cached as canonical. Reduce `a` (no equations) → a; add `a = b`; reduce `a` → b.
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);

        let a0 = e.make_const(a);
        let r1 = e.reduce(a0);
        assert_eq!(e.node(r1).symbol(), a, "no equations yet: a is its own normal form");

        e.add_equation(Equation { lhs: Term::constant(a), rhs: Term::constant(b), nr_vars: 0 });
        let r2 = e.reduce(a0); // same id; must re-reduce despite the earlier REDUCED stamp
        assert_eq!(e.node(r2).symbol(), b, "after adding a = b, reducing a yields b");
    }

    #[test]
    fn ill_sorted_argument_blocks_rewrite_and_lands_in_error_sort() {
        // f : Nat -> Nat applied to a Bool (a different kind): the node lands in Nat's error sort,
        // and `eq f(N:Nat) = z` must NOT fire (a Bool can't match a Nat variable). (Review R2 M4
        // / "error-sort propagation is monotone and safe".)
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let boolean = e.add_sort("Bool"); // separate kind
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let f = e.add_op("f", vec![nat], nat);
        let t = e.add_op("t", vec![], boolean);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, nat)]),
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        let tb = e.make_const(t);
        let ft = e.make_free(f, vec![tb]); // f(t): Bool arg not <= Nat
        assert!(e.sorts().sort(e.sort_of(ft)).is_error, "ill-sorted f(t) is in the error sort");
        let r = e.reduce(ft);
        assert_eq!(e.node(r).symbol(), f, "f(t) does not rewrite: N:Nat cannot match a Bool");
    }

    /// Build the unary numeral `s^n 0`.
    fn numeral(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
        let mut acc = e.make_const(zero);
        for _ in 0..n {
            acc = e.make_free(s, vec![acc]);
        }
        acc
    }

    /// Decode a canonical Peano numeral `s^k 0` back to `k` (iteratively, so the *test* can't be the
    /// thing that overflows).
    fn decode(e: &Engine, mut id: DagId, zero: SymbolId, s: SymbolId) -> u32 {
        let mut k = 0;
        loop {
            let sym = e.node(id).symbol();
            if sym == zero {
                return k;
            }
            assert_eq!(sym, s, "not a Peano numeral");
            id = e.node(id).children().next().expect("successor has one child");
            k += 1;
        }
    }

    /// Depth 200_000 is ~4x the old recursive reducer's debug stack cliff (~50k); the recursive
    /// `reduce`/`reduce_args` aborted the *process* here (review R2 C1). The iterative work-stack
    /// must reduce it. `s^N + s^N` drives the deepest recursion the old code had (the addition loop
    /// rebuilds `s(plus(..))` and re-descends ~N frames).
    #[test]
    fn iterative_reduce_handles_deep_addition_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        const N: u32 = 200_000;
        let a = numeral(&mut e, zero, s, N);
        let b = numeral(&mut e, zero, s, N);
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(decode(&e, r, zero, s), 2 * N, "s^N + s^N = s^2N");
    }

    /// A deep chain with no applicable equation: the old `reduce` still descended the whole spine
    /// (`reduce_args` → `reduce(child)`) and overflowed. The result must be the *input* id — change
    /// detection preserves shared structure rather than rebuilding an identical chain.
    #[test]
    fn iterative_reduce_walks_deep_spine_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let chain = numeral(&mut e, zero, s, 200_000);
        let r = e.reduce(chain);
        assert_eq!(r, chain, "no equations: a deep chain is its own normal form (shared id kept)");
    }

    /// Conformance lock against the reference C++ Maude binary (`conformance/fib.maude`): the
    /// iterative reducer must reproduce the *exact* redex sequence — `fib(22) = 17711` in `186579`
    /// rewrites.
    #[test]
    fn fib_22_matches_reference_rewrite_count() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let fib = e.add_op("fib", vec![nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        let zero_t = || Term::constant(zero);
        e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), zero_t()]), rhs: v(0), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        e.add_equation(Equation { lhs: Term::op(fib, vec![zero_t()]), rhs: zero_t(), nr_vars: 0 });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(zero_t())]),
            rhs: s_of(zero_t()),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
            rhs: Term::op(plus, vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])]),
            nr_vars: 1,
        });

        let n = numeral(&mut e, zero, s, 22);
        let q = e.make_free(fib, vec![n]);
        let r = e.reduce(q);
        assert_eq!(decode(&e, r, zero, s), 17711, "fib(22) = 17711");
        assert_eq!(e.rewrites(), 186579, "exact rewrite count matches reference Maude");
    }

    /// Faithfulness pin (review semantic-fidelity nit): a *shared, still-reducible* redex is reduced
    /// — and counted — once per occurrence. Phase 0 has no hash-consing/forwarding, so a node that
    /// rewrites is never stamped canonical (only its normal form is); the second occurrence of a
    /// shared reducible subterm is therefore re-reduced, exactly as the old recursive reducer did.
    /// This locks A1's faithfulness; if hash-consing later makes this a single rewrite the count must
    /// be deliberately re-baselined here.
    #[test]
    fn shared_reducible_redex_is_reduced_once_per_occurrence() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        // eq N + 0 = N
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });

        // C = s 0 + 0, built once and shared into both children of f (a genuine DAG share).
        let s0 = numeral(&mut e, zero, s, 1);
        let z = e.make_const(zero);
        let c = e.make_free(plus, vec![s0, z]);
        let root = e.make_free(f, vec![c, c]); // f(C, C), C shared
        let r = e.reduce(root);

        // f(s 0, s 0): each occurrence of the shared C fired `N + 0 = N` once.
        assert_eq!(e.node(r).symbol(), f);
        assert_eq!(e.rewrites(), 2, "shared reducible redex counted once per occurrence (no hash-consing)");
    }

    /// A [`RootGuard`] pins its node across `gc`; dropping it releases the root (D2 amendment).
    #[test]
    fn root_guard_keeps_node_alive_then_releases_on_drop() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let node = e.make_const(a);
        {
            let _g = e.root(node);
            assert_eq!(e.gc(Vec::new()), 0, "a guarded node survives gc with no extra roots");
            assert_eq!(e.live_nodes(), 1);
        } // guard dropped here
        assert_eq!(e.gc(Vec::new()), 1, "after the guard drops, the node is collected");
        assert_eq!(e.live_nodes(), 0);
    }

    /// `RootGuard::set` retargets the root — e.g. to follow a term as a reduction rewrites it.
    #[test]
    fn root_guard_set_retargets() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let na = e.make_const(a);
        let nb = e.make_const(b);
        let g = e.root(na);
        g.set(nb); // now protecting nb instead of na
        assert_eq!(e.gc(Vec::new()), 1, "na is no longer rooted and is collected");
        assert_eq!(e.live_nodes(), 1);
        assert_eq!(e.node(g.get()).symbol(), b, "the guard now protects nb");
    }

    /// Done-when: safe-point GC during *one* reduction keeps memory bounded. The same `fib`
    /// reduction is run with GC off (capacity grows to the full allocation high-water) and with a
    /// short GC interval (capacity stays near the live working set); the result is unchanged. Roots
    /// in flight (the work-stack + child_result) are kept, so the answer is still correct.
    #[test]
    fn safe_point_gc_bounds_memory_within_one_reduction() {
        fn run(interval: Option<u64>) -> (u32, u64, usize) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            e.close_sorts();
            let zero = e.add_op("0", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let plus = e.add_op("+", vec![nat, nat], nat);
            let fib = e.add_op("fib", vec![nat], nat);
            let v = |i| Term::var(i, nat);
            let s_of = |t| Term::op(s, vec![t]);
            let zero_t = || Term::constant(zero);
            e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), zero_t()]), rhs: v(0), nr_vars: 1 });
            e.add_equation(Equation {
                lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
                rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
                nr_vars: 2,
            });
            e.add_equation(Equation { lhs: Term::op(fib, vec![zero_t()]), rhs: zero_t(), nr_vars: 0 });
            e.add_equation(Equation { lhs: Term::op(fib, vec![s_of(zero_t())]), rhs: s_of(zero_t()), nr_vars: 0 });
            e.add_equation(Equation {
                lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
                rhs: Term::op(plus, vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])]),
                nr_vars: 1,
            });
            e.set_gc_interval(interval);
            let n = numeral(&mut e, zero, s, 20);
            let q = e.make_free(fib, vec![n]);
            let r = e.reduce(q);
            (decode(&e, r, zero, s), e.rewrites(), e.node_capacity())
        }

        let (val_off, rw_off, cap_off) = run(None);
        let (val_on, rw_on, cap_on) = run(Some(20_000));
        assert_eq!(val_off, 6765, "fib(20) = 6765");
        assert_eq!(val_on, 6765, "safe-point GC does not change the result");
        assert_eq!(rw_on, rw_off, "safe-point GC does not change the rewrite count");
        assert!(
            cap_on < cap_off,
            "safe-point GC bounds the arena high-water: {cap_on} (on) vs {cap_off} (off)"
        );
    }

    /// Locks the `set_gc_interval` rooting contract (review finding): with safe-point GC enabled, a
    /// result held across a later reduction survives *iff* it is pinned by a [`RootGuard`]. Here the
    /// rooted result of `2 + 2` is still `s^4 0` after a second, allocation-heavy reduction triggers
    /// collection. (Without the guard the second reduction would reclaim it — a debug stale-handle
    /// panic / release silent error — which is the documented footgun, not tested here.)
    #[test]
    fn safe_point_gc_preserves_a_rooted_result_across_reductions() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        e.set_gc_interval(Some(100)); // collect several times during a reduction

        let two_a = numeral(&mut e, zero, s, 2);
        let two_b = numeral(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]);
        let four = e.reduce(sum); // s^4 0
        let g = e.root(four); // pin it across the next reduction

        // A second, disjoint reduction whose collections (every ~100 allocs) must not reclaim `four`.
        let big_a = numeral(&mut e, zero, s, 600);
        let big_b = numeral(&mut e, zero, s, 600);
        let big_sum = e.make_free(plus, vec![big_a, big_b]);
        let _ = e.reduce(big_sum);

        assert_eq!(decode(&e, g.get(), zero, s), 4, "the rooted result survives intact");
    }
}
