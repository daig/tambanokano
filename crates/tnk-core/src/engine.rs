//! The [`Engine`] — the instantiable owner of all runtime state (decision **D1**: no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! It owns the sort signature, the symbol table, and the DAG arena; computes each node's least
//! sort at construction; and runs garbage collection (decision **D2**: non-moving mark-sweep)
//! over the DAG from an explicit root set.

use crate::arena::Arena;
use crate::dag::{DagId, DagNode, NodeTerm};
use crate::sort::{SortId, Sorts};
use crate::symbol::{Symbol, SymbolId};
use crate::term::{Equation, Subst, Term};
use std::collections::HashMap;

/// One pending node-normalization on the iterative [`Engine::reduce`] work-stack.
///
/// A frame mirrors one activation of the old recursive `reduce`/`reduce_args` pair: it reduces the
/// node's children left-to-right (`reduced` accumulates results, `next` is the cursor over `orig`),
/// then drives the top-rewrite fixpoint by *reusing its own slot* for each rewritten term.
///
/// **A2 safe-point-GC contract** (the reason this is an explicit heap stack). The frames hold most
/// in-flight `DagId`s of an in-progress reduction — but *not all*: at the [`Engine::reduce`] loop
/// head a just-completed child sits only in the `child_result` local until it is delivered into its
/// parent's `reduced` on the next iteration. So the complete root set at the loop head is
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
    /// self` reductions that may grow (and thus reallocate) the arena.
    orig: Vec<DagId>,
    /// Reduced children collected so far; length grows to `orig.len()` as `next` advances.
    reduced: Vec<DagId>,
    /// Index of the next child of `orig` to reduce.
    next: usize,
}

pub struct Engine {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    dags: Arena<DagNode>,
    /// Unconditional equations indexed by their left-hand side's top symbol.
    equations: HashMap<SymbolId, Vec<Equation>>,
    /// Count of equational rewrites applied (Maude's `rewrites` statistic).
    rewrite_count: u64,
    /// Bumped whenever the equation set changes; stamped into nodes when they are proved canonical,
    /// so `add_equation` invalidates stale "reduced" results (review R2 H2).
    eq_epoch: u32,
}

impl Default for Engine {
    fn default() -> Self {
        Engine {
            sorts: Sorts::default(),
            symbols: Arena::default(),
            dags: Arena::default(),
            equations: HashMap::default(),
            rewrite_count: 0,
            eq_epoch: 1, // 0 is the "never reduced" sentinel stored on nodes
        }
    }
}

impl Engine {
    pub fn new() -> Self {
        Self::default()
    }

    // ---- sort signature ----

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.add_sort(name)
    }
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sorts.add_subsort(sub, sup);
    }
    /// Finish the sort poset (compute kinds + subsort closure). Call before building DAG nodes.
    pub fn close_sorts(&mut self) {
        self.sorts.close();
    }
    pub fn sorts(&self) -> &Sorts {
        &self.sorts
    }

    // ---- symbols ----

    pub fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.symbols.alloc(Symbol { name: name.into(), domain, range })
    }
    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    // ---- DAG construction ----

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub fn make_free(&mut self, symbol: SymbolId, args: Vec<DagId>) -> DagId {
        let sort = self.compute_free_sort(symbol, &args);
        self.dags.alloc(DagNode { sort, reduced_epoch: 0, term: NodeTerm::Free { symbol, args } })
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub fn make_const(&mut self, symbol: SymbolId) -> DagId {
        self.make_free(symbol, Vec::new())
    }

    /// Phase-0 sort computation for a free node: if every argument's sort is `<=` the declared
    /// domain sort the node gets the operator's `range`; otherwise it lands in the error/top sort
    /// of `range`'s kind. (Overloaded least-sort via a sort diagram arrives in Phase 1.)
    fn compute_free_sort(&self, symbol: SymbolId, args: &[DagId]) -> SortId {
        let sym = self.symbols.get(symbol);
        assert_eq!(sym.arity(), args.len(), "arity mismatch building `{}`", sym.name);
        let well_sorted = sym
            .domain
            .iter()
            .zip(args)
            .all(|(&dom, &arg)| self.sorts.leq(self.dags.get(arg).sort, dom));
        if well_sorted {
            sym.range
        } else {
            self.sorts.error_sort(self.sorts.kind_of(sym.range))
        }
    }

    pub fn node(&self, id: DagId) -> &DagNode {
        self.dags.get(id)
    }
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.dags.get(id).sort
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub fn live_nodes(&self) -> usize {
        self.dags.len()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub fn node_capacity(&self) -> usize {
        self.dags.capacity()
    }

    // ---- garbage collection (D2) ----

    /// Collect every DAG node not reachable from `roots`. Returns the number reclaimed.
    pub fn gc(&mut self, roots: impl IntoIterator<Item = DagId>) -> usize {
        self.dags.clear_marks();
        for root in roots {
            self.mark_reachable(root);
        }
        self.dags.sweep(|_| {})
    }

    /// Iterative (stack-based) transitive marker. Marks each node **on push** (using the
    /// "newly-marked" result of [`Arena::mark`]) so a node shared by *k* parents is pushed once,
    /// keeping the work stack O(nodes) rather than O(edges); it also terminates on shared/cyclic
    /// structure.
    fn mark_reachable(&mut self, root: DagId) {
        let mut stack = Vec::new();
        if self.dags.mark(root) {
            stack.push(root);
        }
        while let Some(id) = stack.pop() {
            let len = self.dags.get(id).children().len();
            for i in 0..len {
                let child = self.dags.get(id).children()[i];
                if self.dags.mark(child) {
                    stack.push(child);
                }
            }
        }
    }

    // ---- equations + reduction ----

    /// Register an unconditional equation, indexed by its left-hand side's top symbol.
    pub fn add_equation(&mut self, eq: Equation) {
        let top = eq.lhs.top_symbol().expect("equation lhs must be an application");
        self.equations.entry(top).or_default().push(eq);
        // A term canonical under the old equation set may now be reducible: invalidate every
        // node's cached "reduced" stamp by advancing the epoch (review R2 H2).
        self.eq_epoch += 1;
    }

    /// Total equational rewrites applied so far.
    pub fn rewrites(&self) -> u64 {
        self.rewrite_count
    }
    pub fn reset_rewrites(&mut self) {
        self.rewrite_count = 0;
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
        if self.node(root).reduced_epoch == self.eq_epoch {
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

            // Deliver a completed child to the current (top) frame and advance its cursor.
            if let Some(r) = child_result.take() {
                let f = stack.last_mut().expect("child result with empty reduce stack");
                f.reduced.push(r);
                f.next += 1;
            }

            // Phase 1: reduce the next child (innermost, left-to-right). Already-reduced children
            // (shared subterms, cached by epoch) are delivered without pushing a frame.
            {
                let f = stack.last().expect("empty reduce stack");
                if f.next < f.orig.len() {
                    let child = f.orig[f.next];
                    if self.node(child).reduced_epoch == self.eq_epoch {
                        child_result = Some(child);
                    } else {
                        let frame = self.new_reduce_frame(child);
                        stack.push(frame);
                    }
                    continue;
                }
            }

            // Phase 1 complete: rebuild this term iff some child changed, else keep the shared id.
            let (symbol, original, reduced, changed) = {
                let f = stack.last_mut().expect("empty reduce stack");
                let changed = f.reduced != f.orig;
                // `mem::take` moves the reduced children out (no clone) — the frame is about to be
                // reused or popped, so its `reduced` is no longer needed.
                let reduced = if changed { std::mem::take(&mut f.reduced) } else { Vec::new() };
                (f.symbol, f.original, reduced, changed)
            };
            let rebuilt = if changed { self.make_free(symbol, reduced) } else { original };

            // Phase 2: rewrite the top while an equation applies, re-reducing each result by reusing
            // this frame's slot for the rewritten term.
            if let Some(next) = self.try_rewrite_top(rebuilt) {
                self.rewrite_count += 1;
                let frame = self.new_reduce_frame(next);
                *stack.last_mut().expect("empty reduce stack") = frame;
                continue;
            }

            // `rebuilt` is a normal form: stamp it canonical and hand it up (or return it as root).
            self.dags.get_mut(rebuilt).reduced_epoch = self.eq_epoch;
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
        let orig = node.children().to_vec();
        ReduceFrame {
            original: id,
            symbol: node.symbol(),
            reduced: Vec::with_capacity(orig.len()),
            orig,
            next: 0,
        }
    }

    /// Apply the first matching equation at the top of `id`, returning the instantiated rhs (or
    /// `None` if no equation applies).
    fn try_rewrite_top(&mut self, id: DagId) -> Option<DagId> {
        let symbol = self.node(id).symbol();
        let mut subst = Subst::new();
        let rhs: Term = {
            let eqs = self.equations.get(&symbol)?;
            let mut chosen = None;
            for eq in eqs {
                subst.reset(eq.nr_vars);
                if self.match_pattern(&eq.lhs, id, &mut subst) {
                    chosen = Some(eq.rhs.clone());
                    break;
                }
            }
            chosen?
        };
        Some(self.instantiate(&rhs, &subst))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{Equation, Term};

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

    #[test]
    #[should_panic]
    fn arity_mismatch_panics() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let f = e.add_op("f", vec![nat, nat], nat);
        let _ = e.make_free(f, Vec::new());
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
            id = e.node(id).children()[0];
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
}
