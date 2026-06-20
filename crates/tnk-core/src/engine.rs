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
use crate::dag::{DagId, DagNode, NodeTerm};
use crate::root::{RootGuard, Roots};
use crate::sort::{SortId, Sorts};
use crate::symbol::{Symbol, SymbolId};
use crate::term::{Equation, Subst, Term};
use crate::theory::LhsAutomaton;
use std::collections::HashMap;

/// An equation as stored in the engine: its left-hand side compiled to a theory [`LhsAutomaton`]
/// (decision D3 / review R3 C1), with the right-hand side and variable count kept for instantiation.
/// The public [`Equation`] (lhs as a [`Term`]) is compiled into this by [`Engine::add_equation`].
struct CompiledEquation {
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
}

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

/// The immutable-during-reduction half of the engine: the sort poset, the symbol table, and the
/// compiled equation set. Matching, instantiation, and reduction take this by shared reference, so
/// the [`Runtime`] can mutate the DAG arena while the equation table stays borrowed.
pub(crate) struct Signature {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    /// Unconditional equations (LHS compiled to a theory automaton), indexed by lhs top symbol.
    equations: HashMap<SymbolId, Vec<CompiledEquation>>,
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
        self.symbols.alloc(Symbol { name: name.into(), domain, range })
    }
    pub(crate) fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    /// Register an unconditional equation, compiling its lhs to a theory `LhsAutomaton` once, and
    /// advance the equation epoch (see [`Engine::add_equation`]).
    pub(crate) fn add_equation(&mut self, eq: Equation) {
        let top = eq.lhs.top_symbol().expect("equation lhs must be an application");
        let compiled = CompiledEquation {
            lhs: LhsAutomaton::compile(eq.lhs),
            rhs: eq.rhs,
            nr_vars: eq.nr_vars,
        };
        self.equations.entry(top).or_default().push(compiled);
        // A term canonical under the old equation set may now be reducible: invalidate every
        // node's cached "reduced" stamp by advancing the epoch (review R2 H2).
        self.eq_epoch += 1;
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

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub(crate) fn make_free(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        args: Vec<DagId>,
    ) -> DagId {
        let sort = self.compute_free_sort(sig, symbol, &args);
        // Drives safe-point GC; only meaningful when enabled, so the default path skips it entirely.
        // Reset by `safe_point_gc`, so it can't overflow between collections.
        if self.gc_interval.is_some() {
            self.allocs_since_gc += 1;
        }
        self.dags.alloc(DagNode { sort, reduced_epoch: 0, term: NodeTerm::Free { symbol, args } })
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub(crate) fn make_const(&mut self, sig: &Signature, symbol: SymbolId) -> DagId {
        self.make_free(sig, symbol, Vec::new())
    }

    /// Phase-0 sort computation for a free node: if every argument's sort is `<=` the declared
    /// domain sort the node gets the operator's `range`; otherwise it lands in the error/top sort
    /// of `range`'s kind. (Overloaded least-sort via a sort diagram arrives in Phase 1.)
    fn compute_free_sort(&self, sig: &Signature, symbol: SymbolId, args: &[DagId]) -> SortId {
        let sym = sig.symbols.get(symbol);
        assert_eq!(sym.arity(), args.len(), "arity mismatch building `{}`", sym.name);
        let well_sorted = sym
            .domain
            .iter()
            .zip(args)
            .all(|(&dom, &arg)| sig.sorts.leq(self.dags.get(arg).sort, dom));
        if well_sorted {
            sym.range
        } else {
            sig.sorts.error_sort(sig.sorts.kind_of(sym.range))
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
    /// frame's term (`original`, which transitively covers its `orig` children) and its already-
    /// `reduced` children, plus the `child_result` not yet delivered into a frame. This is the
    /// complete loop-head root set (see the [`ReduceFrame`] safe-point contract); collecting anywhere
    /// else would miss fresh nodes living only in native-stack locals.
    fn safe_point_gc(&mut self, frames: &[ReduceFrame], child_result: Option<DagId>) {
        self.dags.clear_marks();
        self.mark_registered_roots();
        for frame in frames {
            self.mark_reachable(frame.original);
            for &r in &frame.reduced {
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
                    if self.node(child).reduced_epoch == sig.eq_epoch() {
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
            let rebuilt = if changed { self.make_free(sig, symbol, reduced) } else { original };

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
            reduced: Vec::with_capacity(orig.len()),
            orig,
            next: 0,
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
        let mut subst = Subst::new();
        // Shared borrow of `sig` held across the loop; `self` (the runtime) is disjoint, so the
        // matched `&eq.rhs` is instantiated in place without a defensive clone.
        let eqs = sig.equations.get(&symbol)?;
        for eq in eqs {
            subst.reset(eq.nr_vars);
            let Some(mut sp) = eq.lhs.match_(self, sig, id, &mut subst) else { continue };
            // The solution stream. Phase 1 equations are unconditional, so it accepts the first
            // solution and returns; conditional equations / AC will iterate it (check the
            // condition, `continue` to the next solution on failure), which is why it is a loop.
            #[allow(clippy::never_loop)]
            while sp.next(self, &mut subst) {
                return Some(self.instantiate(sig, &eq.rhs, &subst));
            }
        }
        None
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
