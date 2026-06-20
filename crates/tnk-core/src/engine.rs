//! The [`Engine`] — the instantiable owner of all runtime state (decision **D1**: no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! It owns the sort signature, the symbol table, and the DAG arena; computes each node's least
//! sort at construction; and runs garbage collection (decision **D2**: non-moving mark-sweep)
//! over the DAG from an explicit root set.

use crate::arena::Arena;
use crate::dag::{DagId, DagNode, NodeFlags, NodeTerm};
use crate::sort::{SortId, Sorts};
use crate::symbol::{Symbol, SymbolId};

#[derive(Default)]
pub struct Engine {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    dags: Arena<DagNode>,
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
        self.dags.alloc(DagNode { sort, flags: NodeFlags::default(), term: NodeTerm::Free { symbol, args } })
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
        debug_assert_eq!(sym.arity(), args.len(), "arity mismatch building `{}`", sym.name);
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

    // ---- garbage collection (D2) ----

    /// Collect every DAG node not reachable from `roots`. Returns the number reclaimed.
    pub fn gc(&mut self, roots: impl IntoIterator<Item = DagId>) -> usize {
        self.dags.clear_marks();
        for root in roots {
            self.mark_reachable(root);
        }
        self.dags.sweep(|_| {})
    }

    /// Iterative (stack-based) transitive marker; terminates on shared structure because
    /// [`Arena::mark`] reports whether a node was *newly* marked.
    fn mark_reachable(&mut self, root: DagId) {
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if self.dags.mark(id) {
                stack.extend_from_slice(self.dags.get(id).children());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
