//! The [`Engine`] — the instantiable owner of all runtime state (decision **D1**: no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! It owns the symbol table and the DAG arena and runs garbage collection (decision **D2**:
//! non-moving mark-sweep) over the DAG from an explicit root set. A RAII root guard and the
//! `RewritingContext` that supplies live roots during reduction arrive with later tasks; for now
//! roots are passed explicitly to [`Engine::gc`].

use crate::arena::Arena;
use crate::dag::{DagId, DagNode};
use crate::symbol::{Symbol, SymbolId};

#[derive(Default)]
pub struct Engine {
    symbols: Arena<Symbol>,
    dags: Arena<DagNode>,
}

impl Engine {
    pub fn new() -> Self {
        Self::default()
    }

    // ---- signature ----

    pub fn add_symbol(&mut self, name: impl Into<String>, arity: u32) -> SymbolId {
        self.symbols.alloc(Symbol { name: name.into(), arity })
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    // ---- DAG construction ----

    /// Build a free-theory node `symbol(args...)`. Panics (in debug) if `args.len()` disagrees
    /// with the symbol's declared arity.
    pub fn make_free(&mut self, symbol: SymbolId, args: Vec<DagId>) -> DagId {
        debug_assert_eq!(
            self.symbols.get(symbol).arity as usize,
            args.len(),
            "arity mismatch building `{}`",
            self.symbols.get(symbol).name
        );
        self.dags.alloc(DagNode::Free { symbol, args })
    }

    /// Convenience for a constant (an arity-0 symbol).
    pub fn make_const(&mut self, symbol: SymbolId) -> DagId {
        self.make_free(symbol, Vec::new())
    }

    pub fn node(&self, id: DagId) -> &DagNode {
        self.dags.get(id)
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

    /// Iterative (stack-based, not recursive) transitive marker; terminates on shared structure
    /// because [`Arena::mark`] reports whether a node was *newly* marked.
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

    /// Build `f(a, g(a))` with `a` shared (a true DAG, not a tree). Returns the engine and the
    /// root `f(...)`.
    fn fixture() -> (Engine, DagId) {
        let mut e = Engine::new();
        let a = e.add_symbol("a", 0);
        let g = e.add_symbol("g", 1);
        let f = e.add_symbol("f", 2);
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        let root = e.make_free(f, vec![a1, ga]);
        (e, root)
    }

    #[test]
    fn gc_keeps_reachable_shared_structure() {
        let (mut e, root) = fixture();
        assert_eq!(e.live_nodes(), 3); // a, g(a), f(a, g(a))
        assert_eq!(e.gc([root]), 0);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_collects_unreachable() {
        let (mut e, root) = fixture();
        let h = e.add_symbol("h", 0);
        let _garbage = e.make_const(h); // not referenced from root
        assert_eq!(e.live_nodes(), 4);
        assert_eq!(e.gc([root]), 1);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_with_no_roots_collects_all() {
        let (mut e, _root) = fixture();
        assert_eq!(e.gc(Vec::new()), 3);
        assert_eq!(e.live_nodes(), 0);
    }

    #[test]
    #[should_panic]
    fn arity_mismatch_panics() {
        let mut e = Engine::new();
        let f = e.add_symbol("f", 2);
        let _ = e.make_free(f, Vec::new());
    }
}
