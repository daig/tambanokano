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
use crate::term::{Equation, Subst, Term};
use std::collections::HashMap;

#[derive(Default)]
pub struct Engine {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    dags: Arena<DagNode>,
    /// Unconditional equations indexed by their left-hand side's top symbol.
    equations: HashMap<SymbolId, Vec<Equation>>,
    /// Count of equational rewrites applied (Maude's `rewrites` statistic).
    rewrite_count: u64,
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

    // ---- equations + reduction ----

    /// Register an unconditional equation, indexed by its left-hand side's top symbol.
    pub fn add_equation(&mut self, eq: Equation) {
        let top = eq.lhs.top_symbol().expect("equation lhs must be an application");
        self.equations.entry(top).or_default().push(eq);
    }

    /// Total equational rewrites applied so far.
    pub fn rewrites(&self) -> u64 {
        self.rewrite_count
    }
    pub fn reset_rewrites(&mut self) {
        self.rewrite_count = 0;
    }

    /// Reduce `id` to canonical form by innermost, eager equational simplification (Phase 0:
    /// unconditional free-theory equations). Already-reduced nodes are returned unchanged, so
    /// shared subterms are normalized at most once.
    pub fn reduce(&mut self, id: DagId) -> DagId {
        if self.node(id).flags.is_reduced() {
            return id;
        }
        let mut current = self.reduce_args(id);
        while let Some(next) = self.try_rewrite_top(current) {
            self.rewrite_count += 1;
            current = self.reduce_args(next);
        }
        self.dags.get_mut(current).flags.set_reduced();
        current
    }

    /// Reduce each argument; rebuild the node only if some argument changed.
    fn reduce_args(&mut self, id: DagId) -> DagId {
        let (symbol, children) = {
            let node = self.node(id);
            (node.symbol(), node.children().to_vec())
        };
        if children.is_empty() {
            return id;
        }
        let mut changed = false;
        let mut reduced = Vec::with_capacity(children.len());
        for c in children {
            let rc = self.reduce(c);
            changed |= rc != c;
            reduced.push(rc);
        }
        if changed {
            self.make_free(symbol, reduced)
        } else {
            id
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
}
