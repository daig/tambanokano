//! The runtime term representation: a GC'd DAG of [`DagNode`]s.
//!
//! Decision **D3**: the closed theory set is an `enum` ([`NodeTerm`]), not a C++-style virtual
//! hierarchy. Each node caches its least sort (computed at construction by the `engine`) and the
//! equation-set epoch at which it was last proved canonical. Phase 0 implements only the
//! **free-theory** arm.
//!
//! Invariant-bearing fields are `pub(crate)`: only the engine may set a node's sort or its reduced
//! epoch (review R3 H4 — public fields previously let callers mark an unreduced node "reduced" or
//! desync the cached sort).

use crate::id::Id;
use crate::sort::SortId;
use crate::symbol::SymbolId;

pub type DagId = Id<DagNode>;

#[derive(Debug)]
pub struct DagNode {
    /// Least sort of this node (Phase 0: the operator's range sort, or the kind's error sort if
    /// arguments are ill-sorted). Computed once at construction.
    pub(crate) sort: SortId,
    /// The `Engine` equation-set epoch at which this node was last proved canonical, or `0` if it
    /// has never been reduced. The engine treats the node as reduced only while this equals the
    /// current epoch, so adding equations invalidates stale results (review R2 H2).
    pub(crate) reduced_epoch: u32,
    pub(crate) term: NodeTerm,
}

#[derive(Debug)]
pub(crate) enum NodeTerm {
    /// A free-theory application `symbol(args...)`; `args.len()` equals the symbol's arity.
    Free { symbol: SymbolId, args: Vec<DagId> },
}

impl DagNode {
    /// Visit each child once via a closure — the form a consumer uses when it wants to act on each
    /// child *without materializing a collection* (the C++ `markArguments` visitor). Rather than
    /// handing out a `&[DagId]`, it lets non-slice representations participate: ACU's
    /// `(child, multiplicity)` pairs, the S-theory's `(count, arg)`, a red-black `ACU_TreeDagNode`
    /// have no contiguous child array to borrow (review R3 H3). (The GC marker currently uses
    /// [`children`](Self::children)`().extend(..)` instead, whose slice fast-path is faster for the
    /// free rep; both are equivalent traversals through this seam.)
    pub fn for_each_child(&self, mut f: impl FnMut(DagId)) {
        match &self.term {
            NodeTerm::Free { args, .. } => args.iter().for_each(|&c| f(c)),
        }
    }

    /// Iterate this node's children. Returns an iterator (not a slice) for the same reason as
    /// [`for_each_child`](Self::for_each_child): equality and reduction enumerate children
    /// theory-agnostically, so a future non-slice arm is a pure addition to this method rather than an
    /// edit to GC / equality / reduction. (Adding an arm that yields a different iterator type will
    /// unify them here behind a small enum-iterator; the callers are untouched.)
    pub fn children(&self) -> impl Iterator<Item = DagId> + '_ {
        match &self.term {
            NodeTerm::Free { args, .. } => args.iter().copied(),
        }
    }

    pub fn symbol(&self) -> SymbolId {
        match &self.term {
            NodeTerm::Free { symbol, .. } => *symbol,
        }
    }

    /// The node's cached least sort.
    pub fn sort(&self) -> SortId {
        self.sort
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::Engine;

    /// The two traversal forms of the A5 seam agree, and a constant has no children.
    #[test]
    fn children_iterator_and_visitor_agree() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let x = e.make_const(a);
        let y = e.make_const(a);
        let parent = e.make_free(f, vec![x, y]); // f(x, y), distinct child ids

        let node = e.node(parent);
        let via_iter: Vec<_> = node.children().collect();
        let mut via_visitor = Vec::new();
        node.for_each_child(|c| via_visitor.push(c));
        assert_eq!(via_iter, vec![x, y], "children() yields the args in order");
        assert_eq!(via_iter, via_visitor, "children() and for_each_child enumerate the same set");

        assert_eq!(e.node(x).children().count(), 0, "a constant has no children");
    }
}
