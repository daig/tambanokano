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
    /// The child nodes this node points at — used by GC tracing and term traversal.
    pub fn children(&self) -> &[DagId] {
        match &self.term {
            NodeTerm::Free { args, .. } => args,
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
