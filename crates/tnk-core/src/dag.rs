//! The runtime term representation: a GC'd DAG of [`DagNode`]s.
//!
//! Decision **D3**: the closed theory set is an `enum` ([`NodeTerm`]), not a C++-style virtual
//! hierarchy. Each node caches its least sort (computed at construction by the `engine`) and a
//! small flag byte (e.g. `REDUCED`), mirroring Maude's per-node bit-packed metadata.
//! Phase 0 implements only the **free-theory** arm.

use crate::id::Id;
use crate::sort::SortId;
use crate::symbol::SymbolId;

pub type DagId = Id<DagNode>;

#[derive(Debug, Clone, Copy, Default)]
pub struct NodeFlags(u8);

impl NodeFlags {
    const REDUCED: u8 = 0b0000_0001;

    pub fn is_reduced(self) -> bool {
        self.0 & Self::REDUCED != 0
    }
    pub fn set_reduced(&mut self) {
        self.0 |= Self::REDUCED;
    }
}

#[derive(Debug)]
pub struct DagNode {
    /// Least sort of this node (Phase 0: the operator's range sort, or the kind's error sort if
    /// arguments are ill-sorted). Computed once at construction.
    pub sort: SortId,
    pub flags: NodeFlags,
    pub term: NodeTerm,
}

#[derive(Debug)]
pub enum NodeTerm {
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
}
