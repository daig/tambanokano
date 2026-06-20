//! The runtime term representation: a GC'd DAG of [`DagNode`]s.
//!
//! Decision **D3**: the closed theory set is an `enum`, not a C++-style virtual hierarchy.
//! Phase 0 implements only the **free-theory** arm; later phases add variables, the associative
//! theories (ACU/AU/CUI/S), and built-in numbers/strings as further arms.

use crate::id::Id;
use crate::symbol::SymbolId;

pub type DagId = Id<DagNode>;

#[derive(Debug)]
pub enum DagNode {
    /// A free-theory application `symbol(args...)`; `args.len()` equals the symbol's arity.
    Free { symbol: SymbolId, args: Vec<DagId> },
}

impl DagNode {
    /// The child nodes this node points at — used by GC tracing and term traversal.
    pub fn children(&self) -> &[DagId] {
        match self {
            DagNode::Free { args, .. } => args,
        }
    }
}
