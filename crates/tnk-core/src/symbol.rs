//! Operator symbols.
//!
//! Phase 0 carries only a name and arity. Sort declarations, equational attributes, and the
//! per-symbol equation/rule/sort tables are layered on in later tasks **by composition**
//! (decision **D3**: no `Symbol`-is-a-`SortTable` multiple inheritance as in the C++).

use crate::id::Id;

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub arity: u32,
}
