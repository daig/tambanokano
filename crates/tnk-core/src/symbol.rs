//! Operator symbols.
//!
//! Phase 0 carries a name and a single sort declaration (`domain -> range`). Equational
//! attributes, ad-hoc overloading (multiple declarations + sort diagram), and per-symbol
//! equation/rule tables are layered on later **by composition** (decision **D3**: no
//! `Symbol`-is-a-`SortTable` multiple inheritance as in the C++).

use crate::id::Id;
use crate::sort::SortId;

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub domain: Vec<SortId>,
    pub range: SortId,
}

impl Symbol {
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
}
