//! Operator symbols.
//!
//! Phase 0 carries a name and a single sort declaration (`domain -> range`). Equational
//! attributes, ad-hoc overloading (multiple declarations + sort diagram), and per-symbol
//! equation/rule/sort tables are layered on later **by composition** (decision **D3**: no
//! `Symbol`-is-a-`SortTable` multiple inheritance as in the C++). Fields are `pub(crate)`; read
//! access is through getters (review R3 H4).

use crate::id::Id;
use crate::sort::SortId;

pub type SymbolId = Id<Symbol>;

#[derive(Debug, Clone)]
pub struct Symbol {
    pub(crate) name: String,
    pub(crate) domain: Vec<SortId>,
    pub(crate) range: SortId,
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
}
