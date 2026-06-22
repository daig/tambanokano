//! The frontend's syntax + resolution tables, produced by [`build_module`](super::build_sig::build_module)
//! and consumed by the grammar builder (B4.3) and pretty-printer (B4.6).

use crate::lex::Frag;
use crate::surface::ast::{GatherElem, Statement};
use std::collections::HashMap;
use tnk_core::engine::Engine;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;

/// One operator's surface syntax — the per-symbol record the kernel does not store. Holds the mixfix
/// fragments, the resolved domain/range, and the user-given prec/gather (the OBJ3 defaults are filled in
/// by the grammar builder, B4.3).
#[derive(Debug, Clone)]
pub struct SymbolSyntax {
    pub frags: Vec<Frag>,
    pub domain: Vec<SortId>,
    pub range: SortId,
    pub prec: Option<u32>,
    pub gather: Option<Vec<GatherElem>>,
}

impl SymbolSyntax {
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
    pub fn is_constant(&self) -> bool {
        self.domain.is_empty()
    }
}

/// A built module: the `Engine` (sorts + ops + attributes, but **not** statements — those need the grammar,
/// B4.4) plus the frontend's resolution tables and the still-raw statements/commands.
pub struct BuiltModule {
    pub engine: Engine,
    pub name: String,
    /// Sort name → id.
    pub sorts: HashMap<String, SortId>,
    /// `(canonical mixfix name, arity)` → symbol id (overloads/`ditto` share one id).
    pub ops: HashMap<(String, usize), SymbolId>,
    /// Per-symbol surface syntax.
    pub syntax: HashMap<SymbolId, SymbolSyntax>,
    /// The raw statement bubbles (parsed + added to the engine in B4.4).
    pub statements: Vec<Statement>,
    /// Built-in literal anchors (for the grammar's literal productions + `make_*` in build_term).
    pub nat_succ: Option<SymbolId>,
    pub nat_zero: Option<SymbolId>,
    pub string_sym: Option<SymbolId>,
    pub float_sym: Option<SymbolId>,
    pub qid_sym: Option<SymbolId>,
}
