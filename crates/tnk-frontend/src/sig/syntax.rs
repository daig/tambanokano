//! The frontend's syntax + resolution tables, produced by [`build_module`](super::build_sig::build_module)
//! and consumed by the grammar builder (B4.3) and pretty-printer (B4.6).

use crate::lex::Frag;
use crate::surface::ast::{GatherElem, Statement};
use std::collections::HashMap;
use tnk_core::engine::Engine;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Term};

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
    /// Whether the operator carries the `assoc` axiom (ACU/AU). Recorded from the attributes (the kernel
    /// keeps the theory `pub(crate)`); the grammar builder uses it to choose the flattened assoc-list
    /// prefix form `f(<assocList>)` over the positional `f(a, …)` form, and the right-associating gather.
    pub assoc: bool,
}

impl SymbolSyntax {
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
    pub fn is_constant(&self) -> bool {
        self.domain.is_empty()
    }
}

/// Source-form trace metadata for one equation, keyed by the kernel's dense equation id
/// (`BuiltModule::eq_traces[id]`). The kernel keeps no source `Term`s, so the full trace renderer reads
/// the body from here: it Term-prints `[c]eq {lhs} = {rhs}[ if {condition}][ \[owise\]] .` and labels the
/// `Var --> binding` substitution lines from `var_names` (statement-local index → name).
#[derive(Debug, Clone)]
pub struct EqTrace {
    pub lhs: Term,
    pub rhs: Term,
    /// The condition fragments (empty for an unconditional `eq`), in source form for Term-printing the
    /// `if …` clause and the per-fragment `solving/success/failure condition fragment` lines.
    pub condition: Vec<ConditionFragment>,
    /// Statement-local variable names, indexed as the kernel's substitution is (first occurrence order).
    pub var_names: Vec<String>,
    pub owise: bool,
}

/// Source-form trace metadata for one membership axiom, keyed by the kernel's dense membership id
/// (`BuiltModule::mb_traces[id]`) — the counterpart of [`EqTrace`] for `[c]mb {lhs} : {sort}[ if …] .`.
#[derive(Debug, Clone)]
pub struct MbTrace {
    pub lhs: Term,
    pub sort: SortId,
    pub condition: Vec<ConditionFragment>,
    pub var_names: Vec<String>,
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
    /// Declared variables `(name, sort)` (from `var`/`vars`). Used by the grammar builder (variable
    /// productions) and `build_term` (resolving a variable token to its sort + statement-local index).
    pub vars: Vec<(String, SortId)>,
    /// The raw statement bubbles (parsed + added to the engine in B4.4).
    pub statements: Vec<Statement>,
    /// Per-equation trace metadata, indexed by the kernel's dense equation id (populated by
    /// `load_statements`; empty until statements are loaded). See [`EqTrace`].
    pub eq_traces: Vec<EqTrace>,
    /// Per-membership trace metadata, indexed by the kernel's dense membership id. See [`MbTrace`].
    pub mb_traces: Vec<MbTrace>,
    /// Built-in literal anchors (for the grammar's literal productions + `make_*` in build_term).
    pub nat_succ: Option<SymbolId>,
    pub nat_zero: Option<SymbolId>,
    pub string_sym: Option<SymbolId>,
    pub float_sym: Option<SymbolId>,
    pub qid_sym: Option<SymbolId>,
    /// The `MinusSymbol` operator (`-_`), if any — the pretty-printer renders `-(s^n(0))` compactly as
    /// `-n` (Maude-faithful), as Maude's `handleMinus` does.
    pub minus_sym: Option<SymbolId>,
    /// The `DivisionSymbol` operator (`_/_`), if any — the pretty-printer renders a rational special
    /// constant compactly as `num/den` (no spaces), as Maude's `handleDivision` does.
    pub division_sym: Option<SymbolId>,
}
