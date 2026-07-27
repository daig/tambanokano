//! The frontend's syntax + resolution tables, produced by [`build_module`](super::build_sig::build_module)
//! and consumed by the grammar builder (B4.3) and pretty-printer (B4.6).

use crate::lex::{Frag, Token};
use crate::surface::ast::{GatherElem, IdSide, Statement};
use std::collections::{HashMap, HashSet};
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
    /// A constructor of `Attribute` with the reserved canonical `name:_` shape. Retained
    /// independently of the kernel's merged constructor flag for META Qid encoding.
    pub object_attribute: bool,
    /// Whether the source spelling separated the attribute label from `:_` (`bal :_` rather than
    /// `state:_`). Maude preserves that distinction when pretty-printing object attributes.
    pub spaced_label_colon: bool,
    /// Whether the operator carries the `assoc` axiom (ACU/AU). Recorded from the attributes (the kernel
    /// keeps the theory `pub(crate)`); the grammar builder uses it to choose the flattened assoc-list
    /// prefix form `f(<assocList>)` over the positional `f(a, …)` form, and the right-associating gather.
    pub assoc: bool,
    /// Whether the operator carries the `iter` axiom (the S theory — a stacked successor `s_`). The
    /// grammar builder uses it to emit the `f^count(t)` iter-token input form (Maude's `iterSymbols`).
    pub iter: bool,
    /// The `format (…)` directive words (one per mixfix gap), if declared — the pretty-printer's per-gap
    /// spacing/indent layout (`_<-_` substitutions, `rl_=>_[_].`, the `__` declaration/trace lists). `None`
    /// = Maude's default spacing.
    pub format: Option<Vec<String>>,
}

impl SymbolSyntax {
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
    pub fn is_constant(&self) -> bool {
        self.domain.is_empty()
    }
}

/// One source operator declaration after sort resolution. Distinct connected-component overloads have
/// distinct [`symbol`](Self::symbol)s; subsort overloads in the same component share one symbol but retain
/// each declaration profile here. Grammar-aware view maps use this table to resolve a disambiguated source
/// signature to the same symbol identity as the term parser.
#[derive(Debug, Clone)]
pub struct OpProfile {
    pub symbol: SymbolId,
    pub domain: Vec<SortId>,
    pub range: SortId,
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
    /// Whether the equation carries Maude's `[variant]` attribute.
    pub variant: bool,
    /// The `[label …]` name, if any — retained for META `upEqs`/`upModule` (renders `[label('l)]`), not
    /// used by execution.
    pub label: Option<String>,
    /// A `[nonexec]` axiom (a proof obligation). Engine-registered traces are always `false` (build skips
    /// nonexec); META up-translation sets it for a module's own `[nonexec]` equations, which it parses on
    /// demand (they carry no engine trace) — [`parse_statement_trace`](crate::load::parse_statement_trace).
    pub nonexec: bool,
}

/// Source-form trace metadata for one membership axiom, keyed by the kernel's dense membership id
/// (`BuiltModule::mb_traces[id]`) — the counterpart of [`EqTrace`] for `[c]mb {lhs} : {sort}[ if …] .`.
#[derive(Debug, Clone)]
pub struct MbTrace {
    pub lhs: Term,
    pub sort: SortId,
    pub condition: Vec<ConditionFragment>,
    pub var_names: Vec<String>,
    /// The `[label …]` name, if any — retained for META `upMbs`/`upModule`. See [`EqTrace::label`].
    pub label: Option<String>,
    /// A `[nonexec]` membership axiom — see [`EqTrace::nonexec`].
    pub nonexec: bool,
}

/// Source-form trace metadata for one rule, keyed by the kernel's dense rule id
/// (`BuiltModule::rl_traces[id]`) — the counterpart of [`EqTrace`] for `[c]rl [{label}] : {lhs} => {rhs}
/// [ if …] .` Used by the full trace renderer (`*********** rule`) and `show path` (`===[ rl … ]===>`).
#[derive(Debug, Clone)]
pub struct RlTrace {
    pub lhs: Term,
    pub rhs: Term,
    pub condition: Vec<ConditionFragment>,
    pub var_names: Vec<String>,
    /// The `[label]` of a labelled rule (`rl [foo] : …`), if any — rendered in the body and on the
    /// `show path` arc.
    pub label: Option<std::rc::Rc<str>>,
    /// A `[nonexec]` rule — see [`EqTrace::nonexec`].
    pub nonexec: bool,
    /// A `[narrowing]` rule. It remains available to symbolic narrowing even when `nonexec` is set.
    pub narrowing: bool,
}

#[derive(Debug, Clone)]
pub struct IdentitySpec {
    pub symbol: SymbolId,
    pub sort: SortId,
    pub side: IdSide,
    pub tokens: Vec<Token>,
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
    /// Every resolved source operator declaration, including overloads folded into one symbol.
    pub op_profiles: Vec<OpProfile>,
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
    /// Per-rule trace metadata, indexed by the kernel's dense rule id (populated by `load_statements`).
    /// See [`RlTrace`].
    pub rl_traces: Vec<RlTrace>,
    /// Verbose `omod` object-completion notices for statements defined by this module. Each entry is
    /// preformatted but unwrapped; the REPL emits it once when the defining module is entered.
    pub oo_completion_diagnostics: Vec<String>,
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
    /// The boolean truth anchors (`true`/`false`, tagged `SystemTrue`/`SystemFalse` — Maude's
    /// `trueSymbol`/`falseSymbol`). Used to desugar a bare boolean condition `if p` into `p = true`
    /// and by sort-test predicates; `None` until a module declares them (the prelude's `TRUTH-VALUE`).
    pub true_sym: Option<SymbolId>,
    pub false_sym: Option<SymbolId>,
    /// Per-symbol ad-hoc overloading flags for print disambiguation (Maude's `SymbolInfo::iflags`
    /// `*_OVERLOADED` bits, `entry.cc`). A symbol overloaded across connected components prints
    /// `(t).Sort` so the output round-trips. [`OVL_ADHOC`] = another symbol shares its name;
    /// [`OVL_DOMAIN`] = another shares its name *and* domain kinds (forces disambiguation when the range
    /// is unknown); [`OVL_RANGE`] = another shares its name *and* range kind. Absent = unique (no
    /// disambiguation).
    pub overload: HashMap<SymbolId, u8>,
    /// Distinct kinds whose built-in values use positive decimal syntax (`SuccSymbol` naturals plus SMT
    /// integers). Maude qualifies a numeral in an unknown-range context only when this exceeds one.
    pub(crate) integer_literal_kind_count: usize,
    /// Canonical positive decimal spellings also declared as nullary user operators. These collide with
    /// built-in natural pseudo-literals even when there is only one numeral kind.
    pub(crate) overloaded_naturals: HashSet<String>,
    /// Strategy declarations after module flattening. The interpreter coalesces these by
    /// `(name, domain kinds, subject kind)` while retaining donation origins for conflict handling.
    pub strat_decls: Vec<crate::surface::ast::StratDecl>,
    /// Strategy definitions (`sd`/`csd`) of a strategy module (Pillar 2.4) — the call→body table the
    /// strategy interpreter resolves a `Call` against. Empty for a non-strategy module.
    pub strat_defs: Vec<crate::surface::ast::StratDef>,
    /// Identity attribute bubbles retained until the module grammar exists, then parsed and installed
    /// as signature-owned ground terms before statements are compiled.
    pub identity_specs: Vec<IdentitySpec>,
}

/// Another symbol shares this one's name ([`BuiltModule::overload`]).
pub const OVL_ADHOC: u8 = 1;
/// Another symbol shares this one's name and domain kinds — printing must disambiguate `(t).Sort` when
/// the range is not determined by context.
pub const OVL_DOMAIN: u8 = 2;
/// Another symbol shares this one's name and range kind.
pub const OVL_RANGE: u8 = 4;
