//! Surface AST: the `PreModule` (signature + raw statement bubbles) the surface parser produces before
//! the per-module mixfix term parse runs (B4.4). Term-carrying parts (op identity, equation lhs/rhs,
//! conditions, command terms) are kept as un-parsed token **bubbles**.

use crate::lex::Token;

/// A parsed functional-module skeleton. `Clone` so the module system (B5) can combine the declarations
/// of an import closure into one flattened `PreModule`.
#[derive(Debug, Clone)]
pub struct PreModule {
    pub name: String,
    /// Imported modules (`protecting`/`extending`/`including <module-expr> .`), in declaration order.
    pub imports: Vec<Import>,
    pub sorts: Vec<String>,
    /// Each subsort chain `A B < C < D` as ordered groups (every group is below the next).
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
}

/// An import declaration: a mode and the module expression it imports. The mode does **not** affect
/// flattening (which declarations are imported) — it is a semantic-check annotation (no-junk /
/// no-confusion), stored for later. So B5 flattens all three modes identically.
#[derive(Debug, Clone)]
pub struct Import {
    pub mode: ImportMode,
    pub expr: ModuleExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportMode {
    Protecting,
    Extending,
    Including,
}

/// A (non-parameterized) module expression: a named module, a summation `A + B` (the union), or a
/// renaming `M * (sort A to B, op f to g)`. Parameterized instantiation (`LIST{Nat}`) is Phase 2.
#[derive(Debug, Clone)]
pub enum ModuleExpr {
    Named(String),
    Sum(Box<ModuleExpr>, Box<ModuleExpr>),
    Rename(Box<ModuleExpr>, Vec<RenameItem>),
}

/// One mapping inside a renaming `* (…)`. Op renaming is by canonical name (disambiguated
/// `op f : A -> B to g` and mixfix renaming are B5 follow-ups, rejected loudly).
#[derive(Debug, Clone)]
pub enum RenameItem {
    Sort { from: String, to: String },
    Op { from: String, to: String },
}

/// One operator declaration `op <name> : <domain> -> <range> [<attrs>] .` (or `ops …` expanded to one
/// `OpDecl` per name).
#[derive(Debug, Clone)]
pub struct OpDecl {
    /// The mixfix name as raw tokens (`[_+_]`, `[s_]`, `[<_, ,, _>]`, `[gcd]`).
    pub name: Vec<Token>,
    pub domain: Vec<String>,
    pub range: String,
    pub attrs: Attrs,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub names: Vec<String>,
    pub sort: String,
}

/// Operator attributes (`[assoc comm id: … ctor iter prec gather strat special ditto]`).
#[derive(Debug, Default, Clone)]
pub struct Attrs {
    pub assoc: bool,
    pub comm: bool,
    pub idem: bool,
    pub iter: bool,
    pub ctor: bool,
    /// `id: <term>` identity element (a token bubble).
    pub id: Option<Vec<Token>>,
    pub prec: Option<u32>,
    pub gather: Option<Vec<GatherElem>>,
    /// `strat (…)` — the raw 1-based positions (ending in `0`).
    pub strat: Option<Vec<u32>>,
    pub special: Option<SpecialSpec>,
    pub ditto: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GatherElem {
    /// `E` — argument precedence bound = the operator's prec.
    Strong,
    /// `e` — bound = prec − 1.
    Weak,
    /// `&` — no bound (`ANY`).
    Any,
}

/// A `special (id-hook … op-hook … term-hook …)` directive: hook names + their argument bubbles, resolved
/// to a `tnk-core::SpecialOp` by `build_sig` (B4.2).
#[derive(Debug, Default, Clone)]
pub struct SpecialSpec {
    /// `(class_name, data_tokens)` — e.g. `("ACU_NumberOpSymbol", ["+"])`, `("BranchSymbol", [])`.
    pub id_hook: Option<(String, Vec<String>)>,
    /// `op-hook <purpose> (<op-signature>)` — e.g. `("succSymbol", ["s_", ":", "Nat", "~>", "NzNat"])`.
    pub op_hooks: Vec<(String, Vec<Token>)>,
    /// `term-hook <purpose> (<term>)` — e.g. `("zeroTerm", ["0"])`, `("1", ["true"])`.
    pub term_hooks: Vec<(String, Vec<Token>)>,
}

/// A statement — `eq`/`ceq`/`owise`, `mb`/`cmb`. Term parts are raw bubbles (parsed in B4.4).
#[derive(Debug, Clone)]
pub enum Statement {
    Eq { lhs: Vec<Token>, rhs: Vec<Token>, cond: Option<Vec<Token>>, owise: bool },
    Mb { lhs: Vec<Token>, sort: Vec<Token>, cond: Option<Vec<Token>> },
}

/// A top-level command (functional fragment): `reduce`/`red` and `match`/`xmatch`.
#[derive(Debug)]
pub enum Command {
    Reduce { term: Vec<Token> },
    Match { pattern: Vec<Token>, subject: Vec<Token>, xmatch: bool },
}

/// The result of surface-parsing a source file: the modules and the top-level commands, each tagged with
/// the index (into `modules`) of the module it runs against — the most recently entered one, as in Maude.
#[derive(Debug, Default)]
pub struct Source {
    pub modules: Vec<PreModule>,
    pub commands: Vec<(usize, Command)>,
}
