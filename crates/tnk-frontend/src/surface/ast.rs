//! Surface AST: the `PreModule` (signature + raw statement bubbles) the surface parser produces before
//! the per-module mixfix term parse runs (B4.4). Term-carrying parts (op identity, equation lhs/rhs,
//! conditions, command terms) are kept as un-parsed token **bubbles**.

use crate::lex::Token;

/// A parsed functional-module skeleton.
#[derive(Debug)]
pub struct PreModule {
    pub name: String,
    pub sorts: Vec<String>,
    /// Each subsort chain `A B < C < D` as ordered groups (every group is below the next).
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
}

/// One operator declaration `op <name> : <domain> -> <range> [<attrs>] .` (or `ops …` expanded to one
/// `OpDecl` per name).
#[derive(Debug)]
pub struct OpDecl {
    /// The mixfix name as raw tokens (`[_+_]`, `[s_]`, `[<_, ,, _>]`, `[gcd]`).
    pub name: Vec<Token>,
    pub domain: Vec<String>,
    pub range: String,
    pub attrs: Attrs,
}

#[derive(Debug)]
pub struct VarDecl {
    pub names: Vec<String>,
    pub sort: String,
}

/// Operator attributes (`[assoc comm id: … ctor iter prec gather strat special ditto]`).
#[derive(Debug, Default)]
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
#[derive(Debug)]
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

/// The result of surface-parsing a source file: the modules and the top-level commands (in order).
#[derive(Debug, Default)]
pub struct Source {
    pub modules: Vec<PreModule>,
    pub commands: Vec<Command>,
}
