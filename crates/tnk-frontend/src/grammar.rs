//! Per-module typed mixfix grammar consumed by the Earley parser.
//!
//! Grammar construction is signature-driven: each kind gets a nonterminal family, each operator gets
//! productions, and default precedence/gather is computed per operator. Emission order is observable
//! on ambiguous input, so component productions precede symbol productions.

pub mod build;
pub mod prec_gather;

use crate::lex::Sym;
use tnk_core::smt::SmtType;
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::SymbolId;

// Mixfix precedence and gather constants.
/// The most permissive gather bound / maximum precedence (`&` resolves to this).
pub const ANY: u32 = 127;
pub const MAX_PREC: u32 = 127;
/// Prefix-form argument gather; permits `_,_` inside `f(a, b)`.
pub const PREFIX_GATHER: u32 = 95;
/// Default precedence for a bare unary operator (`s_`, `-_`).
pub const UNARY_PREC: u32 = 15;
/// Default precedence for a bare binary infix operator (`_+_`).
pub const INFIX_PREC: u32 = 41;

/// A typed grammar nonterminal. Production emission order, rather than numeric identity, is observable.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Nt {
    /// Universal start symbol; every kind's term lifts to it.
    Term,
    /// A per-kind, per-type nonterminal.
    Comp(KindId, NtType),
}

/// Kind-relative nonterminal families.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum NtType {
    /// A term of this kind (`<FooTerm>`).
    Term,
    /// A sort name of this kind (`<FooSort>`).
    Sort,
    /// A flattened associative argument list of this kind (`<FooAssocList>`).
    AssocList,
}

/// A grammar terminal: a specific interned token, or a built-in lexical class matched by token *kind*.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Terminal {
    /// A specific token (operator-name fragment, punctuation, sort name). Matched by `Sym` equality.
    Tok(Sym),
    /// Any natural-number literal token.
    SmallNat,
    /// Any float literal token.
    Float,
    /// Any negative-integer literal token.
    SmallNeg,
    /// Any glued rational token `[-]num/den`; emitted only when a division symbol exists.
    Rational,
    /// An iteration token `f^count` whose base name matches the held symbol. The trailing digits are
    /// the iteration count.
    IterSymbol(Sym),
    /// Any string literal token.
    Str,
    /// Any quoted-identifier token.
    Qid,
    /// An **on-the-fly variable** written with an explicit sort, `name:sort` (one token, e.g. `X:Nat`):
    /// matches any identifier token whose suffix after the last `:` is this sort's name. The held `Sym`
    /// is the interned sort name. The whole token (`X:Nat`) becomes the variable's name (so `X:Nat` and
    /// `X:Foo` are distinct), with the production's [`Action::MakeVariable`] sort.
    ColonVar(Sym),
}

/// A right-hand-side grammar symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum GSym {
    T(Terminal),
    N(Nt),
}

impl GSym {
    pub fn is_nonterminal(&self) -> bool {
        matches!(self, GSym::N(_))
    }
}

/// The semantic action attached to a production, carrying the resolved symbol or sort needed by the
/// term-tree builder.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Action {
    /// No term built (sort-name productions).
    Nop,
    /// Return the single child's term unchanged (parens, `TERM ::= <kind>Term`).
    PassThru,
    /// Build `symbol(args…)` from the production's nonterminal children (free/mixfix/constant op).
    MakeTerm(SymbolId),
    /// Build a variable of this sort from the matched token.
    MakeVariable(SortId),
    /// Build compact `s^n(0)` from a decimal numeral for the successor `symbol`.
    MakeNatural(SymbolId),
    /// Build a negative integer `-(s^n(0))` from one negative-integer token.
    MakeInteger(SymbolId),
    /// Build compact `f^n(t)` for an iteration symbol; the token carries an arbitrary-size count.
    MakeIter(SymbolId),
    /// Build a glued rational `[-]num/den`, using the division and unary-minus symbols.
    MakeRational {
        division: SymbolId,
        minus: SymbolId,
    },
    /// Build an exact `SMT_NumberSymbol` leaf from the integer/rational token class for `kind`.
    MakeSmtNumber {
        symbol: SymbolId,
        kind: SmtType,
    },
    MakeFloat(SymbolId),
    MakeString(SymbolId),
    MakeQid(SymbolId),
    /// A flattened associative-list element, collected and reversed by `build_term`.
    AssocList,
}

/// One grammar production `lhs ::= rhs`, with its precedence and per-nonterminal gather bounds.
#[derive(Clone, Debug)]
pub struct Production {
    pub lhs: Nt,
    pub rhs: Vec<GSym>,
    /// Production precedence; accepted when `prec <= max_prec`.
    pub prec: u32,
    /// Gather bounds for nonterminal positions from left to right. A child of precedence `p` may fill
    /// position `i` when `gather[i] >= p`.
    pub gather: Vec<u32>,
    pub action: Action,
}

impl Production {
    /// The gather bound for the `nth` nonterminal of `rhs` (panics if out of range — a build bug).
    pub fn gather_for_nonterminal(&self, nth: usize) -> u32 {
        self.gather[nth]
    }
}

/// A per-module mixfix grammar: productions plus a stable [`Nt::Term`] start symbol. Built by
/// [`build::build_grammar`] and consumed by the Earley parser.
#[derive(Debug, Default)]
pub struct Grammar {
    pub productions: Vec<Production>,
}
