//! The per-module **mixfix CF grammar**, built from the signature (B4.3) and consumed by the Earley
//! parser (B4.4). A direct port of Maude's `Mixfix/makeGrammar.cc` + `MixfixModule::computePrecAndGather`
//! (`mixfixModule.cc`), adapted to typed nonterminals/terminals instead of Maude's signed-int encoding.
//!
//! The grammar is *signature-driven*: each connected component (kind) gets a family of nonterminals
//! ([`NtType`]), each operator a set of productions ([`build`]), and OBJ3 default precedence/gather is
//! computed per operator ([`prec_gather`]). The **emission order** (component productions before symbol
//! productions) is observable — it decides which parse is found first on ambiguous input — so [`build`]
//! reproduces Maude's order.

pub mod build;
pub mod prec_gather;

use crate::lex::Sym;
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::SymbolId;

// OBJ3 precedence/gather constants — Maude `mixfixModule.hh` `enum Precedence`.
/// The most permissive gather bound / maximum precedence (`&` resolves to this).
pub const ANY: u32 = 127;
pub const MAX_PREC: u32 = 127;
/// Prefix-form argument gather — lets `_,_` work inside `f(a, b)` (Maude's comment).
pub const PREFIX_GATHER: u32 = 95;
/// OBJ3 default precedence for a bare unary operator (`s_`, `-_`).
pub const UNARY_PREC: u32 = 15;
/// OBJ3 default precedence for a bare binary infix operator (`_+_`).
pub const INFIX_PREC: u32 = 41;

/// A grammar nonterminal. Maude numbers these as negative ints (fixed ones, plus per
/// connected-component × [`NtType`]); we use a typed enum since only the production *emission order*,
/// not the numbering, is observable.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Nt {
    /// The universal start symbol; every kind's term lifts to it (`TERM ::= <kind>Term`, Maude's `TERM`).
    Term,
    /// A per-connected-component (kind), per-type nonterminal (Maude's `nonTerminal(component, type)`).
    Comp(KindId, NtType),
    /// The per-iter-symbol nonterminal for the `f^n(t)` token form (Maude's `iterSymbols` map). Deferred
    /// (the milestone uses repeated mixfix `s s 0`, not the `s_^n` token); reserved here.
    Iter(SymbolId),
}

/// The kind-relative nonterminal families (Maude's `enum NonTerminalType`, simple/non-complex subset).
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
    /// Any natural-number literal token (Maude's `SMALL_NAT`); matched by [`crate::lex::TokKind::Number`].
    SmallNat,
    /// Any float literal token (Maude's `FLOAT_NT`).
    Float,
    /// Any negative-integer literal token (Maude's `SMALL_NEG`); matched by [`crate::lex::TokKind::NegNumber`].
    SmallNeg,
    /// Any string literal token (Maude's `STRING_NT`).
    Str,
    /// Any quoted-identifier token (Maude's `QUOTED_ID`).
    Qid,
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

/// The semantic action attached to a production — the functional subset of Maude's ~70 `MixfixParser`
/// actions, carrying the resolved symbol/sort the tree-walker ([`crate::build_term`], B4.4b) needs.
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
    /// Build `s^n(0)` from a decimal numeral, for the successor `symbol` (Maude's `MAKE_NATURAL`).
    MakeNatural(SymbolId),
    /// Build a negative integer `-(s^n(0))` from a `SMALL_NEG` token, for the minus `symbol` (Maude's
    /// `MAKE_INTEGER` → `MinusSymbol::makeIntTerm`).
    MakeInteger(SymbolId),
    /// Build `f^n(t)` for the `iter` `symbol` (Maude's `MAKE_ITER`). Deferred with [`Nt::Iter`].
    MakeIter(SymbolId),
    MakeFloat(SymbolId),
    MakeString(SymbolId),
    MakeQid(SymbolId),
    /// A flattened associative-list element (Maude's `ASSOC_LIST`); collected + reversed by build_term.
    AssocList,
}

/// One grammar production `lhs ::= rhs`, with its precedence and per-nonterminal gather bounds.
#[derive(Clone, Debug)]
pub struct Production {
    pub lhs: Nt,
    pub rhs: Vec<GSym>,
    /// The production's own precedence (Maude's `Rule::prec`); a call accepts it iff `prec <= maxPrec`.
    pub prec: u32,
    /// One gather bound per **nonterminal** in `rhs`, in left-to-right order (Maude stores it in each
    /// rhs `Pair.prec`). A completed sub-production of precedence `p` may fill the `i`-th nonterminal
    /// hole iff `gather[i] >= p`.
    pub gather: Vec<u32>,
    pub action: Action,
}

impl Production {
    /// The gather bound for the `nth` nonterminal of `rhs` (panics if out of range — a build bug).
    pub fn gather_for_nonterminal(&self, nth: usize) -> u32 {
        self.gather[nth]
    }
}

/// A per-module mixfix grammar: the productions plus a stable start symbol ([`Nt::Term`]). Built by
/// [`build::build_grammar`]; consumed by the Earley parser (B4.4).
#[derive(Debug, Default)]
pub struct Grammar {
    pub productions: Vec<Production>,
}
