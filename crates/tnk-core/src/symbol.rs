//! Operator symbols.
//!
//! Phase 0 carried a name and a single sort declaration (`domain -> range`). Stage B1 adds the
//! **equational axioms** an operator is declared with (`assoc`/`comm`/`id:`), which select the
//! operator's *theory* — the term representation and matching algorithm used for it. Per decision
//! **D3** the theory is a closed `enum` (no `Symbol`-is-a-`Theory` inheritance); the axioms are plain
//! data on the symbol and [`Symbol::theory`] classifies them. Ad-hoc overloading (multiple
//! declarations + sort diagram) and the remaining attributes are layered on later by composition.
//!
//! Fields are `pub(crate)`; read access is through getters (review R3 H4).

use crate::id::Id;
use crate::sort::SortId;

pub type SymbolId = Id<Symbol>;

/// The equational axioms an operator is declared with (Maude's `assoc`/`comm`/`id:` attributes).
/// `idem` (and the assoc-only / comm-only theories) are later B1 sub-steps; this slice handles the
/// **ACU** combination (`assoc comm`, optionally with a two-sided identity).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Axioms {
    pub assoc: bool,
    pub comm: bool,
    /// Idempotence (`f(a, a) = a`) — only meaningful for the commutative, non-associative CUI theory
    /// in this slice (`idem` cannot combine with `assoc`).
    pub idem: bool,
    /// Iteration (`iter`, B3): a unary "stacked successor" operator (`s_`) whose node stores the
    /// iteration count compactly (the **S theory**). Mutually exclusive with assoc/comm/idem.
    pub iter: bool,
}

/// Which equational theory an operator belongs to — selects its `DagNode` representation and its
/// matching automaton (decision **D3**: a closed enum, enum-dispatched). This slice implements
/// [`Free`](Theory::Free), [`Acu`](Theory::Acu), and [`Au`](Theory::Au); `Cui`/`S`/`Na` are later.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Theory {
    /// No structural axioms: `symbol(args...)` matched by direct structural recursion.
    Free,
    /// Associative + commutative (with an optional two-sided identity): a flattened **multiset** of
    /// arguments, matched modulo AC(+U).
    Acu,
    /// Associative (with an optional two-sided identity), **not** commutative: a flattened **ordered
    /// sequence** of arguments, matched modulo A(+U) — e.g. lists, string concatenation.
    Au,
    /// Commutative (with optional identity and/or idempotence), **not** associative: a binary node
    /// with canonically-ordered arguments, matched modulo C(+U+I).
    Cui,
    /// Iteration (`iter`, B3): a unary successor `s_` stored as `s^count(arg)` with a bignum `count`,
    /// matched modulo the stacked-successor extension (`s^k` matches `s^n` for `k <= n`).
    S,
}

/// One operator declaration: argument sorts (`domain`) → `range`, plus whether it is a constructor
/// (`[ctor]`). An operator may carry several declarations (ad-hoc / subsort overloading); the least
/// sort of an application is resolved across all of them (`Signature::compute_sort`). `ctor` is
/// carried now and consumed when the constructor diagram lands (a later B2 sub-step).
#[derive(Debug, Clone)]
pub(crate) struct OpDeclaration {
    pub domain: Vec<SortId>,
    pub range: SortId,
    /// `[ctor]` flag (B2.4). Metadata for functional reduction — a `[ctor]` operator reduces exactly as
    /// a non-`ctor` one (verified against the binary); it marks the operator as a constructor for the
    /// later sufficient-completeness / constructor-diagram analysis.
    pub ctor: bool,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub(crate) name: String,
    /// Operator declarations (≥ 1; the first is the original). Overloads share name + arity; sort
    /// resolution walks them **in declaration order**, so order is load-bearing for the
    /// non-preregular least-sort tie-break.
    pub(crate) decls: Vec<OpDeclaration>,
    /// The structural axioms this operator is declared with.
    pub(crate) axioms: Axioms,
    /// The operator's two-sided identity (`id: <term>`), if any. Stored as the **constant** symbol
    /// that is the identity (every conformance target — `0`/`empty`/`e` — is a constant); a general
    /// identity *term* is a later generalization. Canonicalization drops identity arguments and a
    /// matched AC variable may bind this constant (the "collapse to unit" solutions).
    pub(crate) identity: Option<SymbolId>,
    /// Evaluation strategy `strat (…)` (B2.4): the 0-based argument positions to reduce, in order,
    /// before a top rewrite. `None` is the standard strategy (reduce every argument left-to-right); a
    /// custom strategy may leave arguments unreduced (lazy) — e.g. `if_then_else_fi` with `strat (1 0)`.
    pub(crate) strategy: Option<Vec<u32>>,
    /// Built-in reduction rule (`special (id-hook …)`, B3), if any — tried before user equations.
    pub(crate) special: Option<SpecialOp>,
}

/// A built-in operator's reduction rule (decision **#6** / **D3**): Maude's `special (id-hook …)` seam
/// as a typed enum resolved at module-build time and dispatched by `match` in symbol reduction — not
/// C++'s attached member-function pointers. `term-hook`/`op-hook` references are resolved to
/// [`SymbolId`]s. This slice has the BOOL operators; NAT/INT arithmetic variants are added with those
/// ops. (Until the parser lands the hooks are supplied programmatically via `Engine::set_special`.)
#[derive(Debug, Clone)]
pub enum SpecialOp {
    /// `_==_` / `_=/=_` (Maude's `EqualitySymbol`): reduce both arguments, compare them structurally,
    /// rewrite to `eq` if equal else `neq` (the `equalTerm`/`notEqualTerm` constants, swapped for
    /// `=/=`).
    Equality { eq: SymbolId, neq: SymbolId },
    /// `if_then_else_fi` (Maude's `BranchSymbol`): with the condition reduced (the seam installs a lazy
    /// `strat (1 0)`), select the branch whose position matches the condition among `tests` (the
    /// `term-hook` constants, e.g. `[true, false]`), returning it **unreduced** — the dead branch is
    /// never reduced.
    Branch { tests: Vec<SymbolId> },
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arity(&self) -> usize {
        self.decls[0].domain.len()
    }

    /// The operator's declarations (≥ 1); least-sort resolution walks them in declaration order.
    pub(crate) fn decls(&self) -> &[OpDeclaration] {
        &self.decls
    }

    /// The operator's equational theory (decision **D3**), classified from its [`Axioms`]:
    /// `assoc & comm` → [`Acu`](Theory::Acu); `assoc` only → [`Au`](Theory::Au); `comm` only →
    /// [`Cui`](Theory::Cui); else [`Free`](Theory::Free). (`idem` rides along inside CUI.)
    pub(crate) fn theory(&self) -> Theory {
        if self.axioms.iter {
            return Theory::S; // `iter` is mutually exclusive with assoc/comm (checked at registration)
        }
        match (self.axioms.assoc, self.axioms.comm) {
            (true, true) => Theory::Acu,
            (true, false) => Theory::Au,
            (false, true) => Theory::Cui,
            (false, false) => Theory::Free,
        }
    }

    /// The identity constant symbol, if this operator was declared with `id:`.
    pub(crate) fn identity(&self) -> Option<SymbolId> {
        self.identity
    }

    /// The operator's built-in reduction rule (`special (id-hook …)`), if any (B3).
    pub(crate) fn special(&self) -> Option<&SpecialOp> {
        self.special.as_ref()
    }

    /// Whether every declaration of this operator is a constructor (`[ctor]`). Metadata — it does not
    /// affect reduction; recorded for the later constructor analysis (B2.4).
    pub(crate) fn is_constructor(&self) -> bool {
        self.decls.iter().all(|d| d.ctor)
    }
}
