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
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub(crate) name: String,
    pub(crate) domain: Vec<SortId>,
    pub(crate) range: SortId,
    /// The structural axioms this operator is declared with.
    pub(crate) axioms: Axioms,
    /// The operator's two-sided identity (`id: <term>`), if any. Stored as the **constant** symbol
    /// that is the identity (every conformance target — `0`/`empty`/`e` — is a constant); a general
    /// identity *term* is a later generalization. Canonicalization drops identity arguments and a
    /// matched AC variable may bind this constant (the "collapse to unit" solutions).
    pub(crate) identity: Option<SymbolId>,
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arity(&self) -> usize {
        self.domain.len()
    }

    /// The operator's equational theory (decision **D3**), classified from its [`Axioms`]:
    /// `assoc & comm` → [`Acu`](Theory::Acu); `assoc` only → [`Au`](Theory::Au); else
    /// [`Free`](Theory::Free). (Comm-only is the `Cui` theory — not yet implemented, so it classifies
    /// as `Free` here; the `add_op_*` constructors only set the supported combinations.)
    pub(crate) fn theory(&self) -> Theory {
        match (self.axioms.assoc, self.axioms.comm) {
            (true, true) => Theory::Acu,
            (true, false) => Theory::Au,
            _ => Theory::Free,
        }
    }

    /// The identity constant symbol, if this operator was declared with `id:`.
    pub(crate) fn identity(&self) -> Option<SymbolId> {
        self.identity
    }
}
