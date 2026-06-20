//! The theory-plugin seam (review R3 C1; A2 report §2): a compiled [`LhsAutomaton`] whose two-phase
//! match produces a resumable, multi-solution [`Subproblem`].
//!
//! Phase 1 implements only the **free theory** — a deterministic, single-solution structural match —
//! but the *shape* is what the later theories need and is the reason this seam exists now:
//! - **AC/ACU matching is genuinely multi-solution** (one pattern can match a subject many ways), so
//!   the rewrite driver must consume a *stream* of solutions, not a single yes/no.
//! - **Conditional equations** accept a solution only if the condition holds, and otherwise must
//!   **backtrack into the next solution** of the same left-hand side.
//!
//! Driving [`crate::engine::Engine::reduce`]'s rewrite step around `while sp.next(..) { .. }` now
//! means adding those features later is a new [`Subproblem`] arm plus a condition check in the
//! existing loop — not a rewrite of the reduce core. Free matching stays the recursive
//! [`Engine::match_pattern`]; the compiled discrimination net is a later performance step behind this
//! same seam and does not change the driver.
//!
//! Since the A4 signature/runtime split, [`LhsAutomaton::match_`]/[`Subproblem::next`] take the
//! immutable `Signature` and the mutable `Runtime` separately: a conditional equation can `reduce`
//! its condition (needs `&mut` runtime) and an AC subproblem can allocate residue nodes while the
//! equation table stays borrowed — without changing the driver loop.

use crate::acu::{AcuLhs, AcuSubproblem};
use crate::au::{AuLhs, AuSubproblem};
use crate::cui::{CuiLhs, CuiSubproblem};
use crate::dag::DagId;
use crate::engine::{Runtime, Signature};
use crate::symbol::Theory;
use crate::term::{Subst, Term};

/// A left-hand side compiled for matching in its theory. Closed set (decision **D3**); this slice has
/// the free and **ACU** arms. Future arms (`Au`, `Cui`, `S`, …) carry their compiled per-theory
/// automata and are pure additions behind this type.
pub(crate) enum LhsAutomaton {
    /// Free theory: matched by direct structural recursion ([`Engine::match_pattern`]). The pattern
    /// is stored as-is; compiling it to a discrimination net is a later performance optimization that
    /// does not change this seam. Single-solution **only while every argument is itself free**: once
    /// alien sub-theory arguments appear (e.g. an AC subterm), this arm recurses to the alien boundary
    /// and composes the children's subproblems (a future `Sequence` arm) instead of always returning
    /// [`Subproblem::FreeOnce`].
    Free(Term),
    /// ACU theory (`assoc comm [id:]`): multiset matching, genuinely multi-solution.
    Acu(AcuLhs),
    /// AU theory (`assoc [id:]`, not commutative): ordered-sequence matching with extension.
    Au(AuLhs),
    /// CUI theory (`comm [idem] [id:]`, not associative): commutative binary matching.
    Cui(CuiLhs),
}

impl LhsAutomaton {
    /// Compile a pattern `lhs` into an automaton for its theory, chosen from the top symbol's theory.
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        match lhs.top_symbol().map(|s| sig.symbol(s).theory()) {
            Some(Theory::Acu) => LhsAutomaton::Acu(AcuLhs::compile(lhs, sig)),
            Some(Theory::Au) => LhsAutomaton::Au(AuLhs::compile(lhs, sig)),
            Some(Theory::Cui) => LhsAutomaton::Cui(CuiLhs::compile(lhs, sig)),
            _ => LhsAutomaton::Free(lhs),
        }
    }

    /// First (deterministic) match phase: bind the forced part of the match into `subst` and return a
    /// residual [`Subproblem`] enumerating the solutions, or `None` if the subject cannot match at
    /// all. For the free theory the match is fully determined here, so the returned subproblem yields
    /// exactly the one solution already bound in `subst`.
    ///
    /// `ext_allowed` enables *extension* (matching a sub-multiset of an AC subject and leaving a
    /// residue) — the free theory ignores it; ACU uses it for top-level rewriting and `xmatch`
    /// (audit F-3).
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        subst: &mut Subst,
        ext_allowed: bool,
    ) -> Option<Subproblem> {
        match self {
            LhsAutomaton::Free(pat) => rt
                .match_pattern(sig, pat, subject, subst)
                .then_some(Subproblem::FreeOnce { pending: true }),
            LhsAutomaton::Acu(lhs) => {
                lhs.match_(rt, sig, subject, ext_allowed).map(Subproblem::Acu)
            }
            LhsAutomaton::Au(lhs) => lhs.match_(rt, sig, subject, ext_allowed).map(Subproblem::Au),
            // CUI is binary with no extension, so it ignores `ext_allowed`.
            LhsAutomaton::Cui(lhs) => lhs.match_(rt, sig, subject).map(Subproblem::Cui),
        }
    }
}

/// A residual matching subproblem: a resumable enumerator of the remaining solutions of an
/// [`LhsAutomaton`] against a subject. [`Subproblem::next`] binds the next solution into the shared
/// `Subst` and returns `true`, or returns `false` once the solutions are exhausted.
///
/// This is the stream the reduce driver consumes: ACU matching populates it with the several
/// solutions of an associative-commutative match, and conditional equations (B2) will `next()` again
/// when a solution fails its condition. Closed set (decision **D3**); solution *combinators*
/// (sequence / disjunction over sub-matches) are the heterogeneous case that may later use boxing.
pub(crate) enum Subproblem {
    /// The free theory has at most one solution (a deterministic structural match), already bound in
    /// `subst` by [`LhsAutomaton::match_`]; `pending` yields it exactly once.
    FreeOnce { pending: bool },
    /// ACU theory: a resumable multiset-distribution enumerator (see [`AcuSubproblem`]).
    Acu(AcuSubproblem),
    /// AU theory: a resumable ordered-sequence enumerator (see [`AuSubproblem`]).
    Au(AuSubproblem),
    /// CUI theory: the (at most two) commutative pairings (see [`CuiSubproblem`]).
    Cui(CuiSubproblem),
}

impl Subproblem {
    /// Advance to the next solution, binding it into `subst`; `false` when exhausted. Takes
    /// `&mut Runtime` because a multi-solution arm (ACU/AU) builds fresh binding/residue nodes between
    /// solutions (audit F-3 widening); the free arm ignores `rt`/`sig`/`subst` (its single solution
    /// was bound during `match_`).
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        match self {
            // Yield the already-bound solution exactly once.
            Subproblem::FreeOnce { pending } => core::mem::replace(pending, false),
            Subproblem::Acu(sp) => sp.next(rt, sig, subst),
            Subproblem::Au(sp) => sp.next(rt, sig, subst),
            Subproblem::Cui(sp) => sp.next(rt, sig, subst),
        }
    }

    /// Build the rewrite result by splicing the instantiated `rhs` into the matched position: a whole
    /// match (the free theory, or an extension match with no residue) is just `rhs`; an extension
    /// match re-assembles the residue around it in the theory's normal form — an ACU multiset, or an
    /// AU ordered prefix/suffix (Maude's `partialConstruct`). Needs `&mut Runtime` to build the node.
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        match self {
            Subproblem::FreeOnce { .. } => rhs,
            Subproblem::Acu(sp) => sp.build_result(rt, sig, rhs),
            Subproblem::Au(sp) => sp.build_result(rt, sig, rhs),
            Subproblem::Cui(sp) => sp.build_result(rt, sig, rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// The free arm is single-solution: `match_` binds it, the subproblem yields it once, then stays
    /// exhausted across further `next` calls (the contract the reduce driver relies on).
    #[test]
    fn free_automaton_yields_exactly_one_solution() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let a0 = e.make_const(a);
        let a1 = e.make_const(a);
        let subject = e.make_free(f, vec![a0, a1]); // f(a, a)

        let lhs = LhsAutomaton::compile(
            Term::op(f, vec![Term::var(0, nat), Term::constant(a)]),
            e.signature(),
        ); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        let (sig, rt) = e.parts_mut();
        let mut sp = lhs.match_(rt, sig, subject, &mut subst, false).expect("f(a,a) matches f(X,a)");
        assert!(sp.next(rt, sig, &mut subst), "the one solution");
        assert_eq!(subst.get(0), Some(a0), "X bound to the first argument");
        assert!(!sp.next(rt, sig, &mut subst), "free theory has a single solution");
        assert!(!sp.next(rt, sig, &mut subst), "an exhausted subproblem stays exhausted");
    }

    /// A non-matching subject yields `None` from `match_` (no subproblem to drive).
    #[test]
    fn free_automaton_reports_non_match() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let b0 = e.make_const(b);
        let b1 = e.make_const(b);
        let subject = e.make_free(f, vec![b0, b1]); // f(b, b)

        let lhs = LhsAutomaton::compile(
            Term::op(f, vec![Term::var(0, nat), Term::constant(a)]),
            e.signature(),
        ); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        assert!(
            lhs.match_(e.runtime(), e.signature(), subject, &mut subst, false).is_none(),
            "f(b,b) does not match f(X,a)"
        );
    }
}
