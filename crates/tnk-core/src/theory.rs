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

use crate::dag::DagId;
use crate::engine::{Runtime, Signature};
use crate::term::{Subst, Term};

/// A left-hand side compiled for matching in its theory. Closed set (decision **D3**); Phase 1 has
/// only the free arm. Future arms (`Acu`, `Au`, `Cui`, `S`, …) carry their compiled per-theory
/// automata and are pure additions behind this type.
#[derive(Debug)]
pub(crate) enum LhsAutomaton {
    /// Free theory: matched by direct structural recursion ([`Engine::match_pattern`]). The pattern
    /// is stored as-is; compiling it to a discrimination net is a later performance optimization that
    /// does not change this seam. Single-solution **only while every argument is itself free**: once
    /// alien sub-theory arguments appear (e.g. an AC subterm), this arm recurses to the alien boundary
    /// and composes the children's subproblems (a future `Sequence` arm) instead of always returning
    /// [`Subproblem::FreeOnce`].
    Free(Term),
}

impl LhsAutomaton {
    /// Compile a pattern `lhs` into an automaton for its theory. (Free theory: keep the term.)
    pub(crate) fn compile(lhs: Term) -> Self {
        LhsAutomaton::Free(lhs)
    }

    /// First (deterministic) match phase: bind the forced part of the match into `subst` and return a
    /// residual [`Subproblem`] enumerating the solutions, or `None` if the subject cannot match at
    /// all. For the free theory the match is fully determined here, so the returned subproblem yields
    /// exactly the one solution already bound in `subst`.
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        subst: &mut Subst,
    ) -> Option<Subproblem> {
        match self {
            LhsAutomaton::Free(pat) => rt
                .match_pattern(sig, pat, subject, subst)
                .then_some(Subproblem::FreeOnce { pending: true }),
        }
    }
}

/// A residual matching subproblem: a resumable enumerator of the remaining solutions of an
/// [`LhsAutomaton`] against a subject. [`Subproblem::next`] binds the next solution into the shared
/// `Subst` and returns `true`, or returns `false` once the solutions are exhausted.
///
/// This is the stream the reduce driver consumes; AC matching will populate it with the several
/// solutions of an associative-commutative match, and conditional equations will `next()` again when
/// a solution fails its condition. Closed set (decision **D3**); solution *combinators* (sequence /
/// disjunction over sub-matches) are the heterogeneous case that may later use boxed recursion.
#[derive(Debug)]
pub(crate) enum Subproblem {
    /// The free theory has at most one solution (a deterministic structural match), already bound in
    /// `subst` by [`LhsAutomaton::match_`]; `pending` yields it exactly once.
    FreeOnce { pending: bool },
}

impl Subproblem {
    /// Advance to the next solution, binding it into `subst`; `false` when exhausted. `rt`/`subst`
    /// are unused for the free arm (its single solution was bound during `match_`) but are the inputs
    /// a multi-solution arm needs.
    pub(crate) fn next(&mut self, _rt: &Runtime, _subst: &mut Subst) -> bool {
        match self {
            // Yield the already-bound solution exactly once.
            Subproblem::FreeOnce { pending } => core::mem::replace(pending, false),
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

        let lhs = LhsAutomaton::compile(Term::op(f, vec![Term::var(0, nat), Term::constant(a)])); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        let mut sp = lhs
            .match_(e.runtime(), e.signature(), subject, &mut subst)
            .expect("f(a,a) matches f(X,a)");
        assert!(sp.next(e.runtime(), &mut subst), "the one solution");
        assert_eq!(subst.get(0), Some(a0), "X bound to the first argument");
        assert!(!sp.next(e.runtime(), &mut subst), "free theory has a single solution");
        assert!(!sp.next(e.runtime(), &mut subst), "an exhausted subproblem stays exhausted");
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

        let lhs = LhsAutomaton::compile(Term::op(f, vec![Term::var(0, nat), Term::constant(a)])); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        assert!(
            lhs.match_(e.runtime(), e.signature(), subject, &mut subst).is_none(),
            "f(b,b) does not match f(X,a)"
        );
    }
}
