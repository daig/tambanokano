//! Built-in operator reduction (the `special (id-hook …)` seam, B3).
//!
//! [`Runtime::try_special`] is the `impl Runtime` arm that [`try_rewrite_top`](crate::engine) dispatches
//! a [`SpecialOp`] to — Maude's `eqRewrite`, tried *before* user equations and falling through (`None`)
//! on no-match. A successful return is exactly **one** rewrite: `try_special` never touches the rewrite
//! counter, so the existing `reduce` Phase-2 increment fires once when `try_rewrite_top` returns `Some`
//! (identical to a user-equation rewrite); the returned node is then re-reduced by the outer loop.

use crate::dag::DagId;
use crate::engine::{Runtime, Signature};
use crate::symbol::{SpecialOp, SymbolId};

impl Runtime {
    /// Reduce `id` by its operator's built-in rule, or `None` if the rule does not apply.
    pub(crate) fn try_special(&mut self, sig: &Signature, id: DagId, op: &SpecialOp) -> Option<DagId> {
        match op {
            SpecialOp::Equality { eq, neq } => self.reduce_equality(sig, id, *eq, *neq),
            SpecialOp::Branch { tests } => self.reduce_branch(id, tests),
        }
    }

    /// `_==_` / `_=/=_` (Maude's `EqualitySymbol`): both arguments are already reduced (standard
    /// strategy), so compare them structurally (modulo the axioms) and rewrite to the `eq`/`neq`
    /// constant. Always applies (equality never falls through).
    fn reduce_equality(
        &mut self,
        sig: &Signature,
        id: DagId,
        eq: SymbolId,
        neq: SymbolId,
    ) -> Option<DagId> {
        let (l, r) = {
            let mut kids = self.node(id).children();
            (kids.next().expect("_==_ is binary"), kids.next().expect("_==_ is binary"))
        };
        let chosen = if self.deep_equal(l, r) { eq } else { neq };
        Some(self.make_const(sig, chosen))
    }

    /// `if_then_else_fi` (Maude's `BranchSymbol`): the condition (arg 0) is reduced (the seam's lazy
    /// `strat (1 0)`); match it against the `tests` constants and return the corresponding branch
    /// **unreduced** — the outer reduce loop normalizes only it, so the dead branch is never reduced. A
    /// condition matching no test falls through (→ user equations; the reduce-the-branches-first
    /// fidelity for a stuck condition is a follow-up).
    fn reduce_branch(&self, id: DagId, tests: &[SymbolId]) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let cond_sym = self.node(kids[0]).symbol();
        tests.iter().position(|&t| t == cond_sym).map(|i| kids[i + 1])
    }
}
