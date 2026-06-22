//! Built-in operator reduction (the `special (id-hook …)` seam, B3).
//!
//! [`Runtime::try_special`] is the `impl Runtime` arm that [`try_rewrite_top`](crate::engine) dispatches
//! a [`SpecialOp`] to — Maude's `eqRewrite`, tried *before* user equations and falling through (`None`)
//! on no-match. A successful return is exactly **one** rewrite: `try_special` never touches the rewrite
//! counter, so the existing `reduce` Phase-2 increment fires once when `try_rewrite_top` returns `Some`
//! (identical to a user-equation rewrite); the returned node is then re-reduced by the outer loop.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num::Nat;
use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp, SymbolId};

impl Runtime {
    /// Reduce `id` by its operator's built-in rule, or `None` if the rule does not apply.
    pub(crate) fn try_special(&mut self, sig: &Signature, id: DagId, op: &SpecialOp) -> Option<DagId> {
        match op {
            SpecialOp::Equality { eq, neq } => self.reduce_equality(sig, id, *eq, *neq),
            SpecialOp::Branch { tests } => self.reduce_branch(id, tests),
            SpecialOp::AcuNumberOp { op, nat } => self.reduce_acu_number_op(sig, id, *op, nat),
            SpecialOp::NumberOp { op, nat, bool_ } => {
                self.reduce_number_op(sig, id, *op, nat, bool_.as_ref())
            }
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

    /// Read a `Nat` numeral from `id` — the `zero` constant (`0`) or `s^count(0)` — or `None` if `id`
    /// is not a numeral (a variable-headed term, the error sort, a foreign symbol, …).
    fn as_nat(&self, id: DagId, nat: &NatHooks) -> Option<Nat> {
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == nat.zero && args.is_empty() => {
                Some(Nat::zero())
            }
            NodeTerm::S { symbol, count, arg } if *symbol == nat.succ => match &self.node(*arg).term {
                NodeTerm::Free { symbol: b, args } if *b == nat.zero && args.is_empty() => {
                    Some(count.clone())
                }
                _ => None, // s^count(non-zero) is not a ground numeral
            },
            _ => None,
        }
    }

    /// Build the `Nat` numeral for `n`: the `zero` constant (`n == 0`) or `s^n(0)` (Maude's
    /// `succSymbol->makeNatDag`). The sort follows from the node — `0 : Zero`, `s^n(0) : NzNat`.
    fn make_nat(&mut self, sig: &Signature, nat: &NatHooks, n: Nat) -> DagId {
        if n.is_zero() {
            self.make_const(sig, nat.zero)
        } else {
            let z = self.make_const(sig, nat.zero);
            self.make_s(sig, nat.succ, n, z)
        }
    }

    /// `ACU_NumberOpSymbol` (`_+_`/`_*_`/`gcd`/`lcm`/`min`/`max`): fold the **numeric** operands of the
    /// ACU multiset (each `(element, multiplicity)`), rebuilding from the result and any non-numeric
    /// residue. Needs `>= 2` numeric operands (counting multiplicity) to fire — else there is nothing
    /// to combine (`None` → user equations / normal form), which also prevents a rebuild loop.
    fn reduce_acu_number_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: NumOp,
        nat: &NatHooks,
    ) -> Option<DagId> {
        let symbol = self.node(id).symbol();
        let pairs: Vec<(DagId, u32)> = match &self.node(id).term {
            NodeTerm::Acu { args, .. } => args.clone(),
            _ => return None,
        };
        let mut acc: Option<Nat> = None;
        let mut used: u64 = 0;
        let mut residue: Vec<(DagId, u32)> = Vec::new();
        for (elem, m) in pairs {
            match self.as_nat(elem, nat) {
                Some(n) => {
                    acc = Some(match &acc {
                        None => acu_fold_first(op, &n, m),
                        Some(a) => acu_fold(op, a, &n, m),
                    });
                    used += u64::from(m);
                }
                None => residue.push((elem, m)),
            }
        }
        if used < 2 {
            return None;
        }
        let result = self.make_nat(sig, nat, acc.expect("used >= 2 ⇒ acc set"));
        if residue.is_empty() {
            Some(result)
        } else {
            residue.push((result, 1));
            Some(self.make_acu(sig, symbol, residue))
        }
    }

    /// `NumberOpSymbol` (`_quo_`/`_rem_`/`_^_`/`_<_`/`_<=_`/`_>_`/`_>=_`/`_divides_`): a free op over
    /// numeric arguments. A non-numeric argument, a zero divisor, or a too-large exponent falls through
    /// (`None`). Relational ops rewrite to a Bool constant (`bool_`), arithmetic ops to a Nat.
    fn reduce_number_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: NumOp,
        nat: &NatHooks,
        bool_: Option<&BoolHooks>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let mut a: Vec<Nat> = Vec::with_capacity(kids.len());
        for k in kids {
            a.push(self.as_nat(k, nat)?); // any non-numeric argument ⇒ no built-in reduction
        }
        match op {
            NumOp::Lt | NumOp::Le | NumOp::Gt | NumOp::Ge | NumOp::Divides => {
                let b = match op {
                    NumOp::Lt => a[0] < a[1],
                    NumOp::Le => a[0] <= a[1],
                    NumOp::Gt => a[0] > a[1],
                    NumOp::Ge => a[0] >= a[1],
                    NumOp::Divides => a[0].divides(&a[1]), // divisor is NzNat (well-typed), so > 0
                    _ => unreachable!(),
                };
                let h = bool_.expect("a relational number op carries the true/false hooks");
                Some(self.make_const(sig, if b { h.true_ } else { h.false_ }))
            }
            NumOp::Quo | NumOp::Rem => {
                if a[1].is_zero() {
                    return None; // division by zero ⇒ fall through to user equations
                }
                let (q, r) = a[0].div_rem(&a[1]);
                Some(self.make_nat(sig, nat, if matches!(op, NumOp::Quo) { q } else { r }))
            }
            NumOp::Pow => {
                let r = a[0].pow(&a[1])?; // exponent too large ⇒ fall through
                Some(self.make_nat(sig, nat, r))
            }
            // ACU ops never reach the free path (the seam pairs each op with the right SpecialOp arm).
            NumOp::Add | NumOp::Mul | NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max => {
                unreachable!("ACU number op `{op:?}` reached the free NumberOp path")
            }
        }
    }
}

/// The first numeric operand `n` (multiplicity `m`) folded into a fresh accumulator.
fn acu_fold_first(op: NumOp, n: &Nat, m: u32) -> Nat {
    match op {
        NumOp::Add => n.mul(&Nat::from_u64(u64::from(m))), // n added m times
        NumOp::Mul => n.pow_u64(u64::from(m)),             // n multiplied m times
        // gcd/lcm/min/max are idempotent in multiplicity.
        NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max => n.clone(),
        _ => unreachable!("non-ACU number op `{op:?}` in the ACU fold"),
    }
}

/// A subsequent numeric operand `n` (multiplicity `m`) combined with the accumulator `acc`.
fn acu_fold(op: NumOp, acc: &Nat, n: &Nat, m: u32) -> Nat {
    match op {
        NumOp::Add => acc.add(&n.mul(&Nat::from_u64(u64::from(m)))),
        NumOp::Mul => acc.mul(&n.pow_u64(u64::from(m))),
        NumOp::Gcd => acc.gcd(n),
        NumOp::Lcm => acc.lcm(n),
        NumOp::Min => core::cmp::min(acc.clone(), n.clone()),
        NumOp::Max => core::cmp::max(acc.clone(), n.clone()),
        _ => unreachable!("non-ACU number op `{op:?}` in the ACU fold"),
    }
}
