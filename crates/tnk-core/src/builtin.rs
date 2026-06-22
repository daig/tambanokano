//! Built-in operator reduction (the `special (id-hook …)` seam, B3).
//!
//! [`Runtime::try_special`] is the `impl Runtime` arm that [`try_rewrite_top`](crate::engine) dispatches
//! a [`SpecialOp`] to — Maude's `eqRewrite`, tried *before* user equations and falling through (`None`)
//! on no-match. A successful return is exactly **one** rewrite: `try_special` never touches the rewrite
//! counter, so the existing `reduce` Phase-2 increment fires once when `try_rewrite_top` returns `Some`
//! (identical to a user-equation rewrite); the returned node is then re-reduced by the outer loop.

use crate::dag::{DagId, NaValue, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num::{Int, Nat};
use crate::symbol::{BoolHooks, FltOp, NatHooks, NumOp, SpecialOp, StrOp, SymbolId};
use std::rc::Rc;

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
            SpecialOp::Minus { nat } => self.reduce_minus(id, nat),
            SpecialOp::StringOp { op, str_sym, nat, bool_ } => {
                self.reduce_string_op(sig, id, *op, *str_sym, nat.as_ref(), bool_.as_ref())
            }
            SpecialOp::FloatOp { op, float_sym, bool_ } => {
                self.reduce_float_op(sig, id, *op, *float_sym, bool_.as_ref())
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

    /// The magnitude of a non-negative numeral at `id` — the `zero` constant (`0`) or `s^count(0)` — or
    /// `None` if `id` is not such a numeral. (`as_int` builds on this; `divides` works on magnitudes.)
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

    /// Read an `Int` numeral from `id`: a non-negative numeral (`0` / `s^n(0)`), or `-(s^n(0))` when the
    /// `minus` hook is set (INT). `None` if `id` is not a numeral.
    fn as_int(&self, id: DagId, nat: &NatHooks) -> Option<Int> {
        if let Some(n) = self.as_nat(id, nat) {
            return Some(Int::from_nat(&n));
        }
        let minus = nat.minus?;
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                Some(Int::from_nat(&self.as_nat(args[0], nat)?).neg())
            }
            _ => None,
        }
    }

    /// Build the numeral for `n`: `0` / `s^|n|(0)` / `-(s^|n|(0))` (Maude's `succSymbol->makeNatDag` and
    /// `MinusSymbol`). The sort follows the node (`0 : Zero`, `s^n(0) : NzNat`, `-(s^n(0)) : NzInt`). A
    /// **negative** `n` with no `minus` hook (NAT) returns `None` — the op falls through to user
    /// equations (a signed result needs INT).
    fn make_int(&mut self, sig: &Signature, nat: &NatHooks, n: Int) -> Option<DagId> {
        if n.is_zero() {
            return Some(self.make_const(sig, nat.zero));
        }
        let pos = {
            let z = self.make_const(sig, nat.zero);
            self.make_s(sig, nat.succ, n.magnitude(), z)
        };
        if n.is_negative() {
            Some(self.make_free(sig, nat.minus?, vec![pos]))
        } else {
            Some(pos)
        }
    }

    /// `-_` (Maude's `MinusSymbol`): `-(-x) = x`, `-0 = 0`; `-(s^n(0))` is the canonical negative (no
    /// rewrite). The argument is already reduced (standard strategy).
    fn reduce_minus(&self, id: DagId, nat: &NatHooks) -> Option<DagId> {
        let arg = self.node(id).children().next().expect("-_ is unary");
        match &self.node(arg).term {
            NodeTerm::Free { symbol, args } if Some(*symbol) == nat.minus && args.len() == 1 => {
                Some(args[0]) // -(-x) = x
            }
            NodeTerm::Free { symbol, args } if *symbol == nat.zero && args.is_empty() => Some(arg), // -0 = 0
            _ => None, // -(s^n(0)) is canonical
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
        let mut acc: Option<Int> = None;
        let mut used: u64 = 0;
        let mut residue: Vec<(DagId, u32)> = Vec::new();
        for (elem, m) in pairs {
            match self.as_int(elem, nat) {
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
        let result = self.make_int(sig, nat, acc.expect("used >= 2 ⇒ acc set"))?;
        if residue.is_empty() {
            Some(result)
        } else {
            residue.push((result, 1));
            Some(self.make_acu(sig, symbol, residue))
        }
    }

    /// `NumberOpSymbol` (`_-_`/`_quo_`/`_rem_`/`_^_`/`_<_`/`_<=_`/`_>_`/`_>=_`/`_divides_`): a free op
    /// over numeric arguments. A non-numeric argument, a zero divisor, a negative result with no `minus`
    /// hook, or a too-large/negative exponent falls through (`None`). Relational ops rewrite to a Bool
    /// constant (`bool_`); arithmetic ops to a Nat/Int.
    fn reduce_number_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: NumOp,
        nat: &NatHooks,
        bool_: Option<&BoolHooks>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let mut a: Vec<Int> = Vec::with_capacity(kids.len());
        for k in kids {
            a.push(self.as_int(k, nat)?); // any non-numeric argument ⇒ no built-in reduction
        }
        match op {
            NumOp::Lt | NumOp::Le | NumOp::Gt | NumOp::Ge | NumOp::Divides => {
                let b = match op {
                    NumOp::Lt => a[0] < a[1],
                    NumOp::Le => a[0] <= a[1],
                    NumOp::Gt => a[0] > a[1],
                    NumOp::Ge => a[0] >= a[1],
                    // `_divides_ : NzNat Nat -> Bool` — non-negative operands, so compare magnitudes.
                    NumOp::Divides => a[0].magnitude().divides(&a[1].magnitude()),
                    _ => unreachable!(),
                };
                let h = bool_.expect("a relational number op carries the true/false hooks");
                Some(self.make_const(sig, if b { h.true_ } else { h.false_ }))
            }
            NumOp::Sub => self.make_int(sig, nat, a[0].sub(&a[1])),
            NumOp::Quo | NumOp::Rem => {
                if a[1].is_zero() {
                    return None; // division by zero ⇒ fall through to user equations
                }
                let (q, r) = a[0].div_rem(&a[1]); // truncated toward zero (Maude quo/rem)
                self.make_int(sig, nat, if matches!(op, NumOp::Quo) { q } else { r })
            }
            NumOp::Pow => {
                if a[1].is_negative() {
                    return None; // `_^_ : Int Nat -> Int` needs a non-negative exponent
                }
                let e = a[1].magnitude().to_usize()? as u64; // too-large exponent ⇒ fall through
                self.make_int(sig, nat, a[0].pow_u64(e))
            }
            // ACU ops never reach the free path (the seam pairs each op with the right SpecialOp arm).
            NumOp::Add | NumOp::Mul | NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max => {
                unreachable!("ACU number op `{op:?}` reached the free NumberOp path")
            }
        }
    }

    /// Read a string value from a `NodeTerm::Na::Str`, or `None` (not a string literal/result).
    fn as_str(&self, id: DagId) -> Option<Rc<str>> {
        match &self.node(id).term {
            NodeTerm::Na { value: NaValue::Str(s), .. } => Some(s.clone()),
            _ => None,
        }
    }

    /// `StringOpSymbol` (concat / length / substr / comparisons): operate on string `NodeTerm::Na`
    /// values, building a string (`str_sym`), a Nat (`nat`), or a Bool (`bool_`) result.
    fn reduce_string_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: StrOp,
        str_sym: SymbolId,
        nat: Option<&NatHooks>,
        bool_: Option<&BoolHooks>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        match op {
            StrOp::Concat => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                let r: Rc<str> = format!("{a}{b}").into();
                Some(self.make_na(sig, str_sym, NaValue::Str(r)))
            }
            StrOp::Length => {
                let len = self.as_str(kids[0])?.chars().count();
                self.make_int(sig, nat?, Int::from_nat(&Nat::from_u64(len as u64)))
            }
            StrOp::Substr => {
                let nat = nat?;
                let a = self.as_str(kids[0])?;
                let (start, len) = (self.as_int(kids[1], nat)?, self.as_int(kids[2], nat)?);
                if start.is_negative() || len.is_negative() {
                    return None;
                }
                let (start, len) = (start.magnitude().to_usize()?, len.magnitude().to_usize()?);
                let r: String = a.chars().skip(start).take(len).collect();
                Some(self.make_na(sig, str_sym, NaValue::Str(r.into())))
            }
            StrOp::Lt | StrOp::Le | StrOp::Gt | StrOp::Ge => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                let ord = a.as_ref().cmp(b.as_ref());
                let res = match op {
                    StrOp::Lt => ord.is_lt(),
                    StrOp::Le => ord.is_le(),
                    StrOp::Gt => ord.is_gt(),
                    StrOp::Ge => ord.is_ge(),
                    _ => unreachable!(),
                };
                let h = bool_?;
                Some(self.make_const(sig, if res { h.true_ } else { h.false_ }))
            }
        }
    }

    /// Read an `f64` from a `NodeTerm::Na::Float`, or `None`.
    fn as_float(&self, id: DagId) -> Option<f64> {
        match &self.node(id).term {
            NodeTerm::Na { value: NaValue::Float(bits), .. } => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }

    /// `FloatOpSymbol` (arithmetic / negation / abs / sqrt / comparisons): operate on `f64` values,
    /// building a float (`float_sym`) or a Bool (`bool_`) result via IEEE semantics.
    fn reduce_float_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: FltOp,
        float_sym: SymbolId,
        bool_: Option<&BoolHooks>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let a = self.as_float(kids[0])?;
        let make_f = |this: &mut Self, v: f64| this.make_na(sig, float_sym, NaValue::Float(v.to_bits()));
        match op {
            FltOp::Neg => Some(make_f(self, -a)),
            FltOp::Abs => Some(make_f(self, a.abs())),
            FltOp::Sqrt => Some(make_f(self, a.sqrt())),
            FltOp::Add | FltOp::Sub | FltOp::Mul | FltOp::Div => {
                let b = self.as_float(kids[1])?;
                let v = match op {
                    FltOp::Add => a + b,
                    FltOp::Sub => a - b,
                    FltOp::Mul => a * b,
                    FltOp::Div => a / b,
                    _ => unreachable!(),
                };
                Some(make_f(self, v))
            }
            FltOp::Lt | FltOp::Le | FltOp::Gt | FltOp::Ge => {
                let b = self.as_float(kids[1])?;
                let res = match op {
                    FltOp::Lt => a < b,
                    FltOp::Le => a <= b,
                    FltOp::Gt => a > b,
                    FltOp::Ge => a >= b,
                    _ => unreachable!(),
                };
                let h = bool_?;
                Some(self.make_const(sig, if res { h.true_ } else { h.false_ }))
            }
        }
    }
}

/// The first numeric operand `n` (multiplicity `m`) folded into a fresh accumulator.
fn acu_fold_first(op: NumOp, n: &Int, m: u32) -> Int {
    match op {
        NumOp::Add => n.mul(&Int::from_nat(&Nat::from_u64(u64::from(m)))), // n added m times
        NumOp::Mul => n.pow_u64(u64::from(m)),                            // n multiplied m times
        // gcd/lcm/min/max are idempotent in multiplicity; their operands are non-negative.
        NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max => Int::from_nat(&n.magnitude()),
        _ => unreachable!("non-ACU number op `{op:?}` in the ACU fold"),
    }
}

/// A subsequent numeric operand `n` (multiplicity `m`) combined with the accumulator `acc`.
fn acu_fold(op: NumOp, acc: &Int, n: &Int, m: u32) -> Int {
    match op {
        NumOp::Add => acc.add(&n.mul(&Int::from_nat(&Nat::from_u64(u64::from(m))))),
        NumOp::Mul => acc.mul(&n.pow_u64(u64::from(m))),
        // gcd/lcm work on magnitudes (non-negative operands); min/max via the `Int` order.
        NumOp::Gcd => Int::from_nat(&acc.magnitude().gcd(&n.magnitude())),
        NumOp::Lcm => Int::from_nat(&acc.magnitude().lcm(&n.magnitude())),
        NumOp::Min => core::cmp::min(acc.clone(), n.clone()),
        NumOp::Max => core::cmp::max(acc.clone(), n.clone()),
        _ => unreachable!("non-ACU number op `{op:?}` in the ACU fold"),
    }
}
