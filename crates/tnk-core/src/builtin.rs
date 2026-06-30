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
use crate::num;
use crate::symbol::{
    BoolHooks, CharClass, ConvOp, FltOp, NatHooks, NumOp, QidOp, SpecialOp, StrOp, SymbolId,
};
use std::rc::Rc;

impl Runtime {
    /// Reduce `id` by its operator's built-in rule, or `None` if the rule does not apply.
    pub(crate) fn try_special(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: &SpecialOp,
        descent: &mut dyn crate::descent::DescentOps,
    ) -> Option<DagId> {
        match op {
            SpecialOp::Equality { eq, neq } => self.reduce_equality(sig, id, *eq, *neq),
            SpecialOp::Branch { tests } => self.reduce_branch(id, tests),
            SpecialOp::AcuNumberOp { op, nat } => self.reduce_acu_number_op(sig, id, *op, nat),
            SpecialOp::NumberOp { op, nat, bool_ } => {
                self.reduce_number_op(sig, id, *op, nat, bool_.as_ref())
            }
            SpecialOp::CuiNumberOp { op, nat } => self.reduce_cui_number_op(sig, id, *op, nat),
            SpecialOp::Minus { nat } => self.reduce_minus(id, nat),
            SpecialOp::StringOp { op, str_sym, nat, bool_, not_found } => {
                self.reduce_string_op(sig, id, *op, *str_sym, nat.as_ref(), bool_.as_ref(), *not_found)
            }
            SpecialOp::FloatOp { op, float_sym, bool_ } => {
                self.reduce_float_op(sig, id, *op, *float_sym, bool_.as_ref())
            }
            SpecialOp::Random { nat } => self.reduce_random(sig, id, nat),
            SpecialOp::Conversion { op, float_sym, str_sym, nat, division, dec_float } => self
                .reduce_conversion(sig, id, *op, *float_sym, *str_sym, nat.as_ref(), *division, *dec_float),
            // `counter` is inert under equational reduction — it only advances under `rewrite`/`frewrite`
            // (see `try_counter`), so a `reduce` leaves it as the kind constant `[Nat]: counter`.
            SpecialOp::Counter { .. } => None,
            SpecialOp::QidOp { op, qid_sym, str_sym } => {
                self.reduce_qid_op(sig, id, *op, *qid_sym, *str_sym)
            }
            SpecialOp::Division { nat } => self.reduce_division(sig, id, nat),
            // META-LEVEL descent: down-translate the meta-term arguments, run the engine operation in the
            // object module, up-translate the result. The build pipeline + module database live above this
            // crate, so we call up through the `DescentOps` seam, handing it a `MetaCtx` view of this
            // engine (to read the redex and build the up-result). `None` ⇒ stays at the kind level.
            SpecialOp::Meta { op, hooks } => {
                let mut ctx = crate::descent::MetaCtx { rt: self, sig };
                descent.descend(&mut ctx, *op, hooks, id)
            }
            // A standard-stream manager constant (`stdin`/`stdout`/`stderr`) has no equational reduction —
            // it stands for itself. Its messages are handled by the `erewrite` EXTERNAL driver, not here.
            SpecialOp::StreamManager { .. } => None,
        }
    }

    /// `string : Qid -> String` / `qid : String ~> Qid` (Maude's `QuotedIdentifierOpSymbol`): convert
    /// between a quoted identifier (stored without its leading `'`) and its text. `qid` is partial — a
    /// string that is not a single identifier token (empty or containing whitespace) does not reduce.
    fn reduce_qid_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: QidOp,
        qid_sym: SymbolId,
        str_sym: SymbolId,
    ) -> Option<DagId> {
        let arg = self.node(id).children().next().expect("string/qid is unary");
        match op {
            QidOp::String => {
                let q = self.as_qid(arg)?;
                Some(self.make_na(sig, str_sym, NaValue::Str(q)))
            }
            QidOp::Qid => {
                // `qid` accepts any string (even empty or with spaces) — the raw text is stored and the
                // printer backquote-escapes special characters (`qid("a b")` prints as `'a`b`).
                let s = self.as_str(arg)?;
                Some(self.make_na(sig, qid_sym, NaValue::Qid(s)))
            }
        }
    }

    /// Read a rational from `id`: an integer numeral → `(i, 1)`, or a `_/_` node `I / N` → `(I, N)`.
    /// `None` if `id` is neither.
    fn as_rational(&self, id: DagId, nat: &NatHooks, division: Option<SymbolId>) -> Option<(Int, Nat)> {
        if let Some(i) = self.as_int(id, nat) {
            return Some((i, Nat::one()));
        }
        let div = division?;
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == div && args.len() == 2 => {
                Some((self.as_int(args[0], nat)?, self.as_nat(args[1], nat)?))
            }
            _ => None,
        }
    }

    /// Build the canonical rational `num / den` (already in lowest terms): the integer `num` when
    /// `den == 1`, else the `_/_` node.
    fn make_rational(
        &mut self,
        sig: &Signature,
        nat: &NatHooks,
        division: Option<SymbolId>,
        num: Int,
        den: Nat,
    ) -> Option<DagId> {
        if den == Nat::one() {
            return self.make_int(sig, nat, num);
        }
        let div = division?;
        let n = self.make_int(sig, nat, num)?;
        let d = self.make_int(sig, nat, Int::from_nat(&den))?;
        Some(self.make_free(sig, div, vec![n, d]))
    }

    /// The CONVERSION coercions (`float`/`rat`/`string`/`decFloat`). Each reads/builds the value types it
    /// bridges; a malformed argument (non-numeral, bad base/string, non-finite where exact) falls through.
    #[allow(clippy::too_many_arguments)]
    fn reduce_conversion(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: ConvOp,
        float_sym: Option<SymbolId>,
        str_sym: Option<SymbolId>,
        nat: Option<&NatHooks>,
        division: Option<SymbolId>,
        dec_float: Option<SymbolId>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        match op {
            // `float : Rat -> Float` — the nearest double to the rational.
            ConvOp::RatToFloat => {
                let (num, den) = self.as_rational(kids[0], nat?, division)?;
                let f = num::f64_of_rational(&num, &den);
                Some(self.make_na(sig, float_sym?, NaValue::Float(f.to_bits())))
            }
            // `rat : FiniteFloat -> Rat` — the exact rational of the double.
            ConvOp::FloatToRat => {
                let (num, den) = num::rational_of_f64(self.as_float(kids[0])?)?;
                self.make_rational(sig, nat?, division, num, den)
            }
            // `string : Rat NzNat -> String` — the rational in the given base (`I` or `I/N`).
            ConvOp::RatToString => {
                let nat = nat?;
                let (num, den) = self.as_rational(kids[0], nat, division)?;
                let base = conv_base(self.as_nat(kids[1], nat)?)?;
                let s = if den == Nat::one() {
                    num.to_string_base(base)
                } else {
                    format!("{}/{}", num.to_string_base(base), Int::from_nat(&den).to_string_base(base))
                };
                Some(self.make_na(sig, str_sym?, NaValue::Str(s.into())))
            }
            // `rat : String NzNat -> Rat` — a rational parsed from the base (`I` or `I/N`).
            ConvOp::StringToRat => {
                let nat = nat?;
                let s = self.as_str(kids[0])?;
                let base = conv_base(self.as_nat(kids[1], nat)?)?;
                let (num, den) = match s.split_once('/') {
                    Some((n, d)) => {
                        (Int::from_string_base(base, n)?, Int::from_string_base(base, d)?.magnitude())
                    }
                    None => (Int::from_string_base(base, &s)?, Nat::one()),
                };
                if den.is_zero() {
                    return None;
                }
                self.make_rational(sig, nat, division, num, den)
            }
            // `string : Float -> String` — the float's canonical decimal string (Maude's `doubleToString`).
            ConvOp::FloatToString => {
                let s = num::double_to_string(self.as_float(kids[0])?);
                Some(self.make_na(sig, str_sym?, NaValue::Str(s.into())))
            }
            // `float : String -> Float` — parse the string (partial: not every string is a float).
            ConvOp::StringToFloat => {
                let f = num::parse_double(&self.as_str(kids[0])?)?;
                Some(self.make_na(sig, float_sym?, NaValue::Float(f.to_bits())))
            }
            // `decFloat : Float Nat -> DecFloat` — decompose into `< sign, "digits", exp >` with the value
            // `sign · 0.digits · 10^exp` (precision 0 ⇒ the exact full expansion).
            ConvOp::DecFloat => {
                let nat = nat?;
                let f = self.as_float(kids[0])?;
                let prec = self.as_nat(kids[1], nat)?.to_usize()?;
                let (sign, digits, exp) = dec_float_parts(f, prec)?;
                let one = Int::from_nat(&Nat::one());
                let sign_val = match sign {
                    1 => one,
                    -1 => one.neg(),
                    _ => Int::from_nat(&Nat::zero()),
                };
                let exp_val = if exp < 0 {
                    Int::from_nat(&Nat::from_u64(exp.unsigned_abs())).neg()
                } else {
                    Int::from_nat(&Nat::from_u64(exp as u64))
                };
                let sign_dag = self.make_int(sig, nat, sign_val)?;
                let digits_dag = self.make_na(sig, str_sym?, NaValue::Str(digits.into()));
                let exp_dag = self.make_int(sig, nat, exp_val)?;
                Some(self.make_free(sig, dec_float?, vec![sign_dag, digits_dag, exp_dag]))
            }
        }
    }

    /// Fire a `counter` redex (Maude's `CounterSymbol`) at `node` during rewriting: if `node` is a
    /// counter op, yield the next natural and advance the counter, counting one rewrite. `None` if `node`
    /// is not a counter. Called from the `rewrite`/`frewrite` traversals — never from `reduce`.
    pub(crate) fn try_counter(&mut self, sig: &Signature, node: DagId) -> Option<DagId> {
        let symbol = self.node(node).symbol();
        let nat = match sig.symbol(symbol).special() {
            Some(SpecialOp::Counter { nat }) => *nat,
            _ => return None,
        };
        let v = self.counter_value;
        self.counter_value += 1;
        self.rewrite_count += 1;
        self.make_int(sig, &nat, Int::from_nat(&Nat::from_u64(v)))
    }

    /// Reset the `counter` built-in to 0 — called at the start of each top-level `rewrite`/`frewrite`
    /// command (not on `continue`, which resumes the running count).
    pub(crate) fn reset_counter(&mut self) {
        self.counter_value = 0;
    }

    /// `random : Nat -> Nat` (Maude's `RandomOpSymbol`): the n-th output of MT19937 seeded with 0. A
    /// non-numeral argument falls through.
    fn reduce_random(&mut self, sig: &Signature, id: DagId, nat: &NatHooks) -> Option<DagId> {
        let arg = self.node(id).children().next().expect("random is unary");
        let n = self.as_nat(arg, nat)?.to_u64()?;
        let r = mt19937_nth(n);
        self.make_int(sig, nat, Int::from_nat(&Nat::from_u64(u64::from(r))))
    }

    /// Read a quoted-identifier value from a `NodeTerm::Na::Qid` (the text without its `'`), or `None`.
    fn as_qid(&self, id: DagId) -> Option<Rc<str>> {
        match &self.node(id).term {
            NodeTerm::Na { value: NaValue::Qid(q), .. } => Some(q.clone()),
            _ => None,
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
            // `abs : Int -> Nat` — magnitude (always non-negative, so no `minus` hook needed).
            NumOp::Abs => self.make_int(sig, nat, Int::from_nat(&a[0].magnitude())),
            // `~_ : Int -> Int` — bitwise complement `~x = -(x+1)` (needs the INT `minus` hook).
            NumOp::BitNot => self.make_int(sig, nat, a[0].bitnot()),
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
            // `modExp(b, e, m) = b^e mod m` (`modExp : Nat Nat NzNat ~> Nat`): non-negative operands.
            NumOp::ModExp => {
                if a[2].is_zero() {
                    return None; // modulus 0 (the `NzNat` arg guards this; defend anyway)
                }
                let r = a[0].magnitude().mod_pow(&a[1].magnitude(), &a[2].magnitude());
                self.make_int(sig, nat, Int::from_nat(&r))
            }
            // `_>>_` / `_<<_ : Nat Nat -> Nat`: shift by a machine-width amount (a bignum shift count is
            // unrepresentable ⇒ fall through). Non-negative operands.
            NumOp::Shr | NumOp::Shl => {
                let amount = a[1].magnitude().to_u64()?;
                let base = a[0].magnitude();
                let r = if matches!(op, NumOp::Shr) { base.shr(amount) } else { base.shl(amount) };
                self.make_int(sig, nat, Int::from_nat(&r))
            }
            // ACU / CUI ops never reach the free path (the seam pairs each op with the right arm).
            NumOp::Add | NumOp::Mul | NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max
            | NumOp::Xor | NumOp::And | NumOp::Or | NumOp::Sd => {
                unreachable!("non-free number op `{op:?}` reached the free NumberOp path")
            }
        }
    }

    /// `CUI_NumberOpSymbol` (`sd`): a **commutative** 2-argument numeric op. `sd(m, n) = |m − n|` — read
    /// the two (already-reduced) operands from the CUI node and build the non-negative difference. A
    /// non-numeric argument falls through (`None`).
    fn reduce_cui_number_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: NumOp,
        nat: &NatHooks,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let a = self.as_int(kids[0], nat)?;
        let b = self.as_int(kids[1], nat)?;
        match op {
            NumOp::Sd => self.make_int(sig, nat, Int::from_nat(&a.sub(&b).magnitude())),
            _ => unreachable!("non-CUI number op `{op:?}` reached the CUI path"),
        }
    }

    /// Read a string value from a `NodeTerm::Na::Str`, or `None` (not a string literal/result).
    pub(crate) fn as_str(&self, id: DagId) -> Option<Rc<str>> {
        match &self.node(id).term {
            NodeTerm::Na { value: NaValue::Str(s), .. } => Some(s.clone()),
            _ => None,
        }
    }

    /// Read one line from the pending `stdin` buffer for `getLine` (Pillar 2.5-C): up to and **including**
    /// the next `\n` (the reference returns the newline), or the rest if there is no trailing `\n`, or `""`
    /// when the buffer is empty (EOF). Consumes what it returns from [`external_in`](crate::engine).
    pub(crate) fn read_line(&mut self) -> String {
        match self.external_in.find('\n') {
            Some(i) => self.external_in.drain(..=i).collect(),
            None => std::mem::take(&mut self.external_in),
        }
    }

    /// `StringOpSymbol` (concat / length / substr / comparisons): operate on string `NodeTerm::Na`
    /// values, building a string (`str_sym`), a Nat (`nat`), or a Bool (`bool_`) result.
    #[allow(clippy::too_many_arguments)]
    fn reduce_string_op(
        &mut self,
        sig: &Signature,
        id: DagId,
        op: StrOp,
        str_sym: SymbolId,
        nat: Option<&NatHooks>,
        bool_: Option<&BoolHooks>,
        not_found: Option<SymbolId>,
    ) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let make_str = |this: &mut Self, s: String| this.make_na(sig, str_sym, NaValue::Str(s.into()));
        match op {
            StrOp::Concat => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                Some(make_str(self, format!("{a}{b}")))
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
                Some(make_str(self, r))
            }
            // `ascii : Char -> Nat` — the code of a one-character string (else fall through). For an ASCII
            // char the scalar value equals Maude's byte value (the strings here are byte/ASCII-oriented).
            StrOp::Ascii => {
                let s = self.as_str(kids[0])?;
                let mut cs = s.chars();
                match (cs.next(), cs.next()) {
                    (Some(c), None) => {
                        self.make_int(sig, nat?, Int::from_nat(&Nat::from_u64(u32::from(c) as u64)))
                    }
                    _ => None, // not a single character
                }
            }
            // `char : Nat ~> Char` — the one-character string for a code (partial: a valid scalar value).
            StrOp::Char => {
                let n = self.as_int(kids[0], nat?)?;
                if n.is_negative() {
                    return None;
                }
                let code = u32::try_from(n.magnitude().to_u64()?).ok()?;
                let c = char::from_u32(code)?;
                Some(make_str(self, c.to_string()))
            }
            // `find` / `rfind : String String Nat -> FindResult` — C++ `std::string::find`/`rfind`
            // semantics over the byte sequence (≡ char index for ASCII): first/last occurrence of `pat`
            // starting at an index `>= start` (find) / `<= start` (rfind), else the `notFound` constant.
            StrOp::Find | StrOp::Rfind => {
                let nat = nat?;
                let (s, pat) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                let start = self.as_int(kids[2], nat)?;
                if start.is_negative() {
                    return None;
                }
                let start = start.magnitude().to_usize()?;
                let (hay, needle) = (s.as_bytes(), pat.as_bytes());
                let found = if matches!(op, StrOp::Find) {
                    byte_find(hay, needle, start)
                } else {
                    byte_rfind(hay, needle, start)
                };
                match found {
                    Some(idx) => self.make_int(sig, nat, Int::from_nat(&Nat::from_u64(idx as u64))),
                    None => Some(self.make_const(sig, not_found?)),
                }
            }
            // `upperCase` / `lowerCase` — ASCII case mapping (C `toupper`/`tolower`, byte-wise).
            StrOp::UpperCase => {
                let s = self.as_str(kids[0])?;
                Some(make_str(self, s.to_ascii_uppercase()))
            }
            StrOp::LowerCase => {
                let s = self.as_str(kids[0])?;
                Some(make_str(self, s.to_ascii_lowercase()))
            }
            // `isX : Char -> Bool` — the C `ctype` class of a single character (else fall through).
            StrOp::IsClass(class) => {
                let s = self.as_str(kids[0])?;
                let mut cs = s.chars();
                let c = match (cs.next(), cs.next()) {
                    (Some(c), None) => c,
                    _ => return None, // not a single character
                };
                let h = bool_?;
                Some(self.make_const(sig, if char_in_class(c, class) { h.true_ } else { h.false_ }))
            }
            // `startsWith` / `endsWith : String String -> Bool`.
            StrOp::StartsWith | StrOp::EndsWith => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                let res = if matches!(op, StrOp::StartsWith) {
                    a.starts_with(b.as_ref())
                } else {
                    a.ends_with(b.as_ref())
                };
                let h = bool_?;
                Some(self.make_const(sig, if res { h.true_ } else { h.false_ }))
            }
            // `trim` / `trimStart` / `trimEnd : String -> String` — strip C-whitespace.
            StrOp::Trim | StrOp::TrimStart | StrOp::TrimEnd => {
                let s = self.as_str(kids[0])?;
                let t = match op {
                    StrOp::TrimStart => s.trim_start_matches(is_c_space),
                    StrOp::TrimEnd => s.trim_end_matches(is_c_space),
                    _ => s.trim_matches(is_c_space),
                };
                Some(make_str(self, t.to_string()))
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
        // Comparisons → Bool.
        if matches!(op, FltOp::Lt | FltOp::Le | FltOp::Gt | FltOp::Ge) {
            let b = self.as_float(kids[1])?;
            let res = match op {
                FltOp::Lt => a < b,
                FltOp::Le => a <= b,
                FltOp::Gt => a > b,
                FltOp::Ge => a >= b,
                _ => unreachable!(),
            };
            let h = bool_?;
            return Some(self.make_const(sig, if res { h.true_ } else { h.false_ }));
        }
        // Arithmetic / functions → Float (IEEE `f64`, Maude's C `libm`).
        let v = match op {
            FltOp::Neg => -a,
            FltOp::Abs => a.abs(),
            FltOp::Sqrt => a.sqrt(),
            FltOp::Floor => a.floor(),
            FltOp::Ceiling => a.ceil(),
            FltOp::Exp => a.exp(),
            FltOp::Log => a.ln(),
            FltOp::Sin => a.sin(),
            FltOp::Cos => a.cos(),
            FltOp::Tan => a.tan(),
            FltOp::Asin => a.asin(),
            FltOp::Acos => a.acos(),
            FltOp::Atan => a.atan(),
            _ => {
                let b = self.as_float(kids[1])?;
                // `/`/`rem` by zero is **undefined** in Maude — it does not reduce, even though IEEE
                // would give ±inf (`1.0 / 0.0` stays `[Float]`, 0 rewrites).
                if matches!(op, FltOp::Div | FltOp::Rem) && b == 0.0 {
                    return None;
                }
                match op {
                    FltOp::Add => a + b,
                    FltOp::Sub => a - b,
                    FltOp::Mul => a * b,
                    FltOp::Div => a / b,
                    FltOp::Rem => a % b, // C `fmod` (remainder takes the dividend's sign)
                    FltOp::Pow => a.powf(b),
                    FltOp::Min => a.min(b),
                    FltOp::Max => a.max(b),
                    FltOp::Atan2 => a.atan2(b),
                    _ => unreachable!(),
                }
            }
        };
        // A partial op (`~>`) off its domain yields NaN, which does **not** reduce — `sqrt(-1.0)` /
        // `log(-1.0)` / `asin(2.0)` / an indeterminate `^` stay in the kind `[Float]`. (`log(0.0)` =
        // -inf is *not* NaN, so it reduces — matching the reference.) Total ops keep inf results.
        if v.is_nan() && matches!(op, FltOp::Sqrt | FltOp::Log | FltOp::Asin | FltOp::Acos | FltOp::Pow) {
            return None;
        }
        Some(make_f(self, v))
    }

    /// `_/_` (Maude's `DivisionSymbol`): canonicalise `I / N` to lowest terms. Divide both by
    /// `g = gcd(|I|, N)`: when the denominator becomes 1, reduce to the integer `I/g`; when `g > 1`,
    /// rebuild the reduced rational. An already-canonical `I/N` (`g == 1`, `N > 1`) or a zero numerator
    /// does not rewrite (`0/N` is the user equation `0/Q = 0`, not a kernel op).
    fn reduce_division(&mut self, sig: &Signature, id: DagId, nat: &NatHooks) -> Option<DagId> {
        let symbol = self.node(id).symbol();
        let kids: Vec<DagId> = self.node(id).children().collect();
        let num = self.as_int(kids[0], nat)?;
        let den = self.as_int(kids[1], nat)?;
        if num.is_zero() || den.is_zero() {
            return None; // 0/N (left to the user eq) or a malformed /0
        }
        let gcd = num.magnitude().gcd(&den.magnitude());
        let g = Int::from_nat(&gcd);
        let (new_num, new_den) = (num.div_rem(&g).0, den.div_rem(&g).0);
        if new_den.magnitude() == Nat::one() {
            return self.make_int(sig, nat, new_num); // denominator 1 → the integer
        }
        if gcd > Nat::one() {
            let (nn, dn) = (self.make_int(sig, nat, new_num)?, self.make_int(sig, nat, new_den)?);
            return Some(self.make_free(sig, symbol, vec![nn, dn]));
        }
        None // already in lowest terms
    }
}

/// Whether `c` is C-locale whitespace (`isspace`: space, tab, newline, CR, vertical tab, form feed) —
/// the trim ops' delimiter. Rust's `is_ascii_whitespace` omits the vertical tab, so spell it out.
fn is_c_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\u{0b}' | '\u{0c}')
}

/// Whether the character `c` is in the C `ctype` class `class` (STRING-OPS predicates), tested per byte in
/// the C locale: a non-ASCII char (byte > 127) is in no class, which the `is_ascii_*` checks give for free.
fn char_in_class(c: char, class: CharClass) -> bool {
    match class {
        CharClass::Control => c.is_ascii_control(),
        CharClass::Printable => c == ' ' || c.is_ascii_graphic(), // C `isprint`: graphic or space
        CharClass::Space => is_c_space(c),
        CharClass::Blank => c == ' ' || c == '\t',
        CharClass::Graphic => c.is_ascii_graphic(),
        CharClass::Punct => c.is_ascii_punctuation(),
        CharClass::Alnum => c.is_ascii_alphanumeric(),
        CharClass::Alpha => c.is_ascii_alphabetic(),
        CharClass::Upper => c.is_ascii_uppercase(),
        CharClass::Lower => c.is_ascii_lowercase(),
        CharClass::Digit => c.is_ascii_digit(),
        CharClass::XDigit => c.is_ascii_hexdigit(),
    }
}

/// A conversion base as a `u8` in 2..=36, or `None` (out of range / too large) — Maude's base argument.
fn conv_base(n: Nat) -> Option<u8> {
    u8::try_from(n.to_u64()?).ok().filter(|&b| (2..=36).contains(&b))
}

/// Decompose a float for `decFloat(f, prec)` into `(sign, digits, exp)` with value `sign · 0.digits ·
/// 10^exp` (Maude's `DecFloat`). `sign` is 1 / -1 / 0; `prec > 0` rounds to that many significant digits;
/// `prec == 0` gives the **exact** full decimal expansion (`|f| = num/2^k` ⇒ digits `num·5^k`, exp
/// `len − k`). `None` if the exact denominator exponent exceeds machine width (extreme subnormals).
fn dec_float_parts(f: f64, prec: usize) -> Option<(i32, String, i64)> {
    if f == 0.0 {
        return Some((0, "0".repeat(prec.max(1)), 0));
    }
    let sign = if f < 0.0 { -1 } else { 1 };
    let mag = f.abs();
    if prec == 0 {
        let (num, den) = num::rational_of_f64(mag)?;
        let k = i64::from(den.to_u64()?.trailing_zeros()); // den is a power of two, 2^k
        let five_k = Int::from_nat(&Nat::from_u64(5)).pow_u64(k as u64);
        let digits = num.mul(&five_k).magnitude().to_decimal();
        let exp = digits.len() as i64 - k;
        Some((sign, digits, exp))
    } else {
        // `{:.(prec-1)e}` writes `prec` significant digits as `D.DDDe±E` (or `De±E` for prec 1).
        let sci = format!("{:.*e}", prec - 1, mag);
        let (mantissa, exp_str) = sci.split_once('e')?;
        let digits: String = mantissa.chars().filter(|&c| c != '.').collect();
        Some((sign, digits, exp_str.parse::<i64>().ok()? + 1))
    }
}

/// The n-th 32-bit output (0-indexed) of MT19937 seeded with 0 — Maude's `random(n)`. The generator is
/// re-run from the seed each call (a pure function of `n`); conformance `n` is small. Standard MT19937
/// constants (Matsumoto–Nishimura); the seed init is the 2002 `init_genrand`.
fn mt19937_nth(n: u64) -> u32 {
    const N: usize = 624;
    const M: usize = 397;
    let mut mt = [0u32; N]; // mt[0] = seed = 0
    for i in 1..N {
        mt[i] = 1_812_433_253u32
            .wrapping_mul(mt[i - 1] ^ (mt[i - 1] >> 30))
            .wrapping_add(i as u32);
    }
    let mut idx = N; // force a twist before the first extraction
    let mut out = 0u32;
    for _ in 0..=n {
        if idx >= N {
            for i in 0..N {
                let y = (mt[i] & 0x8000_0000) | (mt[(i + 1) % N] & 0x7fff_ffff);
                mt[i] = mt[(i + M) % N] ^ (y >> 1) ^ if y & 1 != 0 { 0x9908_b0df } else { 0 };
            }
            idx = 0;
        }
        let mut y = mt[idx];
        idx += 1;
        y ^= y >> 11;
        y ^= (y << 7) & 0x9d2c_5680;
        y ^= (y << 15) & 0xefc6_0000;
        y ^= y >> 18;
        out = y;
    }
    out
}

/// First index `>= start` where `needle` occurs in `hay` (C++ `std::string::find`). An empty needle
/// matches at `start` (when in range); `npos` is `None`.
fn byte_find(hay: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    if needle.is_empty() {
        return (start <= hay.len()).then_some(start);
    }
    if needle.len() > hay.len() {
        return None;
    }
    (start..=hay.len() - needle.len()).find(|&i| &hay[i..i + needle.len()] == needle)
}

/// Last index `<= pos` where `needle` occurs in `hay` (C++ `std::string::rfind`). An empty needle matches
/// at `min(pos, len)`; `npos` is `None`.
fn byte_rfind(hay: &[u8], needle: &[u8], pos: usize) -> Option<usize> {
    if needle.is_empty() {
        return Some(pos.min(hay.len()));
    }
    let last = hay.len().checked_sub(needle.len())?;
    (0..=pos.min(last)).rev().find(|&i| &hay[i..i + needle.len()] == needle)
}

/// The first numeric operand `n` (multiplicity `m`) folded into a fresh accumulator.
fn acu_fold_first(op: NumOp, n: &Int, m: u32) -> Int {
    match op {
        NumOp::Add => n.mul(&Int::from_nat(&Nat::from_u64(u64::from(m)))), // n added m times
        NumOp::Mul => n.pow_u64(u64::from(m)),                            // n multiplied m times
        // gcd/lcm/min/max are idempotent in multiplicity; their operands are non-negative.
        NumOp::Gcd | NumOp::Lcm | NumOp::Min | NumOp::Max => Int::from_nat(&n.magnitude()),
        // Bitwise: `xor` cancels in pairs (even multiplicity ⇒ 0); `&`/`|` are idempotent (m ⩾ 1 ⇒ n).
        // The value is kept **signed** (INT folds over two's complement; NAT operands are non-negative).
        NumOp::Xor if m % 2 == 0 => Int::from_nat(&Nat::zero()),
        NumOp::Xor | NumOp::And | NumOp::Or => n.clone(),
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
        // Signed two's-complement bit folds; an even-multiplicity `xor` operand leaves `acc` unchanged.
        NumOp::Xor if m % 2 == 0 => acc.clone(),
        NumOp::Xor => acc.bitxor(n),
        NumOp::And => acc.bitand(n),
        NumOp::Or => acc.bitor(n),
        _ => unreachable!("non-ACU number op `{op:?}` in the ACU fold"),
    }
}
