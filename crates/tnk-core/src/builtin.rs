//! Built-in operator reduction (the `special (id-hook …)` seam, B3).
//!
//! [`Runtime::try_special`] is the `impl Runtime` arm that [`try_rewrite_top`](crate::engine) dispatches
//! a [`SpecialOp`] to — Maude's `eqRewrite`, tried *before* user equations and falling through (`None`)
//! on no-match. A successful return is exactly **one** rewrite: `try_special` never touches the rewrite
//! counter, so the existing `reduce` Phase-2 increment fires once when `try_rewrite_top` returns `Some`
//! (identical to a user-equation rewrite); the returned node is then re-reduced by the outer loop.

use crate::dag::{DagId, NaValue, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num;
use crate::num::{Int, Nat};
use crate::symbol::{
    BoolHooks, CharClass, ConvOp, FltOp, NatHooks, NumOp, QidOp, SpecialOp, StrOp, SymbolClass,
    SymbolId,
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
            SpecialOp::DecomposeEquality {
                eq,
                neq,
                conj,
                disj,
                siblings,
            } => self.reduce_decompose_equality(sig, id, *eq, *neq, *conj, *disj, siblings),
            SpecialOp::Branch { tests } => self.reduce_branch(id, tests),
            SpecialOp::AcuNumberOp { op, nat } => self.reduce_acu_number_op(sig, id, *op, nat),
            SpecialOp::NumberOp { op, nat, bool_ } => {
                self.reduce_number_op(sig, id, *op, nat, bool_.as_ref())
            }
            SpecialOp::CuiNumberOp { op, nat } => self.reduce_cui_number_op(sig, id, *op, nat),
            SpecialOp::Minus { nat } => self.reduce_minus(id, nat),
            SpecialOp::StringOp {
                op,
                str_sym,
                nat,
                bool_,
                not_found,
            } => self.reduce_string_op(
                sig,
                id,
                *op,
                *str_sym,
                nat.as_ref(),
                bool_.as_ref(),
                *not_found,
            ),
            SpecialOp::FloatOp {
                op,
                float_sym,
                bool_,
            } => self.reduce_float_op(sig, id, *op, *float_sym, bool_.as_ref()),
            SpecialOp::Random { nat } => self.reduce_random(sig, id, nat),
            SpecialOp::Conversion {
                op,
                float_sym,
                str_sym,
                nat,
                division,
                dec_float,
            } => self.reduce_conversion(
                sig,
                id,
                *op,
                *float_sym,
                *str_sym,
                nat.as_ref(),
                *division,
                *dec_float,
            ),
            // `counter` is inert under equational reduction — it only advances under `rewrite`/`frewrite`
            // (see `try_counter`), so a `reduce` leaves it as the kind constant `[Nat]: counter`.
            SpecialOp::Counter { .. } => None,
            SpecialOp::ModelCheck { hooks } => {
                crate::ltl::model_check::check_rewrite_system(self, sig, descent, id, hooks)
            }
            SpecialOp::SatSolve { hooks } => crate::ltl::sat_solve::solve(self, sig, id, hooks),
            // T1 recognizes solver-language operators but deliberately leaves them inert. T2 translates
            // these typed hooks into the selected `SmtEngine`; ordinary `reduce` must not evaluate them.
            SpecialOp::Smt { .. } => None,
            SpecialOp::QidOp {
                op,
                qid_sym,
                str_sym,
            } => self.reduce_qid_op(sig, id, *op, *qid_sym, *str_sym),
            SpecialOp::Division { nat } => self.reduce_division(sig, id, nat),
            // META-LEVEL descent: down-translate the meta-term arguments, run the engine operation in the
            // object module, up-translate the result. The build pipeline + module database live above this
            // crate, so we call up through the `DescentOps` seam, handing it a `MetaCtx` view of this
            // engine (to read the redex and build the up-result). `None` ⇒ stays at the kind level.
            SpecialOp::Meta { op, hooks } => {
                let mut ctx = crate::descent::MetaCtx { rt: self, sig };
                descent.descend(&mut ctx, *op, hooks, id)
            }
            // External target constants have no equational reduction. Their messages are handled by the
            // resumable `erewrite` scheduler, not by ordinary reduction.
            SpecialOp::StreamManager { .. } | SpecialOp::InterpreterManager => None,
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
        let arg = self
            .node(id)
            .children()
            .next()
            .expect("string/qid is unary");
        match op {
            QidOp::String => {
                // The qid's canonical text (already valid UTF-8) as the string's raw bytes.
                let q = self.as_qid(arg)?;
                Some(self.make_na(sig, str_sym, NaValue::Str(q.as_bytes().into())))
            }
            QidOp::Qid => {
                // `qid` normalizes the string to Maude's canonical token name at construction
                // (Token::ropeToPrefixNameCode): whitespace/backquote runs become one backquote,
                // specials get a preceding backquote. So `qid("a b")` and `qid("a`b")` build the
                // SAME node ("a`b"), `string` returns the canonical text, and the printer is verbatim.
                // A qid is text: a non-UTF-8 byte string is not a valid identifier, so it falls through.
                let s = self.as_str(arg)?;
                let canonical = normalize_qid_name(std::str::from_utf8(&s).ok()?);
                Some(self.make_na(sig, qid_sym, NaValue::Qid(canonical.into())))
            }
        }
    }

    /// Read a rational from `id`: an integer numeral → `(i, 1)`, or a `_/_` node `I / N` → `(I, N)`.
    /// `None` if `id` is neither.
    fn as_rational(
        &self,
        id: DagId,
        nat: &NatHooks,
        division: Option<SymbolId>,
    ) -> Option<(Int, Nat)> {
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
                    format!(
                        "{}/{}",
                        num.to_string_base(base),
                        Int::from_nat(&den).to_string_base(base)
                    )
                };
                Some(self.make_na(sig, str_sym?, NaValue::Str(s.into_bytes().into())))
            }
            // `rat : String NzNat -> Rat` — a rational parsed from the base (`I` or `I/N`).
            ConvOp::StringToRat => {
                let nat = nat?;
                let s = self.as_str(kids[0])?;
                let s = std::str::from_utf8(&s).ok()?; // non-UTF-8 bytes are not a numeral ⇒ fall through
                let base = conv_base(self.as_nat(kids[1], nat)?)?;
                let (num, den) = match s.split_once('/') {
                    Some((n, d)) => (
                        Int::from_string_base(base, n)?,
                        Int::from_string_base(base, d)?.magnitude(),
                    ),
                    None => (Int::from_string_base(base, s)?, Nat::one()),
                };
                if den.is_zero() {
                    return None;
                }
                self.make_rational(sig, nat, division, num, den)
            }
            // `string : Float -> String` — the float's canonical decimal string (Maude's `doubleToString`).
            ConvOp::FloatToString => {
                let s = num::double_to_string(self.as_float(kids[0])?);
                Some(self.make_na(sig, str_sym?, NaValue::Str(s.into_bytes().into())))
            }
            // `float : String -> Float` — parse the string (partial: not every string is a float).
            ConvOp::StringToFloat => {
                let s = self.as_str(kids[0])?;
                let f = num::parse_double(std::str::from_utf8(&s).ok()?)?;
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
                let digits_dag =
                    self.make_na(sig, str_sym?, NaValue::Str(digits.into_bytes().into()));
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
            NodeTerm::Na {
                value: NaValue::Qid(q),
                ..
            } => Some(q.clone()),
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
            (
                kids.next().expect("_==_ is binary"),
                kids.next().expect("_==_ is binary"),
            )
        };
        // Floats compare by IEEE value, not bit pattern: `- 0.0 == 0.0` is true (Maude's
        // FloatDagNode compares the doubles; NaN never occurs — the float ops gate it out).
        let equal = match (self.as_float(l), self.as_float(r)) {
            (Some(a), Some(b)) => a == b,
            _ => self.deep_equal(l, r),
        };
        let chosen = if equal { eq } else { neq };
        Some(self.make_const(sig, chosen))
    }

    /// `_.=._` (Maude's `CommutativeDecomposeEqualitySymbol`,
    /// `src/Mixfix/commutativeDecomposeEqualitySymbol.cc` ported line-for-line): the initial-model
    /// equality predicate. Equal reduced dags → `true`; unequal ground dags → `false`; otherwise
    /// decompose over equationally-stable tops (free / iter / comm / assoc / AC) or decide `false`
    /// where tops provably differ; `None` (stay unreduced, user equations may apply) when nothing is
    /// provable — e.g. `X .=. Y` for distinct variables.
    #[allow(clippy::too_many_arguments)]
    fn reduce_decompose_equality(
        &mut self,
        sig: &Signature,
        id: DagId,
        eq: SymbolId,
        neq: SymbolId,
        conj: Option<SymbolId>,
        disj: Option<SymbolId>,
        siblings: &Rc<[Option<SymbolId>]>,
    ) -> Option<DagId> {
        let (l, r) = {
            let mut kids = self.node(id).children();
            (
                kids.next().expect("_.=._ is binary"),
                kids.next().expect("_.=._ is binary"),
            )
        };
        // Equal dags are always equal (arguments arrive reduced — standard strategy).
        if self.deep_equal(l, r) {
            return Some(self.make_const(sig, eq));
        }
        // Unequal ground dags are always unequal.
        if self.dag_is_ground(sig, l) && self.dag_is_ground(sig, r) {
            return Some(self.make_const(sig, neq));
        }
        let ls = self.node(l).symbol();
        let rs = self.node(r).symbol();
        if equationally_stable(sig, ls) {
            // Left top symbol cannot change under instantiation and equational rewriting.
            if self.has_immediate_subterm(l, r) {
                return Some(self.make_const(sig, neq)); // occurs-style check
            }
            if ls == rs {
                if let Some(d) = self.decompose(sig, id, l, r, neq, conj, disj, siblings) {
                    return Some(d);
                }
            } else if equationally_stable(sig, rs) || self.dag_is_ground(sig, r) {
                return Some(self.make_const(sig, neq));
            }
        } else if equationally_stable(sig, rs) {
            // Converse case: rs is inert and either l is ground or r has an immediate subterm l.
            if self.dag_is_ground(sig, l) || self.has_immediate_subterm(r, l) {
                return Some(self.make_const(sig, neq));
            }
        }
        None
    }

    /// Whether `id` contains no variable anywhere (Maude's `determineGround`, uncached — `.=.`
    /// subjects are small). tnk realizes command-subject variables as [`SymbolClass::Variable`]
    /// constants, so groundness is a class walk; a genuine `Var` leaf (symbolic-engine DAGs) is
    /// likewise caught via its `SortVariable`-classed symbol.
    fn dag_is_ground(&self, sig: &Signature, id: DagId) -> bool {
        if matches!(
            sig.symbol(self.node(id).symbol()).class,
            SymbolClass::Variable { .. } | SymbolClass::SortVariable
        ) {
            return false;
        }
        self.node(id).children().all(|c| self.dag_is_ground(sig, c))
    }

    /// Whether some immediate argument of `bigger` equals `smaller`.
    fn has_immediate_subterm(&self, bigger: DagId, smaller: DagId) -> bool {
        self.node(bigger)
            .children()
            .any(|c| self.deep_equal(c, smaller))
    }

    /// The `.=.` polymorph instance for the kind of `sort` (Maude's
    /// `instantiatePolymorph(polymorphIndex, kindIndex)`; tnk's per-kind eager expansion makes it a
    /// table lookup).
    fn dec_sibling(
        &self,
        sig: &Signature,
        siblings: &Rc<[Option<SymbolId>]>,
        sort: crate::sort::SortId,
    ) -> Option<SymbolId> {
        siblings
            .get(sig.sorts().kind_of(sort).index())
            .copied()
            .flatten()
    }

    /// Build one decomposed `.=.` pair, sharing the node with any content-equal pair already built
    /// in this decomposition. Maude gets this sharing from compare-based ACU normalization; tnk's
    /// `make_acu` merges distinct nodes only once both are reduced, and a fresh pair that reduces to
    /// itself never triggers the parent's re-canonicalization — so without this, `f(X,Y) .=. f(Y,X)`
    /// would decompose to an `_and_` whose two structurally-equal arguments stay unmerged and the
    /// prelude's idempotence equation cannot match.
    fn make_dec_pair(
        &mut self,
        sig: &Signature,
        sym: SymbolId,
        x: DagId,
        y: DagId,
        seen: &mut Vec<DagId>,
    ) -> DagId {
        let p = self.make_cui(sig, sym, x, y);
        if let Some(&prev) = seen.iter().find(|&&q| q != p && self.deep_equal(q, p)) {
            return prev;
        }
        seen.push(p);
        p
    }

    /// The theory-decomposition arms of `CommutativeDecomposeEqualitySymbol::decompose`. `None` =
    /// no decomposition possible (stay unreduced). Both tops are `ls == rs` and equationally stable
    /// (hence: no identity element — the AU/ACU/CUI arms only ever see pure assoc / pure AC / pure
    /// comm(+idem) nodes).
    fn decompose(
        &mut self,
        sig: &Signature,
        subject: DagId,
        l: DagId,
        r: DagId,
        neq: SymbolId,
        conj: Option<SymbolId>,
        disj: Option<SymbolId>,
        siblings: &Rc<[Option<SymbolId>]>,
    ) -> Option<DagId> {
        let subject_sym = self.node(subject).symbol();
        let mut seen: Vec<DagId> = Vec::new();
        let (lterm, rterm) = (self.node(l).term.clone(), self.node(r).term.clone());
        match (&lterm, &rterm) {
            // Free theory: decompose into a conjunction of per-argument `.=.` problems.
            (NodeTerm::Free { symbol, args: la }, NodeTerm::Free { args: ra, .. }) => {
                let arity = la.len();
                if arity == 0 || (arity > 1 && conj.is_none()) {
                    return None;
                }
                let domain = sig.symbol(*symbol).decls[0].domain.clone();
                let mut subterms = Vec::with_capacity(arity);
                for i in 0..arity {
                    let sibling = self.dec_sibling(sig, siblings, domain[i])?;
                    subterms.push(self.make_dec_pair(sig, sibling, la[i], ra[i], &mut seen));
                }
                Some(if arity == 1 {
                    subterms[0]
                } else {
                    self.make_acu(
                        sig,
                        conj.unwrap(),
                        subterms.into_iter().map(|s| (s, 1)).collect(),
                    )
                })
            }
            // Iter theory: peel the common successor count; domain kind == range kind, so the
            // subject's own instance is the sibling.
            (
                NodeTerm::S {
                    symbol,
                    count: lc,
                    arg: la,
                },
                NodeTerm::S {
                    count: rc, arg: ra, ..
                },
            ) => {
                let (x, y) = if lc > rc {
                    let d = lc.checked_sub(rc).expect("lc > rc");
                    (self.make_s(sig, *symbol, d, *la), *ra)
                } else if lc < rc {
                    let d = rc.checked_sub(lc).expect("rc > lc");
                    let shrunk = self.make_s(sig, *symbol, d, *ra);
                    (*la, shrunk)
                } else {
                    (*la, *ra)
                };
                Some(self.make_cui(sig, subject_sym, x, y))
            }
            // Commutative (CUI) theory: four single-pair cases, else a disjunction of the two
            // pairings.
            (NodeTerm::Cui { symbol, args: la }, NodeTerm::Cui { args: ra, .. }) => {
                let sibling =
                    self.dec_sibling(sig, siblings, sig.symbol(*symbol).decls[0].domain[0])?;
                let (l0, l1, r0, r1) = (la[0], la[1], ra[0], ra[1]);
                for (a, b, c, d) in [
                    (l0, r0, l1, r1),
                    (l1, r1, l0, r0),
                    (l0, r1, l1, r0),
                    (l1, r0, l0, r1),
                ] {
                    if self.deep_equal(a, b) {
                        return Some(self.make_cui(sig, sibling, c, d));
                    }
                }
                let (conj, disj) = (conj?, disj?);
                let p00 = self.make_dec_pair(sig, sibling, l0, r0, &mut seen);
                let p11 = self.make_dec_pair(sig, sibling, l1, r1, &mut seen);
                let and1 = self.make_acu(sig, conj, vec![(p00, 1), (p11, 1)]);
                let p01 = self.make_dec_pair(sig, sibling, l0, r1, &mut seen);
                let p10 = self.make_dec_pair(sig, sibling, l1, r0, &mut seen);
                let and2 = self.make_acu(sig, conj, vec![(p01, 1), (p10, 1)]);
                Some(self.make_acu(sig, disj, vec![(and1, 1), (and2, 1)]))
            }
            (NodeTerm::Au { symbol, args: la }, NodeTerm::Au { args: ra, .. }) => self
                .associative_decompose(
                    sig,
                    *symbol,
                    la.clone(),
                    ra.clone(),
                    subject_sym,
                    neq,
                    conj,
                ),
            (NodeTerm::Acu { symbol, args: la }, NodeTerm::Acu { args: ra, .. }) => {
                self.ac_decompose(sig, *symbol, la.clone(), ra.clone(), subject_sym, neq)
            }
            _ => None,
        }
    }

    /// AU (pure assoc) arm: peel provably-pairable arguments from both ends, prove inequality where
    /// the peel exposes it, and decompose the peels + remainder into a conjunction. Port of
    /// `associativeDecompose` (the peel loops bound by the shorter side — the C++ `maxEnd` read past
    /// the shorter vector is unreachable-by-construction there and plain-bounded here).
    fn associative_decompose(
        &mut self,
        sig: &Signature,
        f: SymbolId,
        left_args: Vec<DagId>,
        right_args: Vec<DagId>,
        subject_sym: SymbolId,
        neq: SymbolId,
        conj: Option<SymbolId>,
    ) -> Option<DagId> {
        let mut left_peels: Vec<DagId> = Vec::new();
        let mut right_peels: Vec<DagId> = Vec::new();
        let min_end = left_args.len().min(right_args.len());

        // Can this (leftArg, rightArg) position peel? Ok(true) = peel, Ok(false) = stop peeling,
        // Err(()) = whole equality is provably false.
        let try_pair = |rt: &mut Self, la: DagId, ra: DagId| -> Result<bool, ()> {
            if rt.deep_equal(la, ra) {
                return Ok(true); // equal arguments peel silently
            }
            let (ls, rs) = (rt.node(la).symbol(), rt.node(ra).symbol());
            if rt.dag_is_ground(sig, la) {
                if rt.dag_is_ground(sig, ra) {
                    return Err(()); // unequal ground terms decompose to false
                }
                if !equationally_stable(sig, rs) {
                    return Ok(false);
                }
            } else {
                if !equationally_stable(sig, ls) {
                    return Ok(false);
                }
                if !(equationally_stable(sig, rs) || rt.dag_is_ground(sig, ra)) {
                    return Ok(false);
                }
            }
            if ls != rs {
                return Err(()); // stable-or-ground tops that differ decompose to false
            }
            Ok(true)
        };

        // Peel from the start.
        let mut start_marker = 0usize;
        while start_marker < min_end {
            let (la, ra) = (left_args[start_marker], right_args[start_marker]);
            match try_pair(self, la, ra) {
                Err(()) => return Some(self.make_const(sig, neq)),
                Ok(false) => break,
                Ok(true) => {
                    if !self.deep_equal(la, ra) {
                        left_peels.push(la);
                        right_peels.push(ra);
                    }
                    start_marker += 1;
                }
            }
        }
        // Peel from the end.
        let mut left_end = left_args.len();
        let mut right_end = right_args.len();
        while left_end > start_marker && right_end > start_marker {
            let (la, ra) = (left_args[left_end - 1], right_args[right_end - 1]);
            match try_pair(self, la, ra) {
                Err(()) => return Some(self.make_const(sig, neq)),
                Ok(false) => break,
                Ok(true) => {
                    if !self.deep_equal(la, ra) {
                        left_peels.push(la);
                        right_peels.push(ra);
                    }
                    left_end -= 1;
                    right_end -= 1;
                }
            }
        }

        let left_remaining = left_end - start_marker;
        let right_remaining = right_end - start_marker;
        if (left_remaining == 0) != (right_remaining == 0) {
            return Some(self.make_const(sig, neq));
        }
        // Try to prove the remainders unequal via the multiset (commutative-relaxation) argument.
        let mut left_ms = self.make_multiset(&left_args[start_marker..left_end]);
        let mut right_ms = self.make_multiset(&right_args[start_marker..right_end]);
        if self.ac_provably_unequal(sig, &mut left_ms, &mut right_ms) {
            return Some(self.make_const(sig, neq));
        }
        if left_remaining == left_args.len() {
            return None; // no progress — bail to avoid rebuilding the subject forever
        }
        // Build the decomposition: one `.=.` per peel pair, plus the remainders re-wrapped.
        let arity = left_peels.len() + usize::from(left_remaining != 0);
        debug_assert!(arity != 0, "0 arity from peeling unequal assoc terms");
        if arity > 1 && conj.is_none() {
            return None;
        }
        let mut seen: Vec<DagId> = Vec::new();
        let mut and_args = Vec::with_capacity(arity);
        for (la, ra) in left_peels.iter().zip(&right_peels) {
            let p = self.make_dec_pair(sig, subject_sym, *la, *ra, &mut seen);
            and_args.push(p);
        }
        if left_remaining != 0 {
            let lrest = if left_remaining == 1 {
                left_args[start_marker]
            } else {
                self.make_au(sig, f, left_args[start_marker..left_end].to_vec())
            };
            let rrest = if right_remaining == 1 {
                right_args[start_marker]
            } else {
                self.make_au(sig, f, right_args[start_marker..right_end].to_vec())
            };
            let p = self.make_dec_pair(sig, subject_sym, lrest, rrest, &mut seen);
            and_args.push(p);
        }
        Some(if arity == 1 {
            and_args[0]
        } else {
            self.make_acu(
                sig,
                conj.unwrap(),
                and_args.into_iter().map(|a| (a, 1)).collect(),
            )
        })
    }

    /// ACU (pure AC) arm: cancel common subterms between the argument multisets; prove inequality
    /// by the stable-or-ground cardinality/pairing arguments; if cancellation made progress,
    /// decompose to a smaller `.=.`. Port of `acDecompose`.
    fn ac_decompose(
        &mut self,
        sig: &Signature,
        f: SymbolId,
        left_args: Vec<(DagId, u32)>,
        right_args: Vec<(DagId, u32)>,
        subject_sym: SymbolId,
        neq: SymbolId,
    ) -> Option<DagId> {
        let nr_left: u64 = left_args.iter().map(|&(_, m)| u64::from(m)).sum();
        let mut left_ms = left_args;
        let mut right_ms = right_args;
        if self.ac_provably_unequal(sig, &mut left_ms, &mut right_ms) {
            return Some(self.make_const(sig, neq));
        }
        let left_remaining: u64 = left_ms.iter().map(|&(_, m)| u64::from(m)).sum();
        if left_remaining < nr_left {
            // Cancellation happened: decompose to the smaller problem.
            let lrest = self.rebuild_ac(sig, f, left_ms);
            let rrest = self.rebuild_ac(sig, f, right_ms);
            return Some(self.make_cui(sig, subject_sym, lrest, rrest));
        }
        None
    }

    /// Collect a slice of arguments into a multiset (merging `deep_equal` duplicates).
    fn make_multiset(&self, args: &[DagId]) -> Vec<(DagId, u32)> {
        let mut ms: Vec<(DagId, u32)> = Vec::with_capacity(args.len());
        for &a in args {
            match ms.iter_mut().find(|(d, _)| self.deep_equal(*d, a)) {
                Some((_, m)) => *m += 1,
                None => ms.push((a, 1)),
            }
        }
        ms
    }

    /// Re-wrap a (non-empty) canceled multiset: a single occurrence is the element itself, more
    /// re-form the AC node.
    fn rebuild_ac(&mut self, sig: &Signature, f: SymbolId, ms: Vec<(DagId, u32)>) -> DagId {
        let total: u64 = ms.iter().map(|&(_, m)| u64::from(m)).sum();
        debug_assert!(total >= 1, "empty multiset after unequal-cancel");
        if total == 1 {
            ms[0].0
        } else {
            self.make_acu(sig, f, ms)
        }
    }

    /// Port of `acProvablyUnequal`: try to prove two argument multisets can never be made equal
    /// under substitution, axioms, and equational rewriting. As a side effect, cancels common
    /// subterms from both multisets (kept by the caller for the decompose-on-progress path).
    fn ac_provably_unequal(
        &self,
        sig: &Signature,
        left: &mut Vec<(DagId, u32)>,
        right: &mut Vec<(DagId, u32)>,
    ) -> bool {
        // Cancel equal subterms (min multiplicity) from each side. Elements within one canonical
        // multiset are pairwise distinct, so at most one partner exists.
        for i in 0..left.len() {
            let ld = left[i].0;
            for (rd, rm) in right.iter_mut() {
                if *rm > 0 && self.deep_equal(ld, *rd) {
                    let common = left[i].1.min(*rm);
                    left[i].1 -= common;
                    *rm -= common;
                    break;
                }
            }
        }
        left.retain(|&(_, m)| m > 0);
        right.retain(|&(_, m)| m > 0);
        if left.is_empty() {
            return !right.is_empty();
        }
        if right.is_empty() {
            return true;
        }
        // Both sides non-empty. If one side is all stable-or-ground, a cardinality or top-symbol
        // pairing argument may prove inequality.
        let count = |ms: &Vec<(DagId, u32)>| ms.iter().map(|&(_, m)| u64::from(m)).sum::<u64>();
        let stable_or_ground = |rt: &Self, ms: &Vec<(DagId, u32)>| {
            ms.iter().all(|&(d, _)| {
                equationally_stable(sig, rt.node(d).symbol()) || rt.dag_is_ground(sig, d)
            })
        };
        let mut swap = false;
        let mut try_pairing = false;
        if stable_or_ground(self, right) {
            if count(left) > count(right) {
                return true; // proof by cardinality
            }
            swap = true;
            try_pairing = true;
        }
        if stable_or_ground(self, left) {
            if count(left) < count(right) {
                return true; // proof by cardinality
            }
            swap = false;
            try_pairing = true;
        }
        if try_pairing {
            let (constrained, other): (&Vec<_>, &Vec<_>) =
                if swap { (right, left) } else { (left, right) };
            // `constrained` holds only subterms whose top symbol is fixed; every stable-or-ground
            // subterm of `other` must pair with a same-top subterm of `constrained`, else unequal.
            let mut budget: Vec<(SymbolId, u64)> = Vec::new();
            for &(d, m) in constrained {
                let s = self.node(d).symbol();
                match budget.iter_mut().find(|(bs, _)| *bs == s) {
                    Some((_, n)) => *n += u64::from(m),
                    None => budget.push((s, u64::from(m))),
                }
            }
            for &(d, m) in other {
                let s = self.node(d).symbol();
                if equationally_stable(sig, s) || self.dag_is_ground(sig, d) {
                    match budget.iter_mut().find(|(bs, _)| *bs == s) {
                        Some((_, n)) if *n >= u64::from(m) => *n -= u64::from(m),
                        _ => return true, // nothing left it could equal
                    }
                }
            }
        }
        false
    }

    /// `if_then_else_fi` (Maude's `BranchSymbol`) selector: with the condition already reduced by the
    /// intrinsic strategy, return the branch matching a hooked `tests` constant. The outer reduce loop
    /// then abandons the old frame and normalizes only that selected result. If no test matches, this
    /// returns `None`; BranchSymbol's strategy continues through every branch before its final
    /// user-equation attempt.
    fn reduce_branch(&self, id: DagId, tests: &[SymbolId]) -> Option<DagId> {
        let kids: Vec<DagId> = self.node(id).children().collect();
        let cond_sym = self.node(kids[0]).symbol();
        tests
            .iter()
            .position(|&t| t == cond_sym)
            .map(|i| kids[i + 1])
    }

    /// The magnitude of a non-negative numeral at `id` — the `zero` constant (`0`) or `s^count(0)` — or
    /// `None` if `id` is not such a numeral. (`as_int` builds on this; `divides` works on magnitudes.)
    fn as_nat(&self, id: DagId, nat: &NatHooks) -> Option<Nat> {
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == nat.zero && args.is_empty() => {
                Some(Nat::zero())
            }
            NodeTerm::S { symbol, count, arg } if *symbol == nat.succ => {
                match &self.node(*arg).term {
                    NodeTerm::Free { symbol: b, args } if *b == nat.zero && args.is_empty() => {
                        Some(count.clone())
                    }
                    _ => None, // s^count(non-zero) is not a ground numeral
                }
            }
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
                    // A zero divisor is off the `NzNat` domain: `0 divides n` stays at `[Bool]`.
                    NumOp::Divides => {
                        if a[0].is_zero() {
                            return None;
                        }
                        a[0].magnitude().divides(&a[1].magnitude())
                    }
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
                let r = a[0]
                    .magnitude()
                    .mod_pow(&a[1].magnitude(), &a[2].magnitude());
                self.make_int(sig, nat, Int::from_nat(&r))
            }
            // `_>>_` / `_<<_ : Int Nat -> Int`: arithmetic shifts on the signed value (`>>` floors toward
            // −∞ — `-8 >> 1 = -4`, `-1 >> 100 = -1`; `-5 << 2 = -20`). Shift count is a machine `u64`
            // (a bignum count is unrepresentable ⇒ fall through).
            NumOp::Shr | NumOp::Shl => {
                let amount = a[1].magnitude().to_u64()?;
                let r = if matches!(op, NumOp::Shr) {
                    a[0].shr(amount)
                } else {
                    a[0].shl(amount)
                };
                self.make_int(sig, nat, r)
            }
            // ACU / CUI ops never reach the free path (the seam pairs each op with the right arm).
            NumOp::Add
            | NumOp::Mul
            | NumOp::Gcd
            | NumOp::Lcm
            | NumOp::Min
            | NumOp::Max
            | NumOp::Xor
            | NumOp::And
            | NumOp::Or
            | NumOp::Sd => {
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

    /// Read a string value (raw bytes) from a `NodeTerm::Na::Str`, or `None` (not a string literal/result).
    pub(crate) fn as_str(&self, id: DagId) -> Option<Rc<[u8]>> {
        match &self.node(id).term {
            NodeTerm::Na {
                value: NaValue::Str(s),
                ..
            } => Some(s.clone()),
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
        let make_str =
            |this: &mut Self, s: Vec<u8>| this.make_na(sig, str_sym, NaValue::Str(s.into()));
        match op {
            StrOp::Concat => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                let mut v = a.to_vec();
                v.extend_from_slice(&b);
                Some(make_str(self, v))
            }
            // `length : String -> Nat` — the **byte** count (Maude's Rope length).
            StrOp::Length => {
                let len = self.as_str(kids[0])?.len();
                self.make_int(sig, nat?, Int::from_nat(&Nat::from_u64(len as u64)))
            }
            // `substr : String Nat Nat -> String` — a **byte** slice with skip/take clamping (start beyond
            // the end ⇒ empty; overlong length ⇒ truncated), exactly like the char form but over bytes.
            StrOp::Substr => {
                let nat = nat?;
                let a = self.as_str(kids[0])?;
                let (start, len) = (self.as_int(kids[1], nat)?, self.as_int(kids[2], nat)?);
                if start.is_negative() || len.is_negative() {
                    return None;
                }
                let (start, len) = (start.magnitude().to_usize()?, len.magnitude().to_usize()?);
                let r: Vec<u8> = a.iter().copied().skip(start).take(len).collect();
                Some(make_str(self, r))
            }
            // `ascii : Char -> Nat` — the byte value of a one-**byte** string (else fall through).
            StrOp::Ascii => {
                let s = self.as_str(kids[0])?;
                match s.as_ref() {
                    [b] => self.make_int(sig, nat?, Int::from_nat(&Nat::from_u64(u64::from(*b)))),
                    _ => None, // not a single byte
                }
            }
            // `char : Nat ~> Char` — the one-**byte** string for a code `0..=255` (256+ falls through: A2f).
            StrOp::Char => {
                let n = self.as_int(kids[0], nat?)?;
                if n.is_negative() {
                    return None;
                }
                let code = n.magnitude().to_u64()?;
                if code > 255 {
                    return None; // byte domain is 0..=255
                }
                Some(make_str(self, vec![code as u8]))
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
                let (hay, needle) = (s.as_ref(), pat.as_ref());
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
            // `isX : Char -> Bool` — the C `ctype` class of a single **byte** (else fall through). A byte
            // ≥ 128 maps to a non-ASCII `char`, which every `is_ascii_*` check rejects (in no C-locale class).
            StrOp::IsClass(class) => {
                let s = self.as_str(kids[0])?;
                let b = match s.as_ref() {
                    [b] => *b,
                    _ => return None, // not a single byte
                };
                let h = bool_?;
                Some(self.make_const(
                    sig,
                    if char_in_class(b as char, class) {
                        h.true_
                    } else {
                        h.false_
                    },
                ))
            }
            // `startsWith` / `endsWith : String String -> Bool` (byte prefix/suffix).
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
            // `trim` / `trimStart` / `trimEnd : String -> String` — strip C-whitespace **bytes**.
            StrOp::Trim | StrOp::TrimStart | StrOp::TrimEnd => {
                let s = self.as_str(kids[0])?;
                let (mut lo, mut hi) = (0, s.len());
                if matches!(op, StrOp::Trim | StrOp::TrimStart) {
                    while lo < hi && is_c_space(s[lo] as char) {
                        lo += 1;
                    }
                }
                if matches!(op, StrOp::Trim | StrOp::TrimEnd) {
                    while hi > lo && is_c_space(s[hi - 1] as char) {
                        hi -= 1;
                    }
                }
                Some(make_str(self, s[lo..hi].to_vec()))
            }
            StrOp::Lt | StrOp::Le | StrOp::Gt | StrOp::Ge => {
                let (a, b) = (self.as_str(kids[0])?, self.as_str(kids[1])?);
                // Maude's `Rope::compare`: signed-byte lexicographic (a high byte sorts before ASCII).
                let ord = crate::dag::rope_cmp(&a, &b);
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
            NodeTerm::Na {
                value: NaValue::Float(bits),
                ..
            } => Some(f64::from_bits(*bits)),
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
        let make_f =
            |this: &mut Self, v: f64| this.make_na(sig, float_sym, NaValue::Float(v.to_bits()));
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
        // NaN never reduces — a Maude Float value is never NaN (floatOpSymbol.cc gates every result on
        // `!isNaN`): partial ops off their domain (`sqrt(-1.0)`, `log(-1.0)`, `asin(2.0)`) AND the
        // indeterminate arithmetic forms (`Infinity - Infinity`, `Infinity * 0.0`, `Infinity / Infinity`,
        // `Infinity rem 2.0`) all stay in the kind `[Float]`. (`log(0.0)` = -inf is *not* NaN, so it
        // reduces; total ops keep inf results.)
        if v.is_nan() {
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
            let (nn, dn) = (
                self.make_int(sig, nat, new_num)?,
                self.make_int(sig, nat, new_den)?,
            );
            return Some(self.make_free(sig, symbol, vec![nn, dn]));
        }
        None // already in lowest terms
    }
}

/// Maude's `CommutativeDecomposeEqualitySymbol::isEquationallyStable`: the symbol cannot disappear
/// or change by instantiation (not a variable, no identity-collapse axiom), by equational rewriting
/// (no equations indexed at it), or by built-in rewriting (`STANDARD` basic type — no [`SpecialOp`]
/// and not a marker-class builtin).
fn equationally_stable(sig: &Signature, s: SymbolId) -> bool {
    let sym = sig.symbol(s);
    sym.class == SymbolClass::Standard
        && sym.special.is_none()
        && sym.identity.is_none()
        && !sig.has_equations(s)
}

/// A string's canonical Maude token name (`Token::ropeToPrefixNameCode`, `qid(String)`'s conversion):
/// a run of whitespace/backquote characters becomes a single backquote separator before the next
/// fragment, and each special char `( ) [ ] { } ,` is preceded by a backquote. `"a b"` and `` "a`b" ``
/// both canonicalize to `` a`b ``, so the qids they build are identical.
fn normalize_qid_name(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut need_bq = false;
    for c in s.chars() {
        if is_c_space(c) || c == '`' {
            need_bq = true;
        } else if matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',') {
            out.push('`');
            out.push(c);
            need_bq = false;
        } else {
            if need_bq {
                out.push('`');
            }
            out.push(c);
            need_bq = false;
        }
    }
    out
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
    u8::try_from(n.to_u64()?)
        .ok()
        .filter(|&b| (2..=36).contains(&b))
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
    (0..=pos.min(last))
        .rev()
        .find(|&i| &hay[i..i + needle.len()] == needle)
}

/// The first numeric operand `n` (multiplicity `m`) folded into a fresh accumulator.
fn acu_fold_first(op: NumOp, n: &Int, m: u32) -> Int {
    match op {
        NumOp::Add => n.mul(&Int::from_nat(&Nat::from_u64(u64::from(m)))), // n added m times
        NumOp::Mul => n.pow_u64(u64::from(m)),                             // n multiplied m times
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
