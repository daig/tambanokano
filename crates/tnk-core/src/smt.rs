//! SMT-language values, per-signature hook metadata, and the query-local solver seam.
//!
//! The language representation and null backend are always available. Native DAG-to-z3 translation
//! is the only `smt-z3`-gated part, so the default build remains pure Rust.

use crate::dag::DagId;
use crate::engine::Engine;
use crate::num::ExactRational;
use crate::sort::{KindId, SortId};
use crate::symbol::SymbolId;
use std::collections::HashMap;

/// The three built-in SMT sorts understood by Maude's `SMT_Info`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtType {
    Boolean,
    Integer,
    Real,
}

/// Maude's 25 `SMT_Symbol::OPERATORS` values. Unary and binary `-` are distinct after the
/// arity-sensitive hook-resolution step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtOp {
    True,
    False,
    Not,
    And,
    Or,
    Xor,
    Implies,
    Equals,
    NotEquals,
    Ite,
    UnaryMinus,
    Minus,
    Plus,
    Multiply,
    Divide,
    Modulo,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Divisible,
    RealDivide,
    ToReal,
    ToInteger,
    IsInteger,
}

/// An exact SMT integer or rational leaf. `ExactRational` is canonical, so derived equality, hashing,
/// and ordering are mathematical rather than source-spelling based (`2/4 == 1/2`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtNumber(ExactRational);

impl SmtNumber {
    /// Parse the token class accepted for `kind`: signed decimal integers for `Integer`, and a signed
    /// decimal numerator over a positive decimal denominator for `Real`.
    pub fn parse(text: &str, kind: SmtType) -> Option<Self> {
        let signed_decimal = |s: &str| {
            let digits = s.strip_prefix('-').unwrap_or(s);
            !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
        };
        match kind {
            SmtType::Integer if !text.contains('/') && signed_decimal(text) => {}
            SmtType::Real => {
                let (num, den) = text.split_once('/')?;
                if !signed_decimal(num)
                    || den.is_empty()
                    || !den.bytes().all(|b| b.is_ascii_digit())
                    || den.bytes().all(|b| b == b'0')
                    || den.contains('/')
                {
                    return None;
                }
            }
            _ => return None,
        }
        Some(Self(ExactRational::parse(text)?))
    }

    /// Canonical Maude token spelling for the declared SMT sort. Reals always retain a denominator,
    /// including `/1`; integers never do.
    pub fn to_maude(&self, kind: SmtType) -> String {
        let text = self.0.to_decimal_ratio();
        match kind {
            SmtType::Integer => text,
            SmtType::Real if text.contains('/') => text,
            SmtType::Real => format!("{text}/1"),
            SmtType::Boolean => unreachable!("an SMT number cannot have Boolean sort"),
        }
    }

    /// Canonical signed-numerator/positive-denominator strings for solver translation.
    pub fn ratio_parts(&self) -> (String, String) {
        let text = self.0.to_decimal_ratio();
        match text.split_once('/') {
            Some((num, den)) => (num.to_string(), den.to_string()),
            None => (text, "1".to_string()),
        }
    }

    #[cfg(feature = "smt-z3")]
    fn is_positive_integer(&self) -> bool {
        let (num, den) = self.ratio_parts();
        den == "1" && num != "0" && !num.starts_with('-')
    }
}

/// Per-signature bindings corresponding to Maude's `SMT_Info`: sort classifications and the operators
/// used to build accumulated constraints.
#[derive(Debug, Default, Clone)]
pub struct SmtInfo {
    sort_types: HashMap<SortId, SmtType>,
    conjunction: Option<SymbolId>,
    true_symbol: Option<SymbolId>,
    equality_by_kind: HashMap<KindId, SymbolId>,
    number_by_kind: HashMap<KindId, SymbolId>,
}

impl SmtInfo {
    pub fn sort_type(&self, sort: SortId) -> Option<SmtType> {
        self.sort_types.get(&sort).copied()
    }

    pub fn conjunction(&self) -> Option<SymbolId> {
        self.conjunction
    }

    pub fn true_symbol(&self) -> Option<SymbolId> {
        self.true_symbol
    }

    pub fn equality(&self, kind: KindId) -> Option<SymbolId> {
        self.equality_by_kind.get(&kind).copied()
    }

    pub fn number_symbol(&self, kind: KindId) -> Option<SymbolId> {
        self.number_by_kind.get(&kind).copied()
    }

    pub(crate) fn set_sort_type(&mut self, sort: SortId, kind: SmtType) {
        self.sort_types.entry(sort).or_insert(kind);
    }

    pub(crate) fn set_conjunction(&mut self, symbol: SymbolId) {
        self.conjunction = Some(symbol);
    }

    pub(crate) fn set_true_symbol(&mut self, symbol: SymbolId) {
        self.true_symbol = Some(symbol);
    }

    pub(crate) fn set_equality(&mut self, kind: KindId, symbol: SymbolId) {
        self.equality_by_kind.insert(kind, symbol);
    }

    pub(crate) fn set_number_symbol(&mut self, kind: KindId, symbol: SymbolId) {
        self.number_by_kind.insert(kind, symbol);
    }
}

/// The four outcomes of translating and checking an SMT DAG.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
    BadDag,
}

/// Query-local SMT backend. `check_dag` is temporary; `assert_dag` leaves the formula asserted.
pub trait SmtEngine {
    fn assert_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult;
    fn check_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult;
    fn clear(&mut self);
    fn push(&mut self);
    fn pop(&mut self);
}

/// Pure-Rust degradation path when no native solver feature is enabled.
#[derive(Debug, Default)]
pub struct NullSmtEngine;

impl SmtEngine for NullSmtEngine {
    fn assert_dag(&mut self, _engine: &Engine, _dag: DagId) -> SmtResult {
        SmtResult::Unknown
    }

    fn check_dag(&mut self, _engine: &Engine, _dag: DagId) -> SmtResult {
        SmtResult::Unknown
    }

    fn clear(&mut self) {}
    fn push(&mut self) {}
    fn pop(&mut self) {}
}

/// The feature-selected production backend without trait-object allocation.
pub enum ConfiguredSmtEngine {
    Null(NullSmtEngine),
    #[cfg(feature = "smt-z3")]
    Z3(z3::Z3Engine),
}

impl Default for ConfiguredSmtEngine {
    fn default() -> Self {
        #[cfg(feature = "smt-z3")]
        {
            Self::Z3(z3::Z3Engine::new())
        }
        #[cfg(not(feature = "smt-z3"))]
        {
            Self::Null(NullSmtEngine)
        }
    }
}

impl SmtEngine for ConfiguredSmtEngine {
    fn assert_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult {
        match self {
            Self::Null(backend) => backend.assert_dag(engine, dag),
            #[cfg(feature = "smt-z3")]
            Self::Z3(backend) => backend.assert_dag(engine, dag),
        }
    }

    fn check_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult {
        match self {
            Self::Null(backend) => backend.check_dag(engine, dag),
            #[cfg(feature = "smt-z3")]
            Self::Z3(backend) => backend.check_dag(engine, dag),
        }
    }

    fn clear(&mut self) {
        match self {
            Self::Null(backend) => backend.clear(),
            #[cfg(feature = "smt-z3")]
            Self::Z3(backend) => backend.clear(),
        }
    }

    fn push(&mut self) {
        match self {
            Self::Null(backend) => backend.push(),
            #[cfg(feature = "smt-z3")]
            Self::Z3(backend) => backend.push(),
        }
    }

    fn pop(&mut self) {
        match self {
            Self::Null(backend) => backend.pop(),
            #[cfg(feature = "smt-z3")]
            Self::Z3(backend) => backend.pop(),
        }
    }
}

#[cfg(feature = "smt-z3")]
pub mod z3 {
    use super::{SmtEngine, SmtOp, SmtResult, SmtType};
    use crate::dag::{DagId, NodeRepr};
    use crate::engine::Engine;
    use ::z3::ast::{Bool, Int, Real};
    use ::z3::{SatResult, Solver};
    use std::collections::HashMap;
    use std::str::FromStr;

    #[derive(Clone)]
    enum Expr {
        Bool(Bool),
        Int(Int),
        Real(Real),
    }

    /// Native z3 backend. z3 0.20 uses a thread-local context, so the solver and all translated ASTs
    /// are query-local values without explicit lifetime parameters.
    pub struct Z3Engine {
        solver: Solver,
    }

    impl Z3Engine {
        pub fn new() -> Self {
            Self {
                solver: Solver::new(),
            }
        }

        fn result(result: SatResult) -> SmtResult {
            match result {
                SatResult::Sat => SmtResult::Sat,
                SatResult::Unsat => SmtResult::Unsat,
                SatResult::Unknown => SmtResult::Unknown,
            }
        }

        /// Translate in iterative post-order so deeply nested solver formulas do not consume the Rust
        /// call stack. Shared DAG children translate once per query.
        fn translate_bool(&self, engine: &Engine, root: DagId) -> Option<Bool> {
            let mut values = HashMap::<DagId, Expr>::new();
            let mut pending = vec![(root, false)];
            while let Some((dag, expanded)) = pending.pop() {
                if values.contains_key(&dag) {
                    continue;
                }
                if expanded {
                    let args: Vec<DagId> = engine.node(dag).children().collect();
                    let op = engine.smt_operator(engine.node(dag).symbol())?;
                    let value = apply(engine, op, &args, &values)?;
                    values.insert(dag, value);
                    continue;
                }
                match engine.node(dag).repr() {
                    NodeRepr::App => {
                        pending.push((dag, true));
                        let args: Vec<DagId> = engine.node(dag).children().collect();
                        pending.extend(args.into_iter().rev().map(|child| (child, false)));
                    }
                    NodeRepr::SmtNum(number) => {
                        let kind = engine.smt_type(engine.sort_of(dag))?;
                        let (num, den) = number.ratio_parts();
                        let value = match kind {
                            SmtType::Integer if den == "1" => Expr::Int(Int::from_str(&num).ok()?),
                            SmtType::Real => Expr::Real(Real::from_rational_str(&num, &den)?),
                            _ => return None,
                        };
                        values.insert(dag, value);
                    }
                    NodeRepr::Var { name } => {
                        let kind = engine.smt_type(engine.sort_of(dag))?;
                        let tag = match kind {
                            SmtType::Boolean => 'b',
                            SmtType::Integer => 'i',
                            SmtType::Real => 'r',
                        };
                        let name = format!("tnk!{tag}!{name}");
                        let value = match kind {
                            SmtType::Boolean => Expr::Bool(Bool::new_const(name)),
                            SmtType::Integer => Expr::Int(Int::new_const(name)),
                            SmtType::Real => Expr::Real(Real::new_const(name)),
                        };
                        values.insert(dag, value);
                    }
                    NodeRepr::Iter { .. }
                    | NodeRepr::Str(_)
                    | NodeRepr::Qid(_)
                    | NodeRepr::Float(_) => return None,
                }
            }
            match values.remove(&root)? {
                Expr::Bool(value) => Some(value),
                Expr::Int(_) | Expr::Real(_) => None,
            }
        }
    }

    impl Default for Z3Engine {
        fn default() -> Self {
            Self::new()
        }
    }

    impl SmtEngine for Z3Engine {
        fn assert_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult {
            let Some(formula) = self.translate_bool(engine, dag) else {
                return SmtResult::BadDag;
            };
            self.solver.assert(&formula);
            Self::result(self.solver.check())
        }

        fn check_dag(&mut self, engine: &Engine, dag: DagId) -> SmtResult {
            let Some(formula) = self.translate_bool(engine, dag) else {
                return SmtResult::BadDag;
            };
            self.solver.push();
            self.solver.assert(&formula);
            let result = Self::result(self.solver.check());
            self.solver.pop(1);
            result
        }

        fn clear(&mut self) {
            self.solver.reset();
        }

        fn push(&mut self) {
            self.solver.push();
        }

        fn pop(&mut self) {
            self.solver.pop(1);
        }
    }

    fn value<'a>(values: &'a HashMap<DagId, Expr>, dag: &DagId) -> Option<&'a Expr> {
        values.get(dag)
    }

    fn apply(
        engine: &Engine,
        op: SmtOp,
        args: &[DagId],
        values: &HashMap<DagId, Expr>,
    ) -> Option<Expr> {
        match op {
            SmtOp::True if args.is_empty() => Some(Expr::Bool(Bool::from_bool(true))),
            SmtOp::False if args.is_empty() => Some(Expr::Bool(Bool::from_bool(false))),
            SmtOp::Not => {
                let [arg] = args else { return None };
                let Expr::Bool(arg) = value(values, arg)? else {
                    return None;
                };
                Some(Expr::Bool(arg.not()))
            }
            SmtOp::And | SmtOp::Or | SmtOp::Xor | SmtOp::Implies => {
                let [lhs, rhs] = args else { return None };
                let (Expr::Bool(lhs), Expr::Bool(rhs)) = (value(values, lhs)?, value(values, rhs)?)
                else {
                    return None;
                };
                Some(Expr::Bool(match op {
                    SmtOp::And => Bool::and(&[lhs, rhs]),
                    SmtOp::Or => Bool::or(&[lhs, rhs]),
                    SmtOp::Xor => lhs.xor(rhs),
                    SmtOp::Implies => lhs.implies(rhs),
                    _ => unreachable!(),
                }))
            }
            SmtOp::Equals | SmtOp::NotEquals => {
                let [lhs, rhs] = args else { return None };
                let equality = match (value(values, lhs)?, value(values, rhs)?) {
                    (Expr::Bool(lhs), Expr::Bool(rhs)) => lhs.eq(rhs),
                    (Expr::Int(lhs), Expr::Int(rhs)) => lhs.eq(rhs),
                    (Expr::Real(lhs), Expr::Real(rhs)) => lhs.eq(rhs),
                    _ => return None,
                };
                Some(Expr::Bool(if op == SmtOp::NotEquals {
                    equality.not()
                } else {
                    equality
                }))
            }
            SmtOp::Ite => {
                let [condition, then_value, else_value] = args else {
                    return None;
                };
                let Expr::Bool(condition) = value(values, condition)? else {
                    return None;
                };
                match (value(values, then_value)?, value(values, else_value)?) {
                    (Expr::Bool(lhs), Expr::Bool(rhs)) => Some(Expr::Bool(condition.ite(lhs, rhs))),
                    (Expr::Int(lhs), Expr::Int(rhs)) => Some(Expr::Int(condition.ite(lhs, rhs))),
                    (Expr::Real(lhs), Expr::Real(rhs)) => Some(Expr::Real(condition.ite(lhs, rhs))),
                    _ => None,
                }
            }
            SmtOp::UnaryMinus => {
                let [arg] = args else { return None };
                match value(values, arg)? {
                    Expr::Int(arg) => Some(Expr::Int(arg.unary_minus())),
                    Expr::Real(arg) => Some(Expr::Real(arg.unary_minus())),
                    Expr::Bool(_) => None,
                }
            }
            SmtOp::Minus | SmtOp::Plus | SmtOp::Multiply => {
                let [lhs, rhs] = args else { return None };
                match (value(values, lhs)?, value(values, rhs)?) {
                    (Expr::Int(lhs), Expr::Int(rhs)) => Some(Expr::Int(match op {
                        SmtOp::Minus => Int::sub(&[lhs, rhs]),
                        SmtOp::Plus => Int::add(&[lhs, rhs]),
                        SmtOp::Multiply => Int::mul(&[lhs, rhs]),
                        _ => unreachable!(),
                    })),
                    (Expr::Real(lhs), Expr::Real(rhs)) => Some(Expr::Real(match op {
                        SmtOp::Minus => Real::sub(&[lhs, rhs]),
                        SmtOp::Plus => Real::add(&[lhs, rhs]),
                        SmtOp::Multiply => Real::mul(&[lhs, rhs]),
                        _ => unreachable!(),
                    })),
                    _ => None,
                }
            }
            SmtOp::Divide | SmtOp::Modulo => {
                let [lhs, rhs] = args else { return None };
                let (Expr::Int(lhs), Expr::Int(rhs)) = (value(values, lhs)?, value(values, rhs)?)
                else {
                    return None;
                };
                Some(Expr::Int(if op == SmtOp::Divide {
                    lhs.div(rhs)
                } else {
                    lhs.modulo(rhs)
                }))
            }
            SmtOp::Less | SmtOp::LessEqual | SmtOp::Greater | SmtOp::GreaterEqual => {
                let [lhs, rhs] = args else { return None };
                let result = match (value(values, lhs)?, value(values, rhs)?) {
                    (Expr::Int(lhs), Expr::Int(rhs)) => match op {
                        SmtOp::Less => lhs.lt(rhs),
                        SmtOp::LessEqual => lhs.le(rhs),
                        SmtOp::Greater => lhs.gt(rhs),
                        SmtOp::GreaterEqual => lhs.ge(rhs),
                        _ => unreachable!(),
                    },
                    (Expr::Real(lhs), Expr::Real(rhs)) => match op {
                        SmtOp::Less => lhs.lt(rhs),
                        SmtOp::LessEqual => lhs.le(rhs),
                        SmtOp::Greater => lhs.gt(rhs),
                        SmtOp::GreaterEqual => lhs.ge(rhs),
                        _ => unreachable!(),
                    },
                    _ => return None,
                };
                Some(Expr::Bool(result))
            }
            SmtOp::Divisible => {
                let [dividend, divisor] = args else {
                    return None;
                };
                let NodeRepr::SmtNum(number) = engine.node(*divisor).repr() else {
                    return None;
                };
                if !number.is_positive_integer() {
                    return None;
                }
                let (Expr::Int(dividend), Expr::Int(divisor)) =
                    (value(values, dividend)?, value(values, divisor)?)
                else {
                    return None;
                };
                Some(Expr::Bool(dividend.modulo(divisor).eq(Int::from_i64(0))))
            }
            SmtOp::RealDivide => {
                let [lhs, rhs] = args else { return None };
                let (Expr::Real(lhs), Expr::Real(rhs)) = (value(values, lhs)?, value(values, rhs)?)
                else {
                    return None;
                };
                Some(Expr::Real(lhs.div(rhs)))
            }
            SmtOp::ToReal => {
                let [arg] = args else { return None };
                let Expr::Int(arg) = value(values, arg)? else {
                    return None;
                };
                Some(Expr::Real(arg.to_real()))
            }
            SmtOp::ToInteger => {
                let [arg] = args else { return None };
                let Expr::Real(arg) = value(values, arg)? else {
                    return None;
                };
                Some(Expr::Int(arg.to_int()))
            }
            SmtOp::IsInteger => {
                let [arg] = args else { return None };
                let Expr::Real(arg) = value(values, arg)? else {
                    return None;
                };
                Some(Expr::Bool(arg.is_int()))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{SmtNumber, SmtType};
    use std::collections::HashSet;

    #[test]
    fn exact_numbers_canonicalize_order_hash_and_spelling() {
        let half = SmtNumber::parse("2/4", SmtType::Real).unwrap();
        let canonical = SmtNumber::parse("1/2", SmtType::Real).unwrap();
        let negative = SmtNumber::parse("-3/6", SmtType::Real).unwrap();
        assert_eq!(half, canonical);
        assert!(negative < half);
        assert_eq!(half.to_maude(SmtType::Real), "1/2");
        assert_eq!(
            SmtNumber::parse("7", SmtType::Integer)
                .unwrap()
                .to_maude(SmtType::Integer),
            "7"
        );
        assert_eq!(
            SmtNumber::parse("0/5", SmtType::Real)
                .unwrap()
                .to_maude(SmtType::Real),
            "0/1"
        );
        assert_eq!(HashSet::from([half, canonical]).len(), 1);
    }

    #[test]
    fn number_token_classes_are_strict() {
        assert!(SmtNumber::parse("-12", SmtType::Integer).is_some());
        assert!(SmtNumber::parse("12/1", SmtType::Integer).is_none());
        assert!(SmtNumber::parse("12", SmtType::Real).is_none());
        assert!(SmtNumber::parse("1/0", SmtType::Real).is_none());
        assert!(SmtNumber::parse("1/-2", SmtType::Real).is_none());
    }
}
