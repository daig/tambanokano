//! Arbitrary-precision arithmetic behind a thin wrapper (decision **D4**: `malachite`, pure Rust).
//!
//! The kernel never names `malachite` directly — the S-theory successor count
//! ([`crate::dag::NodeTerm::S`]) and the built-in numeric operators (`NAT`/`INT`) go through [`Nat`]
//! (and later `Int`/`Rat`), so the bignum backend stays swappable and the exposed op surface is exactly
//! what the prelude needs. `Float` stays IEEE `f64` (not wrapped here). The op set mirrors Maude's
//! `mpz_class` usage in `BuiltIn/{succSymbol,numberOpSymbol,ACU_NumberOpSymbol}.cc` — it grows as each
//! consumer lands (this slice is what the S theory needs; NAT/INT arithmetic is added with those ops).

use malachite::base::num::arithmetic::traits::{
    CheckedSub, DivRem, DivisibleBy, Gcd, Lcm, Pow, UnsignedAbs,
};
use malachite::base::num::basic::traits::{One, Zero};
use malachite::{Integer, Natural};

/// A non-negative arbitrary-precision integer (Maude's `Natural`). `Clone`/`Eq`/`Ord`/`Debug` are
/// derived from the backend so [`NodeTerm`](crate::dag::NodeTerm) can derive `Debug` and the S-theory's
/// equality/order can compare counts directly (the count is scalar payload, not a child id). `min`/`max`
/// come from the derived `Ord` (`std::cmp::min`/`max`). `Hash` lets [`NodeTerm`](crate::dag::NodeTerm)
/// be a construction-dedup memo key (C7), so an `S` (`iter`) successor keys on its count.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default, Hash)]
pub(crate) struct Nat(Natural);

impl Nat {
    /// `0`.
    pub(crate) fn zero() -> Self {
        Nat(Natural::ZERO)
    }
    /// `1` — the successor increment (`rebuild` folds nested `s_` layers one at a time).
    pub(crate) fn one() -> Self {
        Nat(Natural::ONE)
    }
    /// From a machine integer (numerals built in tests / by the future parser).
    pub(crate) fn from_u64(n: u64) -> Self {
        Nat(Natural::from(n))
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.0 == Natural::ZERO
    }

    /// `self + other` (the S-theory `s^j(s^k(x)) = s^(j+k)(x)` flatten).
    pub(crate) fn add(&self, other: &Nat) -> Nat {
        Nat(&self.0 + &other.0)
    }
    /// `self - other`, or `None` if it would go negative — `Natural` subtraction is partial (monus).
    /// The S-theory residue `s^(n-k)` uses this with `n >= k` already checked; for `NAT` a `None` is
    /// the built-in op's "fall through to user equations" case (a signed result needs `Int`, B3.5).
    pub(crate) fn checked_sub(&self, other: &Nat) -> Option<Nat> {
        (&self.0).checked_sub(&other.0).map(Nat)
    }
    // Signed arithmetic (`*`/`/`/`^`/`-`) lives on `Int` — `NAT` and `INT` both compute in `Int`, since
    // `Nat ⊂ Int` (a negative result with no `minus` hook is the NAT "fall through" case). `Nat` keeps
    // only what the S theory and the magnitude-based ops (gcd/lcm/divides) need.
    pub(crate) fn gcd(&self, other: &Nat) -> Nat {
        Nat((&self.0).gcd(&other.0))
    }
    pub(crate) fn lcm(&self, other: &Nat) -> Nat {
        Nat((&self.0).lcm(&other.0))
    }
    /// Whether `self` divides `other` (`self | other`); by `divisible_by`, `0 | other` iff `other == 0`
    /// (the prelude's `_divides_` takes an `NzNat` divisor, so the zero case is moot).
    pub(crate) fn divides(&self, other: &Nat) -> bool {
        (&other.0).divisible_by(&self.0)
    }
    /// As a machine `usize` if it fits — the S-theory sort-path index (always small).
    pub(crate) fn to_usize(&self) -> Option<usize> {
        usize::try_from(&self.0).ok()
    }
    /// Base-10 rendering — for the pretty-printer's decimal numerals / iter counts (a `usize` would
    /// truncate a bignum count). Malachite's `Natural` is `Display`.
    pub(crate) fn to_decimal(&self) -> String {
        self.0.to_string()
    }
    /// `self % m` as a machine `usize` (the S sort-path cycle index; `m` is the small cycle length, so
    /// the remainder is `< m` and always fits). Panics if `m == 0` (a cycle length is always `>= 1`).
    pub(crate) fn rem_usize(&self, m: usize) -> usize {
        let r = &self.0 % Natural::from(m as u64);
        usize::try_from(&r).expect("remainder < m fits usize")
    }
}

/// A signed arbitrary-precision integer (Maude's `Integer`), the `INT` built-ins' value type. A numeral
/// is `0`, `s^n(0)` (positive), or `-(s^n(0))` (negative), so an [`Int`] decomposes into a sign and a
/// [`Nat`] [magnitude](Int::magnitude). `quo`/`rem` truncate toward zero (Maude's convention — the
/// remainder takes the dividend's sign), which is malachite's `DivRem` (not `DivMod`, which floors).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Int(Integer);

impl Int {
    /// A non-negative `Int` from a `Nat` magnitude (the fold's accumulator seed; `Int::from_nat(&zero)`
    /// is the zero value).
    pub(crate) fn from_nat(n: &Nat) -> Self {
        Int(Integer::from(n.0.clone()))
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.0 == Integer::ZERO
    }
    pub(crate) fn is_negative(&self) -> bool {
        self.0 < Integer::ZERO
    }
    /// `|self|` as a `Nat` — the magnitude a numeral node stores (`s^|self|(0)`, negated if negative).
    pub(crate) fn magnitude(&self) -> Nat {
        Nat((&self.0).unsigned_abs())
    }
    /// `-self`.
    pub(crate) fn neg(&self) -> Int {
        Int(-&self.0)
    }

    pub(crate) fn add(&self, other: &Int) -> Int {
        Int(&self.0 + &other.0)
    }
    pub(crate) fn sub(&self, other: &Int) -> Int {
        Int(&self.0 - &other.0)
    }
    pub(crate) fn mul(&self, other: &Int) -> Int {
        Int(&self.0 * &other.0)
    }
    /// `(self / other, self % other)`, **truncated toward zero** (remainder takes the dividend's sign —
    /// Maude `quo`/`rem`). The caller guards `other != 0`.
    pub(crate) fn div_rem(&self, other: &Int) -> (Int, Int) {
        let (q, r) = (&self.0).div_rem(&other.0);
        (Int(q), Int(r))
    }
    /// `self ^ exp` for a non-negative machine exponent (`_^_ : Int Nat -> Int`).
    pub(crate) fn pow_u64(&self, exp: u64) -> Int {
        Int((&self.0).pow(exp))
    }
}

#[cfg(test)]
mod tests {
    use super::Nat;

    fn n(x: u64) -> Nat {
        Nat::from_u64(x)
    }

    #[test]
    fn constants_predicates_and_order() {
        assert!(Nat::zero().is_zero());
        assert!(!Nat::one().is_zero());
        assert_eq!(Nat::zero(), n(0));
        assert_eq!(Nat::one(), n(1));
        assert!(n(2) < n(3) && n(3) > n(2) && n(3) == n(3));
        assert_eq!(std::cmp::min(n(2), n(5)), n(2), "min/max via derived Ord");
    }

    #[test]
    fn add_and_monus() {
        assert_eq!(n(2).add(&n(3)), n(5));
        assert_eq!(n(5).checked_sub(&n(3)), Some(n(2)));
        assert_eq!(n(3).checked_sub(&n(5)), None, "Natural monus is partial");
        assert_eq!(n(0).checked_sub(&n(0)), Some(n(0)));
    }

    #[test]
    fn to_usize_and_bignum_width() {
        assert_eq!(n(100).to_usize(), Some(100));
        // A count past machine width still round-trips through add (genuinely arbitrary-precision).
        let big = n(u64::MAX).add(&n(1));
        assert_eq!(big.to_usize(), None, "u64::MAX + 1 does not fit usize");
        assert_eq!(big.checked_sub(&n(1)), Some(n(u64::MAX)));
    }

    #[test]
    fn number_theory() {
        // `Nat` keeps only the magnitude-based ops; signed `*`/`/`/`^`/`-` are tested on `Int` below.
        assert_eq!(n(12).gcd(&n(18)), n(6));
        assert_eq!(n(4).lcm(&n(6)), n(12));
    }

    #[test]
    fn divides() {
        assert!(n(3).divides(&n(12)) && !n(5).divides(&n(12)));
        assert!(n(1).divides(&n(7)) && !n(7).divides(&n(1)));
    }

    #[test]
    fn signed_int() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let neg = |x: u64| i(x).sub(&i(2 * x)); // -x
        assert!(i(0).is_zero() && !i(3).is_negative());
        assert!(neg(3).is_negative(), "-3 is negative");
        assert_eq!(neg(3).magnitude(), n(3), "|-3| = 3");
        assert_eq!(i(2).add(&neg(5)), neg(3), "2 + (-5) = -3");
        assert_eq!(i(2).sub(&i(5)), neg(3), "2 - 5 = -3");
        assert_eq!(neg(2).mul(&neg(3)), i(6), "(-2)(-3) = 6");
        // quo/rem truncate toward zero; the remainder takes the dividend's sign.
        let (q, r) = i(7).div_rem(&neg(2));
        assert_eq!((q, r), (neg(3), i(1)), "7 quo -2 = -3, 7 rem -2 = 1");
        let (q, r) = neg(7).div_rem(&i(2));
        assert_eq!((q, r), (neg(3), neg(1)), "-7 quo 2 = -3, -7 rem 2 = -1");
        assert!(neg(2) < i(3) && i(3) > neg(2), "-2 < 3");
    }
}
