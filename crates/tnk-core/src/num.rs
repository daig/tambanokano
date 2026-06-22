//! Arbitrary-precision arithmetic behind a thin wrapper (decision **D4**: `malachite`, pure Rust).
//!
//! The kernel never names `malachite` directly — the S-theory successor count
//! ([`crate::dag::NodeTerm::S`]) and the built-in numeric operators (`NAT`/`INT`) go through [`Nat`]
//! (and later `Int`/`Rat`), so the bignum backend stays swappable and the exposed op surface is exactly
//! what the prelude needs. `Float` stays IEEE `f64` (not wrapped here). The op set mirrors Maude's
//! `mpz_class` usage in `BuiltIn/{succSymbol,numberOpSymbol,ACU_NumberOpSymbol}.cc` — it grows as each
//! consumer lands (this slice is what the S theory needs; NAT/INT arithmetic is added with those ops).

use malachite::Natural;
use malachite::base::num::arithmetic::traits::{CheckedSub, DivMod, DivisibleBy, Gcd, Lcm, Pow};
use malachite::base::num::basic::traits::{One, Zero};

/// A non-negative arbitrary-precision integer (Maude's `Natural`). `Clone`/`Eq`/`Ord`/`Debug` are
/// derived from the backend so [`NodeTerm`](crate::dag::NodeTerm) can derive `Debug` and the S-theory's
/// equality/order can compare counts directly (the count is scalar payload, not a child id). `min`/`max`
/// come from the derived `Ord` (`std::cmp::min`/`max`).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
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
    /// `self * other`.
    pub(crate) fn mul(&self, other: &Nat) -> Nat {
        Nat(&self.0 * &other.0)
    }
    /// `(self / other, self % other)` — Euclidean quotient and remainder; the caller guards `other != 0`.
    pub(crate) fn div_rem(&self, other: &Nat) -> (Nat, Nat) {
        let (q, r) = (&self.0).div_mod(&other.0);
        (Nat(q), Nat(r))
    }
    /// `self ^ exp`, or `None` if `exp` does not fit `u64` (an unrepresentable result).
    pub(crate) fn pow(&self, exp: &Nat) -> Option<Nat> {
        let e = u64::try_from(&exp.0).ok()?;
        Some(Nat((&self.0).pow(e)))
    }
    /// `self ^ exp` for a small machine exponent (the ACU-multiplicity fold `n^m` for `_*_`).
    pub(crate) fn pow_u64(&self, exp: u64) -> Nat {
        Nat((&self.0).pow(exp))
    }
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
    /// `self % m` as a machine `usize` (the S sort-path cycle index; `m` is the small cycle length, so
    /// the remainder is `< m` and always fits). Panics if `m == 0` (a cycle length is always `>= 1`).
    pub(crate) fn rem_usize(&self, m: usize) -> usize {
        let r = &self.0 % Natural::from(m as u64);
        usize::try_from(&r).expect("remainder < m fits usize")
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
    fn arithmetic_and_number_theory() {
        assert_eq!(n(3).mul(&n(4)), n(12));
        assert_eq!(n(7).div_rem(&n(2)), (n(3), n(1)));
        assert_eq!(n(2).pow(&n(10)), Some(n(1024)));
        assert_eq!(n(2).pow_u64(3), n(8));
        assert_eq!(n(0).pow(&n(0)), Some(n(1)), "0^0 = 1 (malachite convention)");
        assert_eq!(n(12).gcd(&n(18)), n(6));
        assert_eq!(n(4).lcm(&n(6)), n(12));
    }

    #[test]
    fn divides() {
        assert!(n(3).divides(&n(12)) && !n(5).divides(&n(12)));
        assert!(n(1).divides(&n(7)) && !n(7).divides(&n(1)));
    }
}
