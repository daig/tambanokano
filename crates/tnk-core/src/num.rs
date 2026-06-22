//! Arbitrary-precision arithmetic behind a thin wrapper (decision **D4**: `malachite`, pure Rust).
//!
//! The kernel never names `malachite` directly — the S-theory successor count
//! ([`crate::dag::NodeTerm::S`]) and the built-in numeric operators (`NAT`/`INT`) go through [`Nat`]
//! (and later `Int`/`Rat`), so the bignum backend stays swappable and the exposed op surface is exactly
//! what the prelude needs. `Float` stays IEEE `f64` (not wrapped here). The op set mirrors Maude's
//! `mpz_class` usage in `BuiltIn/{succSymbol,numberOpSymbol,ACU_NumberOpSymbol}.cc` — it grows as each
//! consumer lands (this slice is what the S theory needs; NAT/INT arithmetic is added with those ops).

use malachite::Natural;
use malachite::base::num::arithmetic::traits::CheckedSub;
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
    /// The S-theory residue `s^(n-k)` uses this with `n >= k` already checked.
    pub(crate) fn checked_sub(&self, other: &Nat) -> Option<Nat> {
        (&self.0).checked_sub(&other.0).map(Nat)
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
}
