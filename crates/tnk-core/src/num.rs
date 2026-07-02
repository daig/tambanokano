//! Arbitrary-precision arithmetic behind a thin wrapper (decision **D4**: `malachite`, pure Rust).
//!
//! The kernel never names `malachite` directly — the S-theory successor count
//! ([`crate::dag::NodeTerm::S`]) and the built-in numeric operators (`NAT`/`INT`) go through [`Nat`]
//! (and later `Int`/`Rat`), so the bignum backend stays swappable and the exposed op surface is exactly
//! what the prelude needs. `Float` stays IEEE `f64` (not wrapped here). The op set mirrors Maude's
//! `mpz_class` usage in `BuiltIn/{succSymbol,numberOpSymbol,ACU_NumberOpSymbol}.cc` — it grows as each
//! consumer lands (this slice is what the S theory needs; NAT/INT arithmetic is added with those ops).

use malachite::base::num::arithmetic::traits::{
    CheckedSub, DivRem, DivisibleBy, Gcd, Lcm, ModPow, Pow, UnsignedAbs,
};
use malachite::base::num::basic::traits::{One, Zero};
use malachite::base::num::conversion::traits::{FromStringBase, RoundingFrom, ToStringBase};
use malachite::base::rounding_modes::RoundingMode;
use malachite::{Integer, Natural, Rational};

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
    /// As a machine `u64` if it fits — `NAT` shift amounts (`_<<_`/`_>>_`).
    pub(crate) fn to_u64(&self) -> Option<u64> {
        u64::try_from(&self.0).ok()
    }

    /// `self << amount` / `self >> amount` (`_<<_` / `_>>_`); `>>` floors toward zero (shifts away the
    /// low bits). `amount` is a machine `u64` (the shift count fits — a bignum count is unrepresentable).
    pub(crate) fn shl(&self, amount: u64) -> Nat {
        Nat(&self.0 << amount)
    }
    pub(crate) fn shr(&self, amount: u64) -> Nat {
        Nat(&self.0 >> amount)
    }
    /// `self ^ exp mod modulus` (Maude's `modExp` — efficient modular exponentiation). The caller
    /// guards `modulus != 0` (`modExp`'s third argument is `NzNat`).
    pub(crate) fn mod_pow(&self, exp: &Nat, modulus: &Nat) -> Nat {
        Nat((&self.0).mod_pow(&exp.0, &modulus.0))
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
    /// `self << amount` / `self >> amount` (INT `_<<_` / `_>>_`): **arithmetic** shifts on the signed
    /// value — `>>` floors toward −∞ (GMP `mpz_fdiv_q_2exp`: `-8 >> 1 = -4`, `-1 >> k = -1` for any k),
    /// `<<` is exact scaling (`-5 << 2 = -20`). Malachite's `Integer` shifts have exactly these semantics.
    pub(crate) fn shl(&self, amount: u64) -> Int {
        Int(&self.0 << amount)
    }
    pub(crate) fn shr(&self, amount: u64) -> Int {
        Int(&self.0 >> amount)
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

    /// Base-`base` rendering with a leading `-` for negatives (Maude's `string(Int, base)` — `mpz_get_str`,
    /// lowercase digits). `base` in 2..=36.
    pub(crate) fn to_string_base(&self, base: u8) -> String {
        self.0.to_string_base(base)
    }
    /// Parse a signed integer written in `base` (Maude's `rat(String, base)` on an integer); `None` if the
    /// text is not a valid base-`base` integer.
    pub(crate) fn from_string_base(base: u8, s: &str) -> Option<Int> {
        Integer::from_string_base(base, s).map(Int)
    }

    /// Signed bitwise `_&_` / `_|_` / `_xor_` / `~_` (INT's `ACU_NumberOpSymbol` folds + `NumberOpSymbol
    /// (~)`). malachite's `Integer` uses two's-complement semantics with infinite sign extension —
    /// exactly Maude's GMP `mpz` bit ops — so `~x = -(x+1)` and a negative operand sign-extends. For
    /// non-negative operands these agree with the [`Nat`] magnitude versions (NAT rides the same fold).
    pub(crate) fn bitand(&self, other: &Int) -> Int {
        Int(&self.0 & &other.0)
    }
    pub(crate) fn bitor(&self, other: &Int) -> Int {
        Int(&self.0 | &other.0)
    }
    pub(crate) fn bitxor(&self, other: &Int) -> Int {
        Int(&self.0 ^ &other.0)
    }
    /// `~self = -(self + 1)` (bitwise NOT under two's complement).
    pub(crate) fn bitnot(&self) -> Int {
        Int(!&self.0)
    }
}

/// The exact rational value of a finite `f64` as `(signed numerator, positive denominator)` — Maude's
/// `rat(FiniteFloat)` (`mpq_set_d`: a double is `m · 2^e` exactly). `None` for NaN / infinite. The result
/// is fully reduced (malachite's `Rational` is canonical).
pub(crate) fn rational_of_f64(f: f64) -> Option<(Int, Nat)> {
    let r = Rational::try_from(f.abs()).ok()?; // magnitude; the sign is reapplied below
    let (num, den) = r.into_numerator_and_denominator();
    let num = Integer::from(num);
    Some((Int(if f < 0.0 { -num } else { num }), Nat(den)))
}

/// The `f64` nearest to the rational `num / den` (round-to-nearest-even) — Maude's `float(Rat)`
/// (`mpq_get_d`). `den` must be non-zero (the rational `_/_` constructor guarantees it).
pub(crate) fn f64_of_rational(num: &Int, den: &Nat) -> f64 {
    let r = Rational::from_integers(num.0.clone(), Integer::from(den.0.clone()));
    f64::rounding_from(&r, RoundingMode::Nearest).0
}

/// Parse a string to an `f64` (Maude's `float(String)`): accepted iff it passes Maude's
/// `looksLikeFloat` (Utility/macros.cc) — `[sign] ("Infinity" | digits with a `.` and/or an
/// `e[sign]digits` exponent)`. Bare integers (`"5"`), `"NaN"`, `"nan"`, `"inf"`, dangling exponents
/// (`"1.5e"`) and a lone `.` all stay unreduced — Rust's laxer `from_str` must not decide this.
pub(crate) fn parse_double(s: &str) -> Option<f64> {
    if !looks_like_float(s) {
        return None;
    }
    s.parse::<f64>().ok()
}

fn looks_like_float(s: &str) -> bool {
    let t = s.strip_prefix(['+', '-']).unwrap_or(s);
    if t == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match t.split_once(['e', 'E']) {
        Some((m, e)) => (m, Some(e)),
        None => (t, None),
    };
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, Some(f)),
        None => (mantissa, None),
    };
    let all_digits = |p: &str| p.bytes().all(|b| b.is_ascii_digit());
    if !all_digits(int_part) || !frac_part.is_none_or(all_digits) {
        return false;
    }
    // At least one digit somewhere in the mantissa…
    if int_part.is_empty() && frac_part.is_none_or(str::is_empty) {
        return false;
    }
    // …and a `.` or an exponent to make it a float rather than an integer numeral.
    match exponent {
        Some(e) => {
            let e = e.strip_prefix(['+', '-']).unwrap_or(e);
            !e.is_empty() && all_digits(e)
        }
        None => frac_part.is_some(),
    }
}

/// Render an `f64` exactly as Maude's `doubleToString` (`Utility/macros.cc`): 17 significant digits, the
/// mantissa normalized to `[1, 10)` with at least one fractional digit and trailing zeros stripped, and a
/// signed exponent shown only when nonzero — `1.0e+2`, `2.5e-1`, `3.14159265358979`, `-1.5`. `inf`/`nan`
/// print as `Infinity`/`-Infinity`/`NaN`. Shared by the pretty-printer (display) and the `string(Float)`
/// conversion, so both agree byte-for-byte.
pub fn double_to_string(f: f64) -> String {
    if f.is_nan() {
        return "NaN".to_string();
    }
    if f.is_infinite() {
        return if f < 0.0 { "-Infinity" } else { "Infinity" }.to_string();
    }
    if f == 0.0 {
        return "0.0".to_string(); // also catches -0.0
    }
    // 16 fractional digits ⇒ 17 significant digits, mantissa in [1, 10), correctly rounded — the same
    // value `ecvt(d, 17, …)` produces. Rust's `{:e}` writes `D.DDD…eE` (lowercase, no `+`, no padding).
    let sci = format!("{:.*e}", 16, f.abs());
    let (mantissa, exp) = sci.split_once('e').expect("scientific notation has an exponent");
    let exp: i64 = exp.parse().expect("exponent is an integer");
    let (int_part, frac) = mantissa.split_once('.').expect("a `.16e` mantissa has a decimal point");
    // Strip trailing zeros but keep at least one fractional digit (Maude's `next > 4` guard).
    let frac = frac.trim_end_matches('0');
    let frac = if frac.is_empty() { "0" } else { frac };
    let body = match exp {
        0 => format!("{int_part}.{frac}"),
        e if e > 0 => format!("{int_part}.{frac}e+{e}"),
        e => format!("{int_part}.{frac}e{e}"), // a negative exponent already carries its `-`
    };
    if f < 0.0 {
        format!("-{body}")
    } else {
        body
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
    fn bitwise_shifts_modpow() {
        // Shifts (`_<<_`/`_>>_`); `>>` floors, a huge shift clears all bits.
        assert_eq!(n(5).shl(3), n(40)); // 5 * 8
        assert_eq!(n(40).shr(3), n(5)); // 40 / 8
        assert_eq!(n(5).shr(100), n(0));
        assert_eq!(n(1).shl(64), n(u64::MAX).add(&n(1)), "1 << 64 = 2^64 (bignum)");
        // Modular exponentiation (`modExp`).
        assert_eq!(n(2).mod_pow(&n(10), &n(1000)), n(24)); // 1024 mod 1000
        assert_eq!(n(7).mod_pow(&n(0), &n(13)), n(1)); // x^0 = 1
        assert_eq!(n(3).mod_pow(&n(100), &n(7)), n(4)); // 3^100 ≡ 4 (mod 7)
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

    #[test]
    fn signed_bitwise() {
        use super::Int;
        let i = |x: u64| Int::from_nat(&n(x));
        let neg = |x: u64| i(x).sub(&i(2 * x)); // -x
        // Non-negative operands agree with ordinary unsigned bit ops (NAT rides this).
        assert_eq!(i(12).bitand(&i(10)), i(8)); // 1100 & 1010 = 1000
        assert_eq!(i(12).bitor(&i(10)), i(14)); // 1100 | 1010 = 1110
        assert_eq!(i(5).bitxor(&i(3)), i(6)); // 101 ^ 011 = 110
        assert_eq!(i(5).bitxor(&i(5)), i(0), "xor is self-inverse");
        // Two's-complement complement: ~x = -(x+1).
        assert_eq!(i(0).bitnot(), neg(1), "~0 = -1");
        assert_eq!(i(3).bitnot(), neg(4), "~3 = -4");
        assert_eq!(neg(1).bitnot(), i(0), "~(-1) = 0");
        // Signed operands sign-extend: -1 is all-ones, so (-1) & x = x, (-1) | x = -1.
        assert_eq!(neg(1).bitand(&i(12)), i(12), "(-1) & 12 = 12");
        assert_eq!(neg(1).bitor(&i(12)), neg(1), "(-1) | 12 = -1");
    }
}
