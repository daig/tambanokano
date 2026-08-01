//! Central fresh-variable generation.
//!
//! Three families, one per symbolic layer, each printing as `<char><n>`:
//! `#n` (family 0, unification), `%n` (family 1, variants), `@n` (family 2, narrowing).
//! Index `i` maps to the printed number `i + base_number + 1` (so index 0 with base 0 is `#1`).
//! `base_number` exists for the meta level (`metaUnify(_, _, _, 'X, N)` resumes numbering above `N`)
//! and is a bignum there, so it is a [`Nat`] here.
//!
//! Name-classification predicates preserve the reserved-prefix boundary, including these corners:
//! a printed index never starts with `0` (so `#0`, `#01` are NOT generatable names and never
//! conflict), and `belongs_to_family` accepts any all-digit tail (it classifies family membership
//! for protection purposes, not generatability).

use crate::num::Nat;

/// A fresh-variable family: the three reserved name prefixes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableFamily {
    /// `#n` — unification.
    Unify = 0,
    /// `%n` — variant generation / variant unification.
    Variant = 1,
    /// `@n` — narrowing.
    Narrow = 2,
}

impl VariableFamily {
    pub const ALL: [VariableFamily; 3] = [Self::Unify, Self::Variant, Self::Narrow];

    pub fn prefix(self) -> char {
        match self {
            Self::Unify => '#',
            Self::Variant => '%',
            Self::Narrow => '@',
        }
    }

    /// The family denoted by a one-character root name (`#`, `%`, or `@`).
    pub fn of_root(name: &str) -> Option<VariableFamily> {
        match name {
            "#" => Some(Self::Unify),
            "%" => Some(Self::Variant),
            "@" => Some(Self::Narrow),
            _ => None,
        }
    }

    fn of_prefix(c: char) -> Option<VariableFamily> {
        match c {
            '#' => Some(Self::Unify),
            '%' => Some(Self::Variant),
            '@' => Some(Self::Narrow),
            _ => None,
        }
    }
}

/// Fresh-variable name source for one symbolic operation, optionally resuming above a caller-supplied
/// base number.
#[derive(Debug, Default)]
pub struct FreshVariableGenerator {
    base_number: Nat,
    /// Per-family cache indexed by fresh index. A sparse request fills every preceding entry so
    /// generated names remain densely cached.
    caches: [Vec<String>; 3],
}

impl FreshVariableGenerator {
    pub fn new() -> Self {
        Self::default()
    }

    /// A generator whose printed numbers start above `base_number`, used when META-LEVEL operations
    /// resume a supplied fresh-variable counter.
    pub(crate) fn with_base(base_number: Nat) -> Self {
        FreshVariableGenerator {
            base_number,
            ..Self::default()
        }
    }

    /// The name of fresh variable `index` in `family`: `<prefix><index + base_number + 1>`.
    pub fn fresh_name(&mut self, index: usize, family: VariableFamily) -> &str {
        let cache = &mut self.caches[family as usize];
        while cache.len() <= index {
            let printed = self.base_number.add(&Nat::from_u64(cache.len() as u64 + 1));
            cache.push(format!("{}{}", family.prefix(), printed.to_decimal()));
        }
        &cache[index]
    }

    /// Whether `name` could collide with a fresh variable this generator may produce. Variables from
    /// `ok_family` are exempt because they belong to an earlier stage of the same pipeline. A conflict
    /// is `<prefix><digits>` with a nonzero first digit and a number above `base_number`.
    pub fn variable_name_conflict(&self, name: &str, ok_family: Option<VariableFamily>) -> bool {
        let mut chars = name.chars();
        let Some(family) = chars.next().and_then(VariableFamily::of_prefix) else {
            return false;
        };
        if ok_family == Some(family) {
            return false;
        }
        let digits = chars.as_str();
        if digits.is_empty() || digits.starts_with('0') {
            return false;
        }
        if !digits.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
        match Nat::from_decimal(digits) {
            Some(n) => n > self.base_number,
            None => false,
        }
    }

    /// Whether `name` belongs to `family`: its prefix matches and its tail is all digits. Leading zeroes
    /// are accepted because this classifies reserved-prefix ownership rather than generatability.
    pub fn belongs_to_family(name: &str, family: VariableFamily) -> bool {
        let mut chars = name.chars();
        if chars.next() != Some(family.prefix()) {
            return false;
        }
        let digits = chars.as_str();
        !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
    }

    /// If `name` is generatable, return its `(index, family)`. The printed number must not start with
    /// zero; `index` is that number minus one. Values too large for the machine-indexed cache return
    /// `None`.
    pub fn parse_fresh_name(name: &str) -> Option<(usize, VariableFamily)> {
        let mut chars = name.chars();
        let family = chars.next().and_then(VariableFamily::of_prefix)?;
        let digits = chars.as_str();
        if digits.is_empty() || digits.starts_with('0') {
            return None;
        }
        if !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let printed = Nat::from_decimal(digits)?;
        let index = printed.checked_sub(&Nat::one()).expect("printed >= 1");
        // Reject indices that cannot address the machine-indexed name cache.
        let index = index.to_usize()?;
        Some((index, family))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_names_per_family() {
        let mut g = FreshVariableGenerator::new();
        assert_eq!(g.fresh_name(0, VariableFamily::Unify), "#1");
        assert_eq!(g.fresh_name(1, VariableFamily::Unify), "#2");
        assert_eq!(g.fresh_name(0, VariableFamily::Variant), "%1");
        assert_eq!(g.fresh_name(2, VariableFamily::Narrow), "@3");
        assert_eq!(g.fresh_name(0, VariableFamily::Unify), "#1");
        // Sparse request fills the cache densely below it.
        assert_eq!(g.fresh_name(4, VariableFamily::Unify), "#5");
        assert_eq!(g.fresh_name(3, VariableFamily::Unify), "#4");
    }

    #[test]
    fn base_number_offsets_printed_index() {
        let mut g = FreshVariableGenerator::with_base(Nat::from_u64(10));
        assert_eq!(g.fresh_name(0, VariableFamily::Unify), "#11");
        assert_eq!(g.fresh_name(2, VariableFamily::Variant), "%13");
    }

    #[test]
    fn name_conflicts() {
        let g = FreshVariableGenerator::new();
        assert!(g.variable_name_conflict("#1", None));
        assert!(g.variable_name_conflict("%23", None));
        assert!(!g.variable_name_conflict("#1", Some(VariableFamily::Unify)));
        assert!(g.variable_name_conflict("#1", Some(VariableFamily::Variant)));
        assert!(!g.variable_name_conflict("X", None));
        assert!(!g.variable_name_conflict("#", None)); // no digits
        assert!(!g.variable_name_conflict("#0", None)); // leading zero: not generatable
        assert!(!g.variable_name_conflict("#01", None));
        assert!(!g.variable_name_conflict("#1a", None)); // non-digit tail
        // With a base number, small printed numbers are already used up — no conflict.
        let g = FreshVariableGenerator::with_base(Nat::from_u64(10));
        assert!(!g.variable_name_conflict("#10", None));
        assert!(g.variable_name_conflict("#11", None));
    }

    #[test]
    fn family_classification_and_parse() {
        assert!(FreshVariableGenerator::belongs_to_family(
            "#12",
            VariableFamily::Unify
        ));
        assert!(FreshVariableGenerator::belongs_to_family(
            "#01",
            VariableFamily::Unify
        ));
        assert!(!FreshVariableGenerator::belongs_to_family(
            "%12",
            VariableFamily::Unify
        ));
        assert!(!FreshVariableGenerator::belongs_to_family(
            "#",
            VariableFamily::Unify
        ));

        assert_eq!(
            FreshVariableGenerator::parse_fresh_name("#1"),
            Some((0, VariableFamily::Unify))
        );
        assert_eq!(
            FreshVariableGenerator::parse_fresh_name("@7"),
            Some((6, VariableFamily::Narrow))
        );
        assert_eq!(FreshVariableGenerator::parse_fresh_name("#01"), None);
        assert_eq!(FreshVariableGenerator::parse_fresh_name("Y"), None);
        assert_eq!(VariableFamily::of_root("%"), Some(VariableFamily::Variant));
        assert_eq!(VariableFamily::of_root("#%"), None);
    }
}
