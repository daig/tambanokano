//! Packed constraints on variables in word-equation problems.
//!
//! Line-faithful port of Maude's `Utility/variableConstraint.{hh,cc}`.

/// A variable may take the empty word, have a finite word-length upper bound, or carry a
/// theory index (which implies an upper bound of one). The representation deliberately mirrors
/// Maude's packed 32-bit value: `(index << 2) | theory | take_empty`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct VariableConstraint(u32);

impl VariableConstraint {
    const TAKE_EMPTY: u32 = 1;
    const THEORY: u32 = 2;
    const INDEX_SHIFT: u32 = 2;

    pub(super) fn set_take_empty(&mut self) {
        self.0 |= Self::TAKE_EMPTY;
    }

    /// Zero means unbounded, as in Maude.
    pub(super) fn set_upper_bound(&mut self, upper_bound: usize) {
        debug_assert!(upper_bound <= (u32::MAX >> Self::INDEX_SHIFT) as usize);
        self.0 = (self.0 & Self::TAKE_EMPTY) | ((upper_bound as u32) << Self::INDEX_SHIFT);
    }

    pub(super) fn set_theory_constraint(&mut self, theory_index: usize) {
        debug_assert!(theory_index <= (u32::MAX >> Self::INDEX_SHIFT) as usize);
        self.0 = (self.0 & Self::TAKE_EMPTY)
            | Self::THEORY
            | ((theory_index as u32) << Self::INDEX_SHIFT);
    }

    pub(super) fn can_take_empty(self) -> bool {
        self.0 & Self::TAKE_EMPTY != 0
    }

    pub(super) fn has_theory_constraint(self) -> bool {
        self.0 & Self::THEORY != 0
    }

    pub(super) fn is_unbounded(self) -> bool {
        self.0 & !Self::TAKE_EMPTY == 0
    }

    pub(super) fn upper_bound(self) -> usize {
        if self.has_theory_constraint() {
            1
        } else {
            (self.0 >> Self::INDEX_SHIFT) as usize
        }
    }

    pub(super) fn theory_constraint(self) -> Option<usize> {
        self.has_theory_constraint()
            .then_some((self.0 >> Self::INDEX_SHIFT) as usize)
    }

    /// Update `self` to the meet of the two constraints. Returns false for a theory clash.
    pub(super) fn intersect(&mut self, other: Self) -> bool {
        if self.has_theory_constraint() {
            if other.has_theory_constraint() {
                if self.theory_constraint() == other.theory_constraint() {
                    self.0 &= other.0;
                    return true;
                }
                return false;
            }
            self.0 &= other.0 | !Self::TAKE_EMPTY;
            return true;
        }
        if other.has_theory_constraint() {
            self.0 = other.0 & (self.0 | !Self::TAKE_EMPTY);
            return true;
        }
        let mut upper_bound = self.0 >> Self::INDEX_SHIFT;
        let other_upper_bound = other.0 >> Self::INDEX_SHIFT;
        if other_upper_bound != 0 && (upper_bound == 0 || other_upper_bound < upper_bound) {
            upper_bound = other_upper_bound;
        }
        self.0 = (upper_bound << Self::INDEX_SHIFT) | (Self::TAKE_EMPTY & self.0 & other.0);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::VariableConstraint;

    #[test]
    fn packed_intersection_matches_theory_and_bound_semantics() {
        let mut a = VariableConstraint::default();
        a.set_take_empty();
        a.set_upper_bound(3);
        let mut b = VariableConstraint::default();
        b.set_upper_bound(2);
        assert!(a.intersect(b));
        assert_eq!(a.upper_bound(), 2);
        assert!(!a.can_take_empty());

        let mut t0 = VariableConstraint::default();
        t0.set_take_empty();
        t0.set_theory_constraint(7);
        assert!(t0.intersect(b));
        assert_eq!(t0.theory_constraint(), Some(7));
        assert!(!t0.can_take_empty());

        let mut t1 = VariableConstraint::default();
        t1.set_theory_constraint(8);
        assert!(!t0.intersect(t1));
    }
}
