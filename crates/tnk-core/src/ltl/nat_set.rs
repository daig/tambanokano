use std::cmp::Ordering;
use std::fmt;

const BITS_PER_WORD: usize = u64::BITS as usize;

/// Dense natural-number set with Maude's `NatSet` representation and ordering.
///
/// The first machine word stays inline; `tail[0]` represents elements 64..127. Trailing zero
/// words are never retained, because their presence would change Maude's map ordering.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
pub(crate) struct NatSet {
    first: u64,
    tail: Vec<u64>,
}

impl NatSet {
    pub(crate) fn is_empty(&self) -> bool {
        self.first == 0 && self.tail.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.first.count_ones() as usize
            + self
                .tail
                .iter()
                .map(|word| word.count_ones() as usize)
                .sum::<usize>()
    }

    pub(crate) fn contains(&self, element: usize) -> bool {
        let word = element / BITS_PER_WORD;
        let mask = 1_u64 << (element % BITS_PER_WORD);
        if word == 0 {
            self.first & mask != 0
        } else {
            self.tail
                .get(word - 1)
                .is_some_and(|value| value & mask != 0)
        }
    }

    /// Whether this set is a (possibly equal) superset of `other`.
    pub(crate) fn contains_set(&self, other: &Self) -> bool {
        if self.first | other.first != self.first || other.tail.len() > self.tail.len() {
            return false;
        }
        other
            .tail
            .iter()
            .zip(&self.tail)
            .all(|(&other, &this)| this | other == this)
    }

    pub(crate) fn is_disjoint(&self, other: &Self) -> bool {
        self.first & other.first == 0
            && self
                .tail
                .iter()
                .zip(&other.tail)
                .all(|(&lhs, &rhs)| lhs & rhs == 0)
    }

    pub(crate) fn insert(&mut self, element: usize) {
        let word = element / BITS_PER_WORD;
        let mask = 1_u64 << (element % BITS_PER_WORD);
        if word == 0 {
            self.first |= mask;
        } else {
            if self.tail.len() < word {
                self.tail.resize(word, 0);
            }
            self.tail[word - 1] |= mask;
        }
    }

    pub(crate) fn union_with(&mut self, other: &Self) {
        self.first |= other.first;
        if self.tail.len() < other.tail.len() {
            self.tail.resize(other.tail.len(), 0);
        }
        for (this, &that) in self.tail.iter_mut().zip(&other.tail) {
            *this |= that;
        }
    }

    pub(crate) fn without(mut self, element: usize) -> Self {
        self.remove(element);
        self
    }

    pub(crate) fn remove(&mut self, element: usize) {
        let word = element / BITS_PER_WORD;
        let mask = 1_u64 << (element % BITS_PER_WORD);
        if word == 0 {
            self.first &= !mask;
        } else if let Some(value) = self.tail.get_mut(word - 1) {
            *value &= !mask;
            self.normalize();
        }
    }

    pub(crate) fn subtract(&mut self, other: &Self) {
        self.first &= !other.first;
        for (this, &that) in self.tail.iter_mut().zip(&other.tail) {
            *this &= !that;
        }
        self.normalize();
    }

    pub(crate) fn intersect(&mut self, other: &Self) {
        self.first &= other.first;
        let common = self.tail.len().min(other.tail.len());
        self.tail.truncate(common);
        for (this, &that) in self.tail.iter_mut().zip(&other.tail) {
            *this &= that;
        }
        self.normalize();
    }

    pub(crate) fn iter(&self) -> NatSetIter<'_> {
        NatSetIter {
            set: self,
            word_index: 0,
            remaining: self.first,
        }
    }

    fn normalize(&mut self) {
        while self.tail.last() == Some(&0) {
            self.tail.pop();
        }
    }
}

impl Ord for NatSet {
    fn cmp(&self, other: &Self) -> Ordering {
        self.tail
            .len()
            .cmp(&other.tail.len())
            .then_with(|| self.first.cmp(&other.first))
            .then_with(|| self.tail.cmp(&other.tail))
    }
}

impl PartialOrd for NatSet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for NatSet {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl fmt::Display for NatSet {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("{")?;
        for (position, element) in self.iter().enumerate() {
            if position != 0 {
                formatter.write_str(", ")?;
            }
            write!(formatter, "{element}")?;
        }
        formatter.write_str("}")
    }
}

pub(crate) struct NatSetIter<'a> {
    set: &'a NatSet,
    word_index: usize,
    remaining: u64,
}

impl Iterator for NatSetIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.remaining != 0 {
                let bit = self.remaining.trailing_zeros() as usize;
                self.remaining &= self.remaining - 1;
                return Some(self.word_index * BITS_PER_WORD + bit);
            }
            if self.word_index >= self.set.tail.len() {
                return None;
            }
            self.remaining = self.set.tail[self.word_index];
            self.word_index += 1;
        }
    }
}

impl FromIterator<usize> for NatSet {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let mut set = Self::default();
        for element in iter {
            set.insert(element);
        }
        set
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(elements: &[usize]) -> NatSet {
        elements.iter().copied().collect()
    }

    #[test]
    fn dense_operations_normalize_trailing_words() {
        let mut values = set(&[0, 63, 64, 129]);
        assert_eq!(values.len(), 4);
        assert_eq!(values.iter().collect::<Vec<_>>(), vec![0, 63, 64, 129]);
        assert!(values.contains_set(&set(&[63, 129])));
        assert!(values.is_disjoint(&set(&[1, 65, 130])));

        values.remove(129);
        values.subtract(&set(&[64]));
        assert_eq!(values, set(&[0, 63]));
        assert_eq!(values.tail, Vec::<u64>::new());

        values.union_with(&set(&[65, 130]));
        values.intersect(&set(&[63, 65, 129]));
        assert_eq!(values, set(&[63, 65]));
        assert_eq!(values.to_string(), "{63, 65}");
    }

    #[test]
    fn ordering_is_word_length_then_words_low_to_high() {
        let mut values = vec![
            set(&[1, 64]),
            set(&[0, 65]),
            set(&[64]),
            set(&[63]),
            set(&[0]),
            NatSet::default(),
        ];
        values.sort();
        assert_eq!(
            values,
            vec![
                NatSet::default(),
                set(&[0]),
                set(&[63]),
                set(&[64]),
                set(&[0, 65]),
                set(&[1, 64]),
            ]
        );
    }
}
