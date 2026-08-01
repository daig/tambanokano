use super::bdd::{Bdd, BddContext};
use super::nat_set::NatSet;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::fmt::Write;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Transition {
    pub(crate) states: NatSet,
    pub(crate) formula: Bdd,
}

/// Canonical disjunction of labelled conjunctions of successor states.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TransitionSet {
    pub(crate) map: BTreeMap<NatSet, Bdd>,
}

impl TransitionSet {
    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub(crate) fn insert(&mut self, context: &BddContext, transition: Transition) {
        let Transition {
            states,
            mut formula,
        } = transition;
        if formula.is_false() {
            return;
        }

        let keys: Vec<NatSet> = self.map.keys().cloned().collect();
        let mut equal = false;
        for existing_states in keys {
            if existing_states == states {
                equal = true;
            } else if existing_states.contains_set(&states) {
                let existing_formula = self
                    .map
                    .get(&existing_states)
                    .expect("transition key disappeared");
                let trimmed = context.and_not(existing_formula, &formula);
                if trimmed.is_false() {
                    self.map.remove(&existing_states);
                } else {
                    self.map.insert(existing_states, trimmed);
                }
            } else if states.contains_set(&existing_states) {
                let existing_formula = self
                    .map
                    .get(&existing_states)
                    .expect("transition key disappeared");
                formula = context.and_not(&formula, existing_formula);
                if formula.is_false() {
                    return;
                }
            }
        }

        if equal {
            let existing = self.map.get(&states).expect("equal transition missing");
            formula = context.or(existing, &formula);
        }
        self.map.insert(states, formula);
    }

    pub(crate) fn insert_set(&mut self, context: &BddContext, other: &Self) {
        for (states, formula) in &other.map {
            self.insert(
                context,
                Transition {
                    states: states.clone(),
                    formula: formula.clone(),
                },
            );
        }
    }

    pub(crate) fn product(context: &BddContext, lhs: &Self, rhs: &Self) -> Self {
        let mut product = Self::default();
        for (lhs_states, lhs_formula) in &lhs.map {
            for (rhs_states, rhs_formula) in &rhs.map {
                let formula = context.and(lhs_formula, rhs_formula);
                if !formula.is_false() {
                    let mut states = lhs_states.clone();
                    states.union_with(rhs_states);
                    product.insert(context, Transition { states, formula });
                }
            }
        }
        product
    }

    pub(crate) fn renamed(&self, renaming: &[Option<usize>]) -> Self {
        let mut renamed = BTreeMap::new();
        for (states, formula) in &self.map {
            let mut new_states = NatSet::default();
            for state in states.iter() {
                new_states.insert(renaming[state].expect("reachable state has no renaming"));
            }
            assert!(
                renamed.insert(new_states, formula.clone()).is_none(),
                "state renaming is not injective"
            );
        }
        Self { map: renamed }
    }

    #[cfg(test)]
    pub(crate) fn dump(&self) -> String {
        let mut output = String::new();
        for (states, formula) in &self.map {
            writeln!(output, "{states}\t{formula}").expect("writing to String cannot fail");
        }
        output
    }
}

/// Unsimplified product input used while constructing generalized Büchi states.
#[derive(Clone, Default)]
pub(crate) struct RawTransitionSet {
    transitions: BTreeSet<Transition>,
}

impl RawTransitionSet {
    pub(crate) fn from_transition_set(transition_set: &TransitionSet) -> Self {
        let transitions = transition_set
            .map
            .iter()
            .map(|(states, formula)| Transition {
                states: states.clone(),
                formula: formula.clone(),
            })
            .collect();
        Self { transitions }
    }

    pub(crate) fn product(context: &BddContext, lhs: &Self, rhs: &Self) -> Self {
        let mut transitions = BTreeSet::new();
        for left in &lhs.transitions {
            for right in &rhs.transitions {
                let formula = context.and(&left.formula, &right.formula);
                if !formula.is_false() {
                    let mut states = left.states.clone();
                    states.union_with(&right.states);
                    transitions.insert(Transition { states, formula });
                }
            }
        }
        Self { transitions }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Transition> {
        self.transitions.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn states(elements: &[usize]) -> NatSet {
        elements.iter().copied().collect()
    }

    #[test]
    fn canonical_insert_tracks_subsumption_per_valuation() {
        let context = BddContext::new(1);
        let x = context.ithvar(0);
        let not_x = context.nithvar(0);
        let mut transitions = TransitionSet::default();

        transitions.insert(
            &context,
            Transition {
                states: states(&[0, 1]),
                formula: context.true_bdd(),
            },
        );
        transitions.insert(
            &context,
            Transition {
                states: states(&[0]),
                formula: x.clone(),
            },
        );
        assert_eq!(transitions.dump(), "{0}\tx0\n{0, 1}\t~x0\n");

        transitions.insert(
            &context,
            Transition {
                states: states(&[0, 1]),
                formula: x,
            },
        );
        assert_eq!(transitions.map.len(), 2, "subsumed insertion is ignored");

        transitions.insert(
            &context,
            Transition {
                states: states(&[0]),
                formula: not_x,
            },
        );
        assert_eq!(transitions.dump(), "{0}\ttrue\n");
    }

    #[test]
    fn product_and_raw_product_preserve_canonical_order() {
        let context = BddContext::new(2);
        let mut left = TransitionSet::default();
        left.insert(
            &context,
            Transition {
                states: states(&[2]),
                formula: context.ithvar(0),
            },
        );
        left.insert(
            &context,
            Transition {
                states: states(&[0]),
                formula: context.nithvar(0),
            },
        );
        let mut right = TransitionSet::default();
        right.insert(
            &context,
            Transition {
                states: states(&[1]),
                formula: context.ithvar(1),
            },
        );

        let canonical = TransitionSet::product(&context, &left, &right);
        assert_eq!(canonical.dump(), "{0, 1}\t~x0.(x1)\n{1, 2}\tx0.(x1)\n");
        let raw = RawTransitionSet::product(
            &context,
            &RawTransitionSet::from_transition_set(&left),
            &RawTransitionSet::from_transition_set(&right),
        );
        assert_eq!(raw.iter().count(), 2);
        assert_eq!(
            raw.iter()
                .map(|transition| transition.states.clone())
                .collect::<Vec<_>>(),
            vec![states(&[0, 1]), states(&[1, 2])]
        );
    }

    #[test]
    fn injective_rename_preserves_labels() {
        let context = BddContext::new(1);
        let mut transitions = TransitionSet::default();
        transitions.insert(
            &context,
            Transition {
                states: states(&[0, 2]),
                formula: context.ithvar(0),
            },
        );
        let renamed = transitions.renamed(&[Some(2), None, Some(0)]);
        assert_eq!(renamed.dump(), "{0, 2}\tx0\n");
    }
}
