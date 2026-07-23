use super::bdd::{Bdd, BddContext};
use super::buchi::BuchiAutomaton;
use super::formula::{FormulaId, LogicFormula};
use super::nat_set::NatSet;
use std::collections::VecDeque;

/// Ordinal successor and proposition access for the synchronous product checker.
pub(crate) trait System {
    /// Return successor `transition`, or `None` once all successors have been enumerated.
    fn get_next_state(&mut self, state: usize, transition: usize) -> Option<usize>;

    fn check_proposition(&mut self, state: usize, proposition: usize) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Counterexample {
    pub(crate) lead_in: Vec<usize>,
    pub(crate) cycle: Vec<usize>,
}

/// Holzmann–Peled–Yannakakis nested DFS over a system/property synchronous product.
pub(crate) struct ModelChecker<'a, S: System> {
    system: &'a mut S,
    property: BuchiAutomaton,
}

impl<'a, S: System> ModelChecker<'a, S> {
    pub(crate) fn new(
        system: &'a mut S,
        context: &BddContext,
        property: &LogicFormula,
        top: FormulaId,
    ) -> Self {
        Self {
            system,
            property: BuchiAutomaton::new(context, property, top),
        }
    }

    pub(crate) fn property_state_count(&self) -> usize {
        self.property.state_count()
    }

    pub(crate) fn find_counterexample(&mut self) -> Option<Counterexample> {
        let mut search = Search {
            system: &mut *self.system,
            intersection_states: vec![StateSet::default()],
            cycle_state: None,
            path: VecDeque::new(),
            cycle: VecDeque::new(),
        };
        let found = self.property.initial_states().iter().any(|property_state| {
            search.dfs1_property_transitions(&self.property, 0, property_state)
        });
        found.then(|| Counterexample {
            lead_in: search.path.into_iter().collect(),
            cycle: search.cycle.into_iter().collect(),
        })
    }
}

#[derive(Default)]
struct StateSet {
    dfs1_seen: NatSet,
    on_dfs1_stack: NatSet,
    dfs2_seen: NatSet,
    tested_propositions: NatSet,
    true_propositions: NatSet,
}

struct Search<'a, S: System> {
    system: &'a mut S,
    intersection_states: Vec<StateSet>,
    cycle_state: Option<(usize, usize)>,
    path: VecDeque<usize>,
    cycle: VecDeque<usize>,
}

impl<S: System> Search<'_, S> {
    fn dfs1_system_transitions(
        &mut self,
        property: &BuchiAutomaton,
        system_state: usize,
        property_state: usize,
    ) -> bool {
        self.intersection_states[system_state]
            .dfs1_seen
            .insert(property_state);
        for transition in 0.. {
            let Some(next) = self.system.get_next_state(system_state, transition) else {
                break;
            };
            if next >= self.intersection_states.len() {
                self.intersection_states
                    .resize_with(next + 1, StateSet::default);
            }
            if self.dfs1_property_transitions(property, next, property_state) {
                return true;
            }
        }
        false
    }

    fn dfs1_property_transitions(
        &mut self,
        property: &BuchiAutomaton,
        system_state: usize,
        property_state: usize,
    ) -> bool {
        for (&new_property_state, formula) in property.transitions(property_state) {
            if self.satisfies_propositional_formula(system_state, formula)
                && !self.intersection_states[system_state]
                    .dfs1_seen
                    .contains(new_property_state)
            {
                self.intersection_states[system_state]
                    .on_dfs1_stack
                    .insert(new_property_state);
                if self.dfs1_system_transitions(property, system_state, new_property_state)
                    || (property.is_accepting(new_property_state)
                        && self.dfs2_system_transitions(property, system_state, new_property_state))
                {
                    self.path.push_front(system_state);
                    if self.cycle_state == Some((system_state, new_property_state)) {
                        std::mem::swap(&mut self.cycle, &mut self.path);
                    }
                    return true;
                }
                self.intersection_states[system_state]
                    .on_dfs1_stack
                    .remove(new_property_state);
            }
        }
        false
    }

    fn dfs2_system_transitions(
        &mut self,
        property: &BuchiAutomaton,
        system_state: usize,
        property_state: usize,
    ) -> bool {
        self.intersection_states[system_state]
            .dfs2_seen
            .insert(property_state);
        for transition in 0.. {
            let Some(next) = self.system.get_next_state(system_state, transition) else {
                break;
            };
            assert!(
                next < self.intersection_states.len(),
                "DFS2 discovered a new system state"
            );
            if self.dfs2_property_transitions(property, next, property_state) {
                return true;
            }
        }
        false
    }

    fn dfs2_property_transitions(
        &mut self,
        property: &BuchiAutomaton,
        system_state: usize,
        property_state: usize,
    ) -> bool {
        for (&new_property_state, formula) in property.transitions(property_state) {
            if self.satisfies_propositional_formula(system_state, formula) {
                if self.intersection_states[system_state]
                    .on_dfs1_stack
                    .contains(new_property_state)
                {
                    self.cycle_state = Some((system_state, new_property_state));
                    return true;
                }
                if !self.intersection_states[system_state]
                    .dfs2_seen
                    .contains(new_property_state)
                    && self.dfs2_system_transitions(property, system_state, new_property_state)
                {
                    self.path.push_front(system_state);
                    return true;
                }
            }
        }
        false
    }

    fn satisfies_propositional_formula(&mut self, system_state: usize, formula: &Bdd) -> bool {
        let mut node = formula.root();
        loop {
            if formula.is_one(node) {
                return true;
            }
            if formula.is_zero(node) {
                return false;
            }
            let proposition = formula
                .variable(node)
                .expect("nonterminal BDD node has a variable");
            let known = self.intersection_states[system_state]
                .tested_propositions
                .contains(proposition);
            let is_true = if known {
                self.intersection_states[system_state]
                    .true_propositions
                    .contains(proposition)
            } else {
                self.intersection_states[system_state]
                    .tested_propositions
                    .insert(proposition);
                let is_true = self.system.check_proposition(system_state, proposition);
                if is_true {
                    self.intersection_states[system_state]
                        .true_propositions
                        .insert(proposition);
                }
                is_true
            };
            node = if is_true {
                formula.high(node).expect("nonterminal BDD node")
            } else {
                formula.low(node).expect("nonterminal BDD node")
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestSystem {
        successors: Vec<Vec<usize>>,
        propositions: Vec<Vec<bool>>,
        successor_calls: Vec<(usize, usize)>,
        proposition_calls: Vec<(usize, usize)>,
    }

    impl TestSystem {
        fn new(successors: Vec<Vec<usize>>, propositions: Vec<Vec<bool>>) -> Self {
            assert_eq!(successors.len(), propositions.len());
            Self {
                successors,
                propositions,
                successor_calls: Vec::new(),
                proposition_calls: Vec::new(),
            }
        }
    }

    impl System for TestSystem {
        fn get_next_state(&mut self, state: usize, transition: usize) -> Option<usize> {
            self.successor_calls.push((state, transition));
            self.successors[state].get(transition).copied()
        }

        fn check_proposition(&mut self, state: usize, proposition: usize) -> bool {
            self.proposition_calls.push((state, proposition));
            self.propositions[state][proposition]
        }
    }

    fn check(
        system: &mut TestSystem,
        formula: &LogicFormula,
        top: FormulaId,
        proposition_count: usize,
    ) -> (usize, Option<Counterexample>) {
        let context = BddContext::new(proposition_count);
        let mut checker = ModelChecker::new(system, &context, formula, top);
        let state_count = checker.property_state_count();
        (state_count, checker.find_counterexample())
    }

    #[test]
    fn disabled_property_transition_has_no_counterexample() {
        let mut formula = LogicFormula::default();
        let top = formula.make_proposition(0);
        let mut system = TestSystem::new(vec![vec![0]], vec![vec![false]]);
        let (property_states, counterexample) = check(&mut system, &formula, top, 1);

        assert_eq!(property_states, 2);
        assert_eq!(counterexample, None);
        assert_eq!(system.proposition_calls, vec![(0, 0)]);
        assert!(system.successor_calls.is_empty());
    }

    #[test]
    fn accepting_self_loop_has_nil_lead_in() {
        let mut formula = LogicFormula::default();
        let top = formula.make_true();
        let mut system = TestSystem::new(vec![vec![0]], vec![vec![]]);
        let (_, counterexample) = check(&mut system, &formula, top, 0);

        assert_eq!(
            counterexample,
            Some(Counterexample {
                lead_in: vec![],
                cycle: vec![0],
            })
        );
    }

    #[test]
    fn lead_in_and_multi_state_cycle_are_partitioned_exactly() {
        let mut formula = LogicFormula::default();
        let top = formula.make_true();
        let mut system = TestSystem::new(
            vec![vec![1], vec![2], vec![1]],
            vec![vec![], vec![], vec![]],
        );
        let (_, counterexample) = check(&mut system, &formula, top, 0);

        assert_eq!(
            counterexample,
            Some(Counterexample {
                lead_in: vec![0],
                cycle: vec![1, 2],
            })
        );
    }

    #[test]
    fn ordinal_successor_order_selects_the_first_accepting_branch() {
        let mut formula = LogicFormula::default();
        let top = formula.make_true();
        let mut system = TestSystem::new(
            vec![vec![1, 2], vec![1], vec![2]],
            vec![vec![], vec![], vec![]],
        );
        let (_, counterexample) = check(&mut system, &formula, top, 0);

        assert_eq!(
            counterexample,
            Some(Counterexample {
                lead_in: vec![0],
                cycle: vec![1],
            })
        );
        assert_eq!(system.successor_calls, vec![(0, 0), (1, 0), (1, 1), (1, 0)]);
    }

    #[test]
    fn bdd_walk_is_lazy_and_memoized_per_system_state() {
        let mut formula = LogicFormula::default();
        let p = formula.make_proposition(0);
        let q = formula.make_proposition(1);
        let top = formula.make_and(p, q);

        let mut false_at_first = TestSystem::new(vec![vec![0]], vec![vec![false, true]]);
        let (_, counterexample) = check(&mut false_at_first, &formula, top, 2);
        assert_eq!(counterexample, None);
        assert_eq!(false_at_first.proposition_calls, vec![(0, 0)]);

        let mut both_true = TestSystem::new(vec![vec![0]], vec![vec![true, true]]);
        let (_, counterexample) = check(&mut both_true, &formula, top, 2);
        assert!(counterexample.is_some());
        assert_eq!(both_true.proposition_calls, vec![(0, 0), (0, 1)]);
    }
}
