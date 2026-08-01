use super::bdd::BddContext;
use super::formula::{FormulaId, FormulaKind, LogicFormula};
use super::nat_set::NatSet;
use super::transition::{Transition, TransitionSet};
#[cfg(test)]
use std::fmt::Write;

/// Gastin–Oddoux very weak alternating automaton used as the first LTL-to-Büchi stage, after
/// reachability renumbering.
pub(crate) struct VeryWeakAlternatingAutomaton<'a> {
    context: &'a BddContext,
    formula: &'a LogicFormula,
    initial_states: TransitionSet,
    states: Vec<TransitionSet>,
    final_states: Vec<usize>,
}

impl<'a> VeryWeakAlternatingAutomaton<'a> {
    pub(crate) fn new(context: &'a BddContext, formula: &'a LogicFormula, top: FormulaId) -> Self {
        let mut automaton = Self {
            context,
            formula,
            initial_states: TransitionSet::default(),
            states: vec![TransitionSet::default(); top + 1],
            final_states: Vec::new(),
        };
        let mut initial_states = TransitionSet::default();
        automaton.dnf(top, &mut initial_states);
        automaton.initial_states = initial_states;
        automaton.reachability_optimize();
        automaton
    }

    #[cfg(test)]
    pub(crate) fn state_count(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn final_state_count(&self) -> usize {
        self.final_states.len()
    }

    pub(crate) fn initial_states(&self) -> &TransitionSet {
        &self.initial_states
    }

    pub(crate) fn transition_set(&self, state: usize) -> &TransitionSet {
        &self.states[state]
    }

    fn dnf(&mut self, subformula: FormulaId, result: &mut TransitionSet) {
        match self.formula.node(subformula).kind {
            FormulaKind::And(lhs, rhs) => {
                let mut left = TransitionSet::default();
                self.dnf(lhs, &mut left);
                let mut right = TransitionSet::default();
                self.dnf(rhs, &mut right);
                *result = TransitionSet::product(self.context, &left, &right);
            }
            FormulaKind::Or(lhs, rhs) => {
                self.dnf(lhs, result);
                let mut right = TransitionSet::default();
                self.dnf(rhs, &mut right);
                result.insert_set(self.context, &right);
            }
            _ => {
                let mut states = NatSet::default();
                states.insert(subformula);
                result.insert(
                    self.context,
                    Transition {
                        states,
                        formula: self.context.true_bdd(),
                    },
                );
                self.compute_transition_set(subformula);
            }
        }
    }

    fn compute_transition_set(&mut self, subformula: FormulaId) {
        if !self.states[subformula].is_empty() {
            return;
        }

        let mut result = TransitionSet::default();
        match self.formula.node(subformula).kind {
            FormulaKind::Proposition(proposition) => {
                result.insert(
                    self.context,
                    Transition {
                        states: NatSet::default(),
                        formula: self.context.ithvar(proposition),
                    },
                );
            }
            FormulaKind::True => {
                result.insert(
                    self.context,
                    Transition {
                        states: NatSet::default(),
                        formula: self.context.true_bdd(),
                    },
                );
            }
            FormulaKind::False => {}
            FormulaKind::Not(argument) => {
                let FormulaKind::Proposition(proposition) = self.formula.node(argument).kind else {
                    unreachable!("negative-normal-form NOT must contain a proposition");
                };
                result.insert(
                    self.context,
                    Transition {
                        states: NatSet::default(),
                        formula: self.context.nithvar(proposition),
                    },
                );
            }
            FormulaKind::Next(argument) => self.dnf(argument, &mut result),
            FormulaKind::And(lhs, rhs) => {
                self.compute_transition_set(lhs);
                self.compute_transition_set(rhs);
                result = TransitionSet::product(self.context, &self.states[lhs], &self.states[rhs]);
            }
            FormulaKind::Or(lhs, rhs) => {
                self.compute_transition_set(lhs);
                self.compute_transition_set(rhs);
                result = self.states[lhs].clone();
                result.insert_set(self.context, &self.states[rhs]);
            }
            FormulaKind::Until(lhs, rhs) => {
                self.compute_transition_set(lhs);
                self.compute_transition_set(rhs);
                let mut self_loop = TransitionSet::default();
                let mut states = NatSet::default();
                states.insert(subformula);
                self_loop.insert(
                    self.context,
                    Transition {
                        states,
                        formula: self.context.true_bdd(),
                    },
                );
                result = TransitionSet::product(self.context, &self.states[lhs], &self_loop);
                result.insert_set(self.context, &self.states[rhs]);
                self.final_states.push(subformula);
            }
            FormulaKind::Release(lhs, rhs) => {
                self.compute_transition_set(lhs);
                self.compute_transition_set(rhs);
                let mut sum = self.states[lhs].clone();
                let mut states = NatSet::default();
                states.insert(subformula);
                sum.insert(
                    self.context,
                    Transition {
                        states,
                        formula: self.context.true_bdd(),
                    },
                );
                result = TransitionSet::product(self.context, &sum, &self.states[rhs]);
            }
        }
        self.states[subformula] = result;
    }

    fn reachability_optimize(&mut self) {
        let mut renaming = vec![None; self.states.len()];
        let mut next_state = 0;
        self.find_reachable(&self.initial_states.clone(), &mut renaming, &mut next_state);

        self.initial_states = self.initial_states.renamed(&renaming);
        let mut states = vec![TransitionSet::default(); next_state];
        for (old_state, new_state) in renaming.iter().copied().enumerate() {
            if let Some(new_state) = new_state {
                states[new_state] = self.states[old_state].renamed(&renaming);
            }
        }
        self.states = states;
        self.final_states = self
            .final_states
            .iter()
            .filter_map(|&state| renaming[state])
            .collect();
    }

    fn find_reachable(
        &self,
        transitions: &TransitionSet,
        renaming: &mut [Option<usize>],
        next_state: &mut usize,
    ) {
        for states in transitions.map.keys() {
            for state in states.iter() {
                if renaming[state].is_none() {
                    renaming[state] = Some(*next_state);
                    *next_state += 1;
                    self.find_reachable(&self.states[state], renaming, next_state);
                }
            }
        }
    }

    pub(crate) fn compute_fairness_set(&self, transition: &Transition) -> NatSet {
        let mut fairness = NatSet::default();
        for (index, &final_state) in self.final_states.iter().enumerate() {
            if self.check_fairness(transition, final_state) {
                fairness.insert(index);
            }
        }
        fairness
    }

    fn check_fairness(&self, transition: &Transition, final_state: usize) -> bool {
        if !transition.states.contains(final_state) {
            return true;
        }
        for (states, formula) in &self.states[final_state].map {
            if !states.contains(final_state)
                && transition.states.contains_set(states)
                && self.context.implies(&transition.formula, formula).is_true()
            {
                return true;
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn dump(&self) -> String {
        let mut output = String::from("begin{VeryWeakAlternatingAutomaton}\n");
        for (state, transitions) in self.states.iter().enumerate() {
            write!(output, "state {state}").expect("writing to String cannot fail");
            if self.final_states.contains(&state) {
                output.push_str("\tfinal");
            }
            output.push('\n');
            output.push_str(&transitions.dump());
            output.push('\n');
        }
        output.push_str("initial state conjunctions\n");
        output.push_str(&self.initial_states.dump());
        output.push_str("end{VeryWeakAlternatingAutomaton}\n");
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atom_and_negated_atom_use_opposite_transition_literals() {
        let context = BddContext::new(1);
        let mut atom = LogicFormula::default();
        let p = atom.make_proposition(0);
        let positive = VeryWeakAlternatingAutomaton::new(&context, &atom, p);
        assert_eq!(
            positive.dump(),
            "begin{VeryWeakAlternatingAutomaton}\nstate 0\n{}\tx0\n\ninitial state conjunctions\n{0}\ttrue\nend{VeryWeakAlternatingAutomaton}\n"
        );

        let not_p = atom.make_not(p);
        let negative = VeryWeakAlternatingAutomaton::new(&context, &atom, not_p);
        assert_eq!(
            negative.dump(),
            "begin{VeryWeakAlternatingAutomaton}\nstate 0\n{}\t~x0\n\ninitial state conjunctions\n{0}\ttrue\nend{VeryWeakAlternatingAutomaton}\n"
        );
    }

    #[test]
    fn next_until_release_and_boolean_folding_build_expected_shape() {
        let context = BddContext::new(2);
        let mut formula = LogicFormula::default();
        let p = formula.make_proposition(0);
        let q = formula.make_proposition(1);
        let next_q = formula.make_next(q);
        let until = formula.make_until(p, next_q);
        let release = formula.make_release(q, until);
        let top = formula.make_or(release, p);
        let automaton = VeryWeakAlternatingAutomaton::new(&context, &formula, top);

        assert_eq!(automaton.state_count(), 4);
        assert_eq!(automaton.final_state_count(), 1);
        assert_eq!(
            automaton.dump(),
            "begin{VeryWeakAlternatingAutomaton}\nstate 0\n{}\tx0\n\nstate 1\n{2}\tx1\n{1, 2}\t~x1\n{3}\tx0.(x1)\n{1, 3}\tx0.(~x1)\n\nstate 2\n{}\tx1\n\nstate 3\tfinal\n{2}\ttrue\n{3}\tx0\n\ninitial state conjunctions\n{0}\ttrue\n{1}\ttrue\nend{VeryWeakAlternatingAutomaton}\n"
        );
    }
}
