use super::bdd::{Bdd, BddContext};
use super::formula::{FormulaId, LogicFormula};
use super::nat_set::NatSet;
use super::transition::{RawTransitionSet, Transition};
use super::vwaa::VeryWeakAlternatingAutomaton;
use std::collections::BTreeMap;
#[cfg(test)]
use std::fmt::Write;
use std::rc::Rc;

#[derive(Clone)]
pub(super) struct IndexedSet<T: Ord> {
    elements: Vec<Rc<T>>,
    index: BTreeMap<Rc<T>, usize>,
}

impl<T: Ord> Default for IndexedSet<T> {
    fn default() -> Self {
        Self {
            elements: Vec::new(),
            index: BTreeMap::new(),
        }
    }
}

impl<T: Ord> IndexedSet<T> {
    pub(super) fn insert(&mut self, element: T) -> usize {
        if let Some(index) = self.index.get(&element) {
            return *index;
        }
        let index = self.elements.len();
        let element = Rc::new(element);
        self.index.insert(Rc::clone(&element), index);
        self.elements.push(element);
        index
    }

    pub(super) fn get(&self, index: usize) -> &T {
        &self.elements[index]
    }

    pub(super) fn len(&self) -> usize {
        self.elements.len()
    }
}

pub(crate) type FairTransitionKey = (usize, usize);
pub(crate) type FairTransitionSet = BTreeMap<FairTransitionKey, Bdd>;

/// Transition-fair generalized Büchi automaton used by both model checking and SAT solving.
pub(crate) struct GenBuchiAutomaton<'a> {
    pub(super) context: &'a BddContext,
    pub(super) initial_states: NatSet,
    pub(super) states: Vec<Option<usize>>,
    pub(super) fair_transition_sets: IndexedSet<FairTransitionSet>,
    pub(super) nr_fairness_sets: usize,
    pub(super) fairness_conditions: IndexedSet<NatSet>,
    pub(super) all_fair: NatSet,
}

impl<'a> GenBuchiAutomaton<'a> {
    pub(crate) fn new(context: &'a BddContext, formula: &'a LogicFormula, top: FormulaId) -> Self {
        let vwaa = VeryWeakAlternatingAutomaton::new(context, formula, top);
        let nr_fairness_sets = vwaa.final_state_count();
        let mut all_fair = NatSet::default();
        for fairness in (0..nr_fairness_sets).rev() {
            all_fair.insert(fairness);
        }
        let mut automaton = Self {
            context,
            initial_states: NatSet::default(),
            states: Vec::new(),
            fair_transition_sets: IndexedSet::default(),
            nr_fairness_sets,
            fairness_conditions: IndexedSet::default(),
            all_fair,
        };
        let mut vwaa_state_sets = IndexedSet::<NatSet>::default();

        let initial: Vec<NatSet> = vwaa.initial_states().map.keys().cloned().collect();
        for state_set in initial {
            let state = Self::state_index(&mut automaton.states, &mut vwaa_state_sets, state_set);
            automaton.initial_states.insert(state);
            automaton.generate_state(state, &vwaa, &mut vwaa_state_sets);
        }
        automaton
    }

    fn state_index(
        states: &mut Vec<Option<usize>>,
        state_sets: &mut IndexedSet<NatSet>,
        state_set: NatSet,
    ) -> usize {
        let index = state_sets.insert(state_set);
        if index == states.len() {
            states.push(None);
        }
        index
    }

    fn generate_state(
        &mut self,
        index: usize,
        vwaa: &VeryWeakAlternatingAutomaton<'_>,
        vwaa_state_sets: &mut IndexedSet<NatSet>,
    ) {
        if self.states[index].is_some() {
            return;
        }
        let components = vwaa_state_sets.get(index).clone();
        if components.is_empty() {
            let fairness = self.fairness_conditions.insert(self.all_fair.clone());
            let mut transitions = FairTransitionSet::new();
            self.insert_fair_transition(
                &mut transitions,
                (index, fairness),
                self.context.true_bdd(),
                vwaa_state_sets,
            );
            self.states[index] = Some(self.fair_transition_sets.insert(transitions));
            return;
        }

        let mut component_iter = components.iter();
        let first = component_iter.next().expect("nonempty VWAA state set");
        let mut product = RawTransitionSet::from_transition_set(vwaa.transition_set(first));
        for component in component_iter {
            let next = RawTransitionSet::from_transition_set(vwaa.transition_set(component));
            product = RawTransitionSet::product(self.context, &product, &next);
        }

        let raw_transitions: Vec<Transition> = product.iter().cloned().collect();
        let mut transitions = FairTransitionSet::new();
        for transition in raw_transitions {
            let fairness = vwaa.compute_fairness_set(&transition);
            let target =
                Self::state_index(&mut self.states, vwaa_state_sets, transition.states.clone());
            let fairness = self.fairness_conditions.insert(fairness);
            self.insert_fair_transition(
                &mut transitions,
                (target, fairness),
                transition.formula,
                vwaa_state_sets,
            );
        }
        self.states[index] = Some(self.fair_transition_sets.insert(transitions.clone()));

        let targets: Vec<usize> = transitions.keys().map(|key| key.0).collect();
        for target in targets {
            self.generate_state(target, vwaa, vwaa_state_sets);
        }
    }

    fn insert_fair_transition(
        &self,
        transitions: &mut FairTransitionSet,
        key: FairTransitionKey,
        mut formula: Bdd,
        vwaa_state_sets: &IndexedSet<NatSet>,
    ) {
        assert!(!formula.is_false(), "cannot insert a false transition");
        let keys: Vec<FairTransitionKey> = transitions.keys().copied().collect();
        let mut equal = false;
        for existing_key in keys {
            if existing_key == key {
                equal = true;
                continue;
            }
            let existing_states = vwaa_state_sets.get(existing_key.0);
            let existing_fairness = self.fairness_conditions.get(existing_key.1);
            let new_states = vwaa_state_sets.get(key.0);
            let new_fairness = self.fairness_conditions.get(key.1);
            if existing_states.contains_set(new_states)
                && new_fairness.contains_set(existing_fairness)
            {
                let existing_formula = transitions
                    .get(&existing_key)
                    .expect("fair transition disappeared");
                let trimmed = self.context.and_not(existing_formula, &formula);
                if trimmed.is_false() {
                    transitions.remove(&existing_key);
                } else {
                    transitions.insert(existing_key, trimmed);
                }
            } else if new_states.contains_set(existing_states)
                && existing_fairness.contains_set(new_fairness)
            {
                let existing_formula = transitions
                    .get(&existing_key)
                    .expect("fair transition disappeared");
                formula = self.context.and_not(&formula, existing_formula);
                if formula.is_false() {
                    return;
                }
            }
        }
        if equal {
            let existing = transitions
                .get(&key)
                .expect("equal fair transition missing");
            formula = self.context.or(existing, &formula);
        }
        transitions.insert(key, formula);
    }

    pub(super) fn insert_fair_transition2(
        &self,
        transitions: &mut FairTransitionSet,
        key: FairTransitionKey,
        mut formula: Bdd,
    ) {
        assert!(!formula.is_false(), "cannot insert a false transition");
        let keys: Vec<FairTransitionKey> = transitions.keys().copied().collect();
        let mut equal = false;
        for existing_key in keys {
            if existing_key == key {
                equal = true;
            } else if existing_key.0 == key.0 {
                let existing_fairness = self.fairness_conditions.get(existing_key.1);
                let new_fairness = self.fairness_conditions.get(key.1);
                if new_fairness.contains_set(existing_fairness) {
                    let existing_formula = transitions
                        .get(&existing_key)
                        .expect("fair transition disappeared");
                    let trimmed = self.context.and_not(existing_formula, &formula);
                    if trimmed.is_false() {
                        transitions.remove(&existing_key);
                    } else {
                        transitions.insert(existing_key, trimmed);
                    }
                } else if existing_fairness.contains_set(new_fairness) {
                    let existing_formula = transitions
                        .get(&existing_key)
                        .expect("fair transition disappeared");
                    formula = self.context.and_not(&formula, existing_formula);
                    if formula.is_false() {
                        return;
                    }
                }
            }
        }
        if equal {
            let existing = transitions
                .get(&key)
                .expect("equal fair transition missing");
            formula = self.context.or(existing, &formula);
        }
        transitions.insert(key, formula);
    }

    pub(crate) fn simplify(&mut self) {
        self.maximally_collapse_states();
        self.scc_optimizations();
        self.maximally_collapse_states();
    }

    pub(super) fn maximally_collapse_states(&mut self) {
        while self.fair_transition_sets.len() < self.states.len() {
            self.collapse_states();
        }
    }

    fn collapse_states(&mut self) {
        let new_state_count = self.fair_transition_sets.len();
        let state_map = self.states.clone();
        let mut new_initial_states = NatSet::default();
        Self::remap_nat_set(&mut new_initial_states, &self.initial_states, &state_map);
        let originals: Vec<FairTransitionSet> = (0..new_state_count)
            .map(|index| self.fair_transition_sets.get(index).clone())
            .collect();
        let mut new_states = vec![None; new_state_count];
        let mut new_transition_sets = IndexedSet::default();
        for (index, original) in originals.into_iter().enumerate() {
            let transformed = self.transform_fair_transition_set(&original, &state_map);
            new_states[index] = Some(new_transition_sets.insert(transformed));
        }
        self.initial_states = new_initial_states;
        self.states = new_states;
        self.fair_transition_sets = new_transition_sets;
    }

    fn transform_fair_transition_set(
        &self,
        original: &FairTransitionSet,
        state_map: &[Option<usize>],
    ) -> FairTransitionSet {
        let mut transformed = FairTransitionSet::new();
        for (&(target, fairness), formula) in original {
            self.insert_fair_transition2(
                &mut transformed,
                (state_map[target].expect("generated target state"), fairness),
                formula.clone(),
            );
        }
        transformed
    }

    pub(super) fn remap_nat_set(new_set: &mut NatSet, old_set: &NatSet, mapping: &[Option<usize>]) {
        for old in (0..mapping.len()).rev() {
            if let Some(new) = mapping[old] {
                if old_set.contains(old) {
                    new_set.insert(new);
                }
            }
        }
    }

    pub(crate) fn state_count(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn fairness_set_count(&self) -> usize {
        self.nr_fairness_sets
    }

    pub(crate) fn initial_states(&self) -> &NatSet {
        &self.initial_states
    }

    pub(crate) fn fairness_combination(&self, index: usize) -> &NatSet {
        self.fairness_conditions.get(index)
    }

    pub(crate) fn transitions(&self, state: usize) -> &FairTransitionSet {
        self.fair_transition_sets
            .get(self.states[state].expect("generated GBA state"))
    }

    #[cfg(test)]
    pub(crate) fn dump(&self) -> String {
        let mut output = String::from("begin{GenBuchiAutomaton}\n");
        for (state, transition_set) in self.states.iter().enumerate() {
            writeln!(
                output,
                "state {state}\t({})",
                transition_set
                    .map(|index| index.to_string())
                    .unwrap_or_else(|| "-1".to_string())
            )
            .expect("writing to String cannot fail");
            if let Some(transition_set) = transition_set {
                for (&(target, fairness), formula) in self.fair_transition_sets.get(*transition_set)
                {
                    writeln!(
                        output,
                        "{target}\t{}\t{formula}",
                        self.fairness_conditions.get(fairness)
                    )
                    .expect("writing to String cannot fail");
                }
            }
            output.push('\n');
        }
        writeln!(output, "initial states: {}", self.initial_states)
            .expect("writing to String cannot fail");
        output.push_str("\nend{GenBuchiAutomaton}\n");
        output
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StateSlot {
    Absent,
    Generating,
    Map(usize),
}

pub(crate) type BuchiTransitionMap = BTreeMap<usize, Bdd>;

/// Degeneralized and maximally collapsed Büchi automaton.
pub(crate) struct BuchiAutomaton {
    initial_states: NatSet,
    accepting_states: NatSet,
    states: Vec<StateSlot>,
    transition_maps: IndexedSet<BuchiTransitionMap>,
}

impl BuchiAutomaton {
    pub(crate) fn new(context: &BddContext, formula: &LogicFormula, top: FormulaId) -> Self {
        let mut generalized = GenBuchiAutomaton::new(context, formula, top);
        generalized.simplify();
        let mut automaton = Self::from_generalized(&generalized);
        if automaton.transition_maps.len() < automaton.states.len() {
            loop {
                let old_count = automaton.states.len();
                automaton.collapse_states(context);
                if automaton.states.len() >= old_count {
                    break;
                }
            }
        }
        automaton
    }

    fn from_generalized(generalized: &GenBuchiAutomaton<'_>) -> Self {
        let old_state_count = generalized.state_count();
        if old_state_count == 0 {
            return Self {
                initial_states: NatSet::default(),
                accepting_states: NatSet::default(),
                states: Vec::new(),
                transition_maps: IndexedSet::default(),
            };
        }

        let initial_states = generalized.initial_states.clone();
        let fairness_count = generalized.nr_fairness_sets;
        let mut automaton = Self {
            initial_states,
            accepting_states: NatSet::default(),
            states: vec![StateSlot::Absent; old_state_count * (fairness_count + 1)],
            transition_maps: IndexedSet::default(),
        };
        let initial: Vec<usize> = automaton.initial_states.iter().collect();
        for state in initial {
            automaton.generate(generalized, state, 0);
        }
        automaton
    }

    fn generate(&mut self, generalized: &GenBuchiAutomaton<'_>, old_state: usize, instance: usize) {
        let fairness_count = generalized.nr_fairness_sets;
        let old_state_count = generalized.states.len();
        let state = old_state + instance * old_state_count;
        self.states[state] = StateSlot::Generating;

        let mut transitions = BuchiTransitionMap::new();
        for (&(old_target, fairness_index), formula) in generalized.transitions(old_state) {
            let fairness = generalized.fairness_conditions.get(fairness_index);
            let mut next_instance = if instance == fairness_count {
                0
            } else {
                instance
            };
            while fairness.contains(next_instance) {
                next_instance += 1;
            }
            let target = old_target + next_instance * old_state_count;
            Self::insert_transition(
                &mut transitions,
                target,
                formula.clone(),
                generalized.context,
            );
            if self.states[target] == StateSlot::Absent {
                self.generate(generalized, old_target, next_instance);
            }
        }
        self.states[state] = StateSlot::Map(self.transition_maps.insert(transitions));
        if instance == fairness_count {
            self.accepting_states.insert(state);
        }
    }

    fn insert_transition(
        transitions: &mut BuchiTransitionMap,
        target: usize,
        formula: Bdd,
        context: &BddContext,
    ) {
        if let Some(existing) = transitions.get(&target) {
            let formula = context.or(existing, &formula);
            transitions.insert(target, formula);
        } else {
            transitions.insert(target, formula);
        }
    }

    fn collapse_states(&mut self, context: &BddContext) {
        let mut used_by_accepting = NatSet::default();
        let mut used_by_nonaccepting = NatSet::default();
        for (state, slot) in self.states.iter().copied().enumerate() {
            if let StateSlot::Map(map) = slot {
                if self.accepting_states.contains(state) {
                    used_by_accepting.insert(map);
                } else {
                    used_by_nonaccepting.insert(map);
                }
            }
        }
        used_by_accepting.intersect(&used_by_nonaccepting);

        let map_count = self.transition_maps.len();
        let mut accepting_map = vec![None; map_count];
        let mut fresh_count = map_count;
        for (index, replacement) in accepting_map.iter_mut().enumerate() {
            if used_by_accepting.contains(index)
                && self.has_nonaccepting_target(self.transition_maps.get(index))
            {
                *replacement = Some(fresh_count);
                fresh_count += 1;
            }
        }
        for (state, slot) in self.states.iter_mut().enumerate() {
            if self.accepting_states.contains(state) {
                let StateSlot::Map(map) = *slot else {
                    unreachable!("accepting state is generated");
                };
                if let Some(replacement) = accepting_map[map] {
                    *slot = StateSlot::Map(replacement);
                }
            }
        }

        let state_map: Vec<Option<usize>> = self
            .states
            .iter()
            .map(|slot| match slot {
                StateSlot::Map(map) => Some(*map),
                StateSlot::Absent | StateSlot::Generating => None,
            })
            .collect();
        let mut new_initial_states = NatSet::default();
        let mut new_accepting_states = NatSet::default();
        GenBuchiAutomaton::remap_nat_set(&mut new_initial_states, &self.initial_states, &state_map);
        GenBuchiAutomaton::remap_nat_set(
            &mut new_accepting_states,
            &self.accepting_states,
            &state_map,
        );

        let originals: Vec<BuchiTransitionMap> = (0..map_count)
            .map(|index| self.transition_maps.get(index).clone())
            .collect();
        let mut new_states = vec![StateSlot::Absent; fresh_count];
        let mut new_transition_maps = IndexedSet::default();
        for (index, original) in originals.into_iter().enumerate() {
            let mut transformed = BuchiTransitionMap::new();
            for (target, formula) in original {
                Self::insert_transition(
                    &mut transformed,
                    state_map[target].expect("transition target is generated"),
                    formula,
                    context,
                );
            }
            new_states[index] = StateSlot::Map(new_transition_maps.insert(transformed));
            if let Some(copy) = accepting_map[index] {
                new_states[copy] = new_states[index];
            }
        }

        self.initial_states = new_initial_states;
        self.accepting_states = new_accepting_states;
        self.states = new_states;
        self.transition_maps = new_transition_maps;
    }

    fn has_nonaccepting_target(&self, transitions: &BuchiTransitionMap) -> bool {
        transitions
            .keys()
            .any(|&target| !self.accepting_states.contains(target))
    }

    pub(crate) fn state_count(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn initial_states(&self) -> &NatSet {
        &self.initial_states
    }

    pub(crate) fn is_accepting(&self, state: usize) -> bool {
        self.accepting_states.contains(state)
    }

    pub(crate) fn transitions(&self, state: usize) -> &BuchiTransitionMap {
        let StateSlot::Map(map) = self.states[state] else {
            panic!("requested transitions of an ungenerated Büchi state");
        };
        self.transition_maps.get(map)
    }

    #[cfg(test)]
    pub(crate) fn dump(&self) -> String {
        let mut output = String::from("begin{BuchiAutomaton2}\n");
        for state in 0..self.states.len() {
            write!(output, "state {state}").expect("writing to String cannot fail");
            if self.accepting_states.contains(state) {
                output.push_str("\taccepting");
            }
            output.push('\n');
            if let StateSlot::Map(map) = self.states[state] {
                for (target, formula) in self.transition_maps.get(map) {
                    writeln!(output, "{target}\t{formula}").expect("writing to String cannot fail");
                }
            }
            output.push('\n');
        }
        writeln!(output, "initial states: {}", self.initial_states)
            .expect("writing to String cannot fail");
        output.push_str("end{BuchiAutomaton2}\n");
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complex_formula() -> (LogicFormula, FormulaId) {
        let mut formula = LogicFormula::default();
        let p = formula.make_proposition(0);
        let q = formula.make_proposition(1);
        let next_q = formula.make_next(q);
        let until = formula.make_until(p, next_q);
        let release = formula.make_release(q, until);
        let top = formula.make_or(release, p);
        (formula, top)
    }

    #[test]
    fn generalized_pipeline_matches_each_instrumented_reference_stage() {
        let context = BddContext::new(2);
        let (formula, top) = complex_formula();
        let mut automaton = GenBuchiAutomaton::new(&context, &formula, top);
        assert_eq!(
            automaton.dump(),
            "begin{GenBuchiAutomaton}\nstate 0\t(0)\n1\t{0}\tx0\n\nstate 1\t(1)\n1\t{0}\ttrue\n\nstate 2\t(2)\n3\t{0}\tx1\n4\t{0}\t~x1\n5\t{}\tx0.(x1)\n6\t{}\tx0.(~x1)\n\nstate 3\t(3)\n1\t{0}\tx1\n\nstate 4\t(4)\n3\t{0}\tx1\n5\t{}\tx0.(x1)\n\nstate 5\t(5)\n3\t{0}\ttrue\n5\t{}\tx0\n\nstate 6\t(2)\n3\t{0}\tx1\n4\t{0}\t~x1\n5\t{}\tx0.(x1)\n6\t{}\tx0.(~x1)\n\nstate 7\t(-1)\n\nstate 8\t(-1)\n\ninitial states: {0, 2}\n\nend{GenBuchiAutomaton}\n"
        );

        automaton.maximally_collapse_states();
        assert_eq!(
            automaton.dump(),
            "begin{GenBuchiAutomaton}\nstate 0\t(0)\n1\t{0}\tx0\n\nstate 1\t(1)\n1\t{0}\ttrue\n\nstate 2\t(2)\n2\t{}\tx0.(~x1)\n3\t{0}\tx1\n4\t{0}\t~x1\n5\t{}\tx0.(x1)\n\nstate 3\t(3)\n1\t{0}\tx1\n\nstate 4\t(4)\n3\t{0}\tx1\n5\t{}\tx0.(x1)\n\nstate 5\t(5)\n3\t{0}\ttrue\n5\t{}\tx0\n\ninitial states: {0, 2}\n\nend{GenBuchiAutomaton}\n"
        );

        automaton.scc_optimizations();
        automaton.maximally_collapse_states();
        assert_eq!(
            automaton.dump(),
            "begin{GenBuchiAutomaton}\nstate 0\t(0)\n1\t{}\tx0\n\nstate 1\t(1)\n1\t{0}\ttrue\n\nstate 2\t(2)\n2\t{}\tx0.(~x1)\n3\t{}\tx1\n4\t{}\t~x1\n5\t{}\tx0.(x1)\n\nstate 3\t(3)\n1\t{}\tx1\n\nstate 4\t(4)\n3\t{}\tx1\n5\t{}\tx0.(x1)\n\nstate 5\t(5)\n3\t{}\ttrue\n5\t{}\tx0\n\ninitial states: {0, 2}\n\nend{GenBuchiAutomaton}\n"
        );
    }

    #[test]
    fn degeneralization_and_each_collapse_match_instrumented_reference() {
        let context = BddContext::new(2);
        let (formula, top) = complex_formula();
        let mut generalized = GenBuchiAutomaton::new(&context, &formula, top);
        generalized.simplify();
        let mut automaton = BuchiAutomaton::from_generalized(&generalized);
        assert_eq!(
            automaton.dump(),
            "begin{BuchiAutomaton2}\nstate 0\n1\tx0\n\nstate 1\n7\ttrue\n\nstate 2\n2\tx0.(~x1)\n3\tx1\n4\t~x1\n5\tx0.(x1)\n\nstate 3\n1\tx1\n\nstate 4\n3\tx1\n5\tx0.(x1)\n\nstate 5\n3\ttrue\n5\tx0\n\nstate 6\n\nstate 7\taccepting\n7\ttrue\n\nstate 8\n\nstate 9\n\nstate 10\n\nstate 11\n\ninitial states: {0, 2}\nend{BuchiAutomaton2}\n"
        );

        automaton.collapse_states(&context);
        let collapsed = "begin{BuchiAutomaton2}\nstate 0\taccepting\n0\ttrue\n\nstate 1\n0\tx0\n\nstate 2\n0\tx1\n\nstate 3\n2\ttrue\n3\tx0\n\nstate 4\n2\tx1\n3\tx0.(x1)\n\nstate 5\n2\tx1\n3\tx0.(x1)\n4\t~x1\n5\tx0.(~x1)\n\ninitial states: {1, 5}\nend{BuchiAutomaton2}\n";
        assert_eq!(automaton.dump(), collapsed);
        automaton.collapse_states(&context);
        assert_eq!(automaton.dump(), collapsed);
    }

    #[test]
    fn constants_and_literal_polarities_match_reference_automata() {
        let zero_context = BddContext::new(0);
        let mut false_formula = LogicFormula::default();
        let false_top = false_formula.make_false();
        let false_automaton = BuchiAutomaton::new(&zero_context, &false_formula, false_top);
        assert_eq!(false_automaton.state_count(), 0);
        assert!(false_automaton.initial_states().is_empty());

        let mut true_formula = LogicFormula::default();
        let true_top = true_formula.make_true();
        let true_automaton = BuchiAutomaton::new(&zero_context, &true_formula, true_top);
        assert_eq!(
            true_automaton.dump(),
            "begin{BuchiAutomaton2}\nstate 0\taccepting\n0\ttrue\n\ninitial states: {0}\nend{BuchiAutomaton2}\n"
        );

        let context = BddContext::new(1);
        let mut positive_formula = LogicFormula::default();
        let positive_top = positive_formula.make_proposition(0);
        let positive = BuchiAutomaton::new(&context, &positive_formula, positive_top);
        assert_eq!(
            positive.dump(),
            "begin{BuchiAutomaton2}\nstate 0\taccepting\n1\tx0\n\nstate 1\taccepting\n1\ttrue\n\ninitial states: {0}\nend{BuchiAutomaton2}\n"
        );

        let mut negative_formula = LogicFormula::default();
        let proposition = negative_formula.make_proposition(0);
        let negative_top = negative_formula.make_not(proposition);
        let negative = BuchiAutomaton::new(&context, &negative_formula, negative_top);
        assert_eq!(
            negative.dump(),
            "begin{BuchiAutomaton2}\nstate 0\taccepting\n1\t~x0\n\nstate 1\taccepting\n1\ttrue\n\ninitial states: {0}\nend{BuchiAutomaton2}\n"
        );
    }

    #[test]
    fn left_folded_nary_boolean_matches_instrumented_reference() {
        let context = BddContext::new(3);
        let mut formula = LogicFormula::default();
        let p = formula.make_proposition(0);
        let q = formula.make_proposition(1);
        let r = formula.make_proposition(2);
        let p_and_q = formula.make_and(p, q);
        let top = formula.make_and(p_and_q, r);
        let automaton = BuchiAutomaton::new(&context, &formula, top);
        assert_eq!(
            automaton.dump(),
            "begin{BuchiAutomaton2}\nstate 0\taccepting\n1\tx0.(x1.(x2))\n\nstate 1\taccepting\n1\ttrue\n\ninitial states: {0}\nend{BuchiAutomaton2}\n"
        );
    }
}
