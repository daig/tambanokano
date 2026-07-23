use super::buchi::{FairTransitionSet, GenBuchiAutomaton, IndexedSet};
use super::nat_set::NatSet;

#[derive(Clone, Copy)]
struct StateInfo {
    traversal_number: usize,
    component: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ComponentStatus {
    Dead,
    Unfair,
    Fair,
}

struct ComponentInfo {
    status: ComponentStatus,
    redundant: NatSet,
}

struct Analysis {
    states: Vec<StateInfo>,
    components: Vec<ComponentInfo>,
    essential: NatSet,
}

impl GenBuchiAutomaton<'_> {
    pub(super) fn scc_optimizations(&mut self) {
        let analysis = self.scc_analysis();
        let mut state_map = vec![None; self.states.len()];
        let mut live_count = 0;
        for (state, mapped) in state_map.iter_mut().enumerate() {
            if analysis.components[analysis.states[state].component].status != ComponentStatus::Dead
            {
                *mapped = Some(live_count);
                live_count += 1;
            }
        }

        let mut fairness_map = vec![None; self.nr_fairness_sets];
        let mut fairness_count = 0;
        for (fairness, mapped) in fairness_map.iter_mut().enumerate() {
            if analysis.essential.contains(fairness) {
                *mapped = Some(fairness_count);
                fairness_count += 1;
            }
        }

        let old_fairness_conditions = std::mem::take(&mut self.fairness_conditions);
        let mut new_states = vec![None; live_count];
        let mut new_transition_sets = IndexedSet::default();
        for old_state in 0..self.states.len() {
            let Some(new_state) = state_map[old_state] else {
                continue;
            };
            let component = analysis.states[old_state].component;
            let original = self
                .fair_transition_sets
                .get(self.states[old_state].expect("generated GBA state"))
                .clone();
            let transformed = if analysis.components[component].status == ComponentStatus::Unfair {
                self.eliminate_fairness(&original, &state_map)
            } else {
                self.transform_fair_transition_set2(
                    &old_fairness_conditions,
                    &original,
                    &state_map,
                    &fairness_map,
                    component,
                    &analysis,
                )
            };
            new_states[new_state] = Some(new_transition_sets.insert(transformed));
        }
        let mut new_initial_states = NatSet::default();
        Self::remap_nat_set(&mut new_initial_states, &self.initial_states, &state_map);
        self.initial_states = new_initial_states;
        self.states = new_states;
        self.fair_transition_sets = new_transition_sets;
        self.nr_fairness_sets = fairness_count;
    }

    fn scc_analysis(&self) -> Analysis {
        let mut states = vec![
            StateInfo {
                traversal_number: 0,
                component: 0,
            };
            self.states.len()
        ];
        let mut traversal_count = 0;
        let mut component_count = 0;
        let mut stack = Vec::new();
        for state in self.initial_states.iter() {
            self.strong_connected(
                state,
                &mut states,
                &mut stack,
                &mut traversal_count,
                &mut component_count,
            );
        }

        let mut components = Vec::with_capacity(component_count);
        let mut essential = NatSet::default();
        for component in 0..component_count {
            components.push(self.handle_component(component, &states, &components, &mut essential));
        }
        Analysis {
            states,
            components,
            essential,
        }
    }

    fn strong_connected(
        &self,
        state: usize,
        state_info: &mut [StateInfo],
        stack: &mut Vec<usize>,
        traversal_count: &mut usize,
        component_count: &mut usize,
    ) -> usize {
        stack.push(state);
        *traversal_count += 1;
        let mut low_link = *traversal_count;
        state_info[state].traversal_number = low_link;

        for &(target, _) in self.transitions(state).keys() {
            let target_number = state_info[target].traversal_number;
            if target_number == 0 {
                let target_low_link = self.strong_connected(
                    target,
                    state_info,
                    stack,
                    traversal_count,
                    component_count,
                );
                low_link = low_link.min(target_low_link);
            } else if target_number < low_link {
                low_link = target_number;
            }
        }

        if state_info[state].traversal_number == low_link {
            loop {
                let member = stack.pop().expect("SCC stack underflow");
                state_info[member].traversal_number = usize::MAX;
                state_info[member].component = *component_count;
                if member == state {
                    break;
                }
            }
            *component_count += 1;
        }
        low_link
    }

    fn handle_component(
        &self,
        component: usize,
        state_info: &[StateInfo],
        completed_components: &[ComponentInfo],
        essential: &mut NatSet,
    ) -> ComponentInfo {
        let mut implies = vec![self.all_fair.clone(); self.nr_fairness_sets];
        let mut sum = NatSet::default();
        let mut reaches_live_scc = false;
        let mut has_internal_transition = false;

        for state in 0..self.states.len() {
            if state_info[state].component != component {
                continue;
            }
            for (&(target, fairness_index), _) in self.transitions(state) {
                let target_component = state_info[target].component;
                if target_component == component {
                    has_internal_transition = true;
                    let fairness = self.fairness_conditions.get(fairness_index);
                    sum.union_with(fairness);
                    for (index, implication) in implies.iter_mut().enumerate() {
                        if fairness.contains(index) {
                            implication.intersect(fairness);
                        }
                    }
                } else {
                    assert!(
                        target_component < component,
                        "SCC component order is not reverse topological"
                    );
                    if completed_components[target_component].status != ComponentStatus::Dead {
                        reaches_live_scc = true;
                    }
                }
            }
        }

        if !has_internal_transition || sum != self.all_fair {
            return ComponentInfo {
                status: if reaches_live_scc {
                    ComponentStatus::Unfair
                } else {
                    ComponentStatus::Dead
                },
                redundant: NatSet::default(),
            };
        }

        let mut redundant = NatSet::default();
        for (fairness, implied) in implies.iter_mut().enumerate() {
            if !redundant.contains(fairness) {
                implied.remove(fairness);
                redundant.union_with(implied);
            }
        }
        let mut used = self.all_fair.clone();
        used.subtract(&redundant);
        essential.union_with(&used);
        ComponentInfo {
            status: ComponentStatus::Fair,
            redundant,
        }
    }

    fn eliminate_fairness(
        &mut self,
        original: &FairTransitionSet,
        state_map: &[Option<usize>],
    ) -> FairTransitionSet {
        let mut transformed = FairTransitionSet::new();
        for (&(target, _), formula) in original {
            if let Some(target) = state_map[target] {
                let fairness = self.fairness_conditions.insert(NatSet::default());
                self.insert_fair_transition2(&mut transformed, (target, fairness), formula.clone());
            }
        }
        transformed
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_fair_transition_set2(
        &mut self,
        old_fairness_conditions: &IndexedSet<NatSet>,
        original: &FairTransitionSet,
        state_map: &[Option<usize>],
        fairness_map: &[Option<usize>],
        component: usize,
        analysis: &Analysis,
    ) -> FairTransitionSet {
        let mut transformed = FairTransitionSet::new();
        for (&(old_target, old_fairness), formula) in original {
            let Some(target) = state_map[old_target] else {
                continue;
            };
            let fairness = if analysis.states[old_target].component == component {
                let mut fairness = old_fairness_conditions.get(old_fairness).clone();
                fairness.union_with(&analysis.components[component].redundant);
                let mut remapped = NatSet::default();
                Self::remap_nat_set(&mut remapped, &fairness, fairness_map);
                self.fairness_conditions.insert(remapped)
            } else {
                self.fairness_conditions.insert(NatSet::default())
            };
            self.insert_fair_transition2(&mut transformed, (target, fairness), formula.clone());
        }
        transformed
    }
}
