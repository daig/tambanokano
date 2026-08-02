use super::bdd::{Bdd, BddContext};
use super::buchi::BuchiAutomaton;
use super::formula::{BuiltFormula, FormulaId, LogicFormula, build_formula};
use super::nat_set::NatSet;
use crate::dag::{DagId, NaValue};
use crate::descent::DescentOps;
use crate::engine::{ModelCheckStats, Runtime, Signature};
use crate::host::ReducerFault;
use crate::root::RootGuard;
use crate::search::{GraphContext, RawSuccessors, StateGraph};
use crate::symbol::ModelCheckerHooks;
use std::collections::{BTreeSet, VecDeque};

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

struct ActiveGraphContext<'runtime, 'signature, 'descent> {
    runtime: &'runtime mut Runtime,
    signature: &'signature Signature,
    descent: &'descent mut dyn DescentOps,
}

impl GraphContext for ActiveGraphContext<'_, '_, '_> {
    fn graph_state_successors(&mut self, root: DagId) -> Result<RawSuccessors, ReducerFault> {
        self.runtime.state_successors_deferred(self.signature, root)
    }

    fn graph_replay_rewrites(&mut self, rewrites: u64) {
        self.runtime.add_rewrites(rewrites);
    }

    fn graph_reduce_successor(&mut self, successor: DagId) -> Result<DagId, ReducerFault> {
        self.runtime
            .reduce_graph_successor(self.signature, successor, self.descent)
    }

    fn graph_dag_hash(&self, id: DagId) -> u64 {
        self.runtime.dag_hash(id)
    }

    fn graph_deep_equal(&self, lhs: DagId, rhs: DagId) -> bool {
        self.runtime.deep_equal(lhs, rhs)
    }

    fn graph_root(&self, id: DagId) -> RootGuard {
        self.runtime.root(id)
    }
}

/// Rewrite-system adapter for the generic nested DFS. Deadlock self-loops are deliberately local to
/// this wrapper; ordinary search continues to expose a terminal state with no successors.
struct RewriteSystem<'runtime, 'signature, 'descent, 'formula, 'hooks> {
    graph: StateGraph,
    runtime: &'runtime mut Runtime,
    signature: &'signature Signature,
    descent: &'descent mut dyn DescentOps,
    formula: &'formula BuiltFormula,
    hooks: &'hooks ModelCheckerHooks,
    deadlocks: BTreeSet<usize>,
    fault: Option<ReducerFault>,
}

impl System for RewriteSystem<'_, '_, '_, '_, '_> {
    fn get_next_state(&mut self, state: usize, transition: usize) -> Option<usize> {
        if self.fault.is_some() {
            return None;
        }
        let successor = {
            let mut context = ActiveGraphContext {
                runtime: &mut *self.runtime,
                signature: self.signature,
                descent: &mut *self.descent,
            };
            self.graph.get_next_state(&mut context, state, transition)
        };
        match successor {
            Ok(Some(successor)) => return Some(successor.state),
            Ok(None) => {}
            Err(fault) => {
                self.fault = Some(fault);
                return None;
            }
        }
        if transition == 0
            && self
                .graph
                .fwd_arcs(state)
                .is_some_and(|arcs| arcs.is_empty())
        {
            self.deadlocks.insert(state);
            return Some(state);
        }
        None
    }

    fn check_proposition(&mut self, state: usize, proposition: usize) -> bool {
        if self.fault.is_some() {
            return false;
        }
        let state = self.graph.state_dag(state).expect("checker state exists");
        let proposition = self.formula.proposition(proposition);
        let test = self.runtime.make_free(
            self.signature,
            self.hooks.satisfies_symbol,
            vec![state, proposition],
        );
        match self
            .runtime
            .reduce(self.signature, test, &mut *self.descent)
        {
            Ok(result) => self.runtime.node(result).symbol() == self.hooks.true_term,
            Err(fault) => {
                self.fault = Some(fault);
                false
            }
        }
    }
}

impl RewriteSystem<'_, '_, '_, '_, '_> {
    fn label_dag(&mut self, source: usize, target: usize) -> DagId {
        if source == target
            && self.deadlocks.contains(&source)
            && self
                .graph
                .fwd_arcs(source)
                .is_some_and(|arcs| arcs.is_empty())
        {
            return self
                .runtime
                .make_free(self.signature, self.hooks.deadlock_symbol, Vec::new());
        }

        let rule = self
            .graph
            .arc_rules(source, target)
            .and_then(|rules| rules.first())
            .copied()
            .expect("lasso transition must be a recorded state-graph arc");
        match self.signature.rule_label(rule).cloned() {
            Some(label) => {
                self.runtime
                    .make_na(self.signature, self.hooks.qid_symbol, NaValue::Qid(label))
            }
            None => self
                .runtime
                .make_free(self.signature, self.hooks.unlabeled_symbol, Vec::new()),
        }
    }

    fn transition_dag(&mut self, source: usize, target: usize) -> DagId {
        let state = self.graph.state_dag(source).expect("lasso state exists");
        let label = self.label_dag(source, target);
        self.runtime.make_free(
            self.signature,
            self.hooks.transition_symbol,
            vec![state, label],
        )
    }

    fn transition_list(&mut self, states: &[usize], final_target: usize) -> DagId {
        if states.is_empty() {
            return self.runtime.make_free(
                self.signature,
                self.hooks.nil_transition_list_symbol,
                Vec::new(),
            );
        }
        let mut transitions = Vec::with_capacity(states.len());
        for (index, &source) in states.iter().enumerate() {
            let target = states.get(index + 1).copied().unwrap_or(final_target);
            transitions.push(self.transition_dag(source, target));
        }
        self.runtime.rebuild(
            self.signature,
            self.hooks.transition_list_symbol,
            transitions,
        )
    }

    fn result(&mut self, counterexample: Option<Counterexample>) -> DagId {
        let Some(counterexample) = counterexample else {
            return self
                .runtime
                .make_free(self.signature, self.hooks.true_term, Vec::new());
        };
        let cycle_start = *counterexample
            .cycle
            .first()
            .expect("nested DFS counterexample has a nonempty cycle");
        let lead_in = self.transition_list(&counterexample.lead_in, cycle_start);
        let cycle = self.transition_list(&counterexample.cycle, cycle_start);
        self.runtime.make_free(
            self.signature,
            self.hooks.counterexample_symbol,
            vec![lead_in, cycle],
        )
    }
}

/// Execute one `ModelCheckerSymbol` redex directly in the active reduction context.
pub(crate) fn check_rewrite_system(
    runtime: &mut Runtime,
    signature: &Signature,
    descent: &mut dyn DescentOps,
    redex: DagId,
    hooks: &ModelCheckerHooks,
) -> Option<DagId> {
    let arguments: Vec<DagId> = runtime.node(redex).children().collect();
    let [initial, property] = arguments.as_slice() else {
        return None;
    };

    // The checker searches for a behavior satisfying the negated property. Reducing the negation
    // both charges its equational rewrites and converts the formula to negative normal form.
    let initial_root = runtime.root(*initial);
    let negated = runtime.make_free(signature, hooks.temporal.not_symbol, vec![*property]);
    let negated = runtime.reduce_or_defer_fault(signature, negated, descent);
    let formula = build_formula(&*runtime, &hooks.temporal, negated)?;
    let bdd = BddContext::new(formula.propositions_len());
    let graph = StateGraph::new(initial_root, *initial);
    let mut system = RewriteSystem {
        graph,
        runtime,
        signature,
        descent,
        formula: &formula,
        hooks,
        deadlocks: BTreeSet::new(),
        fault: None,
    };
    let mut checker = ModelChecker::new(&mut system, &bdd, &formula.formula, formula.root);
    let property_automaton_states = checker.property_state_count();
    let counterexample = checker.find_counterexample();
    drop(checker);
    if let Some(fault) = system.fault.take() {
        system.runtime.defer_reducer_fault(fault);
        return None;
    }
    let examined_system_states = system.graph.len();
    system.runtime.record_model_check_stats(ModelCheckStats {
        property_automaton_states,
        examined_system_states,
    });
    Some(system.result(counterexample))
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

    #[test]
    fn production_hook_records_typed_statistics() {
        use crate::engine::Engine;
        use crate::symbol::{ModelCheckerHooks, SpecialOp};
        use crate::term::{Equation, Term};
        use std::rc::Rc;

        let mut engine = Engine::new();
        let any = engine.add_sort("Any");
        engine.close_sorts();

        let state = engine.add_op("state", vec![], any);
        let formula_true = engine.add_op("True", vec![], any);
        let formula_false = engine.add_op("False", vec![], any);
        let not = engine.add_op("not", vec![any], any);
        let next = engine.add_op("next", vec![any], any);
        let and = engine.add_op("and", vec![any, any], any);
        let or = engine.add_op("or", vec![any, any], any);
        let until = engine.add_op("until", vec![any, any], any);
        let release = engine.add_op("release", vec![any, any], any);
        let satisfies = engine.add_op("satisfies", vec![any, any], any);
        let qid = engine.add_op("qid", vec![], any);
        let unlabeled = engine.add_op("unlabeled", vec![], any);
        let deadlock = engine.add_op("deadlock", vec![], any);
        let transition = engine.add_op("transition", vec![any, any], any);
        let nil = engine.add_op("nil", vec![], any);
        let transition_list = engine.add_op_au("list", vec![any, any], any, Some(nil));
        let counterexample = engine.add_op("counterexample", vec![any, any], any);
        let bool_true = engine.add_op("true", vec![], any);
        let model_check = engine.add_op("modelCheck", vec![any, any], any);

        engine.add_equation(Equation {
            lhs: Term::op(not, vec![Term::constant(formula_false)]),
            rhs: Term::constant(formula_true),
            nr_vars: 0,
        });
        engine.add_labelled_rule(
            Term::constant(state),
            Term::constant(state),
            0,
            Some(Rc::from("loop")),
        );
        engine.set_special(
            model_check,
            SpecialOp::ModelCheck {
                hooks: Rc::new(ModelCheckerHooks {
                    temporal: crate::ltl::TemporalHooks {
                        true_symbol: formula_true,
                        false_symbol: formula_false,
                        not_symbol: not,
                        next_symbol: next,
                        and_symbol: and,
                        or_symbol: or,
                        until_symbol: until,
                        release_symbol: release,
                    },
                    satisfies_symbol: satisfies,
                    qid_symbol: qid,
                    unlabeled_symbol: unlabeled,
                    deadlock_symbol: deadlock,
                    transition_symbol: transition,
                    transition_list_symbol: transition_list,
                    nil_transition_list_symbol: nil,
                    counterexample_symbol: counterexample,
                    true_term: bool_true,
                }),
            },
        );

        let initial = engine.make_const(state);
        let property = engine.make_const(formula_false);
        let redex = engine.make_free(model_check, vec![initial, property]);
        let result = engine.reduce(redex);
        assert_eq!(engine.node(result).symbol(), counterexample);
        assert_eq!(
            engine.take_model_check_stats(),
            vec![ModelCheckStats {
                property_automaton_states: 1,
                examined_system_states: 1,
            }]
        );
    }
    #[test]
    fn production_proposition_fault_is_atomic_and_prevents_equation_fallback() {
        use crate::engine::Engine;
        use crate::host::{
            HostFunctionCatalog, ReducerFault, ResolvedHostHooks, StrictCall, StrictOutcome,
            StrictReduceCtx, StrictReducer, StrictReducerDescriptor,
        };
        use crate::symbol::{ModelCheckerHooks, SpecialOp};
        use crate::term::{Equation, Term};
        use std::rc::Rc;

        struct Fault;

        impl StrictReducer for Fault {
            fn reduce<'ctx>(
                &self,
                _ctx: &mut StrictReduceCtx<'ctx>,
                _call: StrictCall<'ctx>,
            ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
                Err(ReducerFault::new("proposition reducer fault"))
            }
        }

        let catalog = HostFunctionCatalog::builder()
            .register(
                "model.proposition",
                Fault,
                StrictReducerDescriptor::builder(2).build(),
            )
            .expect("register proposition reducer")
            .build();
        let mut engine = Engine::with_host_functions(catalog);
        let any = engine.add_sort("Any");
        engine.close_sorts();

        let state = engine.add_op("state", vec![], any);
        let formula_true = engine.add_op("True", vec![], any);
        let formula_false = engine.add_op("False", vec![], any);
        let not = engine.add_op("not", vec![any], any);
        let next = engine.add_op("next", vec![any], any);
        let and = engine.add_op("and", vec![any, any], any);
        let or = engine.add_op("or", vec![any, any], any);
        let until = engine.add_op("until", vec![any, any], any);
        let release = engine.add_op("release", vec![any, any], any);
        let satisfies = engine.add_op("satisfies", vec![any, any], any);
        let qid = engine.add_op("qid", vec![], any);
        let unlabeled = engine.add_op("unlabeled", vec![], any);
        let deadlock = engine.add_op("deadlock", vec![], any);
        let transition = engine.add_op("transition", vec![any, any], any);
        let nil = engine.add_op("nil", vec![], any);
        let transition_list = engine.add_op_au("list", vec![any, any], any, Some(nil));
        let counterexample = engine.add_op("counterexample", vec![any, any], any);
        let bool_true = engine.add_op("true", vec![], any);
        let model_check = engine.add_op("modelCheck", vec![any, any], any);

        engine.add_equation(Equation {
            lhs: Term::op(satisfies, vec![Term::constant(state), Term::constant(qid)]),
            rhs: Term::constant(bool_true),
            nr_vars: 0,
        });
        engine.add_labelled_rule(
            Term::constant(state),
            Term::constant(state),
            0,
            Some(Rc::from("loop")),
        );
        engine
            .bind_host_function(satisfies, "model.proposition", ResolvedHostHooks::default())
            .expect("bind proposition reducer");
        engine.set_special(
            model_check,
            SpecialOp::ModelCheck {
                hooks: Rc::new(ModelCheckerHooks {
                    temporal: crate::ltl::TemporalHooks {
                        true_symbol: formula_true,
                        false_symbol: formula_false,
                        not_symbol: not,
                        next_symbol: next,
                        and_symbol: and,
                        or_symbol: or,
                        until_symbol: until,
                        release_symbol: release,
                    },
                    satisfies_symbol: satisfies,
                    qid_symbol: qid,
                    unlabeled_symbol: unlabeled,
                    deadlock_symbol: deadlock,
                    transition_symbol: transition,
                    transition_list_symbol: transition_list,
                    nil_transition_list_symbol: nil,
                    counterexample_symbol: counterexample,
                    true_term: bool_true,
                }),
            },
        );

        let initial = engine.make_const(state);
        let property = engine.make_const(qid);
        let redex = engine.make_free(model_check, vec![initial, property]);
        engine.set_trace(true);
        engine.reset_rewrites();
        let fault = engine
            .try_reduce(redex)
            .expect_err("proposition reducer fault must abort model checking");
        assert_eq!(
            fault.key().expect("fault key").as_str(),
            "model.proposition"
        );
        assert_eq!(fault.message(), "proposition reducer fault");
        assert_eq!(engine.rewrites(), 0);
        assert_eq!(engine.rewrite_breakdown(), (0, 0, 0, 0));
        assert!(engine.take_trace().is_empty());
        assert!(engine.take_model_check_stats().is_empty());
        assert_eq!(engine.node(redex).symbol(), model_check);
    }
}
