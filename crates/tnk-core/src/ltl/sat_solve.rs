use super::bdd::{Bdd, BddContext};
use super::buchi::GenBuchiAutomaton;
use super::formula::{BuiltFormula, build_formula};
use crate::dag::DagId;
use crate::engine::{Runtime, SatSolveStats, Signature};
use crate::symbol::SatSolverHooks;

/// Reduce one `satSolve(F)` redex. `None` means `F` is not a valid negative-normal-form LTL formula,
/// matching the reference hook's fall-through to user equations.
pub(crate) fn solve(
    runtime: &mut Runtime,
    sig: &Signature,
    redex: DagId,
    hooks: &SatSolverHooks,
) -> Option<DagId> {
    let formula_dag = runtime
        .node(redex)
        .children()
        .next()
        .expect("satSolve is unary");
    let built = build_formula(runtime, &hooks.temporal, formula_dag)?;
    let context = BddContext::new(built.propositions_len());
    let mut automaton = GenBuchiAutomaton::new(&context, &built.formula, built.root);
    let model = automaton.sat_solve();
    let stats = SatSolveStats {
        generalized_buchi_states: automaton.state_count(),
        fairness_sets: automaton.fairness_set_count(),
    };

    let result = if let Some((lead_in, cycle)) = model {
        make_model(runtime, sig, hooks, &built, &lead_in, &cycle)
    } else {
        runtime.make_const(sig, hooks.false_term)
    };
    runtime.record_sat_solve_stats(stats);
    Some(result)
}

fn make_model(
    runtime: &mut Runtime,
    sig: &Signature,
    hooks: &SatSolverHooks,
    built: &BuiltFormula,
    lead_in: &[Bdd],
    cycle: &[Bdd],
) -> DagId {
    let lead_in = make_formula_list(runtime, sig, hooks, built, lead_in);
    let cycle = make_formula_list(runtime, sig, hooks, built, cycle);
    runtime.make_free(sig, hooks.model_symbol, vec![lead_in, cycle])
}

fn make_formula_list(
    runtime: &mut Runtime,
    sig: &Signature,
    hooks: &SatSolverHooks,
    built: &BuiltFormula,
    predicates: &[Bdd],
) -> DagId {
    if predicates.is_empty() {
        return runtime.make_const(sig, hooks.nil_formula_list_symbol);
    }
    let formulae: Vec<_> = predicates
        .iter()
        .map(|predicate| make_formula(runtime, sig, hooks, built, predicate))
        .collect();
    if formulae.len() == 1 {
        formulae[0]
    } else {
        runtime.rebuild(sig, hooks.formula_list_symbol, formulae)
    }
}

fn make_formula(
    runtime: &mut Runtime,
    sig: &Signature,
    hooks: &SatSolverHooks,
    built: &BuiltFormula,
    predicate: &Bdd,
) -> DagId {
    let literals = predicate
        .prime_implicant_literals()
        .expect("a satisfying lasso transition cannot be false");
    let mut conjuncts = Vec::with_capacity(literals.len());
    for (proposition, positive) in literals {
        let proposition = built.proposition(proposition);
        conjuncts.push(if positive {
            proposition
        } else {
            runtime.make_free(sig, hooks.temporal.not_symbol, vec![proposition])
        });
    }

    let Some(mut result) = conjuncts.pop() else {
        return runtime.make_const(sig, hooks.temporal.true_symbol);
    };
    while let Some(lhs) = conjuncts.pop() {
        result = runtime.rebuild(sig, hooks.temporal.and_symbol, vec![lhs, result]);
    }
    result
}
