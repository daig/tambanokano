//! Streaming native variant-satisfiability decision procedure.

use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::root::RootGuard;
use crate::sort::SortId;
use crate::unify::problem::VarSpec;
use crate::unify::{NameCodes, UnifyEnv, instantiate};
use crate::variant::{VariantEquation, VariantMode, VariantSearch};

use super::analysis::{ConstructorAnalysis, Eligibility, EligibilityRejection, SortOverrides};
use super::formula::{Branch, Formula};

/// One native variant-satisfiability request.
pub struct VariantSatQuery {
    pub formula: Formula,
    pub variables: Vec<VarSpec>,
    pub variant_equations: Vec<VariantEquation>,
    pub overrides: SortOverrides,
    pub has_memberships: bool,
}

/// The three-valued public outcome. Rejection means that returning a Boolean would exceed the
/// supported FVP/OS-compact contract; it is not a satisfiability answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decision {
    Sat,
    Unsat,
    Rejected(EligibilityRejection),
}

/// Decide a query in DNF order, preserving the order of branches and variant unifiers and stopping
/// at the first witness.
pub fn decide(engine: &mut Engine, names: &mut dyn NameCodes, query: VariantSatQuery) -> Decision {
    let analysis = match ConstructorAnalysis::build(engine, &query.overrides, query.has_memberships)
    {
        Ok(analysis) => analysis,
        Err(rejection) => return Decision::Rejected(rejection),
    };
    if let Eligibility::Rejected(rejection) = &analysis.eligibility {
        return Decision::Rejected(rejection.clone());
    }

    // The formula's free variables are existentially quantified over constructor inhabitants. If any
    // quantified sort is empty there is no valuation, even when a positive equality such as `X = X`
    // leaves that variable unbound in the unifier.
    if query
        .variables
        .iter()
        .any(|spec| analysis.sorts.empty.contains(&spec.sort))
    {
        return Decision::Unsat;
    }

    // These are the sole object-engine instances of the query's source variables. Every formula
    // term is instantiated with this same layout.
    let mut variable_dags = Vec::with_capacity(query.variables.len());
    let mut variable_roots = Vec::with_capacity(query.variables.len());
    for (slot, spec) in query.variables.iter().enumerate() {
        let dag = engine.make_var(spec.sort, spec.name, slot as u32);
        variable_roots.push(engine.root(dag));
        variable_dags.push(dag);
    }
    let identity_values: Vec<Option<DagId>> = variable_dags.iter().copied().map(Some).collect();

    let VariantSatQuery {
        formula,
        variables,
        variant_equations,
        ..
    } = query;
    for branch in formula.into_dnf() {
        let instantiated = instantiate_branch(engine, branch, &variable_dags);

        if instantiated.positive.is_empty() {
            if instantiated.negative.is_empty() {
                return Decision::Sat;
            }
            match negative_candidate_is_satisfiable(
                engine,
                names,
                &analysis,
                &instantiated.negative,
                &identity_values,
                &variant_equations,
            ) {
                Ok(true) => return Decision::Sat,
                Ok(false) => continue,
                Err(rejection) => return Decision::Rejected(rejection),
            }
        }

        let (mut search, positive_globals) = match positive_unifiers(
            engine,
            names,
            &variables,
            &instantiated.positive,
            &variant_equations,
        ) {
            Ok(search) => search,
            Err(rejection) => return Decision::Rejected(rejection),
        };
        let canonical_order = search.original_variable_order().to_vec();

        loop {
            let next = {
                let mut env = UnifyEnv { e: engine, names };
                search.find_next(&mut env)
            };
            if search.is_incomplete() {
                return Decision::Rejected(EligibilityRejection::VariantSearchIncomplete);
            }
            let Some(unifier) = next else {
                break;
            };
            if !unifier
                .substitution
                .iter()
                .all(|&dag| ConstructorAnalysis::is_constructor_term(engine, dag))
            {
                continue;
            }

            let (values, _value_roots) = lift_unifier(
                engine,
                variables.len(),
                &positive_globals,
                &canonical_order,
                &unifier.substitution,
            );
            if instantiated.negative.is_empty() {
                return Decision::Sat;
            }
            match negative_candidate_is_satisfiable(
                engine,
                names,
                &analysis,
                &instantiated.negative,
                &values,
                &variant_equations,
            ) {
                Ok(true) => return Decision::Sat,
                Ok(false) => {}
                Err(rejection) => return Decision::Rejected(rejection),
            }
        }
    }

    // Keep the query variables pinned through the complete streamed traversal.
    drop(variable_roots);
    Decision::Unsat
}

struct RootedPairs {
    pairs: Vec<(DagId, DagId)>,
    _roots: Vec<RootGuard>,
}

struct InstantiatedBranch {
    positive: RootedPairs,
    negative: RootedPairs,
}

impl RootedPairs {
    fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }
}

impl std::ops::Deref for RootedPairs {
    type Target = [(DagId, DagId)];

    fn deref(&self) -> &Self::Target {
        &self.pairs
    }
}

fn instantiate_branch(
    engine: &mut Engine,
    branch: Branch,
    variables: &[DagId],
) -> InstantiatedBranch {
    InstantiatedBranch {
        positive: instantiate_term_pairs(engine, branch.positive, variables),
        negative: instantiate_term_pairs(engine, branch.negative, variables),
    }
}

fn instantiate_term_pairs(
    engine: &mut Engine,
    pairs: Vec<(crate::term::Term, crate::term::Term)>,
    variables: &[DagId],
) -> RootedPairs {
    let mut dags = Vec::with_capacity(pairs.len());
    let mut roots = Vec::with_capacity(pairs.len() * 2);
    for (lhs, rhs) in pairs {
        let lhs = engine.instantiate_bindings(&lhs, variables);
        roots.push(engine.root(lhs));
        let rhs = engine.instantiate_bindings(&rhs, variables);
        roots.push(engine.root(rhs));
        dags.push((lhs, rhs));
    }
    RootedPairs {
        pairs: dags,
        _roots: roots,
    }
}

/// Build the same free synthetic pair/tuple target used by `metaVariantUnify`, but first compact the
/// branch's possibly sparse query-variable slots into the dense layout required by `VariantSearch`.
fn positive_unifiers(
    engine: &mut Engine,
    names: &mut dyn NameCodes,
    variables: &[VarSpec],
    pairs: &[(DagId, DagId)],
    equations: &[VariantEquation],
) -> Result<(VariantSearch, Vec<usize>), EligibilityRejection> {
    let mut globals = Vec::new();
    let mut seen = vec![false; variables.len()];
    for &(lhs, rhs) in pairs {
        collect_query_slots(engine, lhs, &mut seen, &mut globals);
        collect_query_slots(engine, rhs, &mut seen, &mut globals);
    }

    let mut global_to_local = vec![0; variables.len()];
    for (local, &global) in globals.iter().enumerate() {
        global_to_local[global] = local as u32;
    }
    let specs: Vec<_> = globals.iter().map(|&global| variables[global]).collect();

    let mut remapped = Vec::with_capacity(pairs.len());
    let mut remapped_roots = Vec::with_capacity(pairs.len() * 2);
    for &(lhs, rhs) in pairs {
        let lhs = engine.remap_variable_slots(lhs, &global_to_local);
        remapped_roots.push(engine.root(lhs));
        let rhs = engine.remap_variable_slots(rhs, &global_to_local);
        remapped_roots.push(engine.root(rhs));
        remapped.push((lhs, rhs));
    }

    let pair_count = remapped.len();
    let target = make_unification_target(engine, remapped);
    let target_root = engine.root(target);
    let mut env = UnifyEnv { e: engine, names };
    let mut search = VariantSearch::new(
        &mut env,
        target,
        specs,
        Vec::new(),
        equations.to_vec(),
        VariantMode::Incremental,
        None,
        "0",
    )
    .map_err(|_| EligibilityRejection::VariantSearchSetup)?;
    search.enable_unification(env.e, pair_count);
    drop(target_root);
    drop(remapped_roots);
    Ok((search, globals))
}

fn make_unification_target(engine: &mut Engine, pairs: Vec<(DagId, DagId)>) -> DagId {
    debug_assert!(!pairs.is_empty());
    let range = engine.sort_of(pairs[0].0);
    if pairs.len() == 1 {
        let (lhs, rhs) = pairs.into_iter().next().expect("one unification pair");
        let pair = engine.add_op(
            "$metaVariantUnifyPair",
            vec![engine.sort_of(lhs), engine.sort_of(rhs)],
            range,
        );
        return engine.make_node(pair, vec![lhs, rhs]);
    }

    let lhs_domains = pairs.iter().map(|&(lhs, _)| engine.sort_of(lhs)).collect();
    let rhs_domains = pairs.iter().map(|&(_, rhs)| engine.sort_of(rhs)).collect();
    let lhs_symbol = engine.add_op("$metaVariantUnifyLhs", lhs_domains, range);
    let rhs_symbol = engine.add_op("$metaVariantUnifyRhs", rhs_domains, range);
    let pair_symbol = engine.add_op("$metaVariantUnifyPair", vec![range, range], range);
    let mut lhs = Vec::with_capacity(pairs.len());
    let mut rhs = Vec::with_capacity(pairs.len());
    for (left, right) in pairs {
        lhs.push(left);
        rhs.push(right);
    }
    let lhs = engine.make_node(lhs_symbol, lhs);
    let lhs_root = engine.root(lhs);
    let rhs = engine.make_node(rhs_symbol, rhs);
    let rhs_root = engine.root(rhs);
    let target = engine.make_node(pair_symbol, vec![lhs, rhs]);
    drop(lhs_root);
    drop(rhs_root);
    target
}

fn collect_query_slots(engine: &Engine, root: DagId, seen: &mut [bool], slots: &mut Vec<usize>) {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeTerm::Var { index, .. } = node.term {
            let slot = index as usize;
            if !seen[slot] {
                seen[slot] = true;
                slots.push(slot);
            }
        } else {
            let children: Vec<_> = node.children().collect();
            work.extend(children.into_iter().rev());
        }
    }
}

/// Translate search-local substitution slots back into the query's global layout. Search-created
/// slots are placed above every query slot, preventing their indices from aliasing variables that did
/// not occur in the positive conjunction.
fn lift_unifier(
    engine: &mut Engine,
    query_slots: usize,
    positive_globals: &[usize],
    canonical_order: &[usize],
    substitution: &[DagId],
) -> (Vec<Option<DagId>>, Vec<RootGuard>) {
    debug_assert_eq!(canonical_order.len(), substitution.len());
    let mut max_slot = None;
    for &binding in substitution {
        collect_max_slot(engine, binding, &mut max_slot);
    }
    let mut slot_map = vec![0; max_slot.map_or(0, |slot| slot + 1)];
    for (canonical, &local) in canonical_order.iter().enumerate() {
        if canonical < slot_map.len() {
            slot_map[canonical] = positive_globals[local] as u32;
        }
    }
    for (slot, mapped) in slot_map.iter_mut().enumerate().skip(canonical_order.len()) {
        *mapped = (query_slots + slot - canonical_order.len()) as u32;
    }

    let mut values = vec![None; query_slots];
    let mut roots = Vec::with_capacity(substitution.len());
    for (canonical, &binding) in substitution.iter().enumerate() {
        let binding = if slot_map.is_empty() {
            binding
        } else {
            engine.remap_variable_slots(binding, &slot_map)
        };
        roots.push(engine.root(binding));
        let local = canonical_order[canonical];
        values[positive_globals[local]] = Some(binding);
    }
    (values, roots)
}

fn collect_max_slot(engine: &Engine, root: DagId, max_slot: &mut Option<usize>) {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeTerm::Var { index, .. } = node.term {
            let slot = index as usize;
            *max_slot = Some(max_slot.map_or(slot, |old| old.max(slot)));
        } else {
            work.extend(node.children());
        }
    }
}

fn negative_candidate_is_satisfiable(
    engine: &mut Engine,
    names: &mut dyn NameCodes,
    analysis: &ConstructorAnalysis,
    negative: &[(DagId, DagId)],
    unifier: &[Option<DagId>],
    equations: &[VariantEquation],
) -> Result<bool, EligibilityRejection> {
    let Some(normalized) = normalize_disequalities(engine, negative, unifier) else {
        return Ok(false);
    };
    let pair_count = normalized.pairs.len();
    let mut search = negative_constructor_variants(engine, names, &normalized.pairs, equations)?;

    loop {
        let next = {
            let mut env = UnifyEnv { e: engine, names };
            search.find_next(&mut env)
        };
        if search.is_incomplete() {
            return Err(EligibilityRejection::VariantSearchIncomplete);
        }
        let Some(variant) = next else {
            return Ok(false);
        };
        let Some(pairs) = variant_target_pairs(engine, variant.term, pair_count) else {
            return Err(EligibilityRejection::VariantSearchSetup);
        };
        if !pairs.iter().all(|&(lhs, rhs)| {
            ConstructorAnalysis::is_constructor_term(engine, lhs)
                && ConstructorAnalysis::is_constructor_term(engine, rhs)
        }) {
            continue;
        }
        if constructor_variant_is_satisfiable(engine, analysis, &pairs) {
            return Ok(true);
        }
    }
}

/// Compute the finite complete variant set of the whole conjunction at once. Keeping every literal
/// below one free synthetic root preserves shared-variable correlations between disequalities.
fn negative_constructor_variants(
    engine: &mut Engine,
    names: &mut dyn NameCodes,
    pairs: &[(DagId, DagId)],
    equations: &[VariantEquation],
) -> Result<VariantSearch, EligibilityRejection> {
    let mut slots = Vec::new();
    let mut specs_by_slot = Vec::new();
    for &(lhs, rhs) in pairs {
        collect_variant_variable_specs(engine, lhs, &mut slots, &mut specs_by_slot);
        collect_variant_variable_specs(engine, rhs, &mut slots, &mut specs_by_slot);
    }

    let mut slot_map = vec![0; specs_by_slot.len()];
    let mut specs = Vec::with_capacity(slots.len());
    for (local, &slot) in slots.iter().enumerate() {
        slot_map[slot] = local as u32;
        specs.push(specs_by_slot[slot].expect("collected variant variable must have a spec"));
    }

    let mut remapped = Vec::with_capacity(pairs.len());
    let mut remapped_roots = Vec::with_capacity(pairs.len() * 2);
    for &(lhs, rhs) in pairs {
        let lhs = engine.remap_variable_slots(lhs, &slot_map);
        remapped_roots.push(engine.root(lhs));
        let rhs = engine.remap_variable_slots(rhs, &slot_map);
        remapped_roots.push(engine.root(rhs));
        remapped.push((lhs, rhs));
    }

    let target = make_unification_target(engine, remapped);
    let target_root = engine.root(target);
    let mut env = UnifyEnv { e: engine, names };
    let mut search = VariantSearch::new(
        &mut env,
        target,
        specs,
        Vec::new(),
        equations.to_vec(),
        VariantMode::Irredundant,
        None,
        "0",
    )
    .map_err(|_| EligibilityRejection::VariantSearchSetup)?;
    search.skip_root_position();
    drop(target_root);
    drop(remapped_roots);
    Ok(search)
}

fn collect_variant_variable_specs(
    engine: &Engine,
    root: DagId,
    slots: &mut Vec<usize>,
    specs: &mut Vec<Option<VarSpec>>,
) {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeTerm::Var { name, index, .. } = node.term {
            let slot = index as usize;
            if specs.len() <= slot {
                specs.resize(slot + 1, None);
            }
            let spec = VarSpec {
                sort: engine.sort_of(dag),
                name,
            };
            if let Some(previous) = specs[slot] {
                debug_assert_eq!(previous.sort, spec.sort);
                debug_assert_eq!(previous.name, spec.name);
            } else {
                specs[slot] = Some(spec);
                slots.push(slot);
            }
        } else {
            let children: Vec<_> = node.children().collect();
            work.extend(children.into_iter().rev());
        }
    }
}

fn variant_target_pairs(
    engine: &Engine,
    target: DagId,
    pair_count: usize,
) -> Option<Vec<(DagId, DagId)>> {
    let outer: Vec<_> = engine.node(target).children().collect();
    if outer.len() != 2 {
        return None;
    }
    if pair_count == 1 {
        return Some(vec![(outer[0], outer[1])]);
    }
    let lhs: Vec<_> = engine.node(outer[0]).children().collect();
    let rhs: Vec<_> = engine.node(outer[1]).children().collect();
    if lhs.len() != pair_count || rhs.len() != pair_count {
        return None;
    }
    Some(lhs.into_iter().zip(rhs).collect())
}

fn constructor_variant_is_satisfiable(
    engine: &mut Engine,
    analysis: &ConstructorAnalysis,
    pairs: &[(DagId, DagId)],
) -> bool {
    if pairs.iter().any(|&(lhs, rhs)| engine.deep_equal(lhs, rhs)) {
        return false;
    }

    let mut finite_variables = Vec::new();
    let mut seen = Vec::new();
    for &(lhs, rhs) in pairs {
        if !collect_finite_variables(engine, analysis, lhs, &mut seen, &mut finite_variables)
            || !collect_finite_variables(engine, analysis, rhs, &mut seen, &mut finite_variables)
        {
            // A variable in an empty constructor sort has no assignment.
            return false;
        }
    }
    if finite_variables.is_empty() {
        // OS compactness supplies a constructor assignment for the remaining infinite-sort variables.
        return true;
    }

    let max_slot = finite_variables.iter().copied().max().unwrap_or(0);
    let mut assignment = vec![None; max_slot + 1];
    finite_assignment_satisfies(
        engine,
        analysis,
        pairs,
        &finite_variables,
        0,
        &mut assignment,
    )
}

/// Normalize after applying a positive unifier. `None` means that some disequality collapsed to an
/// equality and therefore rejects this candidate.
fn normalize_disequalities(
    engine: &mut Engine,
    pairs: &[(DagId, DagId)],
    values: &[Option<DagId>],
) -> Option<RootedPairs> {
    let mut normalized = Vec::with_capacity(pairs.len());
    let mut roots = Vec::with_capacity(pairs.len() * 2);
    for &(lhs, rhs) in pairs {
        let lhs = instantiate_reduce_normalize(engine, lhs, values);
        roots.push(engine.root(lhs));
        let rhs = instantiate_reduce_normalize(engine, rhs, values);
        roots.push(engine.root(rhs));
        if engine.deep_equal(lhs, rhs) {
            return None;
        }
        normalized.push((lhs, rhs));
    }
    Some(RootedPairs {
        pairs: normalized,
        _roots: roots,
    })
}

fn instantiate_reduce_normalize(
    engine: &mut Engine,
    dag: DagId,
    values: &[Option<DagId>],
) -> DagId {
    let instantiated = instantiate(engine, values, dag).unwrap_or(dag);
    let instantiated_root = engine.root(instantiated);
    let reduced = engine.reduce(instantiated);
    let reduced_root = engine.root(reduced);
    let normalized = engine.normalize_for_unify(reduced);
    drop(instantiated_root);
    drop(reduced_root);
    normalized
}

fn collect_finite_variables(
    engine: &Engine,
    analysis: &ConstructorAnalysis,
    root: DagId,
    seen: &mut Vec<bool>,
    variables: &mut Vec<usize>,
) -> bool {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeTerm::Var { index, .. } = node.term {
            let slot = index as usize;
            let sort = engine.sort_of(dag);
            if analysis.sorts.empty.contains(&sort) {
                return false;
            }
            if analysis.representatives(sort).is_some() {
                if seen.len() <= slot {
                    seen.resize(slot + 1, false);
                }
                if !seen[slot] {
                    seen[slot] = true;
                    variables.push(slot);
                }
            }
        } else {
            let children: Vec<_> = node.children().collect();
            work.extend(children.into_iter().rev());
        }
    }
    true
}

/// Depth-first Cartesian product over finite-sort representatives. Only the current assignment is
/// retained, so memory is linear in the number of finite variables.
fn finite_assignment_satisfies(
    engine: &mut Engine,
    analysis: &ConstructorAnalysis,
    pairs: &[(DagId, DagId)],
    variables: &[usize],
    depth: usize,
    assignment: &mut [Option<DagId>],
) -> bool {
    if depth == variables.len() {
        for &(lhs, rhs) in pairs {
            let lhs = instantiate_reduce_normalize(engine, lhs, assignment);
            let lhs_root = engine.root(lhs);
            let rhs = instantiate_reduce_normalize(engine, rhs, assignment);
            let rhs_root = engine.root(rhs);
            let equal = engine.deep_equal(lhs, rhs);
            drop(lhs_root);
            drop(rhs_root);
            if equal {
                return false;
            }
        }
        return true;
    }

    let slot = variables[depth];
    let sort = variable_sort(engine, pairs, slot).expect("collected finite variable must occur");
    let representatives = analysis
        .representatives(sort)
        .expect("collected finite variable must have representatives");
    for &representative in representatives {
        assignment[slot] = Some(representative);
        if finite_assignment_satisfies(engine, analysis, pairs, variables, depth + 1, assignment) {
            assignment[slot] = None;
            return true;
        }
    }
    assignment[slot] = None;
    false
}

fn variable_sort(engine: &Engine, pairs: &[(DagId, DagId)], slot: usize) -> Option<SortId> {
    for &(lhs, rhs) in pairs {
        for root in [lhs, rhs] {
            let mut work = vec![root];
            while let Some(dag) = work.pop() {
                let node = engine.node(dag);
                if let NodeTerm::Var { index, .. } = node.term {
                    if index as usize == slot {
                        return Some(engine.sort_of(dag));
                    }
                } else {
                    work.extend(node.children());
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::term::{Equation, Term};
    use crate::variant::compile_variant_equation;
    use crate::variant_sat::formula::Literal;

    #[derive(Default)]
    struct TestNames {
        codes: HashMap<String, u32>,
        next: u32,
    }

    impl NameCodes for TestNames {
        fn code(&mut self, name: &str) -> u32 {
            if let Some(&code) = self.codes.get(name) {
                return code;
            }
            let code = self.next;
            self.next += 1;
            self.codes.insert(name.to_owned(), code);
            code
        }
    }

    /// Constructor variants, not the cardinality of a variable's sort, decide whether an
    /// otherwise-constructor disequality can hold. Both complete variants of `f(X)` reduce to `a`.
    #[test]
    fn negative_variants_precede_infinite_sort_shortcut() {
        let mut engine = Engine::new();
        let nat = engine.add_sort("Nat");
        engine.close_sorts();
        let zero = engine.add_op("0", Vec::new(), nat);
        let successor = engine.add_op("s_", vec![nat], nat);
        let a = engine.add_op("a", Vec::new(), nat);
        let f = engine.add_op("f", vec![nat], nat);
        engine.set_ctor(zero);
        engine.set_ctor(successor);
        engine.set_ctor(a);

        let mut names = TestNames::default();
        let n_name = names.code("N");
        let x_name = names.code("X");
        let zero_term = Term::constant(zero);
        let a_term = Term::constant(a);
        let n_term = Term::var(0, nat);
        let f_zero = Term::op(f, vec![zero_term.clone()]);
        let f_successor = Term::op(f, vec![Term::op(successor, vec![n_term.clone()])]);
        let variant_equations = vec![
            compile_variant_equation(&mut engine, 0, &f_zero, &a_term, Vec::new()),
            compile_variant_equation(
                &mut engine,
                1,
                &f_successor,
                &a_term,
                vec![VarSpec {
                    sort: nat,
                    name: n_name,
                }],
            ),
        ];
        engine.add_equation(Equation {
            lhs: f_zero,
            rhs: a_term.clone(),
            nr_vars: 0,
        });
        engine.add_equation(Equation {
            lhs: f_successor,
            rhs: a_term.clone(),
            nr_vars: 1,
        });

        let variables = vec![VarSpec {
            sort: nat,
            name: x_name,
        }];
        let unsatisfiable = VariantSatQuery {
            formula: Formula::Literal(Literal {
                lhs: Term::op(f, vec![Term::var(0, nat)]),
                rhs: a_term.clone(),
                positive: false,
            }),
            variables: variables.clone(),
            variant_equations: variant_equations.clone(),
            overrides: SortOverrides::default(),
            has_memberships: false,
        };
        assert_eq!(
            decide(&mut engine, &mut names, unsatisfiable),
            Decision::Unsat
        );

        let satisfiable = VariantSatQuery {
            formula: Formula::Literal(Literal {
                lhs: Term::op(f, vec![Term::var(0, nat)]),
                rhs: zero_term,
                positive: false,
            }),
            variables,
            variant_equations,
            overrides: SortOverrides::default(),
            has_memberships: false,
        };
        assert_eq!(decide(&mut engine, &mut names, satisfiable), Decision::Sat);
    }

    /// Variantizing the conjunction under one tuple root keeps the two occurrences of `X`
    /// correlated: neither constructor variant satisfies both disequalities.
    #[test]
    fn negative_conjunction_variants_share_substitution() {
        let mut engine = Engine::new();
        let nat = engine.add_sort("Nat");
        engine.close_sorts();
        let zero = engine.add_op("0", Vec::new(), nat);
        let successor = engine.add_op("s_", vec![nat], nat);
        let a = engine.add_op("a", Vec::new(), nat);
        let g = engine.add_op("g", vec![nat], nat);
        engine.set_ctor(zero);
        engine.set_ctor(successor);
        engine.set_ctor(a);

        let mut names = TestNames::default();
        let n_name = names.code("N");
        let x_name = names.code("X");
        let zero_term = Term::constant(zero);
        let a_term = Term::constant(a);
        let g_zero = Term::op(g, vec![zero_term.clone()]);
        let g_successor = Term::op(g, vec![Term::op(successor, vec![Term::var(0, nat)])]);
        let variant_equations = vec![
            compile_variant_equation(&mut engine, 0, &g_zero, &a_term, Vec::new()),
            compile_variant_equation(
                &mut engine,
                1,
                &g_successor,
                &zero_term,
                vec![VarSpec {
                    sort: nat,
                    name: n_name,
                }],
            ),
        ];
        engine.add_equation(Equation {
            lhs: g_zero,
            rhs: a_term.clone(),
            nr_vars: 0,
        });
        engine.add_equation(Equation {
            lhs: g_successor,
            rhs: zero_term.clone(),
            nr_vars: 1,
        });

        let g_x = Term::op(g, vec![Term::var(0, nat)]);
        let query = VariantSatQuery {
            formula: Formula::And(vec![
                Formula::Literal(Literal {
                    lhs: g_x.clone(),
                    rhs: a_term,
                    positive: false,
                }),
                Formula::Literal(Literal {
                    lhs: g_x,
                    rhs: zero_term,
                    positive: false,
                }),
            ]),
            variables: vec![VarSpec {
                sort: nat,
                name: x_name,
            }],
            variant_equations,
            overrides: SortOverrides::default(),
            has_memberships: false,
        };

        assert_eq!(decide(&mut engine, &mut names, query), Decision::Unsat);
    }
}
