use std::collections::{HashMap, HashSet, VecDeque};

use crate::dag::DagId;
use crate::engine::Engine;
use crate::root::RootGuard;
use crate::sort::SortId;
use crate::symbol::{SymbolId, Theory};

/// Caller-supplied classifications used where constructor collapse axioms prevent an automatic proof.
#[derive(Debug, Clone, Default)]
pub struct SortOverrides {
    pub finite: Vec<SortId>,
    pub infinite: Vec<SortId>,
    pub explicit: bool,
}

/// A definite reason why the variant-satisfiability preconditions are not met.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EligibilityRejection {
    MembershipAxioms,
    AssociativeWithoutCommutativeConstructor { symbol: SymbolId },
    InconsistentOverloadedConstructorAxioms { symbol: SymbolId },
    OverlappingSortOverride { sort: SortId },
    UnknownSortOverride { sort: SortId },
    FalseFiniteSortOverride { sort: SortId },
    FalseInfiniteSortOverride { sort: SortId },
    IdentityClassificationRequiresOverride { symbol: SymbolId, sort: SortId },
    EmptyRequestedFiniteSort { sort: SortId },
    ConstructorPreregularity { symbol: SymbolId },
    VariantSearchSetup,
    VariantSearchIncomplete,
}

/// How much of the semantic eligibility contract was established locally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Eligibility {
    SyntacticallyProved,
    CallerPreconditioned,
    Rejected(EligibilityRejection),
}

/// Constructor inhabitants, partitioned by their proved cardinality.
#[derive(Debug, Default)]
pub struct SortClassification {
    pub empty: HashSet<SortId>,
    pub infinite: HashSet<SortId>,
    pub finite: HashMap<SortId, Vec<DagId>>,
}

/// Query-local constructor signature analysis.
pub struct ConstructorAnalysis {
    pub eligibility: Eligibility,
    pub sorts: SortClassification,
    // Representatives cross later allocations and variant searches, so their DAGs must remain roots
    // for exactly as long as this analysis does.
    _representative_roots: Vec<RootGuard>,
}

#[derive(Clone)]
struct Production {
    symbol: SymbolId,
    domain: Vec<SortId>,
    range: SortId,
    /// For each domain position, whether recursive use through that argument can add a constructor
    /// inhabitant that survives identity collapse.
    growing_arguments: Vec<bool>,
}

impl ConstructorAnalysis {
    pub fn build(
        engine: &mut Engine,
        overrides: &SortOverrides,
        has_memberships: bool,
    ) -> Result<Self, EligibilityRejection> {
        if has_memberships {
            return Err(EligibilityRejection::MembershipAxioms);
        }

        let num_sorts = engine.sorts().num_sorts();
        let user_sorts: Vec<SortId> = (0..num_sorts)
            .map(|i| SortId::from_raw(i as u32))
            .filter(|&sort| !engine.sorts().sort(sort).is_error)
            .collect();

        let constructor_constants: Vec<(SymbolId, SortId)> = engine
            .signature()
            .symbols_iter()
            .filter(|(_, symbol)| symbol.is_constructor() && symbol.arity() == 0)
            .flat_map(|(symbol_id, symbol)| {
                symbol
                    .decls()
                    .iter()
                    .map(move |decl| (symbol_id, decl.range))
            })
            .collect();
        let mut productions = Vec::new();
        let mut identity_affected: HashMap<SortId, SymbolId> = HashMap::new();
        let mut family_axioms: HashMap<(String, usize), (Theory, bool, bool, bool)> =
            HashMap::new();

        for (symbol_id, symbol) in engine.signature().symbols_iter() {
            let has_ctor_decl = symbol.decls().iter().any(|decl| decl.ctor);
            if has_ctor_decl && symbol.has_inconsistent_constructor_axioms() {
                return Err(
                    EligibilityRejection::InconsistentOverloadedConstructorAxioms {
                        symbol: symbol_id,
                    },
                );
            }
            if has_ctor_decl && !symbol.is_constructor() {
                return Err(
                    EligibilityRejection::InconsistentOverloadedConstructorAxioms {
                        symbol: symbol_id,
                    },
                );
            }
            if !symbol.is_constructor() {
                continue;
            }

            if symbol.theory() == Theory::Au {
                return Err(
                    EligibilityRejection::AssociativeWithoutCommutativeConstructor {
                        symbol: symbol_id,
                    },
                );
            }

            let axiom_shape = (
                symbol.theory(),
                symbol.identity().is_some(),
                symbol.left_identity().is_some(),
                symbol.right_identity().is_some(),
            );
            let family = (symbol.name().to_owned(), symbol.arity());
            if family_axioms
                .insert(family, axiom_shape)
                .is_some_and(|previous| previous != axiom_shape)
            {
                return Err(
                    EligibilityRejection::InconsistentOverloadedConstructorAxioms {
                        symbol: symbol_id,
                    },
                );
            }

            if !constructor_preregular(engine, symbol_id, &user_sorts) {
                return Err(EligibilityRejection::ConstructorPreregularity { symbol: symbol_id });
            }

            let has_identity = symbol.identity().is_some()
                || symbol.left_identity().is_some()
                || symbol.right_identity().is_some()
                || symbol.one_sided_identity();
            let identity_constant = symbol
                .identity()
                .or_else(|| symbol.left_identity())
                .or_else(|| symbol.right_identity())
                .and_then(|identity| engine.signature().identity_constant(identity));
            for decl in symbol.decls() {
                let theory_can_grow_through_identity =
                    matches!(symbol.theory(), Theory::Free | Theory::Acu | Theory::Cui);
                let growing_arguments = if !has_identity {
                    vec![true; decl.domain.len()]
                } else if theory_can_grow_through_identity {
                    (0..decl.domain.len())
                        .map(|recursive_position| {
                            decl.domain
                                .iter()
                                .enumerate()
                                .any(|(other_position, &other_sort)| {
                                    if other_position == recursive_position {
                                        return false;
                                    }
                                    constructor_constants.iter().any(|&(added, added_sort)| {
                                        Some(added) != identity_constant
                                                && engine.sorts().leq(added_sort, other_sort)
                                                // CUI idempotence absorbs `f(a, a)`. A distinct
                                                // recursive seed still yields the unbounded nest
                                                // `b, f(b,a), f(f(b,a),a), ...`.
                                                && (!symbol.axioms.idem
                                                    || constructor_constants.iter().any(
                                                        |&(seed, seed_sort)| {
                                                            seed != added
                                                                && Some(seed) != identity_constant
                                                                && engine.sorts().leq(
                                                                    seed_sort,
                                                                    decl.domain
                                                                        [recursive_position],
                                                                )
                                                        },
                                                    ))
                                    })
                                })
                        })
                        .collect()
                } else {
                    vec![false; decl.domain.len()]
                };
                productions.push(Production {
                    symbol: symbol_id,
                    domain: decl.domain.clone(),
                    range: decl.range,
                    growing_arguments,
                });
                if has_identity {
                    for &sort in &user_sorts {
                        if engine.sorts().leq(decl.range, sort) {
                            identity_affected.entry(sort).or_insert(symbol_id);
                        }
                    }
                }
            }
        }

        let finite_override = validate_override_ids(overrides, num_sorts)?;
        let infinite_override: HashSet<SortId> = overrides.infinite.iter().copied().collect();
        if let Some(&sort) = finite_override.intersection(&infinite_override).next() {
            return Err(EligibilityRejection::OverlappingSortOverride { sort });
        }

        if !identity_affected.is_empty() {
            for (&sort, &symbol) in &identity_affected {
                if !overrides.explicit
                    || (!finite_override.contains(&sort) && !infinite_override.contains(&sort))
                {
                    return Err(
                        EligibilityRejection::IdentityClassificationRequiresOverride {
                            symbol,
                            sort,
                        },
                    );
                }
            }
        }

        let productive = productive_sorts(engine, &productions, num_sorts);
        let empty: HashSet<SortId> = (0..num_sorts)
            .map(|i| SortId::from_raw(i as u32))
            .filter(|sort| !productive[sort.index()])
            .collect();

        for &sort in &finite_override {
            if empty.contains(&sort) {
                return Err(EligibilityRejection::EmptyRequestedFiniteSort { sort });
            }
        }
        for &sort in &infinite_override {
            if empty.contains(&sort) {
                return Err(EligibilityRejection::FalseInfiniteSortOverride { sort });
            }
        }

        let dependencies = dependency_graph(engine, &productions, &productive, num_sorts, false);
        let growth_dependencies =
            dependency_graph(engine, &productions, &productive, num_sorts, true);
        let mut infinite = cycle_reachable_sorts(&growth_dependencies);

        for &sort in &finite_override {
            if infinite.contains(&sort) {
                return Err(EligibilityRejection::FalseFiniteSortOverride { sort });
            }
        }
        for &sort in &infinite_override {
            if !infinite.contains(&sort) && !identity_affected.contains_key(&sort) {
                return Err(EligibilityRejection::FalseInfiniteSortOverride { sort });
            }
            infinite.insert(sort);
        }
        // Cardinality is monotone along the sort order: every inhabitant of a subsort is also an
        // inhabitant of each supersort. This matters especially for caller-supplied identity cases.
        let infinite_seeds: Vec<SortId> = infinite.iter().copied().collect();
        for lower in infinite_seeds {
            for upper_index in 0..num_sorts {
                let upper = SortId::from_raw(upper_index as u32);
                if engine.sorts().leq(lower, upper) {
                    infinite.insert(upper);
                }
            }
        }

        // If a constructor result depends on a caller-classified or proved infinite argument, it is
        // infinite as well. This is the reverse reachability closure of result -> argument edges.
        propagate_infinity(&dependencies, &mut infinite);
        if let Some(&sort) = finite_override.intersection(&infinite).next() {
            return Err(EligibilityRejection::FalseFiniteSortOverride { sort });
        }

        let finite_sorts: HashSet<SortId> = (0..num_sorts)
            .map(|i| SortId::from_raw(i as u32))
            .filter(|sort| productive[sort.index()] && !infinite.contains(sort))
            .collect();

        let (finite, representative_roots) =
            generate_representatives(engine, &productions, &finite_sorts);

        // FVP, constructor-freeness modulo B, and OS-compactness are semantic preconditions that the
        // built signature alone cannot establish. Passing every definite check is therefore not a
        // fabricated syntactic proof.
        Ok(Self {
            eligibility: Eligibility::CallerPreconditioned,
            sorts: SortClassification {
                empty,
                infinite,
                finite,
            },
            _representative_roots: representative_roots,
        })
    }

    pub fn is_constructor_term(engine: &Engine, dag: DagId) -> bool {
        let mut pending = vec![dag];
        let mut seen = HashSet::new();
        while let Some(node_id) = pending.pop() {
            if !seen.insert(node_id) {
                continue;
            }
            let node = engine.node(node_id);
            // Variables are constructor terms by the standard homomorphic definition: only
            // operator occurrences, not variable leaves, must belong to the constructor signature.
            if node.variable_index().is_some() {
                continue;
            }
            if !engine.symbol(node.symbol()).is_constructor() {
                return false;
            }
            pending.extend(node.children());
        }
        true
    }

    pub fn representatives(&self, sort: SortId) -> Option<&[DagId]> {
        self.sorts.finite.get(&sort).map(Vec::as_slice)
    }
}

fn validate_override_ids(
    overrides: &SortOverrides,
    num_sorts: usize,
) -> Result<HashSet<SortId>, EligibilityRejection> {
    for &sort in overrides.finite.iter().chain(&overrides.infinite) {
        if sort.index() >= num_sorts {
            return Err(EligibilityRejection::UnknownSortOverride { sort });
        }
    }
    Ok(overrides.finite.iter().copied().collect())
}

fn constructor_preregular(engine: &Engine, symbol: SymbolId, user_sorts: &[SortId]) -> bool {
    let declarations = engine.symbol(symbol).decls();
    if declarations.len() < 2 {
        return true;
    }

    fn visit(
        engine: &Engine,
        declarations: &[crate::symbol::OpDeclaration],
        user_sorts: &[SortId],
        tuple: &mut Vec<SortId>,
        arity: usize,
    ) -> bool {
        if tuple.len() != arity {
            for &sort in user_sorts {
                tuple.push(sort);
                if !visit(engine, declarations, user_sorts, tuple, arity) {
                    return false;
                }
                tuple.pop();
            }
            return true;
        }

        let applicable: Vec<_> = declarations
            .iter()
            .filter(|decl| {
                tuple
                    .iter()
                    .zip(&decl.domain)
                    .all(|(&actual, &formal)| engine.sorts().leq(actual, formal))
            })
            .collect();
        applicable.len() < 2
            || applicable.iter().any(|candidate| {
                applicable
                    .iter()
                    .all(|other| engine.sorts().leq(candidate.range, other.range))
            })
    }

    let mut tuple = Vec::with_capacity(engine.symbol(symbol).arity());
    visit(
        engine,
        declarations,
        user_sorts,
        &mut tuple,
        engine.symbol(symbol).arity(),
    )
}

fn productive_sorts(engine: &Engine, productions: &[Production], num_sorts: usize) -> Vec<bool> {
    let mut productive = vec![false; num_sorts];
    loop {
        let mut changed = false;
        for production in productions {
            if production
                .domain
                .iter()
                .all(|sort| productive[sort.index()])
            {
                for (index, is_productive) in productive.iter_mut().enumerate().take(num_sorts) {
                    let sort = SortId::from_raw(index as u32);
                    if !*is_productive && engine.sorts().leq(production.range, sort) {
                        *is_productive = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            return productive;
        }
    }
}

fn dependency_graph(
    engine: &Engine,
    productions: &[Production],
    productive: &[bool],
    num_sorts: usize,
    growth_only: bool,
) -> Vec<Vec<usize>> {
    let mut graph = vec![Vec::new(); num_sorts];
    for production in productions {
        if !production
            .domain
            .iter()
            .all(|sort| productive[sort.index()])
        {
            continue;
        }
        for (result_index, dependencies) in graph.iter_mut().enumerate().take(num_sorts) {
            let result = SortId::from_raw(result_index as u32);
            if !engine.sorts().leq(production.range, result) {
                continue;
            }
            for (position, dependency) in production.domain.iter().enumerate() {
                if growth_only && !production.growing_arguments[position] {
                    continue;
                }
                let dependency = dependency.index();
                if !dependencies.contains(&dependency) {
                    dependencies.push(dependency);
                }
            }
        }
    }
    graph
}

fn cycle_reachable_sorts(graph: &[Vec<usize>]) -> HashSet<SortId> {
    let mut cyclic = vec![false; graph.len()];
    for start in 0..graph.len() {
        let mut seen = vec![false; graph.len()];
        let mut pending = graph[start].clone();
        while let Some(node) = pending.pop() {
            if node == start {
                cyclic[start] = true;
                break;
            }
            if seen[node] {
                continue;
            }
            seen[node] = true;
            pending.extend(graph[node].iter().copied());
        }
    }

    let mut infinite: HashSet<SortId> = cyclic
        .iter()
        .enumerate()
        .filter(|(_, is_cyclic)| **is_cyclic)
        .map(|(index, _)| SortId::from_raw(index as u32))
        .collect();
    propagate_infinity(graph, &mut infinite);
    infinite
}

fn propagate_infinity(graph: &[Vec<usize>], infinite: &mut HashSet<SortId>) {
    let mut predecessors = vec![Vec::new(); graph.len()];
    for (result, dependencies) in graph.iter().enumerate() {
        for &dependency in dependencies {
            predecessors[dependency].push(result);
        }
    }
    let mut pending: VecDeque<usize> = infinite.iter().map(|sort| sort.index()).collect();
    while let Some(dependency) = pending.pop_front() {
        for &result in &predecessors[dependency] {
            let result_sort = SortId::from_raw(result as u32);
            if infinite.insert(result_sort) {
                pending.push_back(result);
            }
        }
    }
}

fn generate_representatives(
    engine: &mut Engine,
    productions: &[Production],
    finite_sorts: &HashSet<SortId>,
) -> (HashMap<SortId, Vec<DagId>>, Vec<RootGuard>) {
    let mut representatives: HashMap<SortId, Vec<DagId>> = finite_sorts
        .iter()
        .copied()
        .map(|sort| (sort, Vec::new()))
        .collect();
    let mut roots = Vec::new();

    loop {
        let mut pending: HashMap<SortId, Vec<DagId>> = HashMap::new();
        for production in productions {
            if !finite_sorts
                .iter()
                .any(|&sort| engine.sorts().leq(production.range, sort))
            {
                continue;
            }
            let Some(argument_sets) = production
                .domain
                .iter()
                .map(|sort| representatives.get(sort).cloned())
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if argument_sets.iter().any(Vec::is_empty) {
                continue;
            }

            stream_product(&argument_sets, &mut Vec::new(), 0, &mut |arguments| {
                let node = engine.make_node(production.symbol, arguments.to_vec());
                let actual_sort = engine.sort_of(node);
                for &sort in finite_sorts {
                    if engine.sorts().leq(actual_sort, sort) {
                        let terms = pending.entry(sort).or_default();
                        if !terms.iter().any(|&old| engine.deep_equal(old, node)) {
                            terms.push(node);
                        }
                    }
                }
            });
        }

        let mut changed = false;
        for (sort, terms) in pending {
            let existing = representatives
                .get_mut(&sort)
                .expect("pending representative for non-finite sort");
            for term in terms {
                if !existing.iter().any(|&old| engine.deep_equal(old, term)) {
                    roots.push(engine.root(term));
                    existing.push(term);
                    changed = true;
                }
            }
        }
        if !changed {
            return (representatives, roots);
        }
    }
}

fn stream_product(
    sets: &[Vec<DagId>],
    current: &mut Vec<DagId>,
    index: usize,
    emit: &mut impl FnMut(&[DagId]),
) {
    if index == sets.len() {
        emit(current);
        return;
    }
    for &term in &sets[index] {
        current.push(term);
        stream_product(sets, current, index + 1, emit);
        current.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::IdentitySide;
    use crate::term::Term;

    fn acu_bag(constants: &[&str]) -> (Engine, SortId) {
        let mut engine = Engine::new();
        let bag = engine.add_sort("Bag");
        engine.close_sorts();

        let mt = engine.add_op("mt", vec![], bag);
        engine.set_ctor(mt);
        for &name in constants {
            let constant = engine.add_op(name, vec![], bag);
            engine.set_ctor(constant);
        }
        let union = engine.add_op_ac("_+_", vec![bag, bag], bag, Some(mt));
        engine.set_ctor(union);
        (engine, bag)
    }

    #[test]
    fn finite_override_rejects_unbounded_acu_bag() {
        let (mut engine, bag) = acu_bag(&["a", "b"]);
        let overrides = SortOverrides {
            finite: vec![bag],
            infinite: Vec::new(),
            explicit: true,
        };

        let rejection = ConstructorAnalysis::build(&mut engine, &overrides, false).err();

        assert_eq!(
            rejection,
            Some(EligibilityRejection::FalseFiniteSortOverride { sort: bag })
        );
    }

    #[test]
    fn finite_override_accepts_identity_only_acu_sort() {
        let (mut engine, bag) = acu_bag(&[]);
        let overrides = SortOverrides {
            finite: vec![bag],
            infinite: Vec::new(),
            explicit: true,
        };

        let analysis = match ConstructorAnalysis::build(&mut engine, &overrides, false) {
            Ok(analysis) => analysis,
            Err(rejection) => panic!("identity-only Bag was rejected: {rejection:?}"),
        };

        assert_eq!(analysis.representatives(bag).map(<[_]>::len), Some(1));
    }

    #[test]
    fn idempotence_distinguishes_finite_and_growing_cui_identity_families() {
        for (idempotent, expected_rejection) in [(true, false), (false, true)] {
            let mut engine = Engine::new();
            let sort = engine.add_sort("S");
            engine.close_sorts();
            let identity = engine.add_op("id", vec![], sort);
            let atom = engine.add_op("a", vec![], sort);
            let combine = engine.add_op_cui(
                "combine",
                vec![sort, sort],
                sort,
                true,
                idempotent,
                Some(identity),
            );
            for constructor in [identity, atom, combine] {
                engine.set_ctor(constructor);
            }
            let overrides = SortOverrides {
                finite: vec![sort],
                infinite: Vec::new(),
                explicit: true,
            };

            let result = ConstructorAnalysis::build(&mut engine, &overrides, false);

            if expected_rejection {
                assert_eq!(
                    result.err(),
                    Some(EligibilityRejection::FalseFiniteSortOverride { sort })
                );
            } else {
                let analysis = result.expect("idempotent one-atom family must be finite");
                assert_eq!(analysis.representatives(sort).map(<[_]>::len), Some(2));
            }
        }
    }

    #[test]
    fn finite_override_rejects_growing_one_sided_identity_family() {
        let mut engine = Engine::new();
        let sort = engine.add_sort("L");
        engine.close_sorts();
        let identity = engine.add_op("e", vec![], sort);
        let atom = engine.add_op("a", vec![], sort);
        let append = engine.add_op("_._", vec![sort, sort], sort);
        engine.reserve_one_sided_identity(append, IdentitySide::Left, sort);
        engine.set_one_sided_identity_term(append, Term::constant(identity));
        for constructor in [identity, atom, append] {
            engine.set_ctor(constructor);
        }
        let overrides = SortOverrides {
            finite: vec![sort],
            infinite: Vec::new(),
            explicit: true,
        };

        let rejection = ConstructorAnalysis::build(&mut engine, &overrides, false).err();

        assert_eq!(
            rejection,
            Some(EligibilityRejection::FalseFiniteSortOverride { sort })
        );
    }
}
