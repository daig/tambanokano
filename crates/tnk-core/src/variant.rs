//! Folding variant narrowing (S2): breadth-first one-step narrowing, variant-equation reducibility,
//! and term-only subsumption folding. The engine owns DAGs; a [`VariantSearch`] owns roots for every
//! retained state and borrows the engine only while constructing or advancing a layer.

use std::collections::{HashMap, VecDeque};

use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::fresh::{FreshVariableGenerator, VariableFamily};
use crate::num::Nat;
use crate::root::RootGuard;
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};
use crate::unify::filter::subsumes;
use crate::unify::problem::{UnifyProblem, VarSpec};
use crate::unify::{UnifyEnv, instantiate, is_ground};

/// An executable `[variant]` equation in module order. The frontend supplies the source terms and
/// variable names retained in `EqTrace`; keeping this separate from the ordinary rewrite automaton
/// avoids a second source representation in the kernel's equation table.
#[derive(Clone)]
pub struct VariantEquation {
    pub id: u32,
    pub lhs: Term,
    pub rhs: Term,
    pub variables: Vec<VarSpec>,
}

/// Compile a source `[variant]` equation with Maude's `PreEquation::check` variable layout:
/// normalize the lhs first, then assign its variable slots by canonical DAG traversal.
pub fn compile_variant_equation(
    e: &mut Engine,
    id: u32,
    lhs: &Term,
    rhs: &Term,
    variables: Vec<VarSpec>,
) -> VariantEquation {
    let mut substitution = Subst::new();
    substitution.reset(variables.len() as u32);
    for (slot, spec) in variables.iter().enumerate() {
        substitution.bind(slot as u32, e.make_var(spec.sort, spec.name, slot as u32));
    }
    let normalized_lhs = e.instantiate(lhs, &substitution);
    let normalized_lhs = e.normalize_for_unify(normalized_lhs);
    let mut order = Vec::with_capacity(variables.len());
    let mut work = vec![normalized_lhs];
    while let Some(dag) = work.pop() {
        if let NodeTerm::Var { index, .. } = e.node(dag).term {
            let slot = index as usize;
            if !order.contains(&slot) {
                order.push(slot);
            }
        } else {
            let children: Vec<_> = e.node(dag).children().collect();
            work.extend(children.into_iter().rev());
        }
    }
    // Executable equations normally have no rhs-only variables. Preserve a total mapping for a
    // malformed/nonexec trace anyway; its later screening remains responsible for rejecting it.
    for slot in 0..variables.len() {
        if !order.contains(&slot) {
            order.push(slot);
        }
    }
    let mut new_slots = vec![0; variables.len()];
    for (new, &old) in order.iter().enumerate() {
        new_slots[old] = new as u32;
    }
    fn remap(term: &Term, new_slots: &[u32]) -> Term {
        match term {
            Term::Var(var) => Term::var(new_slots[var.index as usize], var.sort),
            Term::Op { symbol, args } => Term::op(
                *symbol,
                args.iter().map(|arg| remap(arg, new_slots)).collect(),
            ),
            Term::Iter { symbol, count, arg } => {
                Term::iter(*symbol, count.clone(), remap(arg, new_slots))
            }
            Term::Na { symbol, value } => Term::Na {
                symbol: *symbol,
                value: value.clone(),
            },
        }
    }
    VariantEquation {
        id,
        lhs: remap(lhs, &new_slots),
        rhs: remap(rhs, &new_slots),
        variables: order.into_iter().map(|old| variables[old]).collect(),
    }
}

/// Whether generation may return variants layer-by-layer or must compute the final survivor set first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantMode {
    Incremental,
    Irredundant,
    /// Compute a complete term-only folding set for E∪Ax subsumption.
    Subsumption,
}

/// One externally visible variant. `index` and `parent` are zero-based external survivor numbers;
/// callers add one for the `Variant n` / `parent n` surface.
#[derive(Clone)]
pub struct VariantResult {
    pub index: usize,
    pub term: DagId,
    pub substitution: Vec<DagId>,
    /// True when this result is a completed variant unifier; `term` then only roots the
    /// state from which its substitution was produced and is not part of the result.
    pub unifier: bool,
    pub family: VariableFamily,
    pub parent: Option<usize>,
    pub more_in_layer: bool,
    /// Total rewrite count when this variant's layer became available.
    pub rewrites: u64,
}

/// One retained plain or filtered variant unifier. Roots keep every binding and each lazily
/// constructed subsumption-variant search alive across arena collections.
struct RetainedVariantUnifier {
    bindings: Vec<DagId>,
    family: VariableFamily,
    rewrites: u64,
    alive: bool,
    _roots: Vec<RootGuard>,
    variant_forms: Vec<Vec<DagId>>,
    _variant_search: Option<VariantSearch>,
}

/// Shared retention stream for object-level, metalevel, and narrowing variant unifiers.
///
/// `insert` preserves Maude's online eviction order. Call [`Self::finish`] before exposing an
/// upfront filtered result set; incremental callers can consume [`Self::pop_pending`] directly.
pub struct FilteredVariantUnifierStream {
    filtered: bool,
    retained: Vec<RetainedVariantUnifier>,
    pending: VecDeque<usize>,
    incomplete: bool,
}

impl FilteredVariantUnifierStream {
    pub fn new(filtered: bool) -> Self {
        Self {
            filtered,
            retained: Vec::new(),
            pending: VecDeque::new(),
            incomplete: false,
        }
    }

    pub fn is_filtered(&self) -> bool {
        self.filtered
    }

    fn retained_subsumes(&self, e: &mut Engine, index: usize, candidate: &[DagId]) -> bool {
        self.retained[index]
            .variant_forms
            .iter()
            .any(|form| unifier_subsumes(e, form, candidate))
    }

    fn make_retained(
        env: &mut UnifyEnv,
        bindings: Vec<DagId>,
        family: VariableFamily,
        rewrites: u64,
        equations: Vec<VariantEquation>,
        filtered: bool,
    ) -> (RetainedVariantUnifier, bool) {
        let roots = bindings.iter().map(|&dag| env.e.root(dag)).collect();
        let mut variant_forms = Vec::new();
        let mut variant_search = None;
        let mut incomplete = false;
        if filtered {
            if let Some(mut search) = unifier_variant_search(env, &bindings, equations, family) {
                while let Some(variant) = search.find_next(env) {
                    variant_forms.push(env.e.node(variant.term).children().collect());
                }
                incomplete |= search.is_incomplete();
                variant_search = Some(search);
            } else {
                variant_forms.push(bindings.clone());
            }
        }
        (
            RetainedVariantUnifier {
                bindings,
                family,
                rewrites,
                alive: true,
                _roots: roots,
                variant_forms,
                _variant_search: variant_search,
            },
            incomplete,
        )
    }

    pub fn insert(
        &mut self,
        env: &mut UnifyEnv,
        bindings: Vec<DagId>,
        family: VariableFamily,
        rewrites: u64,
        equations: &[VariantEquation],
    ) {
        if !self.filtered {
            let (retained, incomplete) = Self::make_retained(
                env,
                bindings,
                family,
                rewrites,
                Vec::new(),
                false,
            );
            let index = self.retained.len();
            self.incomplete |= incomplete;
            self.retained.push(retained);
            self.pending.push_back(index);
            return;
        }
        let existing: Vec<_> = self
            .retained
            .iter()
            .enumerate()
            .filter_map(|(index, retained)| retained.alive.then_some(index))
            .collect();
        for &index in &existing {
            if self.retained_subsumes(env.e, index, &bindings) {
                return;
            }
        }

        let (retained, incomplete) = Self::make_retained(
            env,
            bindings,
            family,
            rewrites,
            equations.to_vec(),
            true,
        );
        self.incomplete |= incomplete;
        for index in existing {
            if retained
                .variant_forms
                .iter()
                .any(|form| unifier_subsumes(env.e, form, &self.retained[index].bindings))
            {
                let victim = &mut self.retained[index];
                victim.alive = false;
                victim.bindings.clear();
                victim.variant_forms.clear();
                victim._variant_search = None;
                victim._roots.clear();
            }
        }
        let index = self.retained.len();
        self.retained.push(retained);
        self.pending.push_back(index);
    }

    /// Replace incremental insertion order with the final alive set in retained order.
    pub fn finish(&mut self) {
        self.pending.clear();
        self.pending.extend(
            self.retained
                .iter()
                .enumerate()
                .filter_map(|(index, retained)| retained.alive.then_some(index)),
        );
    }

    pub fn pop_pending(&mut self) -> Option<usize> {
        while let Some(index) = self.pending.pop_front() {
            if self.retained[index].alive {
                return Some(index);
            }
        }
        None
    }

    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }

    pub fn pending_is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    pub fn bindings(&self, index: usize) -> &[DagId] {
        &self.retained[index].bindings
    }

    pub fn family(&self, index: usize) -> VariableFamily {
        self.retained[index].family
    }

    pub fn rewrites(&self, index: usize) -> u64 {
        self.retained[index].rewrites
    }


    pub fn is_incomplete(&self) -> bool {
        self.incomplete
    }
    pub fn alive_len(&self) -> usize {
        self.retained.iter().filter(|retained| retained.alive).count()
    }
}

struct StoredVariant {
    term: DagId,
    substitution: Vec<DagId>,
    unifier: bool,
    family: VariableFamily,
    parent: Option<usize>,
    layer: usize,
    alive: bool,
    roots: Vec<RootGuard>,
}

impl StoredVariant {
    fn new(
        e: &Engine,
        term: DagId,
        substitution: Vec<DagId>,
        unifier: bool,
        family: VariableFamily,
        parent: Option<usize>,
        layer: usize,
    ) -> Self {
        let mut roots = Vec::with_capacity(substitution.len() + 1);
        roots.extend(substitution.iter().map(|&d| e.root(d)));
        roots.push(e.root(term));
        Self {
            term,
            substitution,
            unifier,
            family,
            parent,
            layer,
            alive: true,
            roots,
        }
    }
}

/// A resumable folding-variant search. Incremental mode expands only when its current output layer is
/// consumed; irredundant mode computes to exhaustion before exposing the first surviving variant.
pub struct VariantSearch {
    equations: Vec<VariantEquation>,
    blockers: Vec<DagId>,
    _blocker_roots: Vec<RootGuard>,
    variants: Vec<StoredVariant>,
    frontier: Vec<usize>,
    ready: VecDeque<usize>,
    external: HashMap<usize, usize>,
    next_external: usize,
    prepared: bool,
    incomplete: bool,
    base: String,
    first_family: VariableFamily,
    second_family: VariableFamily,
    use_first_family: bool,
    original_order: Vec<usize>,
    skip_root: bool,
    term_only_folding: bool,
    unification_pairs: Option<usize>,
}

impl VariantSearch {
    /// Construct the initial variant: rename every original variable into the first protected family,
    /// reduce the renamed term, and retain the full accumulated substitution.
    pub fn new(
        env: &mut UnifyEnv,
        initial: DagId,
        original_variables: Vec<VarSpec>,
        mut blockers: Vec<DagId>,
        equations: Vec<VariantEquation>,
        mode: VariantMode,
        incoming_family: Option<VariableFamily>,
        base: &str,
    ) -> Result<Self, String> {
        let input_initial = initial;
        let count_before_initial = env.e.rewrites();
        let input_cache_before = env.e.reduction_cache_state(input_initial);
        let first_family = if incoming_family == Some(VariableFamily::Unify) {
            VariableFamily::Variant
        } else {
            VariableFamily::Unify
        };
        let second_family =
            if incoming_family.is_none() || incoming_family == Some(VariableFamily::Narrow) {
                VariableFamily::Variant
            } else {
                VariableFamily::Narrow
            };
        // Maude theory-normalizes/canonically walks the target before assigning its original variable
        // slots. Reproduce that visible order, and move blocker-only variables above the target range.
        let original_order = variables_in_dag(env.e, initial);
        if original_order.len() != original_variables.len() {
            return Err("variant variable table does not match the command term".into());
        }
        let blocker_slots: Vec<usize> = blockers
            .iter()
            .flat_map(|&d| variables_in_dag(env.e, d))
            .collect();
        let max_slot = original_order
            .iter()
            .chain(&blocker_slots)
            .copied()
            .max()
            .map_or(0, |m| m + 1);
        let mut slot_map = vec![None; max_slot];
        for (new, &old) in original_order.iter().enumerate() {
            slot_map[old] = Some(new as u32);
        }
        let mut next = original_order.len() as u32;
        for old in blocker_slots {
            if slot_map[old].is_none() {
                slot_map[old] = Some(next);
                next += 1;
            }
        }
        let initial = if slot_map.is_empty() {
            initial
        } else {
            rebuild_slots(env.e, initial, &slot_map)
        };
        for blocker in &mut blockers {
            if !slot_map.is_empty() {
                *blocker = rebuild_slots(env.e, *blocker, &slot_map);
            }
        }
        let original_variables: Vec<VarSpec> = original_order
            .iter()
            .map(|&old| original_variables[old])
            .collect();
        let base_nat = Nat::from_decimal(base).unwrap_or_else(Nat::zero);
        let mut generator = FreshVariableGenerator::with_base(base_nat);
        let mut values = vec![None; original_variables.len()];
        let mut substitution = Vec::with_capacity(original_variables.len());
        for (slot, spec) in original_variables.iter().enumerate() {
            let name = env.names.code(generator.fresh_name(slot, first_family));
            let var = env.e.make_var(spec.sort, name, slot as u32);
            values[slot] = Some(var);
            substitution.push(var);
        }
        let renamed = rebuild_variables_preserving_reduced(
            env.e,
            initial,
            &mut |_, name, sort| {
                let slot = original_variables
                    .iter()
                    .position(|spec| spec.name == name && spec.sort == sort)
                    .expect("initial variant variable");
                values[slot].expect("fresh variant variable")
            },
        );
        let term = env.e.reduce(renamed);
        if std::env::var_os("TNK_NARROW_COUNT_TRACE").is_some() {
            let input_children: Vec<_> = env.e.node(input_initial).children().collect();
            let slotted_children: Vec<_> = env.e.node(initial).children().collect();
            let renamed_children: Vec<_> = env.e.node(renamed).children().collect();
            eprintln!(
                "NCOUNT variant-init order={original_order:?} family={first_family:?} input={input_initial:?}/{input_cache_before:?}/{input_children:?} slotted={initial:?}/{:?}/{slotted_children:?} renamed={renamed:?}/{:?}/{renamed_children:?} term={term:?}/{:?} equations={}",
                env.e.reduction_cache_state(initial),
                env.e.reduction_cache_state(renamed),
                env.e.reduction_cache_state(term),
                env.e.rewrites().saturating_sub(count_before_initial),
            );
        }

        for blocker in &mut blockers {
            *blocker = env.e.normalize_for_unify(*blocker);
            if reducible_by_variant_equation(env.e, *blocker, &equations) {
                return Err("irreducibility constraint is reducible by a variant equation".into());
            }
        }
        let blocker_roots = blockers.iter().map(|&d| env.e.root(d)).collect();
        let initial = StoredVariant::new(env.e, term, substitution, false, first_family, None, 0);
        Ok(Self {
            equations,
            blockers,
            _blocker_roots: blocker_roots,
            variants: vec![initial],
            frontier: vec![0],
            ready: VecDeque::from([0]),
            external: HashMap::new(),
            next_external: 0,
            prepared: mode == VariantMode::Incremental,
            incomplete: false,
            base: base.to_string(),
            first_family,
            second_family,
            // The initial variant uses the first family; its first descendants use the second.
            use_first_family: false,
            original_order,
            skip_root: false,
            term_only_folding: mode == VariantMode::Subsumption,
            unification_pairs: None,
        })
    }

    pub fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Exclude the synthetic root used to hold a simultaneous variant-unification problem.
    pub fn skip_root_position(&mut self) {
        self.skip_root = true;
    }

    /// Search a synthetic tuple of unification pairs. Root unifiers participate in the same
    /// one-step folder as equation narrowings, so a more general equation-generated unifier can
    /// evict a root unifier before either becomes externally visible.
    pub fn enable_unification(&mut self, e: &Engine, pair_count: usize) {
        self.skip_root = true;
        self.unification_pairs = Some(pair_count);
        if unification_pairs(e, self.variants[0].term, pair_count)
            .is_some_and(|pairs| pairs.iter().all(|&(lhs, rhs)| e.deep_equal(lhs, rhs)))
        {
            self.variants[0].unifier = true;
            self.frontier.clear();
        }
    }

    /// Apply variant-narrowing's accumulated-substitution and irreducibility-constraint screen to a
    /// completed unifier before the folder sees it.
    pub fn accepts_completed_unifier(&self, e: &mut Engine, bindings: &[DagId]) -> bool {
        !bindings
            .iter()
            .any(|&dag| reducible_by_variant_equation(e, dag, &self.equations))
            && !self.blocked(e, bindings)
    }

    pub fn variant_equations(&self) -> Vec<VariantEquation> {
        self.equations.clone()
    }

    /// Canonical target-variable order (new substitution slot → caller/source slot).
    pub fn original_variable_order(&self) -> &[usize] {
        &self.original_order
    }

    pub fn is_exhausted(&self) -> bool {
        self.prepared && self.ready.is_empty() && self.frontier.is_empty()
    }

    /// Return the next variant, expanding one breadth-first layer as needed. The result remains rooted
    /// by this search until it is dropped.
    pub fn find_next(&mut self, env: &mut UnifyEnv) -> Option<VariantResult> {
        if !self.prepared {
            self.ready.clear();
            while !self.frontier.is_empty() {
                self.expand_layer(env);
            }
            self.ready
                .extend(self.variants.iter().enumerate().filter_map(|(i, variant)| {
                    (variant.alive && (self.unification_pairs.is_none() || variant.unifier))
                        .then_some(i)
                }));
            self.prepared = true;
        }
        while self.ready.is_empty() && !self.frontier.is_empty() {
            self.expand_layer(env);
            self.ready
                .extend(self.frontier.iter().copied().filter(|&i| {
                    let variant = &self.variants[i];
                    variant.alive && (self.unification_pairs.is_none() || variant.unifier)
                }));
        }
        let internal = self.ready.pop_front()?;
        if !self.variants[internal].alive
            || (self.unification_pairs.is_some() && !self.variants[internal].unifier)
        {
            return self.find_next(env);
        }
        let external_index = self.next_external;
        self.next_external += 1;
        self.external.insert(internal, external_index);
        let variant = &self.variants[internal];
        let parent = variant.parent.and_then(|p| self.external.get(&p).copied());
        let more_in_layer = self.ready.iter().any(|&i| {
            self.variants[i].alive
                && (self.unification_pairs.is_none() || self.variants[i].unifier)
                && self.variants[i].layer == variant.layer
        });
        Some(VariantResult {
            index: external_index,
            term: variant.term,
            substitution: variant.substitution.clone(),
            unifier: variant.unifier,
            family: variant.family,
            parent,
            more_in_layer,
            rewrites: env.e.rewrites(),
        })
    }

    fn expand_layer(&mut self, env: &mut UnifyEnv) {
        let old_frontier = std::mem::take(&mut self.frontier);
        let family = if self.use_first_family {
            self.first_family
        } else {
            self.second_family
        };
        let mut next = Vec::new();
        for parent in old_frontier {
            if !self
                .variants
                .get(parent)
                .is_some_and(|variant| variant.alive && !variant.unifier)
            {
                continue;
            }
            let candidates = self.expand_variant(env, parent, family);
            for candidate in candidates {
                let index = self.variants.len();
                if self.insert_variant(env.e, candidate, parent, index) {
                    next.push(index);
                }
            }
        }
        next.retain(|&i| self.variants.get(i).is_some_and(|v| v.alive));
        self.frontier = next;
        self.use_first_family = !self.use_first_family;
    }

    fn expand_variant(
        &mut self,
        env: &mut UnifyEnv,
        parent: usize,
        family: VariableFamily,
    ) -> Vec<ExpandedVariant> {
        let (state_term, state_substitution) = {
            let v = &self.variants[parent];
            (v.term, v.substitution.clone())
        };
        let (state_term, state_substitution, state_specs, _, _) =
            reslot_state(env.e, state_term, &state_substitution);
        let mut results = Vec::new();
        if let Some(pair_count) = self.unification_pairs {
            let (completed, incomplete) = complete_state_unifier_detailed(
                env,
                state_term,
                &state_substitution,
                pair_count,
                family,
                &self.base,
            );
            self.incomplete |= incomplete;
            for completed in completed {
                if completed.interesting.iter().any(|&dag| {
                    let dag = env.e.normalize_for_unify(dag);
                    reducible_by_variant_equation(env.e, dag, &self.equations)
                }) {
                    continue;
                }
                if self.accepts_completed_unifier(env.e, &completed.bindings) {
                    results.push(ExpandedVariant {
                        term: state_term,
                        substitution: completed.bindings,
                        interesting: completed.interesting,
                        unifier: true,
                        family,
                    });
                }
            }
        }
        let state = PreparedVariantNarrowingState {
            term: state_term,
            substitution: state_substitution,
            variables: state_specs,
        };
        let (steps, incomplete) = variant_narrow_one_step(
            env,
            &state,
            &self.equations,
            &self.equations,
            &self.blockers,
            family,
            &self.base,
            self.skip_root,
            false,
            Some(&mut results),
        );
        self.incomplete |= incomplete;
        results.extend(steps.into_iter().map(|step| ExpandedVariant {
            term: step.term,
            substitution: step.substitution,
            interesting: step.interesting,
            unifier: false,
            family: step.family,
        }));
        results
    }

    fn blocked(&self, e: &mut Engine, substitution: &[DagId]) -> bool {
        let values: Vec<Option<DagId>> = substitution.iter().copied().map(Some).collect();
        self.blockers.iter().any(|&blocker| {
            let Some(dag) = instantiate(e, &values, blocker) else {
                return false;
            };
            let dag = e.normalize_for_unify(dag);
            reducible_by_variant_equation(e, dag, &self.equations)
        })
    }

    fn insert_variant(
        &mut self,
        e: &mut Engine,
        candidate: ExpandedVariant,
        parent: usize,
        index: usize,
    ) -> bool {
        let ExpandedVariant {
            term,
            substitution,
            unifier,
            family,
            ..
        } = candidate;
        for retained in self.variants.iter().filter(|variant| variant.alive) {
            let subsumes = if retained.unifier != unifier {
                false
            } else if unifier {
                unifier_subsumes(e, &retained.substitution, &substitution)
            } else {
                let retained_substitution = if self.term_only_folding {
                    &[][..]
                } else {
                    retained.substitution.as_slice()
                };
                let candidate_substitution = if self.term_only_folding {
                    &[][..]
                } else {
                    substitution.as_slice()
                };
                variant_subsumes(
                    e,
                    retained.term,
                    retained_substitution,
                    term,
                    candidate_substitution,
                )
            };
            if subsumes {
                return false;
            }
        }
        let mut ancestors = Vec::new();
        let mut ancestor = Some(parent);
        while let Some(index) = ancestor {
            ancestors.push(index);
            ancestor = self.variants[index].parent;
        }
        let mut evicted = Vec::new();
        for (i, retained) in self.variants.iter().enumerate().filter(|(_, v)| v.alive) {
            if ancestors.contains(&i) || retained.unifier != unifier {
                continue;
            }
            let subsumes = if unifier {
                unifier_subsumes(e, &substitution, &retained.substitution)
            } else {
                let candidate_substitution = if self.term_only_folding {
                    &[][..]
                } else {
                    substitution.as_slice()
                };
                let retained_substitution = if self.term_only_folding {
                    &[][..]
                } else {
                    retained.substitution.as_slice()
                };
                variant_subsumes(
                    e,
                    term,
                    candidate_substitution,
                    retained.term,
                    retained_substitution,
                )
            };
            if subsumes {
                evicted.push(i);
            }
        }
        if !evicted.is_empty() {
            for i in 0..self.variants.len() {
                if self.variants[i].alive
                    && evicted
                        .iter()
                        .any(|&ancestor| i == ancestor || self.descends_from(i, ancestor))
                {
                    self.variants[i].alive = false;
                    self.variants[i].roots.clear();
                }
            }
        }
        let layer = self.variants[parent].layer + 1;
        debug_assert_eq!(index, self.variants.len());
        self.variants.push(StoredVariant::new(
            e,
            term,
            substitution,
            unifier,
            family,
            Some(parent),
            layer,
        ));
        true
    }

    fn descends_from(&self, mut child: usize, ancestor: usize) -> bool {
        while let Some(parent) = self.variants[child].parent {
            if parent == ancestor {
                return true;
            }
            child = parent;
        }

        false
    }
}
pub(crate) trait VariantNarrowingSource {
    fn source_id(&self) -> u32;
    fn lhs(&self) -> &Term;
    fn rhs(&self) -> &Term;
    fn variables(&self) -> &[VarSpec];
}

impl VariantNarrowingSource for VariantEquation {
    fn source_id(&self) -> u32 {
        self.id
    }

    fn lhs(&self) -> &Term {
        &self.lhs
    }

    fn rhs(&self) -> &Term {
        &self.rhs
    }

    fn variables(&self) -> &[VarSpec] {
        &self.variables
    }
}

pub(crate) struct PreparedVariantNarrowingState {
    pub term: DagId,
    pub substitution: Vec<DagId>,
    pub variables: Vec<VarSpec>,
}

pub(crate) fn prepare_variant_narrowing_state(
    e: &mut Engine,
    term: DagId,
    substitution: &[DagId],
) -> PreparedVariantNarrowingState {
    let (term, substitution, variables, _, _) = reslot_state(e, term, substitution);
    PreparedVariantNarrowingState {
        term,
        substitution,
        variables,
    }
}

pub(crate) struct VariantNarrowingStep {
    pub term: DagId,
    pub substitution: Vec<DagId>,
    pub interesting: Vec<DagId>,
    pub family: VariableFamily,
    pub source_index: usize,
    pub source_id: u32,
    pub path: Vec<usize>,
    pub source_substitution: Vec<DagId>,
    pub state_unifier: Vec<DagId>,
}

/// One equation/rule-neutral variant-narrowing expansion. Every source shares one state-wide
/// unifier filter; irreducibility blockers and accumulated substitutions use the same S2 screens.
#[allow(clippy::too_many_arguments)]
pub(crate) fn variant_narrow_one_step<S: VariantNarrowingSource>(
    env: &mut UnifyEnv,
    state: &PreparedVariantNarrowingState,
    sources: &[S],
    equations: &[VariantEquation],
    blockers: &[DagId],
    family: VariableFamily,
    base: &str,
    skip_root: bool,
    respect_frozen: bool,
    mut competing: Option<&mut Vec<ExpandedVariant>>,
) -> (Vec<VariantNarrowingStep>, bool) {
    let interesting_slots = variables_in_dag(env.e, state.term);
    let mut positions = positions_breadth_first(env.e, state.term, respect_frozen);
    if skip_root && !positions.is_empty() {
        positions.remove(0);
    }
    let mut raw = Vec::new();
    let mut incomplete = false;

    for (path, redex) in positions {
        if matches!(env.e.node(redex).term, NodeTerm::Var { .. }) {
            continue;
        }
        let redex_kind = env.e.sorts().kind_of(env.e.sort_of(redex));
        for (source_index, source) in sources.iter().enumerate() {
            let source_kind = if let Some(lhs_top) = source.lhs().top_symbol() {
                env.e.symbol_kind(lhs_top)
            } else if let Term::Var(variable) = source.lhs() {
                env.e.sorts().kind_of(variable.sort)
            } else {
                continue;
            };
            if source_kind != redex_kind {
                continue;
            }
            let target_slots = variables_in_dag(env.e, redex);
            let source_n = source.variables().len();
            let state_base = env.e.minimum_substitution_size().max(source_n);
            let layout_size = state_base + state.variables.len();
            let local_of_state: Vec<_> = (0..state.variables.len())
                .map(|slot| Some((state_base + slot) as u32))
                .collect();
            let local_redex = remap_selected_slots(env.e, redex, &local_of_state);

            let mut source_subst = Subst::new();
            source_subst.reset(source_n as u32);
            for (slot, spec) in source.variables().iter().enumerate() {
                source_subst.bind(
                    slot as u32,
                    env.e.make_var(spec.sort, spec.name, slot as u32),
                );
            }
            let lhs = env.e.instantiate(source.lhs(), &source_subst);
            let mut active_specs: Vec<(usize, VarSpec)> =
                source.variables().iter().copied().enumerate().collect();
            active_specs.extend(
                state
                    .variables
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(slot, spec)| (state_base + slot, spec)),
            );
            let mut name_order = FreshVariableGenerator::with_base(
                Nat::from_decimal(base).unwrap_or_else(Nat::zero),
            );
            for slot in 0..active_specs.len() {
                env.names.code(name_order.fresh_name(slot, family));
            }
            let mut unificands = vec![(lhs, local_redex)];
            for slot in 0..state.variables.len() {
                if !target_slots.contains(&slot) {
                    let spec = state.variables[slot];
                    let variable =
                        env.e
                            .make_var(spec.sort, spec.name, (state_base + slot) as u32);
                    unificands.push((variable, variable));
                }
            }
            let mut problem = UnifyProblem::new_for_variant(
                env,
                unificands,
                active_specs,
                layout_size,
                family,
                base,
            );
            incomplete |= problem.is_incomplete();
            while let Some(caller) = problem.find_next_full(env) {
                incomplete |= problem.is_incomplete();
                let state_values = caller[state_base..].to_vec();
                let interesting: Vec<_> = interesting_slots
                    .iter()
                    .map(|&slot| state_values[slot].expect("state solution"))
                    .collect();
                if interesting.iter().any(|&dag| {
                    let dag = env.e.normalize_for_unify(dag);
                    reducible_by_variant_equation(env.e, dag, equations)
                }) {
                    continue;
                }
                raw.push(RawNarrowing {
                    path: path.clone(),
                    source_index,
                    source_values: caller[..source_n]
                        .iter()
                        .map(|value| value.expect("source solution"))
                        .collect(),
                    interesting,
                    state_values,
                });
            }
        }
    }

    let mut survivors: Vec<RawNarrowing> = Vec::new();
    'candidate: for candidate in raw {
        for retained in &survivors {
            if narrowing_subsumes(env.e, &retained.interesting, &candidate.interesting) {
                continue 'candidate;
            }
        }
        survivors.retain(|retained| {
            !narrowing_subsumes(env.e, &candidate.interesting, &retained.interesting)
        });
        survivors.push(candidate);
    }

    if let Some(competing) = competing.as_mut() {
        let mut filtered = Vec::new();
        'direct: for candidate in std::mem::take(*competing) {
            if filtered.iter().any(|retained: &ExpandedVariant| {
                unifier_subsumes(env.e, &retained.interesting, &candidate.interesting)
            }) {
                continue 'direct;
            }
            filtered.retain(|retained| {
                !unifier_subsumes(env.e, &candidate.interesting, &retained.interesting)
            });
            filtered.push(candidate);
        }
        **competing = filtered;
        survivors.retain(|candidate| {
            if competing.iter().any(|retained| {
                unifier_subsumes(env.e, &retained.interesting, &candidate.interesting)
            }) {
                return false;
            }
            competing.retain(|retained| {
                !unifier_subsumes(env.e, &candidate.interesting, &retained.interesting)
            });
            true
        });
    }

    let mut results = Vec::new();
    for candidate in survivors {
        let mut new_substitution = Vec::with_capacity(state.substitution.len());
        for dag in state.substitution.iter().copied() {
            let dag = instantiate(env.e, &candidate.state_values, dag).unwrap_or(dag);
            new_substitution.push(env.e.normalize_for_unify(dag));
        }
        if new_substitution
            .iter()
            .any(|&dag| reducible_by_variant_equation(env.e, dag, equations))
        {
            continue;
        }
        let values: Vec<Option<DagId>> = new_substitution.iter().copied().map(Some).collect();
        let blocked = blockers.iter().any(|&blocker| {
            let Some(dag) = instantiate(env.e, &values, blocker) else {
                return false;
            };
            let dag = env.e.normalize_for_unify(dag);
            reducible_by_variant_equation(env.e, dag, equations)
        });
        if blocked {
            continue;
        }
        let source = &sources[candidate.source_index];
        let mut rhs_subst = Subst::new();
        rhs_subst.reset(candidate.source_values.len() as u32);
        for (slot, &value) in candidate.source_values.iter().enumerate() {
            rhs_subst.bind(slot as u32, value);
        }
        let replacement = env.e.instantiate(source.rhs(), &rhs_subst);
        let rebuilt = replace_and_instantiate(
            env.e,
            state.term,
            &candidate.path,
            replacement,
            &candidate.state_values,
        );
        env.e.count_variant_narrowing_step();
        let term = env.e.reduce(rebuilt);
        let (term, substitution, _, _, _) = reslot_state(env.e, term, &new_substitution);
        let term = env.e.normalize_for_unify(term);
        let term = env.e.reduce(term);
        results.push(VariantNarrowingStep {
            term,
            substitution,
            interesting: candidate.interesting,
            family,
            source_index: candidate.source_index,
            source_id: source.source_id(),
            path: candidate.path,
            source_substitution: candidate.source_values,
            state_unifier: candidate
                .state_values
                .into_iter()
                .map(|value| value.expect("state solution"))
                .collect(),
        });
    }
    (results, incomplete)
}

pub(crate) struct ExpandedVariant {
    term: DagId,
    substitution: Vec<DagId>,
    interesting: Vec<DagId>,
    unifier: bool,
    family: VariableFamily,
}

struct CompletedStateUnifier {
    bindings: Vec<DagId>,
    interesting: Vec<DagId>,
}

struct RawNarrowing {
    path: Vec<usize>,
    source_index: usize,
    source_values: Vec<DagId>,
    state_values: Vec<Option<DagId>>,
    interesting: Vec<DagId>,
}

/// Maude compiles every interesting binding into one UnifierFilter match before solving the
/// accumulated theory subproblems. Our shared matcher drives each binding immediately, so checking
/// an underconstrained AC binding first can enumerate millions of partitions before a later bare
/// variable or free skeleton supplies the decisive prebindings. Reordering the pairs is logically
/// immaterial because they share one substitution; deterministic and cheaply failing pairs first
/// recreates the reference filter's effective constraint order.
fn narrowing_subsumes(e: &mut Engine, retained: &[DagId], candidate: &[DagId]) -> bool {
    if retained.len() != candidate.len() {
        return false;
    }
    let mut pairs: Vec<_> = retained
        .iter()
        .copied()
        .zip(candidate.iter().copied())
        .collect();
    pairs.sort_by_key(|&(pattern, subject)| matching_pair_cost(e, pattern, subject));
    let (patterns, subjects): (Vec<_>, Vec<_>) = pairs.into_iter().unzip();
    subsumes(e, &patterns, &subjects)
}

fn matching_pair_cost(e: &Engine, pattern: DagId, subject: DagId) -> (u8, u8, usize) {
    let pattern_node = e.node(pattern);
    if !matches!(pattern_node.term, NodeTerm::Var { .. })
        && pattern_node.symbol() != e.node(subject).symbol()
    {
        return (0, 0, 0);
    }
    let root_cost = match pattern_node.term {
        NodeTerm::Var { .. } => 0,
        NodeTerm::Free { .. } | NodeTerm::Na { .. } => 1,
        NodeTerm::S { .. } => 2,
        NodeTerm::Cui { .. } => 3,
        NodeTerm::Au { .. } => 4,
        NodeTerm::Acu { .. } => 5,
    };
    let mut theory_cost = root_cost;
    let mut size = 1;
    let mut work: Vec<_> = pattern_node.children().collect();
    while let Some(dag) = work.pop() {
        size += 1;
        let node = e.node(dag);
        theory_cost = theory_cost.max(match node.term {
            NodeTerm::Var { .. } => 0,
            NodeTerm::Free { .. } | NodeTerm::Na { .. } => 1,
            NodeTerm::S { .. } => 2,
            NodeTerm::Cui { .. } => 3,
            NodeTerm::Au { .. } => 4,
            NodeTerm::Acu { .. } => 5,
        });
        work.extend(node.children());
    }
    (theory_cost, root_cost, size)
}

/// Recursive child-first test used for accumulated bindings and irreducibility blockers.
pub fn reducible_by_variant_equation(
    e: &mut Engine,
    dag: DagId,
    equations: &[VariantEquation],
) -> bool {
    let mut previous = None;
    for child in e.node(dag).children().collect::<Vec<_>>() {
        if previous == Some(child) {
            continue; // one physical ACU argument, regardless of multiplicity
        }
        previous = Some(child);
        if reducible_by_variant_equation(e, child, equations) {
            return true;
        }
    }
    let kind = e.sorts().kind_of(e.sort_of(dag));
    for eq in equations {
        if eq
            .lhs
            .top_symbol()
            .is_some_and(|top| e.symbol_kind(top) == kind)
            && e.has_equation_match(&eq.lhs, eq.variables.len() as u32, dag, true)
        {
            return true;
        }
    }
    false
}
fn xor_signature(equations: &[VariantEquation]) -> Option<(SymbolId, SymbolId)> {
    let mut identity = None;
    for equation in equations {
        let (Term::Op { symbol, args }, Term::Var(rhs)) = (&equation.lhs, &equation.rhs) else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        for (variable, constant) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            if let (
                Term::Var(lhs),
                Term::Op {
                    symbol: identity_symbol,
                    args,
                },
            ) = (variable, constant)
                && lhs == rhs
                && args.is_empty()
            {
                identity = Some((*symbol, *identity_symbol));
            }
        }
    }
    let (xor, identity) = identity?;
    equations
        .iter()
        .any(|equation| {
            matches!(
                (&equation.lhs, &equation.rhs),
                (
                    Term::Op { symbol, args },
                    Term::Op { symbol: rhs, args: rhs_args }
                ) if *symbol == xor
                    && *rhs == identity
                    && rhs_args.is_empty()
                    && args.len() == 2
                    && matches!((&args[0], &args[1]), (Term::Var(a), Term::Var(b)) if a == b)
            )
        })
        .then_some((xor, identity))
}

fn toggle_atom(e: &Engine, atoms: &mut Vec<DagId>, atom: DagId) {
    if let Some(index) = atoms
        .iter()
        .position(|&existing| e.deep_equal(existing, atom))
    {
        atoms.swap_remove(index);
    } else {
        atoms.push(atom);
    }
}

fn xor_atoms(e: &Engine, dag: DagId, xor: SymbolId, identity: DagId, atoms: &mut Vec<DagId>) {
    if e.deep_equal(dag, identity) {
        return;
    }
    match &e.node(dag).term {
        NodeTerm::Acu { symbol, args } if *symbol == xor => {
            for &(child, multiplicity) in args {
                if multiplicity % 2 == 1 {
                    xor_atoms(e, child, xor, identity, atoms);
                }
            }
        }
        _ => toggle_atom(e, atoms, dag),
    }
}

fn contains_key_variable(e: &Engine, dag: DagId, keys: &[(u32, SortId)]) -> bool {
    match &e.node(dag).term {
        NodeTerm::Var { name, .. } => keys.contains(&(*name, e.sort_of(dag))),
        _ => e
            .node(dag)
            .children()
            .any(|child| contains_key_variable(e, child, keys)),
    }
}

fn linearize_xor_pattern(
    e: &Engine,
    dag: DagId,
    xor: SymbolId,
    identity: DagId,
    keys: &[(u32, SortId)],
    coefficients: &mut [bool],
    atoms: &mut Vec<DagId>,
) -> bool {
    if e.deep_equal(dag, identity) {
        return true;
    }
    match &e.node(dag).term {
        NodeTerm::Var { name, .. } => {
            let key = (*name, e.sort_of(dag));
            let Some(index) = keys.iter().position(|&candidate| candidate == key) else {
                return false;
            };
            coefficients[index] = !coefficients[index];
            true
        }
        NodeTerm::Acu { symbol, args } if *symbol == xor => {
            for &(child, multiplicity) in args {
                if multiplicity % 2 == 1
                    && !linearize_xor_pattern(e, child, xor, identity, keys, coefficients, atoms)
                {
                    return false;
                }
            }
            true
        }
        _ if contains_key_variable(e, dag, keys) => false,
        _ => {
            toggle_atom(e, atoms, dag);
            true
        }
    }
}

/// Fast exact ACUN-instance check for the common XOR variant theory. It solves the tuple's direct
/// XOR equations by Gaussian elimination and then verifies every (including free-rooted) binding by
/// actual equation reduction. `None` means the direct equations underdetermine a failed verification,
/// so the caller must use general variant subsumption.
pub fn xor_unifier_subsumes(
    e: &mut Engine,
    retained: &[DagId],
    candidate: &[DagId],
    equations: &[VariantEquation],
) -> Option<bool> {
    if retained.len() != candidate.len() {
        return Some(false);
    }
    let (xor, identity_symbol) = xor_signature(equations)?;
    let identity = e.make_free(identity_symbol, Vec::new());
    let mut keys = Vec::new();
    for &dag in retained {
        collect_variable_keys(e, dag, &mut keys);
    }
    if keys.is_empty() {
        return Some(
            retained
                .iter()
                .zip(candidate)
                .all(|(&left, &right)| e.deep_equal(left, right)),
        );
    }
    let mut rows: Vec<(Vec<bool>, Vec<DagId>)> = Vec::new();
    for (&pattern, &subject) in retained.iter().zip(candidate) {
        let mut coefficients = vec![false; keys.len()];
        let mut rhs = Vec::new();
        if !linearize_xor_pattern(
            e,
            pattern,
            xor,
            identity,
            &keys,
            &mut coefficients,
            &mut rhs,
        ) {
            continue;
        }
        xor_atoms(e, subject, xor, identity, &mut rhs);
        rows.push((coefficients, rhs));
    }
    if rows.is_empty() {
        return None;
    }
    let mut pivot_row_for_column = vec![None; keys.len()];
    let mut pivot_row = 0;
    for column in 0..keys.len() {
        let Some(found) = (pivot_row..rows.len()).find(|&row| rows[row].0[column]) else {
            continue;
        };
        rows.swap(pivot_row, found);
        for row in 0..rows.len() {
            if row == pivot_row || !rows[row].0[column] {
                continue;
            }
            for col in column..keys.len() {
                rows[row].0[col] ^= rows[pivot_row].0[col];
            }
            let pivot_rhs = rows[pivot_row].1.clone();
            for atom in pivot_rhs {
                toggle_atom(e, &mut rows[row].1, atom);
            }
        }
        pivot_row_for_column[column] = Some(pivot_row);
        pivot_row += 1;
    }
    if rows
        .iter()
        .any(|(coefficients, rhs)| !coefficients.iter().any(|&bit| bit) && !rhs.is_empty())
    {
        return Some(false);
    }
    let mut assignments = vec![identity; keys.len()];
    for (column, row) in pivot_row_for_column.iter().enumerate() {
        let Some(row) = row else { continue };
        let atoms = &rows[*row].1;
        assignments[column] = match atoms.as_slice() {
            [] => identity,
            [atom] => *atom,
            _ => e.make_acu(xor, atoms.iter().copied().map(|atom| (atom, 1)).collect()),
        };
    }
    let mut variables = Vec::new();
    let patterns: Vec<_> = retained
        .iter()
        .map(|&dag| dag_to_matching_term(e, dag, &mut variables))
        .collect();
    let mut substitution = Subst::new();
    substitution.reset(variables.len() as u32);
    for (slot, key) in variables.iter().enumerate() {
        let Some(index) = keys.iter().position(|candidate| candidate == key) else {
            return None;
        };
        substitution.bind(slot as u32, assignments[index]);
    }
    let matches = patterns.iter().zip(candidate).all(|(pattern, &subject)| {
        let instantiated = e.instantiate(pattern, &substitution);
        let normalized = e.reduce(instantiated);
        let normalized = e.normalize_for_unify(normalized);
        let normalized = e.reduce(normalized);
        e.deep_equal(normalized, subject)
    });
    if matches {
        Some(true)
    } else if pivot_row == keys.len() {
        Some(false)
    } else {
        None
    }
}

fn variant_subsumes(
    e: &mut Engine,
    retained_term: DagId,
    retained_substitution: &[DagId],
    candidate_term: DagId,
    candidate_substitution: &[DagId],
) -> bool {
    if retained_substitution.len() != candidate_substitution.len() {
        return false;
    }
    let mut variables = Vec::new();
    let mut patterns = Vec::with_capacity(retained_substitution.len() + 1);
    for &dag in retained_substitution {
        patterns.push(dag_to_matching_term(e, dag, &mut variables));
    }
    patterns.push(dag_to_matching_term(e, retained_term, &mut variables));
    let mut subjects = Vec::with_capacity(candidate_substitution.len() + 1);
    subjects.extend_from_slice(candidate_substitution);
    subjects.push(candidate_term);
    e.shared_match_exists(patterns, &subjects, variables.len() as u32)
}

/// Whether one retained unifier vector subsumes another modulo the signature axioms.
pub fn unifier_subsumes(e: &mut Engine, retained: &[DagId], candidate: &[DagId]) -> bool {
    if retained.len() != candidate.len() {
        return false;
    }
    let mut pairs: Vec<_> = retained
        .iter()
        .copied()
        .zip(candidate.iter().copied())
        .collect();
    pairs.sort_by_key(|&(pattern, subject)| matching_pair_cost(e, pattern, subject));
    let mut variables = Vec::new();
    let mut patterns = Vec::with_capacity(pairs.len());
    let mut subjects = Vec::with_capacity(pairs.len());
    for (pattern, subject) in pairs {
        patterns.push(dag_to_matching_term(e, pattern, &mut variables));
        subjects.push(subject);
    }
    e.shared_match_exists(patterns, &subjects, variables.len() as u32)
}

/// Match one retained variant term against a grounded subject and compose every theory match with
/// the variant's accumulated original-variable substitution.
pub fn variant_match_bindings(
    env: &mut UnifyEnv,
    variant: &VariantResult,
    subject: DagId,
    base: &str,
) -> Vec<Vec<DagId>> {
    let mut variables = Vec::new();
    let pattern = dag_to_matching_term(env.e, variant.term, &mut variables);
    let mut matcher_values = Vec::new();
    {
        let mut solutions = env
            .e
            .match_solutions(pattern, variables.len() as u32, subject, false);
        while solutions.advance() {
            matcher_values.push(
                (0..variables.len())
                    .map(|slot| {
                        solutions
                            .binding(slot as u32)
                            .expect("matched variant variable")
                    })
                    .collect::<Vec<_>>(),
            );
        }
    }
    matcher_values
        .into_iter()
        .map(|values| {
            let mut bindings: Vec<_> = variant
                .substitution
                .iter()
                .map(|&binding| {
                    rebuild_variables(env.e, binding, &mut |e, name, sort| {
                        variables
                            .iter()
                            .position(|&key| key == (name, sort))
                            .map_or_else(|| e.make_var(sort, name, 0), |slot| values[slot])
                    })
                })
                .collect();
            for binding in &mut bindings {
                *binding = env.e.normalize_for_unify(*binding);
            }
            let mut keys = Vec::new();
            for &binding in &bindings {
                collect_variable_keys(env.e, binding, &mut keys);
            }
            let mut generator = FreshVariableGenerator::with_base(
                Nat::from_decimal(base).unwrap_or_else(Nat::zero),
            );
            let replacements: Vec<_> = keys
                .iter()
                .enumerate()
                .map(|(index, &(name, sort))| {
                    let fresh = env
                        .names
                        .code(generator.fresh_name(index, VariableFamily::Unify));
                    ((name, sort), fresh, index as u32)
                })
                .collect();
            for binding in &mut bindings {
                *binding = rebuild_variables(env.e, *binding, &mut |e, name, sort| {
                    let (_, fresh, index) = replacements
                        .iter()
                        .find(|(key, _, _)| *key == (name, sort))
                        .expect("unbound matcher variable");
                    e.make_var(sort, *fresh, *index)
                });
                *binding = env.e.normalize_for_unify(*binding);
            }
            bindings
        })
        .collect()
}

/// Complete the simultaneous unification problem held in a synthetic free-rooted variant term and
/// compose each solved form with the variant's accumulated original-variable substitution.
pub fn complete_variant_unifier(
    env: &mut UnifyEnv,
    result: &VariantResult,
    pair_count: usize,
    family: VariableFamily,
    base: &str,
) -> Vec<Vec<DagId>> {
    complete_state_unifier_detailed(
        env,
        result.term,
        &result.substitution,
        pair_count,
        family,
        base,
    )
    .0
    .into_iter()
    .map(|completed| completed.bindings)
    .collect()
}

fn unification_pairs(e: &Engine, term: DagId, pair_count: usize) -> Option<Vec<(DagId, DagId)>> {
    let children: Vec<_> = e.node(term).children().collect();
    if pair_count == 1 {
        return (children.len() == 2).then(|| vec![(children[0], children[1])]);
    }
    if children.len() != 2 {
        return None;
    }
    let lhs: Vec<_> = e.node(children[0]).children().collect();
    let rhs: Vec<_> = e.node(children[1]).children().collect();
    if lhs.len() != pair_count || rhs.len() != pair_count {
        return None;
    }
    Some(lhs.into_iter().zip(rhs).collect())
}

fn complete_state_unifier_detailed(
    env: &mut UnifyEnv,
    state_term: DagId,
    state_substitution: &[DagId],
    pair_count: usize,
    family: VariableFamily,
    base: &str,
) -> (Vec<CompletedStateUnifier>, bool) {
    let (term, substitution, specs, _, _) = reslot_state(env.e, state_term, state_substitution);
    let state_base = env.e.minimum_substitution_size();
    let state_map: Vec<_> = (0..specs.len())
        .map(|slot| Some((state_base + slot) as u32))
        .collect();
    let problem_term = rebuild_slots(env.e, term, &state_map);
    let pairs = match unification_pairs(env.e, problem_term, pair_count) {
        Some(pairs) => pairs,
        None => return (Vec::new(), false),
    };
    let occurring = variables_in_dag(env.e, term);
    if pairs.iter().all(|&(lhs, rhs)| env.e.deep_equal(lhs, rhs)) {
        let mut bindings = substitution;
        let interesting: Vec<_> = occurring
            .iter()
            .map(|&slot| {
                let spec = specs[slot];
                env.e.make_var(spec.sort, spec.name, slot as u32)
            })
            .collect();
        let binding_count = bindings.len();
        bindings.extend_from_slice(&interesting);
        canonicalize_family_variables(env, &mut bindings, family, base);
        let interesting = bindings.split_off(binding_count);
        return (
            vec![CompletedStateUnifier {
                bindings,
                interesting,
            }],
            false,
        );
    }

    let mut unificands = pairs;
    for slot in 0..specs.len() {
        if !occurring.contains(&slot) {
            let spec = specs[slot];
            let variable = env
                .e
                .make_var(spec.sort, spec.name, (state_base + slot) as u32);
            unificands.push((variable, variable));
        }
    }
    let active_specs: Vec<(usize, VarSpec)> = specs
        .iter()
        .copied()
        .enumerate()
        .map(|(slot, spec)| (state_base + slot, spec))
        .collect();
    let mut problem = UnifyProblem::new_for_variant(
        env,
        unificands,
        active_specs,
        state_base + specs.len(),
        family,
        base,
    );
    let mut completed = Vec::new();
    while let Some(solution) = problem.find_next_full(env) {
        let values = solution[state_base..].to_vec();
        let interesting: Vec<_> = occurring
            .iter()
            .map(|&slot| values[slot].expect("interesting state variable"))
            .collect();
        let mut bindings = Vec::with_capacity(substitution.len());
        for dag in substitution.iter().copied() {
            let dag = instantiate(env.e, &values, dag).unwrap_or(dag);
            bindings.push(env.e.normalize_for_unify(dag));
        }
        let binding_count = bindings.len();
        bindings.extend_from_slice(&interesting);
        let upper_bound = state_base + specs.len() + solution.len() + bindings.len();
        retag_foreign_family_variables(env, &mut bindings, family, base, upper_bound);
        let interesting = bindings.split_off(binding_count);
        let mut keys = Vec::new();
        for &binding in &bindings {
            collect_variable_keys(env.e, binding, &mut keys);
        }
        bindings = bindings
            .into_iter()
            .map(|dag| reindex_by_keys(env.e, dag, &keys))
            .collect();
        completed.push(CompletedStateUnifier {
            bindings,
            interesting,
        });
    }
    (completed, problem.is_incomplete())
}

/// A solved narrowing form can leave an unconstrained target variable in the previous layer's
/// family. Retag those variables when they participate in a nontrivial unification solution;
/// substitution-only variables in an already-equal state are handled separately above.
fn retag_foreign_family_variables(
    env: &mut UnifyEnv,
    values: &mut [DagId],
    family: VariableFamily,
    base: &str,
    upper_bound: usize,
) {
    let mut keys = Vec::new();
    for &value in values.iter() {
        collect_variable_keys(env.e, value, &mut keys);
    }
    let mut generator =
        FreshVariableGenerator::with_base(Nat::from_decimal(base).unwrap_or_else(Nat::zero));
    let mut codes = Vec::with_capacity(upper_bound);
    for index in 0..upper_bound {
        let mut row = [0; 3];
        for candidate in VariableFamily::ALL {
            row[candidate as usize] = env.names.code(generator.fresh_name(index, candidate));
        }
        codes.push(row);
    }
    let mut used: Vec<(u32, SortId)> = keys
        .iter()
        .copied()
        .filter(|&(name, _)| codes.iter().any(|row| row[family as usize] == name))
        .collect();
    let mut replacements = Vec::new();
    for &(name, sort) in &keys {
        if used.contains(&(name, sort)) {
            continue;
        }
        let Some(preferred) = codes.iter().position(|row| {
            VariableFamily::ALL
                .iter()
                .copied()
                .filter(|&candidate| candidate != family)
                .any(|candidate| row[candidate as usize] == name)
        }) else {
            continue;
        };
        let target_index = if !used.contains(&(codes[preferred][family as usize], sort)) {
            preferred
        } else {
            (0..codes.len())
                .find(|&index| !used.contains(&(codes[index][family as usize], sort)))
                .expect("fresh-family reservation covers every completed variable")
        };
        let fresh = codes[target_index][family as usize];
        used.push((fresh, sort));
        replacements.push((name, sort, fresh));
    }
    if replacements.is_empty() {
        return;
    }
    for value in values {
        *value = rebuild_variables(env.e, *value, &mut |e, name, sort| {
            let fresh = replacements
                .iter()
                .find(|&&(candidate, candidate_sort, _)| {
                    candidate == name && candidate_sort == sort
                })
                .map_or(name, |&(_, _, fresh)| fresh);
            let index = keys
                .iter()
                .position(|&(candidate, candidate_sort)| {
                    candidate == name && candidate_sort == sort
                })
                .expect("completed-unifier variable");
            e.make_var(sort, fresh, index as u32)
        });
        *value = env.e.normalize_for_unify(*value);
    }
}
/// Rename a completed narrowing unifier into the family assigned to this expansion layer, ordered
/// by the composed original-variable bindings.
fn canonicalize_family_variables(
    env: &mut UnifyEnv,
    values: &mut [DagId],
    family: VariableFamily,
    base: &str,
) {
    let mut keys = Vec::new();
    for &value in values.iter() {
        collect_variable_keys(env.e, value, &mut keys);
    }
    let mut generator =
        FreshVariableGenerator::with_base(Nat::from_decimal(base).unwrap_or_else(Nat::zero));
    let replacements: Vec<_> = keys
        .iter()
        .enumerate()
        .map(|(index, &(name, sort))| {
            let fresh = env.names.code(generator.fresh_name(index, family));
            (name, sort, fresh, index as u32)
        })
        .collect();
    for value in values {
        *value = rebuild_variables(env.e, *value, &mut |e, name, sort| {
            let &(_, _, fresh, index) = replacements
                .iter()
                .find(|&&(candidate, candidate_sort, _, _)| {
                    candidate == name && candidate_sort == sort
                })
                .expect("completed-unifier variable");
            e.make_var(sort, fresh, index)
        });
        *value = env.e.normalize_for_unify(*value);
    }
}

pub fn unifier_variant_search(
    env: &mut UnifyEnv,
    retained: &[DagId],
    equations: Vec<VariantEquation>,
    incoming_family: VariableFamily,
) -> Option<VariantSearch> {
    if retained.is_empty() {
        return None;
    }
    let domains: Vec<_> = retained
        .iter()
        .map(|&dag| {
            let kind = env.e.sorts().kind_of(env.e.sort_of(dag));
            env.e.sorts().error_sort(kind)
        })
        .collect();
    let tuple = env
        .e
        .add_op("$variant-subsumption-tuple", domains.clone(), domains[0]);
    let target = env.e.make_free(tuple, retained.to_vec());
    let (target, _, specs, _, _) = reslot_state(env.e, target, &[]);
    let mut search = VariantSearch::new(
        env,
        target,
        specs,
        Vec::new(),
        equations,
        VariantMode::Subsumption,
        Some(incoming_family),
        "0",
    )
    .ok()?;
    search.skip_root_position();
    Some(search)
}

pub fn unifier_subsumes_modulo_variants(
    env: &mut UnifyEnv,
    retained: &[DagId],
    candidate: &[DagId],
    equations: Vec<VariantEquation>,
    incoming_family: VariableFamily,
) -> bool {
    if retained.len() != candidate.len() {
        return false;
    }
    if unifier_subsumes(env.e, retained, candidate) {
        return true;
    }
    let Some(mut search) = unifier_variant_search(env, retained, equations, incoming_family) else {
        return retained.is_empty();
    };
    while let Some(variant) = search.find_next(env) {
        let form: Vec<_> = env.e.node(variant.term).children().collect();
        if unifier_subsumes(env.e, &form, candidate) {
            return true;
        }
    }
    false
}

fn dag_to_matching_term(e: &Engine, dag: DagId, variables: &mut Vec<(u32, SortId)>) -> Term {
    match &e.node(dag).term {
        NodeTerm::Var { name, .. } => {
            let key = (*name, e.sort_of(dag));
            let slot = match variables.iter().position(|&candidate| candidate == key) {
                Some(slot) => slot,
                None => {
                    variables.push(key);
                    variables.len() - 1
                }
            };
            Term::var(slot as u32, key.1)
        }
        NodeTerm::Free { symbol, args }
        | NodeTerm::Au { symbol, args }
        | NodeTerm::Cui { symbol, args } => Term::op(
            *symbol,
            args.iter()
                .map(|&child| dag_to_matching_term(e, child, variables))
                .collect(),
        ),
        NodeTerm::Acu { symbol, args } => Term::op(
            *symbol,
            args.iter()
                .flat_map(|&(child, multiplicity)| {
                    std::iter::repeat_n(child, multiplicity as usize)
                })
                .map(|child| dag_to_matching_term(e, child, variables))
                .collect(),
        ),
        NodeTerm::S { symbol, count, arg } => Term::iter(
            *symbol,
            count.clone(),
            dag_to_matching_term(e, *arg, variables),
        ),
        NodeTerm::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
    }
}

/// Convert a canonical runtime DAG back to a static command term while preserving its caller-assigned
/// variable slots. This is used only for Maude's normalized command echo.
pub fn term_from_dag_slots(e: &Engine, dag: DagId) -> Term {
    match &e.node(dag).term {
        NodeTerm::Var { index, .. } => Term::var(*index, e.sort_of(dag)),
        NodeTerm::Free { symbol, args } => Term::op(
            *symbol,
            args.iter().map(|&d| term_from_dag_slots(e, d)).collect(),
        ),
        NodeTerm::Acu { symbol, args } => Term::op(
            *symbol,
            args.iter()
                .flat_map(|&(d, multiplicity)| {
                    std::iter::repeat_with(move || term_from_dag_slots(e, d))
                        .take(multiplicity as usize)
                })
                .collect(),
        ),
        NodeTerm::Au { symbol, args } => Term::op(
            *symbol,
            args.iter().map(|&d| term_from_dag_slots(e, d)).collect(),
        ),
        NodeTerm::Cui { symbol, args } => Term::op(
            *symbol,
            args.iter().map(|&d| term_from_dag_slots(e, d)).collect(),
        ),
        NodeTerm::S { symbol, count, arg } => {
            Term::iter(*symbol, count.clone(), term_from_dag_slots(e, *arg))
        }
        NodeTerm::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
    }
}

/// Reindex every variable shared by a state's term/substitution by `(name, sort)`. Maude indexes the
/// variant term first and then adds variables occurring only in the accumulated substitution.
fn reslot_state(
    e: &mut Engine,
    term: DagId,
    substitution: &[DagId],
) -> (DagId, Vec<DagId>, Vec<VarSpec>, Vec<DagId>, usize) {
    // Narrowing replacement and substitution composition can retain an AC argument order that was
    // canonical before instantiation but is stale afterward. Maude's DAGs restore that order before
    // `indexVariables`; do the same so fresh-slot assignment follows canonical term traversal.
    let term = e.normalize_for_unify(term);
    let substitution: Vec<_> = substitution
        .iter()
        .map(|&dag| e.normalize_for_unify(dag))
        .collect();
    let mut keys = Vec::new();
    collect_variable_keys(e, term, &mut keys);
    for &dag in &substitution {
        collect_variable_keys(e, dag, &mut keys);
    }
    let n_interesting = variables_in_dag(e, term).len();
    let specs: Vec<VarSpec> = keys
        .iter()
        .map(|&(name, sort)| VarSpec { name, sort })
        .collect();
    let term = reindex_by_keys(e, term, &keys);
    let substitution = substitution
        .into_iter()
        .map(|dag| reindex_by_keys(e, dag, &keys))
        .collect();
    let vars = specs
        .iter()
        .enumerate()
        .map(|(slot, spec)| e.make_var(spec.sort, spec.name, slot as u32))
        .collect();
    (term, substitution, specs, vars, n_interesting)
}

fn collect_variable_keys(e: &Engine, root: DagId, keys: &mut Vec<(u32, SortId)>) {
    let mut work = vec![root];
    while let Some(d) = work.pop() {
        match &e.node(d).term {
            NodeTerm::Var { name, .. } => {
                let key = (*name, e.sort_of(d));
                if !keys.contains(&key) {
                    keys.push(key);
                }
            }
            _ => {
                let children: Vec<_> = e.node(d).children().collect();
                work.extend(children.into_iter().rev());
            }
        }
    }
}

fn reindex_by_keys(e: &mut Engine, dag: DagId, keys: &[(u32, SortId)]) -> DagId {
    rebuild_variables_preserving_reduced(e, dag, &mut |e, name, sort| {
        let slot = keys
            .iter()
            .position(|&k| k == (name, sort))
            .expect("state variable key");
        e.make_var(sort, name, slot as u32)
    })
}

pub fn variables_in_dag(e: &Engine, root: DagId) -> Vec<usize> {
    let mut slots = Vec::new();
    let mut work = vec![root];
    while let Some(d) = work.pop() {
        match &e.node(d).term {
            NodeTerm::Var { index, .. } => {
                let slot = *index as usize;
                if !slots.contains(&slot) {
                    slots.push(slot);
                }
            }
            _ => {
                let children: Vec<_> = e.node(d).children().collect();
                work.extend(children.into_iter().rev());
            }
        }
    }
    slots
}

fn remap_selected_slots(e: &mut Engine, dag: DagId, local: &[Option<u32>]) -> DagId {
    rebuild_slots(e, dag, local)
}

/// Replace every variable in a variant-match subject by a fresh internal constant. The returned
/// pairs map each constant back to the original subject variable for result rendering.
pub fn ground_subject_variables(e: &mut Engine, dag: DagId) -> (DagId, Vec<(DagId, DagId)>) {
    let mut keys = Vec::new();
    collect_variable_keys(e, dag, &mut keys);
    let replacements: Vec<_> = keys
        .iter()
        .enumerate()
        .map(|(index, &(name, sort))| {
            let symbol = e.add_op(format!("$variant-match-ground-{index}"), Vec::new(), sort);
            let constant = e.make_free(symbol, Vec::new());
            let variable = e.make_var(sort, name, index as u32);
            (name, sort, constant, variable)
        })
        .collect();
    let grounded = rebuild_variables(e, dag, &mut |_, name, sort| {
        replacements
            .iter()
            .find(|&&(candidate, candidate_sort, _, _)| candidate == name && candidate_sort == sort)
            .map(|&(_, _, constant, _)| constant)
            .expect("subject variable replacement")
    });
    let restorations = replacements
        .into_iter()
        .map(|(_, _, constant, variable)| (constant, variable))
        .collect();
    (grounded, restorations)
}

/// Restore variant-match subject constants in one result binding.
pub fn restore_subject_variables(
    e: &mut Engine,
    dag: DagId,
    restorations: &[(DagId, DagId)],
) -> DagId {
    if let Some((_, variable)) = restorations
        .iter()
        .find(|&&(constant, _)| e.deep_equal(dag, constant))
    {
        return *variable;
    }
    enum Shape {
        Free(SymbolId, Vec<DagId>),
        Acu(SymbolId, Vec<(DagId, u32)>),
        Au(SymbolId, Vec<DagId>),
        Cui(SymbolId, Vec<DagId>),
        S(SymbolId, Nat, DagId),
        Leaf,
    }
    let shape = match &e.node(dag).term {
        NodeTerm::Free { symbol, args } if !args.is_empty() => Shape::Free(*symbol, args.clone()),
        NodeTerm::Acu { symbol, args } => Shape::Acu(*symbol, args.clone()),
        NodeTerm::Au { symbol, args } => Shape::Au(*symbol, args.clone()),
        NodeTerm::Cui { symbol, args } => Shape::Cui(*symbol, args.clone()),
        NodeTerm::S { symbol, count, arg } => Shape::S(*symbol, count.clone(), *arg),
        _ => Shape::Leaf,
    };
    match shape {
        Shape::Free(symbol, args) => {
            let args = args
                .into_iter()
                .map(|child| restore_subject_variables(e, child, restorations))
                .collect();
            e.make_free(symbol, args)
        }
        Shape::Acu(symbol, args) => {
            let args = args
                .into_iter()
                .map(|(child, multiplicity)| {
                    (
                        restore_subject_variables(e, child, restorations),
                        multiplicity,
                    )
                })
                .collect();
            e.make_acu_preserving_order(symbol, args)
        }
        Shape::Au(symbol, args) => {
            let args = args
                .into_iter()
                .map(|child| restore_subject_variables(e, child, restorations))
                .collect();
            e.make_au(symbol, args)
        }
        Shape::Cui(symbol, args) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|child| restore_subject_variables(e, child, restorations))
                .collect();
            e.make_cui(symbol, args[0], args[1])
        }
        Shape::S(symbol, count, arg) => {
            let arg = restore_subject_variables(e, arg, restorations);
            e.make_iter_decimal(symbol, &count.to_decimal(), arg)
                .expect("valid Nat count")
        }
        Shape::Leaf => dag,
    }
}

fn rebuild_variables(
    e: &mut Engine,
    dag: DagId,
    leaf: &mut dyn FnMut(&mut Engine, u32, SortId) -> DagId,
) -> DagId {
    rebuild_variables_inner(e, dag, leaf, false)
}

fn rebuild_variables_preserving_reduced(
    e: &mut Engine,
    dag: DagId,
    leaf: &mut dyn FnMut(&mut Engine, u32, SortId) -> DagId,
) -> DagId {
    rebuild_variables_inner(e, dag, leaf, true)
}

/// Generic variable-leaf rebuild preserving every theory representation.
fn rebuild_variables_inner(
    e: &mut Engine,
    dag: DagId,
    leaf: &mut dyn FnMut(&mut Engine, u32, SortId) -> DagId,
    preserve_reduced: bool,
) -> DagId {
    if is_ground(e, dag) {
        return dag;
    }
    enum Shape {
        Var(u32, SortId),
        Free(SymbolId, Vec<DagId>),
        Acu(SymbolId, Vec<(DagId, u32)>),
        Au(SymbolId, Vec<DagId>),
        Cui(SymbolId, Vec<DagId>),
        S(SymbolId, Nat, DagId),
        Ground,
    }
    let shape = match &e.node(dag).term {
        NodeTerm::Var { name, .. } => Shape::Var(*name, e.sort_of(dag)),
        NodeTerm::Free { symbol, args } => Shape::Free(*symbol, args.clone()),
        NodeTerm::Acu { symbol, args } => Shape::Acu(*symbol, args.clone()),
        NodeTerm::Au { symbol, args } => Shape::Au(*symbol, args.clone()),
        NodeTerm::Cui { symbol, args } => Shape::Cui(*symbol, args.clone()),
        NodeTerm::S { symbol, count, arg } => Shape::S(*symbol, count.clone(), *arg),
        NodeTerm::Na { .. } => Shape::Ground,
    };
    let rebuilt = match shape {
        Shape::Var(name, sort) => leaf(e, name, sort),
        Shape::Free(symbol, args) => {
            let args = args
                .into_iter()
                .map(|d| rebuild_variables_inner(e, d, leaf, preserve_reduced))
                .collect();
            e.make_free(symbol, args)
        }
        Shape::Acu(symbol, args) => {
            let args = args
                .into_iter()
                .map(|(d, m)| (rebuild_variables_inner(e, d, leaf, preserve_reduced), m))
                .collect();
            e.make_acu_preserving_order(symbol, args)
        }
        Shape::Au(symbol, args) => {
            let args = args
                .into_iter()
                .map(|d| rebuild_variables_inner(e, d, leaf, preserve_reduced))
                .collect();
            e.make_au(symbol, args)
        }
        Shape::Cui(symbol, args) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|d| rebuild_variables_inner(e, d, leaf, preserve_reduced))
                .collect();
            e.make_cui(symbol, args[0], args[1])
        }
        Shape::S(symbol, count, arg) => {
            let arg = rebuild_variables_inner(e, arg, leaf, preserve_reduced);
            e.make_iter_decimal(symbol, &count.to_decimal(), arg)
                .expect("valid Nat count")
        }
        Shape::Ground => dag,
    };
    if preserve_reduced {
        e.inherit_reduced_status(dag, rebuilt);
    }
    rebuilt
}

/// Indexed version needed to map a state's slots into one local unification problem.
fn rebuild_slots(e: &mut Engine, dag: DagId, map: &[Option<u32>]) -> DagId {
    enum Shape {
        Var(u32, u32, SortId),
        Free(SymbolId, Vec<DagId>),
        Acu(SymbolId, Vec<(DagId, u32)>),
        Au(SymbolId, Vec<DagId>),
        Cui(SymbolId, Vec<DagId>),
        S(SymbolId, Nat, DagId),
        Ground,
    }
    if is_ground(e, dag) {
        return dag;
    }
    let shape = match &e.node(dag).term {
        NodeTerm::Var { name, index, .. } => Shape::Var(*name, *index, e.sort_of(dag)),
        NodeTerm::Free { symbol, args } => Shape::Free(*symbol, args.clone()),
        NodeTerm::Acu { symbol, args } => Shape::Acu(*symbol, args.clone()),
        NodeTerm::Au { symbol, args } => Shape::Au(*symbol, args.clone()),
        NodeTerm::Cui { symbol, args } => Shape::Cui(*symbol, args.clone()),
        NodeTerm::S { symbol, count, arg } => Shape::S(*symbol, count.clone(), *arg),
        NodeTerm::Na { .. } => Shape::Ground,
    };
    let rebuilt = match shape {
        Shape::Var(name, old, sort) => {
            e.make_var(sort, name, map[old as usize].expect("selected slot"))
        }
        Shape::Free(symbol, args) => {
            let args = args.into_iter().map(|d| rebuild_slots(e, d, map)).collect();
            e.make_free(symbol, args)
        }
        Shape::Acu(symbol, args) => {
            let args = args
                .into_iter()
                .map(|(d, m)| (rebuild_slots(e, d, map), m))
                .collect();
            e.make_acu(symbol, args)
        }
        Shape::Au(symbol, args) => {
            let args = args.into_iter().map(|d| rebuild_slots(e, d, map)).collect();
            e.make_au(symbol, args)
        }
        Shape::Cui(symbol, args) => {
            let args: Vec<_> = args.into_iter().map(|d| rebuild_slots(e, d, map)).collect();
            e.make_cui(symbol, args[0], args[1])
        }
        Shape::S(symbol, count, arg) => {
            let arg = rebuild_slots(e, arg, map);
            e.make_iter_decimal(symbol, &count.to_decimal(), arg)
                .expect("valid Nat count")
        }
        Shape::Ground => dag,
    };
    e.inherit_reduced_status(dag, rebuilt);
    rebuilt
}

fn positions_breadth_first(
    e: &Engine,
    root: DagId,
    respect_frozen: bool,
) -> Vec<(Vec<usize>, DagId)> {
    let mut result = Vec::new();
    let mut queue = VecDeque::from([(Vec::new(), root)]);
    while let Some((path, dag)) = queue.pop_front() {
        result.push((path.clone(), dag));
        let symbol = e.node(dag).symbol();
        let children: Vec<_> = e.node(dag).children().collect();
        let mut previous = None;
        for (index, child) in children.into_iter().enumerate() {
            if previous == Some(child) || (respect_frozen && e.is_frozen_arg(symbol, index)) {
                continue;
            }
            previous = Some(child);
            let mut child_path = path.clone();
            child_path.push(index);
            queue.push_back((child_path, child));
        }
    }
    result
}

fn replace_and_instantiate(
    e: &mut Engine,
    dag: DagId,
    path: &[usize],
    replacement: DagId,
    values: &[Option<DagId>],
) -> DagId {
    if path.is_empty() {
        return replacement;
    }
    let symbol = e.node(dag).symbol();
    let mut children: Vec<_> = e.node(dag).children().collect();
    let selected = path[0];
    for (index, child) in children.iter_mut().enumerate() {
        *child = if index == selected {
            replace_and_instantiate(e, *child, &path[1..], replacement, values)
        } else {
            instantiate(e, values, *child).unwrap_or(*child)
        };
    }
    match &e.node(dag).term {
        NodeTerm::S { count, .. } => e
            .make_iter_decimal(symbol, &count.to_decimal(), children[0])
            .expect("valid Nat count"),
        _ => e.make_node(symbol, children),
    }
}
