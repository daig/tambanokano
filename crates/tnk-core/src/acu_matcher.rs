//! Lazy ACU solution enumerator for the **no-alien** case, driven by [`DiophantineSystem`].
//!
//! When every non-ground pattern subterm is a top variable, matching reduces to a Diophantine
//! system: one row per top variable (coefficient = multiplicity, size bounds from the variable sort
//! and identity capability), one column per residual subject element, plus one extension row when
//! matching with a residue. Solutions are enumerated lazily. A repeated sole variable in extension
//! mode takes a dedicated fast path in which every divisible subject multiplicity contributes to one
//! maximal binding.
//!
//! Element variables (`upper_bound == 1`) use an ordinary Diophantine row. Rows sort by ascending
//! maximum size, so element variables enumerate outside collector variables without a separate
//! bipartite pattern representation.
//!
//! Empty-multiset and no-variable matches use finite modes without constructing a system. Extension
//! matching retains the unmatched subject portion: matching `a + X` against `a + b + d` leaves
//! `b + d`. A degenerate all-identity/all-extension no-op is skipped unless the subject is the
//! identity or the pattern has ground subterms.

use crate::dag::DagId;
use crate::diophantine::{DiophantineSystem, UNBOUNDED};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::{IdentityId, SymbolId};
use crate::term::Subst;

/// One top variable of the pattern (all occurrences of an index merged): its substitution index, its
/// multiplicity (Diophantine coefficient), size bounds, and declared sort.
#[derive(Clone)]
pub(crate) struct MatcherVar {
    pub index: u32,
    pub coeff: u32,
    pub lower_bound: i32,
    pub upper_bound: i32,
    pub sort: SortId,
}

/// The enumeration mode, decided once at [`AcuMatcher::new`] from the residual multiset + variables.
enum Mode {
    /// No unbound top variables: at most one solution, with the residual multiset as extension or
    /// an empty residual as a whole match.
    NoVar { done: bool },
    /// Variables with an empty residual bind to identity exactly once when every variable permits it.
    Trivial { done: bool },
    /// The general Diophantine system. `subject_map[col]` is the element index of column `col`;
    /// `ext_row` is the extension row's insertion index (`nr_vars`) when matching with a residue.
    System {
        sys: DiophantineSystem,
        subject_map: Vec<usize>,
        ext_row: Option<usize>,
    },
    /// Exhausted / statically infeasible.
    Done,
}

/// A resumable enumerator over the ACU solutions of a no-alien pattern against a residual subject
/// multiset. Owns all its state; [`next`](Self::next) binds the next solution into the shared `Subst`
/// (building fresh binding nodes, hence `&mut Runtime`) and returns `true`, or `false` when exhausted.
pub(crate) struct AcuMatcher {
    symbol: SymbolId,
    identity: Option<IdentityId>,
    ext_allowed: bool,
    has_grounds: bool,
    subject_is_identity: bool,
    vars: Vec<MatcherVar>,
    /// Residual subject elements after ground consumption, aligned with the Diophantine columns.
    elements: Vec<DagId>,
    /// The nonzero residual `(element, multiplicity)` pairs. This is the [`Mode::NoVar`] residue and
    /// supplies the Diophantine columns.
    residual: Vec<(DagId, u32)>,
    mode: Mode,
    /// Whether the sole repeated-variable extension fast path is eligible, and whether its one
    /// deterministic attempt has already been made.
    special_nonlinear: bool,
    special_attempted: bool,
    /// Variable indices bound by the most recent solution (unbound at the next `next`).
    bound: Vec<u32>,
    residue: Vec<(DagId, u32)>,
    matched_whole: bool,
}

impl AcuMatcher {
    /// Build the enumerator from the residual multiset (`elements` + `mult`, aligned), the top
    /// variables, and the match flags. Pure integer setup (no `Runtime`): the Diophantine system is
    /// constructed here; solving + node building happen lazily in [`next`](Self::next).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        symbol: SymbolId,
        identity: Option<IdentityId>,
        elements: Vec<DagId>,
        mult: Vec<u32>,
        vars: Vec<MatcherVar>,
        ext_allowed: bool,
        has_grounds: bool,
        subject_is_identity: bool,
        special_nonlinear: bool,
    ) -> Self {
        debug_assert_eq!(elements.len(), mult.len());
        // The residual multiset: elements with positive multiplicity (the Diophantine columns).
        let residual: Vec<(DagId, u32)> = elements
            .iter()
            .zip(&mult)
            .filter(|&(_, &m)| m > 0)
            .map(|(&e, &m)| (e, m))
            .collect();
        let columns: Vec<(usize, u32)> = mult
            .iter()
            .enumerate()
            .filter(|&(_, &m)| m > 0)
            .map(|(i, &m)| (i, m))
            .collect();

        // A lone count-one collector absorbs the whole remainder in one matched-whole solution.
        // Suppressing the extension row enforces this. With an identity, the variable may instead
        // bind identity first and leave the remainder as residue, so this fast path is disabled.
        let lone_linear =
            vars.len() == 1 && vars[0].coeff == 1 && !(ext_allowed && identity.is_some());
        let ext_allowed = ext_allowed && !lone_linear;

        let mode = if vars.is_empty() {
            Mode::NoVar { done: false }
        } else if columns.is_empty() {
            // Empty residual multiset: bind every variable to identity iff all are identity-capable.
            if vars.iter().all(|v| v.lower_bound == 0) {
                Mode::Trivial { done: false }
            } else {
                Mode::Done
            }
        } else {
            let nr_vars = vars.len();
            let mut sys = DiophantineSystem::new(nr_vars + usize::from(ext_allowed), columns.len());
            for v in &vars {
                sys.insert_row(v.coeff as i32, v.lower_bound, v.upper_bound);
            }
            // Insert the unbounded residue row after all variable rows.
            if ext_allowed {
                sys.insert_row(1, 0, UNBOUNDED);
            }
            let mut subject_map = Vec::with_capacity(columns.len());
            for &(elem_idx, m) in &columns {
                subject_map.push(elem_idx);
                sys.insert_column(m as i32);
            }
            let ext_row = ext_allowed.then_some(nr_vars);
            Mode::System {
                sys,
                subject_map,
                ext_row,
            }
        };

        AcuMatcher {
            symbol,
            identity,
            ext_allowed,
            has_grounds,
            subject_is_identity,
            vars,
            elements,
            residual,
            mode,
            special_nonlinear: special_nonlinear && ext_allowed,
            special_attempted: false,
            bound: Vec::new(),
            residue: Vec::new(),
            matched_whole: true,
        }
    }

    pub(crate) fn residue(&self) -> &[(DagId, u32)] {
        &self.residue
    }

    pub(crate) fn matched_whole(&self) -> bool {
        self.matched_whole
    }

    /// Advance to the next solution, binding its variables into `subst` and recording its residue;
    /// `false` when exhausted. Undoes the previous solution's bindings first. A candidate whose binding
    /// violates a variable's sort, is inconsistent with an outer (non-linear) binding, or is the
    /// degenerate empty match is skipped.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();

        // A sole repeated variable with no other pattern arguments has one maximal quotient match:
        // `X*X` over `a*a*b*b` binds `X := a*b`. An existing outer binding uses the general matcher.
        if self.special_nonlinear && !self.special_attempted {
            self.special_attempted = true;
            let index = self.vars[0].index;
            if subst.get(index).is_none() && self.finish_nonlinear(rt, sig, subst) {
                self.mode = Mode::Done;
                return true;
            }
        }

        match &mut self.mode {
            Mode::Done => false,
            Mode::NoVar { done } => {
                if *done {
                    return false;
                }
                *done = true;
                self.finish_no_var()
            }
            Mode::Trivial { done } => {
                if *done {
                    return false;
                }
                *done = true;
                self.finish_trivial(rt, sig, subst)
            }
            Mode::System { .. } => self.next_system(rt, sig, subst),
        }
    }

    /// Match a sole variable of coefficient `m >= 2` against assignable subject entries with
    /// multiplicity at least `m`. An element-sort variable takes the first such entry; a collector
    /// takes every assignable entry, dividing each multiplicity by `m` and leaving the remainders in
    /// the extension.
    fn finish_nonlinear(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        let variable = self.vars[0].clone();
        debug_assert!(variable.coeff >= 2);
        let unit_sort = variable.upper_bound == 1;
        let assignable = |rt: &Runtime, dag: DagId| sig.sorts().leq(rt.sort_of(dag), variable.sort);

        let mut binding_parts = Vec::new();
        let mut residue = Vec::new();
        if unit_sort {
            let Some(chosen) = self.residual.iter().position(|&(dag, multiplicity)| {
                multiplicity >= variable.coeff && assignable(rt, dag)
            }) else {
                return false;
            };
            let (binding, _) = self.residual[chosen];
            let source = &self.residual;
            binding_parts.push((binding, 1));
            for (index, &(dag, multiplicity)) in source.iter().enumerate() {
                let remaining = if index == chosen {
                    multiplicity - variable.coeff
                } else {
                    multiplicity
                };
                if remaining != 0 {
                    residue.push((dag, remaining));
                }
            }
        } else {
            for &(dag, multiplicity) in &self.residual {
                if multiplicity >= variable.coeff && assignable(rt, dag) {
                    binding_parts.push((dag, multiplicity / variable.coeff));
                    let remaining = multiplicity % variable.coeff;
                    if remaining != 0 {
                        residue.push((dag, remaining));
                    }
                } else {
                    residue.push((dag, multiplicity));
                }
            }
            if binding_parts.is_empty() {
                return false;
            }
        }

        let binding = if binding_parts.len() == 1 && binding_parts[0].1 == 1 {
            binding_parts[0].0
        } else {
            rt.make_acu(sig, self.symbol, binding_parts)
        };
        if !sig.sorts().leq(rt.sort_of(binding), variable.sort)
            || !self.apply_binds(rt, &[(variable.index, binding)], subst)
        {
            return false;
        }
        self.matched_whole = residue.is_empty();
        self.residue = residue;
        true
    }

    /// Finish a match with no unbound variables. The residual multiset becomes the extension;
    /// without extension a non-empty residue fails, and a degenerate empty no-op with neither
    /// grounds nor an identity subject is omitted.
    fn finish_no_var(&mut self) -> bool {
        let total: u32 = self.residual.iter().map(|&(_, m)| m).sum();
        if total == 0 {
            // Everything was consumed by grounds (or the subject was empty): a whole match.
            self.matched_whole = true;
            self.residue.clear();
            return true;
        }
        if !self.ext_allowed {
            return false; // leftover with no extension
        }
        // Extension with a non-empty residue. Skip the degenerate "match nothing, leave everything"
        // unless grounds matched something or the subject is the identity.
        if !self.has_grounds && !self.subject_is_identity {
            return false;
        }
        self.residue = self.residual.clone();
        self.matched_whole = false;
        true
    }

    /// The empty-multiset trivial system: bind every variable to the identity, once.
    fn finish_trivial(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        let id_sym = self
            .identity
            .expect("identity-capable vars require an identity element");
        let id_dag = rt.identity_dag(sig, id_sym);
        let mut binds: Vec<(u32, DagId)> = Vec::with_capacity(self.vars.len());
        for v in &self.vars {
            // The identity's sort must satisfy the variable's declared sort (it does: lower_bound == 0
            // means identity <= sort), but keep the check for robustness.
            if !sig.sorts().leq(rt.sort_of(id_dag), v.sort) {
                return false;
            }
            binds.push((v.index, id_dag));
        }
        if !self.apply_binds(rt, &binds, subst) {
            return false;
        }
        self.residue.clear();
        self.matched_whole = true;
        true
    }

    /// Drive the Diophantine system lazily: get the next raw solution, build + validate the variable
    /// bindings and residue, and skip (loop to the next solution) any candidate rejected by a sort
    /// check, an outer-binding inconsistency, or the empty-match gating.
    fn next_system(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        loop {
            let (sys, subject_map, ext_row) = match &mut self.mode {
                Mode::System {
                    sys,
                    subject_map,
                    ext_row,
                } => (sys, &*subject_map, *ext_row),
                _ => unreachable!("next_system on non-System mode"),
            };
            if !sys.solve() {
                self.mode = Mode::Done;
                return false;
            }
            // Build each variable's binding from its Diophantine row.
            let mut binds: Vec<(u32, DagId)> = Vec::with_capacity(self.vars.len());
            let mut matched: u32 = 0;
            let mut ok = true;
            for (k, v) in self.vars.iter().enumerate() {
                let pairs: Vec<(DagId, u32)> = subject_map
                    .iter()
                    .enumerate()
                    .filter_map(|(col, &elem_idx)| {
                        let m = sys.solution(k, col);
                        (m > 0).then(|| (self.elements[elem_idx], m as u32))
                    })
                    .collect();
                let size: u32 = pairs.iter().map(|&(_, m)| m).sum();
                matched += v.coeff * size;
                let binding = if pairs.is_empty() {
                    match self.identity {
                        Some(id_sym) => rt.identity_dag(sig, id_sym),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                } else {
                    rt.make_acu(sig, self.symbol, pairs)
                };
                if !sig.sorts().leq(rt.sort_of(binding), v.sort) {
                    ok = false;
                    break;
                }
                binds.push((v.index, binding));
            }
            if !ok {
                continue; // sort violation (or an identity-free variable forced empty): next solution
            }
            // The degenerate empty match (nothing matched by variables, no grounds, subject not the
            // identity) is a no-op rather than a rewrite.
            if matched == 0 && !self.has_grounds && !self.subject_is_identity {
                continue;
            }
            // Residue from the extension row.
            let mut residue: Vec<(DagId, u32)> = Vec::new();
            if let Some(er) = ext_row {
                for (col, &elem_idx) in subject_map.iter().enumerate() {
                    let m = sys.solution(er, col);
                    if m > 0 {
                        residue.push((self.elements[elem_idx], m as u32));
                    }
                }
            }
            // Consistency with outer / non-linear bindings, then apply.
            if !self.apply_binds(rt, &binds, subst) {
                continue;
            }
            self.matched_whole = residue.is_empty();
            self.residue = residue;
            return true;
        }
    }

    /// Bind each `(index, value)` into `subst`, honouring any variable **already bound** by an outer
    /// subterm (a non-linear occurrence): the enumerated value must be deep-equal to the existing one,
    /// else this candidate is rejected (any freshly-applied binds are rolled back). Records the newly
    /// bound indices in `self.bound` for the next `next` to undo.
    fn apply_binds(&mut self, rt: &Runtime, binds: &[(u32, DagId)], subst: &mut Subst) -> bool {
        for &(idx, b) in binds {
            match subst.get(idx) {
                Some(existing) => {
                    if !rt.deep_equal(existing, b) {
                        for &done in &self.bound {
                            subst.unbind(done);
                        }
                        self.bound.clear();
                        return false;
                    }
                }
                None => {
                    subst.bind(idx, b);
                    self.bound.push(idx);
                }
            }
        }
        true
    }
}
