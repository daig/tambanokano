//! Lazy ACU solution enumerator for the **no-alien** case, driven by the [`DiophantineSystem`].
//!
//! This is the Phase-2 port of Maude's `ACU_Subproblem` restricted to the (very common) case where
//! the pattern's non-ground subterms are all **top variables** (no non-ground *aliens*). In that case
//! the whole bipartite-graph layer collapses away and matching is a pure Diophantine problem: one row
//! per top variable (coefficient = its multiplicity, size bounds from its sort's identity-capability
//! and `sortBound`), one column per residual subject element, plus one **extension** row when matching
//! with a residue. The solver enumerates solutions **lazily and in Maude's order** (minimal variable
//! size first) — so a pattern like SET's `(E, S)` over a 30-element set yields its first solution
//! immediately instead of the naive matcher's `2^30` eager materialisation (the D2a hang).
//!
//! Element variables (`upperBound == 1`, e.g. SET's `E : X$Elt`) are *not* special-cased into
//! bipartite pattern nodes as Maude does; a Diophantine row with `maxSize == 1` produces the identical
//! accepted-solution order (rows sort *ascending by maxSize*, so element variables enumerate outer,
//! collectors inner — exactly Maude's patterns-outer/Diophantine-inner order) with no extra cost.
//!
//! The special cases (`noVariableCase`, the empty-multiset "trivial system", the identity-first
//! collapse gating) are ported faithfully; extension uses the **unbounded** residue model of the
//! existing matcher (oracle-verified: `a + b + d` under `eq a + X = c` leaves the two-element residue
//! `b + d`), with the degenerate all-identity/all-extension no-op skipped unless the subject *is* the
//! identity or the pattern has ground subterms (the B1 gating).

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
    /// No unbound top variables (Maude's `noVariableCase`): a single potential solution — the whole
    /// residual multiset is the residue (extension), or a whole match if it is empty.
    NoVar { done: bool },
    /// Non-empty variable set but empty residual multiset (Maude's "no subjects" trivial system): bind
    /// every variable to the identity (one solution) iff every variable is identity-capable (already
    /// checked at construction, else [`Mode::Done`]).
    Trivial { done: bool },
    /// The general Diophantine system. `subject_map[col]` is the element index of column `col`;
    /// `ext_row` is the extension row's original index (`= nr_vars`) when matching with a residue.
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
    /// The residual subject elements (post-grounds), aligned with the Diophantine columns' source.
    elements: Vec<DagId>,
    /// The residual subject multiset as `(element, multiplicity)` pairs (post-grounds, nonzero) — the
    /// residue for the [`Mode::NoVar`] case and the source of the Diophantine columns.
    residual: Vec<(DagId, u32)>,
    mode: Mode,
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

        // The **lone-variable collector** (Maude's LONE_VARIABLE / `forcedLoneVariableCase`): a single
        // count-1 top variable absorbs the *whole* remainder as one matched-whole solution — a
        // correctness rule, not just ordering (`eq a + X = b` on `a + c + c` gives `b`, not `b + c`).
        // This is achieved by suppressing the extension row (so the sole Diophantine row takes
        // everything). It is gated OFF when the operator has an identity: then the variable may take
        // the identity, and Maude enumerates the empty assignment first with the rest as extension
        // residue (`eq a + X = c [id: e]` on `a + b` gives `b + c`, X := e). This mirrors the naive
        // matcher's `lone_linear` condition exactly (the B1 identity-first gating).
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
            // Extension row (original index `nr_vars`, inserted last), unbounded residue model.
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

    /// `noVariableCase`: 0 unbound variables. The residue is the whole residual multiset (extension);
    /// without extension a non-empty residue is a failure, and the degenerate empty no-op (no grounds,
    /// non-identity subject) is not offered.
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
        // unless grounds matched something or the subject is the identity (the B1 gating).
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
            // identity) is the no-op — not a real rewrite (the B1 identity-first gating).
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
