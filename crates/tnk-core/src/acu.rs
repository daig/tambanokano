//! ACU matching: a complete, multi-solution matcher for `assoc comm [id:]` operators.
//!
//! The pattern and subject are both *multisets* over the AC operator. Matching is genuinely
//! multi-solution (e.g. `X + Y <=? a + b + c` has 6 solutions), so the [`AcuSubproblem`] is a
//! resumable enumerator driven through the [`crate::theory`] seam's `next()` stream.
//!
//! **Strategy (correctness-first).** We enumerate *every* solution by a direct backtracking
//! distribution of the subject multiset among the pattern variables — not Maude's optimized
//! bipartite + Diophantine solver (a later perf step). Two ordering rules make this reproduce the
//! reference binary's *rewrite counts*, which depend on solution order even for confluent systems
//! (verified empirically: `eq X+X=X` on `a+a+a+a` is 3 rewrites, not 1):
//! - solutions are yielded **minimal-matched-size first**, so a repeated/over-large variable binds
//!   the *smallest* multiset that works (Maude binds `X` to a single `a`, not to `a+a`);
//! - the degenerate **matched-size-0** solution (every variable bound to the identity, no ground
//!   part) is skipped — it is the identity no-op that would rewrite a term to itself.
//!
//! Scope (this slice): ground subterms + variables (linear and non-linear) under the AC operator,
//! with two-sided identity. **Alien** (non-ground, non-variable) subterms under the AC operator, the
//! red-black tree representation, and lazy subproblems are follow-ups.

use crate::acu_matcher::{AcuMatcher, MatcherVar};
use crate::dag::{DagId, NodeTerm};
use crate::diophantine::UNBOUNDED;
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::{IdentityId, SymbolId};
use crate::term::{Subst, Term};
use crate::theory::LhsAutomaton;
use std::collections::HashSet;

/// A compiled ACU left-hand side: the flattened pattern multiset partitioned into ground subterms
/// (each consumes one structurally-equal subject element), **aliens** (non-ground non-variable
/// subterms, each matched recursively by its own automaton — Maude's `NonGroundAlien`), and distinct
/// variables.
#[derive(Clone)]
pub(crate) struct AcuLhs {
    symbol: SymbolId,
    /// Ground, free-matchable sub-patterns; each must match one structurally-equal subject element
    /// (the deterministic fast path — no sub-automaton needed).
    grounds: Vec<Term>,
    /// Alien sub-patterns: a non-ground subterm (e.g. `s M` under `+`) or a theory-rooted subterm,
    /// each compiled to its own [`LhsAutomaton`] and matched recursively against a subject element
    /// (Maude's `ACU_LhsAutomaton::NonGroundAlien`). Structurally-equal aliens are merged with a
    /// summed multiplicity, mirroring the canonical pattern multiset (`s M + s M` ⇒ one alien × 2).
    aliens: Vec<AcuAlien>,
    /// Distinct variable occurrences under the operator (a repeated index is non-linear).
    vars: Vec<AcuVar>,
    identity: Option<IdentityId>,
    /// `true` when this pattern is Maude's top-level repeated-variable special case
    /// (`X + ... + X`, no grounds/aliens, no identity or condition-variable conflict).
    special_nonlinear: bool,
}

#[derive(Clone)]
struct AcuAlien {
    /// The alien sub-pattern, kept as a [`Term`] (re-compiled to an automaton during enumeration —
    /// alien patterns are small and rare, so this stays correctness-first over caching the automaton).
    term: Term,
    /// Copies of this exact sub-pattern in the canonical pattern multiset (it must consume that many
    /// copies of whatever subject element it matches).
    multiplicity: u32,
}

#[derive(Clone)]
struct AcuVar {
    index: u32,
    /// How many times this variable index occurs in the pattern (the Diophantine coefficient).
    count: u32,
    sort: SortId,
    /// Diophantine **lower bound** on the binding size: `0` if the variable can take the identity
    /// (Maude's `takeIdentity`), else `1`. Computed at compile from the operator + variable sort.
    lower_bound: i32,
    /// Diophantine **upper bound** on the binding size (Maude's `sortBound`): `1` for an element sort,
    /// [`UNBOUNDED`] for a collector. Distinguishes stripper rows from collector rows.
    upper_bound: i32,
}

/// Structural equality on patterns (same operator + recursively-equal args, or the same variable
/// index) — the key that merges repeated aliens into one with a summed multiplicity, exactly as the
/// canonical pattern multiset would. Author-shallow recursion (alien patterns are small).
fn term_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Var(x), Term::Var(y)) => x.index == y.index,
        (
            Term::Op {
                symbol: sa,
                args: aa,
            },
            Term::Op {
                symbol: sb,
                args: ab,
            },
        ) => sa == sb && aa.len() == ab.len() && aa.iter().zip(ab).all(|(x, y)| term_eq(x, y)),
        (
            Term::Iter {
                symbol: sa,
                count: ca,
                arg: aa,
            },
            Term::Iter {
                symbol: sb,
                count: cb,
                arg: ab,
            },
        ) => sa == sb && ca == cb && term_eq(aa, ab),
        _ => false,
    }
}

impl AcuLhs {
    /// Compile an ACU pattern, suppressing the repeated-variable fast path when its variable occurs
    /// in the enclosing statement's condition. Maude then needs the general solution stream so a
    /// failed condition can backtrack.
    pub(crate) fn compile_avoiding_nonlinear_vars(
        lhs: Term,
        sig: &Signature,
        condition_variables: &HashSet<u32>,
    ) -> Self {
        let symbol = lhs.top_symbol().expect("ACU lhs must be an application");
        let identity = sig.symbol(symbol).identity();
        // Per-sort bounds for this operator's kind (Maude's `sortBound`), computed once: each top
        // variable's Diophantine row `maxSize` (element vs collector) — see [`AcuVar`].
        let sort_bounds = sig.acu_sort_bounds(symbol);
        let mut grounds: Vec<Term> = Vec::new();
        let mut aliens: Vec<AcuAlien> = Vec::new();
        let mut vars: Vec<AcuVar> = Vec::new();

        let mut stack = vec![lhs];
        while let Some(t) = stack.pop() {
            match t {
                Term::Op { symbol: s, args } if s == symbol => {
                    // `stack` is LIFO, so push arguments right-to-left. Maude records top
                    // variables in left-to-right pattern order, and equal Diophantine rows retain
                    // that order; it therefore determines which variable receives the first
                    // canonical subject element during solution enumeration.
                    stack.extend(args.into_iter().rev());
                }
                Term::Var(v) => match vars.iter_mut().find(|av| av.index == v.index) {
                    Some(av) => av.count += 1,
                    None => {
                        let lower_bound = if sig.acu_take_identity(symbol, v.sort) {
                            0
                        } else {
                            1
                        };
                        let upper_bound = sort_bounds.get(&v.sort).copied().unwrap_or(UNBOUNDED);
                        vars.push(AcuVar {
                            index: v.index,
                            count: 1,
                            sort: v.sort,
                            lower_bound,
                            upper_bound,
                        });
                    }
                },
                // A built-in literal is a ground, free-matchable leaf — same fast path as a ground Op.
                t @ Term::Na { .. } => grounds.push(t),
                // A ground, free-matchable subterm consumes one structurally-equal subject element
                // deterministically (the fast path). Everything else — a non-ground subterm (`s M`) or
                // a theory-rooted one — is an **alien**, matched recursively by its own automaton; merge
                // structurally-equal aliens, as the canonical pattern multiset does.
                t @ Term::Op { .. } if t.is_ground() && t.is_free_matchable(sig) => grounds.push(t),
                alien @ Term::Op { .. } => {
                    match aliens.iter_mut().find(|a| term_eq(&a.term, &alien)) {
                        Some(a) => a.multiplicity += 1,
                        None => aliens.push(AcuAlien {
                            term: alien,
                            multiplicity: 1,
                        }),
                    }
                }
                alien @ Term::Iter { .. } => {
                    match aliens.iter_mut().find(|a| term_eq(&a.term, &alien)) {
                        Some(a) => a.multiplicity += 1,
                        None => aliens.push(AcuAlien {
                            term: alien,
                            multiplicity: 1,
                        }),
                    }
                }
            }
        }
        let special_nonlinear = grounds.is_empty()
            && aliens.is_empty()
            && vars.len() == 1
            && vars[0].count >= 2
            && vars[0].lower_bound == 1
            && !condition_variables.contains(&vars[0].index)
            && sig.acu_nonlinear_sort_safe(symbol, vars[0].sort);
        AcuLhs {
            symbol,
            grounds,
            aliens,
            vars,
            identity,
            special_nonlinear,
        }
    }

    /// First match phase: the subject must be an ACU node of this operator; its ground sub-patterns
    /// are matched deterministically against (and consume) equal subject elements; the remaining
    /// multiset and the variables become an [`AcuSubproblem`] enumerating the distributions. Returns
    /// `None` if the subject is not an ACU node of this symbol or a ground subterm is absent.
    ///
    /// `ext_allowed` enables *extension* (matching a sub-multiset, leaving a residue) — `true` for
    /// AC rewriting at the top and for `xmatch`; `false` for a plain `match` (the whole subject must
    /// be consumed). Reads only the runtime (no allocation), so it takes `&Runtime`.
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        ext_allowed: bool,
    ) -> Option<AcuSubproblem> {
        // **Collapse matching** (mirrors `au`): a subject not rooted at this operator is a one-element
        // multiset — or the empty multiset if it is the operator's identity. So an ACU pattern `(E, S)`
        // (e.g. SET's `_,_ [assoc comm id: empty]`) matches a singleton set `c` as `E = c, S = empty`,
        // which arises whenever the pattern is an *argument* (`$intersect((E, S), …)` on a singleton),
        // not only at the top. A collapsed subject is the whole multiset, so extension is off for it.
        let mut subject_is_identity = false;
        let (mut multiset, ext): (Vec<(DagId, u32)>, bool) = match &rt.node(subject).term {
            NodeTerm::Acu { symbol, args } if *symbol == self.symbol => (args.clone(), ext_allowed),
            _ if self
                .identity
                .is_some_and(|id| rt.is_identity(sig, id, subject)) =>
            {
                subject_is_identity = true;
                (Vec::new(), false)
            }
            _ => (vec![(subject, 1)], false),
        };

        // Consume each ground subterm against a structurally-equal element (deterministic).
        let mut throwaway = Subst::new();
        throwaway.reset(0);
        for g in &self.grounds {
            let pos = multiset
                .iter()
                .position(|&(e, _)| rt.match_pattern(sig, g, e, &mut throwaway))?;
            multiset[pos].1 -= 1;
            if multiset[pos].1 == 0 {
                multiset.remove(pos);
            }
        }

        // Symbolic instantiation copies bindings up to eager, so a retained ACU DAG can contain
        // distinct entries that are structurally equal. Maude's AC matcher treats those entries as
        // one multiset element; coalesce the residual here (without rewriting the retained DAG) before
        // constructing the Diophantine columns. Keeping the first occurrence preserves enumeration
        // order while making a nonlinear pattern such as `X * X` match two copied equal arguments.
        let mut merged = Vec::with_capacity(multiset.len());
        for (element, multiplicity) in multiset {
            if let Some((_, count)) = merged
                .iter_mut()
                .find(|(retained, _)| rt.deep_equal(*retained, element))
            {
                *count += multiplicity;
            } else {
                merged.push((element, multiplicity));
            }
        }
        let multiset = merged;

        let var_coeffs: Vec<u32> = self.vars.iter().map(|v| v.count).collect();
        // No aliens: the whole match is a pure Diophantine distribution of the residual multiset among
        // the top variables (+ an extension row). The [`AcuMatcher`] enumerates it **lazily** in
        // Maude's order — the D2a fix (the naive path materialised every distribution eagerly). With
        // aliens present we defer to the alien path in `next` instead (matching an alien builds binding
        // nodes, so it needs `&mut Runtime` the immutable first phase does not have).
        let matcher = if self.aliens.is_empty() {
            let elements: Vec<DagId> = multiset.iter().map(|&(e, _)| e).collect();
            let mult: Vec<u32> = multiset.iter().map(|&(_, m)| m).collect();
            let mvars: Vec<MatcherVar> = self
                .vars
                .iter()
                .map(|v| MatcherVar {
                    index: v.index,
                    coeff: v.count,
                    lower_bound: v.lower_bound,
                    upper_bound: v.upper_bound,
                    sort: v.sort,
                })
                .collect();
            Some(AcuMatcher::new(
                self.symbol,
                self.identity,
                elements,
                mult,
                mvars,
                ext,
                !self.grounds.is_empty(),
                subject_is_identity,
                self.special_nonlinear,
            ))
        } else {
            None
        };
        let mut alien_var_indices: Vec<u32> = Vec::new();
        for a in &self.aliens {
            collect_vars(&a.term, &mut alien_var_indices);
        }

        Some(AcuSubproblem {
            symbol: self.symbol,
            identity: self.identity,
            ext_allowed: ext,
            matcher,
            var_indices: self.vars.iter().map(|v| v.index).collect(),
            var_sorts: self.vars.iter().map(|v| v.sort).collect(),
            var_coeffs,
            aliens: self.aliens.clone(),
            multiset,
            alien_var_indices,
            recorded: None,
            rec_cursor: 0,
            bound: Vec::new(),
            residue: Vec::new(),
            matched_whole: true,
        })
    }
}

/// Collect the distinct variable indices occurring in a pattern (used to capture an alien's internal
/// bindings into a recorded solution).
fn collect_vars(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => args.iter().for_each(|a| collect_vars(a, out)),
        Term::Iter { arg, .. } => collect_vars(arg, out),
    }
}

/// One way of distributing the remaining subject multiset: for each (distinct) element, how many
/// copies go to each variable (per occurrence) and how many to the residue.
struct Candidate {
    /// `to_var[element][var]` — per-occurrence count of `element` in that variable's binding.
    to_var: Vec<Vec<u32>>,
    /// `residue[element]` — copies left unmatched (the extension).
    residue: Vec<u32>,
    /// Total matched size contributed by variables (for minimal-first ordering).
    matched: u32,
}

/// Enumerate every distribution of the element multiset `mults` among `coeffs.len()` variables
/// (variable `k` consuming `coeffs[k]` copies per unit it binds), with an optional residue. The
/// per-element sub-problems are independent (the multiset equation decomposes by element), so we take
/// the Cartesian product of per-element compositions and filter by the global constraints:
/// every variable non-empty unless an identity exists, and the matched portion non-empty (skip the
/// identity no-op). Results are ordered **minimal-matched-first**.
#[allow(clippy::too_many_arguments)]
fn enumerate_distributions(
    mults: &[u32],
    coeffs: &[u32],
    ext_allowed: bool,
    identity: bool,
    has_grounds: bool,
    lone_linear: bool,
    subject_is_identity: bool,
) -> Vec<Candidate> {
    let r = coeffs.len();
    // Collector strategy: the one linear variable takes the whole remainder (matched whole).
    if lone_linear {
        let to_var: Vec<Vec<u32>> = mults.iter().map(|&m| vec![m]).collect();
        return vec![Candidate {
            residue: vec![0; mults.len()],
            matched: mults.iter().sum(),
            to_var,
        }];
    }
    let per_element: Vec<Vec<Split>> = mults
        .iter()
        .map(|&m| compositions(m, coeffs, ext_allowed))
        .collect();
    // An element with no valid composition makes the whole match impossible.
    if per_element.iter().any(|s| s.is_empty()) {
        return Vec::new();
    }

    let radices: Vec<usize> = per_element.iter().map(Vec::len).collect();
    let mut idx = vec![0usize; per_element.len()];
    let mut out: Vec<Candidate> = Vec::new();
    loop {
        let chosen: Vec<&Split> = idx
            .iter()
            .enumerate()
            .map(|(i, &j)| &per_element[i][j])
            .collect();
        let mut var_total = vec![0u32; r];
        for s in &chosen {
            for (vt, &c) in var_total.iter_mut().zip(&s.to_var) {
                *vt += c;
            }
        }
        let all_vars_filled = identity || var_total.iter().all(|&t| t > 0);
        let matched: u32 = coeffs.iter().zip(&var_total).map(|(&c, &t)| c * t).sum();
        // The all-identity assignment (matched == 0, nothing consumed) is a real Maude match
        // ONLY when the subject IS the identity element (`eq (S ; S) = S` fires once on `e`);
        // on any other subject an empty match is not offered (oracle: `red a` under that eq is
        // 0 rewrites). With grounds present, a zero VARIABLE contribution still consumed the
        // grounds, which is a genuine match (`eq a + X = c` on `a`, X := e).
        if all_vars_filled && (has_grounds || matched > 0 || subject_is_identity) {
            out.push(Candidate {
                to_var: chosen.iter().map(|s| s.to_var.clone()).collect(),
                residue: chosen.iter().map(|s| s.residue).collect(),
                matched,
            });
        }
        if !increment_mixed_radix(&mut idx, &radices) {
            break;
        }
    }
    out.sort_by_key(|c| c.matched); // minimal matched size first (stable within a size)
    out
}

/// One element's contribution: `to_var[k]` copies to variable `k` (per occurrence) and `residue`
/// copies unmatched, with `Σ coeffs[k]·to_var[k] + residue = m`.
struct Split {
    to_var: Vec<u32>,
    residue: u32,
}

/// All `(to_var, residue)` with `Σ coeffs[k]·to_var[k] + residue = m` (residue forced to 0 unless
/// `allow_residue`). Each `coeffs[k] ≥ 1`.
fn compositions(m: u32, coeffs: &[u32], allow_residue: bool) -> Vec<Split> {
    let mut out = Vec::new();
    let mut cur = vec![0u32; coeffs.len()];
    compose(0, m, coeffs, &mut cur, allow_residue, &mut out);
    out
}

fn compose(
    k: usize,
    remaining: u32,
    coeffs: &[u32],
    cur: &mut Vec<u32>,
    residue: bool,
    out: &mut Vec<Split>,
) {
    if k == coeffs.len() {
        if residue || remaining == 0 {
            out.push(Split {
                to_var: cur.clone(),
                residue: remaining,
            });
        }
        return;
    }
    for t in 0..=(remaining / coeffs[k]) {
        cur[k] = t;
        compose(k + 1, remaining - coeffs[k] * t, coeffs, cur, residue, out);
    }
    cur[k] = 0;
}

/// Remove a bound top variable's contribution from the available multiset (alien path, non-linear
/// across levels): flatten `binding` into element-multiplicities under `symbol` (an ACU node spreads
/// into its args; anything else is a single element), then take `coeff` copies of each — `false` if
/// any is short, meaning this branch has no solution.
fn subtract_binding(
    avail: &mut Vec<(DagId, u32)>,
    rt: &Runtime,
    sig: &Signature,
    binding: DagId,
    coeff: u32,
    symbol: SymbolId,
    identity: Option<IdentityId>,
) -> bool {
    // A prebound variable at the ACU identity contributes the empty multiset. Treating the
    // canonical identity DAG as an ordinary alien element makes a shared match spuriously fail:
    // there is (correctly) no explicit identity element in the normalized subject multiset.
    if identity.is_some_and(|id| rt.is_identity(sig, id, binding)) {
        return true;
    }
    let elems: Vec<(DagId, u32)> = match &rt.node(binding).term {
        NodeTerm::Acu { symbol: s, args } if *s == symbol => args.clone(),
        _ => vec![(binding, 1)],
    };
    for (e, m) in elems {
        let need = m * coeff;
        match avail.iter().position(|&(a, _)| rt.deep_equal(a, e)) {
            Some(p) if avail[p].1 >= need => {
                avail[p].1 -= need;
                if avail[p].1 == 0 {
                    avail.remove(p);
                }
            }
            _ => return false,
        }
    }
    true
}

/// Advance a mixed-radix counter; `false` when it wraps (enumeration complete). An empty counter
/// (no elements) yields exactly one iteration then wraps.
fn increment_mixed_radix(idx: &mut [usize], radices: &[usize]) -> bool {
    for i in (0..idx.len()).rev() {
        idx[i] += 1;
        if idx[i] < radices[i] {
            return true;
        }
        idx[i] = 0;
    }
    false
}

/// A resumable enumerator over the solutions of an [`AcuLhs`] against a subject (decision D3: an arm
/// of the closed [`crate::theory::Subproblem`] enum). Each `next()` undoes the previous solution's
/// bindings, then binds the next candidate's variables (building their multiset bindings as fresh
/// canonical ACU nodes) and records the residue (the extension). Owns all its state — no borrows of
/// the engine — so it survives across the `&mut Runtime` calls the driver makes between solutions.
pub(crate) struct AcuSubproblem {
    symbol: SymbolId,
    identity: Option<IdentityId>,
    ext_allowed: bool,
    var_indices: Vec<u32>,
    var_sorts: Vec<SortId>,
    var_coeffs: Vec<u32>,
    // ---- no-alien path: the lazy Diophantine enumerator (`None` ⇒ the alien path below) ----
    matcher: Option<AcuMatcher>,
    // ---- alien path (when `aliens` is non-empty): lazily enumerated on the first `next` ----
    /// Alien sub-patterns to match recursively (empty ⇒ the no-alien fast path above).
    aliens: Vec<AcuAlien>,
    /// The post-grounds subject multiset the aliens + variables distribute over.
    multiset: Vec<(DagId, u32)>,
    /// Variable indices the aliens may bind (captured into each recorded solution).
    alien_var_indices: Vec<u32>,
    /// Fully-built solutions (alien bindings + variable distribution), greedy-first; `None` until the
    /// first `next` enumerates them (needs `&mut Runtime` to drive the alien sub-automata).
    recorded: Option<Vec<RecordedSolution>>,
    rec_cursor: usize,
    // ---- shared replay state ----
    /// Variable indices bound by the most recent solution (unbound before the next one).
    bound: Vec<u32>,
    residue: Vec<(DagId, u32)>,
    matched_whole: bool,
}

/// One fully-built alien-path solution: every pattern variable's binding (alien-internal + top
/// variables) and the residue (extension). Built eagerly during enumeration (the alien sub-matches
/// already allocate binding nodes), then replayed by `next`.
struct RecordedSolution {
    binds: Vec<(u32, DagId)>,
    residue: Vec<(DagId, u32)>,
}


impl AcuSubproblem {
    /// Advance to the next solution, binding its variables into `subst` and recording its residue;
    /// `false` when exhausted. Builds binding nodes (so it needs `&mut Runtime`); a candidate whose
    /// binding violates a variable's sort is skipped. Dispatches to the alien path when the pattern has
    /// alien subterms, else the proven no-alien variable-distribution path.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        if !self.aliens.is_empty() {
            for &idx in &self.bound {
                subst.unbind(idx);
            }
            self.bound.clear();
            return self.next_alien(rt, sig, subst);
        }

        // No-alien path: the lazy Diophantine enumerator owns its own bind/unbind lifecycle.
        let matcher = self
            .matcher
            .as_mut()
            .expect("no-alien subproblem has a matcher");
        if matcher.next(rt, sig, subst) {
            self.residue = matcher.residue().to_vec();
            self.matched_whole = matcher.matched_whole();
            true
        } else {
            false
        }
    }

    /// The alien-path counterpart of the candidate loop: on the first call, fully enumerate the
    /// solutions (driving each alien's sub-automaton — needs `&mut Runtime`) greedy-first, then replay
    /// them one per `next`. The bindings are already built during enumeration, so replay just binds.
    fn next_alien(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        if self.recorded.is_none() {
            let sols = self.enumerate_aliens(rt, sig, subst);
            self.recorded = Some(sols);
        }
        let (binds, residue) = {
            let recorded = self.recorded.as_ref().expect("just enumerated");
            if self.rec_cursor >= recorded.len() {
                return false;
            }
            let sol = &recorded[self.rec_cursor];
            (sol.binds.clone(), sol.residue.clone())
        };
        self.rec_cursor += 1;
        for &(idx, b) in &binds {
            match subst.get(idx) {
                Some(existing) if !rt.deep_equal(existing, b) => return false,
                Some(_) => {}
                None => {
                    subst.bind(idx, b);
                    self.bound.push(idx);
                }
            }
        }
        self.matched_whole = residue.is_empty();
        self.residue = residue;
        true
    }

    /// Enumerate every solution of the alien + variable parts against the post-grounds multiset,
    /// **greedy-first** (Maude's `ACU_GreedyMatcher` order): each alien is tried against the subject
    /// elements in canonical order, taking the first match before the next. `base` seeds the scratch
    /// substitution so existing (outer / non-linear) bindings are respected.
    fn enumerate_aliens(
        &self,
        rt: &mut Runtime,
        sig: &Signature,
        base: &Subst,
    ) -> Vec<RecordedSolution> {
        let mut out = Vec::new();
        let mut scratch = base.clone();
        let multiset = self.multiset.clone();
        self.rec_alien(0, &multiset, rt, sig, &mut scratch, &mut out);
        out
    }

    /// Match alien `ai` against each remaining subject element (canonical order, first-match-first),
    /// recursing to the next alien; at the leaf, distribute what's left among the top variables. The
    /// scratch substitution is checkpointed/restored around each element so backtracking is clean.
    fn rec_alien(
        &self,
        ai: usize,
        multiset: &[(DagId, u32)],
        rt: &mut Runtime,
        sig: &Signature,
        scratch: &mut Subst,
        out: &mut Vec<RecordedSolution>,
    ) {
        if ai == self.aliens.len() {
            self.distribute_leaf(multiset, rt, sig, scratch, out);
            return;
        }
        let alien = &self.aliens[ai];
        let automaton = LhsAutomaton::compile(alien.term.clone(), sig);
        for i in 0..multiset.len() {
            let (elem, m) = multiset[i];
            if m < alien.multiplicity {
                continue;
            }
            let checkpoint = scratch.clone();
            // An alien consumes a whole element — no extension on the sub-match.
            if let Some(mut sp) = automaton.match_(rt, sig, elem, scratch, false, false) {
                while sp.next(rt, sig, scratch) {
                    let mut reduced = multiset.to_vec();
                    reduced[i].1 -= alien.multiplicity;
                    if reduced[i].1 == 0 {
                        reduced.remove(i);
                    }
                    self.rec_alien(ai + 1, &reduced, rt, sig, scratch, out);
                }
            }
            *scratch = checkpoint; // restore for the next candidate element
        }
    }

    /// All aliens are placed; distribute the remaining multiset among the top variables (reusing the
    /// no-alien enumerator). A top variable already bound by an alien (non-linear across levels) has
    /// its value subtracted from the remainder first; the rest are free. Each accepted distribution
    /// becomes a fully-built [`RecordedSolution`] (top-variable bindings + the aliens' internal ones).
    fn distribute_leaf(
        &self,
        multiset: &[(DagId, u32)],
        rt: &mut Runtime,
        sig: &Signature,
        scratch: &Subst,
        out: &mut Vec<RecordedSolution>,
    ) {
        let mut avail: Vec<(DagId, u32)> = multiset.to_vec();
        let mut prebound: Vec<(u32, DagId)> = Vec::new();
        let mut free: Vec<usize> = Vec::new();
        for k in 0..self.var_indices.len() {
            match scratch.get(self.var_indices[k]) {
                Some(b) => {
                    if !subtract_binding(
                        &mut avail,
                        rt,
                        sig,
                        b,
                        self.var_coeffs[k],
                        self.symbol,
                        self.identity,
                    ) {
                        return; // the bound variable's value isn't present in the remainder
                    }
                    prebound.push((self.var_indices[k], b));
                }
                None => free.push(k),
            }
        }

        let free_coeffs: Vec<u32> = free.iter().map(|&k| self.var_coeffs[k]).collect();
        let lone_linear = free.len() == 1 && free_coeffs[0] == 1;
        let elements: Vec<DagId> = avail.iter().map(|&(e, _)| e).collect();
        let mults: Vec<u32> = avail.iter().map(|&(_, m)| m).collect();
        // Aliens already matched something, so a size-0 variable distribution is not the identity
        // no-op — allow it (`has_matched = true`).
        let cands = enumerate_distributions(
            &mults,
            &free_coeffs,
            self.ext_allowed,
            self.identity.is_some(),
            true,
            lone_linear,
            false,
        );
        for cand in cands {
            let mut binds = prebound.clone();
            let mut ok = true;
            for (ci, &k) in free.iter().enumerate() {
                let pairs: Vec<(DagId, u32)> = (0..elements.len())
                    .filter(|&i| cand.to_var[i][ci] > 0)
                    .map(|i| (elements[i], cand.to_var[i][ci]))
                    .collect();
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
                if !sig.sorts().leq(rt.sort_of(binding), self.var_sorts[k]) {
                    ok = false;
                    break;
                }
                binds.push((self.var_indices[k], binding));
            }
            if !ok {
                continue;
            }
            // Capture each alien's internal variable bindings (those not also a top variable).
            for &av in &self.alien_var_indices {
                if !self.var_indices.contains(&av)
                    && let Some(b) = scratch.get(av)
                {
                    binds.push((av, b));
                }
            }
            let residue: Vec<(DagId, u32)> = cand
                .residue
                .iter()
                .enumerate()
                .filter(|&(_, &r)| r > 0)
                .map(|(i, &r)| (elements[i], r))
                .collect();
            out.push(RecordedSolution { binds, residue });
        }
    }

    /// Splice the instantiated `rhs` into the matched position: a whole match is just `rhs`; an
    /// extension match re-canonicalizes `rhs ⊎ residue` as a fresh ACU node (order-free).
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        if self.matched_whole {
            return rhs;
        }
        let mut parts: Vec<(DagId, u32)> = Vec::with_capacity(self.residue.len() + 1);
        parts.push((rhs, 1));
        parts.extend_from_slice(&self.residue);
        rt.make_acu(sig, self.symbol, parts)
    }

    /// The unmatched residue (extension) of the most recent solution (tests / `xmatch` reporting).
    #[cfg(test)]
    pub(crate) fn residue(&self) -> &[(DagId, u32)] {
        &self.residue
    }

    /// Extension-match status of the *current* solution, for the `xmatch` display: `None` when this was
    /// not an extension match (no `Matched portion` line), else whether the whole subject was matched.
    pub(crate) fn matched_status(&self) -> Option<bool> {
        self.ext_allowed.then_some(self.matched_whole)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dag::DagId;
    use crate::engine::Engine;

    /// Each solution: the variable bindings (by index) and the residue (extension) multiset.
    type Solutions = Vec<(Vec<Option<DagId>>, Vec<(DagId, u32)>)>;

    /// Drive `match_` + `next` to collect every solution as `(variable bindings, residue)`. Mirrors
    /// the reference binary's `match`/`xmatch` enumeration.
    fn match_all(
        e: &mut Engine,
        pattern: Term,
        subject: DagId,
        ext_allowed: bool,
        nr_vars: u32,
    ) -> Solutions {
        let lhs = AcuLhs::compile_avoiding_nonlinear_vars(pattern, e.signature(), &HashSet::new());
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let (sig, rt) = e.parts_mut();
        let Some(mut sp) = lhs.match_(rt, sig, subject, ext_allowed) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        while sp.next(rt, sig, &mut subst) {
            let bindings = (0..nr_vars).map(|i| subst.get(i)).collect();
            out.push((bindings, sp.residue().to_vec()));
        }
        out
    }

    /// The **naive** no-alien matcher (the pre-Diophantine algorithm), kept live as a test-gated
    /// cross-check oracle per the AC-matcher plan's discipline. Replicates the old `match_` phase-1
    /// (collapse / ground consumption) + eager `enumerate_distributions` + candidate→binding build,
    /// returning the same `(bindings, residue)` stream. Used by [`differential_naive_vs_diophantine`]
    /// to assert the new lazy path yields the identical solution multiset on small subjects.
    fn naive_match_all(
        e: &mut Engine,
        pattern: Term,
        subject: DagId,
        ext_allowed: bool,
        nr_vars: u32,
    ) -> Solutions {
        let lhs = AcuLhs::compile_avoiding_nonlinear_vars(pattern, e.signature(), &HashSet::new());
        assert!(
            lhs.aliens.is_empty(),
            "naive cross-check is for the no-alien path"
        );
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let (sig, rt) = e.parts_mut();
        // Phase 1: collapse detection + ground consumption (identical to `match_`).
        let mut subject_is_identity = false;
        let (mut multiset, ext): (Vec<(DagId, u32)>, bool) = match &rt.node(subject).term {
            NodeTerm::Acu { symbol, args } if *symbol == lhs.symbol => (args.clone(), ext_allowed),
            _ if lhs
                .identity
                .is_some_and(|id| rt.is_identity(sig, id, subject)) =>
            {
                subject_is_identity = true;
                (Vec::new(), false)
            }
            _ => (vec![(subject, 1)], false),
        };
        let mut throwaway = Subst::new();
        throwaway.reset(0);
        for g in &lhs.grounds {
            let Some(pos) = multiset
                .iter()
                .position(|&(el, _)| rt.match_pattern(sig, g, el, &mut throwaway))
            else {
                return Vec::new();
            };
            multiset[pos].1 -= 1;
            if multiset[pos].1 == 0 {
                multiset.remove(pos);
            }
        }
        let elements: Vec<DagId> = multiset.iter().map(|&(el, _)| el).collect();
        let var_coeffs: Vec<u32> = lhs.vars.iter().map(|v| v.count).collect();
        let lone_linear =
            lhs.vars.len() == 1 && lhs.vars[0].count == 1 && !(ext && lhs.identity.is_some());
        let candidates = enumerate_distributions(
            &multiset.iter().map(|&(_, m)| m).collect::<Vec<_>>(),
            &var_coeffs,
            ext,
            lhs.identity.is_some(),
            !lhs.grounds.is_empty(),
            lone_linear,
            subject_is_identity,
        );
        let mut out = Vec::new();
        for cand in &candidates {
            let mut ok = true;
            let mut to_bind: Vec<(u32, DagId)> = Vec::new();
            for (k, v) in lhs.vars.iter().enumerate() {
                let pairs: Vec<(DagId, u32)> = (0..elements.len())
                    .filter(|&i| cand.to_var[i][k] > 0)
                    .map(|i| (elements[i], cand.to_var[i][k]))
                    .collect();
                let binding = if pairs.is_empty() {
                    match lhs.identity {
                        Some(id_sym) => rt.identity_dag(sig, id_sym),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                } else {
                    rt.make_acu(sig, lhs.symbol, pairs)
                };
                if !sig.sorts().leq(rt.sort_of(binding), v.sort) {
                    ok = false;
                    break;
                }
                to_bind.push((v.index, binding));
            }
            if !ok {
                continue;
            }
            let residue: Vec<(DagId, u32)> = cand
                .residue
                .iter()
                .enumerate()
                .filter(|&(_, &r)| r > 0)
                .map(|(i, &r)| (elements[i], r))
                .collect();
            let bindings: Vec<Option<DagId>> = (0..nr_vars)
                .map(|i| to_bind.iter().find(|&&(idx, _)| idx == i).map(|&(_, b)| b))
                .collect();
            out.push((bindings, residue));
        }
        out
    }

    /// Canonicalize a solution stream to a *set* of comparable name-tuples (per-variable binding
    /// name-multiset + residue name-multiset), so two matchers' outputs can be compared ignoring
    /// enumeration order and node identity.
    fn solution_set(
        e: &Engine,
        sols: &Solutions,
        nr_vars: u32,
    ) -> std::collections::BTreeSet<Vec<Vec<String>>> {
        sols.iter()
            .map(|(binds, residue)| {
                let mut row: Vec<Vec<String>> = (0..nr_vars as usize)
                    .map(|i| binds[i].map(|d| names(e, d)).unwrap_or_default())
                    .collect();
                let mut res: Vec<String> = residue
                    .iter()
                    .flat_map(|&(d, m)| std::iter::repeat_n(names(e, d), m as usize).flatten())
                    .collect();
                res.sort();
                row.push(res);
                row
            })
            .collect()
    }

    /// Decode a term into a sorted multiset of leaf-constant names (an AC binding `b+c` → `["b","c"]`,
    /// a constant `a` → `["a"]`), so a solution's bindings can be compared against the reference.
    fn names(e: &Engine, id: DagId) -> Vec<String> {
        let node = e.node(id);
        let kids: Vec<DagId> = node.children().collect();
        if kids.is_empty() {
            vec![e.symbol(node.symbol()).name().to_string()]
        } else {
            let mut out: Vec<String> = kids.into_iter().flat_map(|c| names(e, c)).collect();
            out.sort();
            out
        }
    }

    /// Differential cross-check (AC-matcher plan discipline): the new lazy Diophantine path and the
    /// retained naive `enumerate_distributions` path must yield the **identical solution multiset** on
    /// small subjects. Exercises several shapes: 2 collectors, a coefficient-2 variable, an element +
    /// collector pair, the identity-collapse case, and extension.
    #[test]
    fn differential_naive_vs_diophantine() {
        // Build a small AC signature with an identity and an element sort, plus a plain-AC sibling.
        let mut e = Engine::new();
        let elt = e.add_sort("Elt");
        let ne = e.add_sort("NeS");
        let set = e.add_sort("S");
        e.add_subsort(elt, ne);
        e.add_subsort(ne, set);
        e.close_sorts();
        let a = e.add_op("a", vec![], elt);
        let b = e.add_op("b", vec![], elt);
        let c = e.add_op("c", vec![], elt);
        let empty = e.add_op("empty", vec![], set);
        // _,_ : S S -> S [assoc comm id: empty]  (element sort Elt has sortBound 1).
        let comma = e.add_op_ac(",", vec![set, set], set, Some(empty));
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));

        let mk = |e: &mut Engine, ids: &[DagId]| e.make_ac(comma, ids.to_vec());
        let two = mk(&mut e, &[a0, b0]);
        let three = mk(&mut e, &[a0, b0, c0]);
        // a,a,b (a with multiplicity 2)
        let aab = mk(&mut e, &[a0, a0, b0]);

        // Each case: (pattern, subject, ext, nr_vars).
        let cases: Vec<(Term, DagId, bool, u32)> = vec![
            // X , Y  (two collectors) over a,b,c  — with id: also offers identity bindings.
            (
                Term::op(comma, vec![Term::var(0, set), Term::var(1, set)]),
                three,
                false,
                2,
            ),
            (
                Term::op(comma, vec![Term::var(0, set), Term::var(1, set)]),
                two,
                false,
                2,
            ),
            // E , S  (element + collector) over a,b,c — the D2a shape at small size.
            (
                Term::op(comma, vec![Term::var(0, elt), Term::var(1, set)]),
                three,
                false,
                2,
            ),
            // X , X  (coefficient-2 variable) over a,a,b.
            (
                Term::op(comma, vec![Term::var(0, set), Term::var(0, set)]),
                aab,
                false,
                1,
            ),
            // ground a , X  with extension over a,b,c (the collapse/identity-first case).
            (
                Term::op(comma, vec![Term::constant(a), Term::var(0, set)]),
                three,
                true,
                1,
            ),
            // X , Y with extension over a,b (residue splits).
            (
                Term::op(comma, vec![Term::var(0, set), Term::var(1, set)]),
                two,
                true,
                2,
            ),
        ];
        for (i, (pat, subj, ext, nv)) in cases.into_iter().enumerate() {
            let new_sols = match_all(&mut e, pat.clone(), subj, ext, nv);
            let naive_sols = naive_match_all(&mut e, pat, subj, ext, nv);
            let new_set = solution_set(&e, &new_sols, nv);
            let naive_set = solution_set(&e, &naive_sols, nv);
            assert_eq!(
                new_set,
                naive_set,
                "case {i}: Diophantine and naive matchers disagree (new={} naive={})",
                new_sols.len(),
                naive_sols.len()
            );
        }
    }

    /// `match X + Y <=? a + b + c` over `[assoc comm]` — the exact 6-solution sequence of the
    /// reference binary (every split of {a,b,c} into two non-empty ordered parts).
    #[test]
    fn ac_match_two_vars_six_solutions() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, b0, c0]);
        let pat = Term::op(plus, vec![Term::var(0, s), Term::var(1, s)]);

        let sols = match_all(&mut e, pat, subject, false, 2);
        let got: Vec<(Vec<String>, Vec<String>)> = sols
            .iter()
            .map(|(bnd, _)| (names(&e, bnd[0].unwrap()), names(&e, bnd[1].unwrap())))
            .collect();
        let expected = vec![
            (vec!["a".into()], vec!["b".into(), "c".into()]),
            (vec!["b".into()], vec!["a".into(), "c".into()]),
            (vec!["c".into()], vec!["a".into(), "b".into()]),
            (vec!["a".into(), "b".into()], vec!["c".into()]),
            (vec!["a".into(), "c".into()], vec!["b".into()]),
            (vec!["b".into(), "c".into()], vec!["a".into()]),
        ];
        assert_eq!(got, expected, "exact six-matcher sequence");
    }

    /// `match X + Y <=? a + b` over `[assoc comm id: e]` — the 4 solutions, including the two where a
    /// variable binds the identity `e`.
    #[test]
    fn ac_match_with_identity_four_solutions() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, Some(unit));
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let subject = e.make_ac(plus, vec![a0, b0]);
        let pat = Term::op(plus, vec![Term::var(0, s), Term::var(1, s)]);

        let sols = match_all(&mut e, pat, subject, false, 2);
        let mut got: Vec<(Vec<String>, Vec<String>)> = sols
            .iter()
            .map(|(bnd, _)| (names(&e, bnd[0].unwrap()), names(&e, bnd[1].unwrap())))
            .collect();
        got.sort();
        let mut expected = vec![
            (vec!["e".into()], vec!["a".into(), "b".into()]),
            (vec!["a".into()], vec!["b".into()]),
            (vec!["b".into()], vec!["a".into()]),
            (vec!["a".into(), "b".into()], vec!["e".into()]),
        ];
        expected.sort();
        assert_eq!(got.len(), 4, "four matchers");
        assert_eq!(got, expected);
    }

    /// `xmatch a + b <=? a + b + c` — one solution with extension: matched portion `a + b`, empty
    /// substitution, residue `c`.
    #[test]
    fn ac_xmatch_extension_one_solution_with_residue() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, b0, c0]);
        // ground pattern a + b (no variables)
        let pat = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);

        let sols = match_all(&mut e, pat, subject, true, 0);
        assert_eq!(sols.len(), 1, "one matcher (with extension)");
        let residue = &sols[0].1;
        let residue_names: Vec<String> =
            residue.iter().flat_map(|&(id, _)| names(&e, id)).collect();
        assert_eq!(residue_names, vec!["c".to_string()], "residue is c");
    }

    /// Without extension, the same ground pattern cannot match (the `c` cannot be left over).
    #[test]
    fn ac_match_ground_no_extension_fails() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, b0, c0]);
        let pat = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        assert!(
            match_all(&mut e, pat, subject, false, 0).is_empty(),
            "a+b !<=? a+b+c without ext"
        );
    }

    /// C8: ACU **alien** matching end to end. `eq s M + N = s (M + N)` reduces `s z + s s z` to
    /// `s s s z` in **2** rewrites — the count Maude's greedy matcher fixes by binding the alien `s M`
    /// to the canonically-smaller element `s z` (binding it to `s s z` would take 3). Was a panic
    /// (acu.rs:64); the greedy order comes straight from `ACU_GreedyMatcher`, not from tuning.
    #[test]
    fn ac_alien_reduce_greedy_count() {
        use crate::term::Equation;
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op_ac("+", vec![nat, nat], nat, None);
        // eq z + N = N .
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(z), Term::var(0, nat)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        // eq s M + N = s (M + N) .
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::op(s, vec![Term::var(0, nat)]), Term::var(1, nat)],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });
        let num = |e: &mut Engine, k: u32| {
            let mut t = e.make_const(z);
            for _ in 0..k {
                t = e.make_free(s, vec![t]);
            }
            t
        };
        let (one, two) = (num(&mut e, 1), num(&mut e, 2));
        let subject = e.make_ac(plus, vec![one, two]); // s z + s s z
        let r = e.reduce(subject);
        assert_eq!(
            e.rewrites(),
            2,
            "greedy binds the alien to the smaller element: 2 rewrites, not 3"
        );
        let three = num(&mut e, 3);
        assert!(e.deep_equal(r, three), "s z + s s z = s s s z");
    }
}
