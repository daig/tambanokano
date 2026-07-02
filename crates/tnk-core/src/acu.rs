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

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};
use crate::theory::LhsAutomaton;

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
    identity: Option<SymbolId>,
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
}

/// Structural equality on patterns (same operator + recursively-equal args, or the same variable
/// index) — the key that merges repeated aliens into one with a summed multiplicity, exactly as the
/// canonical pattern multiset would. Author-shallow recursion (alien patterns are small).
fn term_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Var(x), Term::Var(y)) => x.index == y.index,
        (Term::Op { symbol: sa, args: aa }, Term::Op { symbol: sb, args: ab }) => {
            sa == sb && aa.len() == ab.len() && aa.iter().zip(ab).all(|(x, y)| term_eq(x, y))
        }
        _ => false,
    }
}

impl AcuLhs {
    /// Compile an ACU pattern. The lhs is flattened modulo associativity, then each argument is
    /// classified as a nested same-operator application (spliced), a variable (accumulated by index),
    /// or a ground subterm. Alien subterms are not yet supported (a loud assert, never silent).
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("ACU lhs must be an application");
        let identity = sig.symbol(symbol).identity();
        let mut grounds: Vec<Term> = Vec::new();
        let mut aliens: Vec<AcuAlien> = Vec::new();
        let mut vars: Vec<AcuVar> = Vec::new();

        let mut stack = vec![lhs];
        while let Some(t) = stack.pop() {
            match t {
                Term::Op { symbol: s, args } if s == symbol => stack.extend(args),
                Term::Var(v) => match vars.iter_mut().find(|av| av.index == v.index) {
                    Some(av) => av.count += 1,
                    None => vars.push(AcuVar { index: v.index, count: 1, sort: v.sort }),
                },
                // A built-in literal is a ground, free-matchable leaf — same fast path as a ground Op.
                t @ Term::Na { .. } => grounds.push(t),
                // A ground, free-matchable subterm consumes one structurally-equal subject element
                // deterministically (the fast path). Everything else — a non-ground subterm (`s M`) or
                // a theory-rooted one — is an **alien**, matched recursively by its own automaton; merge
                // structurally-equal aliens, as the canonical pattern multiset does.
                t @ Term::Op { .. } if t.is_ground() && t.is_free_matchable(sig) => grounds.push(t),
                alien @ Term::Op { .. } => match aliens.iter_mut().find(|a| term_eq(&a.term, &alien)) {
                    Some(a) => a.multiplicity += 1,
                    None => aliens.push(AcuAlien { term: alien, multiplicity: 1 }),
                },
            }
        }
        AcuLhs { symbol, grounds, aliens, vars, identity }
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
            NodeTerm::Free { symbol: s, args } if args.is_empty() && Some(*s) == self.identity => {
                subject_is_identity = true;
                (Vec::new(), false)
            }
            _ => (vec![(subject, 1)], false),
        };

        // Consume each ground subterm against a structurally-equal element (deterministic).
        let mut throwaway = Subst::new();
        throwaway.reset(0);
        for g in &self.grounds {
            let pos = multiset.iter().position(|&(e, _)| rt.match_pattern(sig, g, e, &mut throwaway))?;
            multiset[pos].1 -= 1;
            if multiset[pos].1 == 0 {
                multiset.remove(pos);
            }
        }

        let elements: Vec<DagId> = multiset.iter().map(|&(e, _)| e).collect();
        let var_coeffs: Vec<u32> = self.vars.iter().map(|v| v.count).collect();
        // No aliens: precompute the variable distributions eagerly (pure, the proven B1 fast path). A
        // single linear variable is the *collector* (Maude's LONE_VARIABLE) — it absorbs the entire
        // remainder, a correctness rule not just an ordering one (`eq a + X = b` on `a + c + c` gives
        // `b`, not `b + c`). With aliens present we defer to `next` instead: matching an alien builds
        // binding nodes, so it needs `&mut Runtime` the immutable first phase does not have.
        let candidates = if self.aliens.is_empty() {
            // The lone-variable collector (force the whole remainder) is Maude's no-identity
            // behavior; a variable that can take the identity is enumerated smallest-first
            // instead (`a + X = b` on `a + c + c`: no id ⇒ `b`; with `id: e` ⇒ `b + c + c`,
            // X := e first with the rest as extension residue — both oracle-verified).
            let lone_linear = self.vars.len() == 1
                && self.vars[0].count == 1
                && !(ext && self.identity.is_some());
            enumerate_distributions(
                &multiset.iter().map(|&(_, m)| m).collect::<Vec<_>>(),
                &var_coeffs,
                ext,
                self.identity.is_some(),
                !self.grounds.is_empty(),
                lone_linear,
                subject_is_identity,
            )
        } else {
            Vec::new()
        };
        let mut alien_var_indices: Vec<u32> = Vec::new();
        for a in &self.aliens {
            collect_vars(&a.term, &mut alien_var_indices);
        }

        Some(AcuSubproblem {
            symbol: self.symbol,
            identity: self.identity,
            ext_allowed: ext,
            elements,
            var_indices: self.vars.iter().map(|v| v.index).collect(),
            var_sorts: self.vars.iter().map(|v| v.sort).collect(),
            var_coeffs,
            candidates,
            cursor: 0,
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
    let per_element: Vec<Vec<Split>> =
        mults.iter().map(|&m| compositions(m, coeffs, ext_allowed)).collect();
    // An element with no valid composition makes the whole match impossible.
    if per_element.iter().any(|s| s.is_empty()) {
        return Vec::new();
    }

    let radices: Vec<usize> = per_element.iter().map(Vec::len).collect();
    let mut idx = vec![0usize; per_element.len()];
    let mut out: Vec<Candidate> = Vec::new();
    loop {
        let chosen: Vec<&Split> = idx.iter().enumerate().map(|(i, &j)| &per_element[i][j]).collect();
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

fn compose(k: usize, remaining: u32, coeffs: &[u32], cur: &mut Vec<u32>, residue: bool, out: &mut Vec<Split>) {
    if k == coeffs.len() {
        if residue || remaining == 0 {
            out.push(Split { to_var: cur.clone(), residue: remaining });
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
    binding: DagId,
    coeff: u32,
    symbol: SymbolId,
) -> bool {
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
    identity: Option<SymbolId>,
    ext_allowed: bool,
    var_indices: Vec<u32>,
    var_sorts: Vec<SortId>,
    var_coeffs: Vec<u32>,
    // ---- no-alien path: precomputed variable distributions over `elements` ----
    elements: Vec<DagId>,
    candidates: Vec<Candidate>,
    cursor: usize,
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
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();

        if !self.aliens.is_empty() {
            return self.next_alien(rt, sig, subst);
        }

        while self.cursor < self.candidates.len() {
            let ci = self.cursor;
            self.cursor += 1;
            let r = self.var_indices.len();
            let mut to_bind: Vec<(u32, DagId)> = Vec::with_capacity(r);
            let mut residue: Vec<(DagId, u32)> = Vec::new();
            let mut ok = true;
            {
                let cand = &self.candidates[ci];
                for k in 0..r {
                    let pairs: Vec<(DagId, u32)> = (0..self.elements.len())
                        .filter(|&i| cand.to_var[i][k] > 0)
                        .map(|i| (self.elements[i], cand.to_var[i][k]))
                        .collect();
                    let binding = if pairs.is_empty() {
                        match self.identity {
                            // The CACHED identity dag (already-reduced): what makes the
                            // collapse rewrite one-shot (see Runtime::identity_dag).
                            Some(id_sym) => rt.identity_dag(sig, id_sym),
                            None => {
                                ok = false; // unreachable: filtered when no identity
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
                    to_bind.push((self.var_indices[k], binding));
                }
                if ok {
                    for (i, &res) in cand.residue.iter().enumerate() {
                        if res > 0 {
                            residue.push((self.elements[i], res));
                        }
                    }
                }
            }
            if !ok {
                continue;
            }
            // Apply the bindings, honoring any variable **already bound** by an outer subterm — a
            // non-linear occurrence across arguments, e.g. `E in (E, S)` binds `E` from the first
            // argument, so the enumerated multiset binding must equal it (else this candidate is no
            // solution). The free matcher does the same deep-equal check (`term.rs`); the alien path
            // already seeds from the incoming subst.
            let mut consistent = true;
            for &(idx, b) in &to_bind {
                match subst.get(idx) {
                    Some(existing) => {
                        if !rt.deep_equal(existing, b) {
                            consistent = false;
                            break;
                        }
                    }
                    None => {
                        subst.bind(idx, b);
                        self.bound.push(idx);
                    }
                }
            }
            if !consistent {
                for &idx in &self.bound {
                    subst.unbind(idx);
                }
                self.bound.clear();
                continue;
            }
            self.matched_whole = residue.is_empty();
            self.residue = residue;
            return true;
        }
        false
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
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        self.matched_whole = residue.is_empty();
        self.residue = residue;
        true
    }

    /// Enumerate every solution of the alien + variable parts against the post-grounds multiset,
    /// **greedy-first** (Maude's `ACU_GreedyMatcher` order): each alien is tried against the subject
    /// elements in canonical order, taking the first match before the next. `base` seeds the scratch
    /// substitution so existing (outer / non-linear) bindings are respected.
    fn enumerate_aliens(&self, rt: &mut Runtime, sig: &Signature, base: &Subst) -> Vec<RecordedSolution> {
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
            if let Some(mut sp) = automaton.match_(rt, sig, elem, scratch, false) {
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
                    if !subtract_binding(&mut avail, rt, b, self.var_coeffs[k], self.symbol) {
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
        let lhs = AcuLhs::compile(pattern, e.signature());
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let (sig, rt) = e.parts_mut();
        let Some(mut sp) = lhs.match_(rt, sig, subject, ext_allowed) else { return Vec::new() };
        let mut out = Vec::new();
        while sp.next(rt, sig, &mut subst) {
            let bindings = (0..nr_vars).map(|i| subst.get(i)).collect();
            out.push((bindings, sp.residue().to_vec()));
        }
        out
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

    /// `match X + Y <=? a + b + c` over `[assoc comm]` — the 6 solutions of the reference binary
    /// (every split of {a,b,c} into two non-empty ordered parts).
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
        let mut got: Vec<(Vec<String>, Vec<String>)> = sols
            .iter()
            .map(|(bnd, _)| (names(&e, bnd[0].unwrap()), names(&e, bnd[1].unwrap())))
            .collect();
        got.sort();
        let mut expected = vec![
            (vec!["a".into()], vec!["b".into(), "c".into()]),
            (vec!["b".into()], vec!["a".into(), "c".into()]),
            (vec!["c".into()], vec!["a".into(), "b".into()]),
            (vec!["a".into(), "b".into()], vec!["c".into()]),
            (vec!["a".into(), "c".into()], vec!["b".into()]),
            (vec!["b".into(), "c".into()], vec!["a".into()]),
        ];
        expected.sort();
        assert_eq!(got.len(), 6, "six matchers");
        assert_eq!(got, expected);
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
        assert!(match_all(&mut e, pat, subject, false, 0).is_empty(), "a+b !<=? a+b+c without ext");
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
            lhs: Term::op(plus, vec![Term::op(s, vec![Term::var(0, nat)]), Term::var(1, nat)]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
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
        assert_eq!(e.rewrites(), 2, "greedy binds the alien to the smaller element: 2 rewrites, not 3");
        let three = num(&mut e, 3);
        assert!(e.deep_equal(r, three), "s z + s s z = s s s z");
    }
}
