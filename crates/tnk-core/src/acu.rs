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

/// A compiled ACU left-hand side: the flattened pattern multiset partitioned into ground subterms
/// (each consumes one structurally-equal subject element) and distinct variables.
pub(crate) struct AcuLhs {
    symbol: SymbolId,
    /// Ground sub-patterns (no variables); each must match one subject element.
    grounds: Vec<Term>,
    /// Distinct variable occurrences under the operator (a repeated index is non-linear).
    vars: Vec<AcuVar>,
    identity: Option<SymbolId>,
}

struct AcuVar {
    index: u32,
    /// How many times this variable index occurs in the pattern (the Diophantine coefficient).
    count: u32,
    sort: SortId,
}

impl AcuLhs {
    /// Compile an ACU pattern. The lhs is flattened modulo associativity, then each argument is
    /// classified as a nested same-operator application (spliced), a variable (accumulated by index),
    /// or a ground subterm. Alien subterms are not yet supported (a loud assert, never silent).
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("ACU lhs must be an application");
        let identity = sig.symbol(symbol).identity();
        let mut grounds: Vec<Term> = Vec::new();
        let mut vars: Vec<AcuVar> = Vec::new();

        let mut stack = vec![lhs];
        while let Some(t) = stack.pop() {
            match t {
                Term::Op { symbol: s, args } if s == symbol => stack.extend(args),
                Term::Var(v) => match vars.iter_mut().find(|av| av.index == v.index) {
                    Some(av) => av.count += 1,
                    None => vars.push(AcuVar { index: v.index, count: 1, sort: v.sort }),
                },
                ground @ Term::Op { .. } => {
                    assert!(
                        ground.is_ground(),
                        "an alien (non-ground, non-variable) subterm under an ACU operator is not \
                         yet supported (B1 follow-up)"
                    );
                    grounds.push(ground);
                }
            }
        }
        AcuLhs { symbol, grounds, vars, identity }
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
        // The subject must be a canonical ACU node of this operator. (A collapsed single-element
        // subject is a follow-up; it never arises in reduction, where the top symbol selects the
        // equation set.)
        let mut multiset: Vec<(DagId, u32)> = match &rt.node(subject).term {
            NodeTerm::Acu { symbol, args } if *symbol == self.symbol => args.clone(),
            _ => return None,
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
        let coeffs: Vec<u32> = self.vars.iter().map(|v| v.count).collect();
        // A single linear variable is the *collector*: it absorbs the entire remainder (Maude's
        // LONE_VARIABLE strategy), giving one whole match — not a minimal binding with extension.
        // This is a correctness rule, not just an ordering one: `eq a + X = b` on `a + c + c` must
        // give `b` (X → c+c), not `b + c` (the system is non-confluent under extension; Maude's
        // strategy picks the collector match).
        let lone_linear = self.vars.len() == 1 && self.vars[0].count == 1;
        let candidates = enumerate_distributions(
            &multiset.iter().map(|&(_, m)| m).collect::<Vec<_>>(),
            &coeffs,
            ext_allowed,
            self.identity.is_some(),
            !self.grounds.is_empty(),
            lone_linear,
        );

        Some(AcuSubproblem {
            symbol: self.symbol,
            identity: self.identity,
            elements,
            var_indices: self.vars.iter().map(|v| v.index).collect(),
            var_sorts: self.vars.iter().map(|v| v.sort).collect(),
            candidates,
            cursor: 0,
            bound: Vec::new(),
            residue: Vec::new(),
            matched_whole: true,
        })
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
fn enumerate_distributions(
    mults: &[u32],
    coeffs: &[u32],
    ext_allowed: bool,
    identity: bool,
    has_grounds: bool,
    lone_linear: bool,
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
        if all_vars_filled && (has_grounds || matched > 0) {
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
    elements: Vec<DagId>,
    var_indices: Vec<u32>,
    var_sorts: Vec<SortId>,
    candidates: Vec<Candidate>,
    cursor: usize,
    /// Variable indices bound by the most recent solution (unbound before the next one).
    bound: Vec<u32>,
    residue: Vec<(DagId, u32)>,
    matched_whole: bool,
}

impl AcuSubproblem {
    /// Advance to the next solution, binding its variables into `subst` and recording its residue;
    /// `false` when exhausted. Builds binding nodes (so it needs `&mut Runtime`); a candidate whose
    /// binding violates a variable's sort is skipped.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();

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
                            Some(id_sym) => rt.make_const(sig, id_sym),
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
            for &(idx, b) in &to_bind {
                subst.bind(idx, b);
                self.bound.push(idx);
            }
            self.matched_whole = residue.is_empty();
            self.residue = residue;
            return true;
        }
        false
    }

    /// Whether the most recent solution matched the whole subject (no residue/extension).
    pub(crate) fn matched_whole(&self) -> bool {
        self.matched_whole
    }
    /// The unmatched residue (extension) of the most recent solution — the elements an AC rewrite
    /// splices back around the instantiated right-hand side.
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
}
