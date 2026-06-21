//! AU matching: a complete, multi-solution matcher for `assoc [id:]` (associative, **not**
//! commutative) operators — lists, sequences, string concatenation.
//!
//! The pattern and subject are ordered sequences over the operator. A pattern matches a **contiguous
//! sub-sequence** of the subject; its elements partition that sub-sequence left-to-right (a ground
//! subterm matches one equal element, a variable a contiguous run). With extension the matched
//! sub-sequence can sit anywhere, leaving an ordered **prefix + suffix** residue (vs the ACU theory's
//! order-free multiset residue) — so the rewrite splice is `prefix ++ rhs ++ suffix`.
//!
//! **Strategy (correctness-first, mirrors `acu`).** A complete backtracking enumeration of
//! `(start, run-lengths)`, yielded **maximal-matched-first**, so a lone (linear) variable absorbs the
//! whole remainder — Maude's collector strategy: `eq a X = b` on `a c c` gives `b` (X → `c c`), not
//! `b c`. Scope: ground subterms + **linear** variables + identity; non-linear variables (`X X`) and
//! alien subterms are loud unsupported-asserts (follow-ups).

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};

/// A compiled AU left-hand side: the flattened pattern as an ordered list of elements.
pub(crate) struct AuLhs {
    symbol: SymbolId,
    elements: Vec<AuElem>,
    identity: Option<SymbolId>,
}

enum AuElem {
    /// A ground sub-pattern: matches exactly one structurally-equal subject element.
    Ground(Term),
    /// A variable: matches a contiguous run (≥1, or ≥0 with identity).
    Var { index: u32, sort: SortId },
}

impl AuLhs {
    /// Compile an AU pattern: flatten modulo associativity (order preserved), then classify each
    /// argument. Non-linear (repeated) variables and alien subterms are not yet supported (loud
    /// asserts, never silent).
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("AU lhs must be an application");
        let identity = sig.symbol(symbol).identity();
        let mut flat: Vec<Term> = Vec::new();
        flatten(lhs, symbol, &mut flat);

        let mut elements: Vec<AuElem> = Vec::new();
        let mut seen_vars: Vec<u32> = Vec::new();
        for t in flat {
            let ground = t.is_ground();
            match t {
                Term::Var(v) => {
                    assert!(
                        !seen_vars.contains(&v.index),
                        "non-linear AU pattern (a repeated variable) is not yet supported (follow-up)"
                    );
                    seen_vars.push(v.index);
                    elements.push(AuElem::Var { index: v.index, sort: v.sort });
                }
                other => {
                    assert!(
                        ground,
                        "an alien (non-ground, non-variable) subterm under an AU operator is not yet \
                         supported (follow-up)"
                    );
                    assert!(
                        other.is_free_matchable(sig),
                        "a theory-rooted ground subterm under an AU operator is not yet supported: \
                         it is matched by the free matcher, which fails silently on a theory subject \
                         (cross-theory composition is a follow-up)"
                    );
                    elements.push(AuElem::Ground(other));
                }
            }
        }
        AuLhs { symbol, elements, identity }
    }

    /// First match phase: the subject must be an AU node of this operator; enumerate every contiguous
    /// match (with extension if `ext_allowed`) as a `(start, run-lengths)` plan, ordered
    /// maximal-matched-first. Reads only the runtime (ground checks, no allocation).
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        ext_allowed: bool,
    ) -> Option<AuSubproblem> {
        let seq: Vec<DagId> = match &rt.node(subject).term {
            NodeTerm::Au { symbol, args } if *symbol == self.symbol => args.clone(),
            _ => return None,
        };
        let n = seq.len();
        let mut throwaway = Subst::new();
        throwaway.reset(0);
        let mut candidates: Vec<Candidate> = Vec::new();
        let last_start = if ext_allowed { n } else { 0 };
        for start in 0..=last_start {
            let mut lengths = Vec::with_capacity(self.elements.len());
            self.walk(rt, sig, &seq, start, 0, start, ext_allowed, &mut lengths, &mut throwaway, &mut candidates);
        }
        // Maximal matched portion first → a lone linear variable absorbs the remainder (collector).
        candidates.sort_by_key(|c| std::cmp::Reverse(c.matched()));

        let var_at: Vec<Option<(u32, SortId)>> = self
            .elements
            .iter()
            .map(|e| match e {
                AuElem::Var { index, sort } => Some((*index, *sort)),
                AuElem::Ground(_) => None,
            })
            .collect();
        Some(AuSubproblem {
            symbol: self.symbol,
            identity: self.identity,
            subject: seq,
            var_at,
            candidates,
            cursor: 0,
            bound: Vec::new(),
            prefix: Vec::new(),
            suffix: Vec::new(),
            matched_whole: true,
        })
    }

    /// Recursive enumerator: match `elements[elem_idx..]` against `seq` starting at `pos`, accumulating
    /// each element's run length, and record a candidate when all elements are placed.
    #[allow(clippy::too_many_arguments)]
    fn walk(
        &self,
        rt: &Runtime,
        sig: &Signature,
        seq: &[DagId],
        pos: usize,
        elem_idx: usize,
        start: usize,
        ext_allowed: bool,
        lengths: &mut Vec<usize>,
        throwaway: &mut Subst,
        out: &mut Vec<Candidate>,
    ) {
        let n = seq.len();
        if elem_idx == self.elements.len() {
            // All elements placed, ending at `pos`. With extension the tail `seq[pos..]` is residue;
            // without it the match must reach the end.
            if ext_allowed || pos == n {
                out.push(Candidate { start, lengths: lengths.clone() });
            }
            return;
        }
        match &self.elements[elem_idx] {
            AuElem::Ground(g) => {
                if pos < n && rt.match_pattern(sig, g, seq[pos], throwaway) {
                    lengths.push(1);
                    self.walk(rt, sig, seq, pos + 1, elem_idx + 1, start, ext_allowed, lengths, throwaway, out);
                    lengths.pop();
                }
            }
            AuElem::Var { .. } => {
                let min_len = usize::from(self.identity.is_none()); // ≥1 without identity, else ≥0
                for len in min_len..=(n - pos) {
                    lengths.push(len);
                    self.walk(rt, sig, seq, pos + len, elem_idx + 1, start, ext_allowed, lengths, throwaway, out);
                    lengths.pop();
                }
            }
        }
    }
}

/// Flatten `term` modulo associativity into `out`, preserving left-to-right order.
fn flatten(term: Term, symbol: SymbolId, out: &mut Vec<Term>) {
    match term {
        Term::Op { symbol: s, args } if s == symbol => {
            for a in args {
                flatten(a, symbol, out);
            }
        }
        other => out.push(other),
    }
}

/// One match plan: the start offset into the subject and the run length consumed by each pattern
/// element (in order). `matched` = total consumed.
struct Candidate {
    start: usize,
    lengths: Vec<usize>,
}

impl Candidate {
    fn matched(&self) -> usize {
        self.lengths.iter().sum()
    }
}

/// A resumable enumerator over the solutions of an [`AuLhs`] against a subject (an arm of the closed
/// [`crate::theory::Subproblem`] enum). Owns its state, so it survives the `&mut Runtime` calls the
/// driver makes between solutions.
pub(crate) struct AuSubproblem {
    symbol: SymbolId,
    identity: Option<SymbolId>,
    subject: Vec<DagId>,
    /// Per pattern element: `Some((index, sort))` for a variable, `None` for a ground.
    var_at: Vec<Option<(u32, SortId)>>,
    candidates: Vec<Candidate>,
    cursor: usize,
    bound: Vec<u32>,
    /// The unmatched ordered prefix/suffix of the most recent solution (the extension residue).
    prefix: Vec<DagId>,
    suffix: Vec<DagId>,
    matched_whole: bool,
}

impl AuSubproblem {
    /// Advance to the next solution, binding its variables (each to the AU node of its run) and
    /// recording the prefix/suffix residue; `false` when exhausted. A candidate whose binding violates
    /// a variable's sort is skipped.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();

        while self.cursor < self.candidates.len() {
            let ci = self.cursor;
            self.cursor += 1;
            let mut to_bind: Vec<(u32, DagId)> = Vec::new();
            let mut ok = true;
            let (start, total) = {
                let cand = &self.candidates[ci];
                let start = cand.start;
                let mut pos = start;
                for (elem_idx, &len) in cand.lengths.iter().enumerate() {
                    if let Some((index, sort)) = self.var_at[elem_idx] {
                        let run = &self.subject[pos..pos + len];
                        let binding = match run {
                            [] => match self.identity {
                                Some(id_sym) => rt.make_const(sig, id_sym),
                                None => {
                                    ok = false;
                                    break;
                                }
                            },
                            [single] => *single,
                            many => rt.make_au(sig, self.symbol, many.to_vec()),
                        };
                        if !sig.sorts().leq(rt.sort_of(binding), sort) {
                            ok = false;
                            break;
                        }
                        to_bind.push((index, binding));
                    }
                    pos += len;
                }
                (start, pos - start)
            };
            if !ok {
                continue;
            }
            for &(idx, b) in &to_bind {
                subst.bind(idx, b);
                self.bound.push(idx);
            }
            self.prefix = self.subject[..start].to_vec();
            self.suffix = self.subject[start + total..].to_vec();
            self.matched_whole = self.prefix.is_empty() && self.suffix.is_empty();
            return true;
        }
        false
    }

    /// Splice the instantiated `rhs` into the matched position: a whole match is just `rhs`; an
    /// extension match re-assembles the **ordered** `prefix ++ rhs ++ suffix` as a fresh AU node.
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        if self.matched_whole {
            return rhs;
        }
        let mut seq: Vec<DagId> = Vec::with_capacity(self.prefix.len() + 1 + self.suffix.len());
        seq.extend_from_slice(&self.prefix);
        seq.push(rhs);
        seq.extend_from_slice(&self.suffix);
        rt.make_au(sig, self.symbol, seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// Drive `match_` + `next` to collect each solution's variable bindings.
    fn match_all(
        e: &mut Engine,
        pattern: Term,
        subject: DagId,
        ext_allowed: bool,
        nr_vars: u32,
    ) -> Vec<Vec<Option<DagId>>> {
        let lhs = AuLhs::compile(pattern, e.signature());
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let (sig, rt) = e.parts_mut();
        let Some(mut sp) = lhs.match_(rt, sig, subject, ext_allowed) else { return Vec::new() };
        let mut out = Vec::new();
        while sp.next(rt, sig, &mut subst) {
            out.push((0..nr_vars).map(|i| subst.get(i)).collect());
        }
        out
    }

    /// Decode a term into its **ordered** sequence of leaf-constant names (AU is not commutative, so
    /// order is significant): `a b` → `["a","b"]`, a constant `a` → `["a"]`.
    fn names(e: &Engine, id: DagId) -> Vec<String> {
        let node = e.node(id);
        let kids: Vec<DagId> = node.children().collect();
        if kids.is_empty() {
            vec![e.symbol(node.symbol()).name().to_string()]
        } else {
            kids.into_iter().flat_map(|c| names(e, c)).collect()
        }
    }

    fn au_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let nil = e.add_op("nil", vec![], s);
        let cat = e.add_op_au("__", vec![s, s], s, Some(nil));
        (e, s, a, b, c, nil, cat)
    }

    /// `match X Y <=? a b c` over `[assoc id: nil]` — the 4 ordered prefix/suffix splits (== reference
    /// binary), including the two where a variable binds the identity `nil`.
    #[test]
    fn au_match_two_vars_four_solutions() {
        let (mut e, s, a, b, c, _nil, cat) = au_ctx();
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_au(cat, vec![a0, b0, c0]);
        let pat = Term::op(cat, vec![Term::var(0, s), Term::var(1, s)]);

        let sols = match_all(&mut e, pat, subject, false, 2);
        let mut got: Vec<(Vec<String>, Vec<String>)> = sols
            .iter()
            .map(|b| (names(&e, b[0].unwrap()), names(&e, b[1].unwrap())))
            .collect();
        got.sort();
        let mut expected = vec![
            (vec!["nil".into()], vec!["a".into(), "b".into(), "c".into()]),
            (vec!["a".into()], vec!["b".into(), "c".into()]),
            (vec!["a".into(), "b".into()], vec!["c".into()]),
            (vec!["a".into(), "b".into(), "c".into()], vec!["nil".into()]),
        ];
        expected.sort();
        assert_eq!(got.len(), 4, "four ordered splits");
        assert_eq!(got, expected);
    }

    /// AU construction is canonical modulo associativity and identity, but order is significant.
    #[test]
    fn au_canonical_modulo_associativity_not_commutativity() {
        let (mut e, _s, a, b, c, nil, cat) = au_ctx();
        let abc_left = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let ab = e.make_au(cat, vec![x, y]);
            let z = e.make_const(c);
            e.make_au(cat, vec![ab, z])
        };
        let abc_right = {
            let (y, z) = (e.make_const(b), e.make_const(c));
            let bc = e.make_au(cat, vec![y, z]);
            let x = e.make_const(a);
            e.make_au(cat, vec![x, bc])
        };
        assert!(e.deep_equal(abc_left, abc_right), "(a b) c == a (b c)");
        assert_eq!(e.node(abc_left).children().count(), 3, "flattened to 3 ordered children");

        let a_nil = {
            let (x, u) = (e.make_const(a), e.make_const(nil));
            e.make_au(cat, vec![x, u])
        };
        assert_eq!(e.node(a_nil).symbol(), a, "a nil collapses to a");

        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_au(cat, vec![x, y])
        };
        let ba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_au(cat, vec![x, y])
        };
        assert!(!e.deep_equal(ab, ba), "AU is not commutative: a b != b a");
    }
}
