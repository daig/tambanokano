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
//! `b c`. The simple case (ground subterms + linear variables + identity) takes a pure enumeration in
//! `match_`; **aliens** (a non-ground subterm under the operator — `s M`, Maude's `NonGroundAlien`) and
//! **non-linear** variables (`X X`) take a binding-aware backtracking path in `next` (an alien is
//! matched recursively by its own automaton, which needs `&mut Runtime`). Same ordering convention
//! throughout (var lengths ascending + a stable maximal-matched-first sort), so the alien binds to the
//! **leftmost** position first — the order Maude's greedy matcher uses, fixing the reduce count.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};
use crate::theory::LhsAutomaton;

/// A compiled AU left-hand side: the flattened pattern as an ordered list of elements.
pub(crate) struct AuLhs {
    symbol: SymbolId,
    elements: Vec<AuElem>,
    identity: Option<SymbolId>,
    /// `true` when the pattern has an alien or a non-linear (repeated) variable — matched by the
    /// binding-aware path in [`AuSubproblem::next`] rather than the pure positional enumeration.
    complex: bool,
}

#[derive(Clone)]
enum AuElem {
    /// A ground, free-matchable sub-pattern: matches exactly one structurally-equal subject element.
    Ground(Term),
    /// A variable: matches a contiguous run (≥1, or ≥0 with identity). A repeated index is non-linear.
    Var { index: u32, sort: SortId },
    /// An alien (non-ground, or theory-rooted) sub-pattern: matches exactly one subject element
    /// recursively via its own automaton (Maude's `NonGroundAlien`).
    Alien(Term),
}

impl AuLhs {
    /// Compile an AU pattern: flatten modulo associativity (order preserved), then classify each
    /// argument as a ground (free-matchable) subterm, a variable, or an **alien** (anything else —
    /// matched recursively). A repeated variable or any alien sets the `complex` flag.
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("AU lhs must be an application");
        let identity = sig.symbol(symbol).identity();
        let mut flat: Vec<Term> = Vec::new();
        flatten(lhs, symbol, &mut flat);

        let mut elements: Vec<AuElem> = Vec::new();
        let mut seen_vars: Vec<u32> = Vec::new();
        let mut complex = false;
        for t in flat {
            match t {
                Term::Var(v) => {
                    if seen_vars.contains(&v.index) {
                        complex = true; // a repeated (non-linear) variable
                    }
                    seen_vars.push(v.index);
                    elements.push(AuElem::Var { index: v.index, sort: v.sort });
                }
                t @ Term::Op { .. } if t.is_ground() && t.is_free_matchable(sig) => {
                    elements.push(AuElem::Ground(t))
                }
                alien @ Term::Op { .. } => {
                    complex = true;
                    elements.push(AuElem::Alien(alien));
                }
            }
        }
        AuLhs { symbol, elements, identity, complex }
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

        // Aliens / non-linear variables need binding while enumerating, so defer to `next` (it has the
        // `&mut Runtime` the alien sub-automata require).
        if self.complex {
            let mut all_var_indices: Vec<u32> = Vec::new();
            for e in &self.elements {
                match e {
                    AuElem::Var { index, .. } => {
                        if !all_var_indices.contains(index) {
                            all_var_indices.push(*index);
                        }
                    }
                    AuElem::Alien(t) => collect_vars(t, &mut all_var_indices),
                    AuElem::Ground(_) => {}
                }
            }
            return Some(AuSubproblem {
                symbol: self.symbol,
                identity: self.identity,
                subject: seq,
                var_at: Vec::new(),
                candidates: Vec::new(),
                cursor: 0,
                complex: true,
                elements: self.elements.clone(),
                ext_allowed,
                all_var_indices,
                recorded: None,
                rec_cursor: 0,
                bound: Vec::new(),
                prefix: Vec::new(),
                suffix: Vec::new(),
                matched_whole: true,
            });
        }

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
                AuElem::Alien(_) => unreachable!("the pure path has no aliens (would set `complex`)"),
            })
            .collect();
        Some(AuSubproblem {
            symbol: self.symbol,
            identity: self.identity,
            subject: seq,
            var_at,
            candidates,
            cursor: 0,
            complex: false,
            elements: Vec::new(),
            ext_allowed,
            all_var_indices: Vec::new(),
            recorded: None,
            rec_cursor: 0,
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
            AuElem::Alien(_) => unreachable!("the pure path has no aliens (would set `complex`)"),
        }
    }
}

/// Collect the distinct variable indices in a pattern (an alien's internal bindings to capture).
fn collect_vars(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Op { args, .. } => args.iter().for_each(|a| collect_vars(a, out)),
    }
}

/// The run length a bound variable's value occupies in the subject sequence — its flattened element
/// count under `symbol` (an AU node spreads into its args; the identity is 0; anything else is 1) —
/// used to force a repeated (non-linear) variable to re-match the exact same run.
fn au_run_len(rt: &Runtime, binding: DagId, symbol: SymbolId, identity: Option<SymbolId>) -> usize {
    match &rt.node(binding).term {
        NodeTerm::Au { symbol: s, args } if *s == symbol => args.len(),
        NodeTerm::Free { symbol: s, args } if args.is_empty() && Some(*s) == identity => 0,
        _ => 1,
    }
}

/// Build the AU binding for a contiguous run of the subject: empty → the identity (`None` if the
/// operator has none, so the empty run is rejected), a single element → that element, else a fresh AU
/// node. The canonical counterpart of the run that [`au_run_len`] measures.
fn build_run(
    rt: &mut Runtime,
    sig: &Signature,
    symbol: SymbolId,
    identity: Option<SymbolId>,
    run: &[DagId],
) -> Option<DagId> {
    match run {
        [] => identity.map(|id| rt.make_const(sig, id)),
        [single] => Some(*single),
        many => Some(rt.make_au(sig, symbol, many.to_vec())),
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
    // ---- pure path (no aliens, all-linear): precomputed `(start, run-lengths)` plans ----
    /// Per pattern element: `Some((index, sort))` for a variable, `None` for a ground.
    var_at: Vec<Option<(u32, SortId)>>,
    candidates: Vec<Candidate>,
    cursor: usize,
    // ---- complex path (aliens / non-linear vars): lazily enumerated on the first `next` ----
    complex: bool,
    elements: Vec<AuElem>,
    ext_allowed: bool,
    /// All pattern variable indices (top + alien-internal), captured into each recorded solution.
    all_var_indices: Vec<u32>,
    /// Fully-built solutions, maximal-matched-first; `None` until the first `next` enumerates them.
    recorded: Option<Vec<AuRecorded>>,
    rec_cursor: usize,
    // ---- shared replay state ----
    bound: Vec<u32>,
    /// The unmatched ordered prefix/suffix of the most recent solution (the extension residue).
    prefix: Vec<DagId>,
    suffix: Vec<DagId>,
    matched_whole: bool,
}

/// One fully-built complex-path solution: every pattern variable's binding and the matched span
/// `[start, end)` (the prefix `subject[..start]` / suffix `subject[end..]` are the extension residue).
struct AuRecorded {
    binds: Vec<(u32, DagId)>,
    start: usize,
    end: usize,
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

        if self.complex {
            return self.next_complex(rt, sig, subst);
        }

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

    /// The complex-path (aliens / non-linear vars) counterpart: enumerate all solutions on the first
    /// call (driving alien sub-automata — needs `&mut Runtime`), maximal-matched-first, then replay.
    fn next_complex(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        if self.recorded.is_none() {
            let sols = self.enumerate_complex(rt, sig, subst);
            self.recorded = Some(sols);
        }
        let (binds, start, end) = {
            let recorded = self.recorded.as_ref().expect("just enumerated");
            if self.rec_cursor >= recorded.len() {
                return false;
            }
            let sol = &recorded[self.rec_cursor];
            (sol.binds.clone(), sol.start, sol.end)
        };
        self.rec_cursor += 1;
        for &(idx, b) in &binds {
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        self.prefix = self.subject[..start].to_vec();
        self.suffix = self.subject[end..].to_vec();
        self.matched_whole = self.prefix.is_empty() && self.suffix.is_empty();
        true
    }

    /// Enumerate every contiguous match (with extension if `ext_allowed`), binding aliens recursively
    /// and forcing non-linear repeats; var run-lengths ascending then a stable maximal-matched-first
    /// sort, so the lone variable absorbs the remainder and an alien binds to its leftmost position —
    /// the order Maude's greedy matcher fixes the reduce count by.
    fn enumerate_complex(&self, rt: &mut Runtime, sig: &Signature, base: &Subst) -> Vec<AuRecorded> {
        let n = self.subject.len();
        let last_start = if self.ext_allowed { n } else { 0 };
        let mut out = Vec::new();
        for start in 0..=last_start {
            let mut scratch = base.clone();
            self.rec_complex(0, start, start, rt, sig, &mut scratch, &mut out);
        }
        out.sort_by_key(|r| std::cmp::Reverse(r.end - r.start));
        out
    }

    /// Place `elements[elem_idx..]` against `subject[pos..]`: a ground matches one equal element, an
    /// alien one element recursively (its automaton), a fresh variable a run of each length, a repeated
    /// variable the (forced) run equal to its binding. Records a solution when all elements are placed.
    #[allow(clippy::too_many_arguments)]
    fn rec_complex(
        &self,
        elem_idx: usize,
        pos: usize,
        start: usize,
        rt: &mut Runtime,
        sig: &Signature,
        scratch: &mut Subst,
        out: &mut Vec<AuRecorded>,
    ) {
        let n = self.subject.len();
        if elem_idx == self.elements.len() {
            // Record when the residue rule allows it — and the matched span is non-empty: a zero-width
            // match (every variable bound to the identity, nothing consumed) is the identity no-op that
            // would rewrite a term to itself forever. Mirrors the ACU `matched > 0` skip; a ground/alien
            // always consumes ≥ 1, so this only ever drops the all-identity case.
            if (self.ext_allowed || pos == n) && pos > start {
                let binds = self
                    .all_var_indices
                    .iter()
                    .filter_map(|&i| scratch.get(i).map(|b| (i, b)))
                    .collect();
                out.push(AuRecorded { binds, start, end: pos });
            }
            return;
        }
        match &self.elements[elem_idx] {
            AuElem::Ground(g) => {
                if pos < n && rt.match_pattern(sig, g, self.subject[pos], scratch) {
                    self.rec_complex(elem_idx + 1, pos + 1, start, rt, sig, scratch, out);
                }
            }
            AuElem::Alien(t) => {
                if pos < n {
                    let automaton = LhsAutomaton::compile(t.clone(), sig);
                    let checkpoint = scratch.clone();
                    // An alien consumes one element — no extension on the sub-match.
                    if let Some(mut sp) = automaton.match_(rt, sig, self.subject[pos], scratch, false) {
                        while sp.next(rt, sig, scratch) {
                            self.rec_complex(elem_idx + 1, pos + 1, start, rt, sig, scratch, out);
                        }
                    }
                    *scratch = checkpoint;
                }
            }
            AuElem::Var { index, sort } => {
                let (index, sort) = (*index, *sort);
                if let Some(b) = scratch.get(index) {
                    // Repeated (non-linear) variable: the run is forced to equal the existing binding.
                    let blen = au_run_len(rt, b, self.symbol, self.identity);
                    if pos + blen <= n
                        && let Some(run) = build_run(rt, sig, self.symbol, self.identity, &self.subject[pos..pos + blen])
                        && rt.deep_equal(run, b)
                    {
                        self.rec_complex(elem_idx + 1, pos + blen, start, rt, sig, scratch, out);
                    }
                } else {
                    let min_len = usize::from(self.identity.is_none()); // ≥1 without identity, else ≥0
                    for len in min_len..=(n - pos) {
                        let Some(binding) =
                            build_run(rt, sig, self.symbol, self.identity, &self.subject[pos..pos + len])
                        else {
                            continue;
                        };
                        if !sig.sorts().leq(rt.sort_of(binding), sort) {
                            continue;
                        }
                        scratch.bind(index, binding);
                        self.rec_complex(elem_idx + 1, pos + len, start, rt, sig, scratch, out);
                        scratch.unbind(index);
                    }
                }
            }
        }
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

    /// C8: AU **alien** matching — `eq (s M) L = M L` peels successors off the head element. Reducing
    /// `(s s a) b c` takes **2** rewrites (the alien `s M` binds the head, the lone variable `L` collects
    /// the rest). Was a panic; the leftmost-alien/maximal-collector order is Maude's greedy order.
    #[test]
    fn au_alien_reduce() {
        use crate::term::Equation;
        let (mut e, s, a, b, c, nil, cat) = au_ctx();
        let succ = e.add_op("s", vec![s], s);
        // eq (s M) L = M L .   (M = var 0, L = var 1)
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::op(succ, vec![Term::var(0, s)]), Term::var(1, s)]),
            rhs: Term::op(cat, vec![Term::var(0, s), Term::var(1, s)]),
            nr_vars: 2,
        });
        let _ = nil;
        // (s s a) b c
        let ssa = {
            let a0 = e.make_const(a);
            let sa = e.make_free(succ, vec![a0]);
            e.make_free(succ, vec![sa])
        };
        let (b0, c0) = (e.make_const(b), e.make_const(c));
        let subject = e.make_au(cat, vec![ssa, b0, c0]);
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 2, "two successors peeled off the head");
        let (a1, b1, c1) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let abc = e.make_au(cat, vec![a1, b1, c1]);
        assert!(e.deep_equal(r, abc), "(s s a) b c = a b c");
    }

    /// C8: a **non-linear** AU variable — `eq X X = X` collapses an adjacent doubled run, so `a a a`
    /// reduces to `a` in **2** rewrites. The repeated `X` must re-match the identical run; was a panic.
    #[test]
    fn au_nonlinear_reduce() {
        use crate::term::Equation;
        let (mut e, s, a, _b, _c, _nil, cat) = au_ctx();
        // eq X X = X .
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::var(0, s), Term::var(0, s)]),
            rhs: Term::var(0, s),
            nr_vars: 1,
        });
        let (a0, a1, a2) = (e.make_const(a), e.make_const(a), e.make_const(a));
        let aaa = e.make_au(cat, vec![a0, a1, a2]);
        let r = e.reduce(aaa);
        assert_eq!(e.rewrites(), 2, "a a a -> a a -> a");
        let a3 = e.make_const(a);
        assert!(e.deep_equal(r, a3), "a a a = a");
    }
}
