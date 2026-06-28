//! CUI matching: a matcher for `comm` (commutative, **not** associative; optionally `idem`/`id:`)
//! binary operators.
//!
//! A CUI node is binary, so matching `f(p1, p2)` against the canonical `f(s1, s2)` is just the two
//! commutative pairings — `(p1↦s1, p2↦s2)` and `(p1↦s2, p2↦s1)` — with no extension (the whole node
//! is matched). Idempotence and identity are handled by *construction* (`make_cui` collapses
//! `f(a,a)`/`f(a,e)` to a single element), so the subject of an in-reduction CUI match is always a
//! two-argument node; **collapse matching** of `f(X,Y)` against a non-`f` subject (the `match`-command
//! case `f(X,Y) <=? a`) is a follow-up.
//!
//! Each argument sub-pattern is matched through the full [`LhsAutomaton`](crate::theory) seam (via
//! [`enumerate_alien_solutions`](crate::theory::enumerate_alien_solutions)), so it may be a variable
//! (including the non-linear `f(X, X)`), a ground/free subterm, **or a theory-rooted subterm** — the two
//! arguments compose as a length-2 alien sequence, sharing the substitution. (Collapse matching of
//! `f(X, Y)` against a non-`f` subject — the `match`-command case `f(X,Y) <=? a` — is still a follow-up.)

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};
use crate::theory::enumerate_alien_solutions;

/// A compiled CUI left-hand side: the binary pattern `f(p1, p2)` plus the variable indices it binds.
pub(crate) struct CuiLhs {
    symbol: SymbolId,
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
}

impl CuiLhs {
    pub(crate) fn compile(lhs: Term, _sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("CUI lhs must be an application");
        let (p1, p2) = match lhs {
            Term::Op { args, .. } => {
                let mut args = args;
                assert_eq!(args.len(), 2, "a CUI pattern is binary");
                let p2 = args.pop().unwrap();
                let p1 = args.pop().unwrap();
                (p1, p2)
            }
            Term::Var(_) | Term::Na { .. } => {
                unreachable!("compile is only called on an application lhs")
            }
        };
        let mut var_indices = Vec::new();
        collect_vars(&p1, &mut var_indices);
        collect_vars(&p2, &mut var_indices);
        CuiLhs { symbol, p1, p2, var_indices }
    }

    /// Match the binary pattern against a CUI subject of the same operator. The two commutative pairings
    /// are enumerated lazily in [`CuiSubproblem::next`] (each argument is matched through the full
    /// matcher seam, which needs `&mut Runtime` for a theory-rooted argument); this phase only confirms
    /// the subject is a CUI node of this operator and captures its two arguments.
    pub(crate) fn match_(&self, rt: &Runtime, _sig: &Signature, subject: DagId) -> Option<CuiSubproblem> {
        let (s1, s2) = match &rt.node(subject).term {
            NodeTerm::Cui { symbol, args } if *symbol == self.symbol => (args[0], args[1]),
            _ => return None,
        };
        Some(CuiSubproblem {
            p1: self.p1.clone(),
            p2: self.p2.clone(),
            var_indices: self.var_indices.clone(),
            pairings: [(s1, s2), (s2, s1)],
            solutions: None,
            cursor: 0,
            bound: Vec::new(),
        })
    }
}

/// Collect the distinct variable indices of a (free) pattern term, in first-seen order.
fn collect_vars(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => {
            for a in args {
                collect_vars(a, out);
            }
        }
    }
}

/// A resumable enumerator over the (at most two, deduped) commutative pairings of a [`CuiLhs`]. The
/// pairings are enumerated lazily on the first [`next`](CuiSubproblem::next) — each argument is matched
/// through the full matcher seam, so a theory-rooted argument needs `&mut Runtime` — then replayed.
pub(crate) struct CuiSubproblem {
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
    pairings: [(DagId, DagId); 2],
    /// Deduped pairing solutions; `None` until the first `next` enumerates them.
    solutions: Option<Vec<Vec<(u32, DagId)>>>,
    cursor: usize,
    bound: Vec<u32>,
}

impl CuiSubproblem {
    /// Install the next pairing's bindings into `subst`; `false` when exhausted. On the first call,
    /// enumerate both commutative pairings — each as a length-2 alien sequence `[(p1, a), (p2, b)]` so
    /// theory-rooted arguments and non-linear variables compose correctly — deduping symmetric matches.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();
        if self.solutions.is_none() {
            let mut sols: Vec<Vec<(u32, DagId)>> = Vec::new();
            for (a, b) in self.pairings {
                let aliens = [(self.p1.clone(), a), (self.p2.clone(), b)];
                for sol in enumerate_alien_solutions(rt, sig, subst, &aliens, &self.var_indices) {
                    // The two pairings coincide for symmetric matches (`f(X, X) <=? f(a, a)`).
                    if !sols.contains(&sol) {
                        sols.push(sol);
                    }
                }
            }
            self.solutions = Some(sols);
        }
        let binds = {
            let sols = self.solutions.as_ref().expect("just enumerated");
            if self.cursor >= sols.len() {
                return false;
            }
            sols[self.cursor].clone()
        };
        self.cursor += 1;
        for &(idx, b) in &binds {
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        true
    }

    /// CUI matching is always a whole match (no extension), so the result is just the instantiated rhs.
    pub(crate) fn build_result(&self, _rt: &mut Runtime, _sig: &Signature, rhs: DagId) -> DagId {
        rhs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// `match f(X, Y) <=? f(a, b)` over `[comm]` — the two commutative pairings (== reference binary).
    #[test]
    fn cui_match_two_pairings() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, false, None);
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let subject = e.make_cui(f, a0, b0); // f(a, b)
        let pat = Term::op(f, vec![Term::var(0, s), Term::var(1, s)]);

        let lhs = CuiLhs::compile(pat, e.signature());
        let mut subst = Subst::new();
        subst.reset(2);
        let (sig, rt) = e.parts_mut();
        let mut sp = lhs.match_(rt, sig, subject).expect("f(X,Y) matches f(a,b)");
        let mut got: Vec<(Option<DagId>, Option<DagId>)> = Vec::new();
        while sp.next(rt, sig, &mut subst) {
            got.push((subst.get(0), subst.get(1)));
        }
        // Decode to symbol-name pairs.
        let mut names: Vec<(String, String)> = got
            .iter()
            .map(|&(x, y)| {
                let nm = |id: DagId| e.symbol(e.node(id).symbol()).name().to_string();
                (nm(x.unwrap()), nm(y.unwrap()))
            })
            .collect();
        names.sort();
        assert_eq!(
            names,
            vec![("a".into(), "b".into()), ("b".into(), "a".into())],
            "two pairings: X=a/Y=b and X=b/Y=a"
        );
    }
}
