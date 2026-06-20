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
//! Each argument sub-pattern is matched with the free recursive matcher
//! ([`Runtime::match_pattern`](crate::engine::Runtime)), which handles variables (including the
//! non-linear `f(X, X)` via structural equality) and ground/nested-free subterms; theory sub-patterns
//! under a CUI operator are a follow-up.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};

/// A compiled CUI left-hand side: the binary pattern `f(p1, p2)` plus the variable indices it binds.
pub(crate) struct CuiLhs {
    symbol: SymbolId,
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
    /// Size for the scratch substitution used while trying a pairing (max variable index + 1).
    local_size: u32,
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
            Term::Var(_) => unreachable!("compile is only called on an application lhs"),
        };
        let mut var_indices = Vec::new();
        collect_vars(&p1, &mut var_indices);
        collect_vars(&p2, &mut var_indices);
        let local_size = var_indices.iter().copied().max().map_or(0, |m| m + 1);
        CuiLhs { symbol, p1, p2, var_indices, local_size }
    }

    /// Match the binary pattern against a CUI subject of the same operator, enumerating the (deduped)
    /// commutative pairings. Reads only the runtime (no allocation — bindings are subject arguments).
    pub(crate) fn match_(&self, rt: &Runtime, sig: &Signature, subject: DagId) -> Option<CuiSubproblem> {
        let (s1, s2) = match &rt.node(subject).term {
            NodeTerm::Cui { symbol, args } if *symbol == self.symbol => (args[0], args[1]),
            _ => return None,
        };
        let mut solutions: Vec<Vec<(u32, DagId)>> = Vec::new();
        for (a, b) in [(s1, s2), (s2, s1)] {
            let mut local = Subst::new();
            local.reset(self.local_size);
            if rt.match_pattern(sig, &self.p1, a, &mut local)
                && rt.match_pattern(sig, &self.p2, b, &mut local)
            {
                let binding: Vec<(u32, DagId)> =
                    self.var_indices.iter().map(|&i| (i, local.get(i).expect("bound"))).collect();
                // The two pairings coincide for symmetric matches (e.g. `f(X, X) <=? f(a, a)`).
                if !solutions.contains(&binding) {
                    solutions.push(binding);
                }
            }
        }
        Some(CuiSubproblem { solutions, cursor: 0, bound: Vec::new() })
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
        Term::Op { args, .. } => {
            for a in args {
                collect_vars(a, out);
            }
        }
    }
}

/// A resumable enumerator over the (at most two) commutative pairings of a [`CuiLhs`]. Each solution
/// is a precomputed list of bindings; [`next`](CuiSubproblem::next) installs the next one.
pub(crate) struct CuiSubproblem {
    solutions: Vec<Vec<(u32, DagId)>>,
    cursor: usize,
    bound: Vec<u32>,
}

impl CuiSubproblem {
    /// Install the next pairing's bindings into `subst`; `false` when exhausted. No allocation (the
    /// bindings are subject arguments), so `rt`/`sig` are unused.
    pub(crate) fn next(&mut self, _rt: &mut Runtime, _sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();
        if self.cursor >= self.solutions.len() {
            return false;
        }
        for &(idx, b) in &self.solutions[self.cursor] {
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        self.cursor += 1;
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
