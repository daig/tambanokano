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
#[derive(Clone)]
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

    /// Match the binary pattern against a subject. Pairings are enumerated lazily in
    /// [`CuiSubproblem::next`] (each argument is matched through the full matcher seam, which needs
    /// `&mut Runtime` for a theory-rooted argument); this phase classifies the subject and builds the
    /// pairing list:
    /// - a CUI node of this operator: the whole-node pairings (both orders when `comm`), preceded —
    ///   when extension is allowed and the op has `id:` — by the **collapse-extension** pairings
    ///   (one pattern operand takes the identity, the other matches ONE argument, the remaining
    ///   argument is the residue: `eq a * X = c` on `a * b` gives `b * c`, oracle-verified;
    ///   identity-first ordering).
    /// - any other subject, for an op with `id:`/`idem`: the **collapse** arms (Maude's
    ///   id0/id1/idemCollapseMatch) — one operand vs the identity dag and the other vs the whole
    ///   subject (id), or both operands vs the subject (idem).
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        ext_allowed: bool,
    ) -> Option<CuiSubproblem> {
        let sym = sig.symbol(self.symbol);
        let comm = sym.axioms.comm;
        let idem = sym.axioms.idem;
        let identity = sym.identity;
        let mut pairings: Vec<Pairing> = Vec::new();
        match &rt.node(subject).term {
            NodeTerm::Cui { symbol, args } if *symbol == self.symbol => {
                let (s1, s2) = (args[0], args[1]);
                if ext_allowed && identity.is_some() {
                    // Identity-first: the collapse-extension options precede the whole matches.
                    pairings.push(Pairing { t1: Target::Dag(s1), t2: Target::Identity, residue: Some(s2) });
                    pairings.push(Pairing { t1: Target::Dag(s2), t2: Target::Identity, residue: Some(s1) });
                    pairings.push(Pairing { t1: Target::Identity, t2: Target::Dag(s1), residue: Some(s2) });
                    pairings.push(Pairing { t1: Target::Identity, t2: Target::Dag(s2), residue: Some(s1) });
                }
                pairings.push(Pairing { t1: Target::Dag(s1), t2: Target::Dag(s2), residue: None });
                if comm {
                    pairings.push(Pairing { t1: Target::Dag(s2), t2: Target::Dag(s1), residue: None });
                }
            }
            _ => {
                // Collapse arms against a non-`f` subject (whole matches, no residue).
                if identity.is_some() {
                    pairings.push(Pairing { t1: Target::Dag(subject), t2: Target::Identity, residue: None });
                    pairings.push(Pairing { t1: Target::Identity, t2: Target::Dag(subject), residue: None });
                }
                if idem {
                    pairings.push(Pairing { t1: Target::Dag(subject), t2: Target::Dag(subject), residue: None });
                }
                if pairings.is_empty() {
                    return None;
                }
            }
        }
        Some(CuiSubproblem {
            symbol: self.symbol,
            identity,
            p1: self.p1.clone(),
            p2: self.p2.clone(),
            var_indices: self.var_indices.clone(),
            pairings,
            solutions: None,
            cursor: 0,
            bound: Vec::new(),
            residue: None,
        })
    }
}

/// One pattern-operand target: a subject node, or the operator's (cached, already-reduced)
/// identity dag — resolved lazily in `next` (building/refreshing the dag needs `&mut Runtime`).
#[derive(Clone, Copy)]
enum Target {
    Dag(DagId),
    Identity,
}

/// One way of pairing the two pattern operands with targets, with an optional unmatched residue
/// argument (the CUI collapse-extension case).
struct Pairing {
    t1: Target,
    t2: Target,
    residue: Option<DagId>,
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
    symbol: SymbolId,
    identity: Option<SymbolId>,
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
    /// The pairing options, in match-preference order (identity/collapse first).
    pairings: Vec<Pairing>,
    /// Deduped pairing solutions (bindings + the pairing's residue); `None` until the first `next`.
    solutions: Option<Vec<(Vec<(u32, DagId)>, Option<DagId>)>>,
    cursor: usize,
    bound: Vec<u32>,
    /// The most recent solution's unmatched argument (collapse-extension), spliced by `build_result`.
    residue: Option<DagId>,
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
            // Resolve Identity targets to the cached (already-reduced) identity dag now that
            // `&mut Runtime` is available — the reduced stamp is refreshed here, which is what
            // makes a bare-variable rhs bound to it one-shot (see Runtime::identity_dag).
            let id_dag = self.identity.map(|id_sym| rt.identity_dag(sig, id_sym));
            let resolve = |t: Target| match t {
                Target::Dag(d) => d,
                Target::Identity => id_dag.expect("Identity target only built when id: present"),
            };
            let mut sols: Vec<(Vec<(u32, DagId)>, Option<DagId>)> = Vec::new();
            for p in &self.pairings {
                let (a, b) = (resolve(p.t1), resolve(p.t2));
                let aliens = [(self.p1.clone(), a), (self.p2.clone(), b)];
                for sol in enumerate_alien_solutions(rt, sig, subst, &aliens, &self.var_indices) {
                    // Distinct pairings can coincide for symmetric matches (`f(X, X) <=? f(a, a)`).
                    let entry = (sol, p.residue);
                    if !sols.contains(&entry) {
                        sols.push(entry);
                    }
                }
            }
            self.solutions = Some(sols);
        }
        let (binds, residue) = {
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
        self.residue = residue;
        true
    }

    /// A whole match is just the instantiated rhs; a collapse-extension match re-seats the rhs
    /// beside the unmatched argument (the CUI residue: `eq a * X = c` on `a * b` -> `b * c`).
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        match self.residue {
            Some(res) => rt.make_cui(sig, self.symbol, rhs, res),
            None => rhs,
        }
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
        let f = e.add_op_cui("f", vec![s, s], s, true, false, None);
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
