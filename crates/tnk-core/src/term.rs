//! Patterns ([`Term`]), substitutions, equational matching, and instantiation for the free theory.
//!
//! A [`Term`] is the *static* pattern form used in equation/rule left- and right-hand sides — the
//! C++ `Term` (static) vs `DagNode` (runtime) duality. Phase 0 matching is a direct recursive
//! structural match over the free theory with sort-checked variable binding; the compiled
//! discrimination-net `LhsAutomaton` (A2) is a Phase-1 performance optimization.

use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::sort::SortId;
use crate::symbol::SymbolId;

/// A pattern variable: an index into the enclosing statement's substitution, plus its sort.
#[derive(Debug, Clone)]
pub struct Var {
    pub index: u32,
    pub sort: SortId,
}

/// A static term / pattern.
#[derive(Debug, Clone)]
pub enum Term {
    Var(Var),
    Op { symbol: SymbolId, args: Vec<Term> },
}

impl Term {
    pub fn var(index: u32, sort: SortId) -> Self {
        Term::Var(Var { index, sort })
    }
    pub fn op(symbol: SymbolId, args: Vec<Term>) -> Self {
        Term::Op { symbol, args }
    }
    pub fn constant(symbol: SymbolId) -> Self {
        Term::Op { symbol, args: Vec::new() }
    }

    /// Top symbol, if this is an application (used to index equations by their lhs head).
    pub fn top_symbol(&self) -> Option<SymbolId> {
        match self {
            Term::Op { symbol, .. } => Some(*symbol),
            Term::Var(_) => None,
        }
    }
}

/// An unconditional (Phase-0) equation `lhs = rhs` with `nr_vars` distinct variables.
#[derive(Debug, Clone)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
    pub nr_vars: u32,
}

/// A substitution: variable index → bound DAG node. Reused across match attempts via [`reset`].
///
/// [`reset`]: Subst::reset
#[derive(Debug, Default)]
pub struct Subst {
    bindings: Vec<Option<DagId>>,
}

impl Subst {
    pub fn new() -> Self {
        Self::default()
    }
    /// Clear all bindings and size for `nr_vars` variables.
    pub fn reset(&mut self, nr_vars: u32) {
        self.bindings.clear();
        self.bindings.resize(nr_vars as usize, None);
    }
    pub fn get(&self, index: u32) -> Option<DagId> {
        self.bindings[index as usize]
    }
    fn set(&mut self, index: u32, id: DagId) {
        self.bindings[index as usize] = Some(id);
    }
}

impl Engine {
    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success. On failure
    /// `subst` may hold partial bindings, so callers reset before each attempt.
    pub fn match_pattern(&self, pat: &Term, subject: DagId, subst: &mut Subst) -> bool {
        match pat {
            Term::Var(v) => match subst.get(v.index) {
                // Repeated (non-linear) variable: must bind to a structurally equal subterm.
                Some(bound) => self.deep_equal(bound, subject),
                // Fresh variable: bind iff the subject's sort fits the variable's sort.
                None => {
                    if self.sorts().leq(self.sort_of(subject), v.sort) {
                        subst.set(v.index, subject);
                        true
                    } else {
                        false
                    }
                }
            },
            Term::Op { symbol, args } => match &self.node(subject).term {
                NodeTerm::Free { symbol: ssym, args: sargs } => {
                    *ssym == *symbol
                        && sargs.len() == args.len()
                        && args
                            .iter()
                            .zip(sargs.iter())
                            .all(|(p, &s)| self.match_pattern(p, s, subst))
                }
            },
        }
    }

    /// Structural equality of two DAG nodes (Phase 0 has no hash-consing, so this is a deep walk).
    pub fn deep_equal(&self, a: DagId, b: DagId) -> bool {
        if a == b {
            return true;
        }
        match (&self.node(a).term, &self.node(b).term) {
            (
                NodeTerm::Free { symbol: sa, args: aa },
                NodeTerm::Free { symbol: sb, args: bb },
            ) => {
                sa == sb
                    && aa.len() == bb.len()
                    && aa.iter().zip(bb).all(|(&x, &y)| self.deep_equal(x, y))
            }
        }
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    pub fn instantiate(&mut self, term: &Term, subst: &Subst) -> DagId {
        match term {
            Term::Var(v) => subst.get(v.index).expect("unbound variable in instantiation"),
            Term::Op { symbol, args } => {
                let arg_ids: Vec<DagId> = args.iter().map(|a| self.instantiate(a, subst)).collect();
                self.make_free(*symbol, arg_ids)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    struct Ctx {
        e: Engine,
        nat: SortId,
        a: SymbolId,
        b: SymbolId,
        f: SymbolId,
        g: SymbolId,
    }

    fn ctx() -> Ctx {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let g = e.add_op("g", vec![nat], nat);
        Ctx { e, nat, a, b, f, g }
    }

    #[test]
    fn binds_variable() {
        let Ctx { mut e, nat, a, b, f, .. } = ctx();
        let b0 = e.make_const(b);
        let a0 = e.make_const(a);
        let subject = e.make_free(f, vec![b0, a0]); // f(b, a)
        let pat = Term::op(f, vec![Term::var(0, nat), Term::constant(a)]); // f(X, a)

        let mut s = Subst::new();
        s.reset(1);
        assert!(e.match_pattern(&pat, subject, &mut s));
        assert_eq!(s.get(0), Some(b0));
    }

    #[test]
    fn fails_on_symbol_mismatch() {
        let Ctx { mut e, nat, a, b, f, .. } = ctx();
        let b0 = e.make_const(b);
        let b1 = e.make_const(b);
        let subject = e.make_free(f, vec![b0, b1]); // f(b, b)
        let pat = Term::op(f, vec![Term::var(0, nat), Term::constant(a)]); // f(X, a)

        let mut s = Subst::new();
        s.reset(1);
        assert!(!e.match_pattern(&pat, subject, &mut s));
    }

    #[test]
    fn nonlinear_pattern() {
        let Ctx { mut e, nat, a, b, f, .. } = ctx();
        let pat = Term::op(f, vec![Term::var(0, nat), Term::var(0, nat)]); // f(X, X)

        let a0 = e.make_const(a);
        let a1 = e.make_const(a);
        let faa = e.make_free(f, vec![a0, a1]); // f(a, a) — distinct ids, structurally equal
        let mut s = Subst::new();
        s.reset(1);
        assert!(e.match_pattern(&pat, faa, &mut s));

        let a2 = e.make_const(a);
        let b0 = e.make_const(b);
        let fab = e.make_free(f, vec![a2, b0]); // f(a, b)
        s.reset(1);
        assert!(!e.match_pattern(&pat, fab, &mut s));
    }

    #[test]
    fn instantiate_builds_dag() {
        let Ctx { mut e, nat, b, g, .. } = ctx();
        let b0 = e.make_const(b);
        let mut s = Subst::new();
        s.reset(1);
        assert!(e.match_pattern(&Term::var(0, nat), b0, &mut s)); // bind X = b

        let built = e.instantiate(&Term::op(g, vec![Term::var(0, nat)]), &s); // g(X) -> g(b)
        let b1 = e.make_const(b);
        let expected = e.make_free(g, vec![b1]);
        assert!(e.deep_equal(built, expected));
    }

    #[test]
    fn variable_sort_is_checked() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let z0 = e.make_const(z); // sort Zero

        let mut s = Subst::new();
        s.reset(1);
        assert!(!e.match_pattern(&Term::var(0, nznat), z0, &mut s), "Zero is not <= NzNat");
        s.reset(1);
        assert!(e.match_pattern(&Term::var(0, nat), z0, &mut s), "Zero <= Nat");
    }
}
