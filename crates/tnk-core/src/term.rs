//! Patterns ([`Term`]), substitutions, equational matching, and instantiation for the free theory.
//!
//! A [`Term`] is the *static* pattern form used in equation/rule left- and right-hand sides — the
//! C++ `Term` (static) vs `DagNode` (runtime) duality. Phase 0 matching is a direct recursive
//! structural match over the free theory with sort-checked variable binding; the compiled
//! discrimination-net `LhsAutomaton` (A2) is a Phase-1 performance optimization.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::{SymbolId, Theory};

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

    /// True if this term contains no variables. The ACU compiler classifies pattern arguments into
    /// ground subterms (matched against an equal subject element), variables, and aliens.
    pub(crate) fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Op { args, .. } => args.iter().all(Term::is_ground),
        }
    }

    /// Whether the recursive free matcher [`Runtime::match_pattern`] can match this pattern: every
    /// `Op` in it — root and descendants — must be a **free-theory** operator. A theory-rooted
    /// (ACU/AU/CUI) `Op` is matched only by its own automaton; handed to `match_pattern` it returns a
    /// *silent* non-match on the theory subject (`match_pattern`'s `Op` arm yields `false` for any
    /// `Acu`/`Au`/`Cui` node). So a theory `Op` buried inside a free-matched (sub)pattern — a theory
    /// subterm under a free operator, or a theory-rooted *ground* subterm under a theory operator —
    /// would make its equation quietly never fire. Such patterns need the cross-theory `Sequence`
    /// composition (a B1 follow-up) and are rejected **loudly** at compile time until then, mirroring
    /// the alien-under-AC assert. Variables match any subject, so they are always fine.
    pub(crate) fn is_free_matchable(&self, sig: &Signature) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Op { symbol, args } => {
                sig.symbol(*symbol).theory() == Theory::Free
                    && args.iter().all(|a| a.is_free_matchable(sig))
            }
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

/// An (unconditional) membership axiom `mb lhs : sort` — asserts that any term matching `lhs` has
/// (at least) sort `sort`, refining its least sort *downward* (B2.2). `nr_vars` is the distinct-variable
/// count of `lhs`, as for [`Equation`]. Conditional membership (`cmb`) gains a condition in B2.3.
#[derive(Debug, Clone)]
pub struct Membership {
    pub lhs: Term,
    pub sort: SortId,
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
    /// Bind variable `index` to `id` (overwriting any previous binding).
    pub(crate) fn bind(&mut self, index: u32, id: DagId) {
        self.bindings[index as usize] = Some(id);
    }
    /// Clear variable `index`. A multi-solution matcher (ACU) unbinds the variables it set before
    /// computing the next solution, so a stale binding from a prior solution can't leak (F-4).
    pub(crate) fn unbind(&mut self, index: u32) {
        self.bindings[index as usize] = None;
    }
}

impl Runtime {
    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success. On failure
    /// `subst` may hold partial bindings, so callers reset before each attempt. Sort checks consult
    /// the (shared) signature; binding/equality walk the runtime's DAG arena — the A4 split.
    ///
    /// Recurses on *pattern* depth only (the `Op` arm descends `pat.args`; a `Var` binds without
    /// descending, and the non-linear case defers to the iterative [`Engine::deep_equal`]). Pattern
    /// depth is author-controlled and small for hand-written equations, so — unlike the old
    /// subject-depth recursion in `reduce` (A1) — this cannot overflow on deep runtime terms. A
    /// machine-generated equation with a pathologically deep lhs would still recurse; that path is
    /// superseded by A3's compiled, iterative `LhsAutomaton`.
    #[must_use]
    pub(crate) fn match_pattern(
        &self,
        sig: &Signature,
        pat: &Term,
        subject: DagId,
        subst: &mut Subst,
    ) -> bool {
        match pat {
            Term::Var(v) => match subst.get(v.index) {
                // Repeated (non-linear) variable: must bind to a structurally equal subterm.
                Some(bound) => self.deep_equal(bound, subject),
                // Fresh variable: bind iff the subject's sort fits the variable's sort.
                None => {
                    if sig.sorts().leq(self.sort_of(subject), v.sort) {
                        subst.bind(v.index, subject);
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
                            .all(|(p, &s)| self.match_pattern(sig, p, s, subst))
                }
                // The recursive free matcher never matches a theory subject: those are matched by
                // their own automata, and a free Op pattern's symbol differs from any theory symbol.
                // (A *variable* pattern still binds such a subject — that is the `Term::Var` arm.)
                NodeTerm::Acu { .. } | NodeTerm::Au { .. } | NodeTerm::Cui { .. } => false,
            },
        }
    }

    /// Structural equality of two DAG nodes (Phase 0 has no hash-consing, so this is a deep walk).
    ///
    /// Iterative (explicit pair-stack) for the same reason as [`Engine::reduce`]: the recursive form
    /// descended on *subject* depth and overflowed on deep terms (e.g. a non-linear pattern over a
    /// million-deep chain — review R2 C1).
    ///
    /// Compares top symbols and walks children through the [`DagNode::children`] visitor rather than
    /// matching a specific `NodeTerm` arm (review R3 H3): same-symbol + pairwise-equal-children is the
    /// free-theory equality. It also serves the canonically-ordered representations whose identity is
    /// fully carried by the child sequence (ACU, *provided* `children` yields the whole ordered
    /// multiset, repeats included). A theory whose node carries scalar payload that is *not* a child
    /// id — e.g. the S-theory's successor `count` — will need theory-specific equality here, exactly
    /// as matching stays per-theory ([`match_pattern`](Self::match_pattern) keeps its own `NodeTerm`
    /// arm).
    #[must_use]
    pub(crate) fn deep_equal(&self, a: DagId, b: DagId) -> bool {
        let mut stack: Vec<(DagId, DagId)> = vec![(a, b)];
        while let Some((x, y)) = stack.pop() {
            if x == y {
                continue; // same node (shared structure): trivially equal, prune the subtree
            }
            let (nx, ny) = (self.node(x), self.node(y));
            if nx.symbol() != ny.symbol() {
                return false;
            }
            // Enqueue children pairwise; a length mismatch (different arity) is inequality.
            let (mut cx, mut cy) = (nx.children(), ny.children());
            loop {
                match (cx.next(), cy.next()) {
                    (Some(cx), Some(cy)) => stack.push((cx, cy)),
                    (None, None) => break,
                    _ => return false,
                }
            }
        }
        true
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    ///
    /// Recurses on *rhs* depth only (author-controlled, small), so like [`Engine::match_pattern`] it
    /// is not exposed to the deep-subject overflow A1 fixed. Note its freshly built children live in
    /// the native-stack `arg_ids` local, so it must not be a GC safe point (see the `ReduceFrame`
    /// safe-point contract in `engine`). Allocates into the runtime's arena while the (shared)
    /// signature stays borrowed — the A4 split that lets a rewrite instantiate without cloning the rhs.
    pub(crate) fn instantiate(&mut self, sig: &Signature, term: &Term, subst: &Subst) -> DagId {
        match term {
            Term::Var(v) => subst.get(v.index).expect("unbound variable in instantiation"),
            Term::Op { symbol, args } => {
                let arg_ids: Vec<DagId> =
                    args.iter().map(|a| self.instantiate(sig, a, subst)).collect();
                // Dispatch on the operator's theory (an AC rhs builds a canonical multiset node, not a
                // free node) — `rebuild` rejects neither.
                self.rebuild(sig, *symbol, arg_ids)
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

    /// Two structurally-equal chains `g^200000(a)` with *distinct* node ids: the recursive
    /// `deep_equal` descended on subject depth and overflowed the stack on deep terms (review R2 C1,
    /// e.g. a non-linear pattern `h(X, X)` over deep arguments). The iterative pair-stack must not.
    #[test]
    fn deep_equal_iterative_on_deep_terms() {
        fn chain(e: &mut Engine, a: SymbolId, g: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(a);
            for _ in 0..n {
                acc = e.make_free(g, vec![acc]);
            }
            acc
        }
        let Ctx { mut e, a, g, .. } = ctx();
        let x = chain(&mut e, a, g, 200_000);
        let y = chain(&mut e, a, g, 200_000);
        assert_ne!(x, y, "distinct ids (no hash-consing)");
        assert!(e.deep_equal(x, y), "structurally equal deep chains compare equal");
    }
}
