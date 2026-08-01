//! Static terms, substitutions, matching, and instantiation.
//!
//! A [`Term`] is the static form used in equation and rule sides, distinct from the runtime
//! [`DagNode`](crate::dag::DagNode). Matching dispatches through the crate-private `LhsAutomaton`:
//! all-free patterns use direct structural matching, while theory-rooted and cross-theory patterns use
//! their compiled, resumable automata.

use crate::dag::{DagId, NaValue, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num::Nat;
use crate::smt::SmtNumber;
use crate::sort::SortId;
use crate::symbol::{SymbolId, Theory};
use std::collections::HashMap;
use std::rc::Rc;

/// A pattern variable: its substitution index and sort.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    pub index: u32,
    pub sort: SortId,
}

enum InstantiatedBase<'a> {
    Term(&'a Term),
    Dag(DagId),
}

/// A static term or pattern. Structural equality and hashing let the engine detect repeated rhs
/// subterms and enable construction deduplication only when useful.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Var(Var),
    Op {
        symbol: SymbolId,
        args: Vec<Term>,
    },
    /// A compact static S-theory application `symbol^count(arg)`. `count` is scalar bignum data, not
    /// `count` nested unary [`Term::Op`] allocations. The constructor canonicalizes zero and adjacent
    /// runs of the same symbol.
    Iter {
        symbol: SymbolId,
        count: Nat,
        arg: Box<Term>,
    },
    /// A built-in atomic literal: a string, quoted identifier, float, or SMT number. `symbol` is its
    /// pseudo-constructor and `value` distinguishes constants that share that symbol. It is a ground
    /// leaf and matches only a subject with the same symbol and value.
    Na {
        symbol: SymbolId,
        value: NaValue,
    },
}

impl Term {
    pub fn var(index: u32, sort: SortId) -> Self {
        Term::Var(Var { index, sort })
    }
    pub fn op(symbol: SymbolId, args: Vec<Term>) -> Self {
        Term::Op { symbol, args }
    }
    pub fn constant(symbol: SymbolId) -> Self {
        Term::Op {
            symbol,
            args: Vec::new(),
        }
    }
    /// Build a compact iterated S-theory application. A zero count is the argument itself; adjacent
    /// iterations of the same symbol are folded (`s^j(s^k(x)) = s^(j+k)(x)`).
    pub fn iter(symbol: SymbolId, mut count: Nat, mut arg: Term) -> Self {
        if count.is_zero() {
            return arg;
        }
        loop {
            match arg {
                Term::Iter {
                    symbol: inner,
                    count: inner_count,
                    arg: inner_arg,
                } if inner == symbol => {
                    count = count.add(&inner_count);
                    arg = *inner_arg;
                }
                Term::Op {
                    symbol: inner,
                    mut args,
                } if inner == symbol && args.len() == 1 => {
                    count = count.add(&Nat::one());
                    arg = args.pop().unwrap();
                }
                arg => {
                    return Term::Iter {
                        symbol,
                        count,
                        arg: Box::new(arg),
                    };
                }
            }
        }
    }

    /// Parse an arbitrary-size decimal count and build [`Term::iter`]. Returns `None` for malformed
    /// input so callers can produce the appropriate parse diagnostic.
    pub fn iter_decimal(symbol: SymbolId, count: &str, arg: Term) -> Option<Self> {
        Some(Self::iter(symbol, Nat::from_decimal(count)?, arg))
    }
    /// A float literal (`<Floats>`), stored as IEEE bits like [`NaValue::Float`].
    pub fn float(symbol: SymbolId, value: f64) -> Self {
        // Normalize -0.0 exactly as the DAG constructor does.
        let value = if value == 0.0 { 0.0 } else { value };
        Term::Na {
            symbol,
            value: NaValue::Float(value.to_bits()),
        }
    }
    /// A string literal (`<Strings>`) stored as raw bytes rather than UTF-8 text.
    pub fn string(symbol: SymbolId, value: &[u8]) -> Self {
        Term::Na {
            symbol,
            value: NaValue::Str(Rc::from(value)),
        }
    }
    /// A quoted-identifier literal (`<Qids>`), stored without the leading quote.
    pub fn qid(symbol: SymbolId, value: &str) -> Self {
        Term::Na {
            symbol,
            value: NaValue::Qid(Rc::from(value)),
        }
    }
    /// An exact SMT integer/rational literal.
    pub fn smt_number(symbol: SymbolId, value: SmtNumber) -> Self {
        Term::Na {
            symbol,
            value: NaValue::SmtNum(Rc::new(value)),
        }
    }

    /// Top symbol, if this is an application or a built-in literal (used to index equations by their lhs
    /// head — an `Na` literal heads on its pseudo-constructor symbol).
    pub fn top_symbol(&self) -> Option<SymbolId> {
        match self {
            Term::Op { symbol, .. } | Term::Iter { symbol, .. } | Term::Na { symbol, .. } => {
                Some(*symbol)
            }
            Term::Var(_) => None,
        }
    }

    /// True if this term contains no variables. The ACU compiler classifies pattern arguments into
    /// ground subterms (matched against an equal subject element), variables, and aliens. A literal is
    /// ground.
    pub(crate) fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Na { .. } => true,
            Term::Op { args, .. } => args.iter().all(Term::is_ground),
            Term::Iter { arg, .. } => arg.is_ground(),
        }
    }

    /// Whether this pattern can use the deterministic all-free matcher. A theory-rooted operator anywhere
    /// in the tree returns `false`, causing [`LhsAutomaton`](crate::theory::LhsAutomaton) to route the
    /// pattern through a per-theory or free-with-aliens automaton instead. Variables and atomic literals
    /// are valid leaves on the all-free path.
    pub(crate) fn is_free_matchable(&self, sig: &Signature) -> bool {
        match self {
            Term::Var(_) => true,
            // A built-in literal is a leaf matched only by an equal literal subject (the free matcher's
            // `Na` arm handles it) — like a free constant, it is free-matchable.
            Term::Na { .. } => true,
            // An Iter is rooted in the S theory, so the free matcher must route it through the
            // theory-automaton/alien seam rather than recursively treating it as a free application.
            Term::Iter { .. } => false,
            Term::Op { symbol, args } => {
                sig.symbol(*symbol).theory() == Theory::Free
                    && args.iter().all(|a| a.is_free_matchable(sig))
            }
        }
    }
}

/// An unconditional equation `lhs = rhs` with `nr_vars` distinct variables.
#[derive(Debug, Clone)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
    pub nr_vars: u32,
}

/// An unconditional membership axiom that refines matching terms to `sort`.
/// `nr_vars` is the number of distinct variables in `lhs`.
#[derive(Debug, Clone)]
pub struct Membership {
    pub lhs: Term,
    pub sort: SortId,
    pub nr_vars: u32,
}

/// One fragment of a conditional statement's condition (`ceq`/`cmb`/`crl` ... `if` ...). The fragments
/// are a conjunction evaluated left-to-right; a failure backtracks into the previous fragment's next
/// solution (and ultimately into the next matcher solution of the statement). Closed set.
#[derive(Debug, Clone)]
pub enum ConditionFragment {
    /// `lhs = rhs` — holds iff both sides, instantiated under the match and reduced, are equal modulo
    /// the axioms. Introduces no new variables.
    Equality { lhs: Term, rhs: Term },
    /// `term : sort` — holds iff `term`, instantiated and reduced, has a least sort `<= sort`.
    SortTest { term: Term, sort: SortId },
    /// `pattern := subject` — holds iff `pattern` matches `subject` (instantiated and reduced), binding
    /// the **fresh** variables `fresh_vars` (the indices the pattern introduces). A multi-solution
    /// match backtracks: a later fragment's failure retries the next match. The pattern's non-fresh
    /// variables are checked (non-linearly) against their existing bindings.
    Matching {
        pattern: Term,
        subject: Term,
        fresh_vars: Vec<u32>,
    },
    /// `lhs => pattern` — a rewrite condition legal only in a rule `crl`: holds when an instance of
    /// `lhs` reaches a state matching `pattern`, binding its fresh variables. Reachable states are
    /// breadth-first, a later-fragment failure resumes with the next state, and every rule step counts
    /// as a rewrite.
    Rewrite {
        lhs: Term,
        pattern: Term,
        fresh_vars: Vec<u32>,
    },
}

/// A substitution from variable index to bound DAG node, reused across match attempts via [`reset`].
///
/// [`reset`]: Subst::reset
///
/// Cross-theory matchers clone the substitution to checkpoint speculative alien matches, then restore
/// the clone on backtracking. The flat `Vec<Option<DagId>>` representation makes each checkpoint one
/// contiguous binding-array copy.
#[derive(Debug, Default, Clone)]
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
    /// The number of variable slots (`nr_vars` of the statement this substitution was [`reset`] for).
    /// Used to snapshot the whole substitution for a trace event without threading `nr_vars` separately.
    ///
    /// [`reset`]: Subst::reset
    pub(crate) fn len(&self) -> u32 {
        self.bindings.len() as u32
    }
    /// Bind variable `index` to `id` (overwriting any previous binding).
    pub(crate) fn bind(&mut self, index: u32, id: DagId) {
        self.bindings[index as usize] = Some(id);
    }
    /// Clear variable `index`. A multi-solution matcher (ACU) unbinds the variables it set before
    /// computing the next solution, so a binding from the prior solution cannot leak.
    pub(crate) fn unbind(&mut self, index: u32) {
        self.bindings[index as usize] = None;
    }
}

impl Runtime {
    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success. On failure
    /// `subst` may hold partial bindings, so callers reset before each attempt. Sort checks consult
    /// the (shared) signature; binding/equality walk the runtime's DAG arena.
    ///
    /// Recurses on *pattern* depth only: the `Op` arm descends through `pat.args`, a `Var` binds
    /// directly, and non-linear equality uses iterative [`Engine::deep_equal`]. Subject depth
    /// therefore does not consume call-stack space. A pathologically deep generated pattern can
    /// still exhaust the native stack.
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
            // A literal pattern matches an identical literal subject (same pseudo-constructor + value).
            Term::Na { symbol, value } => match &self.node(subject).term {
                NodeTerm::Na {
                    symbol: ssym,
                    value: sval,
                } => *ssym == *symbol && *sval == *value,
                _ => false,
            },
            Term::Op { symbol, args } => match &self.node(subject).term {
                NodeTerm::Free {
                    symbol: ssym,
                    args: sargs,
                } => {
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
                // A `Var` leaf only occurs in symbolic-engine DAGs, which are never match subjects.
                NodeTerm::Acu { .. }
                | NodeTerm::Au { .. }
                | NodeTerm::Cui { .. }
                | NodeTerm::S { .. }
                | NodeTerm::Na { .. }
                | NodeTerm::Var { .. } => false,
            },
            // An Iter pattern is S-theory rooted and is handled by `SLhs`, never the recursive free
            // matcher. A variable can still bind an S subject in the `Var` arm above.
            Term::Iter { .. } => false,
        }
    }

    /// Match a free-rooted pattern while collecting theory-rooted child patterns for separate,
    /// resumable matching. The free skeleton binds deterministically; the collected pairs compose into
    /// a [`Subproblem::Sequence`].
    pub(crate) fn match_skeleton(
        &self,
        sig: &Signature,
        pat: &Term,
        subject: DagId,
        subst: &mut Subst,
        aliens: &mut Vec<(Term, DagId)>,
    ) -> bool {
        match pat {
            Term::Var(v) => match subst.get(v.index) {
                Some(bound) => self.deep_equal(bound, subject),
                None => {
                    if sig.sorts().leq(self.sort_of(subject), v.sort) {
                        subst.bind(v.index, subject);
                        true
                    } else {
                        false
                    }
                }
            },
            // A literal pattern matches an identical literal subject (a ground leaf, never an alien).
            Term::Na { symbol, value } => match &self.node(subject).term {
                NodeTerm::Na {
                    symbol: ssym,
                    value: sval,
                } => *ssym == *symbol && *sval == *value,
                _ => false,
            },
            // A theory-rooted sub-pattern is an alien: record it (with its subject subterm) for the
            // Sequence to match recursively; the recursive free matcher can't enumerate its solutions.
            Term::Op { symbol, .. } if sig.symbol(*symbol).theory() != Theory::Free => {
                aliens.push((pat.clone(), subject));
                true
            }
            Term::Iter { .. } => {
                aliens.push((pat.clone(), subject));
                true
            }
            Term::Op { symbol, args } => match &self.node(subject).term {
                NodeTerm::Free {
                    symbol: ssym,
                    args: sargs,
                } => {
                    *ssym == *symbol
                        && sargs.len() == args.len()
                        && args
                            .iter()
                            .zip(sargs.iter())
                            .all(|(p, &s)| self.match_skeleton(sig, p, s, subst, aliens))
                }
                NodeTerm::Acu { .. }
                | NodeTerm::Au { .. }
                | NodeTerm::Cui { .. }
                | NodeTerm::S { .. }
                | NodeTerm::Na { .. }
                | NodeTerm::Var { .. } => false,
            },
        }
    }

    /// Structural equality of two DAG nodes.
    ///
    /// Iterative (explicit pair stack) so a deeply nested runtime term cannot overflow the call stack.
    /// Canonical theory nodes compare through their ordered child stream; representations with scalar
    /// identity, such as an iterated successor's count, are checked explicitly below.
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
            // The S successor's `count` is scalar identity, not a child: compare it explicitly, else
            // `s^2(0)` and `s^3(0)` — both `[arg]` under the generic child walk — would compare equal.
            // Equal symbols ⇒ same theory ⇒ both are the S arm; recurse on the argument.
            if let (
                NodeTerm::S {
                    count: cx, arg: ax, ..
                },
                NodeTerm::S {
                    count: cy, arg: ay, ..
                },
            ) = (&nx.term, &ny.term)
            {
                if cx != cy {
                    return false;
                }
                stack.push((*ax, *ay));
                continue;
            }
            // An NA constant's `value` is scalar identity, not a child: equal symbols are equal iff the
            // values are (same shape — equal symbols ⇒ both the Na arm). A leaf — `continue` on equal
            // (process the rest of the pair-stack), fail on unequal.
            if let (NodeTerm::Na { value: vx, .. }, NodeTerm::Na { value: vy, .. }) =
                (&nx.term, &ny.term)
            {
                if vx != vy {
                    return false;
                }
                continue;
            }
            // Variable leaves compare by symbol (checked above) and name-token code. Their substitution
            // `index` is bookkeeping and does not participate in identity.
            if let (NodeTerm::Var { name: vx, .. }, NodeTerm::Var { name: vy, .. }) =
                (&nx.term, &ny.term)
            {
                if vx != vy {
                    return false;
                }
                continue;
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

    /// Resolve candidate terms to exact, already-reduced sub-DAGs of the matched equation subject.
    /// Only nodes stamped with the current equation epoch are reusable; reusing an unreduced lhs
    /// occurrence in an eager rhs position would incorrectly skip its reduction.
    pub(crate) fn find_reduced_instances<'t>(
        &self,
        sig: &Signature,
        subject: DagId,
        terms: &'t [Term],
        subst: &Subst,
    ) -> Vec<(&'t Term, DagId)> {
        let mut found = Vec::with_capacity(terms.len());
        for term in terms {
            let mut stack = vec![subject];
            while let Some(id) = stack.pop() {
                let node = self.node(id);
                let current = if node.reduced_epoch == sig.eq_epoch() {
                    node.nf.unwrap_or(id)
                } else {
                    id
                };
                let current_node = self.node(current);
                if current_node.reduced_epoch == sig.eq_epoch()
                    && self.instantiated_term_equal(term, current, subst)
                {
                    found.push((term, current));
                    break;
                }
                stack.extend(current_node.children());
            }
        }
        found
    }

    fn instantiated_term_equal(&self, term: &Term, dag: DagId, subst: &Subst) -> bool {
        if let NodeTerm::S { symbol, count, arg } = &self.node(dag).term {
            let (instance_count, base) = self.instantiated_s_parts(term, *symbol, subst);
            return instance_count == *count
                && match base {
                    InstantiatedBase::Term(base) => self.instantiated_term_equal(base, *arg, subst),
                    InstantiatedBase::Dag(base) => self.deep_equal(base, *arg),
                };
        }

        match term {
            Term::Var(v) => subst
                .get(v.index)
                .is_some_and(|binding| self.deep_equal(binding, dag)),
            Term::Na { symbol, value } => {
                matches!(&self.node(dag).term,
                    NodeTerm::Na { symbol: actual, value: actual_value }
                        if actual == symbol && actual_value == value)
            }
            Term::Iter { .. } => false,
            Term::Op { symbol, args } => {
                let node = self.node(dag);
                if node.symbol() != *symbol
                    || matches!(node.term, NodeTerm::Na { .. } | NodeTerm::Var { .. })
                {
                    return false;
                }
                let mut children = node.children();
                for arg in args {
                    let Some(child) = children.next() else {
                        return false;
                    };
                    if !self.instantiated_term_equal(arg, child, subst) {
                        return false;
                    }
                }
                children.next().is_none()
            }
        }
    }

    fn instantiated_s_parts<'t>(
        &self,
        mut term: &'t Term,
        symbol: SymbolId,
        subst: &Subst,
    ) -> (Nat, InstantiatedBase<'t>) {
        let mut count = Nat::zero();
        loop {
            match term {
                Term::Op {
                    symbol: current,
                    args,
                } if *current == symbol && args.len() == 1 => {
                    count = count.add(&Nat::one());
                    term = &args[0];
                }
                Term::Iter {
                    symbol: current,
                    count: current_count,
                    arg,
                } if *current == symbol => {
                    count = count.add(current_count);
                    term = arg;
                }
                Term::Var(var) => {
                    let mut dag = subst
                        .get(var.index)
                        .expect("bound lhs variable missing during rhs sharing");
                    loop {
                        match &self.node(dag).term {
                            NodeTerm::S {
                                symbol: current,
                                count: current_count,
                                arg,
                            } if *current == symbol => {
                                count = count.add(current_count);
                                dag = *arg;
                            }
                            _ => return (count, InstantiatedBase::Dag(dag)),
                        }
                    }
                }
                _ => return (count, InstantiatedBase::Term(term)),
            }
        }
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    ///
    /// Recurses on *rhs* depth only, independent of matched-subject depth. Freshly built children live
    /// only in the native-stack `arg_ids` local until their parent is allocated, so this function must
    /// not cross a GC safe point during that interval. It allocates in the runtime arena while the
    /// shared signature remains borrowed, avoiding an rhs clone during rewriting.
    pub(crate) fn instantiate(&mut self, sig: &Signature, term: &Term, subst: &Subst) -> DagId {
        match term {
            Term::Var(v) => subst
                .get(v.index)
                .expect("unbound variable in instantiation"),
            Term::Na { symbol, value } => self.make_na(sig, *symbol, value.clone()),
            Term::Iter { symbol, count, arg } => {
                let arg = self.instantiate(sig, arg, subst);
                self.make_s(sig, *symbol, count.clone(), arg)
            }
            Term::Op { symbol, args } => {
                let arg_ids: Vec<DagId> = args
                    .iter()
                    .map(|a| self.instantiate(sig, a, subst))
                    .collect();
                // Dispatch on the operator's theory (an AC rhs builds a canonical multiset node, not a
                // free node) — `rebuild` rejects neither.
                self.rebuild(sig, *symbol, arg_ids)
            }
        }
    }

    /// Instantiate an rhs while replacing exact terms listed in `reuse` with their saved,
    /// already-reduced lhs DAGs.
    pub(crate) fn instantiate_reusing(
        &mut self,
        sig: &Signature,
        term: &Term,
        subst: &Subst,
        reuse: &[(&Term, DagId)],
    ) -> DagId {
        if let Some((_, dag)) = reuse.iter().find(|(candidate, _)| *candidate == term) {
            return *dag;
        }
        match term {
            Term::Var(v) => subst
                .get(v.index)
                .expect("unbound variable in instantiation"),
            Term::Na { symbol, value } => self.make_na(sig, *symbol, value.clone()),
            Term::Iter { symbol, count, arg } => {
                let arg = self.instantiate_reusing(sig, arg, subst, reuse);
                self.make_s(sig, *symbol, count.clone(), arg)
            }
            Term::Op { symbol, args } => {
                let arg_ids = args
                    .iter()
                    .map(|arg| self.instantiate_reusing(sig, arg, subst, reuse))
                    .collect();
                self.rebuild(sig, *symbol, arg_ids)
            }
        }
    }

    /// Instantiate an rhs with syntax-keyed common-subexpression reuse. Each syntactically repeated
    /// compound subterm is built once and shared, so reducing that shared instance increments the
    /// rewrite count once. Distinct rhs subterms remain separate even when substitution gives them
    /// equal values, preserving one reduction count per distinct occurrence.
    pub(crate) fn instantiate_cse(&mut self, sig: &Signature, term: &Term, subst: &Subst) -> DagId {
        self.instantiate_cse_with_reuse(sig, term, subst, &[])
    }

    pub(crate) fn instantiate_cse_reusing(
        &mut self,
        sig: &Signature,
        term: &Term,
        subst: &Subst,
        reuse: &[(&Term, DagId)],
    ) -> DagId {
        self.instantiate_cse_with_reuse(sig, term, subst, reuse)
    }

    fn instantiate_cse_with_reuse(
        &mut self,
        sig: &Signature,
        term: &Term,
        subst: &Subst,
        reuse: &[(&Term, DagId)],
    ) -> DagId {
        let mut counts: HashMap<&Term, u32> = HashMap::new();
        let mut stack = vec![term];
        while let Some(cur) = stack.pop() {
            match cur {
                Term::Op { args, .. } => {
                    let n = counts.entry(cur).or_insert(0);
                    *n += 1;
                    if *n == 1 {
                        stack.extend(args.iter());
                    }
                }
                Term::Iter { arg, .. } => {
                    let n = counts.entry(cur).or_insert(0);
                    *n += 1;
                    if *n == 1 {
                        stack.push(arg);
                    }
                }
                Term::Var(_) | Term::Na { .. } => {}
            }
        }
        let repeated: Vec<&Term> = counts
            .iter()
            .filter(|&(_, &n)| n > 1)
            .map(|(&t, _)| t)
            .collect();
        let mut memo: Vec<(&Term, DagId)> = Vec::new();
        self.instantiate_cse_rec(sig, term, subst, &repeated, &mut memo, reuse)
    }

    fn instantiate_cse_rec<'t>(
        &mut self,
        sig: &Signature,
        term: &'t Term,
        subst: &Subst,
        repeated: &[&'t Term],
        memo: &mut Vec<(&'t Term, DagId)>,
        reuse: &[(&Term, DagId)],
    ) -> DagId {
        if let Some((_, dag)) = reuse.iter().find(|(candidate, _)| *candidate == term) {
            return *dag;
        }
        let shared =
            matches!(term, Term::Op { .. } | Term::Iter { .. }) && repeated.contains(&term);
        if shared && let Some(&(_, d)) = memo.iter().find(|(k, _)| *k == term) {
            return d;
        }
        let d = match term {
            Term::Var(v) => subst
                .get(v.index)
                .expect("unbound variable in instantiation"),
            Term::Na { symbol, value } => self.make_na(sig, *symbol, value.clone()),
            Term::Iter { symbol, count, arg } => {
                let arg = self.instantiate_cse_rec(sig, arg, subst, repeated, memo, reuse);
                self.make_s(sig, *symbol, count.clone(), arg)
            }
            Term::Op { symbol, args } => {
                let arg_ids: Vec<DagId> = args
                    .iter()
                    .map(|a| self.instantiate_cse_rec(sig, a, subst, repeated, memo, reuse))
                    .collect();
                self.rebuild(sig, *symbol, arg_ids)
            }
        };
        if shared {
            memo.push((term, d));
        }
        d
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
        let Ctx {
            mut e,
            nat,
            a,
            b,
            f,
            ..
        } = ctx();
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
        let Ctx {
            mut e,
            nat,
            a,
            b,
            f,
            ..
        } = ctx();
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
        let Ctx {
            mut e,
            nat,
            a,
            b,
            f,
            ..
        } = ctx();
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
        let Ctx {
            mut e, nat, b, g, ..
        } = ctx();
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
        assert!(
            !e.match_pattern(&Term::var(0, nznat), z0, &mut s),
            "Zero is not <= NzNat"
        );
        s.reset(1);
        assert!(
            e.match_pattern(&Term::var(0, nat), z0, &mut s),
            "Zero <= Nat"
        );
    }

    /// Iterative equality compares structurally equal `g^200000(a)` chains with distinct node ids
    /// without recursing on runtime-term depth.
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
        assert!(
            e.deep_equal(x, y),
            "structurally equal deep chains compare equal"
        );
    }
}
