//! CUI-theory unification — commutative and/or identity and/or idempotent operators that are
//! **not** associative (Maude's `CUI_Theory`). Idempotence is unsupported for unification, so this
//! covers C / CU / CUl / CUr / U / Ul / Ur.
//!
//! Ports, line-faithful including alternative enumeration order:
//!   * `CUI_DagNode::computeSolvedForm2` / `computeSolvedFormCommutativeCase` /
//!     `makePurifiedVersion` / `indirectOccursCheck` (`src/CUI_Theory/CUI_DagNode.cc`),
//!   * `CUI_UnificationSubproblem` — the pure-commutative subproblem, forwards then reverse per
//!     problem (`src/CUI_Theory/CUI_UnificationSubproblem.cc`),
//!   * `CUI_UnificationSubproblem2` — the with-identity subproblem, seven ordered alternatives per
//!     problem (`src/CUI_Theory/CUI_UnificationSubproblem2.cc`).
//!
//! A CUI node's two arguments are kept in `dag_compare` order for the commutative cases (tnk's
//! `make_cui` canonicalizes exactly as Maude's normal form), so the four-comparison C decision
//! procedure reads them as `l0 <= l1`, `r0 <= r1`.

use super::{
    Marker, PendingStack, SavedSubst, UnifyContext, UnifyEnv, compute_solved_form,
    last_variable_in_chain, var_index,
};
use crate::dag::DagId;
use crate::engine::Engine;
use crate::symbol::SymbolId;
use std::cmp::Ordering;

/// The two arguments of a CUI-unification node. Read generically through `children()` so it works
/// for BOTH node representations a CUI-unification-theory symbol can have: a genuine `Cui` node
/// (two-sided `id:` / `comm` / `idem` ops, identity kept in the kernel) and a **`Free`** node
/// (one-sided `left id:`/`right id:` ops, whose identity the frontend withholds from the kernel,
/// so tnk builds them as binary free applications). Both are binary with
/// positionally-meaningful (or, for comm, `dag_compare`-ordered) arguments.
fn cui_args(e: &Engine, id: DagId) -> (DagId, DagId) {
    let mut kids = e.node(id).children();
    let a0 = kids.next().expect("CUI-unification node is binary");
    let a1 = kids.next().expect("CUI-unification node is binary");
    debug_assert!(
        kids.next().is_none(),
        "CUI-unification node has exactly two arguments"
    );
    (a0, a1)
}

/// Rebuild a binary CUI-unification node from its two arguments, dispatching on the symbol's
/// theory (`Engine::rebuild`): a genuine Cui op re-canonicalizes (comm order / id / idem collapse),
/// a one-sided-id Free op stays a positional free application.
fn rebuild_binary(env: &mut UnifyEnv, symbol: SymbolId, a0: DagId, a1: DagId) -> DagId {
    let (sig, rt) = env.e.parts_mut();
    rt.rebuild(sig, symbol, vec![a0, a1])
}

/// Build the identity DAG of a CUI-with-id operator (`getIdentityDag`): the two-sided identity,
/// or whichever one-sided identity is declared.
fn identity_dag(env: &mut UnifyEnv, symbol: SymbolId) -> DagId {
    let identity = env
        .e
        .symbol(symbol)
        .left_identity()
        .or_else(|| env.e.symbol(symbol).right_identity())
        .expect("a CUI-with-id operator has an identity");
    env.e.make_identity(identity)
}

/// `DagNode::compare` on two nodes, via the runtime's canonical total order.
fn compare(e: &Engine, a: DagId, b: DagId) -> Ordering {
    e.dag_compare(a, b)
}

// ======================================================================================
// CUI_DagNode::computeSolvedForm2
// ======================================================================================

/// `CUI_DagNode::computeSolvedForm2` — `lhs` is a non-ground CUI node.
pub(crate) fn cui_solved_form2(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    let s = env.e.node(lhs).symbol();
    let has_id = {
        let sym = env.e.symbol(s);
        sym.left_identity().is_some() || sym.right_identity().is_some()
    };
    if s == env.e.node(rhs).symbol() {
        if has_id {
            // With an identity we consider all collapse alternatives — push for the theory solver.
            pending.push(Some(s), lhs, rhs, false);
            return true;
        }
        // The pure-commutative case has an optimized in-place decision procedure.
        return commutative_case(env, lhs, rhs, ctx, pending);
    }
    if var_index(env.e, rhs).is_some() {
        let r = last_variable_in_chain(env.e, ctx, rhs);
        let r_index = var_index(env.e, r).unwrap() as usize;
        if let Some(value) = ctx.value(r_index) {
            // Bound: recurse with computeSolvedForm2 (matches the reference — not the ground-aware
            // computeSolvedForm).
            return cui_solved_form2_generic(env, lhs, value, ctx, pending);
        }
        if has_id {
            pending.push(Some(s), lhs, rhs, false);
        } else {
            let purified = make_purified_version(env, lhs, ctx, pending);
            ctx.unification_bind(env.e, r, purified);
        }
        return true;
    }
    pending.resolve_theory_clash(env.e, lhs, rhs)
}

/// Re-entry when the bound value's top may differ from CUI: dispatch through the generic
/// `computeSolvedForm2` again (the reference calls the virtual `computeSolvedForm2`, which for a
/// non-CUI value lands in that value's theory arm).
fn cui_solved_form2_generic(
    env: &mut UnifyEnv,
    lhs: DagId,
    value: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    // `lhs` is our CUI node (non-ground); solve lhs =? value through the standard dispatcher.
    super::compute_solved_form2(env, lhs, value, ctx, pending)
}

/// `CUI_DagNode::computeSolvedFormCommutativeCase` — pure C, same top symbol. Decide in ≤4
/// comparisons whether any of the six argument equalities forces a single branch; otherwise push
/// the two-alternative problem onto the pending stack.
fn commutative_case(
    env: &mut UnifyEnv,
    lhs: DagId,
    rhs: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> bool {
    let s = env.e.node(lhs).symbol();
    let (mut l0, mut l1) = cui_args(env.e, lhs);
    let (mut r0, mut r1) = cui_args(env.e, rhs);
    // l0 <= l1 and r0 <= r1 by normal form.
    let res1 = compare(env.e, l0, r0);
    if res1 == Ordering::Equal {
        return compute_solved_form(env, l1, r1, ctx, pending);
    }
    if res1 == Ordering::Greater {
        std::mem::swap(&mut l0, &mut r0);
        std::mem::swap(&mut l1, &mut r1);
    }
    // Now l0 < r0 <= r1 ⇒ l0 < r1. Still possible: l1 == r0 or l1 == r1.
    let res2 = compare(env.e, l1, r0);
    if res2 == Ordering::Equal {
        return compute_solved_form(env, l0, r1, ctx, pending);
    }
    if res2 == Ordering::Less {
        // l0 <= l1 < r0 <= r1. Check both sides for duplicated arguments.
        if !(env.e.deep_equal(l0, l1) || env.e.deep_equal(r0, r1)) {
            pending.push(Some(s), lhs, rhs, false);
            return true;
        }
    } else {
        // l0 < r0 < l1 and r0 <= r1, so l1 == r1 still possible.
        let res3 = compare(env.e, l1, r1);
        if res3 == Ordering::Equal {
            return compute_solved_form(env, l0, r0, ctx, pending);
        }
        if res3 == Ordering::Less {
            // l0 < r0 < l1 < r1. No equalities — two alternatives.
            pending.push(Some(s), lhs, rhs, false);
            return true;
        } else {
            // l0 < r0 < l1 and r1 < l1, so r0 == r1 is the only possible equality.
            if !env.e.deep_equal(r0, r1) {
                pending.push(Some(s), lhs, rhs, false);
                return true;
            }
        }
    }
    // A duplicated argument in at least one unificand — a single possibility suffices.
    compute_solved_form(env, l0, r0, ctx, pending) && compute_solved_form(env, l1, r1, ctx, pending)
}

/// `CUI_DagNode::makePurifiedVersion` — abstract each non-variable argument to a fresh variable
/// (solving it against the abstraction), then rebuild in commutative normal order.
fn make_purified_version(
    env: &mut UnifyEnv,
    this: DagId,
    ctx: &mut UnifyContext,
    pending: &mut PendingStack,
) -> DagId {
    let s = env.e.node(this).symbol();
    let comm = env.e.symbol(s).axioms.comm;
    let (a0, a1) = cui_args(env.e, this);
    let mut need_rebuild = false;

    let l0 = if var_index(env.e, a0).is_some() {
        a0
    } else {
        let kind = super::domain_kind(env.e, s, 0);
        let abstraction = ctx.make_fresh_variable(env, kind);
        compute_solved_form(env, a0, abstraction, ctx, pending);
        need_rebuild = true;
        abstraction
    };
    let l1 = if env.e.deep_equal(a1, a0) {
        l0 // both arguments equal — reuse the same purified form
    } else if var_index(env.e, a1).is_some() {
        a1
    } else {
        let kind = super::domain_kind(env.e, s, 1);
        let abstraction = ctx.make_fresh_variable(env, kind);
        compute_solved_form(env, a1, abstraction, ctx, pending);
        need_rebuild = true;
        abstraction
    };
    if !need_rebuild {
        return this;
    }
    // Rebuild via the theory dispatcher: a comm Cui op re-sorts, a one-sided-id Free op keeps
    // positional order — both handled by `rebuild_binary`.
    let _ = comm;
    rebuild_binary(env, s, l0, l1)
}

/// `CUI_DagNode::indirectOccursCheck` — can `rep_var` be reached by chasing `var |-> var` and
/// `var |-> our-symbol` bindings from `this`'s arguments? `rep_var` is a representative (unbound
/// or bound-to-non-variable).
fn indirect_occurs_check(env: &UnifyEnv, this: DagId, rep_var: DagId, ctx: &UnifyContext) -> bool {
    let s = env.e.node(this).symbol();
    let (a0, a1) = cui_args(env.e, this);
    indirect_occurs_arg(env, a0, s, rep_var, ctx) || indirect_occurs_arg(env, a1, s, rep_var, ctx)
}

fn indirect_occurs_arg(
    env: &UnifyEnv,
    arg: DagId,
    s: SymbolId,
    rep_var: DagId,
    ctx: &UnifyContext,
) -> bool {
    if var_index(env.e, arg).is_some() {
        let r = last_variable_in_chain(env.e, ctx, arg);
        if env.e.deep_equal(r, rep_var) {
            return true;
        }
        // Same-symbol binding (`d->symbol() == s`) — s is our binary CUI-unification op, so any
        // node with that symbol is a binary node whether its rep is Cui or (one-sided-id) Free.
        if let Some(d) = ctx.value(var_index(env.e, r).unwrap() as usize)
            && env.e.node(d).symbol() == s
        {
            return indirect_occurs_check(env, d, rep_var, ctx);
        }
        false
    } else if env.e.node(arg).symbol() == s {
        indirect_occurs_check(env, arg, rep_var, ctx)
    } else {
        false
    }
}

// ======================================================================================
// CUI_UnificationSubproblem — pure C
// ======================================================================================

struct CProblem {
    lhs: DagId,
    rhs: DagId,
    saved_subst: SavedSubst,
    saved_pending: Marker,
    reverse_tried: bool,
}

/// The pure-commutative subproblem: each problem tries forwards `(l0=?r0, l1=?r1)` then, on
/// backtrack, reverse `(l0=?r1, l1=?r0)`.
#[derive(Default)]
pub(crate) struct CSubproblem {
    problems: Vec<CProblem>,
}

impl CSubproblem {
    pub(crate) fn add_unification(&mut self, lhs: DagId, rhs: DagId, marked: bool) {
        debug_assert!(
            !marked,
            "pure-C subproblems never receive collapse (marked) problems"
        );
        self.problems.push(CProblem {
            lhs,
            rhs,
            saved_subst: Vec::new(),
            saved_pending: 0,
            reverse_tried: false,
        });
    }

    pub(crate) fn gc_roots(&self) -> Vec<DagId> {
        self.problems
            .iter()
            .flat_map(|p| {
                p.saved_subst
                    .iter()
                    .copied()
                    .flatten()
                    .chain([p.lhs, p.rhs])
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub(crate) fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        let n = self.problems.len() as isize;
        let mut i: isize;
        let mut forward: bool;
        if find_first {
            i = 0;
            forward = true;
        } else {
            i = n - 1;
            forward = false;
        }
        loop {
            if forward {
                let mut failed = false;
                while i < n {
                    let idx = i as usize;
                    self.problems[idx].saved_subst = ctx.clone_subst();
                    self.problems[idx].saved_pending = pending.checkpoint();
                    self.problems[idx].reverse_tried = false;
                    let (lhs, rhs) = (self.problems[idx].lhs, self.problems[idx].rhs);
                    let (l0, l1) = cui_args(env.e, lhs);
                    let (r0, r1) = cui_args(env.e, rhs);
                    if !(compute_solved_form(env, l0, r0, ctx, pending)
                        && compute_solved_form(env, l1, r1, ctx, pending))
                    {
                        failed = true;
                        break; // goto backtrack (from this same index)
                    }
                    i += 1;
                }
                if !failed {
                    return true;
                }
                forward = false;
            } else {
                let mut restart = false;
                while i >= 0 {
                    let idx = i as usize;
                    if !self.problems[idx].reverse_tried {
                        let saved = self.problems[idx].saved_subst.clone();
                        ctx.restore_from_clone(&saved);
                        pending.restore(self.problems[idx].saved_pending);
                        let (lhs, rhs) = (self.problems[idx].lhs, self.problems[idx].rhs);
                        let (l0, l1) = cui_args(env.e, lhs);
                        let (r0, r1) = cui_args(env.e, rhs);
                        if compute_solved_form(env, l0, r1, ctx, pending)
                            && compute_solved_form(env, l1, r0, ctx, pending)
                        {
                            self.problems[idx].reverse_tried = true;
                            i += 1;
                            restart = true;
                            break; // goto forward
                        }
                    }
                    i -= 1;
                }
                if restart {
                    forward = true;
                    continue;
                }
                // Exhausted: restore initial state.
                let saved = self.problems[0].saved_subst.clone();
                ctx.restore_from_clone(&saved);
                pending.restore(self.problems[0].saved_pending);
                return false;
            }
        }
    }
}

// ======================================================================================
// CUI_UnificationSubproblem2 — with identity
// ======================================================================================

/// The seven ordered alternatives (`CUI_UnificationSubproblem2::Alternatives`). Numeric order IS
/// the enumeration order.
mod alt {
    pub(super) const FORWARDS: u8 = 0;
    pub(super) const REVERSE: u8 = 1;
    pub(super) const LHS_ARG0_TAKES_ID: u8 = 2;
    pub(super) const LHS_ARG1_TAKES_ID: u8 = 3;
    pub(super) const RHS_ARG0_TAKES_ID: u8 = 4;
    pub(super) const RHS_ARG1_TAKES_ID: u8 = 5;
    pub(super) const RHS_VARIABLE_TAKES_ALL: u8 = 6;
    pub(super) const NO_MORE: u8 = 7;
}

struct IdProblem {
    lhs: DagId,
    rhs: DagId,
    /// Bit `k` set iff alternative `k` is legal for this problem.
    legal: u8,
    saved_subst: SavedSubst,
    saved_pending: Marker,
    alternative: u8,
}

impl IdProblem {
    fn legal(&self, a: u8) -> bool {
        self.legal & (1 << a) != 0
    }
}

/// The with-identity CUI subproblem.
#[derive(Default)]
pub(crate) struct CuiIdSubproblem {
    problems: Vec<IdProblem>,
    /// The operator's identity node, built once on the first `add_unification`.
    identity: Option<DagId>,
}

impl CuiIdSubproblem {
    pub(crate) fn gc_roots(&self) -> Vec<DagId> {
        let mut roots: Vec<DagId> = self
            .problems
            .iter()
            .flat_map(|p| {
                p.saved_subst
                    .iter()
                    .copied()
                    .flatten()
                    .chain([p.lhs, p.rhs])
            })
            .collect();
        roots.extend(self.identity);
        roots
    }

    /// `CUI_UnificationSubproblem2::addUnification` — classify the legal alternatives (recursing on
    /// the degenerate collapse cases).
    pub(crate) fn add_unification(
        &mut self,
        env: &mut UnifyEnv,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
        lhs: DagId,
        rhs: DagId,
        marked: bool,
    ) {
        let _ = pending;
        let top = env.e.node(lhs).symbol();
        if self.identity.is_none() {
            self.identity = Some(identity_dag(env, top));
        }
        let sym = env.e.symbol(top);
        let left_id = sym.left_identity().is_some();
        let right_id = sym.right_identity().is_some();
        let comm = sym.axioms.comm;
        let id = self.identity.unwrap();

        let mut legal: u8 = 0;
        if env.e.node(rhs).symbol() == top {
            // f(u, v) =? f(s, t).
            let (l0, l1) = cui_args(env.e, lhs);
            let (r0, r1) = cui_args(env.e, rhs);
            // Degenerate collapses first (each returns after re-adding a smaller problem).
            if self.left_collapse(env, l0, top, left_id, id, ctx) {
                self.add_unification(env, ctx, pending, rhs, l1, false);
                return;
            }
            if self.right_collapse(env, l1, top, right_id, id, ctx) {
                self.add_unification(env, ctx, pending, rhs, l0, false);
                return;
            }
            if self.left_collapse(env, r0, top, left_id, id, ctx) {
                self.add_unification(env, ctx, pending, lhs, r1, false);
                return;
            }
            if self.right_collapse(env, r1, top, right_id, id, ctx) {
                self.add_unification(env, ctx, pending, lhs, r0, false);
                return;
            }
            legal |= 1 << alt::FORWARDS;
            let lhs_arg_equiv = self.equivalent(env, l0, l1, ctx);
            let rhs_arg_equiv = self.equivalent(env, r0, r1, ctx);
            if comm && !lhs_arg_equiv && !rhs_arg_equiv {
                legal |= 1 << alt::REVERSE;
            }
            if left_id {
                legal |= 1 << alt::LHS_ARG0_TAKES_ID;
                legal |= 1 << alt::RHS_ARG0_TAKES_ID;
                if right_id {
                    if !lhs_arg_equiv {
                        legal |= 1 << alt::LHS_ARG1_TAKES_ID;
                    }
                    if !rhs_arg_equiv {
                        legal |= 1 << alt::RHS_ARG1_TAKES_ID;
                    }
                }
            } else if right_id {
                legal |= 1 << alt::LHS_ARG1_TAKES_ID;
                legal |= 1 << alt::RHS_ARG1_TAKES_ID;
            }
        } else {
            // f(u, v) =? X and f(u, v) =? g(...).
            let (l0, l1) = cui_args(env.e, lhs);
            if self.equivalent_to_ground(env, rhs, id, ctx) {
                // Both arguments must take identity; LHS_ARG0_TAKES_ID's handler achieves it.
                legal |= 1 << alt::LHS_ARG0_TAKES_ID;
            } else if self.left_collapse(env, l0, top, left_id, id, ctx) {
                legal |= 1 << alt::LHS_ARG0_TAKES_ID;
            } else if self.right_collapse(env, l1, top, right_id, id, ctx) {
                legal |= 1 << alt::LHS_ARG1_TAKES_ID;
            } else {
                if left_id {
                    legal |= 1 << alt::LHS_ARG0_TAKES_ID;
                }
                if right_id && (!left_id || !self.equivalent(env, l0, l1, ctx)) {
                    legal |= 1 << alt::LHS_ARG1_TAKES_ID;
                }
                if !marked && var_index(env.e, rhs).is_some() {
                    legal |= 1 << alt::RHS_VARIABLE_TAKES_ALL;
                }
            }
        }
        self.problems.push(IdProblem {
            lhs,
            rhs,
            legal,
            saved_subst: Vec::new(),
            saved_pending: 0,
            alternative: 0,
        });
    }

    /// `leftCollapse`: `left_arg` is a variable bound to the identity (left id only).
    fn left_collapse(
        &self,
        env: &UnifyEnv,
        left_arg: DagId,
        top: SymbolId,
        left_id: bool,
        id: DagId,
        ctx: &UnifyContext,
    ) -> bool {
        let _ = top;
        left_id && self.bound_to_identity(env, left_arg, id, ctx)
    }

    /// `rightCollapse`: `right_arg` is a variable bound to the identity (right id only).
    fn right_collapse(
        &self,
        env: &UnifyEnv,
        right_arg: DagId,
        top: SymbolId,
        right_id: bool,
        id: DagId,
        ctx: &UnifyContext,
    ) -> bool {
        let _ = top;
        right_id && self.bound_to_identity(env, right_arg, id, ctx)
    }

    fn bound_to_identity(&self, env: &UnifyEnv, arg: DagId, id: DagId, ctx: &UnifyContext) -> bool {
        if var_index(env.e, arg).is_some() {
            let rep = last_variable_in_chain(env.e, ctx, arg);
            if let Some(binding) = ctx.value(var_index(env.e, rep).unwrap() as usize) {
                return env.e.deep_equal(binding, id);
            }
        }
        false
    }

    /// `equivalent`: two terms equal after chasing each's variable representative + binding.
    fn equivalent(&self, env: &UnifyEnv, first: DagId, second: DagId, ctx: &UnifyContext) -> bool {
        let f = self.resolve(env, first, ctx);
        let s = self.resolve(env, second, ctx);
        env.e.deep_equal(f, s)
    }

    fn resolve(&self, env: &UnifyEnv, d: DagId, ctx: &UnifyContext) -> DagId {
        if var_index(env.e, d).is_some() {
            let rep = last_variable_in_chain(env.e, ctx, d);
            ctx.value(var_index(env.e, rep).unwrap() as usize)
                .unwrap_or(rep)
        } else {
            d
        }
    }

    /// `equivalentToGroundDag`: `dag` equals `ground` directly, or is a variable bound to it.
    fn equivalent_to_ground(
        &self,
        env: &UnifyEnv,
        dag: DagId,
        ground: DagId,
        ctx: &UnifyContext,
    ) -> bool {
        if env.e.deep_equal(dag, ground) {
            return true;
        }
        if var_index(env.e, dag).is_some() {
            let rep = last_variable_in_chain(env.e, ctx, dag);
            if let Some(binding) = ctx.value(var_index(env.e, rep).unwrap() as usize) {
                return env.e.deep_equal(binding, ground);
            }
        }
        false
    }

    pub(crate) fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        let n = self.problems.len() as isize;
        let mut i: isize;
        let mut forward: bool;
        if find_first {
            i = 0;
            forward = true;
        } else {
            i = n - 1;
            forward = false;
        }
        loop {
            if forward {
                let mut failed = false;
                while i < n {
                    let idx = i as usize;
                    if !self.find_alternative(env, idx, true, ctx, pending) {
                        i -= 1;
                        failed = true;
                        break; // goto backtrack
                    }
                    i += 1;
                }
                if !failed {
                    return true;
                }
                forward = false;
            } else {
                let mut restart = false;
                while i >= 0 {
                    let idx = i as usize;
                    if self.find_alternative(env, idx, false, ctx, pending) {
                        i += 1;
                        restart = true;
                        break; // goto forward
                    }
                    i -= 1;
                }
                if restart {
                    forward = true;
                    continue;
                }
                return false;
            }
        }
    }

    /// `Problem::findAlternative` — advance to the next legal alternative that solves.
    fn find_alternative(
        &mut self,
        env: &mut UnifyEnv,
        idx: usize,
        first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        if first {
            self.problems[idx].alternative = alt::FORWARDS;
        } else {
            let saved = self.problems[idx].saved_subst.clone();
            ctx.restore_from_clone(&saved);
            pending.restore(self.problems[idx].saved_pending);
            self.problems[idx].alternative += 1;
        }
        while self.problems[idx].alternative != alt::NO_MORE {
            let a = self.problems[idx].alternative;
            if self.problems[idx].legal(a) {
                self.problems[idx].saved_subst = ctx.clone_subst();
                self.problems[idx].saved_pending = pending.checkpoint();
                if self.try_alternative(env, idx, ctx, pending) {
                    return true;
                }
                let saved = self.problems[idx].saved_subst.clone();
                ctx.restore_from_clone(&saved);
                pending.restore(self.problems[idx].saved_pending);
            }
            self.problems[idx].alternative += 1;
        }
        false
    }

    /// `Problem::tryAlternative` — attempt the current alternative.
    fn try_alternative(
        &mut self,
        env: &mut UnifyEnv,
        idx: usize,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        let (lhs, rhs, a) = (
            self.problems[idx].lhs,
            self.problems[idx].rhs,
            self.problems[idx].alternative,
        );
        let id = self.identity.unwrap();
        let (l0, l1) = cui_args(env.e, lhs);
        match a {
            alt::FORWARDS => {
                let (r0, r1) = cui_args(env.e, rhs);
                compute_solved_form(env, l0, r0, ctx, pending)
                    && compute_solved_form(env, l1, r1, ctx, pending)
            }
            alt::REVERSE => {
                let (r0, r1) = cui_args(env.e, rhs);
                compute_solved_form(env, l0, r1, ctx, pending)
                    && compute_solved_form(env, l1, r0, ctx, pending)
            }
            alt::LHS_ARG0_TAKES_ID => {
                compute_solved_form(env, l0, id, ctx, pending)
                    && compute_solved_form(env, l1, rhs, ctx, pending)
            }
            alt::LHS_ARG1_TAKES_ID => {
                compute_solved_form(env, l1, id, ctx, pending)
                    && compute_solved_form(env, l0, rhs, ctx, pending)
            }
            alt::RHS_ARG0_TAKES_ID => {
                let (r0, r1) = cui_args(env.e, rhs);
                compute_solved_form(env, r0, id, ctx, pending)
                    && compute_solved_form(env, r1, lhs, ctx, pending)
            }
            alt::RHS_ARG1_TAKES_ID => {
                let (r0, r1) = cui_args(env.e, rhs);
                compute_solved_form(env, r1, id, ctx, pending)
                    && compute_solved_form(env, r0, lhs, ctx, pending)
            }
            alt::RHS_VARIABLE_TAKES_ALL => {
                let r2 = last_variable_in_chain(env.e, ctx, rhs);
                let r2_index = var_index(env.e, r2).unwrap() as usize;
                match ctx.value(r2_index) {
                    None => {
                        // Avoid an occur-check-failing binding local to our theory (collapse would
                        // have been tried on another branch, so we just fail here).
                        if indirect_occurs_check(env, lhs, r2, ctx) {
                            return false;
                        }
                        let purified = make_purified_version(env, lhs, ctx, pending);
                        ctx.unification_bind(env.e, r2, purified);
                        true
                    }
                    Some(d) => compute_solved_form(env, d, lhs, ctx, pending),
                }
            }
            _ => unreachable!("nonexistent CUI alternative"),
        }
    }
}
