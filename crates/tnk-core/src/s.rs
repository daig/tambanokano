//! S-theory (`iter` successor) matching: a matcher for the unary stacked successor `s_`.
//!
//! A pattern `s^k(sub)` matches a subject `s^n(base)` of the same operator. The successor count `k` is
//! peeled off the pattern at compile time; matching then compares it to the subject's count `n`:
//! - `n < k` — no match (the pattern needs more successors than the subject has).
//! - `n == k` — `sub` matches the subject's `base`, no residue (a "whole" match).
//! - `n > k`, with **extension** (`ext_allowed`, the top-rewrite / `xmatch` case) — the matched `s^k`
//!   sits under `residue = n − k − j` surplus successors that wrap the rhs; a *variable* `sub` can
//!   absorb `j` of the surplus (`X = s^j(base)`, `j` from `n−k` down to `0` — genuinely multi-solution,
//!   so the enumerator is **lazy** because `n−k` is a bignum), while a ground/alien `sub` forces `j = 0`
//!   (it must align with the single base), leaving `residue = n − k`.
//! - `n > k`, **no extension** (condition / membership matching) — a variable `sub` must absorb the
//!   whole surplus (`X = s^(n−k)(base)`, residue 0); a ground/alien `sub` cannot match.
//!
//! A bare-variable sub-pattern takes the direct (possibly lazy, bignum) absorption path here; any other
//! sub-pattern (ground, free alien, **or theory-rooted**) is matched against the subject's base through
//! the full matcher seam ([`enumerate_alien_solutions`](crate::theory::enumerate_alien_solutions)), so
//! cross-theory composition under an `iter` operator works uniformly with the other theories.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num::Nat;
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::{Subst, Term};
use crate::theory::enumerate_alien_solutions;

/// A compiled S left-hand side `s^count(sub)`: the peeled successor `count` (≥ 1) and the residual
/// sub-pattern.
#[derive(Clone)]
pub(crate) struct SLhs {
    symbol: SymbolId,
    count: Nat,
    sub: SSub,
}

/// The residual sub-pattern after peeling the successors.
#[derive(Clone)]
enum SSub {
    /// A bare variable — absorbs a run of successors over the base.
    Var { index: u32, sort: SortId },
    /// A non-variable sub-pattern (ground, free alien like `f(X)`, or theory-rooted like `a + b`):
    /// matched against the subject's base through the full matcher seam. `vars` are its variable indices
    /// (captured into each solution / unbound on backtracking).
    Pat { pat: Term, vars: Vec<u32> },
}

impl SLhs {
    /// Compile an iter pattern: peel the leading `s_` layers, counting them, then classify the residual.
    pub(crate) fn compile(lhs: Term, _sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("S lhs must be an application");
        let mut count = Nat::zero();
        let mut t = lhs;
        loop {
            match t {
                Term::Op { symbol: s, args } if s == symbol && args.len() == 1 => {
                    count = count.add(&Nat::one());
                    t = args.into_iter().next().unwrap();
                }
                other => {
                    t = other;
                    break;
                }
            }
        }
        debug_assert!(!count.is_zero(), "an S pattern has at least one successor");
        let sub = match t {
            Term::Var(v) => SSub::Var { index: v.index, sort: v.sort },
            other => {
                // Any non-variable sub-pattern (ground / free alien / theory-rooted) matches the base
                // through the full matcher seam in `next` (`enumerate_alien_solutions`).
                let mut vars = Vec::new();
                collect_vars(&other, &mut vars);
                SSub::Pat { pat: other, vars }
            }
        };
        SLhs { symbol, count, sub }
    }

    /// First match phase: the subject must be an S node of this operator with `count >= self.count`.
    /// Sets up the (resumable) solution enumerator; `None` if the subject is not an S node of this
    /// symbol or has too few successors.
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        subject: DagId,
        ext_allowed: bool,
    ) -> Option<SSubproblem> {
        let (n, base) = match &rt.node(subject).term {
            NodeTerm::S { symbol, count, arg } if *symbol == self.symbol => (count.clone(), *arg),
            _ => return None,
        };
        let diff = n.checked_sub(&self.count)?; // None ⇒ n < k ⇒ no match
        let state = match &self.sub {
            SSub::Var { index, sort } if ext_allowed => {
                // X absorbs j of the surplus, j = diff … 0 (lazy — diff is a bignum). A peeled-successor
                // pattern (`s^k X`) has floor 0; the bare-variable case (constructed separately) uses 1.
                SState::VarExt {
                    index: *index,
                    sort: *sort,
                    diff: diff.clone(),
                    next_j: Some(diff),
                    floor: Nat::zero(),
                }
            }
            SSub::Var { index, sort } => {
                // No extension: X absorbs the whole surplus (residue 0).
                SState::VarWhole { index: *index, sort: *sort, j: diff }
            }
            SSub::Pat { pat, vars } => {
                if !ext_allowed && !diff.is_zero() {
                    return None; // a non-variable sub needs n == k without extension
                }
                SState::Pat {
                    pat: pat.clone(),
                    vars: vars.clone(),
                    residue: diff,
                    recorded: None,
                    cursor: 0,
                }
            }
        };
        Some(SSubproblem {
            symbol: self.symbol,
            base,
            state,
            bound: Vec::new(),
            residue: Nat::zero(),
            matched_whole: true,
            extension: ext_allowed,
        })
    }
}

/// A resumable enumerator over the solutions of an [`SLhs`] against a subject (an arm of the closed
/// [`crate::theory::Subproblem`] enum). Owns its state, so it survives the `&mut Runtime` calls the
/// driver makes between solutions.
pub(crate) struct SSubproblem {
    symbol: SymbolId,
    base: DagId,
    state: SState,
    /// Variable indices bound by the most recent solution (unbound before the next one — F-4).
    bound: Vec<u32>,
    /// Residue of the most recent solution: the rhs is wrapped in `s^residue` (`build_result`).
    residue: Nat,
    matched_whole: bool,
    /// `true` when this was an extension match against an S node — governs the `xmatch` `Matched
    /// portion` line (`false` prints no line, as for a non-theory subject).
    extension: bool,
}

/// The per-pattern-shape enumerator state.
enum SState {
    /// Variable + extension: bind `X = s^j(base)` for `j` descending from `next_j` to `floor`, residue
    /// `diff − j`. Lazy because `diff` may be astronomically large. `floor` is 0 for a peeled `s^k X`
    /// pattern and 1 for a bare variable (Maude's `S_Subproblem` `mustMatchAtLeast`, so the matched
    /// portion keeps at least one successor).
    VarExt { index: u32, sort: SortId, diff: Nat, next_j: Option<Nat>, floor: Nat },
    /// Variable, no extension: a single solution `X = s^j(base)`, residue 0.
    VarWhole { index: u32, sort: SortId, j: Nat },
    /// Non-variable sub-pattern matched against the base (through the full matcher seam, so it may be
    /// theory-rooted), with a fixed `residue` (`diff`). Multi-solution: `recorded` holds the per-solution
    /// variable snapshots (enumerated lazily on the first `next`), `cursor` the replay position.
    Pat { pat: Term, vars: Vec<u32>, residue: Nat, recorded: Option<Vec<Vec<(u32, DagId)>>>, cursor: usize },
    /// Exhausted (the single-solution arms transition here after yielding once).
    Done,
}

impl SSubproblem {
    /// A **bare variable** matched with extension against an S node `s^n(base)` (Maude's
    /// `S_DagNode::matchVariableWithExtension` → `S_Subproblem` with `mustMatchAtLeast = 1`): bind
    /// `X = s^j(base)` for `j = n, n−1, …, 1`, leaving `residue = n − j` surplus successors. The floor of
    /// 1 keeps at least one successor in the matched portion (so `xmatch X:Nat <=? 3` yields the whole
    /// plus the `2` and `1` portions — not the bare `0`; fable-audit.md §3.3).
    pub(crate) fn match_variable_with_extension(
        symbol: SymbolId,
        n: Nat,
        base: DagId,
        var_index: u32,
        var_sort: SortId,
    ) -> SSubproblem {
        SSubproblem {
            symbol,
            base,
            state: SState::VarExt {
                index: var_index,
                sort: var_sort,
                diff: n.clone(),
                next_j: Some(n),
                floor: Nat::one(),
            },
            bound: Vec::new(),
            residue: Nat::zero(),
            matched_whole: true,
            extension: true,
        }
    }

    /// Extension-match status of the *current* solution, for the `xmatch` display: `None` when this was
    /// not an extension match (no `Matched portion` line), else whether the whole subject was matched.
    pub(crate) fn matched_status(&self) -> Option<bool> {
        self.extension.then_some(self.matched_whole)
    }

    /// Advance to the next solution, binding its variable(s) into `subst` and recording the residue;
    /// `false` when exhausted. Builds binding nodes (needs `&mut Runtime`).
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();

        let symbol = self.symbol;
        let base = self.base;

        // Non-variable sub-pattern: match it against the base through the full matcher seam (so it may
        // be free, theory-rooted, or mixed), enumerated once then replayed. Each solution carries the
        // same fixed `residue` (the surplus successors that wrap the rhs).
        if matches!(self.state, SState::Pat { .. }) {
            if matches!(self.state, SState::Pat { recorded: None, .. }) {
                let (pat, vars) = match &self.state {
                    SState::Pat { pat, vars, .. } => (pat.clone(), vars.clone()),
                    _ => unreachable!(),
                };
                let sols = enumerate_alien_solutions(rt, sig, subst, &[(pat, base)], &vars);
                if let SState::Pat { recorded, .. } = &mut self.state {
                    *recorded = Some(sols);
                }
            }
            let (binds, residue) = match &mut self.state {
                SState::Pat { recorded: Some(sols), cursor, residue, .. } => {
                    if *cursor >= sols.len() {
                        return false;
                    }
                    let binds = sols[*cursor].clone();
                    *cursor += 1;
                    (binds, residue.clone())
                }
                _ => unreachable!(),
            };
            for (idx, b) in binds {
                subst.bind(idx, b);
                self.bound.push(idx);
            }
            self.residue = residue;
            self.matched_whole = self.residue.is_zero();
            return true;
        }

        loop {
            // A variable sub-pattern absorbs `j` successors over the base: extract `(index, sort, j,
            // residue)` (releasing the `self.state` borrow), build `s^j(base)`, bind. Sort-violating `j`
            // skips to the next.
            let (index, sort, j, residue) = match &mut self.state {
                SState::VarExt { index, sort, diff, next_j, floor } => match next_j.take() {
                    None => return false,
                    Some(j) => {
                        // Descend to `floor` (0 for `s^k X`, 1 for a bare variable — Maude's
                        // `mustMatchAtLeast`), so a bare variable never yields the zero-successor portion.
                        *next_j = if j == *floor {
                            None
                        } else {
                            Some(j.checked_sub(&Nat::one()).unwrap())
                        };
                        let residue = diff.checked_sub(&j).unwrap();
                        (*index, *sort, j, residue)
                    }
                },
                SState::VarWhole { index, sort, j } => {
                    let r = (*index, *sort, j.clone(), Nat::zero());
                    self.state = SState::Done;
                    r
                }
                SState::Done => return false,
                SState::Pat { .. } => unreachable!("a Pat sub-pattern is handled above"),
            };
            let binding = rt.make_s(sig, symbol, j, base);
            if !sig.sorts().leq(rt.sort_of(binding), sort) {
                continue; // this j violates the variable's sort; try the next (or finish)
            }
            if let Some(existing) = subst.get(index) {
                // Non-linear S variable, pre-bound elsewhere: a solution exists only where the
                // absorbed portion agrees with the existing binding (Maude's S_LhsAutomaton
                // bound-variable path); nothing new is bound.
                if !rt.deep_equal(existing, binding) {
                    continue;
                }
            } else {
                subst.bind(index, binding);
                self.bound.push(index);
            }
            self.residue = residue;
            self.matched_whole = self.residue.is_zero();
            return true;
        }
    }

    /// Splice the instantiated `rhs` into the matched position: a whole match is just `rhs`; an
    /// extension match wraps it in the residue successors (`s^residue(rhs)` — Maude's `partialConstruct`).
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        if self.matched_whole {
            rhs
        } else {
            rt.make_s(sig, self.symbol, self.residue.clone(), rhs)
        }
    }
}

/// Collect the distinct variable indices of a (free) sub-pattern, in first-seen order.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// Sorts `Zero NzNat < Nat`, `0 : Zero`, unary `iter` `s_ : Nat -> NzNat`; returns `(e, nat, 0, s_)`.
    fn ctx() -> (Engine, SortId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        (e, nat, z, s)
    }

    /// Decode an `s^n(0)` DAG node to `n` (a constant base `0` is `n = 0`).
    fn count_of(e: &Engine, id: DagId) -> u64 {
        match &e.node(id).term {
            NodeTerm::S { count, .. } => count.to_usize().unwrap() as u64,
            _ => 0,
        }
    }

    /// Drive `match_` + `next` over a 1-variable pattern, returning each solution's `X` binding as a count.
    fn solutions(e: &mut Engine, pattern: Term, subject: DagId, ext: bool) -> Vec<u64> {
        let lhs = SLhs::compile(pattern, e.signature());
        let mut subst = Subst::new();
        subst.reset(1);
        let mut bindings: Vec<DagId> = Vec::new();
        {
            let (sig, rt) = e.parts_mut();
            let Some(mut sp) = lhs.match_(rt, subject, ext) else { return Vec::new() };
            while sp.next(rt, sig, &mut subst) {
                bindings.push(subst.get(0).expect("X bound"));
            }
        }
        bindings.into_iter().map(|b| count_of(e, b)).collect()
    }

    /// `xmatch s X <=? s s s 0` (== reference binary): 3 solutions, X absorbing `j = 2,1,0` successors
    /// (descending — the first is the whole match).
    #[test]
    fn s_extension_enumerates_descending_absorptions() {
        let (mut e, nat, z, s) = ctx();
        let z0 = e.make_const(z);
        let subject = e.make_iter(s, 3, z0); // s^3(0)
        let pat = Term::op(s, vec![Term::var(0, nat)]); // s X
        assert_eq!(solutions(&mut e, pat, subject, true), vec![2, 1, 0], "X = s^2 0, s 0, 0");
    }

    /// Without extension a variable sub-pattern absorbs the *whole* surplus — the single collector
    /// solution `X = s^(n-k)(0)` (the condition/membership matching case).
    #[test]
    fn s_without_extension_is_the_whole_collector() {
        let (mut e, nat, z, s) = ctx();
        let z0 = e.make_const(z);
        let subject = e.make_iter(s, 3, z0);
        let pat = Term::op(s, vec![Term::var(0, nat)]); // s X
        assert_eq!(solutions(&mut e, pat, subject, false), vec![2], "only X = s^2 0 (whole)");
    }

    /// A pattern needing more successors than the subject has does not match; a ground sub matches only
    /// its own base.
    #[test]
    fn s_too_few_successors_and_ground_base() {
        let (mut e, nat, z, s) = ctx();
        let z0 = e.make_const(z);
        let s1 = e.make_iter(s, 1, z0); // s^1(0)
        // s s X <=? s 0 : pattern needs 2 successors, subject has 1 → no match.
        let pat = Term::op(s, vec![Term::op(s, vec![Term::var(0, nat)])]);
        assert!(solutions(&mut e, pat, s1, true).is_empty(), "s s X !<=? s 0");
    }
}
