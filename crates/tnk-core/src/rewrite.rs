//! Resumable rewriting sessions — `rewrite` (rule-fair) and, from Pillar A-ii, `frewrite`
//! (position-fair).
//!
//! A [`Rewriting`] owns its current term (kept live by a [`RootGuard`]) and the round-robin rule
//! cursors, borrowing the [`Engine`] only per [`run`](Rewriting::run) call — so the REPL can store it
//! between commands to implement `continue`.

use crate::dag::DagId;
use crate::engine::Engine;
use crate::root::RootGuard;
use crate::symbol::SymbolId;
use std::collections::HashMap;

/// A resumable rewriting session. Owns the current term — pinned by a [`RootGuard`] so it survives GC
/// across the reductions inside [`run`](Self::run) and while stored between REPL `continue`s — and the
/// per-symbol round-robin rule cursors (Maude's `RuleTable::nextRule`), persisting across steps so a
/// rewrite sequence cycles fairly through a symbol's rules.
pub struct Rewriting {
    current: DagId,
    root: RootGuard,
    cursors: HashMap<SymbolId, u32>,
    /// Set once a normal form is reached (no rule applies anywhere); a further `continue` is a no-op.
    done: bool,
}

/// The outcome of one bounded [`Rewriting::run`]: the current term, whether a normal form was reached
/// (`done`), and whether the term's least sort is known. `sort_known` is always `true` for `rewrite`
/// (every step ends on a `reduce`); a bounded `frewrite` stop will leave a non-canonical term whose
/// sort is not computed, so the REPL prints `result (sort not calculated): …` (A-ii).
pub struct RewriteStep {
    pub term: DagId,
    pub done: bool,
    pub sort_known: bool,
}

impl Rewriting {
    /// Construct a rule-fair (`rewrite`) session rooted at `current`.
    pub(crate) fn new_rule_fair(root: RootGuard, current: DagId) -> Self {
        Rewriting { current, root, cursors: HashMap::new(), done: false }
    }

    /// The current term.
    pub fn current(&self) -> DagId {
        self.current
    }

    /// Whether a normal form has been reached (no rule applies anywhere).
    pub fn is_done(&self) -> bool {
        self.done
    }

    /// Run up to `bound` rule applications (`None` = unbounded, to a normal form); `continue m` calls
    /// this again with `Some(m)`. Each step reduces `current` to canonical form (equationally — those
    /// rewrites count toward the total) then applies one rule at the top-down-first redex (Maude's
    /// `ruleRewrite`). Returns when the bound is hit (`done == false`) or a normal form is reached
    /// (`done == true`).
    pub fn run(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
        if self.done {
            return RewriteStep { term: self.current, done: true, sort_known: true };
        }
        let mut steps = 0u64;
        loop {
            let reduced = engine.reduce(self.current);
            self.current = reduced;
            self.root.set(reduced);
            if bound == Some(steps) {
                return RewriteStep { term: self.current, done: false, sort_known: true };
            }
            match engine.rewrite_step(self.current, &mut self.cursors) {
                Some(next) => {
                    self.current = next;
                    self.root.set(next);
                    steps += 1;
                }
                None => {
                    self.done = true;
                    return RewriteStep { term: self.current, done: true, sort_known: true };
                }
            }
        }
    }
}
