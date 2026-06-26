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

/// The traversal discipline of a [`Rewriting`] session.
#[derive(Clone, Copy)]
enum Mode {
    /// `rewrite`: rule-fair — reduce to canonical, then apply the first rule at the top-down-first redex.
    RuleFair,
    /// `frewrite`: position-fair — `gas` rule applications per non-frozen position per traversal pass.
    PositionFair { gas: u64 },
}

/// A resumable rewriting session (`rewrite` or `frewrite`). Owns the current term — pinned by a
/// [`RootGuard`] so it survives GC across the reductions inside [`run`](Self::run) and while stored
/// between REPL `continue`s — and the per-symbol round-robin rule cursors (Maude's `RuleTable::nextRule`),
/// persisting across steps so a rewrite sequence cycles fairly through a symbol's rules.
pub struct Rewriting {
    current: DagId,
    root: RootGuard,
    cursors: HashMap<SymbolId, u32>,
    /// Set once a normal form is reached (no rule applies anywhere); a further `continue` is a no-op.
    done: bool,
    mode: Mode,
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
        Rewriting { current, root, cursors: HashMap::new(), done: false, mode: Mode::RuleFair }
    }

    /// Construct a position-fair (`frewrite`) session rooted at `current`, with `gas` rule applications
    /// per position per pass.
    pub(crate) fn new_position_fair(root: RootGuard, current: DagId, gas: u64) -> Self {
        Rewriting { current, root, cursors: HashMap::new(), done: false, mode: Mode::PositionFair { gas } }
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
    /// this again with `Some(m)`. Returns when the bound is hit (`done == false`) or a normal form is
    /// reached (`done == true`).
    pub fn run(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
        if self.done {
            return RewriteStep { term: self.current, done: true, sort_known: true };
        }
        match self.mode {
            Mode::RuleFair => self.run_rule_fair(engine, bound),
            Mode::PositionFair { gas } => self.run_position_fair(engine, bound, gas),
        }
    }

    /// `rewrite`: each step reduces `current` to canonical form (equationally — those rewrites count)
    /// then applies one rule at the top-down-first redex (Maude's `ruleRewrite`).
    fn run_rule_fair(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
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

    /// `frewrite`: position-fair. Reduce once, then repeat traversal passes (each gives every non-frozen
    /// position up to `gas` rule applications, reducing between) until the bound is hit or a pass makes
    /// no progress (a normal form). A bounded stop leaves a non-canonical term — `sort_known = false`, so
    /// the REPL prints `result (sort not calculated): …`, exactly as Maude does.
    fn run_position_fair(&mut self, engine: &mut Engine, bound: Option<u64>, gas: u64) -> RewriteStep {
        let mut remaining = bound;
        self.current = engine.reduce(self.current);
        self.root.set(self.current);
        loop {
            let mut progress = false;
            let next = engine.frewrite_pass(self.current, gas, &mut remaining, &mut progress, &mut self.cursors);
            self.current = next;
            self.root.set(next);
            if remaining == Some(0) {
                return RewriteStep { term: self.current, done: false, sort_known: false };
            }
            if !progress {
                self.done = true;
                return RewriteStep { term: self.current, done: true, sort_known: true };
            }
        }
    }
}
