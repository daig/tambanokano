//! `search` — the reachable-state graph and breadth-first reachability search (Pillar A-iv).
//!
//! A [`Search`] builds Maude's `StateTransitionGraph` on the fly: each reduced state is **hash-consed**
//! (structurally-equal states collapse to one node, so distinct paths to the same term share a state),
//! and a lazy BFS discovers states in index order. [`next_solution`](Search::next_solution) yields the
//! states matching the goal pattern (filtered by the reachability arrow + an optional `such that`
//! condition), in discovery order, each tagged with the `(states, rewrites)` snapshot taken when the
//! state was first reached — exactly the counts Maude reports per solution.
//!
//! Like [`Rewriting`](crate::rewrite::Rewriting), a `Search` owns its state graph (each state pinned by a
//! [`RootGuard`]) and borrows the [`Engine`] only per call, so the REPL stores it between `continue`s.

use crate::dag::DagId;
use crate::engine::{CompiledFragment, Engine};
use crate::root::RootGuard;
use crate::theory::LhsAutomaton;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

/// The reachability relation a `search` explores.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arrow {
    /// `=>1` — exactly one rewrite step.
    One,
    /// `=>+` — one or more steps.
    Plus,
    /// `=>*` — zero or more steps (the initial state is a candidate).
    Star,
    /// `=>!` — to a normal form (a state with no successors).
    Bang,
}

/// One node of the reachable-state graph.
struct State {
    /// The reduced, canonical term — kept live by `_root`.
    term: DagId,
    _root: RootGuard,
    /// BFS-tree predecessor and the rule on that arc (for `show path`); `None` for the initial state.
    parent: Option<usize>,
    via: Option<u32>,
    /// All forward arcs: successor state index → the rule(s) producing it (for `show search graph`,
    /// ordered for determinism).
    fwd: BTreeMap<usize, BTreeSet<u32>>,
    /// BFS depth (0 = initial).
    depth: u32,
    /// Whether this state's successors have been generated.
    expanded: bool,
}

/// One search solution: the goal-variable bindings and the state + counts to report.
pub struct Solution {
    pub number: u32,
    pub state: usize,
    pub bindings: Vec<DagId>,
    pub states: usize,
    pub rewrites: u64,
}

/// One arc on a reconstructed `show path`: the state index, its term, and the rule reaching it (`None`
/// for the initial state).
pub struct PathStep {
    pub state: usize,
    pub term: DagId,
    pub via: Option<u32>,
}

/// One state's view for `show search graph`: its index, term, and forward arcs (each `(successor state,
/// the rules reaching it)`).
pub type GraphState = (usize, DagId, Vec<(usize, Vec<u32>)>);

/// The state currently being expanded, one successor at a time (lazy generation — so a bounded
/// `search [n]` generates only as many successors as it needs, and `continue` resumes mid-expansion).
struct Expanding {
    state: usize,
    depth: u32,
    /// The raw (uncounted, unreduced) successors of `state`, generated once when expansion begins.
    raw: Vec<(u32, DagId)>,
    cursor: usize,
}

pub struct Search {
    states: Vec<State>,
    /// Hash-cons index: `dag_hash` → candidate state indices (resolved by `deep_equal`).
    index: HashMap<u64, Vec<usize>>,
    arrow: Arrow,
    goal: LhsAutomaton,
    goal_nr_vars: u32,
    such_that: Vec<CompiledFragment>,
    max_depth: Option<u32>,
    /// Discovered, not-yet-expanded state indices (BFS order = index order).
    frontier: VecDeque<usize>,
    /// The state mid-expansion (lazy successor generation), if any.
    expanding: Option<Expanding>,
    /// Goal solutions discovered but not yet yielded (a goal can match several ways).
    pending: VecDeque<Solution>,
    solution_count: u32,
    /// Whether state 0 has been tested against the goal yet (it is seeded, not discovered by expansion).
    tested_initial: bool,
}

impl Search {
    /// Seed the graph with the reduced initial term as state 0. The initial reduction's rewrites are
    /// already in the engine counter; per-solution snapshots are read live (see [`queue_solutions`]).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        root: RootGuard,
        term: DagId,
        goal: LhsAutomaton,
        goal_nr_vars: u32,
        such_that: Vec<CompiledFragment>,
        arrow: Arrow,
        max_depth: Option<u32>,
    ) -> Self {
        let state0 = State {
            term,
            _root: root,
            parent: None,
            via: None,
            fwd: BTreeMap::new(),
            depth: 0,
            expanded: false,
        };
        Search {
            states: vec![state0],
            index: HashMap::new(),
            arrow,
            goal,
            goal_nr_vars,
            such_that,
            max_depth,
            frontier: VecDeque::from([0]),
            expanding: None,
            pending: VecDeque::new(),
            solution_count: 0,
            tested_initial: false,
        }
    }

    /// Total distinct states discovered so far (the `states:` statistic).
    pub fn states(&self) -> usize {
        self.states.len()
    }

    /// The next solution, lazily generating just enough of the BFS, or `None` when the (bounded)
    /// reachable space is exhausted. `continue` calls this again for more. Generation is one successor at
    /// a time so a bounded `search [n]` does only the work it needs (and `continue`'s rewrite snapshots
    /// reflect the post-reset count) — matching Maude's lazy `findNextInterestingState`.
    pub fn next_solution(&mut self, engine: &mut Engine) -> Option<Solution> {
        // State 0 is seeded (not discovered by expansion); test it once — handles `=>*`'s state-0 solution.
        if !self.tested_initial {
            self.tested_initial = true;
            self.test_discovered(engine, 0);
        }
        loop {
            if let Some(sol) = self.pending.pop_front() {
                return Some(sol);
            }
            if !self.step(engine) {
                return None;
            }
        }
    }

    /// Advance the lazy BFS by one quantum: generate the next successor of the state under expansion, or
    /// move on to the next frontier state. Returns `false` when the reachable space is exhausted.
    fn step(&mut self, engine: &mut Engine) -> bool {
        if self.expanding.is_none() {
            // Take the next frontier state to expand. Handle one state per call (returning `true` for
            // progress) so a queued solution is never lost to an exhaustion `false` in the same call.
            let Some(s) = self.frontier.pop_front() else {
                return false; // nothing left to expand
            };
            self.states[s].expanded = true;
            if !self.may_expand(s) {
                return true; // depth-capped (`=>1` / `max_depth`): generate no successors
            }
            let raw = engine.state_successors(self.states[s].term);
            if raw.is_empty() {
                self.test_normal_form(engine, s); // no successors → a normal form (`=>!` candidate)
                return true;
            }
            let depth = self.states[s].depth;
            self.expanding = Some(Expanding { state: s, depth, raw, cursor: 0 });
        }
        let exp = self.expanding.as_mut().unwrap();
        if exp.cursor >= exp.raw.len() {
            self.expanding = None; // finished — it had successors, so not a `=>!` normal form
            return true;
        }
        let (rule_id, succ) = exp.raw[exp.cursor];
        exp.cursor += 1;
        let src = exp.state;
        let succ_depth = exp.depth + 1;
        // Count this rule application and reduce the successor to its canonical state form.
        let reduced = engine.reduce_successor(succ);
        let h = engine.dag_hash(reduced);
        match self.lookup(engine, h, reduced) {
            Some(t) => {
                self.states[src].fwd.entry(t).or_default().insert(rule_id);
            }
            None => {
                let new_idx = self.states.len();
                let root = engine.root(reduced);
                self.states.push(State {
                    term: reduced,
                    _root: root,
                    parent: Some(src),
                    via: Some(rule_id),
                    fwd: BTreeMap::new(),
                    depth: succ_depth,
                    expanded: false,
                });
                self.index.entry(h).or_default().push(new_idx);
                self.states[src].fwd.entry(new_idx).or_default().insert(rule_id);
                self.frontier.push_back(new_idx);
                self.test_discovered(engine, new_idx); // `=>1`/`=>+`/`=>*` test on discovery
            }
        }
        true
    }

    /// Whether state `s` may generate successors (the depth caps of `=>1` and the `[_, max_depth]` bound).
    fn may_expand(&self, s: usize) -> bool {
        let depth = self.states[s].depth;
        if self.arrow == Arrow::One && depth >= 1 {
            return false;
        }
        self.max_depth.is_none_or(|md| depth < md)
    }

    /// `=>1`/`=>+`/`=>*`: if state `s` is at a qualifying depth, match the goal and queue solutions.
    fn test_discovered(&mut self, engine: &mut Engine, s: usize) {
        let ok = match self.arrow {
            Arrow::One => self.states[s].depth == 1,
            Arrow::Plus => self.states[s].depth >= 1,
            Arrow::Star => true,
            Arrow::Bang => false, // a `=>!` solution is a normal form (see `test_normal_form`)
        };
        if ok {
            self.queue_solutions(engine, s);
        }
    }

    /// `=>!`: state `s` has no successors (a normal form) — match the goal and queue solutions.
    fn test_normal_form(&mut self, engine: &mut Engine, s: usize) {
        if self.arrow == Arrow::Bang {
            self.queue_solutions(engine, s);
        }
    }

    /// Match the goal (filtered by `such_that`) against state `s` and queue a [`Solution`] per match,
    /// each tagged with the counts **at the moment the solution is found** — Maude's per-solution snapshot.
    ///
    /// The snapshot is taken *live* (current `states` + `rewrites`) rather than from the state's discovery
    /// counts, which matters in two ways: a `=>!` solution is found when its state is dequeued and
    /// confirmed a normal form — *after* the frontier ahead of it was expanded (more states/rewrites than
    /// at discovery — §3.3 B2b) — and a `such that` solution's rewrite count includes the condition's own
    /// reductions, which `eval_goal` snapshots per binding (§3.3 B2a). For the plain `=>1`/`=>+`/`=>*`
    /// cases the solution is found at discovery, so the live counts equal the old discovery snapshot.
    fn queue_solutions(&mut self, engine: &mut Engine, s: usize) {
        let term = self.states[s].term;
        let states = self.states.len();
        for (bindings, rewrites) in engine.eval_goal(&self.goal, self.goal_nr_vars, &self.such_that, term) {
            self.solution_count += 1;
            self.pending.push_back(Solution { number: self.solution_count, state: s, bindings, states, rewrites });
        }
    }

    /// Resolve a hash-cons hit: an existing state structurally equal to `term`.
    fn lookup(&self, engine: &Engine, h: u64, term: DagId) -> Option<usize> {
        for &idx in self.index.get(&h).into_iter().flatten() {
            if engine.deep_equal(self.states[idx].term, term) {
                return Some(idx);
            }
        }
        // State 0 was seeded without its hash in `index`; check it explicitly.
        if engine.deep_equal(self.states[0].term, term) {
            return Some(0);
        }
        None
    }

    /// The path from the initial state (state 0) to state `n`, following BFS-tree `parent` links — the
    /// `show path n` reconstruction. Empty if `n` is out of range.
    pub fn path(&self, n: usize) -> Vec<PathStep> {
        let mut steps = Vec::new();
        let mut cur = n;
        if cur >= self.states.len() {
            return steps;
        }
        loop {
            let st = &self.states[cur];
            steps.push(PathStep { state: cur, term: st.term, via: st.via });
            match st.parent {
                Some(p) => cur = p,
                None => break,
            }
        }
        steps.reverse();
        steps
    }

    /// The whole graph for `show search graph`: each state's term and its forward arcs (successor index →
    /// the rules reaching it), in state-index order.
    pub fn graph(&self) -> Vec<GraphState> {
        self.states
            .iter()
            .enumerate()
            .map(|(i, st)| {
                let arcs = st
                    .fwd
                    .iter()
                    .map(|(&t, rules)| (t, rules.iter().copied().collect()))
                    .collect();
                (i, st.term, arcs)
            })
            .collect()
    }

    /// The term at state `n` (for `show path`/`show graph` rendering).
    pub fn state_term(&self, n: usize) -> Option<DagId> {
        self.states.get(n).map(|s| s.term)
    }
}
