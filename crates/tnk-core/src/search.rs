//! `search` — the reachable-state graph and breadth-first reachability search.
//!
//! A [`Search`] builds a reachable-state graph lazily. Structurally equal reduced states share one
//! node, and BFS discovers nodes in index order. [`next_solution`](Search::next_solution) yields goal
//! matches in discovery order; each solution records the current graph size and accepted rewrite count.
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
    /// Distinct successor states in first-rewrite-result order. Model checking consumes this ordinal
    /// view; `fwd` retains every rule that produced each arc.
    successor_order: Vec<usize>,
    /// Pending rewrite results and the equation work needed to enumerate each one. Generation is eager,
    /// but the work is charged lazily as the model checker/search consumes the stream. Every pending
    /// term is rooted because proposition checks and other reductions can collect between graph calls.
    raw: Option<VecDeque<RawSuccessor>>,
    /// Equation work needed to prove the raw stream exhausted, charged only when the caller asks past
    /// its final result.
    raw_tail_rewrites: u64,
    /// BFS depth (0 = initial).
    depth: u32,
    /// Whether every raw successor has been committed.
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

pub(crate) struct RawSuccessor {
    pub(crate) rule_id: u32,
    pub(crate) term: DagId,
    pub(crate) enumeration_rewrites: u64,
    pub(crate) _root: RootGuard,
}

pub(crate) struct RawSuccessors {
    pub(crate) entries: Vec<RawSuccessor>,
    pub(crate) tail_rewrites: u64,
}

/// The rewrite-engine operations needed by [`StateGraph`]. Implementations are statically dispatched:
/// ordinary search uses [`Engine`], while model checking supplies the active `Runtime`/`Signature` view.
pub(crate) trait GraphContext {
    fn graph_state_successors(&mut self, root: DagId) -> RawSuccessors;
    fn graph_replay_rewrites(&mut self, rewrites: u64);
    fn graph_reduce_successor(&mut self, successor: DagId) -> DagId;
    fn graph_dag_hash(&self, id: DagId) -> u64;
    fn graph_deep_equal(&self, lhs: DagId, rhs: DagId) -> bool;
    fn graph_root(&self, id: DagId) -> RootGuard;
}

impl GraphContext for Engine {
    fn graph_state_successors(&mut self, root: DagId) -> RawSuccessors {
        self.state_successors(root)
    }

    fn graph_replay_rewrites(&mut self, rewrites: u64) {
        self.replay_graph_rewrites(rewrites);
    }

    fn graph_reduce_successor(&mut self, successor: DagId) -> DagId {
        self.reduce_successor(successor)
    }

    fn graph_dag_hash(&self, id: DagId) -> u64 {
        self.dag_hash(id)
    }

    fn graph_deep_equal(&self, lhs: DagId, rhs: DagId) -> bool {
        self.deep_equal(lhs, rhs)
    }

    fn graph_root(&self, id: DagId) -> RootGuard {
        self.root(id)
    }
}

/// One ordinal successor returned by [`StateGraph::get_next_state`].
pub(crate) struct GraphSuccessor {
    pub(crate) state: usize,
    /// True only when committing this rewrite result inserted a new canonical state.
    pub(crate) discovered: bool,
}

/// Shared, lazily expanded reachable-state graph used by ordinary search and LTL model checking.
pub(crate) struct StateGraph {
    states: Vec<State>,
    /// Hash-cons index: `dag_hash` → candidate state indices (resolved by `deep_equal`).
    index: HashMap<u64, Vec<usize>>,
}

impl StateGraph {
    pub(crate) fn new(root: RootGuard, term: DagId) -> Self {
        Self {
            states: vec![State {
                term,
                _root: root,
                parent: None,
                via: None,
                fwd: BTreeMap::new(),
                successor_order: Vec::new(),
                raw: None,
                raw_tail_rewrites: 0,
                depth: 0,
                expanded: false,
            }],
            index: HashMap::new(),
        }
    }

    /// Return distinct successor `transition` in first-result order, lazily committing raw rule
    /// applications until that ordinal exists or the source is exhausted. Duplicate rewrites still
    /// count and add their rule ids to the shared forward arc.
    pub(crate) fn get_next_state<C: GraphContext>(
        &mut self,
        context: &mut C,
        state: usize,
        transition: usize,
    ) -> Option<GraphSuccessor> {
        if let Some(&target) = self.states.get(state)?.successor_order.get(transition) {
            return Some(GraphSuccessor {
                state: target,
                discovered: false,
            });
        }
        loop {
            if self.states[state].expanded {
                return None;
            }
            if self.states[state].raw.is_none() {
                let term = self.states[state].term;
                let batch = context.graph_state_successors(term);
                let source = &mut self.states[state];
                source.raw = Some(batch.entries.into());
                source.raw_tail_rewrites = batch.tail_rewrites;
            }
            let (next, tail_rewrites) = {
                let source = &mut self.states[state];
                let raw = source.raw.as_mut().expect("raw successors initialized");
                if let Some(next) = raw.pop_front() {
                    (Some(next), 0)
                } else {
                    source.raw = None;
                    source.expanded = true;
                    let tail = std::mem::take(&mut source.raw_tail_rewrites);
                    (None, tail)
                }
            };
            context.graph_replay_rewrites(tail_rewrites);
            let next = next?;
            context.graph_replay_rewrites(next.enumeration_rewrites);
            let (rule_id, successor) = (next.rule_id, next.term);

            let reduced = context.graph_reduce_successor(successor);
            let hash = context.graph_dag_hash(reduced);
            let existing = self.lookup(context, hash, reduced);
            let (target, discovered) = match existing {
                Some(target) => (target, false),
                None => {
                    let target = self.states.len();
                    let depth = self.states[state].depth + 1;
                    let root = context.graph_root(reduced);
                    self.states.push(State {
                        term: reduced,
                        _root: root,
                        parent: Some(state),
                        via: Some(rule_id),
                        fwd: BTreeMap::new(),
                        successor_order: Vec::new(),
                        raw: None,
                        raw_tail_rewrites: 0,
                        depth,
                        expanded: false,
                    });
                    self.index.entry(hash).or_default().push(target);
                    (target, true)
                }
            };
            let distinct = !self.states[state].fwd.contains_key(&target);
            self.states[state]
                .fwd
                .entry(target)
                .or_default()
                .insert(rule_id);
            if !distinct {
                continue;
            }
            self.states[state].successor_order.push(target);
            debug_assert_eq!(self.states[state].successor_order.len() - 1, transition);
            return Some(GraphSuccessor {
                state: target,
                discovered,
            });
        }
    }

    fn lookup<C: GraphContext>(&self, context: &C, hash: u64, term: DagId) -> Option<usize> {
        for &index in self.index.get(&hash).into_iter().flatten() {
            if context.graph_deep_equal(self.states[index].term, term) {
                return Some(index);
            }
        }
        // State 0 is seeded without its hash in `index`; check it explicitly.
        context
            .graph_deep_equal(self.states[0].term, term)
            .then_some(0)
    }

    pub(crate) fn len(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn state_dag(&self, state: usize) -> Option<DagId> {
        self.states.get(state).map(|entry| entry.term)
    }

    pub(crate) fn state_depth(&self, state: usize) -> u32 {
        self.states[state].depth
    }

    pub(crate) fn fwd_arcs(&self, state: usize) -> Option<&BTreeMap<usize, BTreeSet<u32>>> {
        self.states.get(state).map(|entry| &entry.fwd)
    }

    pub(crate) fn arc_rules(&self, source: usize, target: usize) -> Option<&BTreeSet<u32>> {
        self.states.get(source)?.fwd.get(&target)
    }

    pub(crate) fn path(&self, state: usize) -> Vec<PathStep> {
        let mut steps = Vec::new();
        let mut current = state;
        if current >= self.states.len() {
            return steps;
        }
        loop {
            let entry = &self.states[current];
            steps.push(PathStep {
                state: current,
                term: entry.term,
                via: entry.via,
            });
            match entry.parent {
                Some(parent) => current = parent,
                None => break,
            }
        }
        steps.reverse();
        steps
    }

    pub(crate) fn view(&self) -> Vec<GraphState> {
        self.states
            .iter()
            .enumerate()
            .map(|(index, state)| {
                let arcs = state
                    .fwd
                    .iter()
                    .map(|(&target, rules)| (target, rules.iter().copied().collect()))
                    .collect();
                (index, state.term, arcs)
            })
            .collect()
    }
}

/// The state currently being expanded, one successor at a time (lazy generation — so a bounded
/// `search [n]` generates only as many successors as it needs, and `continue` resumes mid-expansion).
struct Expanding {
    state: usize,
    cursor: usize,
}

pub struct Search {
    graph: StateGraph,
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
        Search {
            graph: StateGraph::new(root, term),
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

    pub fn states(&self) -> usize {
        self.graph.len()
    }

    /// Return the next solution, generating only enough of the BFS to find it. `continue` resumes the
    /// same expansion. One-successor quanta prevent bounded searches from doing unnecessary work and
    /// preserve rewrite snapshots across counter resets.
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
            let Some(state) = self.frontier.pop_front() else {
                return false;
            };
            if !self.may_expand(state) {
                return true;
            }
            self.expanding = Some(Expanding { state, cursor: 0 });
        }

        let expanding = self.expanding.as_mut().expect("expansion initialized");
        let source = expanding.state;
        let transition = expanding.cursor;
        match self.graph.get_next_state(engine, source, transition) {
            None => {
                self.expanding = None;
                if transition == 0 {
                    self.test_normal_form(engine, source);
                }
            }
            Some(successor) => {
                expanding.cursor += 1;
                if successor.discovered {
                    self.frontier.push_back(successor.state);
                    self.test_discovered(engine, successor.state);
                }
            }
        }
        true
    }

    /// Whether state `s` may generate successors (the depth caps of `=>1` and the `[_, max_depth]` bound).
    fn may_expand(&self, s: usize) -> bool {
        let depth = self.graph.state_depth(s);
        if self.arrow == Arrow::One && depth >= 1 {
            return false;
        }
        self.max_depth.is_none_or(|md| depth < md)
    }

    /// `=>1`/`=>+`/`=>*`: if state `s` is at a qualifying depth, match the goal and queue solutions.
    fn test_discovered(&mut self, engine: &mut Engine, s: usize) {
        let ok = match self.arrow {
            Arrow::One => self.graph.state_depth(s) == 1,
            Arrow::Plus => self.graph.state_depth(s) >= 1,
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

    /// Match the goal, filtered by `such_that`, against state `s` and queue one [`Solution`] per
    /// accepted match. Each solution records the current graph size and the rewrite count after its own
    /// condition evaluation.
    ///
    /// A `=>!` state is tested only after successor exhaustion, so its counts include work performed
    /// between discovery and normal-form confirmation. The other arrows test qualifying states when
    /// they are discovered.
    fn queue_solutions(&mut self, engine: &mut Engine, s: usize) {
        let term = self.graph.state_dag(s).expect("search state exists");
        let states = self.graph.len();
        for (bindings, rewrites) in
            engine.eval_goal(&self.goal, self.goal_nr_vars, &self.such_that, term)
        {
            self.solution_count += 1;
            self.pending.push_back(Solution {
                number: self.solution_count,
                state: s,
                bindings,
                states,
                rewrites,
            });
        }
    }

    /// The path from the initial state (state 0) to state `n`, following BFS-tree `parent` links — the
    /// `show path n` reconstruction. Empty if `n` is out of range.
    pub fn path(&self, n: usize) -> Vec<PathStep> {
        self.graph.path(n)
    }

    /// The whole graph for `show search graph`: each state's term and its forward arcs (successor index →
    /// the rules reaching it), in state-index order.
    pub fn graph(&self) -> Vec<GraphState> {
        self.graph.view()
    }

    /// The term at state `n` (for `show path`/`show graph` rendering).
    pub fn state_term(&self, n: usize) -> Option<DagId> {
        self.graph.state_dag(n)
    }
}
