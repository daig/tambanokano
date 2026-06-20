# A6 — Operational rewriting: rules, rewrite/frewrite, search, strategies, objects, external IO (deep-dive report)

### 1. Functional scope
Covers the *dynamic* layer of rewriting-logic execution (manual ch.5, 8, 9, 10): **rules** in system modules, conditional rules with rewrite conditions (§5.1–5.3); the **`rewrite`** (top-down rule-fair) and **`frewrite`** (position-fair, depth-first) commands plus `continue` (§5.4.1–5.4.2, ch.23.2); **`search`** with `=>1/=>+/=>*/=>!`, `such that`, bound `[n,m]`, `show path`/`show search graph` (§5.4.3); model-checking-via-search (ch.11); the **strategy language** (`srewrite`/`dsrewrite`, combinators in Table 10.1: `idle/fail`, `rl[...]{...}`, `;`, `|`, `*`/`+`, tests `match/xmatch/amatch`, `?:`, `matchrew`, strategy calls, `top`, `all`); **object/configuration** systems with object-message fair rewriting (§8.2); and **external objects + IO** (sockets/files/processes/streams/dir/time/prng, control-C, §9.1–9.5).

### 2. Architecture in C++
**Rules.** `Rule` (`Core/rule.hh:31`) derives from `PreEquation` (shared with Equation/SortConstraint/Pattern), holding `rhs`, an `RhsBuilder`, and two lazily-compiled `LhsAutomaton`s (ext/non-ext, `rule.cc:97-119`). `RuleTable` (`Core/ruleTable.hh:31`) is an abstract mixin inherited by symbols; `applyRules` (`ruleTable.cc:74`) walks rules **round-robin** via `nextRule` for rule fairness, matching through `LhsAutomaton::match` → `Subproblem::solve` → `checkCondition` → `RhsBuilder::construct`. The two top-level engines live in `Core/run.cc`: `ruleRewrite` (`:24`, the `rewrite` strategy — reduce to canonical, traverse from the top, apply first rule at first rewritable redex) and `fairRewrite`/`fairTraversal` (`:109,:163`, the `frewrite` strategy — position-fair bottom-up with a persistent `redexStack`, `gasPerNode`, `progress` flag).

**Search.** `StateTransitionGraph` (`Higher/stateTransitionGraph.hh:33`) builds the reachable-state DAG on the fly, **hash-consing** each reduced state (`HashConsSet`) so structurally-equal states collapse; `State` holds `nextStates`, `fwdArcs : map<int,set<Rule*>>`, a lazy `RewriteSearchState`, and a `parent` for path reconstruction (`stateTransitionGraph.cc:67-183`). `RewriteSequenceSearch` (`rewriteSequenceSearch.cc`) layers BFS on top: `findNextInterestingState` is a **goto-resumed coroutine** whose behavior for each `SearchType` (`sequenceSearch.hh:33`) is driven by flags `needToTryInitialState`/`reachingInitialStateOK`/`normalFormNeeded`/`branchNeeded`. `PositionState` (`positionState.hh:34`) enumerates redex positions (frozen/unstackable-aware) and rebuilds the DAG along the path (`rebuildDag`, `:125`); `SearchState` (`searchState.hh:33`) adds backtrackable matching + condition solving via a `Stack<ConditionState*>`; `RewriteSearchState` and `MatchSearchState` specialize it. **Condition fragments** are a virtual hierarchy (`ConditionFragment::solve`, `conditionFragment.hh:32`); rewrite conditions recurse into a *nested* `StateTransitionGraph` (`rewriteConditionState.cc:49`).

**Strategy language.** A small **process/task interpreter**. `StrategyExpression` subclasses (`strategyExpression.hh:33`, e.g. `BranchStrategy`, `SubtermStrategy`) implement `decompose()`. Execution units derive from `StrategicExecution` (`strategicExecution.hh`): `StrategicProcess` (round-robin `run()`, `strategicProcess.hh:30`) and `StrategicTask` (event callbacks, a `slaveList`, and a `seenSet` for cycle detection, `strategicTask.hh:33`) — both wired with **intrusive doubly-linked lists** and manual `delete`. `StrategicSearch` (`strategicSearch.hh:34`) multiply-inherits `HashConsSet`/`StrategyStackManager`/`VariableBindingsManager`; `FairStrategicSearch` (`srewrite`) vs `DepthFirstStrategicSearch` (`dsrewrite`) only differ in process selection (`depthFirstStrategicSearch.cc:65`, `fairStrategicSearch.cc:52`). `ApplicationProcess::run` (`applicationProcess.cc:137`) drives rule application, rewrite-condition strategies (`RewriteTask`), and spawns `DecompositionProcess`. `VariableBindingsManager` (`variableBindingsManager.hh:38`) holds GC-rooted task-local substitution contexts.

**Objects/IO.** `ConfigSymbol` (`configSymbol.hh:32`) extends `ACU_Symbol` and overrides `ruleRewrite` (`configSymbol.cc:220`) to implement object-message fair delivery: partition ACU args into objects/messages/remainder, round-robin object-message rules per message symbol, then one non-object-message rewrite. `ObjectSystemRewritingContext` (`objectSystemRewritingContext.hh:36`) adds `STANDARD/FAIR/EXTERNAL` modes, an external-object map keyed by `DagNode*` identity, a buffered-message map, and `interleave()`/`externalRewrite()` that pump `fairTraversal` against `PseudoThread::eventLoop` (`:114-225`). `ExternalObjectManagerSymbol` (`externalObjectManagerSymbol.hh:30`, a `FreeSymbol`) is the abstract FFI seam (`handleMessage`/`cleanUp`); concrete managers (`socket/file/process/stream/directory/time/prng`) sit beside it. `PseudoThread` (`pseudoThread.hh:34`) is a **static global reactor** over poll/ppoll/pselect with an fd table, a `multimap<timespec,…>` of timed callbacks, and SIGCHLD child-exit handling. `IO_Manager` wraps stdin/tecla line-editing and auto-wrap output.

### 3. Rust migration
- **Rule / RuleTable — ADAPT.** `Rule` as a plain struct sharing a `PreEquation` core (composition, not inheritance); `RuleTable` becomes a *field* on a symbol (`Vec<Rule>` + round-robin cursor), not a base class. Matching via the `LhsAutomaton`/`Subproblem` traits from A2. Rationale: Rust has no virtual base mixins.
- **rewrite/frewrite engines — PORT.** Translate the explicit redex-stack loops directly; replace `copyWithReplacement` raw-pointer path-rebuild with index-based rebuild over an arena of DAG nodes (A1). Keep `gas`/`progress` fairness logic verbatim.
- **Search / StateTransitionGraph — PORT structure, RETHINK control flow.** States become a `Vec<State>` arena with `usize` indices (no `Rule*`/`State*`), arcs `BTreeMap<usize, BTreeSet<RuleId>>`; hash-consing reused from A1. The `goto`-resumed `findNextInterestingState` should become an explicit `Iterator`/state-enum (or a generator), since Rust forbids cross-scope `goto`. `SearchType` → enum; flags → match arms.
- **SearchState/PositionState/conditions — RETHINK as iterators.** Backtracking (`Subproblem`, `Stack<ConditionState*>`) → owned iterator state machines; `ConditionFragment` virtual dispatch → `enum ConditionFragment { Equality, SortTest, Assignment, Rewrite }` with a `solve` method (small closed set ⇒ enum-dispatch).
- **Strategy interpreter — RETHINK (highest risk).** The intrusive linked-list process/task graph with manual `delete` does **not** translate. Model processes/tasks in a slab/arena keyed by `usize`, with an explicit ready-queue (`VecDeque`) and parent/slave links as indices; `StrategyExpression` → enum or `Box<dyn>`; `decompose`/`run` return an action enum (`Survive`/`Die`). `srewrite` vs `dsrewrite` differ only by queue discipline (FIFO-ish fair vs LIFO stack). Variable-binding contexts → arena of GC-rooted substitutions.
- **Objects — ADAPT.** `ConfigSymbol` as an ACU symbol variant overriding rule-rewrite; partition logic ports directly but the `DagNode*`-identity maps need **stable node IDs** (hash-cons index) as keys in Rust.
- **External IO / PseudoThread — RETHINK.** Replace the global static poll reactor + signal handlers with an idiomatic async reactor (`tokio`/`mio`) or a single owned `Reactor` struct; managers become trait objects implementing `handle_message`/`clean_up`. Control-C/SIGCHLD → `signal-hook`/`tokio::signal`. The `special (id-hook …)` binding (A7) maps managers to prelude ops. `IO_Manager`/tecla → `rustyline`.

**Does not translate:** raw-pointer state/process/task graphs and manual `delete`; multiple-inheritance mixins (`RuleTable`, `StrategicSearch`); `goto`-coroutines; `DagNode*`-identity STL maps; global mutable static reactor + Unix signal plumbing; C++ `dynamic_cast` fragment dispatch.

### 4. Hardest parts / risks / open questions
- The **strategy process/task graph**: cyclic ownership + manual lifetime is the single biggest port hazard; needs an arena/index design and careful `seenSet` cycle detection.
- **Resumable search state machines** (`goto` in `RewriteSequenceSearch`, `RewriteConditionState`) must be rewritten as explicit iterators without losing the subtle `=>!`/`branch`/initial-state edge cases.
- **frewrite/srewrite fairness** semantics (round-robin, gas, "counts as one rewrite", fake trace rewrites in `ConfigSymbol`) are observable; exact parity is fiddly.
- **DagNode identity** as map keys across object/external maps — must standardize on hash-cons IDs.
- **External IO concurrency model**: async runtime vs hand-rolled poll loop; how to keep deterministic interleaving for `erewrite`; signal-safe control-C.
- Open: how faithfully to reproduce `frewrite`'s system-dependent ordering vs. a cleaner deterministic order.

### 5. Proposed Rust module layout
```
operational/
  rules.rs              // Rule, RuleTable (cursor), apply_rules
  engine/
    rewrite.rs          // rule-fair `rewrite` + continue
    frewrite.rs         // position-fair traversal, gas/progress
  search/
    state_graph.rs      // StateTransitionGraph arena + hash-cons
    sequence_search.rs  // BFS, SearchType, path/graph reconstruction
    position_state.rs   // redex enumeration + dag rebuild
    search_state.rs     // backtracking match + condition iterators
    conditions.rs       // ConditionFragment enum (eq/sort/assign/rewrite)
  strategy/
    expr.rs             // StrategyExpression enum + decompose
    interp.rs           // process/task arena, ready-queue
    fair.rs / dfs.rs    // srewrite / dsrewrite drivers
    bindings.rs         // VariableBindingsManager (context arena)
  objects/
    config.rs           // ConfigSymbol object-message fair rewriting
    context.rs          // ObjectSystemRewritingContext (modes, buffers)
  io/
    reactor.rs          // PseudoThread replacement (mio/tokio)
    managers/{socket,file,process,stream,dir,time,prng}.rs
    terminal.rs         // IO_Manager / rustyline
```
