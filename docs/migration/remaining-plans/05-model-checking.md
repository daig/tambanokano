# 05 — Model checking (phase M / roadmap G4)

**Subsystem.** LTL model checking of rewrite systems: an LTL formula is turned into a
Büchi automaton (Gastin–Oddoux), the product of that automaton with the rewrite
state-transition system is searched for an accepting cycle by nested DFS, and a
**counterexample lasso** (lead-in prefix + cycle) is returned. Plus the sibling LTL
satisfiability/tautology solver (`satSolve`/`tautCheck`).

**Status: IN PROGRESS (2026-07-23); M0 COMPLETE, implementation cursor M1.** The frozen
manifest is 10 fixtures / 49 commands. An oracle-vs-oracle run reports `SUBSYSTEMS 10/10 PASS`;
the production binary accepts every fixture but reports `0/10`, as expected, because
`SatSolverSymbol` and `ModelCheckerSymbol` remain declared-inert and their applications stay
unreduced. M0 changed no production code. Phase M is independent of S and T
(`subsystems-goal.md` §2); T is complete, so M1 is now the selected serial step.

**Pass criterion (the hard part).** Per `subsystems-goal.md` §2, counterexample
output must be **byte-exact** to the reference — *"paths are deterministic; they are the
pass criterion, not just the verdict."* This elevates the README's "(where it matters)
byte-for-byte output" to a hard requirement for phase M. A logically-correct but
*different* lasso is a FAIL.

---

## 1. Subsystem overview — the `modelCheck` interface

### 1.1 The prelude (`~/code/maude-lang/maude/src/Main/model-checker.maude`)

Six functional/system modules, all loaded via `load model-checker`:

| module | role |
|---|---|
| `LTL` (lines 28–71) | `Formula` sort; primitive ops `True False ~_ _/\_ _\/_ O_ _U_ _R_` (ctor); derived ops `_->_ _<->_ <>_ []_ _W_ _|->_ _=>_ _<=>_` (defined by eqs); **negative-normal-form** equations (`~True=False`, `~(f\/g)=~f/\~g`, `~ O f = O ~ f`, `~(f U g)=(~f) R (~g)`, …). |
| `LTL-SIMPLIFIER` (73–173) | Etessami–Holzmann + Somenzi–Bloem formula simplification, driven by the order-sorted sort system (`PureFormula`/`PE-Formula`/`PU-Formula`) + a `_<=_` implication relation. **Optional** — not included by `MODEL-CHECKER`. Pure equations. |
| `SAT-SOLVER` (175–214) | `satSolve : Formula ~> SatSolveResult` (id-hook `SatSolverSymbol`); `tautCheck(F) = $invert(satSolve(~ F))`; results `model(FormulaList,FormulaList)` / `false` / `counterexample(...)`. |
| `SATISFACTION` (216–220) | the abstract interface: `sorts State Prop` and `op _|=_ : State Prop ~> Bool [frozen]`. The user's module defines `State`, the `Prop`s, and the satisfaction equations. |
| `MODEL-CHECKER` (222–262) | `modelCheck : State Formula ~> ModelCheckResult` (id-hook `ModelCheckerSymbol`); `subsort Prop < Formula`; `RuleName` (`Qid` ∪ `unlabeled` ∪ `deadlock`), `Transition {_,_}`, `TransitionList __`, `counterexample(TransitionList,TransitionList)`. |
| `LTL+` / `MODEL-CHECKER+` (264–298) | existential/universal wrappers `E_ A_`, `modelCheck+`, `witness`. **Pure equations** on top of `modelCheck` — no new hooks (`modelCheck+(st,E f)=neg(modelCheck(st,~f))`, etc.). |

### 1.2 What a model-checking program looks like (from `tests/Misc/dekker.maude`)

The user makes their machine-state sort a subsort of `State`, declares `Prop`s, and
gives the satisfaction equations (`dekker.maude:169–182`):

```maude
mod CHECK is
  inc DEKKER .  inc MODEL-CHECKER .
  subsort MachineState < State .
  ops enterCrit exec : Pid -> Prop .
  eq {[I, crit ; R] | S, M, J} |= enterCrit(I) = true .
  eq {S, M, J} |= exec(J) = true .
endm
red modelCheck(initial, [] ~ (enterCrit(1) /\ enterCrit(2))) .   *** true
red modelCheck(initial, []<> exec(1) -> []<> enterCrit(1)) .     *** counterexample
```

`_|=_` reduces to `true` exactly when the proposition holds in the state; anything else
is treated as false. Propositions are ordinary ground terms of sort `Prop`.

### 1.3 Reference output (confirmed on the oracle, Opt-buddy-bison-yices2 build)

A minimal 2-state toggle (`{zero} -flip0-> {one} -flip1-> {zero}`, with `{zero}|=p0`,
`{one}|=p1`), which makes an ideal first fixture:

```
red modelCheck({zero}, []<> p0) .   ⇒  result Bool: true                       (rewrites: 10)
red modelCheck({zero}, [] p0) .     ⇒  counterexample({{zero}, 'flip0},
                                                     {{one}, 'flip1} {{zero}, 'flip0})   (rewrites: 7)
red modelCheck({zero}, <> [] p1) .  ⇒  counterexample(nil,
                                                     {{zero}, 'flip0} {{one}, 'flip1})   (rewrites: 10)
```

- A `counterexample(leadIn, cycle)`: two `TransitionList`s. Each transition is
  `{stateTerm, ruleName}`; `ruleName` is the rule's label as a `Qid` (`'flip0`), or
  `unlabeled`, or `deadlock`. An empty lead-in is `nil`.
- `satSolve(a U b) ⇒ model(b, True)`; `satSolve(a /\ ~ a) ⇒ false`;
  `tautCheck(a -> a) ⇒ true`; `tautCheck([] a -> a) ⇒ true`.
- Note: the whole result is an ordinary term of sort `ModelCheckResult`/`SatSolveResult`
  built from the op-hook symbols and printed by the standard result printer. So
  byte-exactness of the counterexample = correct lasso (which states, in which order) +
  the term pretty-printer tnk **already** produces byte-exactly for `search`/`show path`.

---

## 2. Reference approach (Maude C++)

Bridge in `src/Higher/`, engine in `src/Temporal/`. The pipeline for
`modelCheck(s, φ)`:

### 2.1 The bridge — `Higher/modelCheckerSymbol.{cc,hh}`

`ModelCheckerSymbol::eqRewrite` (`modelCheckerSymbol.cc:253–309`):

1. **Negate + reduce.** `newContext = makeSubcontext(negate(φ)); newContext->reduce();`
   (`:261–262`). The LTL prelude equations put `¬φ` into NNF. (Model checking looks for a
   run satisfying `¬φ`; such a run is a counterexample to `φ`.)
2. **Build a `LogicFormula`.** `TemporalSymbol::build(formula, propositions, root)`
   (`temporalSymbol.cc:126–196`) recursively converts the reduced dag into a
   `LogicFormula` node DAG. It recognizes `trueSymbol/falseSymbol/notSymbol/nextSymbol/
   andSymbol/orSymbol/untilSymbol/releaseSymbol`; **everything else is a proposition**,
   indexed by first-encounter order into a `DagNodeSet propositions`
   (`temporalSymbol.cc:189–194`). `NOT` is accepted only over a proposition (NNF check,
   `:141–142`). If it is not valid NNF → `NONE` → advisory + `tryEquations` (op stays a term).
   **This descent order fixes the proposition→BDD-variable index map — determinism root #1.**
3. **Build the system + property automata and run the checker** (`:269–292`):
   ```
   SystemAutomaton system; ...
   system.systemStates = new StateTransitionGraph(makeSubcontext(s));   // lazy state graph
   ModelChecker2 mc(system, formula, top);
   bool result = mc.findCounterexample();
   ```
4. **Emit the result** (`:304–308`): `result ? makeCounterexample(states, mc) : trueTerm`.

`makeCounterexample` (`:233–242`): `junction = mc.getCycle().front();` then
`counterexample(makeTransitionList(leadIn, junction), makeTransitionList(cycle, junction))`.
`makeTransitionList` (`:210–231`) walks a state list emitting `makeTransition(from, to)` for
consecutive pairs, the last one targeting `junction` (closing the arc into the cycle head).
`makeTransition` (`:191–208`): `args[0]=stateDag(from)`; for `args[1]` it looks up the
**forward arc** `from→to`; if none, `deadlock`; else it takes the label of *the first rule
in the arc's `set<Rule*>`* — `unlabeled` if the label id is `NONE`, else
`QuotedIdentifierDagNode(qidSymbol, id)`.

The `System` interface (`modelChecker2.hh:42–46`) decouples the checker from rewriting:
```
struct System {
  virtual int  getNextState(int stateNr, int transitionNr) = 0;
  virtual bool checkProposition(int stateNr, int propositionIndex) const = 0;
};
```
`SystemAutomaton::getNextState` (`modelCheckerSymbol.cc:311–318`) delegates to
`StateTransitionGraph::getNextState`, and — critically — **fakes a self-loop for a
deadlocked (successor-less) state**: `if (n==NONE && transitionNr==0) return stateNr;`.
`checkProposition` (`:320–333`) builds `satisfiesSymbol(stateDag, propDag)`, reduces it in
a subcontext, and returns `trueTerm->equal(root)`, adding the rewrite count into the parent.

### 2.2 The reused state graph — `Higher/stateTransitionGraph.{cc,hh}`

A lazy, **hash-consed**, on-the-fly graph shared with the `search` command's
`RewriteSequenceSearch`. `getNextState(stateNr, index)` (`stateTransitionGraph.cc:67–183`):
if `index` < already-computed successors, return it; else drive a
`RewriteSearchState::findNextRewrite()` (with flags
`SET_UNREWRITABLE|RESPECT_UNREWRITABLE|SET_UNSTACKABLE|RESPECT_UNSTACKABLE|GC_CONTEXT`)
to produce the next successor, `reduce()` it, `hashConsSet.insert` for canonical dedup,
append to `nextStates`, and record `fwdArcs[nextState].insert(rule)` (`:166`). Each `State`
keeps a `parent` back-link (`:144`) and `ArcMap fwdArcs = map<int, set<Rule*>>`
(`stateTransitionGraph.hh:38`). This is exactly what tnk's `Search` already reimplements
(§3.2).

### 2.3 The property automaton — LTL → Büchi (`src/Temporal/`), Gastin–Oddoux

`BuchiAutomaton2(formula, top)` (`buchiAutomaton2.cc:38–71`) runs a three-stage pipeline;
every stage uses **BDD-labelled transitions** (a transition's label is a Boolean function
over proposition variables).

1. **Very-weak alternating automaton** — `veryWeakAlternatingAutomaton.{cc,hh}`. `dnf()`
   (`vwaa.cc:54–91`) computes a disjunction-of-conjunctions of subformula-states as a
   `TransitionSet`; `computeTransitionSet()` (`:93–175`) gives each subformula its
   transitions: `PROPOSITION → ithvar(p)`, `NOT p → nithvar(p)`, `NEXT → dnf(arg)`,
   `AND → product`, `OR → union`, and the fixpoint unfoldings for `UNTIL` (which
   `finalStates.append(sub)` — the fairness sources) and `RELEASE`. `reachabilityOpt()`
   (`:177–208`) renumbers to reachable states only. `TransitionSet` (`transitionSet.hh`)
   is a `map<NatSet, Bdd>` kept in a canonical **subsumption-minimal** form
   (`transitionSet.cc:37–101`: a smaller state-conjunction trims a larger one's valuations).
2. **Generalized Büchi automaton** — `genBuchiAutomaton.{cc,hh}` (the Gastin–Oddoux VWAA→GBA
   translation, cited `genBuchiAutomaton.cc:23–37`). GBA states are **sets of VWAA states**
   (`NatSet`) interned by an `IndexedSet` (`getStateIndex`, `:145–160`); `generateState`
   (`:77–143`) forms the raw product (`rawTransitionSet.cc`) of the component transition
   sets and computes a per-transition **fairness set** (`vwaa->computeFairnessSet`).
   `FairTransition = pair<pair<state,fairness>, Bdd>`; `insertFairTransition` (`:162–202`)
   canonicalizes with BDD subsumption. `simplify()` (`:63–75`) =
   `maximallyCollapseStates()` (`collapseStates.cc`) + `sccOptimizations()`
   (`sccOptimizations.cc`, using Tarjan `sccAnalysis.cc` — components classified
   DEAD/UNFAIR/FAIR with redundant-fairness-set computation, per Somenzi–Bloem).
3. **Degeneralization to an ordinary Büchi automaton** — `BuchiAutomaton2::generate`
   (`buchiAutomaton2.cc:73–104`): the standard counter construction over the
   `nrFairnessSets+1` copies; `acceptingStates` = the top-copy states. `TransitionMap =
   map<int, Bdd>` (`buchiAutomaton2.hh:37`). `collapseStates` (`:115–192`) merges states
   with identical transition maps. This is the object the nested DFS consumes:
   `getInitialStates()`, `isAccepting(s)`, `getTransitions(s)` (a `map<int,Bdd>`).

### 2.4 The emptiness check — `Temporal/modelChecker2.{cc,hh}`, nested (double) DFS

Holzmann–Peled–Yannakakis nested DFS (cited `modelChecker2.hh:26–29`) over the **product**
of the system graph and the Büchi automaton. A product state is `(systemStateNr,
propertyStateNr)`. `intersectionStates` is indexed by system state; each entry (`StateSet`,
`:54–61`) holds `dfs1Seen`, `onDfs1Stack`, `dfs2Seen`, and the **per-system-state
proposition memo** `testedProps`/`trueProps`.

- `findCounterexample` (`:45–57`): for each Büchi initial state, `dfs1PropertyTransitions(0, i)`.
- DFS1 (`:81–111` + `:64–79`): follow enabled property transitions
  (`satisfiesPropositionalFormula`) then all system successors; when reaching an
  **accepting** property state, launch DFS2 from it.
- DFS2 (`:118–165`): look for a transition back to a product state on the DFS1 stack
  (`onDfs1Stack.contains`) — that closes an accepting cycle.
- **Counterexample recovery**: `path.push_front(systemStateNr)` as recursion unwinds;
  when the recorded junction `(cycleSystemStateNr, cyclePropertyStateNr)` is hit,
  `cycle.swap(path)` splits lead-in from cycle (`:100–104`).
- `satisfiesPropositionalFormula` (`:167–193`): **walk the label ROBDD from the root** —
  `int p = bdd_var(f); ... f = checkProposition(state, p) ? bdd_high(f) : bdd_low(f)` —
  memoizing each proposition per system state. It only tests the props on the root→leaf
  path (short-circuiting). **This lazy walk + per-state memo determines how many
  `state|=prop` reductions happen, hence the reported `rewrites:` count** — determinism
  root #3 (see §4.3).

### 2.5 The SAT/tautology sibling — `Higher/satSolverSymbol.cc` + `Temporal/satSolve.cc`

`satSolve(φ)` reuses the **generalized** Büchi automaton (no degeneralization):
`SatSolverSymbol::eqRewrite` (`satSolverSymbol.cc:166–201`) reduces φ, `build`s the
`LogicFormula`, constructs `GenBuchiAutomaton`, and calls `gba.satSolve(leadIn, cycle)`.
`GenBuchiAutomaton::satSolve` (`satSolve.cc:42–106`): `maximallyCollapseStates` +
`sccAnalysis`, find a FAIR component, BFS to it (`bfsToFairComponent`), BFS accumulating
fairness (`bfsToMoreFairness`), BFS to close the cycle (`bfsToTarget`), then "roll" the
lead-in into the cycle where labels imply. `makeModel` (`satSolverSymbol.cc:203–229`)
renders each BDD label as a conjunction of (possibly negated) propositions via
`extractPrimeImplicant` (`:231–265`) → `model(leadInList, cycleList)`.

### 2.6 The conformance-load-bearing surface

The result is a term (`counterexample`/`model`/`true`/`false`) built from the op-hook
symbols; its bytes are fixed by three things, in decreasing "already-solved" order:
(a) the term pretty-printer — **already byte-exact in tnk**; (b) the **system state graph
enumeration + hash-consing order** — **already conformance-verified via `search`**;
(c) the **property-automaton state numbering + the nested-DFS traversal order** — the new,
determinism-critical work. See §4.

---

## 3. What tnk already has to build on

### 3.1 The special-op / id-hook seam (for `SatSolverSymbol` / `ModelCheckerSymbol`)

tnk models Maude's `special (id-hook …)` as `SpecialOp`
(`crates/tnk-core/src/symbol.rs:197–318`), dispatched by
`Runtime::try_special` (`builtin.rs:21–105`) before user equations
(`engine.rs:3706–3708`). Signature-time binding is `special_op`
(`crates/tnk-frontend/src/sig/build_sig.rs:690–872`); the current inert behavior is the
unknown-class fallback at `:864–869`, whose comment names `SatSolverSymbol`.
`op_hook_sym`/`term_hook_sym` are at `:632–663`; the many-hook precedent is
`MetaHooks` (`symbol.rs:423–431`) populated by `resolve_meta_hooks`
(`build_sig.rs:1081+`). This is the current post-Phase-T layout; M1–M4 do not touch it.

The `Theory` enum remains orthogonal: `modelCheck`/`satSolve` are free operators with an
additional special reduction, not new equational theories.

**M5 integration decision (post-M0 reorientation): both hooks stay kernel-direct.**
`modelCheck` operates on the current engine's rules, equations, DAG arena, and signature;
it does not need the module database that justifies the `DescentOps` up-call. Add
`SpecialOp::ModelCheck` and run it directly from `Runtime::try_special`, passing the
already-available `DescentOps` through any nested reductions. The one missing datum is a
rule's source label: share one `Rc<str>` between `CompiledRule` and `RlTrace` at
registration (an explicit labelled-rule API, while tests may retain the unlabelled
convenience API). This fixes the ownership boundary instead of routing the whole checker
through the meta-interpreter seam or duplicating label strings.

M7's `SpecialOp::SatSolve` is likewise kernel-direct and needs no rewriting. Both variants
carry dedicated typed hook structs resolved from `model-checker.maude:186–203,239–261`;
do not reuse the semantically unrelated meta hook map at runtime.

### 3.2 The state-graph / search machinery (the reused state-transition system)

tnk's `crates/tnk-core/src/search.rs` already reimplements Maude's
`StateTransitionGraph` as the `Search` struct (`search.rs:80–98`) — the module doc says it
"builds Maude's `StateTransitionGraph` on the fly." The state node (`State`,
`search.rs:32–47`) has exactly the fields the checker needs:

```rust
struct State {
    term: DagId,                         // reduced, canonical term (arena handle)
    _root: RootGuard,                    // pins `term` against GC
    parent: Option<usize>,               // BFS-tree predecessor  ← lead-in reconstruction
    via: Option<u32>,                    // rule id on the arc from parent
    fwd: BTreeMap<usize, BTreeSet<u32>>, // successor idx -> rule id(s)  ← Maude's ArcMap
    depth: u32,
    expanded: bool,
}
```

Reusable engine seams: `state_successors(root)` — every `(rule_id, successor)` one step
from root, all rules × positions (`engine.rs:4241+`, public wrapper `:6156+`);
`reduce_successor` — counts one rewrite and reduces (`:6167+`); `dag_hash` +
`deep_equal` for canonical hash-cons dedup. Lazy successor generation is in
`Search::step` (`search.rs:163–227`); an `Expanding` cursor (`search.rs:70–78`) already
yields successors one index at a time, matching Maude's
`getNextState(stateNr, index)` access pattern. During M5, put these operations behind one
crate-private, statically dispatched graph context implemented by both `Engine` (ordinary
search) and the active `Runtime`/`Signature` reduction view (model checking); do not copy
successor logic or allocate a trait object per edge.

**GC discipline (roadmap risk #9).** Each state pins its `DagId` with a per-state
`RootGuard` (`search.rs:35`, `206–211`; RAII registry `crates/tnk-core/src/root.rs:60–86`),
so the whole graph survives any collection while the session lives; and the REPL runs with
in-reduction GC off by default (`gc_interval: None`, `engine.rs:408–411`;
`lib.rs:65–68`). This is exactly "the same GC discipline the re-entrant reducer got" that
risk #9 asks the state graph to have. The model checker reuses it unchanged.

**Rule labels for `{state, ruleName}`.** The kernel currently stores only a dense `u32`
rule id (`CompiledRule`, `engine.rs:284–296); the textual label lives frontend-side as
`RlTrace.label: Option<String>`, indexed by rule id
(`crates/tnk-frontend/src/sig/syntax.rs:83–99`; invariant `load.rs:763–768`). M5 changes
that ownership once: convert the parsed label to `Option<Rc<str>>`, share it between
`CompiledRule` and `RlTrace`, and construct either the Qid or `unlabeled` directly in the
kernel. Existing trace/show-path rendering keeps reading `RlTrace`; no label lookup
callback and no duplicate string allocation remain.

**Three gaps in the current `Search` (all additive, none blocking):**
1. **No cycle in path reconstruction.** `Search::path` (`search.rs:282–300`) rebuilds the
   BFS-tree lead-in only; there is no cycle component. The model checker needs its own
   lasso reconstruction (§2.4) — the raw back-edges are already in `fwd`/`graph()`.
2. **No `deadlock` self-loop.** Successor-less states are just empty-`fwd` normal forms
   (`search.rs:177–180`, `243–248`); the checker must synthesize the deadlock self-loop
   itself (Maude's `getNextState` fake, §2.1) and the `deadlock` label.
3. **`Search` is BFS-/goal-oriented, the checker wants index access.** `Search::step`
   interleaves goal-testing and BFS ordering; the checker wants raw
   `get_next_state(state, index)`. See §6.4 for the recommended small refactor that lets
   both share one successor-generation code path (which is what *guarantees* the
   checker's system graph matches the conformance-verified `search` graph).

### 3.3 The BDD facade (D6 — already GO/binding)

D6 (`03-open-decisions.md:105–122`) selected pure-Rust `biodivine-lib-bdd` behind a
facade, and the S0 spike ratified it GO. **`LTL→Büchi labels` is one of the three named D6
consumers.** biodivine-lib-bdd is already a dependency (`crates/tnk-core/Cargo.toml:22`)
and is used by `SortBdds` (`crates/tnk-core/src/sort_bdds.rs`), whose `AllSat` walker
(`sort_bdds.rs:470–534`) is a working precedent for ROBDD traversal. The LTL construction
needs a *separate, small* BDD context (one `BddVariableSet` sized to the proposition count,
variable index = proposition index) and a handful of ops the sort facade does not yet
expose: `ithvar`/`nithvar`, `and`/`or`/`not`, structural `==`, and **root-variable +
low/high cofactor navigation** for `satisfiesPropositionalFormula`'s walk. All are directly
available on biodivine's `Bdd`/`BddNode` API; the plan is to expose them as a thin
`ltl::bdd` helper rather than force them into `SortBdds`.

### 3.4 The fixture harness and frozen baseline

`conformance/subsystems/M*.maude` run under `tools/subsystems-scoreboard.sh` (the same
`diffmaude.sh` normalization, 60s per side, `SUBSYSTEMS n/m PASS`). M0 froze
**M01–M10: 10 fixtures / 49 commands** on 2026-07-23; the exact manifest and source
enumeration are in §7 and `subsystems-goal.md` §2. Every fixture carries `*** PRELUDE`, so
the oracle and tnk both load the standing prelude plus `model-checker.maude`. The oracle
self-diff is 10/10; the inert-hook tnk baseline is intentionally 0/10 without load, parse,
or command-dispatch errors. F1 (`SCOREBOARD 77/77`) and F2 (`LEGACY 87/87`) continue to
gate every implementation commit.

---

## 4. Architectural fit & divergence analysis

### 4.1 The mapping is clean

| Maude C++ | tnk |
|---|---|
| `StateTransitionGraph` (`stateTransitionGraph.hh`) | `Search`'s state-graph core (`search.rs`), refactored to expose `get_next_state(state, index)` (§6.4) |
| `RewriteSearchState::findNextRewrite` | `Engine::state_successors` + `reduce_successor` (`engine.rs:2965–3023`, `3987`) |
| `HashConsSet` dedup | `dag_hash` + `deep_equal` + per-`Search` `index` (`engine.rs:3030`, `term.rs:322`, `search.rs:84`) |
| `ArcMap = map<int, set<Rule*>>` | `fwd: BTreeMap<usize, BTreeSet<u32>>` (`search.rs:42`) |
| `ModelChecker2::System` (virtual) | a Rust `trait System { fn next_state; fn check_proposition }` — the D3 "`dyn` at an open seam" idiom, or a concrete struct since there is exactly one impl |
| `LogicFormula`, VWAA, GBA, Büchi2, ModelChecker2 | new `crates/tnk-core/src/ltl/` module (self-contained; §6) |
| BuDDy `Bdd` | `biodivine-lib-bdd` (D6) |
| `NatSet` | a sorted-bitset newtype (or `BTreeSet<u32>`) with matching `Ord` |
| `IndexedSet<T>` | a `Vec<T>` + `HashMap<T,usize>` interner (equality by value incl. canonical BDDs) |
| `map<Key, …>` (ordered) | `BTreeMap<Key, …>` (Ord matching C++'s `<`) |

A8 §5 already prescribes this: *"PORT the algorithms (they are self-contained graph/automata
code, the least pointer-heavy part of Maude) … Nested DFS and SCC analysis are textbook
ports."* The `System` interface becomes a trait, decoupling the checker from the engine.

### 4.2 Where the divergences help

- **Instance-based engine (D1) + no BuDDy global state.** biodivine-lib-bdd is
  manager-less, which is exactly why D6 preferred it over BuDDy (BuDDy's global manager
  clashes with the multi-engine model). The LTL BDD context is a plain local value — no
  global init/teardown, no interaction with `SortBdds`' variable space.
- **The state graph is already rooted (D2).** Risk #9's concern ("the state graph needs the
  same GC discipline the re-entrant reducer got") is already discharged by `Search`'s
  per-state `RootGuard`s + default-off in-reduction GC. The checker inherits this.
- **Shared successor generation guarantees byte-exact system paths.** Because tnk's
  `search` (which produces byte-exact `show path`/`show graph`) and the model checker will
  share one successor-enumeration path (§6.4), the checker's system-graph enumeration
  *cannot* drift from the conformance-verified `search` behavior. This retires the single
  largest determinism risk before it starts.

### 4.3 The determinism decomposition (this is the whole game)

The counterexample is byte-exact iff **all** of the following match Maude; each is analyzed
honestly below.

1. **System state-graph enumeration order** — the order `getNextState(s,0), (s,1), …`
   yields successors, plus hash-cons dedup and parent back-links. **Already solved**:
   reused from the conformance-verified `search` machinery (§3.2, §4.2). One item to port:
   the **deadlock self-loop** (§3.2 gap 2). M0 also corrected a stale assumption here:
   `makeTransition` takes the first element of C++ `set<Rule*>`, whose pointer order is
   not process-stable for two differently-labelled rules reaching one target. A 12-pair
   Maude-3.5.1 oracle self-diff produced two first-label/second-label mismatches. M03
   therefore drives two rules into one arc with a shared visible label; differently-labelled
   arcs use tnk's deterministic lowest-source-rule-id representative and are not claimed as
   a byte-stable oracle surface (§8.4).
2. **Proposition → BDD-variable index map** — first-encounter order in `build`'s recursive
   descent (§2.1 step 2). **Easy and fully deterministic**: port the exact descent
   (`temporalSymbol.cc:126–196`); index a proposition on first sight; make BDD variable
   index = proposition index.
3. **Property-automaton state numbering + transition iteration order** — the output of
   VWAA→GBA→Büchi2 and the order the nested DFS visits transitions. **The hard part**, but
   *not* fundamentally non-deterministic. Key insight: **every ordering-sensitive container
   in the construction is keyed by state indices / `NatSet`s, never by BDD identity.** BDDs
   appear only as transition-label *values*; BDD equality is canonical in any ROBDD library
   (BuDDy and biodivine both), and all subsumption tests are semantic (`and`/`not`/`==false`).
   Therefore, **given a canonical ROBDD facade with variable order = proposition-index
   order, the automaton is identical regardless of BDD library** — biodivine reproduces
   BuDDy's automaton. What remains is a *faithful* port of the container orderings:
   `map<NatSet,Bdd>` → `BTreeMap` with matching `NatSet` `Ord`; `IndexedSet` → insertion-
   order interner with value-equality; Tarjan `sccAnalysis` DFS order; the degeneralization
   counter order. Any mismatch yields a **valid but different** lasso → FAIL. This is
   diligence, not research.
4. **Nested-DFS traversal order** — determined by (2)+(3): iterate the Büchi
   `TransitionMap` (`BTreeMap<u32,Bdd>` by target) and system successors by index; return
   the **first** accepting lasso. Deterministic once (2),(3) are; a direct port of
   `modelChecker2.cc`.
5. **Rewrite count** (a diffed conformance field, not just the value). Comes from: the
   negated-formula reduction + each `state|=prop` reduction + each successor reduction.
   The `state|=prop` count depends on `satisfiesPropositionalFormula`'s **lazy BDD walk +
   per-system-state memo** (`testedProps`/`trueProps`): a proposition is reduced at most
   once per system state, and only when the label-BDD walk actually reaches its variable.
   **tnk must port this walk faithfully** (root-var/low/high navigation + the `StateSet`
   memo), or the `rewrites:` line diverges even when the lasso is correct. This is why the
   facade must expose ROBDD navigation (§3.3), not just `AllSat`.

**Verdict:** determinism roots #1 and #2 are cheap/solved; #4 falls out of #3; the real
work and risk are concentrated in the *faithful* reproduction of #3 (container tie-breaks)
and #5 (the BDD-walk/memo for rewrite counts).

---

## 5. Feasibility & risk

**Overall: feasible, medium-to-high effort, concentrated risk.** A8 §5 calls this "the
least pointer-heavy part of Maude … ports almost verbatim and is good early Rust practice."
The reference is compact and self-contained: the entire Temporal engine is ~1.9k lines
(genBuchiAutomaton 241, vwaa 284, modelChecker2 193, buchiAutomaton2 258, sccAnalysis 197,
transitionSet 167, collapseStates 122, satSolve 271, logicFormula 261) plus ~0.9k of bridge.

**What lowers risk:**
- The system side (state graph, GC, rendering) is **done and verified** (§4.2).
- The BDD backend is **decided and spiked GO** (D6); LTL labels are a named consumer.
- Independence from S and T — no ordering dependency; can land in parallel (subsystems-goal:156).
- The pipeline is layerable with unit-testable seams at every stage (§6).

**What raises risk (honest):**
- **Byte-exact counterexample determinism (#3 above) is the headline risk.** The Büchi
  construction has many container-ordering tie-breaks (subsumption in `insertFairTransition`,
  IndexedSet numbering, Tarjan component order, degeneralization counter). Each must match
  Maude's `std::map`/`set` semantics precisely. A subtle mismatch produces a correct-but-
  different lasso that fails the fixture. Mitigation: port stage-by-stage with a `dump()`
  equivalent (Maude's automata all have `dump()` — `genBuchiAutomaton.cc:217`,
  `buchiAutomaton2.cc:232`, etc.) and diff the intermediate automata against
  `TDEBUG`-instrumented reference builds, not just the final bytes.
- **Rewrite-count exactness (#5)** requires porting the lazy BDD-walk + per-state memo, not
  a shortcut evaluation. Needs facade ROBDD navigation.
- **`satSolve`/`tautCheck` prime-implicant rendering** uses BuDDy `extractPrimeImplicant`
  (`satSolverSymbol.cc:242`); biodivine's clause/valuation extraction must reproduce the
  same conjunction (variable order + polarity) byte-for-byte in `model(...)`. This is a
  **distinct, arguably harder** rendering match than `modelCheck` (which needs no prime
  implicants). Recommend sequencing `satSolve` *after* `modelCheck` and treating its
  rendering as its own risk item / open question (§8).
- **The manifest is now seeded.** M0 retired the unseeded-contract risk with 10 fixtures /
  49 commands and exposed one real oracle limitation: a differently-labelled multi-rule
  arc has a process-dependent representative. The stable boundary is recorded in §7/§8.4.
- **BDD facade extension.** `SortBdds` doesn't expose the ops LTL needs; a small
  `ltl::bdd` helper (ithvar/nithvar/navigation) must be added and validated against
  biodivine's canonicity.

**Not a risk:** BDD-library choice affecting the automaton (canonicity settles it, §4.3);
state-graph memory (rooting + off-by-default GC handle it); the result rendering (standard
term printer).

---

## 6. Implementation plan (staged)

New code lives in `crates/tnk-core/src/ltl/` (self-contained automata pipeline + checker),
with hook binding in the frontend and an up-call seam mirroring `descent.rs`. **Nothing is
deferred**; sub-issues (facade ops, the `Search` refactor, deadlock self-loop) are called
out in the stage where they arise.

### Stage M0 — seed the fixture manifest — **DONE 2026-07-23**

M01–M10 enumerate the fresh probes, all terminating manual Chapter 12 examples, and all
four model-checker-gated reference-suite sources. They cover every LTL connective,
`LTL-SIMPLIFIER`, true/counterexample/nil-lead-in/deadlock/Qid/unlabeled output,
duplicate-rule arcs, LTL+, Dekker, both dining-philosophers encodings, and
`satSolve`/`tautCheck` model/false/prime-implicant output. The oracle self-diff is 10/10;
the production baseline is 0/10 solely at the two inert hooks. The manifest is frozen in
`subsystems-goal.md` §2 in the same commit as the fixtures. **Next: M1 only.**

#### Post-M0 serial cursor (binding)

| next | implementation slice | objective gate |
|---|---|---|
| **M1** | `LogicFormula` DAG, structural interning, exact `TemporalSymbol::build` descent and proposition indexing | source-verified unit cases; no production hook and no M fixture expected green |
| **M2** | local `ltl::bdd` facade: variables, Boolean ops, equality, root/low/high navigation | biodivine canonicity/navigation tests |
| **M3** | `TransitionSet`/raw product → VWAA → GBA/SCC/collapse → degeneralized Büchi | intermediate dump parity with an instrumented reference |
| **M4** | `ModelChecker2` nested DFS, lazy BDD proposition walk/memo, lasso split, `System` trait | known lassos over a synthetic system; still no production hook |
| **M5** | shared `StateGraph`, deadlock completion, typed hooks/up-call, result construction | M01 + M03 byte-exact target |
| **M6** | determinism closure, LTL+ path, large reference systems, typed verbose-stat event | M01–M09 byte-exact target |
| **M7** | GBA SAT BFS, prime implicants, `SatSolverSymbol`; pure `tautCheck` equations | M01–M10 10/10 plus frozen invariants |

Do not start M2 before M1's indexing contract, M3 before M2's BDD gate, or M5 before the
synthetic M4 checker is exact. M5 is the first stage allowed to change the production
M-scoreboard.

### Stage M1 — LogicFormula + `build` (determinism root #2)

Create `tnk-core/src/ltl/{mod.rs,formula.rs}`. Port `LogicFormula`
(`logicFormula.{hh,cc}`) as an append-only `Vec<FormulaNode>` plus a lookup-only structural
interner: a node id is still its first DFS insertion index, while repeated
`(op,arg0,arg1)` nodes reuse that id without the C++ linear scan. Return
`BuiltFormula { formula, root, propositions }`; omitting the root id from the API would
lose the value returned by `TemporalSymbol::build`.

Port `TemporalSymbol::build` (`temporalSymbol.cc:126–196`) exactly:

- `True`/`False` are propositional constants; unknown top symbols are whole atomic
  propositions and their children are **not** traversed.
- propositions are structurally interned by `dag_hash` + `deep_equal`, pinned by
  `RootGuard`, and numbered in first DFS encounter order;
- flattened associative `and`/`or` children are left-folded in stored argument order;
- `not` succeeds only when its built child is a `PROPOSITION`; `next`, `until`, and
  `release` are non-propositional; `and`/`or` are propositional iff both children are;
- malformed recognized operators return `None`, not a partial formula or atomic fallback.

Define the shared eight-symbol `TemporalHooks` value here but bind no production special
op. Unit tests must cover repeated/deep-equal proposition collapse, first-encounter
numbering, repeated formula-node sharing, n-ary left folding, every propositional flag,
unknown-subtree atomicity, and each malformed/rejected case.

**Gate:** focused tnk-core tests pass and the frozen M-scoreboard remains 0/10 for the same
inert-hook reason. No BDD code and no production hook in M1.

### Stage M2 — the `ltl::bdd` helper (facade extension)

Add ithvar/nithvar, and/or/not, `==`, and root-var/low/high navigation over a local
`BddVariableSet` sized to the proposition count (variable index = proposition index).
Validate canonicity against biodivine directly. This is the only new external-facing BDD
surface; keep it out of `SortBdds`.

### Stage M3 — the LTL→Büchi pipeline (determinism root #3)

Port, in order, each unit-tested against `dump()`-diffs of `TDEBUG` reference builds:
1. `TransitionSet` (`transitionSet.{hh,cc}`) — `BTreeMap<NatSet,Bdd>` with the subsumption-
   canonical `insert`/`product`; plus `RawTransitionSet` (`rawTransitionSet.cc`).
2. `VeryWeakAlternatingAutomaton` (`veryWeakAlternatingAutomaton.{hh,cc}`) — `dnf`,
   `computeTransitionSet`, `reachabilityOpt`, `computeFairnessSet`.
3. `GenBuchiAutomaton` (`genBuchiAutomaton.{hh,cc}` + `collapseStates.cc` +
   `sccAnalysis.cc` + `sccOptimizations.cc`) — the interner (`IndexedSet` analogue),
   `generateState`, `insertFairTransition`, Tarjan SCC, `simplify`.
4. `BuchiAutomaton2` (`buchiAutomaton2.{hh,cc}`) — degeneralization + `collapseStates`.

### Stage M4 — the nested DFS + `System` trait (determinism root #4)

Port `ModelChecker2` (`modelChecker2.{cc,hh}`): the product `intersectionStates`, DFS1/DFS2,
`satisfiesPropositionalFormula` (the lazy BDD walk + per-state memo — determinism root #5),
and lasso recovery (`path`/`cycle` + `swap`). Define `trait System`. **Unit-test against a
synthetic `System`** (a fixed tiny transition graph + a proposition oracle) with
known-answer automata, independent of the rewrite engine.

### Stage M5 — first vertical slice: shared graph + hooks + M01/M03

1. Extract `Search`'s graph fields and successor quantum into `StateGraph`
   (`get_next_state`, `state_dag`, `fwd_arcs`); `Search` retains only BFS/goal logic.
   The checker wrapper adds the **deadlock self-loop** without changing ordinary search.
2. Implement `System` over that graph. `check_proposition` reduces
   `satisfies(state, proposition)` through `MetaCtx`, compares with `trueTerm`, and charges
   the subcontext rewrites exactly once.
3. Add typed `ModelCheckerHooks` and `SpecialOp::ModelCheck`, bind
   `"ModelCheckerSymbol"` immediately before the unknown-class fallback at
   `build_sig.rs:864`, and run it directly in `Runtime::try_special`. Introduce the
   labelled-rule registration path and shared `Rc<str>` ownership described in §3.2.
4. Build `counterexample`/transition/list/Qid/unlabeled/deadlock terms from the resolved
   hooks, or return `trueTerm`.
5. Record typed `(property_automaton_states, examined_system_states)` events during every
   check. M6 teaches the REPL's existing `set verbose` path to render the exact two
   `ModelChecker:` lines; core code does not print.

**Gate:** M01 and M03 byte-exact, including rewrite counts, deadlock, unlabeled/Qid labels,
nil/nonempty lead-ins, and the deterministic shared-label duplicate-rule arc. Retained
search fixtures must remain unchanged.

### Stage M6 — close `modelCheck` / `modelCheck+` (M01–M09)

Turn on M02 and M04–M09 one at a time; diff determinism against instrumented reference
automata. This includes all LTL operators and simplifier equations, MUTEX, round-robin,
LTL+ witness inversion, Dekker's 9+2 lasso, both 459-state dining counterexamples, exact
48,194 rewrite counts, and the verbose property/system-state statistics in M05/M08/M09.
**Gate:** M01–M09 pass together; M10 remains the only expected failure.

### Stage M7 — `satSolve` / `tautCheck` (sibling; separate risk)

Reuse `GenBuchiAutomaton` (do not degeneralize); port `GenBuchiAutomaton::satSolve`
(`satSolve.cc`) — the three BFS passes + lead-in rolling — and `SatSolverSymbol`'s
`makeModel`/`makeFormula` prime-implicant rendering. Bind `"SatSolverSymbol"` in
`special_op`. This is where the BuDDy-vs-biodivine prime-implicant match must be nailed
(§8). `tautCheck` and `LTL+`/`MODEL-CHECKER+` are **pure prelude equations** — they work
automatically once `satSolve`/`modelCheck` do; just verify.

### 6.3 Why there is no new upper call

`modelCheck` uses only the current engine: its rewrite rules, equational reducer, DAG
arena, and the symbols/terms resolved by its own hook attachment. Rule labels become
shared kernel metadata at registration. Therefore `Runtime::try_special` can run the
checker and pass its existing `DescentOps` argument through nested reductions; extending
`MetaCtx` or `MetaDescent` would couple an ordinary built-in to the module database for no
semantic reason. `satSolve` is simpler still: it consumes only its formula DAG and result
hooks.

### 6.4 The `Search` refactor (called out, not deferred)

To *guarantee* the checker's system graph matches the conformance-verified `search` graph
(and to avoid a second, drifting copy of successor generation), extract the common core
from `Search` — expand-state → enumerate (`state_successors`) → reduce (`reduce_successor`)
→ hash-cons (`dag_hash`/`deep_equal`) → record `fwd`/`parent` + `RootGuard` — into a shared
`StateGraph` exposing `get_next_state(state, index) -> Option<usize>`, `state_dag`,
`fwd_arcs`. `Search` becomes `StateGraph` + goal/BFS/`such_that` logic; the checker uses
`StateGraph` directly with the deadlock self-loop added. This is a mechanical, test-covered
refactor (the `search` fixtures regression-guard it).

---

## 7. Verification

**Oracle-diff harness (unchanged).** `tools/subsystems-scoreboard.sh` over
`conformance/subsystems/M*.maude`, each transcribed from
`MAUDE_LIB=~/code/maude-lang/maude/src/Main ~/.local/bin/maude -no-banner <f> < /dev/null`.
Diff result value, **result sort**, **rewrite count**, termination, and — the phase-M
hard requirement — **byte-for-byte** the `counterexample`/`model` text.

**Frozen M0 manifest (2026-07-23):**

| fixture | commands | frozen contract |
|---|---:|---|
| `M01-toggle` | 3 | smallest `true`, Qid-labelled lead-in/cycle, and `nil` lead-in cases (`10/7/10` rewrites) |
| `M02-ltl-operators` | 17 | all eight primitive and eight derived LTL connectives, unlabeled arcs, plus an `LTL-SIMPLIFIER` rule entering the checker |
| `M03-deadlock-multi-rule` | 2 | synthesized `deadlock` self-loop and two rules reaching one arc with a stable shared label |
| `M04-manual-mutex` | 7 | every executable manual §12.3 MUTEX check: six `true`, one exact counterexample |
| `M05-manual-rrobin` | 3 | manual §12.5 and reference `ObjectOriented/rrobin`: two `true`, one long exact lasso, including verbose checker statistics |
| `M06-manual-ltl-plus` | 1 | manual §12.6 existential `modelCheck+` result: exact 9-transition lead-in plus deadlock witness |
| `M07-reference-dekker` | 3 | exact `tests/Misc/dekker`: safety `true`, 9+2 unlabeled lasso, fairness `true` |
| `M08-reference-dining-philosophers5` | 3 | exact source, including setup reduce/search and the 459-state, 48,194-rewrite counterexample |
| `M09-reference-dining-philosophers6` | 3 | alternate Oid encoding of the same complete reference test and exact counterexample |
| `M10-sat-taut` | 7 | `model(b,True)`, `false`, four tautology outcomes, manual prime implicant `model(a ; b,(~ c) ; c)`, and exact tautology counterexample |

Total: **10 fixtures / 49 commands**. `TNK_BIN=~/.local/bin/maude
tools/subsystems-scoreboard.sh -p M` reports **10/10 PASS**. The production release
reports **0/10**, with every file accepted and the two special-hook applications left
unreduced as expected before M1–M7.

**Source enumeration and exclusions.** The reference-suite model-checker denominator is
`Misc/dekker` plus `ObjectOriented/rrobin`, `dining-philosophers5`, and
`dining-philosophers6`; all four are included. The terminating manual Chapter 12 command
families are MUTEX (§12.3), SAT/tautology (§12.4), round-robin (§12.5), and LTL+ (§12.6);
all are included. The manual's `MODEL-CHECK-BAD-EX` is the sole exclusion: it intentionally
demonstrates nontermination on an infinite reachable-state set, so it cannot satisfy the
60-second per-side harness contract. No reference-suite model-checker file is excluded.

The denominator may grow but may not shrink or weaken without a recorded user decision.
For the differently-labelled multi-rule-arc limitation discovered while freezing M03,
see §8.4.

**Unit tests (below the oracle, for the determinism-critical internals):**
- `build`/`LogicFormula`: descent order + proposition indexing on hand-written formulas.
- Büchi construction: diff the ported `dump()` output against `TDEBUG`-instrumented
  reference builds of `VeryWeakAlternatingAutomaton`/`GenBuchiAutomaton`/`BuchiAutomaton2`
  for a battery of formulas (the intermediate-automaton diff catches tie-break drift long
  before the final bytes do).
- Nested DFS: known-answer lassos on synthetic `System`s (no rewrite engine), including the
  Holzmann–Peled–Yannakakis textbook examples.
- `ltl::bdd`: canonicity + navigation against biodivine directly.

**Naive cross-check (optional, high-value for confidence, not for conformance):** since a
counterexample lasso is a concrete run, validate that the *returned* lead-in+cycle actually
(a) is a real path in the state graph and (b) violates the formula — a cheap independent
oracle that catches "wrong-but-plausible" lassos distinct from the byte diff. (Maude's own
`dekker.expected` documents "9 state lead in to a 2 state cycle" as a sanity anchor.)

---

## 8. Bound constraints and early gates

1. **LTL→Büchi algorithm — bound.** Port the reference Gastin–Oddoux pipeline exactly (VWAA → GBA →
   degeneralized Büchi, plus the Somenzi–Bloem SCC optimization). Byte-exact counterexamples make the
   automaton and traversal order part of the spec; an alternative valid construction is not conformant.
2. **BDD backend gate.** Before the full port, diff intermediate automaton dumps for a formula battery
   using proposition-index variable order. If `biodivine-lib-bdd` does not reproduce the reference
   structure/order through the facade, use D6's recorded BuDDy-FFI escape hatch. Do not discover this
   only at final lasso rendering.
3. **`satSolve`/`tautCheck` ordering — bound.** Implement after `modelCheck` (M7), but it may not lag the
   completed M denominator. Its BuDDy prime-implicant polarity/order is a byte-visible contract; seed
   it separately and finish exact `model(...)` rendering before phase M closes.
4. **Multi-rule arc labels — determinized boundary.** M03 seeds two rules/one target with a
   shared visible label. A probe with different labels proved Maude 3.5.1's `set<Rule*>`
   representative process-dependent (two mismatches in 12 oracle self-diffs), so no
   byte-exact fixture may depend on which label wins. Keep tnk deterministic by selecting
   the lowest source rule id, retain every rule in `fwd_arcs`, and unit-test that set
   internally when the shared `StateGraph` lands.
5. **Shared `StateGraph` refactor — bound yes.** Extract successor generation from the already
   conformance-verified `Search`; do not build a second rewrite graph for the checker. Existing search
   fixtures guard the mechanical refactor, and M0 adds deadlock/self-loop coverage.
6. **`LTL-SIMPLIFIER`.** No checker-specific implementation: ordinary reduction already handles its
   equations. Include at least one M0 fixture proving the reduced formula enters the identical
   automaton/checker pipeline.
