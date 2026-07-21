# 05 — Model checking (phase M / roadmap G4)

**Subsystem.** LTL model checking of rewrite systems: an LTL formula is turned into a
Büchi automaton (Gastin–Oddoux), the product of that automaton with the rewrite
state-transition system is searched for an accepting cycle by nested DFS, and a
**counterexample lasso** (lead-in prefix + cycle) is returned. Plus the sibling LTL
satisfiability/tautology solver (`satSolve`/`tautCheck`).

**Status when this plan was written.** No temporal / model-checking code exists in tnk.
`modelCheck`/`satSolve`/`counterexample`/`Büchi` appear nowhere in the tree except one
comment naming `SatSolverSymbol` at
`crates/tnk-frontend/src/sig/build_sig.rs:716`. The `MODEL-CHECKER` prelude's two
`special` operators are currently **declared-inert**: their id-hooks fall through the
graceful-degrade arm `_other => return Ok(None)` at `build_sig.rs:720`, so
`model-checker.maude` *loads* but `modelCheck(...)` never reduces. This subsystem is
**independent of phase S (symbolic) and phase T (SMT)** (subsystems-goal §2, line 156:
"independent of S and T; may interleave with T") and can proceed in parallel.

**Pass criterion (the hard part).** subsystems-goal §2 (lines 158–160): counterexample
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

tnk models Maude's `special (id-hook …)` as a typed enum `SpecialOp`
(`crates/tnk-core/src/symbol.rs:180–285`), stored as `Symbol.special: Option<SpecialOp>`
(`symbol.rs:99`), dispatched by `match` in `Runtime::try_special`
(`crates/tnk-core/src/builtin.rs:21–68`), which is called from `Engine::try_rewrite_top`
before user equations (`crates/tnk-core/src/engine.rs:2631–2659`) — this is Maude's
`eqRewrite`. Binding happens at signature-build time in `special_op`
(`crates/tnk-frontend/src/sig/build_sig.rs:585–723`), a `match` on the id-hook class name;
unrecognized classes hit the graceful-degrade `_other => return Ok(None)` at
**`build_sig.rs:720`** (its comment at `:716` already names `SatSolverSymbol`). Op-hook /
term-hook symbols are resolved by helpers `op_hook_sym` (`:534–547`), `term_hook_sym`
(`:549–557`), and — for the many-hook case — the `MetaHooks` map pattern
(`symbol.rs:354–358`, populated by `resolve_meta_hooks` `:813–828`; shared across ops via
`find_canonical_meta_hooks` `:790–806`). Binding is finalized by
`engine.set_special(sym, op)` (`build_sig.rs:392` → `Signature::set_special`
`engine.rs:781`).

The `Theory` enum (`symbol.rs:35–51`) is **orthogonal**: it classifies equational axioms
(Free/Acu/Au/Cui/S) to pick DAG rep + matcher. A `modelCheck` op is a `Free` operator that
additionally carries a `SpecialOp` — the `Theory` enum is untouched.

**Crucially, the up-call seam already exists.** `SpecialOp::Meta` (META-LEVEL descent) does
not compute in the kernel — it up-calls through `trait DescentOps`
(`crates/tnk-core/src/descent.rs:102–113`) implemented in the frontend, handed a `MetaCtx`
façade (`descent.rs:27–98`) over `(&Signature, &mut Runtime)`. Model checking is the same
shape (it must drive the rewrite engine to build the state graph), so it follows the
`Meta` precedent (§6.3), not the pure-kernel `NumberOp` precedent.

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

Reusable engine seams (all public on `Engine`): `state_successors(root)` — every
`(rule_id, successor)` one step from root, all rules × positions
(`engine.rs:3978–3982`, internal `2965–3023`); `reduce_successor` — counts one rewrite and
reduces (`engine.rs:3987–3990`); `dag_hash` (`:3971`, `:3030–3066`) + `deep_equal`
(`:4443`, `term.rs:322–376`) — canonical hash-cons dedup. Lazy successor generation is in
`Search::step` (`search.rs:163–219`); an `Expanding` cursor (`search.rs:70–78`) already
yields successors one index at a time, which is exactly Maude's
`getNextState(stateNr, index)` access pattern.

**GC discipline (roadmap risk #9).** Each state pins its `DagId` with a per-state
`RootGuard` (`search.rs:35`, `206–211`; RAII registry `crates/tnk-core/src/root.rs:60–86`),
so the whole graph survives any collection while the session lives; and the REPL runs with
in-reduction GC off by default (`gc_interval: None`, `engine.rs:408–411`;
`lib.rs:65–68`). This is exactly "the same GC discipline the re-entrant reducer got" that
risk #9 asks the state graph to have. The model checker reuses it unchanged.

**Rule labels for `{state, ruleName}`.** The kernel stores only a dense `u32` rule id
(`CompiledRule.id`, `engine.rs:95–107`); the textual label lives frontend-side as
`RlTrace.label: Option<String>`, indexed by rule id
(`crates/tnk-frontend/src/sig/syntax.rs:85–95`; invariant `load.rs:375–376`). So
`rl_traces[id].label` gives `Some(qid)` (a `Qid`) or `None` (`unlabeled`). Rendering
precedent: `trace::rule_body`/`rl_body` (`crates/tnk-repl/src/trace.rs:131–142`, `410–427`).

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

### 3.4 The fixture harness

`conformance/subsystems/*.maude` run by `tools/subsystems-scoreboard.sh` (same
`diffmaude.sh` harness/normalization, 60s/fixture, prints `SUBSYSTEMS n/m PASS`, exit 0 iff
n=m). ID prefix for model checking is **`M*`**. Naming follows the phase-S convention:
manual-chapter fixtures `M-ch12-NN-slug`, fresh probes `M-probe-NN-slug`, plus `dekker`.
The §5 ledger line `- [ ] M model checker —` (subsystems-goal:232) gets a commit hash when
done. The always-green invariants F1 (`SCOREBOARD 77/77`) and F2 (`LEGACY 87/87`) gate
every commit.

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
   the **deadlock self-loop** (§3.2 gap 2). One edge case: `makeTransition` takes the label
   of the *first rule* in the arc's rule-set; Maude's `set<Rule*>` orders by pointer
   (≈ declaration order ≈ id order), tnk's `BTreeSet<u32>` orders by id — these agree
   except in the rare case where one target state is reached by two **differently-labeled**
   rules; flag as a known edge case (dekker: all unlabeled; toggle: one rule per arc).
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
- **Unseeded fixtures.** Phase M's manifest does not exist yet (subsystems-goal §2 has
  prose but no `M*` list; only phase S is frozen). Seeding is **step 0** of the work and
  is itself load-bearing: the fixtures define "done," and each must be oracle-verified.
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

### Stage M0 — seed the fixture manifest (phase M step 0; do first)

Enumerate, oracle-verify (expect FAIL initially), and **freeze into subsystems-goal §2 in
the same commit as the fixtures** (per the goal's discipline, §1.2). Sources: the toggle
probes from §1.3; `tests/Misc/dekker`; `tests/ObjectOriented/dining-philosophers5`; the
Maude manual ch.12 worked examples; fresh minimal probes covering each LTL operator,
`true`/`counterexample`, `nil` lead-in, `deadlock`, `unlabeled` vs `Qid`, and (for later)
`satSolve`/`tautCheck`/`model`/`false`. See §7 for the concrete list. The `M*` denominator
in `subsystems-scoreboard.sh` grows accordingly.

### Stage M1 — LogicFormula + `build` (determinism root #2)

Port `LogicFormula` (`logicFormula.{hh,cc}`: the node DAG with `makeProp`/`makeOp` +
propositional flag + structural sharing) and `TemporalSymbol::build`
(`temporalSymbol.cc:126–196`) as a function `DagId → (LogicFormula, PropTable)` given the
resolved LTL op-hook symbols. Unit-test the descent + proposition indexing on hand-written
formulas. No BDDs yet.

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

### Stage M5 — first vertical slice: wire to the state graph + hooks; byte-exact toggle

1. **Refactor `Search`** (§6.4) to expose a shared `get_next_state(state, index)` +
   `state_dag` + `fwd_arcs` core; add the **deadlock self-loop**.
2. Implement `System` for the tnk state graph (the `SystemAutomaton` analogue): `next_state`
   via the shared core; `check_proposition` reduces `satisfies_sym(stateDag, propDag)` in a
   sub-context and compares to the `true` term (counting rewrites like Maude).
3. Add `SpecialOp::ModelCheck { hooks: Rc<McHooks> }` (`symbol.rs`), the `try_special`
   up-call arm (`builtin.rs`), and the `"ModelCheckerSymbol"` id-hook arm in `special_op`
   just above `build_sig.rs:720`; resolve the op/term hooks with the `resolve_meta_hooks`
   pattern. Drive it through a new `DescentOps`-style trait (or an extension) implemented in
   the frontend, since it must build the state graph (§6.3).
4. `make_counterexample`: build the `counterexample`/`transition`/`transitionList`/`qid`/
   `unlabeled`/`deadlock` terms from the resolved hooks; return `true` term otherwise.
   **Target: byte-exact on the toggle fixtures** (§1.3) — the smallest end-to-end slice.

### Stage M6 — scale to dekker + the manual examples

Turn on the seeded `M*` fixtures one at a time; diff and fix determinism tie-breaks
(§4.3 #3) against `dump()`-instrumented reference automata. dekker's liveness case has a
9-state lead-in + 2-state cycle (`dekker.maude:199`) — a real stress of the lasso recovery
and label rendering.

### Stage M7 — `satSolve` / `tautCheck` (sibling; separate risk)

Reuse `GenBuchiAutomaton` (do not degeneralize); port `GenBuchiAutomaton::satSolve`
(`satSolve.cc`) — the three BFS passes + lead-in rolling — and `SatSolverSymbol`'s
`makeModel`/`makeFormula` prime-implicant rendering. Bind `"SatSolverSymbol"` in
`special_op`. This is where the BuDDy-vs-biodivine prime-implicant match must be nailed
(§8). `tautCheck` and `LTL+`/`MODEL-CHECKER+` are **pure prelude equations** — they work
automatically once `satSolve`/`modelCheck` do; just verify.

### 6.3 Why the up-call (not pure-kernel) shape

`modelCheck` must build the state-transition graph by *rewriting*, so it cannot compute
from the redex alone (unlike `NumberOp`). It follows the `SpecialOp::Meta` precedent
(`builtin.rs:60–63` → `descent.rs`): the resolved LTL op-hook symbols ride in an
`Rc<McHooks>` on the variant (like `Rc<MetaHooks>`), and the kernel up-calls a
frontend-implemented trait handed a `MetaCtx`-style façade. This keeps the automata code in
tnk-core while the engine-driving glue sits where the module DB / search bridge already live.

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

**Fixtures to seed (Stage M0)** — proposed `M*` manifest:
- `M-probe-01-toggle-true` — `modelCheck({zero},[]<> p0)` ⇒ `true` (smallest true case).
- `M-probe-02-toggle-ce` — `modelCheck({zero},[] p0)` ⇒ `counterexample({{zero},'flip0}, …)`
  (smallest counterexample; exercises `Qid` labels + lead-in + cycle).
- `M-probe-03-toggle-nil-leadin` — `modelCheck({zero},<> [] p1)` ⇒ `counterexample(nil, …)`.
- `M-probe-04-deadlock` — a machine with a terminal state under a liveness formula ⇒
  `deadlock` transition (exercises the self-loop synthesis).
- `M-probe-05..NN` — one per LTL operator (`U`,`R`,`O`,`<>`,`[]`,`W`,`|->`,`=>`,`<->`) as
  small `modelCheck` cases, including `unlabeled` rules.
- `M-ch12-01..NN` — the Maude 3.5.1 manual ch.12 worked model-checking examples.
- `M-dekker` — `tests/Misc/dekker` (safety `true`, liveness 9+2 counterexample, fairness `true`).
- `M-dining-philosophers5` — `tests/ObjectOriented/dining-philosophers5` (OO + `modelCheck`).
- `M-sat-01..NN` / `M-taut-01..NN` (Stage M7) — `satSolve`/`tautCheck` cases:
  `satSolve(a U b)⇒model(b,True)`, `satSolve(a/\~a)⇒false`, `tautCheck(a->a)⇒true`,
  `tautCheck([]a->a)⇒true`, plus `LTL+`/`MODEL-CHECKER+` `E_`/`A_`/`witness` cases.

Every seeded fixture is oracle-verified at authoring and **expected to FAIL initially**;
the manifest is frozen by appending the `M*` list to subsystems-goal §2 in the same commit
as the fixtures (denominator may grow later, never shrink/weaken without a recorded decision).

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

## 8. Open questions / decisions

1. **LTL→Büchi algorithm choice.** Recommendation: **port Gastin–Oddoux exactly** (VWAA →
   GBA → degeneralized Büchi, + Somenzi–Bloem SCC opt), as the roadmap G4 specifies and the
   reference implements. Rationale: byte-exact counterexamples require the *same* automaton
   the reference builds; an alternative construction (e.g. LTL2BA/ltl3ba/Spot-style) would
   produce different (valid) lassos and fail conformance. This is not really open — it is
   forced by the pass criterion — but worth recording as a ratified constraint: **the
   algorithm is part of the spec, not an implementation choice.**
2. **BDD canonicity ⇒ automaton determinism.** The plan asserts (§4.3 #3) that a canonical
   ROBDD facade with variable-order = proposition-index-order reproduces Maude's automaton
   regardless of library, because no ordering-sensitive container is keyed by BDD identity.
   This should be **empirically confirmed early** via the intermediate-`dump()` diff on a
   formula battery before committing to the full port. If it fails, fall back to BuDDy-FFI
   (D6 keeps it as a recorded escape hatch) — but this is not expected.
3. **`satSolve` prime-implicant rendering fidelity.** BuDDy's `extractPrimeImplicant` output
   order/polarity must be reproduced by biodivine's clause/valuation extraction to make
   `model(...)` byte-exact. This is the least-certain sub-target. **Decision to record:**
   sequence `satSolve`/`tautCheck` *after* `modelCheck` (Stage M7), and if the prime-
   implicant match proves fiddly, seed its fixtures but let that sub-metric lag `modelCheck`
   (the primary G4 deliverable) rather than block it.
4. **The multi-rule arc-label edge case (§4.3 #1).** When one target state is reached by two
   differently-labeled rules, Maude prints the pointer-first rule's label; tnk prints the
   min-id rule's label. Confirm these agree on the seeded fixtures; if a manual example
   exercises it and diverges, decide whether to match Maude's pointer order explicitly.
   (Low priority — no seeded fixture is known to hit it.)
5. **`Search` refactor scope (§6.4).** Confirm the extract-shared-`StateGraph` refactor is
   acceptable now (recommended: yes — it prevents a drifting second copy of successor
   generation and is regression-guarded by the existing `search` fixtures) versus a
   standalone graph for the checker.
6. **The `LTL-SIMPLIFIER` interaction.** It is optional prelude equations; when a user
   includes it, the formula reduces to a smaller NNF and the automaton (and possibly the
   lasso) changes. Since it is pure order-sorted reduction that tnk already does
   byte-exactly, no model-checker-specific work is needed — but fixtures should include at
   least one `including LTL-SIMPLIFIER` case to confirm the reduced formula feeds the
   pipeline identically.
