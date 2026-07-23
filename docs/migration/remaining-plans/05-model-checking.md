# 05 — Model checking (phase M / roadmap G4)

**Subsystem.** LTL model checking of rewrite systems: an LTL formula is turned into a
Büchi automaton (Gastin–Oddoux), the product of that automaton with the rewrite
state-transition system is searched for an accepting cycle by nested DFS, and a
**counterexample lasso** (lead-in prefix + cycle) is returned. Plus the sibling LTL
satisfiability/tautology solver (`satSolve`/`tautCheck`).

**Status: COMPLETE (2026-07-23); M1–M7 implemented and the Phase-M gate is closed.**
The frozen manifest remains 10 fixtures / 50 commands. Both `ModelCheckerSymbol` and
`SatSolverSymbol` are kernel-direct; every result value, sort, rewrite count, verbose
line, counterexample lasso, SAT model, and prime implicant is byte-exact. The current
default pure-Rust release reports **M01–M10 10/10 PASS**. Phase M remains independent of
completed S and T (`subsystems-goal.md` §2).

**Pass criterion (the hard part).** Per `subsystems-goal.md` §2, counterexample
output must be **byte-exact** to the reference — *"paths are deterministic; they are the
pass criterion, not just the verdict."* This elevates the README's "(where it matters)
byte-for-byte output" to a hard requirement for phase M. A logically-correct but
*different* lasso is a FAIL.

**Authority and conflict rule for the Phase-M `/goal`.**

- **Behavioral truth:** the frozen `conformance/subsystems/M*.maude` bytes and live Maude
  3.5.1 oracle, then the C++ sources under `~/code/maude-lang/Maude/src/{Temporal,Higher,Utility}`.
- **Rust design and scope:** this file, the Phase-M subsection of `subsystems-goal.md`, and
  binding decisions D1/D6 in `03-open-decisions.md`.
- **Current status:** the code and harness results, then the Phase-M ledger in
  `subsystems-goal.md`.
- `reports/A8-symbolic-smt-ltl.md`, `01-architecture-map.md`, completed plans 01–04, and
  closed goal documents are historical background only. Their proposed layouts, fallback
  choices, or old cursors never override this plan.

If a historical document conflicts, follow the authority above and correct the stale
summary in the same stage. **The active goal is exactly M1–M7; stop before Phase I,
meta-interpreters, external IO, or unrelated roadmap work.**

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

### 3.2 The shared state graph / search machinery — implemented

`crates/tnk-core/src/search.rs` now factors the reachable-state machinery into
`StateGraph`; ordinary `Search` retains only BFS, goal matching, bounds, and continuation,
while model checking implements the same crate-private `GraphContext` over the active
`Runtime`/`Signature` reduction view. Dispatch is static—there is no trait object per edge
and no second successor implementation.

Each canonical state owns its `RootGuard`, BFS predecessor/rule, deterministic
`BTreeMap<state, BTreeSet<rule>>` arcs, and first-result successor order. Raw rewrite
results are materialized as a rooted `VecDeque<RawSuccessor>` because the matcher cannot
retain borrows across checker calls. `Runtime::state_successors_deferred` timestamps the
equational work at each accepted matcher result, restores the live rewrite counter, and
records the final exhaustion tail. `StateGraph::get_next_state` replays only the prefix it
actually consumes, then counts and normalizes that rule result. Asking beyond the final
ordinal replays the tail. This reproduces Maude's lazy `findNextRewrite` accounting while
keeping every pending DAG live across proposition reductions and GC safe points.

Duplicate raw rewrites still count and add their rule ids to the shared arc, but only a new
canonical target advances the ordinal successor view. `dag_hash` plus `deep_equal`
provides hash-consing; `RootGuard` pins both canonical states and pending raw results.
Ordinary bounded search and `continue` use the same incremental commit path, so the
model-checking fix did not create a second counting convention.

Rule labels are shared `Rc<str>` metadata between `CompiledRule` and frontend `RlTrace`.
The kernel therefore constructs Qid labels or `unlabeled` directly without a frontend
callback or duplicate label allocation. The checker supplies the two model-specific
operations on top of the shared graph: deterministic lasso reconstruction and the
synthetic `deadlock` self-loop.

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
available on biodivine's `Bdd`/`BddNode` API; M2 exposes them through the dedicated
`ltl::bdd` helper rather than coupling temporal code to `SortBdds`.

### 3.4 The fixture harness and frozen baseline

`conformance/subsystems/M*.maude` run under `tools/subsystems-scoreboard.sh` (the same
`diffmaude.sh` normalization, 60s per side, `SUBSYSTEMS n/m PASS`). M0 froze
**M01–M10: 10 fixtures / 50 commands** on 2026-07-23; the exact manifest and source
enumeration are in §7 and `subsystems-goal.md` §2. Every fixture carries `*** PRELUDE`, so
the oracle and tnk both load the standing prelude plus `model-checker.maude`. The oracle
self-diff and current production release are now 10/10. M0's historical inert-hook
production baseline was 0/10 without load, parse, or command-dispatch errors. F1
(`SCOREBOARD 77/77`) and F2 (`LEGACY 87/87`) gated every implementation commit.

---

## 4. Architectural fit & divergence analysis

### 4.1 The mapping is clean

| Maude C++ | tnk |
|---|---|
| `StateTransitionGraph` (`stateTransitionGraph.hh`) | `Search`'s state-graph core (`search.rs`), refactored to expose `get_next_state(state, index)` (§6.4) |
| `RewriteSearchState::findNextRewrite` | `Engine::state_successors` + `reduce_successor` (`engine.rs:2965–3023`, `3987`) |
| `HashConsSet` dedup | `dag_hash` + `deep_equal` + per-`Search` `index` (`engine.rs:3030`, `term.rs:322`, `search.rs:84`) |
| `ArcMap = map<int, set<Rule*>>` | `fwd: BTreeMap<usize, BTreeSet<u32>>` (`search.rs:42`) |
| `ModelChecker2::System` (virtual) | `trait System`, consumed through a generic parameter (`S: System`); no `Box<dyn System>` or per-edge virtual allocation |
| `LogicFormula`, VWAA, GBA, Büchi2, ModelChecker2 | new `crates/tnk-core/src/ltl/` module (self-contained; §6) |
| BuDDy `Bdd` | `biodivine-lib-bdd` 0.5.27, engine-local and mandatory (D6) |
| `NatSet` | `ltl::NatSet`: inline `u64` first word + normalized `Vec<u64>`, with the reference's exact length/word `Ord`; **not** `BTreeSet` ordering |
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
- **`satSolve`/`tautCheck` prime-implicant rendering** uses the recursive algorithm in
  `Utility/bdd.cc:31–49`, followed by the variable-order walk in
  `Higher/satSolverSymbol.cc:231–265`. Port those operations exactly over biodivine;
  an arbitrary satisfying valuation or library convenience clause is not conformant.
  This is a distinct bound M7 risk, sequenced after `modelCheck`, not an open design
  question.
- **The manifest is now seeded.** M0 retired the unseeded-contract risk with 10 fixtures /
  50 commands and exposed one real oracle limitation: a differently-labelled multi-rule
  arc has a process-dependent representative. The stable boundary is recorded in §7/§8.4.
- **BDD facade extension.** `SortBdds` doesn't expose the ops LTL needs; a small
  `ltl::bdd` helper (ithvar/nithvar/navigation) must be added and validated against
  biodivine's canonicity.

**Not a risk:** BDD-library choice affecting the automaton (canonicity settles it, §4.3);
state-graph memory (rooting + off-by-default GC handle it); the result rendering (standard
term printer).

---

## 6. Implementation plan (staged)

New code lives in `crates/tnk-core/src/ltl/` (self-contained automata pipeline + checker);
the frontend resolves typed hooks and both special reductions execute kernel-direct in
`Runtime::try_special` (§3.1). There is no new upper-call seam. **Nothing is deferred**;
facade ops, exact set ordering, the `Search` refactor, deadlock self-loop, verbose events,
and prime-implicant extraction land in their named stages.

### Stage M0 — seed the fixture manifest — **DONE 2026-07-23**

M01–M10 enumerate the fresh probes, all terminating manual Chapter 12 examples, and all
four model-checker-gated reference-suite sources. They cover every LTL connective,
`LTL-SIMPLIFIER`, true/counterexample/nil-lead-in/deadlock/Qid/unlabeled output,
duplicate-rule arcs, LTL+, Dekker, both dining-philosophers encodings,
`satSolve`/`tautCheck` model/false/prime-implicant output, and the SatSolver verbose
statistics. The oracle self-diff is 10/10. At the M0 checkpoint the production baseline was
0/10: both applications were inert, and M10 lacked the hook-owned verbose event and
identity-collapse lines. That historical baseline is superseded by the status at the top of this
plan; the frozen manifest remains unchanged.

#### Post-M0 serial cursor (binding)

| next | implementation slice | objective gate |
|---|---|---|
| **M1** | `LogicFormula` DAG, structural interning, exact `TemporalSymbol::build` descent and proposition indexing | source-verified unit cases; no production hook and no M fixture expected green |
| **M2** | local `ltl::bdd` facade: variables, Boolean ops, equality, root/low/high navigation | biodivine canonicity/navigation tests |
| **M3** | `TransitionSet`/raw product → VWAA → GBA/SCC/collapse → degeneralized Büchi | intermediate dump parity with an instrumented reference |
| **M4** | `ModelChecker2` nested DFS, lazy BDD proposition walk/memo, lasso split, `System` trait | known lassos over a synthetic system; still no production hook |
| **M5** | shipped `model-checker.maude`, shared `StateGraph`, deadlock completion, kernel-direct typed hooks, result construction | M01 + M03 byte-exact target |
| **M6** | determinism closure, LTL+ path, large reference systems, typed verbose-stat event | M01–M09 byte-exact target |
| **M7** | GBA SAT BFS, prime implicants, `SatSolverSymbol`; pure `tautCheck` equations | M01–M10 10/10 plus frozen invariants |

The stages were executed in this order: M1's indexing contract before M2, M2's BDD gate
before M3, and the exact synthetic M4 checker before the production M5 hook. The table and
stage prose below preserve those implementation contracts and historical checkpoint gates;
references to 0/10 describe that stage's observed baseline, not the completed subsystem.
Every stage is implemented, verified, committed, and recorded in the Phase-M ledger.

### Stage M1 — LogicFormula + `build` (determinism root #2) — **DONE 26f4089**

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

**Gate:** focused tnk-core tests pass and the frozen M-scoreboard remains 0/10; production
hooks and M10's hook-owned verbose output remain absent. No BDD code and no production hook
in M1.

### Stage M2 — the `ltl::bdd` helper (facade extension) — **DONE 20f9bde**

Add `ltl/bdd.rs`, owning a local `BddVariableSet` whose variable index is the proposition
index. Its crate-private API covers `true`/`false` (including zero variables),
`ithvar`/`nithvar`, `and`/`or`/`not`, equality, implication, and root/variable/low/high
navigation; backend pointers do not escape the helper. Keep it separate from `SortBdds`.
Tests cover terminal navigation, literal polarity/order, truth tables, De Morgan,
canonicity, implication, and multi-level low/high walks against biodivine directly.

**Gate:** the focused BDD tests pass; M remains 0/10 and no production hook is bound.

### Stage M3 — the LTL→Büchi pipeline (determinism root #3) — **DONE 0b02e00**

Port, in order, each unit-tested against `dump()`-diffs of `TDEBUG` reference builds:
1. `TransitionSet` (`transitionSet.{hh,cc}`) — `BTreeMap<NatSet,Bdd>` with the subsumption-
   canonical `insert`/`product`; plus `RawTransitionSet` (`rawTransitionSet.cc`).
2. `VeryWeakAlternatingAutomaton` (`veryWeakAlternatingAutomaton.{hh,cc}`) — `dnf`,
   `computeTransitionSet`, `reachabilityOpt`, `computeFairnessSet`.
3. `GenBuchiAutomaton` (`genBuchiAutomaton.{hh,cc}` + `collapseStates.cc` +
   `sccAnalysis.cc` + `sccOptimizations.cc`) — the interner (`IndexedSet` analogue),
   `generateState`, `insertFairTransition`, Tarjan SCC, `simplify`.
4. `BuchiAutomaton2` (`buchiAutomaton2.{hh,cc}`) — degeneralization + `collapseStates`.

Add `ltl/nat_set.rs`, `transition.rs`, `vwaa.rs`, `buchi.rs`, and `scc.rs`. `NatSet`
ports `Utility/natSet` with normalized trailing words and its exact comparison: word-vector
length, then first word, then remaining words low-to-high. This ordering is observable in
`BTreeMap<NatSet, _>` and must not be replaced by element-lexicographic `BTreeSet`.
Test-only dump adapters compare a fixed battery (constants, atom/negated atom, n-ary
Boolean, `NEXT`, nested `UNTIL`/`RELEASE`) against temporary `TDEBUG` reference builds.
Do not leave instrumentation or binaries in this repository.

**Gate:** every layer's focused tests and intermediate dumps match; M remains 0/10 and no
production hook is bound.

### Stage M4 — the nested DFS + `System` trait (determinism root #4) — **DONE c4a14a2**

Port `ModelChecker2` (`modelChecker2.{cc,hh}`) into `ltl/model_check.rs`: product-state
interning, DFS1/DFS2, `satisfiesPropositionalFormula` (lazy root/low/high walk plus
per-system-state tested/true proposition sets), and exact `path`/`cycle`/`swap` recovery.
Define `trait System` with ordinal successor access and proposition testing; make the
checker generic over `S: System`, not a trait object. Unit-test fixed tiny systems for no
counterexample, nonempty/nil lead-ins, self-cycle, multi-state cycles, lazy proposition
memoization/call counts, and deterministic traversal. No rewrite engine or production
hook participates in M4.

**Gate:** all synthetic-system lassos and proposition-call counts are exact; M remains
0/10.

### Stage M5 — first vertical slice: shared graph + hooks + M01/M03 — **DONE 6afb47d**

1. Extract `Search`'s graph fields and successor quantum into `StateGraph`
   (`get_next_state`, `state_dag`, `fwd_arcs`); `Search` retains only BFS/goal logic.
   The checker wrapper adds the **deadlock self-loop** without changing ordinary search.
2. Implement `System` over that graph. `check_proposition` constructs and reduces
   `satisfies(state, proposition)` in the active `Runtime`/`Signature` context, passes the
   existing `DescentOps` through nested reduction, compares with `trueTerm`, and charges
   the nested rewrites exactly once. It does not use `MetaCtx`.
3. Add the repository-root `model-checker.maude` as an exact copy of the Maude 3.5.1
   source (`sha256 be53123786b18da5a91ac0fa0436e1d72ec87fc76076c1a12398d4d8166948d0`).
   From this point, the root-first harness path must exercise the shipped copy rather than
   fall through to the reference library.
4. Add typed `ModelCheckerHooks` and `SpecialOp::ModelCheck`, bind
   `"ModelCheckerSymbol"` immediately before the unknown-class fallback at
   `build_sig.rs:864`, and run it directly in `Runtime::try_special`. Introduce the
   labelled-rule registration path and shared `Rc<str>` ownership described in §3.2.
5. Build `counterexample`/transition/list/Qid/unlabeled/deadlock terms from the resolved
   hooks, or return `trueTerm`.
6. Record typed `(property_automaton_states, examined_system_states)` events during every
   check. M6 taught the REPL's existing `set verbose` path to render the exact two
   `ModelChecker:` lines; core code does not print.

**Gate:** M01 and M03 byte-exact, including rewrite counts, deadlock, unlabeled/Qid labels,
nil/nonempty lead-ins, and the deterministic shared-label duplicate-rule arc. Retained
search fixtures must remain unchanged.

### Stage M6 — close `modelCheck` / `modelCheck+` (M01–M09) — **DONE 119c3a0**

M01–M09 now pass together. The closure preserved reduced compound RHS subterms for
Maude-equivalent sharing/counts, completed the source-form object-completion diagnostic
path (including suppression for statements already complete), and made state-successor
enumeration lazily charge matcher-condition reductions and exhaustion work. M05's verbose
round-robin diagnostics and 52-state lasso are byte-exact. M08 and M09 each report the
reference 459 examined states, exactly 48,194 rewrites, and the frozen dining-philosophers
counterexample.

**Gate:** closed; M01–M09 pass together, and M10 also passes.

### Stage M7 — `satSolve` / `tautCheck` (sibling; separate risk) — **DONE 119c3a0**

`GenBuchiAutomaton::sat_solve` implements the reference's three ordered BFS passes and
lead-in rolling. The BDD facade extracts prime implicants in root-variable order; typed
`SatHooks` build `model`/`false`/counterexample terms, while the prelude continues to
define `tautCheck` as a pure equation over `satSolve`. Typed statistics flow through the
existing REPL verbose-event path, and the identity-collapse reporter emits the two frozen
diagnostics without hook-specific strings.

**Gate:** closed; all eight M10 commands are byte-exact, including singular/plural/zero
statistics, conjunction order and polarity, result sorts/counts, `false`, and tautology
counterexamples.

### 6.3 Why there is no new upper call

`modelCheck` uses only the current engine: its rewrite rules, equational reducer, DAG
arena, and the symbols/terms resolved by its own hook attachment. Rule labels become
shared kernel metadata at registration. Therefore `Runtime::try_special` can run the
checker and pass its existing `DescentOps` argument through nested reductions; extending
`MetaCtx` or `MetaDescent` would couple an ordinary built-in to the module database for no
semantic reason. `satSolve` is simpler still: it consumes only its formula DAG and result
hooks.

### 6.4 The `Search` refactor — completed

`StateGraph` owns expansion, deferred matcher accounting, successor normalization,
hash-consing, deterministic arcs/order, parent links, and roots. `Search` composes it with
BFS/goal logic; the checker composes it with ordinal access, proposition memoization,
deadlock completion, and lasso recovery. Both call the same `GraphContext` methods.
Pending results are rooted at matcher acceptance and after path rebuilding, so eager
materialization cannot expose an unrooted DAG between reductions. The retained search
fixtures and full audit/legacy gates show no observational drift.

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
| `M10-sat-taut` | 8 | `model(nil,True)`, `model(b,True)`, `false`, four tautology outcomes, manual prime implicant `model(a ; b,(~ c) ; c)`, exact tautology counterexample, and verbose 1-state/0-fairness + 2-state/1-fairness statistics |

Total: **10 fixtures / 50 commands**. Both
`TNK_BIN=~/.local/bin/maude tools/subsystems-scoreboard.sh -p M` (oracle self-diff) and the
current default production release report **10/10 PASS**. M01–M10 conform together:
model-checking lassos/statistics, SAT/tautology output, identity diagnostics, result sorts,
and rewrite counts are all byte-exact.

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

### 7.1 Phase-M `/goal` stopping gate

M1–M7 is complete only when **all** of the following hold on the same final tree:

1. A default pure-Rust release build reports `SUBSYSTEMS 10/10 PASS` for `-p M`; all 50
   result values, sorts, rewrite counts, verbose lines, and printed lassos/models are
   byte-exact. The oracle self-run remains 10/10.
2. F1–F4 hold: `SCOREBOARD 77/77 PASS`, `LEGACY 87/87 CLEAN`,
   `cargo test --release` fully green, and stock `term-order.maude`,
   `machine-int.maude`, and `linear.maude` load clean.
3. Retained subsystem gates pass: U 27/27, V 21/21, and N 16/16 on the default release;
   T 11/11 on a fresh `smt-z3` release; the default release remains solver-free. T11's
   native lane passes. Re-run the checksum-pinned external T11 oracle only if its fixture
   or expected contract changed (Phase M must not change either).
4. The checked-in `model-checker.maude` has SHA-256
   `be53123786b18da5a91ac0fa0436e1d72ec87fc76076c1a12398d4d8166948d0`, loads with
   `MAUDE_LIB=$PWD` (no reference-library fallback), and `modelCheck`, `modelCheck+`,
   `satSolve`, and `tautCheck` all compute; neither special hook remains inert.
5. The M manifest has not shrunk or weakened, no accepted diff masks an M failure, and no
   timeout/exclusion was added. New defects found during implementation are fixed and
   regression-covered rather than deferred.
6. All temporary reference instrumentation and generated artifacts are removed. No Phase-I
   or unrelated feature code landed.
7. This plan, `subsystems-goal.md`, `roadmap.md`, `README.md`, and `fable-audit.md` state
   observed completion; the Phase-M ledger records commit hashes for M1–M7. All intended
   work is committed and the working tree is clean.

**Observed close evidence (2026-07-23, implementation commit `119c3a0`):** M 10/10,
U 27/27, V 21/21, N 16/16, optional-z3 T 11/11, audit 77/77, legacy 87/87, and
`cargo test --release --workspace` 438/438. The three stock load probes are clean and the
shipped `model-checker.maude` checksum is the value pinned above.

Do not mark the `/goal` complete for a plausible subset, a logically valid but different
lasso/model, one narrowed test command, or a stage checkpoint.

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
2. **BDD backend — bound.** D6 binds normal-dependency `biodivine-lib-bdd` 0.5.27. Diff
   intermediate automaton dumps early using proposition-index variable order. Any drift
   is a facade/ordering bug to diagnose and fix; do not switch to BuDDy FFI without a new,
   explicit user decision amending D6.
3. **`satSolve`/`tautCheck` ordering — bound.** Implement after `modelCheck` (M7). M10 is
   already frozen with eight commands. Port `Utility/bdd.cc:31-49` rather than choosing a
   different satisfying cube, and finish exact `model(...)` rendering before Phase M
   closes. Its verbose pair also binds SatSolverSymbol's state/fairness statistics and the
   identity-collapse lines exposed by `set verbose on`.
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
