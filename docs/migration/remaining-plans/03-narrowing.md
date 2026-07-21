# Phase S3 — Narrowing (`vu-narrow` / `fvu-narrow` + meta counterparts) — implementation plan

**Status: READY (inventory refreshed 2026-07-19; no S3 code written).** This is the S3 item of the
subsystems goal (`docs/migration/subsystems-goal.md` §2, Phase S). S1 order-sorted unification and S2
folding variants are closed, including A/AU, incompleteness propagation, persistent meta caches, and
fresh-family alternation; all hard prerequisites are present. The former fixture and legacy-surface
decisions are resolved in §8. Scope remains **variant-based narrowing, v3 semantics**, with only the
oracle-compatible legacy `metaNarrow` boundary retained.

All reference citations are into `~/code/maude-lang/maude/src/`; all tnk citations into
`/Users/dai/Downloads/tambanokano/`. Behaviour claims were confirmed against the live oracle
(`MAUDE_LIB=~/code/maude-lang/maude/src/Main ~/.local/bin/maude -no-banner`).

---

## 1. Subsystem overview

Narrowing is symbolic reachability: instead of matching a rule LHS against a ground term and rewriting,
we **unify** a rule LHS with a (non-variable) subterm of a *symbolic* term modulo the equational axioms
+ variant equations, apply the rule, and iterate — building a search space of symbolic states, each
carrying an accumulated substitution back to the original variables. It answers "for which instances of
the start term is the goal pattern reachable?".

### Commands and meta-functions this phase must deliver

| Surface | Meaning | Reference engine |
|---|---|---|
| `vu-narrow [n,d] in M : t =>A p [such that C]` | variant-unification narrowing; a nonempty `C` is parsed then rejected exactly as by Maude 3.5.1 | `NarrowingSequenceSearch3` |
| `fvu-narrow …` | `vu-narrow` with **folding** forced on (`{fold}`) | same, `FOLD` flag |
| `{fold}` / `{vfold}` / `{path}` / `{filter,delay}` option blocks | matching fold / variant fold / history / minimal-unifier options | folder + variant flags |
| `t1 \/ t2 \/ …` start term | narrow a **disjunction** of initial states | `termDisjunction` |
| `show most general states .` | the retained (folded) states | `showMostGeneralStates` |
| `show frontier states .` | the open (unexpanded) leaves | `showFrontierStates` |
| `show path N .` / `show path states N .` | reconstruct the narrowing path to state N | `showNarrowingSearchPath` |
| arrows `=>1 / =>+ / =>* / =>!` | one / ≥1 / ≥0 / normal-form steps | `SearchType` |
| `set verbose on/off` | per-search state-count + folding-trace lines | `Verbose(...)` |
| `set show breakdown on/off` | narrowing and variant-narrowing rewrite counters | `RewritingContext` counts |
| `continue` | resume the suspended narrowing enumeration without rebuilding it | interpreter session |
| meta `metaNarrowingApply` | one variant-narrowing step (7-tuple result) | `NarrowingSearchState2` |
| meta `metaNarrowingSearch` | multi-step variant narrowing search (6-tuple) | `NarrowingSequenceSearch3` |
| meta `metaNarrowingSearchPath` | + full narrowing trace | `NarrowingSequenceSearch3` + `KEEP_HISTORY` |
| meta legacy `metaNarrow` | classic (v1) narrowing, `ResultTriple` | `NarrowingSequenceSearch` **(v1!)** |

### What the 15 N* fixtures exercise (168 substantive primary commands; frozen manifest, `subsystems-goal.md` §2)

- **N-probe-01** (free `COUNT`, one narrowing rule `X => s(X)`): `=>1/=>*/=>!`, bounded/unbounded,
  and no-solution behavior. Its formerly nonterminating fourth command is now depth-bounded at 3 (§8).
- **N01-narrow** (`BAZ`: free ops + one `[variant]` equation; `FOO`: one free rule): `vu-narrow` /
  `fvu-narrow`, `=>*/=>+/=>!`, depth bounds, `set show breakdown on`.
- **N02-narrow2**: `R&W` (free + `NAT`, `{fold}`/`{vfold}`, `\/` disjunction, `show most general/frontier
  states`); `R&W-FAIR` (ACU `_+_`); `COMM` (**AU** `_;_ [assoc id: nil]` + ACU `_ _`).
- **N03-meta-narrow**: `metaNarrow` (legacy), `metaNarrowingApply` (incl. `delay filter`, irreducibility
  constraint, `#`-var no-rename), `metaNarrowingSearch`/`…Path` (`none`/`match` fold). Modules use
  **AU** (`f [assoc]`) and **AC** (`_+_ [assoc comm]` XOR).
- **N-ch15-01** (free Peano): plain `vu-narrow`, bounds. **No variants, no AU, no folding — the ideal
  first-green fixture.**
- **N-ch15-02/03/05/06/10/11** (vending, ACU `__` + one `[variant]` change equation): `vu-narrow`/
  `fvu-narrow`, `{fold}`, disjunction, `nonexec narrowing` extra-variable rule, `show …states`.
- **N-ch15-04/07/08/09** (strand-space XOR protocol): AC `_*_` + XOR `[variant]` nilpotence eqs + ACU
  `_&_` + **AU `_,_`**; `{fold}/{vfold}/{filter,delay}/{path}`; `N-ch15-07/08` carry `set verbose on`.

### Fixture → axiom-support matrix (updated after S1 completion)

All 15 N fixtures have their axiom-unification prerequisite. Nine use free/AC/ACU only
(`N-ch15-01`, `N-probe-01`, N01, `N-ch15-02/03/05/06/10/11`); six also exercise the complete A/AU
solver (N02, N03, `N-ch15-04/07/08/09`). S2 supplies the required folding-variant engine, variant
unification, incompleteness propagation, and family ordering. There is no remaining subsystem blocker.

---

## 2. Reference approach (v3 variant narrowing)

Live v3 files: `Higher/narrowingSequenceSearch3.{hh,cc}` (BFS driver), `narrowingSearchState3.{hh,cc}`
(one step), `narrowingFolder.{hh,cc}` (folding + history), `variantNarrowingSearchState.{hh,cc}` (the
variant step primitive), `narrowingUnificationProblem.{hh,cc}`, plus the shared `variantSearch.*`,
`positionState.*`, `freshVariableSource.*`. Command driver: `Mixfix/search.cc` + `Mixfix/narrowing.cc` +
`Mixfix/commands.yy`. The v1 engine (`narrowingSequenceSearch.*` + `narrowingSearchState.*`, backing the
old `narrow`/`xg-narrow` and **legacy `metaNarrow`**) uses ordinary matching, not variant unification.

### 2.1 What a "state" is

A `NarrowingFolder::RetainedState` (`narrowingFolder.hh:109-159`): the current term DAG, an
**accumulated substitution** from the *initial* variables to their narrowed instances (`:121`), the
**variable family** the state + substitution-range live in (`:120`), `parentIndex`/`rootIndex`/`depth`
(`:117-119`), and optional fold payload (an `LhsAutomaton` for `{fold}` or a subsumption `VariantSearch`
for `{vfold}`) / history payload. States get a monotone integer index (`counter`, `…3.cc:100,446`); a
child's index always exceeds its parent's — this invariant makes the ordered `std::map<int,
RetainedState*> mostGeneralSoFar` (`narrowingFolder.hh:161,176`) a BFS queue.

### 2.2 Initial state — `handleInitialState` (`…3.cc:54-112`)

Index the initial variables; rename every one to a **family-0 (`#`) fresh variable**
(`getFreshVariableName(i,0)`, `:75`); instantiate + **reduce with equations** in a subcontext
(`:87-94`); insert with `parentIndex=-1`, `variableFamily=0` (`:101`); the renaming becomes the initial
accumulated substitution (`:104`). Oracle-confirmed: the zero-step (`=>*`) solution of `< M > =>* < a c >`
prints `state: < #1:Marking >`, `M --> #1:Marking`.

### 2.3 One narrowing step — `NarrowingSearchState3::findNextNarrowing` (`narrowingSearchState3.cc:95-173`)

- **Positions**: `PositionState` breadth-first over the term, root-first, left-to-right; **only
  non-variable positions** (`:135`); to the leaves (`maxDepth=UNBOUNDED`, `…3.cc:511`).
- **Rules at a position**: ascending rule index over `module->getRules()` (`:143`). Eligible iff **not
  conditional** (`:146`), executable unless `ALLOW_NONEXEC` (`:147` — narrowing always passes
  `ALLOW_NONEXEC`), **has the `narrowing` attribute** (`rl->isNarrowing()`, `:148`), top symbol in the
  right kind (`:149`). Loop is **position-major, rule-minor**.
- **Unify LHS into subterm modulo axioms+variants**: build a `VariantUnificationProblem(context,
  blockers, rule, subterm, varInfo, freshGen, incomingFamily, flags)` (`:152-159`) and pull unifiers
  with `findNextUnifier()` (`:160`) — each unifier is one step.
- **Apply / build the new term** — `getNarrowedDag` (`:175-207`): construct the rule RHS under the
  unifier, `makeClone()` (guards bare-var RHS aliasing), zero the gap slots, and
  `rebuildAndInstantiateDag` up the position stack instantiating surviving-term variables with the
  unifier (`:206`). Also keeps a hole-marked `replacementContext` for tracing.
- **Accumulated substitution** — `makeAccumulatedSubstitution` (`:209-222`): each old binding is
  instantiated by the step's unifier (`:218`), threading the map back to the initial variables.

### 2.4 The BFS driver — `NarrowingSequenceSearch3::findNextUnifier` (`…3.cc:264-354`)

Two-level: if a goal-unification problem is live, return its next unifier (`:269-292`); else fetch the
next interesting state (`findNextInterestingState`, `:296`), set up the goal test (§2.6), loop.

`findNextInterestingState` (`:356-529`) is the actual search: (1) for `=>*`, first hand back the initial
states (`:362-372`); (2) drive `stateBeingExpanded->findNextNarrowing()`; per child: trace, count
(`:434`), **reduce** in a subcontext (`:438-442`), `stateCollection.insertState(++counter, …)`
(`:446-450`); a surviving child is **returned immediately** (unless `=>!`, `:469-470`); (3) when
expansion is exhausted, `getNextSurvivingState` picks the next state to expand if depth allows (`:499`),
builds a fresh `NarrowingSearchState3` (`:503-512`); (4) exhausted → print verbose counts (`:526-527`),
return `NONE`. **A state is goal-tested once, at generation; its children are produced later, when BFS
reaches it.**

### 2.5 Arrows (`Higher/sequenceSearch.hh:33-40`; ctor `…3.cc:121-134`)

`ONE_STEP`(`=>1`), `AT_LEAST_ONE_STEP`(`=>+`), `ANY_STEPS`(`=>*`), `NORMAL_FORM`(`=>!`), `BRANCH`(`=>#`).
`=>#` is rejected for narrowing (`search.cc:55-59`). The arrow sets three fields:
`nrInitialStatesToTry = (=>*) ? #startStates : 0` (only `=>*` tests 0-step states); `maxDepth = (=>1)?1`
(clamp); `normalFormNeeded = (=>!)`. For `=>!` a state is goal-tested only when its expansion yields **no
successor within depth** (leaf test, `:388-411`) — states are still expanded at `maxDepth` to detect a
successor, which is then discarded.

### 2.6 The goal test / final unification (`…3.cc:296-352`)

Instantiate the goal pattern by the state's accumulated substitution (the goal may mention initial
variables; extra goal-only variables are zeroed, `:304-330`), pair `⟨goal,state⟩` via an internal tuple
symbol (`createInternalTupleSymbol`, `:227-234`), and create a `VariantSearch` — or a
`FilteredVariantUnifierSearch` under the `filter` flag — in `UNIFICATION_MODE` (`:341-351`). Each
`findNextUnifier` yields a variant unifier; `VariantSearch::findNextUnifier` returns only unifiers whose
size equals `nrVariantVariables` (the `t =? t` identity case, `variantSearch.cc:57-80`). Variant-
unification incompleteness propagates via `isIncomplete()` and surfaces as the "Some solutions may have
been missed" warning (`narrowing.cc:181-182`).

**The printed answer is a triple, not a composed substitution** (`narrowing.cc:210-235`): `state:` the
state dag (`:216`); `accumulated substitution:` initial→narrowed (`:219-220`); `variant unifier:`
goal-vs-state (`:221-222`). Oracle sample (N-ch15-06):
```
state: < %1:Marking >
accumulated substitution:
M --> $ $ %1:Marking
variant unifier:
%1:Marking --> empty
```

### 2.7 Folding — `NarrowingFolder::insertState` (`narrowingFolder.cc:194-300`)

- `{fold}` = subsumption by **matching modulo axioms**: retained term compiled to an `LhsAutomaton`
  (`:463-488`), `subsumes` runs `match` (`:528-541`).
- `{vfold}` = subsumption by **variant subsumption**: a `VariantSearch` in `SUBSUMPTION_MODE`
  (`:489-503`), `subsumes` calls `isSubsumed` — strictly coarser (folds more) than `{fold}`.
- `fvu-narrow` = `vu-narrow` + `FOLD` forced (`search.cc:285-286`).
- Insert logic: (1) if any retained state subsumes the newcomer, **drop it** (`:204-214`); (2) else
  build it, compute ancestors; (3) it may **evict** existing states — either **descendant eviction**
  (a state whose parent is already subsumed, `:261-272`, prunes a whole explored subtree) or **direct
  subsumption** (`:273-282`). Victims are `delete`d, or **kept-but-marked** if locked / a needed parent /
  (with `keepHistory`) an ancestor (`doSubsumption`, `:163-192`, `markedSubsumed` `hh:274-289`).
- Non-folding cleanup is `cleanGraph` (`:371-427`). `showMostGeneralStates` is meaningful only when
  folding (`narrowing.cc:392-394`).

### 2.8 Verbose state-count reporting (`set verbose on`)

`globalVerboseFlag` (`macros.cc:36`, set at `commands.yy:531-533`) gates `Verbose(x)` →
`cerr << CYAN << x << RESET` (`macros.hh:363-366`). **Color is off when stdout is not a TTY** — oracle
lines are plain text (confirmed). Two summary lines at search end (`…3.cc:526-527`), oracle-exact:
```
Total number of states seen = 916
Of which 916 were considered for further narrowing.
```
(`counter+1` seen; `nrStatesExpanded` considered, `:518`). **Critically, folding also emits a `Verbose`
line per subsumption/eviction** — `New state … subsumed by …` (`:211`), `… evicted descendent … by
subsuming an ancestor.` (`:267-269`), `… subsumed older state …` (`:279`) — with full term printing.
For N-ch15-07 the oracle emits **1307 stderr lines**, nearly all subsumption traces. Because
`diffmaude.sh` compares `2>&1` byte-exact (only `Warning:`/`Advisory:`/`error:` blocks and timing tails
are normalized — `diffmaude.sh:65-101`), **every one of these lines is a conformance target** for the two
`set verbose on` fixtures. This is the single largest byte-exactness surface in the phase.

### 2.9 Fresh-variable families (`freshVariableSource.cc:63-99`)

Families 0/1/2 → prefixes `#`/`%`/`@` (`"#%@"[family]`, `:64-68`), names `<prefix><index+base+1>`, cached
per family. Initial states → family 0 (`#`). Each step's unifier is produced in a family **different from
the incoming** one; `VariantSearch` picks `firstVariableFamily=(incoming==0)?1:0`,
`secondVariableFamily=(incoming∈{2,NONE})?1:2` and toggles per layer (`variantSearch.cc:128-129,420,445`);
the child state adopts the unifier's family (`…3.cc:450,454`). **This alternation is byte-visible** —
`show most general states` on N-ch15-05 prints `< #1:Money > \/ < c @1:Money > \/ < c c %1:Money > \/ < c
c c @1:Money > …` (depth 0=`#`, 1=`@`, 2=`%`, 3=`@`), and N01 solution bindings cross families
(`#1:Foo --> @1:Foo`, `%2:Foo --> @1:Foo`). Getting the family selection wrong changes output bytes.

### 2.10 History / paths / show-states (`narrowingFolder.cc`, `narrowing.cc`)

`KEEP_HISTORY` retains per state the rule, narrowing context+position, a copy of the step unifier, and
its varInfo (`:302-328`). `KEEP_PATHS` locks the whole path to any solution-producing state
(`lockPathToState`, `:429-449`). `showNarrowingSearchPath` (`narrowing.cc:261-323`) walks `getStateParent`
to the root, reverses, prints `===[ rule ]===>` arcs + compound unifier + `state N, sort: dag` +
accumulated substitution. `showFrontierStates` (`:325-381`) prints `getUnexpandedStates` ∪
`getUnvisitedStates`; `showMostGeneralStates` (`:383-414`) prints the retained map. All three render the
state list joined by ` \/\n` (oracle-confirmed). Note the manual-vs-3.5.1 path-numbering deviation is
already recorded in N-ch15-09's header.

### 2.11 Meta layer (`Meta/metaNarrow.cc`, `metaNewNarrow.cc`, `metaNewNarrow2.cc`)

Dispatch: `descentSignature.cc:50-51,83-85` (X-macro `MACRO(name,arity)`) → `metaLevelOpSymbol.cc`
`attachData`/`eqRewriteFast`. Solution indexing/continuation is uniform: decode `solutionNr`
(`downSaturate64`), consult a **bounded MRU cache** `MetaOpCache` (default size 4, `metaOpCache.hh:36`)
keyed on the problem **ignoring module + the last (`solutionNr`) arg** (`metaOpCache.cc:72-95`) so
`(…,n+1)` resumes the cached engine one step; advance `while(lastSolutionNr<solutionNr) findNext…()`.

| Meta fn | arity | Result sort (shape) | Engine |
|---|---|---|---|
| legacy `metaNarrow` | 6 | `ResultTriple` `{Term,Type,Subst}` | `NarrowingSequenceSearch` **v1** (`metaNarrow.cc:27-54,56-103`) |
| `metaNarrow2` | 6 | `ResultPair` `{Term,Type}` (state enumeration) | v1 + `SINGLE_POSITION` (`:105-186`) |
| `metaNarrowingApply` | 6 | `NarrowingApplyResult` 7-tuple `{Term,Type,Context,Qid(rule),Subst(into-term),Subst(into-rule),Qid(family)}` | `NarrowingSearchState2` (`metaNewNarrow.cc:76-215`) |
| `metaNarrowingSearch` | 8 | `NarrowingSearchResult` 6-tuple `{Term,Type,Subst(accum),Qid(state-family),Subst(unifier),Qid(unifier-family)}` | `NarrowingSequenceSearch3` (`metaNewNarrow2.cc:70-150`) |
| `metaNarrowingSearchPath` | 8 | `NarrowingSearchPathResult` 6-tuple with a `NarrowingTrace` (list of 7-field `NarrowingStep`) | `…3` + `KEEP_HISTORY` (`:153-325`) |

Failure/exhaustion → `failure` / `failureIncomplete` of the `…?` result sort (from engine
`isIncomplete()`). Decoders: arrow `downSearchType` accepts only `'+ '* '! '#` — **there is no `=>1`
arrow at the meta level**; a single step is `metaNarrowingApply` (`metaLevel.hh:733-768`); fold
`downFoldType` `'none`/`'match` (`:770-785`); `VariantOptionSet` `delay`/`filter` (`metaDown.cc:1562-1590`);
bound `Nat ∪ unbounded`. Result constructors: `metaUp.cc:369,999-1029,1066-1093,1137-1202`. Prelude decls
`prelude.maude:2864,2869,2900,2905,2911` (+ convenience overloads defaulting `VariantOptionSet` to
`none`, `:3127-3137`).

---

## 3. What tnk already has to build on

### 3.1 The rewrite-search driver + resumable session (the shape to mirror, `crates/tnk-repl/src/lib.rs`)

- `Repl.last: Option<(String, Continuation)>` owns the suspended command session. `Continuation`
  currently covers `Rewrite`, `Search`, `Variants`, and `VariantUnifiers`; the two S2 variants prove
  that a symbolic enumerator can persist across `continue`, preserve numbering, and keep its DAG roots.
- `render_search` supplies the output shape for solutions, bindings, path reconstruction, and graph
  display. The variant renderers supply the closer precedent for mode-specific rewrite counts and
  delayed/full-set preparation.
- The rewrite state graph in `crates/tnk-core/src/search.rs` is a rooted, index-addressed BFS graph with
  parent arcs, a frontier, lazy expansion, and stable external solution numbering.

**Reuse verdict:** narrowing states are *symbolic* (variables, accumulated substitutions, subsumption
folding, and family-tagged fresh variables), unlike the rewrite graph's ground hash-consed states.
Build a new `narrow` module (`NarrowSearch` + `NarrowFolder`) rather than adding modes to `Search`, but
reuse the established session contract: add `Continuation::Narrow(Box<NarrowSession>)`, retain
index-addressed parent/history records and `RootGuard`s, and expose a lazy `next_solution` driver.

### 3.2 Unification driver (`crates/tnk-core/src/unify/`)

`UnifyProblem::{new_preserving_order,new_for_variant}` plus `find_next_full` already implement the
absolute, gap-preserving variable layout required by symbolic narrowing. They are the APIs used by
S2's one-step variant narrowing, including module-wide protected slots, caller-selected fresh family,
order-sorted solutions over every supported theory, and `is_incomplete()` propagation. The ordinary
`find_next` API remains suitable for simple final unification. This is stronger groundwork than the
pre-S2 plan assumed: rule-step and goal-test unification do not need a new solved-form engine.

### 3.3 S2 variants (completed hard prerequisite)

S2 supplies `VariantSearch`, `VariantSearch::enable_unification`, `complete_variant_unifier`,
variant-equation reducibility, shared matching/subsumption, exact family alternation, incompleteness,
and rooted persistent searches. Its private `expand_variant` also contains the reusable mechanics S3
needs: state re-slotting, breadth-first non-variable positions, a state-wide unifier filter,
substitution composition, replacement, reduction, and family canonicalization.

Two APIs still need factoring as **S3 groundwork**, not reinvention: extract the rule/equation-neutral
one-step machinery from `VariantSearch::expand_variant`, and move the duplicated filtered-unifier
retention currently in REPL `VariantUnifySession` and meta `MetaVariantUnifyCache` behind one reusable
core stream. No public `VariantUnificationProblem` or `FilteredVariantUnifierSearch` type exists today;
S3 must not code against those pre-S2 placeholder names or introduce a third filter implementation.

### 3.4 Meta descent (`crates/tnk-modules/src/meta.rs`, `crates/tnk-core/src/descent.rs`)

`trait DescentOps::descend` and `MetaOp` provide the dispatch seam. `MetaState` now owns structurally keyed,
four-entry persistent caches for `metaGetVariant`, variant unification, and variant matching; they resume
forward indices, reuse equal indices, discard on backward requests, retain rooted DAG state, and clear on
module/view rebuild. That S2 cache contract—not `metaSearch`'s older stateless re-drive—is the precedent
for `metaNarrowing*`.

All `metaNarrow*` names still map to `MetaOp::Deferred`, so they remain inert. S3 adds dedicated
`MetaOp` variants, `build_sig.rs` mappings, result constructors, and persistent narrowing cache entries.

### 3.5 Fresh-var generator (`crates/tnk-core/src/fresh.rs`)

`VariableFamily::{Unify=#, Variant=%, Narrow=@}` (`:19-26`); `@n` is reserved for narrowing (`:24`) with
**no consumer yet**. `FreshVariableGenerator::{new, with_base(Nat), fresh_name(index, family)}`
(`:63-92`), `variable_name_conflict` (`:99`), `parse_fresh_name`/`belongs_to_family` (`:122-134`). This
is the single generator roadmap risk #8 mandates; narrowing must route **all** fresh vars through it and
must reproduce the reference's per-step family alternation (§2.9).

### 3.6 `[variant]` is retained; `[narrowing]` is still discarded, and variable-LHS rules panic

- S2 added `variant: bool` to `Statement::Eq` and `EqTrace`; executable variant equations are compiled
  into `VariantEquation`s. This half of the old groundwork is complete.
- `Statement::Rule` and `RlTrace` still have no `narrowing` field. The parser accepts `narrowing` as a
  legal attribute token but does not retain it.
- `CompiledRule` has no narrowing flag or source LHS. `push_rule` requires
  `lhs.top_symbol().expect("rule lhs must be an application")`, so the probe's
  `rl [up] : X => s(X) [narrowing]` still panics during module loading.

Stage 0 must thread only the missing rule flag, retain a rule term/descriptor suitable for unification,
and make narrowing rules discoverable in module order even when their LHS is a bare variable. Ordinary
rewrite indexing should remain top-symbol based; a variable-LHS rule exists for symbolic narrowing and
must not become a catch-all ordinary rewrite rule accidentally.

---

## 4. Architectural fit & divergence analysis

- **Two search graphs, one plumbing.** tnk's rewrite `Search` is not the right data structure for
  narrowing (ground hash-cons vs symbolic subsumption), matching the reference's own split
  (`RewriteSequenceSearch` vs `NarrowingSequenceSearch3`). Divergence is *neutral-to-helpful*: a fresh
  `NarrowSearch` in `crates/tnk-core/src/narrow/` (sequence.rs + folder.rs, per A8 §9's proposed layout)
  keeps the two clean, while the REPL session/`render`/`show` plumbing is shared. Enum-dispatched theories
  (D3) and the instance engine (D1) are helpful — no vtable churn in the step loop, and the meta descent
  runs in the same arena (no cross-engine translation for `metaNarrowing*`).
- **GC discipline (risk #9).** The narrowing frontier must root every retained state term, accumulated
  substitution range, goal, initial disjunct, and in-flight renaming. Unlike rewrite search, folding can
  evict states, so eviction and graph cleanup must release their `RootGuard`s.
- **Persistent meta ownership.** `metaNarrowing*` search objects can survive across descent calls, just
  as S2's variant caches do. Cache entries must own every graph/substitution root, obey the same
  four-entry structural-key policy, and be cleared whenever REPL module/view state is rebuilt. Do not
  substitute stateless drive-to-nth recomputation: it loses the reference cache's observable
  continuation and rewrite-count behavior and repeats semi-decidable work.
- **The `@` family + alternation.** tnk's single `FreshVariableGenerator` (risk #8) is the right home,
  but the reference's *family selection per step* (§2.9) is subtle and byte-observable. Port
  `variantSearch.cc:128-129` + the per-layer toggle **verbatim** and co-locate it with S2's variant
  family logic; do not re-derive it.
- **Attributes as flags.** `[variant]` already follows surface → trace → executable variant equation.
  Add `[narrowing]` through the parallel rule path without reopening statement representation.
- **`continue` for narrowing.** The reference supports `vuNarrowingCont` (`narrowing.cc:248-257`); tnk's
  `Continuation` extends cleanly with a `Narrow` variant, GC-off persistence identical to `Search`.

---

## 5. Feasibility & risk (honest assessment)

**Dependency chain is closed:** S0, S1, and S2 are complete. Concretely:

1. The 13 variant-dependent fixtures now have the exact variant engine, filter, family ordering, and
   persistent-cache behavior they require.
2. The six A/AU fixtures are unblocked at the unifier layer (N02, N03,
   `N-ch15-04/07/08/09`). Associative incompleteness already propagates through S2; S3 must carry it
   into object warnings and meta `failureIncomplete` results.

**Byte-exactness risks, in priority order:**

- **(A) The `set verbose on` folding trace (N-ch15-07/08).** ~1300 stderr lines of `New state … subsumed
  by …` / `evicted descendent …`, compared byte-exact (§2.8). Reproducing the exact *set* of
  subsumptions **in the exact order**, with faithful term pretty-printing + line-wrapping, is the hardest
  single target. It rides on the folder producing byte-identical decisions in byte-identical order —
  which rides on S2 variant enumeration order and the family alternation. High risk; verify these two
  fixtures last.
- **(B) Fresh-var family selection/alternation (§2.9).** Byte-visible in every state/substitution/
  show-states line. Port verbatim; unit-test the emitted variable names on N-ch15-05's `show most general
  states` (the `# @ % @` ladder is a precise oracle).
- **(C) Solution/state enumeration order & counts.** Position-major/rule-minor/unifier order, BFS by
  generation index, `=>*` initial-state-first. `N-ch15-07`'s documented counts (plain 916 states/84
  solutions, `{fold}` 197/1, `{vfold}` 68/1, `{filter,delay}` 20/1) are exact conformance targets and a
  strong differential signal.
- **(D) `set show breakdown on` counters (N01).** The `rewrites:` line is followed by `… variant
  narrowing steps: N  narrowing steps: M` — narrowing-specific counters
  (`incrementNarrowingCount`/`incrementVariantNarrowingCount`) that must be reproduced.

**Former readiness blockers are resolved (§8):**

- N-probe-01's unreachable unbounded command is depth-bounded at 3. The live oracle terminates
  immediately with `No solution.` and `rewrites: 9`; the fixture no longer requires timeout semantics.
- Legacy `metaNarrow` remains in the N03 gate, but not as a second full public narrowing generation.
  Serve its legacy `ResultTriple`/goal-matching boundary from the v3 engine when oracle-identical; if
  N03 exposes a real semantic difference, implement the smallest v1-compatible path needed for those
  calls. Excluding or weakening N03 is not an option.

**Termination/bounds.** Narrowing is semi-decidable; tnk must honor solution/depth bounds exactly and
support `continue`. The frozen manifest now bounds its deliberately unreachable probe. Folding
(`{fold}`/`{vfold}`) makes the vending/protocol graphs finite; the reference completes every frozen
fixture within the 60-second harness. S3 therefore has no expected-timeout case and must not add one.

**Overall:** the free slice is low-risk; the ACU+variant tier is medium-risk; the A/AU+verbose tier is the
high-risk long pole. All three now depend on S2 order fidelity, not missing S1 theory support.

---

## 6. Implementation plan (staged, smallest-first)

**Stage 0 — groundwork (unblocks everything, no narrowing search semantics yet).**
- Add `narrowing: bool` to `Statement::Rule` and `RlTrace`; retain it from the already-recognized
  attribute token and preserve it through flattening, renaming, and metalevel module translation.
- Give the kernel a module-order narrowing-rule descriptor containing source LHS/RHS, variable layout,
  condition, label/id, `nonexec`, and narrowing flag. Keep ordinary executable rules in their existing
  top-symbol index; a variable-LHS narrowing rule must load without becoming an ordinary catch-all rule.
- Factor the rule/equation-neutral step mechanics and filtered variant-unifier stream identified in
  §3.3 into `tnk-core`; S3 and the existing object/meta variant consumers must share them.
- `tools/diffmaude-command.py` already recognizes optional `{…}` + `vu-narrow`/`fvu-narrow` starts;
  preserve its 168-command manifest count as fixtures evolve.
- Route the reserved `@` family through the existing central generator.

**Stage 1 — the vertical slice: free-theory `vu-narrow` (verifies N-ch15-01).**
- Parser: `vu-narrow [n,d] in M : t =>A p [such that C] .` (reuse the existing bound, arrow, module,
  and condition grammar). Accept a nonempty condition syntactically, then reject it before session
  creation with Maude's `conditions are not currently supported for narrowing.` warning. No `{…}`
  option blocks or `\/` initial disjunction yet.
- New `crates/tnk-core/src/narrow/sequence.rs`: a `NarrowSearch` mirroring the reference driver (§2.2-2.6)
  but with the **step and goal test using the existing plain `UnifyProblem`** (in a free theory with no
  `[variant]` equations, variant unification degenerates to syntactic unification — so S2 is *not* needed
  for this slice). Index-`Vec` states + parent links + `RootGuard` per state; breadth-first non-variable
  positions respecting every symbol's `frozen` arguments; unconditional `[narrowing]` rules in module
  order with `nonexec` allowed; `@`-family renaming; lazy `next_solution` with exact solution/depth
  bounds and `=>1/=>+/=>*/=>!` semantics.
- REPL: `Continuation::Narrow(Box<NarrowSession>)`; `render_narrow` printing the `state:` / `accumulated
  substitution:` / `variant unifier:` triple (§2.6) and `No more solutions.` / `No solution.`; `continue`
  support.
- **Gate:** N-ch15-01 and all four now-terminating N-probe-01 commands diff clean.

**Stage 2 — ACU + variant goal test (verifies N-ch15-02).**
- Use the reusable core variant-unifier stream factored in Stage 0. It should be built from the current
  `VariantSearch::new` + `enable_unification`/`complete_variant_unifier` machinery, not a nonexistent
  pre-S2 `VariantUnificationProblem` wrapper.
- Use that same stream for rule-step unification modulo variant equations and for the final
  state/goal pair. Reduce every accepted state with equations; preserve incompleteness and exact family
  alternation.
- Add `set show breakdown on` narrowing counters and `show frontier states .`.
- **Gate:** N-ch15-02 clean (ACU + `[variant]` goal test + frontier display, no folding).

**Stage 3 — folding + filter + disjunction + most-general states (verifies N01, N-ch15-03/05/06/10/11).**
- `crates/tnk-core/src/narrow/folder.rs`: `NarrowFolder` with `{fold}` via the existing shared matcher
  and `{vfold}` via S2's variant-subsumer, descendant eviction, and `RootGuard` release. `fvu-narrow`
  forces `{fold}`.
- `{filter}`/`{filter,delay}` use the single core filtered-unifier stream factored in Stage 0; no
  REPL-only filter or frozen-subject approximation. Syntax accepts the fixture's option placement and
  rejects `=>#`.
- Parser: `{fold}`/`{vfold}`/`{path}` prefixes; `\/` initial-state disjunction.
- Preserve variables that occur only in a `[nonexec narrowing]` rule RHS and instantiate them in the
  selected outgoing fresh family; N-ch15-11 is the gate for this path. Preserve bare-variable RHS
  replacement identity with an explicit clone/hole record; N-ch15-01 covers it.
- `show most general states .` (folding only, `narrowing.cc:392-394`); `show path N .` /
  `show path states N .` (reuse `render_path` shape + `KEEP_HISTORY`/`KEEP_PATHS`).
- **Gate:** N01 (`fvu-narrow` + `set show breakdown on`), N-ch15-03 (`{filter}`/`{filter,delay}`),
  N-ch15-05, N-ch15-06, N-ch15-10, N-ch15-11 clean.

**Stage 4 — A/AU + the verbose protocol cluster (verifies N02, N-ch15-04/07/08/09).**
- Consume the completed S1 A/AU unifier (SMsgList `_,_ [assoc]`; N02's `_;_ [assoc id: nil]`).
- Parse and persist `set verbose on/off`; emit its lines on the same stream/order as the oracle.
  Reproduce every `subsumed by`/`evicted descendent` line, full wrapped terms, and the two terminal
  state-count lines. This is the last and hardest byte-exact gate.
- **Gate:** N-ch15-04, N-ch15-07, N-ch15-08, N-ch15-09, N02 clean.

**Stage 5 — meta narrowing (verifies N03).**
- Add dedicated `MetaOp` variants for `metaNarrowingApply`, `metaNarrowingSearch`,
  `metaNarrowingSearchPath`, and legacy `metaNarrow`; map their names out of `Deferred`.
- Add structurally keyed, four-entry persistent cache entries to `MetaState`, sharing S2's exact
  forward/equal/backward-index behavior and root ownership. Build the exact result tuples and
  `failure`/`failureIncomplete`; never recompute from zero as a fallback.
- Decode the single-step and sequence arrows/options/bounds exactly (`'#`, `'*`, `'+`, `'!`,
  `'none`/`'match`, `delay`/`filter`).
- For `metaNarrowingApply`, decode blocker `TermList`, incoming family Qid, `delay`/`filter`, and result
  index; return the exact split substitutions into the subject and rule plus the outgoing family.
- For sequence/path calls, decode arrow Qid, depth bound, fold Qid, options, and result index; no
  object-level `=>1` encoding exists here.
- Serve legacy `metaNarrow` according to resolved decision §8.2: v3-backed legacy result adapter when
  byte-exact on N03; otherwise the minimal v1-compatible path needed to keep every N03 command.
- **Gate:** all 102 N03 meta reductions, including repeated/forward/backward index probes, diff clean.

---

## 7. Verification and completion criteria

S3 is complete only when all of the following hold on one working tree:

1. `tools/subsystems-scoreboard.sh -p N` reports **15/15 PASS**, with no timeout, removed command,
   accepted divergence, or new normalization. All **168** substantive primary commands also pass
   through `tools/diffmaude-command.py` in isolation where the command is self-contained; stateful
   `show`/`continue` sequences remain covered by their full fixtures.
2. Exact output includes solution/state order, state numbers, parent/path history, accumulated
   substitutions, variant unifiers, fresh families, rewrite/breakdown counts, incompleteness, frontier
   and most-general-state displays, and every verbose folding-trace line.
3. Sequence-level unit tests pin emitted `(state, accumulated substitution, variant unifier)` streams,
   family alternation, fold/eviction order, unsupported-condition rejection, frozen-position skipping,
   bare and extra RHS-variable handling, `continue`, and meta cache forward/equal/backward/capacity
   behavior. Keep a slow unfolded breadth-first reference path live as a differential cross-check until
   the byte-exact N gate closes.
4. Existing gates remain green simultaneously: U **27/27**, V **21/21**, audit **77/77**, legacy
   **87/87**, `cargo test --release` (current baseline 394 tests), and all three stock libraries.
5. Object commands, `continue`, all `show …states/path` commands, current meta operations, and legacy
   `metaNarrow` are reachable end to end; no declared S3 operation remains in `MetaOp::Deferred`.
6. Refresh `subsystems-goal.md`, `roadmap.md`, `README.md`, `fable-audit.md`, and this plan's status/ledger
   with observed fixture and command totals. Do not begin SMT, model checking, or session extraction.

---

## 8. Resolved decisions (binding for S3)

1. **Nonterminating probe:** `N-probe-01` command 4 is `vu-narrow [1, 3] s(X) =>* z .`. The oracle
   returns `No solution.` with 9 rewrites. No expected-timeout harness mode and no manifest exclusion.
2. **Legacy `metaNarrow`:** keep the frozen N03 calls. Prefer a v3-backed `ResultTriple` +
   goal-matching adapter; if it is not byte-identical, implement the minimal v1-compatible semantics
   required by those calls. Do not expose or port the unused `metaNarrow2`, and do not carve lines out.
3. **Meta continuation:** use a persistent structurally keyed four-entry cache, matching the S2
   `MetaState` policy and the reference `MetaOpCache`. Stateless drive-to-nth is not acceptable.
4. **A/AU and AC:** resolved by S1's 27/27 gate; consume the existing solvers and preserve their
   incompleteness/order.
5. **Verbose trace:** reproduce it byte-exactly. Do not normalize folder-trace lines; their order is a
   real conformance surface.
