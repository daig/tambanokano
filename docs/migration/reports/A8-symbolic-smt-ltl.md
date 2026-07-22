# A8 — Symbolic reasoning, SMT, LTL, Full Maude/OO (deep-dive report)

This subsystem sits *on top of* the kernel (A1), matching/unification primitives (A2)
and the sort lattice (A3). It consumes the per-theory `computeSolvedForm` /
`UnificationSubproblem` machinery and the `SortBdds` and turns them into user-facing
symbolic capabilities: order-sorted unification, variants & variant unification, narrowing,
SMT solving, LTL model checking, plus the OO desugaring and the experimental FullCompiler.

---

## 1. Order-sorted unification (`unify`, `irredundant unify`)

**Functional scope** — Manual ch.13 (7454–7976): E∪Ax-unification decomposed into Ax-unification
(built into C++) + E∪Ax on top (variants, §below). Supported axioms: free, `iter`, C, AC, ACU, AU,
CU, U/Ul/Ur; A is *incomplete* (warns); `idem` excluded (do via variants). Order-sorted (endogenous)
algorithm; `irredundant` returns a minimal complete set; incompleteness is tracked and warned.

**Architecture in C++** — `Higher/unificationProblem.cc`. The constructor normalizes terms, indexes
variables, checks "safe" `#n`/`%n` names, builds dags, and drives a *two-phase* algorithm:
(1) **unsorted solved form** — for each equation `leftHandDags[i]->computeSolvedForm(rhs, *unsortedSolution, pendingStack)`
(`unificationProblem.cc:143-153`); the actual combination of theories (Boudet, theory clash split,
compound-cycle handling, manual 13.7.1) lives in `PendingUnificationStack` + per-theory
`UnificationSubproblem`s (A2). (2) **order-sorted filtering** — `findOrderSortedUnifiers()`
(`:305-476`) allocates BDD variables per free variable, conjoins `leqRelation` BDDs from `SortBdds`,
computes a `maximal` BDD (via `bdd_appall`/quantification) and hands it to `AllSat`
(`:442`) to enumerate maximal sort assignments; `bindFreeVariables()` (`:248`) materializes
fresh `VariableDagNode`s. Dispatch is C++ **virtual** (`UnificationProblem::findNextUnifier` is
`virtual`; `IrredundantUnificationProblem` overrides and wraps a `UnifierFilter`,
`irredundantUnificationProblem.hh:30-55`). `isIncomplete()` is read off `pendingStack` (`:101-105`).
GC integration via `SimpleRootContainer::markReachableNodes` (`:178`).

**Rust migration** — RETHINK the dispatch, PORT the algorithm. The unifier is essentially an
**iterator** `impl Iterator<Item = Substitution>`; expose `findNextUnifier` as `next()`. The
unsorted/order-sorted split should stay: the solved-form layer calls A2's theory enum;
the order-sorted layer needs a BDD engine — there is **no idiomatic Rust BDD crate at BuDDy's
maturity**; either wrap BuDDy via FFI initially or use `biodivine-lib-bdd` (pure Rust, well
maintained) — *rationale: the AllSat/maximality computation is on the critical path and is hard to
re-derive.* `irredundant` = a post-filter combinator over the iterator. Drop manual `markReachableNodes`
in favor of arena handles owned by the iterator (A1).

---

## 2. Variants & variant unification (`get variants`, `variant unify`, `variant match`)

**Functional scope** — Manual ch.14 (7976–8316): folding variant narrowing (Escobar–Sasse–Meseguer),
FVP detection, incremental generation with a bound, irreducibility constraints (`such that … irreducible`),
filtered (minimal) variant unifiers, variant matching (rhs treated ground). Variant unification reduces
to variants of `eq(t,t') → tt` (manual §14.8).

**Architecture in C++** — `Higher/variantSearch.{hh,cc}` is the engine, parameterized by `Flags`
(`UNIFICATION_MODE`, `IRREDUNDANT_MODE`, `SUBSUMPTION_MODE`, `MATCH_MODE`,
`variantSearch.hh:45-54`). It is a **layered BFS**: `expandLayer()`/`expandVariant()`
(`variantSearch.cc:398-490`) run one variant-narrowing step per node via
`VariantNarrowingSearchState`, then `VariantFolder::insertVariant` (`variantFolder.hh:52`,
`.cc`) keeps the "most general so far" map and **evicts subsumed variants and all their descendants**
— this *is* the folding strategy. `findNextUnifier` (`variantSearch.cc:57-80`) just walks surviving
variants whose size equals `nrVariantVariables`. `VariantUnificationProblem`
(`variantUnificationProblem.hh`) wraps `VariantSearch` for the narrowing step;
`FilteredVariantUnifierSearch : public VariantSearch` (`filteredVariantUnifierSearch.hh:36`) adds a
`VariantUnifierFilter` for minimal unifiers; `VariantMatchingProblem` does matching (compiles
`LhsAutomaton`s from retained variants, `variantFolder.hh:103`).

**Rust migration** — PORT as the symbolic backbone. `VariantFolder` is a clean fit for Rust:
a `BTreeMap<usize, RetainedVariant>` plus a subsumption check; eviction of descendants is a tree
prune. The `Flags` int-bitmask → a small config struct or `bitflags!`. `VariantSearch` becomes a
lazy layered iterator; the four "modes" are better expressed as **separate iterator adapters**
sharing the folder rather than one class with a mode flag — *rationale: removes the pervasive
`if (flags & …)` branching and makes match/unify/subsume statically distinct.* Subsumption needs the
A2 matching automata, so this depends on A2 exposing a "compile term → matcher" API.

---

## 3. Narrowing (`vu-narrow`, `fvu-narrow`)

**Functional scope** — Manual ch.15 (8317–8582): R,E∪Ax narrowing for symbolic reachability;
arrows `=>1/=>+/=>*/=>!`; `narrowing` rule attribute; folding (`fvu`) builds a reachability *graph*;
narrowing-with-simplification (equations without `variant`); extra rhs variables (`nonexec`); frozen args.

**Architecture in C++** — three generations coexist; the live one is
`Higher/narrowingSequenceSearch3.{hh,cc}` + `narrowingSearchState3` + `narrowingFolder`.
`NarrowingSequenceSearch3` (`narrowingSequenceSearch3.hh:34`) is BFS over states; each step uses
variant unification (`VariantUnificationProblem`) of a rule lhs against subdags; the final
state-vs-goal test uses a `VariantSearch` (`:197`). `NarrowingFolder` (`narrowingFolder.hh:44`)
optionally folds states by matching/variant subsumption (`FOLD`/`VFOLD`) and keeps history
(`KEEP_HISTORY`/`KEEP_PATHS`, flags `:42-64`) for path reconstruction. Substitutions are accumulated
along the path (`addAccumulatedSubstitution`).

**Rust migration** — PORT, but **delete the two dead generations** (`narrowingSearchState`/`2`,
`narrowingSequenceSearch`) — keep only the v3 design. Model as a `SequenceSearch` trait returning an
iterator of (state, accumulated-subst, unifier). Folder reuses §2's folder logic. History/path
tracking → an explicit DAG arena with parent indices (already the C++ shape) rather than raw pointers.

---

## 4. SMT solving (`check`, `smt-search`) + variant satisfiability

**Functional scope** — Manual ch.16 (8583–8680): QF Booleans, Presburger integers, rational LA,
mixed int/rat; `check` answers sat/unsat; `smt-search` does rewriting modulo SMT; **one** solver
(CVC4 **or** Yices2) is chosen at build time. Variant satisfiability (§16.6) is a Maude-level
prototype using variant unification.

**Architecture in C++** — Clean **abstract-base FFI seam**: `SMT/SMT_EngineWrapper.hh` declares
`assertDag/checkDag/push/pop/clearAssertions/makeFreshVariable` (`:46-54`), returning a
`Result` enum (`SAT/UNSAT/SAT_UNKNOWN/BAD_DAG`). Concrete impls are `VariableGenerator` in
`Mixfix/yices2_Bindings.{hh,cc}` and `cvc4_Bindings.{hh,cc}`, which translate `DagNode`→solver
`term_t` (`yices2_Bindings.hh:60-62`) caching variables in a map. SMT operators are inert at the
Maude level: `SMT_Symbol : public FreeSymbol` with an `OPERATORS` enum (`SMT_Symbol.hh:31-`),
constants via `SMT_NumberSymbol/Term/DagNode`; sort↔type mapping in `SMT_Info`
(`SMT_Info.hh:33-90`, BOOLEAN/INTEGER/REAL by sort index). `SMT_RewriteSequenceSearch`
(`SMT_RewriteSequenceSearch.hh`) accumulates a per-state `constraint` dag and a `MatchSearchState`,
calling `engine->checkDag` to prune infeasible states.

**Rust migration** — ADAPT. D7 is now bound: keep a narrow
`trait SmtEngine { assert_dag/check_dag/clear/push/pop }` in core, with the concrete `z3` 0.20.2
translator/backend behind `smt-z3`; the default selects a pure-Rust null backend. Fresh
`#n-Base` DAGs are engine-owned, not a solver method. The DAG→solver translation is a recursive
match plus exact bignum/rational string conversion. Variant satisfiability remains a separate
deliverable over variant unification. The official 2016 Maude-2.7 prototype is now recovered and
checksum-pinned as an executable oracle; because its source has no explicit license and its reflective
dependencies/API are obsolete, phase T6 implements a new native Rust decision procedure behind a
compatible `VAR-SAT-TOOL` facade rather than copying it.

---

## 5. LTL model checking (`modelCheck`) + LTL SAT/tautology (`satSolve`/`tautCheck`)

**Functional scope** — Manual ch.12 (7102–7453): on-the-fly LTL model checking returning
`true` or a `counterexample(leadIn, cycle)`; SATISFACTION/`_|=_`, MODEL-CHECKER, LTL-SIMPLIFIER;
SAT-SOLVER for satisfiability/tautology with finite models.

**Architecture in C++** — bridge in `Higher/modelCheckerSymbol.{hh,cc}`, engine in `Temporal/`.
`ModelCheckerSymbol::eqRewrite` (`modelCheckerSymbol.cc:253-309`): negates the formula, reduces it
(the LTL prelude equations do NNF + simplification), builds a `LogicFormula` via `TemporalSymbol::build`,
constructs a `StateTransitionGraph` (lazy on-the-fly state generation by rewriting), then runs
`ModelChecker2` and turns `getLeadIn()`/`getCycle()` into a counterexample term
(`makeCounterexample :233-242`). The system is decoupled from rewriting by an abstract interface
`ModelChecker2::System { getNextState; checkProposition }` (`modelChecker2.hh:42-46`), implemented by
`SystemAutomaton` (`:311-333`, `checkProposition` reduces `state |= prop` and compares to `true`).
`ModelChecker2` is **nested double DFS** (Holzmann–Peled–Yannakakis, `modelChecker2.hh:26-29`) over
the product with `BuchiAutomaton2`. The LTL→Büchi pipeline: `LogicFormula` → very-weak alternating
automaton (`veryWeakAlternatingAutomaton`) → generalized Büchi (`genBuchiAutomaton`, Gastin–Oddoux,
`genBuchiAutomaton.hh:26-37`) with **BDD-encoded transition labels** and SCC optimizations
(Somenzi–Bloem; `sccAnalysis`/`sccOptimizations`). `satSolverSymbol`/`satSolve.cc` reuse the GBA for
LTL satisfiability/tautology (`satSolverSymbol.hh`).

**Rust migration** — PORT the algorithms (they are self-contained graph/automata code, the *least*
pointer-heavy part of Maude). The `System` interface → a Rust trait, decoupling the checker from the
rewrite engine cleanly. BDD label encoding again needs `biodivine-lib-bdd` or BuDDy-FFI. Nested DFS and
SCC analysis are textbook ports using `NatSet`→`FixedBitSet`/`HashSet`, `IndexedSet`→an interning
`Vec`+`HashMap`. *Rationale: this subsystem is algorithm-dense but data-structure-light, so it ports
almost verbatim and is good early Rust practice.*

---

## 6. Full Maude & OO modules

**Functional scope** — Manual chs.21–22 (11348–12429): OO modules (`omod`, classes, attributes,
messages, inheritance via subsorts, attribute-omission/object completion, subclass-aware matching),
OO parameterization/views, TUPLE/POWER, Ax-coherence completion, up/down reflection. Historically
Full Maude (a `.maude` metaprogram) added these; much OO support has since moved into **Core Maude C++**.

**Architecture in C++** — `Mixfix/ooTransform.cc`, `ooSorts.cc`, `ooView.cc`, `ooRenaming.cc`,
`ooProcess.cc`. `ooSorts.cc` *heuristically discovers* the `Cid`/`Attribute`/`AttributeSet` sorts
from the object-constructor symbol's op-declarations (`ooSorts.cc:62-90, 92-172`). `ooTransform.cc`
implements a `StatementTransformer` that desugars equations/rules/memberships ("object completion":
fills in unmentioned attributes, adds `AttributeSet` variables so subclass objects match,
`ooTransform.cc:27-102`). `ooView`/`ooRenaming` extend view/renaming maps to classes/attrs/msgs.

**Rust migration** — RETHINK as a **frontend desugaring pass** (belongs with A4/A5, not a runtime
feature): parse `omod`/class/msg syntax → ordinary order-sorted module + transformed
statements. This is pure tree-rewriting and ports naturally to Rust visitors. The standalone
**Full Maude metaprogram itself is out of scope as engine code** — it is a `.maude` library that runs
on the meta-level; ship it as data, not Rust. *Rationale: keeping OO as a desugaring keeps the runtime
free of OO special cases, exactly as the C++ now does.*

---

## 7. FullCompiler (experimental)

`FullCompiler/` compiles a module to standalone C++: `CompilationContext`
(`compilationContext.hh:30-59`) writes `.hh`/`.cc`, emits an `eval()` per module and sort vectors;
`runtime.cc`/`runtime.hh` provide a hand-rolled GC'd `Node` arena (tagged union `symbol`/`fwd`,
`MAX_NR_ARGS 20`, `runtime.hh:33-59`). It is tiny (~0.9k), free-theory-only, and not wired into normal
use. **Recommendation: DROP for parity-1.** If a compiled path is wanted later, RETHINK as Rust
codegen or a Cranelift/LLVM JIT over the A1 stack-machine — not a port of this prototype.

---

## 8. Hardest parts / risks / open questions

- **BDD dependency is pervasive** (order-sorted unifier filtering §1, ACU Diophantine selection in A2,
  GBA transition labels §5). The single biggest external-lib decision: pure-Rust `biodivine-lib-bdd`
  vs. FFI to BuDDy. Recommend prototyping `biodivine-lib-bdd` early on §1.
- **Incompleteness propagation** (associative unification) is threaded through unify→variant→narrow as
  a boolean flag; must be preserved end-to-end so the right warnings fire (manual 13.4.6, 14.7, 14.12).
- **Variable families** (`#n` vs `%n`, the `variableFamilyToUse`/`disallowedVariableFamily` plumbing,
  `unificationProblem.cc:61`, `variantUnificationProblem.hh:75`) are fiddly fresh-variable-counter
  bookkeeping that is easy to get subtly wrong; needs a single shared `FreshVariableGenerator` abstraction.
- **SMT backend swap** (CVC4/Yices2 → Z3) changes the term-translation surface; the `SMT_EngineWrapper`
  abstraction makes this safe but `assertDag` semantics (incremental push/pop) must match.
- **Three narrowing generations** in the tree — confirm only v3 is reachable before porting (dead-code risk).
- **OO sort discovery is heuristic** (unique-candidate search) and emits warnings on ambiguity; the Rust
  port must reproduce these diagnostics or users' modules silently change meaning.

---

## 9. Proposed Rust module layout

```
crates/symbolic/
  unify/          # order-sorted unification: UnificationProblem iterator, irredundant filter
    order_sorted.rs   # BDD maximal-sort enumeration (wraps bdd backend)
    filter.rs         # UnifierFilter / minimal complete set
  variant/        # folding variant narrowing
    search.rs         # layered BFS (was VariantSearch)
    folder.rs         # most-general-so-far map + descendant eviction
    unify.rs          # variant unify + filtered (minimal) unifiers
    matching.rs       # variant match
  narrow/         # symbolic reachability
    sequence.rs       # BFS (was NarrowingSequenceSearch3) — v3 only
    folder.rs         # state folding + history/paths
  smt/
    engine.rs         # trait SmtEngine (assert/check/push/pop/fresh_var)
    z3.rs             # default backend (z3 crate) behind a feature
    translate.rs      # DagNode -> solver term
    rewrite_search.rs # rewriting modulo SMT (smt-search)
  ltl/            # self-contained automata pipeline
    formula.rs        # LogicFormula (NNF)
    vwaa.rs           # very-weak alternating automaton
    buchi.rs          # generalized + degeneralized Büchi (Gastin-Oddoux), SCC opt
    model_check.rs    # nested DFS over product; System trait
    sat.rs            # LTL satisfiability / tautology
  bdd/            # shared BDD facade over biodivine-lib-bdd (or BuDDy FFI)
crates/frontend/oo/   # OO desugaring pass (with A4/A5): omod -> module + transformed statements
# FullCompiler: omitted from parity-1
```

Cross-crate: `symbolic` depends on `theories` (A2: `computeSolvedForm`, matching automata),
`sorts` (A3: `SortBdds`), `kernel` (A1: DagNode arena, RewritingContext). `bdd` is shared by
`unify`, `theories`, and `ltl`.
