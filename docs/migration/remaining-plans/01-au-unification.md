# Associative (A / AU) unification — implementation record

**Status: DONE (2026-07-19).** The word-equation stack is in
`crates/tnk-core/src/unify/{au.rs,word/}`; AU dispatch and GC integration are in `unify/mod.rs`.
`tools/subsystems-scoreboard.sh -p U` verifies all 27 S1 fixtures (676 substantive commands) byte-for-byte
against Maude 3.5.1, and `cargo test --release` is green (394 tests). The staged sections below preserve
the preimplementation source/behavior map; present-tense “missing” claims describe that historical state.

Reference sources: C++ at `~/code/maude-lang/maude/src/{AU_Theory,Utility,Core,Interface,Mixfix}`; binary
oracle at `MAUDE_LIB=~/code/maude-lang/maude/src/Main ~/.local/bin/maude -no-banner`. Deep-dive backgrounder:
`reports/A8-symbolic-smt-ltl.md`. Decision record: `03-open-decisions.md`. Manual: §13.4.6 (associative),
§13.4.7 (associative + identity). The AC/ACU sibling plan (finished, byte-exact) is the closest template:
`crates/tnk-core/src/unify/acu.rs` + `int_system.rs`.

---

## 0. Honest scope (read first)

At the time this plan was written, AU was the **remaining** unification theory of S1 and, by a wide margin,
the **largest single theory to port**. The free / variable / S / CUI / AC-ACU solved-form machinery already
worked; AU was screened out and its subproblem arm was unreachable. Both temporary backstops have now been
removed.

Three facts frame the effort:

1. **The dispatch is already wired.** `compute_solved_form2`'s `NodeTerm::Acu | NodeTerm::Au` arm
   (`unify/mod.rs:1026-1046`) is already a faithful port of `AU_DagNode::computeSolvedForm2`
   (`AU_Theory/AU_DagNode.cc:315-351`): same-top ⇒ `pending.push`, unbound-variable-rhs ⇒ `pending.push`,
   else ⇒ `resolve_theory_clash`. The pending stack, `flag_as_incomplete`/`is_incomplete`, the
   solved-form protocol, `unification_priority`, `can_resolve_theory_clash` — all already handle AU. What is
   missing is the **subproblem solver** behind `make_unification_subproblem`'s AU arm (`unify/mod.rs:792`,
   currently `unreachable!`).

2. **The solver is a ~3,500-line self-contained algorithm.** Maude solves A/AU by reducing to **word
   equations over a free monoid** and running a modified PIG-PUG search, wrapped in a system-of-equations
   driver with identity/collapse handling. It lives in `~/code/maude-lang/maude/src/Utility/` as pure
   integer machinery (no DAG/engine dependency) — a clean seam that ports to a standalone, unit-testable
   Rust sub-module, exactly as `int_system.rs` did for the AC Diophantine core.

3. **A/AU is the only theory that can be incomplete.** PIG-PUG is complete only on *strict-left-linear*
   equations; otherwise Maude bounds the search (cycle detection or a depth bound) and sets an
   **incompleteness flag**. The warning *text* is stripped by the conformance harness (see §5), but the
   bound's **effect on the unifier set/count is fully load-bearing** — this is the subtlest conformance
   surface in the whole subsystem.

This plan covers the full port. The cheapest genuine vertical slice (pure-A, strict-left-linear, no
identity — §6 stage A1) verifies against real fixture output and is the recommended first milestone.

---

## 1. Subsystem overview

**What AU unification provides.** Order-sorted unification modulo the associativity axiom `f(f(a,b),c) =
f(a,f(b,c))`, optionally with a **two-sided identity** `f(e,x)=x=f(x,e)` (`assoc id: e`), for operators
declared `[assoc]` / `[assoc id: e]` — i.e. lists, sequences, string concatenation. It is **not**
commutative (that is the AC/ACU theory, `unify/acu.rs`). It backs:

- the `unify` / `unify [k]` / `irredundant unify` commands over AU operators (REPL: `tnk-repl/src/lib.rs:606-654`);
- the `metaUnify` / `metaDisjointUnify` / `metaIrredundant{,Disjoint}Unify` descent family
  (`tnk-modules/src/meta.rs:282-425`, already threaded for incompleteness — see §3);
- downstream, AU **variant** unification and **narrowing** (phases S2/S3), which sit on this solver.

**Its distinguishing role: incompleteness.** Associative unification is only semi-decidable in general;
Maude returns a finite (possibly incomplete) set and flags it. AU is therefore the subsystem that lights up
**risk-register item #7** (`roadmap.md:253` — "thread the assoc-unification incompleteness flag
unify→variant→narrow so warnings fire end-to-end"). The flag plumbing already exists; AU is its first real
producer.

**Fixtures exercised** (`conformance/subsystems/`, all confirmed against the oracle):

| Fixture | Theory features | Oracle shape (counts / warnings) |
|---|---|---|
| `U-ch13-14-assoc` | pure A: linear (finitary), no-unifier, cycle-detection + depth-bound incompleteness | 5 cmds: 5 unifiers / No unifier / 2/… / 1(+incomplete) / 3(+incomplete) |
| `U-ch13-15-assoc-id` | AU (`assoc id: nil`), `irredundant unify` | 3 unifiers (plain unify would give 32); prints `Decision time:` |
| `U04-assoc-unification` | pure A (`__`,`f`) + mixing (`h` AC, `j` ACU, `g`/`i` free); Delannoy-sized sets | **459 `unify`**, 396 `No unifier.`; **5 incomplete cmds**; sizes 1,3,5,13,25,41,…,3740 |
| `U05-au-unification` | AU (`assoc id: …`), order-sorted, AU×S / AU×comm cycle-breaking | 25 base `unify`; redundant duplicate unifiers. Its 18 `variant unify` commands now live in `V13-au-variant-unification`. |
| `U06-au-irred-unification` | same set as U05 but `irred unify` (minimal stable sets) | 25 `irred unify`; e.g. LIST `E L E M =? E N F N` → 3 (vs 10 plain) |
| `U07-au-a-edge-cases` | pure-A overloads + AU with sort-decreasing identity ("Alpha133" cases); `unify`+`irred` | 12 blocks; e.g. FOO2 `W =? Y Z` → 3 plain / 2 irred |
| `U11-check-unifiers` | META harness: base `metaUnify`, self-verifying; A/AC/ACU | 27 `reduce`; `unifierCount(A) unifierCount(B)`; **1 `unifierCountIncomplete`**. The `metaVariantUnify` half is `V12-check-variant-unifiers`. |
| `U01-unification` | kitchen-sink: free/AC/iter (all complete) + AU **one-sided-id** screen + unsafe `#`-name | 29 blocks; one-sided-id AU ⇒ "not currently supported" (stays screened) |

The `s_^k` iterated-successor input notation is implemented and covered by `U-ch13-07`, U05, U06, and U01.

---

## 2. Reference approach

Four layers, bottom-up. The bottom three are pure integer machinery in `Utility/`; only the top bridges to
DAGs.

### 2.1 The bridge — `AU_UnificationSubproblem2` (`AU_Theory/AU_UnificationSubproblem2.{cc,hh}`, ~600 lines)

This is the sibling of `unify/acu.rs`'s `AcuSubproblem`, and ports the same way.

- **`addUnification(lhs, rhs, marked)`** (`.cc:92-168`): each `f(…) =? f(…)` (or `f(…) =? X`) is turned into
  an **abstract word equation**. `assocToAbstract` (`.cc:225-238`) walks the AU node's `argArray`, mapping
  each argument to an integer via `dagToAbstract` (`.cc:170-223`): a variable is resolved to its chain
  representative (**never** substituted — the termination rule, same as ACU), an identity-bound variable is
  dropped (returns `NONE`), and every distinct subterm gets a stable index into `subterms[]`. The result is
  classified into `unifications` (word=?word), `assignments` (var|->word), or `nullEquations` (word that
  must be empty — only with identity). `marked` (theory-clash collapse) records the subterm in
  `markedSubterms`, forcing `upperBound=1`.
- **`makeWordSystem`** (`.cc:240-395`): builds the `WordSystem`, then per subterm sets **constraints**:
  `setTheoryConstraint(i, symbolIndex)` for a ground or *stable* alien (two different theory indices can
  never be equated); `setUpperBound(i, n)` from the variable's **`sortBound`** (an element sort ⇒ 1, a
  collector sort ⇒ unbounded); `setTakeEmpty(i)` from **`takeIdentity`** (the identity's sort ≤ the
  variable's sort). Then it feeds the null equations, assignments, and equations.
- **`solve(findFirst, …)`** (`.cc:417-488`): on first call, `preSolveSubstitution.clone`, then **unsolve**
  any existing in-theory solved forms `X = f(…)` back into equations (`.cc:438-444` — same termination hack
  as `acu.rs:227-233`), `makeWordSystem`, snapshot subst + pending checkpoint. Then loop
  `wordSystem->findNextSolution()`: if `INCOMPLETE`, `pending.flagAsIncomplete(topSymbol)`; if `SUCCESS`,
  `buildSolution`; on backtrack, restore subst+pending.
- **`buildSolution`** (`.cc:500-599`): materializes the word-system solution into DAGs. `abstractToFreshVariable`
  (`.cc:491-498`) creates a Maude fresh variable **on demand**, cached per abstract-variable index; the
  `REUSE_VARIABLES` pass (`.cc:517-541`) reuses an original variable when it is assigned exactly one abstract
  variable. Each subterm's assignment word (length 0 ⇒ identity DAG, 1 ⇒ the fresh/alien, ≥2 ⇒ a new AU node)
  is unified against the subterm via `computeSolvedForm` (re-entering the pending stack). **The order of
  `makeFreshVariable` calls fixes the fresh-variable slot order** (see §4, load-bearing).

### 2.2 `WordSystem` — the level-stack driver (`Utility/wordSystem.{cc,hh}`, ~190 lines, trivial)

Owns `current: WordLevel` + `levelStack: Vec<WordLevel>`. `findNextSolution()` (`.cc:36-69`) is a DFS over
levels: `current->findNextPartialSolution()` returns `(flags, child)`; `SUCCESS` with `child==null` ⇒
`current` is a complete solution (caller reads `getAssignment(i)`); `SUCCESS` with a child ⇒ push `current`,
descend into `child`; `FAILURE` ⇒ pop the stack (backtrack) or terminate. `INCOMPLETE` is OR-accumulated.

### 2.3 `WordLevel` — one system-of-equations state (`Utility/wordLevel*.cc`, ~2,000 lines)

The intricate middle layer. Three `LevelType`s: **`INITIAL`** (root; runs identity **selection**; simplifies
in *collapse* mode), **`SELECTION`** (identity-subset child of INITIAL), **`PIGPUG`** (residual after one
PIG-PUG unifier; simplifies in *normal*, collapse-free mode).

`findNextPartialSolution` (`wordLevel.cc:64-171`) **alternates** a deterministic `simplify()` pass with a
nondeterministic branch: pick an equation (`chooseEquation`) and solve it with a fresh `PigPug` (one
`PIGPUG` child per unifier), or — only at `INITIAL`, after PIG-PUG is exhausted — enumerate identity
selections. Key routines and their load:

- **`simplify()`** (`.cc:173-197`) → `simplifyEquations` to a fixed point (`wordLevel-simplifyEquations.cc`,
  **~460 lines, the single most intricate file**): left/right cancellation of equal end variables, null &
  singleton detection, `makeAssignment`, `unifyVariables`, cursor bookkeeping, and an `UNSAFE`-deferral for
  singletons already carrying a risky binding. `Result ∈ {FAIL, DONE, CHANGED, CONTINUE, UNSAFE}`.
- **assignment checking** — *normal* (`wordLevel-normalCase.cc`, ~185 lines: bound tightening, no collapse)
  vs *collapse* (`wordLevel-collapseCase.cc`, ~300 lines: forces unique collapses, marks unsafe, defers).
- **null equations** (`wordLevel-null.cc`, ~130): a word that must vanish; `makeEmptyAssignment` cascades.
- **selection** (`wordLevel-selections.cc`, ~310): after PIG-PUG, enumerate non-empty **subsets** of
  identity-capable variables to force empty. `nrSelections = (1<<nrIdVariables) - 1`, iterated as a bitmask;
  `identityOptimizations` narrows the candidate set to "pinched" variables (an over-approximation) and
  dedups via the INITIAL parent's `finalCombinations` set.
- `chooseEquation` (`.cc:254-309`): index-order scan; first strict-left-linear equation wins (right-linear
  flipped in place); determines linearity ∈ {NONLINEAR, STRICT_LEFT_LINEAR, LINEAR} passed to PIG-PUG.

### 2.4 `PigPug` — single word equation (`Utility/pigPug*.cc`, ~1,500 lines)

The Plotkin/PIG-PUG search. State = `lhsStack`/`rhsStack` of `Unificand{index, word}` + a `constraintStack`
+ a `path` of move codes. `getNextUnifier` (`pigPug.cc:124-155`) runs the DFS, then `extractUnifier`.

- **Three moves** (`pigPug.hh:85-138`): `RHS_PEEL` (`x… =? y…` → `x|->yx`, consume `y`), `LHS_PEEL`
  (`y|->xy`, consume `x`), `EQUATE` (`x|->y` or `y|->x`, consume both). Plus forced finals `LHS_TAKES_ALL` /
  `RHS_TAKES_ALL` when a side reaches one variable.
- **`firstMove`** (`pigPug-search.cc:59-105`): `cancel()` equal leading vars first, `feasible()`,
  depth-bound check, then try moves in the **fixed order `rhsPeel, lhsPeel, equate`** — *"it is critical
  that equate comes last"*. `nextMove` (`.cc:107-144`) backtracks via `undoMove` (`.cc:503-559`, decodes the
  move-code bit-set).
- **`equate` direction** (`.cc:341-501`): `lhsVar|->rhsVar` when the rhs constraint is the meet, else
  `rhsVar|->lhsVar` (`RHS_ASSIGN`); the incomparable case pushes a new constraint map. Chooses which
  variable survives — affects substitution content and downstream fresh numbering.
- **`extractUnifier`** (`pigPug-extract.cc:42-235`): replays `path` into a `Subst`; `compose2` prepends,
  `composeFinal` substitutes a suffix, both enforcing upper bounds (a late bound violation ⇒ `NONE`, the path
  is silently skipped). **Fresh variables** are numbered densely from `freshVariableStart`, in **increasing
  original-variable index order**, only for originals that appear in some binding's range (`.cc:160-224`).
- **Termination & incompleteness** (`pigPug.cc:81-98`): strict-left-linear ⇒ complete, no bound. Else if
  every unbounded variable occurs ≤2× ⇒ **cycle detection** (`pigPug-cycleDetection.cc`, ~240 lines:
  state-key dedup on remaining-words+bounds; marks infinite-family cycles → `INCOMPLETE`). Else ⇒ **depth
  bound** `depthBoundMultiplier * (|lhs| + |rhs|)` (`pigPug-search.cc:78-91`, cutoff → `INCOMPLETE`).
  `depthBoundMultiplier` is a static, default **1** (`pigPug.hh:143`), **not** user-settable (no `set`
  command references it — confirmed).

### 2.5 Conformance-load-bearing semantics

- **Enumeration order** (all deterministic, all observable in fresh-var numbering and unifier order):
  1. PIG-PUG move order `RHS_PEEL < LHS_PEEL < EQUATE`, depth-first;
  2. `equate` assignment direction (constraint meet);
  3. `chooseEquation` index-order preference;
  4. identity **selection** bitmask order (`1..nrSelections` over id-variables in increasing index) — **all
     base PIG-PUG solutions come out before any selection solution**;
  5. `WordSystem` level-stack DFS (a unifier's whole residual subtree precedes the next unifier).
  - **Observed net effect** (oracle): the full-length / non-collapse unifier is enumerated **first**, then
    identity/collapse unifiers, and within the collapse family the non-identity content sweeps positions
    **right-to-left** (e.g. `A B C =? a` → `C→a`, `B→a`, `A→a`).
- **Counts** are load-bearing including **redundant duplicates** (U05 emits `X→s 0, Y→0` *twice* — the
  identity over-generation; the `irredundant` filter later prunes it). The linear elementary cases follow
  **Delannoy numbers** D(n,m) (U04: 1,3,5,13,25,41,…).
- **Incompleteness effect** determines *which* and *how many* unifiers appear for the bounded cases (5 in
  U04, 1 in U11). The depth bound `= |lhs|+|rhs|` and the cycle-detection cutoff must be byte-exact.
- **Warnings** (verbatim, 4-space continuation): WARNING-A per operator, eager during solve, once per symbol
  — `flagAsIncomplete` (`Core/pendingUnificationStack.hh:126-136`): *"Unification modulo the theory of
  operator __ has encountered an instance for which it may not be complete."* WARNING-B trailing, on full
  exhaustion only — `doUnification` (`Mixfix/unify.cc:110-116`): *"Some unifiers may have been missed due to
  incomplete unification algorithm(s)."* At the **meta** level there is no text; incompleteness surfaces as
  `noUnifierIncomplete` in the result term.

---

## 3. What tnk already has to build on

Everything except the word-equation solver itself.

**Pending stack + solved-form protocol** — `crates/tnk-core/src/unify/mod.rs`:
- `PendingStack` (`:486-776`): `push`, `resolve_theory_clash`, `checkpoint`/`restore`, `solve` master loop,
  `choose_theory_to_solve` (by `unification_priority`), compound-cycle detection, and
  `flag_as_incomplete`/`is_incomplete` (`:585-591`) — **already the AU flag sink**.
- `UnifyContext` (`:65-181`): the slot-indexed substitution; `make_fresh_variable` (`:128-136`, kind-level,
  names from the central generator), `unification_bind`, `clone_subst`/`restore_from_clone`,
  `variable_node`, `gc_roots`.
- The AU dispatch arm `compute_solved_form2` `NodeTerm::Acu | NodeTerm::Au` (`:1026-1046`) — **already a
  faithful `AU_DagNode::computeSolvedForm2`**: same-top push, unbound-var-rhs push, `resolve_theory_clash`.
- `unification_priority` (`:425-440`) and `can_resolve_theory_clash` (`:444-453`) already cover AU
  (`Theory::Au => sym.identity().is_some()`).
- Shared helpers: `is_ground`, `insert_variables` (`BTreeSet`, ascending — the cycle-DFS order),
  `instantiate` (with an AU arm at `:295-307`), `last_variable_in_chain`, `var_index`.

**The one screen to lift** — `unimplemented_theory` (`unify/mod.rs:372-379`): today
`Theory::Au => sym.one_sided_identity() || true`. The fix is to drop `|| true`, leaving
`Theory::Au => sym.one_sided_identity()` — so two-sided-id and no-id AU become implemented while
**one-sided-id AU stays unimplemented** (matching `AU_DagNode.cc:324` `if (symbol()->oneSidedId()) return
DagNode::computeSolvedForm2(...)` — the backstop path U01 exercises and expects to abort).

**AU DAG representation** — `crates/tnk-core/src/`:
- `NodeTerm::Au { symbol, args: Vec<DagId> }` (`dag.rs:66`) = the flattened, ordered sequence.
- `Runtime::make_au` (`engine.rs:1908-1941`): flattens nested same-symbol args, drops identity args, empty ⇒
  identity DAG, singleton ⇒ the element — the canonical builder `instantiate`/`buildSolution` reuse.
- `dag_compare` AU arm (`engine.rs:2142-2155`): **length-first, then element-wise** (Maude's
  `AU_DagNode::compareArguments`) — the ordering invariant AU solutions must respect.

**Reusable constraint infrastructure** (the biggest single reuse win): Maude's `sortBound` and
`takeIdentity` live in the **shared** `Interface/associativeSymbol.hh:56` and `Interface/binarySymbol.hh:63`
base classes — identical for AU and ACU. tnk already ported them as engine methods:
`acu_take_identity` (`engine.rs:965-973`) and `acu_sort_bounds` (`engine.rs:986-1025`). They are **directly
usable** for AU's `makeWordSystem` constraint setup (an element-sort variable ⇒ `upperBound=1`; an
identity-capable variable ⇒ `setTakeEmpty`). (Cosmetic: consider renaming `acu_*` → `assoc_*`.)

**Order-sorted driver** — `unify/problem.rs` (`UnifyProblem`): the outer/inner enumeration
(`find_next` `:153-176` drives `pending.solve` then `find_order_sorted_unifiers`), the per-form `#k`
renaming in **slot order** (`:267-278`), and `generalized_sort` — which **already has an AU arm**
(`:374-385`, left-folds `operator_compose` over the flattened sequence). This means the display numbering
and sort solving need **no AU-specific work**; they consume whatever slots the AU solver creates.

**Fresh-variable generator** — `fresh.rs`: the single `#n` (Unify) generator with `with_base` for the meta
counter. Done; the AU solver just calls `ctx.make_fresh_variable`.

**Irredundant filter** — `unify/filter.rs`: `irredundant(engine, unifiers)` (already built, verified). U06,
U-ch13-15, and the `irred` half of U07 depend on it — **no AU-specific work**, it consumes the enumerated
sequence.

**Meta descent** — `tnk-modules/src/meta.rs`: `metaUnify` result encoding **already handles incompleteness**
(`:405` reads `prob.is_incomplete()`; `:419-422` emit `noUnifierIncomplete{,Pair,Triple}Symbol`). U11's
meta-incompleteness path is ready the moment the AU solver sets the flag.

**Not reused:** `int_system.rs` (Contejean–Devie Hilbert basis) is **AC-only** — AU uses word equations, a
disjoint algorithm. `au.rs` (the AU *matcher*) is conceptually parallel (its `flatten`/`compile` at `:52-83`
mirrors `assocToAbstract`) but is a different problem (matching, not unification); no code is shared, though
its flattening pattern is a useful reference.

---

## 4. Architectural fit & divergence analysis

**Enum-Theory fit.** AU slots into the closed `UnifySubproblem` enum (`unify/mod.rs:805-811`) as a new
`Au(au::AuSubproblem)` variant, exactly like `Acu(acu::AcuSubproblem)`. The three match arms
(`add_unification` `:823`, `solve` `:841`, `gc_roots` `:850`) gain an `Au` case; `make_unification_subproblem`
(`:781-799`) replaces the `unreachable!` AU arm with `AuSubproblem::new(e, symbol)`. This is the same
mechanical shape the ACU landing used — no new dispatch machinery.

**The clean sub-module seam.** Maude keeps the word-equation machinery in `Utility/` with **zero** DAG/engine
dependency: it operates on `Word = Vector<int>`, `Subst = Vector<Word>`, and a bit-packed
`VariableConstraint`. tnk should mirror this: a new module (e.g. `unify/word/` with `word_system.rs`,
`word_level.rs`, `pigpug.rs`, `constraint.rs`) of **pure integer machinery**, unit-testable standalone
(precisely how `int_system.rs` is tested independently of the engine). Only `au.rs`'s `AuSubproblem`
(the bridge, `<>` `AU_UnificationSubproblem2`) touches DAGs, the engine, `make_fresh_variable`, and
`compute_solved_form`. This isolation is a major de-risker: the hardest, most order-sensitive code (PIG-PUG
search) can be developed and diff-tested against Maude on *integer inputs* before any DAG plumbing exists.

**No BDDs.** The word system uses none; identity selection is a plain bitmask enumeration (the ACU identity
path's BDD `AllSat` is a *different* mechanism — it does not apply to AU). The order-sorted layer's BDDs
(`problem.rs`) run *after* the AU solver and are unchanged.

**GC discipline (D2).** `AuSubproblem` holds transient DAGs (`subterms`, the demand-created fresh variables,
`pre_solve`/`saved_subst` snapshots) and must expose `gc_roots()` — mirror `AcuSubproblem::gc_roots`
(`acu.rs:104-111`), wired into `UnifySubproblem::gc_roots` (`mod.rs:850-862`). The integer word machinery
holds no DAGs, so it needs no rooting. `UnifyProblem::gc_roots` (`problem.rs:329-338`) already sweeps the
pending stack, so once the `Au` arm reports roots, the command-boundary rooting is complete.

**Incompleteness flag threading (risk #7).** `PendingStack::flag_as_incomplete(top)` is called by the AU
solver when `findNextSolution` returns `INCOMPLETE`; `UnifyProblem::is_incomplete` (`problem.rs:135-137`)
already surfaces it, and both the REPL (`lib.rs:630`) and `meta.rs` already read it. **End-to-end plumbing is
done** — AU just becomes the first producer.

**Divergences that help.** Enum dispatch (no vtables on the hot search); the `Signature`/`Runtime`
`parts_mut()` split for building AU DAGs in `buildSolution`; `malachite` `Nat` for the meta base counter and
for `iter` counts (Maude uses `mpz`).

**Divergences that need care.**
- **Ownership vs. Maude's raw pointers.** Maude's level stack is `Vector<unique_ptr<WordLevel>>` and the
  `SELECTION` level keeps a raw `parent: WordLevel*` back-pointer (`wordLevel.hh:224`) purely to dedup via
  the parent's `finalCombinations` set (`wordLevel-selections.cc:310-333`). Rust cannot hold that back-pointer
  across an owning `Vec`. Re-encode: either hoist the dedup set into the `WordSystem` driver and pass it
  `&mut` into `find_next_partial_solution`, or keep levels in a `Vec<WordLevel>` indexed by `usize` and pass
  the parent index. This is a real (localized) design decision — flag at stage A4.
- **Sentinels.** Maude uses `NONE = -1`, `NOT_YET_CHOSEN = -2`, `UNBOUNDED = INT_MAX`, and the move-code
  bit-set. Port these as explicit consts/enums; the three same-named enums (`OutcomeFlags`,
  `WordLevel::Result`, `PigPug::Result`) must not be conflated (use distinct Rust enums).
- **`depthBoundMultiplier`.** A global static in Maude; make it a module const `= 1` (not user-settable).

**Invariants AU must respect.** (1) Variable/dag ordering: `dag_compare` AU length-first; variable-vs-variable
orientation keeps the more-constrained (larger per-kind sort index) representative (`mod.rs:1117-1137`) — the
AU bridge must call `unification_bind` with the same orientation Maude's `buildSolution` uses. (2) The
**fresh-variable creation order = slot order = display `#k` numbering**: `buildSolution` must call
`make_fresh_variable` in exactly Maude's order (the `abstractToFreshVariable`-on-demand order while
materializing subterm assignments left-to-right), because the order-sorted layer renames free slots `#1,#2,…`
in ascending slot order (`problem.rs:267-278`). This is the same discipline ACU's `build_solution`
(`acu.rs:563-626`) already follows and verifies byte-exact — copy it. (3) Never eagerly substitute a
variable bound *into* the AU theory (the unsolve step exists precisely to re-open such bindings for
simultaneous solving — `AU_UnificationSubproblem2.cc:438-444`, `acu.rs:227-233`).

---

## 5. Feasibility & risk

**Overall: feasible but the largest S1 item; correctness is fragile in two specific places.** The wiring is
done and the algorithm is fully specified and deterministic. The difficulty is volume (~3,500 lines of dense
C++) plus two byte-exactness knife-edges.

**Straightforward** (low risk, mostly mechanical, close templates exist):
- `WordSystem` driver (~40 real lines) — a plain DFS over an owned level stack.
- `VariableConstraint` (`variableConstraint.{hh,cc}`) — a bit-packed `u32`; the only subtlety is that
  `intersect` fails **only** on a theory-index clash and take-empty is conjunctive (`variableConstraint.cc:29-82`).
- The `AuSubproblem` bridge — mirrors `AcuSubproblem` (`acu.rs`) arm-for-arm: `add_unification` (=
  `assocToAbstract`/`dagToAbstract` classification), `solve` (pre_solve/saved_subst/saved_pending +
  unsolve-in-theory), `build_solution` (fresh-on-demand + reuse). The constraint setup reuses
  `acu_sort_bounds`/`acu_take_identity` verbatim.
- Order-sorted display, sort solving, `irredundant`, meta incomplete-encoding — **already done**.

**Hard / fragile (the real work):**
1. **`simplifyEquation` and the collapse case** (`wordLevel-simplifyEquations.cc` ~460 +
   `wordLevel-collapseCase.cc` ~300). The two cancellation loops, cursor bookkeeping, the `UNSAFE` deferral,
   and the unique-collapse forcing interact subtly; a wrong `DONE`/`CHANGED`/`CONTINUE`/`UNSAFE` verdict
   silently changes the solution set. **Highest porting risk.**
2. **PIG-PUG search order + `equate` direction + fresh numbering** (`pigPug-search.cc` ~500 +
   `pigPug-extract.cc` ~330 + `pigPug-cycleDetection.cc` ~240). These jointly determine the exact solution
   *sequence* being matched byte-for-byte. The move order (`RHS<LHS<EQUATE`, equate last), the forced-final
   moves, the constraint-meet assignment direction, and the dense original-order fresh numbering all must be
   exact.

**Biggest byte-exactness risks:**
- **Enumeration order.** The nested DFS (move order × `chooseEquation` × selection bitmask × level-stack)
  fixes both unifier order and `#k` numbering. *Mitigation:* it is fully deterministic and specified; port
  line-faithfully; the order-sorted + fresh-renaming layers are already proven for ACU, so if the AU solver
  emits slots in Maude's order, display falls out for free.
- **The incompleteness bound's effect.** Even though the harness strips warning text (see next bullet), the
  depth bound (`= |lhs|+|rhs|`) and cycle-detection cutoff decide the exact unifier **count** for the 5 U04
  and 1 U11 bounded cases. An off-by-one in the bound, or a wrong cycle state-key, diverges the count. This
  is the subtlest surface; test the bounded cases explicitly and early (stage A2).
- **Redundant duplicates are load-bearing.** Plain `unify` must reproduce Maude's over-generation exactly
  (U05's doubled `X→s 0`), because the `irredundant` filter's output depends on the pre-filter sequence. Do
  **not** "optimize away" duplicates in the plain path.

**What de-risks the effort:**
- **Warning *text* is out of scope for the byte-exact goal.** `tools/diffmaude.sh` normalization strips
  `Warning:`/`Advisory:` blocks on *both* sides (documented in the harness header), and the REPL already
  discards the flag (`lib.rs:632` `let _ = incomplete; // phase-E (stripped)`). So the two incompleteness
  warnings need **not** be emitted for S1 conformance — only their *effect* on the unifier set matters. (The
  flag and per-symbol set are available if phase-E later wants to emit them.)
- **The integer seam** lets the fragile search be built and diff-tested standalone before DAG plumbing.
- **ACU is a proven, close template** for the bridge, the snapshot/restore protocol, and the fresh-var
  discipline.

**Not a concern:** performance. Correctness-first; the fixtures are small. (Maude precomputes a per-sort
`sortPathTable` etc.; tnk can recompute — a later perf follow-up, as elsewhere.)

---

## 6. Implementation plan (completed)

All stages A0–A5 below landed. The smallest vertical slice was A1; the final implementation also includes
nonlinear cycle/depth bounding, multi-equation simplification, identity selection/collapse, mixed-theory
integration, exact duplicate behavior, and metalevel incompleteness propagation. The stage checkpoints
remain useful as a subsystem map.

**A0 — wiring + subproblem skeleton.**
- `unify/mod.rs:376`: `Theory::Au => sym.one_sided_identity()` (drop `|| true`).
- Add `UnifySubproblem::Au(au::AuSubproblem)`; add the three match arms; replace the `unreachable!` AU arm in
  `make_unification_subproblem` with `AuSubproblem::new`.
- New module `unify/au.rs` (bridge) + `unify/word/` skeleton. Implement `add_unification`
  (`assocToAbstract`/`dagToAbstract` classification into unifications/assignments/nullEquations, marked
  handling) and `gc_roots`. `solve` returns "no solutions" for now.
- *Checkpoint:* compiles; screening lifts for two-sided/no-id AU; one-sided-id AU still aborts (U01 block
  unchanged). No unifiers yet.

**A1 — pure-A, strict-left-linear (the vertical slice).**
- `VariableConstraint` (`constraint.rs`); `WordSystem` (`word_system.rs`); `WordLevel` INITIAL→PIGPUG
  spine with `simplify`/`chooseEquation`/`makePigPug`/`makeNewLevel`; `PigPug` `run`/`firstMove`/`nextMove`/
  `cancel`/`rhsPeel`/`lhsPeel`/`equate`/`undoMove` **for the strict-left-linear case only** (no cycle
  detection, no depth bound, no `equateOptimization`); `extractUnifier`. `AuSubproblem::solve` +
  `build_solution` (fresh-on-demand + `reuse_variable`).
- *Verify:* U04 opening blocks — `A B =? X`(1), `A B =? X Y`(3), `A B C =? X Y`(5), `A B C =? X Y Z`(13),
  `A B C D =? X Y Z`(25), … (Delannoy D(n,m)); exact order + `#k` numbering.

**A2 — non-linear A: cycle detection + depth bound + the flag.**
- `pigPug-cycleDetection.cc` (state-key dedup, infinite-family marking), the depth-bound cutoff
  (`= |lhs|+|rhs|`), and `flag_as_incomplete` on `INCOMPLETE`.
- *Verify:* `U-ch13-14-assoc` (all 5, incl. `No unifier.` and the 2 incomplete cases → exactly 1 and 3
  unifiers); `U04` in full (459 cmds incl. the large PIG-PUG dead-cycle battery → mostly `No unifier.`, and
  the **5 incomplete cmds** → counts 2,1,1,2,1). **This is the count-fragile stage — test the bound
  arithmetic directly.**

**A3 — multi-equation systems + full simplification.**
- `simplifyEquations` to a fixed point (normal case), `chooseEquation` linearity classification, simultaneous
  unification across equations, `fullyExpandAssignments`, `unifyVariables`.
- *Verify:* U04 simultaneous cases (e.g. `A B C =? X Y Z /\ G H I =? M N` → 65); U07 conjunction cases
  (`P =? A B /\ X P =? P Y` → 3).

**A4 — identity / collapse (AU).**
- `wordLevel-collapseCase.cc` (unsafe-marking, unique-collapse), `wordLevel-null.cc` (null equations,
  `makeEmptyAssignment`, `resolveOccursCheckFailure`), `wordLevel-selections.cc` (id-variable selection
  bitmask, pinch over-approximation, `finalCombinations` dedup — resolve the `parent*` re-encoding here),
  `identityOptimizations` + PIG-PUG `equateOptimization` (`doublePeelPossible`), and the `setTakeEmpty`/
  `sortBound` constraint setup (reuse `acu_take_identity`/`acu_sort_bounds`). Materialize length-0 assignment
  words as the identity DAG (`make_au` empty ⇒ identity).
- *Verify:* `U-ch13-15-assoc-id` (`irredundant unify` → 3, plain would be 32 — confirms the filter consumes
  the right pre-filter sequence, and `Decision time:` prints); `U07` AU-id edge cases (FOO2 `W =? Y Z` →
  3 plain / 2 irred); `U06` (needs `s_^k` for the NAT' cases — see §8).

**A5 — integration + mixed fixtures.**
- End-to-end `irredundant` over AU (filter already built); `metaUnify` over AU → U11 (meta incomplete
  encoding already present); mixed-theory fixtures.
- *Verify:* `U11-check-unifiers` (27 `reduce`, incl. the 1 `unifierCountIncomplete`); `U05`/`U01` (both need
  `s_^k`; U01 also re-confirms the one-sided-id screen + unsafe-`#`-name block shape). Optionally emit
  WARNING-A/B at the REPL (phase-E, since stripped).

---

## 7. Verification

**Primary harness.** `tools/diffmaude.sh <fixture.maude>` per fixture: runs tnk and the oracle with matched
flags, normalizes (strips `====` separators, banner/`Bye.`/prompts, the timing tail, and — crucially —
`Warning:`/`Advisory:` blocks), and diffs. Byte-exact on **unifier sets, counts, order, and `#k`
numbering**; incompleteness warnings are normalized away, but the bounded counts are not. Fixture→stage map:

| Stage | Fixtures gated | What it proves |
|---|---|---|
| A1 | `U04` (opening blocks) | strict-left-linear A, Delannoy counts, order, `#k` |
| A2 | `U-ch13-14`, `U04` (full) | cycle detection + depth bound; incomplete counts (2,1,1,2,1) |
| A3 | `U04` (simultaneous), `U07` (conjunctions) | multi-equation simplification |
| A4 | `U-ch13-15`, `U06`, `U07` (AU-id) | identity/collapse/selection + irredundant |
| A5 | `U11`, `U05`, `U01` | meta incompleteness, mixed theories (+ `s_^k`) |

**Unit tests on emitted sequences** (mirror `unify/mod.rs`'s `all_solved_forms` tests, `:1430-1604`): assert
exact unifier count and content for small A/AU problems — e.g. `A B =? X Y` → 3 unifiers in order; `A B C =?
a` → `C→a, B→a, A→a` (the right-to-left collapse sweep). Test the incompleteness path: a known-incomplete
problem yields the exact bounded count *and* sets `is_incomplete()`.

**Standalone word-machinery tests** (mirror `int_system.rs`'s independent tests): drive `PigPug`/`WordSystem`
on **integer words** directly (no engine), asserting the exact substitution sequence and the
`INCOMPLETE`/`SUCCESS`/`FAILURE` outcome bits. This is the highest-leverage test surface because it isolates
the two fragile areas (§5) from DAG plumbing and can be diffed against Maude's own `Utility` behavior via
targeted C++ probes if needed.

**Naive differential cross-check** (the ac-matcher-plan discipline, `ac-matcher-plan.md:33-36`): for the
**finitary** (strict-left-linear) cases, a bounded brute-force A-unifier generator can confirm the produced
set is complete and correct **modulo renaming** (the ground truth exists for these cases). Not applicable to
the bounded/incomplete cases — there is no ground truth, so those rely solely on the oracle diff.

**Regression backstop.** The full existing S1 suite (77/77 audit, the `U01`-`U03`/`U08`-`U10` non-AU
fixtures) must stay green — the screening flip and the new enum arm must not perturb free/CUI/S/ACU paths.

---

## 8. Resolved questions / decisions

1. **`s_^k` input notation:** implemented in the prefix-iteration grammar and covered by S1 fixtures.

2. **Selection-level dedup ownership:** `WordLevel` shares an `Rc<RefCell<SelectionDedup>>` across the
   selection chain. This preserves Maude's parent-chain dedup semantics without pointers into moving Rust
   values.

3. **Warning-A/B text emission:** remains out of S1 scope under the repository's recorded diagnostic-parity
   policy. The incompleteness flag and its effect on bounded result sets propagate exactly; the harness
   intentionally normalizes diagnostic prose.

4. **`depthBoundMultiplier`:** confirmed not user-settable; the Rust bound is exactly `lhs.len() + rhs.len()`
   for the applicable nonlinear case.

5. **`equateOptimization` / `identityOptimizations`:** ported with Maude's single-linear-equation scope;
   U05/U06 cover its byte-visible AU redundancy behavior.

6. **Redundant duplicates:** intentionally reproduced before irredundant filtering, including U05's doubled
   `X→s 0`; this is part of the verified sequence contract.

7. **Shared helper names:** `acu_sort_bounds`/`acu_take_identity` remain named for their first consumer but
   are deliberately reused by AU. This is cosmetic debt only, not a blocker.
