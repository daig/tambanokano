# TNK-005 goal — compositional strategy-module imports (the `/goal` contract)

**Status:** complete; all behavior, recovery, reflection, lifecycle, and retained-suite gates passed on 2026-07-26.  
**Frozen baseline:** Maude 3.5.1 and tnk commit `9790dc1` (`2026-07-26`).  
**Primary closure record:** `docs/bug-triage.md`, TNK-005.  
**Purpose:** this remains the binding correctness contract and implementation record. The live code and
six retained oracle fixtures now satisfy the work graph and completion gate; the ledger in §9 records the
observed closeout rather than a future plan.

## Goal statement

Make strategy modules compose through tnk's existing module algebra. A strategy declared or defined in an
imported `smod` must be available to an importing `smod`, with Maude-compatible declaration identity,
definition matching, donation order, duplicate handling, home-grammar parsing, ordinary module
transformations, reflection, result order, and rewrite counts.

The motivating repro is deliberately small:

```maude
smod STRAT-BASE is
  sort S .
  ops a b : -> S .
  rl [r] : a => b .
  strat go @ S .
  sd go := r .
endsm
smod STRAT-USE is
  protecting STRAT-BASE .
endsm
srew in STRAT-USE : a using go .
```

Maude 3.5.1 returns one `S: b` solution with one rewrite. The frozen tnk baseline rejected `go` as neither a
rule label nor a strategy of `STRAT-USE`; the completed implementation now returns the oracle result. The
full six-fixture matrix, rather than this one repro alone, defines completion.

---

## 0. Authority and confirmed baseline

When sources disagree, use this order:

1. the live Maude 3.5.1 binary on a minimal source fixture;
2. Maude's implementation, especially `Mixfix/process.cc`, `Mixfix/importModule.cc`,
   `Mixfix/strategyDefinition.cc`, `Mixfix/global.cc`, and `Mixfix/renaming.cc`;
3. the Maude manual, Chapter 10.2–10.3 (strategy declarations, definitions, and calls);
4. this document;
5. older roadmap, audit, and triage prose.

Never choose behavior from memory. If a new probe contradicts this document, preserve the probe, explain
the discrepancy, and amend the contract before changing code.

### 0.1 Frozen repository baseline

At commit `9790dc1`:

- `crates/tnk-modules/src/flatten.rs:197-204` copies only the root `PreModule`'s `strat_decls` and
  `strat_defs`; imported strategy metadata never enters the flattened accumulator.
- `crates/tnk-frontend/src/strategy.rs:210-217` compiles unconditional, zero-argument definitions into
  `HashMap<String, Rc<RStrat>>`; later definitions overwrite earlier definitions of the same name.
- `crates/tnk-frontend/src/strategy.rs:612-642` and `1249-1256` resolve and execute calls by bare name,
  not by declared argument profile and matching definition lhs.
- `crates/tnk-frontend/src/load.rs:118-128` already accepts a statement-home vector for ordinary imported
  statements. Strategy definitions have no corresponding provenance path.
- `crates/tnk-modules/src/meta.rs:4784-4838` selects source versus flat ordinary declarations for
  reflection, but receives only root strategy vectors from the current flattener.

This is a module-construction and strategy-definition representation defect, not a kernel rewrite defect.
Do not special-case `resolve_call` to search the `ModuleDb`; the required information must survive module
flattening and transformation first.

### 0.2 Reference design facts

Maude does not import strategies as ordinary equations or rules:

- `SyntacticPreModule::process()` processes imports before local statements and calls
  `importStrategies()` as a distinct phase.
- `ImportModule::importStrategies()` recursively visits imported modules, uses a visitation phase to
  suppress diamonds, and asks each module to donate its strategies.
- `ImportModule::donateStrategies()` donates declarations and definitions through translation-aware
  insertion paths; it does not concatenate source vectors blindly.
- Strategy declaration identity is based on the strategy name and argument kinds. The declared subject
  sort is checked at declaration time but is ignored when deciding whether two declarations denote the
  same strategy.
- A named call may have several definitions. The call arguments are matched against each applicable
  definition lhs, and all successful definitions contribute continuations in deterministic order.

The Rust implementation need not copy the C++ classes or phase enum. It must preserve these observable
invariants.

---

## 1. Scope boundary

### 1.1 Required in this goal

1. **Named strategy-module imports.** `protecting`, `extending`, and `including` imports from an `smod`
   into an `smod`, including transitive imports and diamonds.
2. **Root and imported declarations.** Declaration-only strategies, declarations with one or more
   definitions, overloaded declarations, repeated declarations, and independently conflicting
   declarations.
3. **Root and imported definitions.** Zero-argument and parameterized unconditional `sd` definitions;
   constant and variable lhs arguments; all matching definitions; variables bound in the lhs and used in
   embedded term bubbles in the body.
4. **Definition order and deduplication.** Source-local order, import order, local-versus-imported order,
   same-origin diamond suppression, and independent-origin conflict behavior.
5. **Home semantics.** Imported definition lhs and body term bubbles parse against the defining module's
   grammar before they are re-pointed into the flattened executable module.
6. **Existing module expressions.** Summation, ordinary sort/operator/rule-label renaming, and existing
   functional-theory/module-view parameter instantiation must transform strategy declarations and
   definitions coherently.
7. **Reflection.** `upStratDecls`, `upSds`, and the strategy fields of `upModule` must agree with the live
   module at both `flat = false` and `flat = true`; renamed and instantiated modules must reflect their
   transformed forms.
8. **Module lifecycle.** Redefining an imported strategy module must invalidate/rebuild importers through
   the existing dependency mechanism; no stale strategy table may remain in a `Session`.
9. **Illegal cross-family import.** An ordinary `mod`/`fmod` importing an `smod` is rejected as Maude does:
   the complete import is ignored, not merely its strategy declarations, and later independent input in
   the same session still executes.
10. **Both strategy schedulers.** `srewrite` and `dsrewrite` consume the same compiled declaration and
    definition collection while preserving their existing breadth/depth scheduling difference.

### 1.2 Explicit non-goals

Do not expand this goal to adjacent strategy-language work:

- conditional strategy definitions (`csd`), including condition binding and backtracking;
- `xmatchrew` (TNK-006) or any new strategy combinator;
- strategy-specific module renamings such as `strat old to new` or strategy mappings in views;
- strategy theories as parameter theories, strategy-view bindings, or a new parameterization model;
- a full D10 compiled-module algebra rework or general import-as-reparse;
- warning/advisory wording, source coordinates, or byte-identical diagnostics;
- TNK-009's implicit-BOOL reflection mode difference;
- continuation/session concurrency (Phase I-C), cancellation, threads, or protocol changes;
- unrelated accepted count/schedule differences.

The in-scope renaming requirement means that **already supported** sort, operator, and rule-label mappings
must also rewrite strategy profiles and bodies. It does not add new surface syntax for renaming a strategy
name.

A newly discovered dependency that falls in this list is not silently implemented. Record the oracle
probe, explain why the dependency is unavoidable, and revise the goal boundary explicitly.

---

## 2. Binding behavioral contract

### 2.1 Import admissibility and visibility

- All three legal import modes donate the same strategy declaration/definition surface. Their existing
  semantic-mode annotation must not change strategy visibility.
- Visibility is transitive.
- A same-origin declaration or definition reached through two sides of a diamond is donated once.
- Importing the same named module twice is semantically one origin, not two definitions.
- Two independently declared strategies that happen to have the same profile are not a diamond and must
  not be string-deduplicated into one declaration.
- A declaration is visible even when it has no definition. Calling it produces `No solution.` with zero
  rewrites; it is not reported as an unknown strategy.
- An ordinary non-strategy module cannot acquire ordinary sorts/operators/rules by illegally importing an
  `smod`. Maude ignores the whole import after diagnosing it, then continues processing later input.

### 2.2 Declaration identity and overload resolution

Use a semantic declaration key, not a display string:

- key: strategy name plus the kinds of its explicit argument sorts;
- not part of the key: the subject sort following `@`;
- source sort names that belong to one kind therefore collide as Maude's declarations do;
- declarations whose argument profiles belong to distinct kinds are valid overloads;
- a call's explicit argument terms select the applicable profile; the current subject term does not
  select between declarations that differ only in the ignored subject slot.

Preserve source declarations separately from the compiled key table. Reflection must be able to report
actual declarations rather than reconstructing lossy strings from the executable map.

### 2.3 Definition selection and matching

For every source form accepted in this goal:

1. Resolve the call name and explicit argument terms against declarations.
2. Parse/build each definition lhs in its home grammar and compile it against the flattened engine.
3. Try applicable definitions in the ordering contract of §2.4.
4. Match call arguments as terms, with one shared substitution across all arguments. Repeated variables
   must agree; constants and constructors must match structurally/modulo their declared theories using
   the existing matcher semantics.
5. Substitute lhs bindings into every term-bearing bubble in the selected body before resolving/executing
   it. This includes `match`/`amatch`/`xmatch`, rule-application substitutions, and nested strategy-call
   arguments.
6. Schedule every matching definition. An unmatched definition contributes no process and does not mask a
   later match.
7. Preserve the search scheduler's process order and cumulative rewrite snapshots. Do not collect all
   completed terms and sort them afterward.

An unconditional `sd` with no explicit arguments is a zero-argument pattern and remains lazy: recursive
strategy definitions must not be expanded eagerly at module-build time.

`csd` remains rejected by the existing explicit error. The representation may reserve a condition field,
but no condition may be dropped and executed as if it were unconditional.

### 2.4 Ordering and duplicate contract

The following live-oracle observations are frozen as acceptance behavior:

| Case | Required result sequence and cumulative counts |
|---|---|
| one imported `go := rb` | `b / 1`; final `1` |
| one declaration `empty` with no definition | no solution; final `0` |
| local `go := rb ; go := rc` | `b / 2`, `c / 2`; final `2` |
| importer adds `go := rd` before imported `go := rb` | `d / 2`, `b / 2`; final `2` |
| diamond: base `rb`, left adds `rc`, right adds `rd` | `b / 2`, `c / 3`, `d / 3`; final `3` |
| same diamond with right/left import order reversed | `b / 2`, `d / 3`, `c / 3`; final `3` |
| root adds `re` above the first diamond | `e / 2`, `b / 3`, `c / 4`, `d / 4`; final `4` |
| two direct imports of the same declaration origin | one `b / 1`; final `1` |
| two independent modules declaring the same zero-argument strategy profile | no solution; final `0` |

`value / n` means the value printed for that solution and its `rewrites: n` snapshot. These counts are not
incidental: they expose when definition alternatives are decomposed. A solution-set-only implementation is
insufficient.

Within one module expression, declaration and definition order are separate concerns. Do not infer one by
zipping the other, and do not rely on `HashMap` iteration order. Reflection may canonicalize a set according
to the reference meta-level constructor; execution must retain the reference donation/scheduling order.

### 2.5 Definition-dispatch prerequisite

Imported definitions cannot be made correct while root definitions still collapse to one body per bare
name. The goal therefore closes these already-accepted local cases at the same seam:

- `pick : S @ S` and `pick : T @ T` dispatch independently when `S` and `T` are in different kinds;
- declarations with argument sorts in one kind exhibit Maude's conflict behavior without panicking;
- two zero-argument declarations differing only in subject sort remain the same declaration identity, but
  the applicable definitions can still match/execute as Maude does;
- `choose(a)`, `choose(b)`, and `choose(c)` select constant-pattern definitions (`c`, `d`, and no solution
  in the frozen probe);
- `echo(X) := match X` binds the call argument into the body (`echo(a)` succeeds on `a`, `echo(b)` on `b`).

This prerequisite is bounded to `sd`; it is not a general strategy-language redesign.

### 2.6 Home grammar and executable identity

A plain named import must preserve the defining module as the parsing home for each imported definition.
The decisive collision fixture is:

- donor defines `h : S -> S`, `home(X) := match h(X)`;
- importer defines its own incompatible `h : -> S`;
- `home(b)` on `h(b)` succeeds because the body is parsed in the donor, not in the importer.

After parsing, all sorts, symbols, variables, labels, and term patterns must be re-pointed to the flattened
module's `BuiltModule`; no `DagId`, `SymbolId`, or `SortId` from another `Engine` may escape its owner.

Follow D10's existing distinction:

- plain named imports retain home provenance;
- renamed, instantiated, and summed donations are transformed as source data and compiled against the
  resulting flat grammar, rather than pretending the original untransformed grammar is still their home.

Do not build and retain a second engine merely to execute an imported strategy body.

### 2.7 Module-expression transforms

The strategy payload must travel with the ordinary declaration payload through each existing transform:

- **sum:** both operands' strategy declarations/definitions survive, while a shared transitive origin is
  donated once;
- **sort renaming:** argument and subject sort names in `strat`, variable sort annotations in definition
  lhs/body bubbles, and reflected forms change coherently;
- **operator renaming:** term-bearing lhs/body bubbles change at parse-identified operator positions, not by
  blind text replacement;
- **rule-label renaming:** `apply`/bare rule applications in bodies target the renamed label;
- **functional parameter instantiation:** parameter sorts/operators appearing in profiles and bodies are
  substituted into the instance, and reflected declarations/definitions name the instantiated sorts and
  operators.

The transform must recurse through the full existing `StratExpr` tree. Updating only a top-level `match`
or `apply` node is a latent wrong-value bug.

### 2.8 Reflection

For a strategy module with local and imported declarations/definitions:

- `upStratDecls(name, false)` and `upSds(name, false)` report only the named source module's own payload;
- `upStratDecls(name, true)` and `upSds(name, true)` report the effective flattened payload;
- the corresponding fields of `upModule(name, false)` and `upModule(name, true)` agree with those choices;
- `flat = false` retains the source import expression rather than inlining the imported payload;
- `flat = true` reports each same-origin diamond declaration/definition once;
- renamed and instantiated module expressions report transformed profiles and bodies;
- execution and reflection consume one authoritative strategy collection. A strategy cannot execute while
  being absent from flat reflection, or reflect while being unavailable to execution.

TNK-009's known implicit-BOOL import-mode difference remains allowed. Tests for this goal must project or
otherwise isolate the strategy fields rather than declaring all unrelated `upModule` output fixed.

### 2.9 Redefinition and session continuity

If `BASE` is redefined from `sd go := rb` to `sd go := rc`, a previously named importer must produce `b`
before redefinition and `c` after redefinition. Use the existing module dependency invalidation/rebuild
path; do not add a strategy-only cache invalidator.

Every rejection/conflict fixture ends with an independent sentinel command. Panics, process exits, poisoned
session state, or stale current-module state fail the goal even if the expected earlier command was
rejected.

---

## 3. Architecture constraints

The concrete Rust type names may change. These invariants may not.

### 3.1 Preserve source data, origin, and compiled data separately

The design needs three concepts:

1. **source declaration/definition** — sufficient for `show`/reflection and later transformations;
2. **origin/provenance** — stable across a named-import graph, so diamonds deduplicate by origin rather
   than text;
3. **compiled executable entry** — resolved declaration key, built lhs pattern, variable layout, and body
   representation owned by the destination `BuiltModule`.

A source-position key, module-expression origin key, or equivalent stable identity is acceptable. A
`HashSet<String>` of printed declarations is not: distinct modules may contain identical text, and one
module may be reached through several paths.

### 3.2 Collection and build rules

- Extend the existing `FlatDecls`/module-expression collection path; do not bolt a second recursive DB walk
  onto command evaluation.
- The flattener's visitation/dedup transaction covers one module-expression build. It must not leak state
  between independent builds.
- Root-local strategies and imported strategies remain distinguishable after flattening.
- Compile declarations only after the destination signature has closed its sorts/operators, so kind-based
  keys and term parsing use final identities.
- Replace the one-body `HashMap<String, Rc<RStrat>>` with an ordered overload/definition representation.
  Bare-name lookup may be an index into that representation, but it cannot be the semantic key.
- Preserve lazy recursion. Compiled bodies may contain named call nodes; module construction must not
  recursively inline zero-argument definitions.
- Invalid or conditional definitions remain explicit errors/disabled entries. Never silently omit an
  entry and thereby expose a lower-priority unrelated definition.

### 3.3 Home and transform rules

- Reuse the existing home-grammar architecture in `load.rs`; add the strategy analogue rather than a
  parallel ad-hoc parser.
- Reuse existing sort/operator/rule-label renaming machinery and token-position discipline. Do not global
  string-replace raw bubbles.
- Reuse existing term matcher/extension semantics for definition lhs matching. Do not introduce a
  free-theory-only matcher in `strategy.rs`.
- Reuse existing module dependency invalidation. Do not give strategies a second lifecycle.

### 3.4 Isolation rules

- No semantic change belongs in `tnk-core` unless a genuinely missing public matcher operation is needed;
  if so, expose the smallest engine-owned API and prove it independently.
- Do not change ordinary equation/rule flattening, `rewrite`/`frewrite`, strategy combinator scheduling, or
  the `Session`/local-meta protocol except where a strategy metadata type must be threaded through.
- Keep output rendering in `tnk-session`/`tnk-repl`; strategy collection and resolution stay below terminal
  policy.
- No new global mutable state, process singleton, or cross-engine handle.

---

## 4. Source touchpoint map

Read these sections before editing. Line numbers are baseline anchors, not permanent API promises.

| Area | Current source | Required responsibility |
|---|---|---|
| source AST | `crates/tnk-frontend/src/surface/ast.rs:302-388` | retain complete `StratDecl`/`StratDef`/`StratExpr` data through transforms |
| source parsing | `crates/tnk-frontend/src/surface/parser.rs:1498-1558` | keep `smod` gating and accepted `sd` forms; no new `csd` semantics |
| module flattening | `crates/tnk-modules/src/flatten.rs:24-50, 159-260` | collect root/imported strategy payload, origins, ordering, and diamond dedup |
| module transforms | `crates/tnk-modules/src/flatten.rs:480-650, 780-1635`; `rename.rs` | sum, rename, and instantiate the complete strategy payload |
| signature/build data | `crates/tnk-frontend/src/sig/syntax.rs:108-183`; `build_sig.rs` | represent compiled declaration keys and ordered definitions in `BuiltModule` |
| homed load | `crates/tnk-frontend/src/load.rs:101-190, 291-320` | parse strategy lhs/body bubbles with donor provenance and destination identities |
| strategy resolution | `crates/tnk-frontend/src/strategy.rs:184-235, 500-690, 1240-1260` | overload resolution, lhs matching, binding substitution, ordered scheduling |
| reflection | `crates/tnk-modules/src/meta.rs:4784-4960` | source/flat strategy projections and transformed meta representation |
| meta execution | `crates/tnk-modules/src/meta.rs:940-980`; `tnk-session/src/interpreter.rs` | consume the authoritative compiled collection without a stale override |
| module lifecycle | `crates/tnk-modules/src/db.rs`; `load.rs` | preserve existing dependency invalidation across strategy payload changes |
| behavior tests | `conformance/audit/`; `crates/tnk-repl/src/tests.rs`; crate-local tests | pin public values/order/counts first, internals only where behavior cannot isolate an invariant |

Reference anchors:

- `~/code/maude-lang/maude/src/Mixfix/process.cc:455-510` — local strategy declarations and import phase;
- `~/code/maude-lang/maude/src/Mixfix/importModule.cc:499-678, 809-930` — recursive donation,
  translation, and visitation;
- `~/code/maude-lang/maude/src/Mixfix/strategyDefinition.cc` and `strategyDefinition.hh` — definition
  matching/execution representation;
- `~/code/maude-lang/maude/src/Mixfix/global.cc` and `renaming.cc` — summation and strategy-aware
  transformations;
- `~/Downloads/Maude-3/book/reference/manual_pdf_text.txt:12230-12510` — Chapter 10 strategy syntax and
  semantics.

---

## 5. Frozen conformance manifest

### 5.1 Authoring rule

Before implementation, create the six fixtures below from live Maude output. Each fixture must:

- contain the smallest modules needed for its matrix;
- state its oracle claim in comments and use the correct `*** PRELUDE` marker for the harness;
- end rejection/conflict sections with a valid sentinel command;
- pass `tools/diffmaude.sh` against the reference only after its expected output has been inspected;
- fail on the frozen tnk baseline for the intended reason;
- use no custom output normalizer and no accepted-diff exemption.

The audit denominator is `78` at the frozen baseline; this manifest intentionally grows it to `84`.
If a matrix must be split further for determinism, grow the denominator and record why—never merge away a
behavioral assertion to preserve the number.

### 5.2 Required fixtures

#### `conformance/audit/A3f-strategy-import-basic.maude`

- direct `protecting`, `extending`, and `including` imports: one `b / 1` result each;
- a two-hop transitive import: one `b / 1` result;
- imported declaration `empty` without `sd`: no solution, final count `0`;
- illegal `mod` importing `smod`: imported `a` is unavailable, whole import ignored, later sentinel rewrites;
- run both `srewrite` and `dsrewrite` on at least one imported call.

#### `conformance/audit/A3g-strategy-import-order.maude`

Pin §2.4 exactly:

- two local definitions (`b / 2`, `c / 2`);
- a root-local definition before an imported definition (`d / 2`, `b / 2`);
- diamond, reversed sibling order, and root-local-plus-diamond sequences/counts;
- repeated import of one origin and a two-sided diamond donate the base once;
- two independent same-profile imports produce no solution and do not kill the sentinel.

#### `conformance/audit/A3h-strategy-definition-dispatch.maude`

- distinct-kind overloads dispatch `a -> b` and `x -> y`;
- same-kind declaration conflict follows the oracle for both source sorts without panicking;
- two declarations differing only in subject sort follow the oracle for both subjects;
- `choose(a) -> c`, `choose(b) -> d`, `choose(c)` has no solution;
- `echo(X) := match X` succeeds for at least two constants, proving lhs-to-body substitution;
- an unmatched earlier definition does not mask a matching later definition.

#### `conformance/audit/A3i-strategy-import-home.maude`

- donor `h : S -> S`, importer incompatible `h : -> S`;
- imported `home(X) := match h(X)` succeeds on `h(b)` with zero rewrites;
- a nested call or application body also uses donor-resolved term/label identity;
- a failed home parse is a recoverable command/module error followed by a sentinel, never a panic.

#### `conformance/audit/A3j-strategy-import-transform.maude`

- sum of two modules yields both strategies in oracle order and suppresses a shared origin;
- sort renaming transforms declaration profile and body annotations;
- operator renaming transforms embedded term patterns;
- rule-label renaming transforms applications;
- functional-theory/module-view instantiation transforms a strategy profile/body and executes it;
- redefining a donor changes a previously declared importer from `b / 1` to `c / 1`.

Strategy-specific renaming syntax and strategy-view mappings do not belong in this fixture.

#### `conformance/audit/A5g-strategy-import-reflection.maude`

- a root with both local and imported strategies probes `upStratDecls` and `upSds` at `false` and `true`;
- flat output contains each diamond origin once;
- non-flat output contains only root-local strategies plus the source import expression;
- summed, ordinarily renamed, and functionally instantiated forms reflect transformed payloads;
- project the strategy fields of `upModule` so TNK-009's unrelated BOOL import-mode difference does not
  contaminate the claim.

### 5.3 Required focused Rust tests

Add focused tests only for invariants that the public fixtures cannot diagnose precisely:

1. origin-key diamond dedup does not merge identical text from independent modules;
2. declaration profiles use argument and subject kinds, not exact sort identities;
3. one call retains all ordered candidate definitions and shared lhs bindings;
4. home-built terms contain only destination-engine symbol/sort identities;
5. each existing transform recursively updates strategy payloads;
6. source-versus-flat reflection selects the intended collection;
7. module redefinition invalidates a cached importer.

Tests must assert behavior/data invariants, not source-code text or private field names.

---

## 6. Implementation work graph

The edges are dependencies, not permission to skip later nodes:

```text
G0 oracle fixtures and frozen outputs
  -> G1 strategy source/origin collection in module expressions
       -> G2 compiled declaration keys + ordered definition dispatcher
       -> G3 home-grammar build/re-pointing
       -> G4 sum/rename/instantiation transforms
G2 + G3 + G4
  -> G5 reflection, meta execution, and lifecycle integration
       -> G6 complete gates, docs, and closure ledger
```

**Implemented cut:** all G0–G6 edges are closed. `FlatModule` owns strategy payload/provenance and
origin-based donation; `StrategyProgram` owns kind profiles and ordered compiled definitions; imported
home grammars are action-remapped to destination identities; existing sum/rename/instantiation passes
transform strategy payloads recursively; reflection and Session consume the same source/flat split.
Recursive calls remain runtime-lazy and conditional `csd` remains outside this goal.

### G0 — Freeze behavior before repair

1. Add all six fixtures and inspect their Maude output.
2. Run each through the tnk baseline and classify the intended failure.
3. Preserve exact values, sorts, solution order, per-solution counts, final counts, and session survival.
4. If the live oracle differs from §2/§5, update this contract before proceeding.

### G1 — Carry compositional strategy source data

1. Introduce a strategy payload in the same module-expression accumulator as ordinary declarations.
2. Attach stable origin and plain-import home provenance.
3. Donate transitive imports in deterministic source/import order.
4. Suppress only repeated paths to the same origin; retain independent identical text.
5. Enforce strategy-module import admissibility before donating any ordinary or strategy payload.

Exit: flatten-level tests prove direct/transitive/diamond/conflict collection without executing a strategy.

### G2 — Compile declarations and definitions without collapsing them

1. Resolve declaration profiles to argument-kind keys after signature closure.
2. Preserve declaration-only entries and overload conflicts.
3. Build an ordered candidate list/multimap for every strategy identity.
4. Compile definition lhs patterns and variable layouts.
5. Replace bare-name/one-body call execution with profile selection, lhs matching, substitution, and
   scheduling of all matches.
6. Keep recursive calls lazy and keep `csd` disabled.

Exit: the local-dispatch fixture passes before relying on imports.

### G3 — Preserve home semantics

1. Extend the homed loader to strategy lhs/body term bubbles.
2. Parse against donor grammar, then map all semantic identities to the destination `BuiltModule`.
3. Reject any unmapppable donor identity deterministically; never retain a cross-engine handle.
4. Prove the importer-local `h` collision and nested-body case.

Exit: `A3i` passes with zero-rewrite identity cases and a live sentinel.

### G4 — Transform the full strategy payload

1. Thread payloads through summation and parameter-copy/instantiation collection.
2. Apply ordinary sort/operator/rule-label mappings recursively to declarations, lhs bubbles, conditions
   retained as data, and every body expression.
3. Preserve/recompute provenance consistently: same named origin dedups; transformed donations remain
   distinct when Maude treats them as distinct.
4. Compile transformed payloads only in the resulting grammar.

Exit: `A3j` passes without adding strategy-specific renaming syntax.

### G5 — Integrate reflection and lifecycle

1. Make `upStratDecls`, `upSds`, and `upModule` select source versus flat payload consistently.
2. Remove or adapt any meta-interpreter `strat_defs` override that would bypass the authoritative compiled
   collection.
3. Thread representation changes through `tnk-session` without changing its protocol.
4. Verify normal module redefinition invalidates/rebuilds strategy importers.
5. Re-run existing root strategy, meta-strategy, Russian-dolls, and session fixtures for regressions.

Exit: `A5g`, redefinition, local meta-interpreter, and existing strategy suites pass.

### G6 — Close the goal

1. Run §8 in order on a release binary built from the final source.
2. Mark TNK-005 resolved in `docs/bug-triage.md` with commit and retained fixture names.
3. Update `docs/documentation-survey.md`, `fable-audit.md`, and status/index prose that explicitly describes
   imported strategies as missing. Do not rewrite unrelated planning history.
4. Fill §9 with observed counts/hashes; leave no scratch probe in the repository root.
5. Commit the completed goal as coherent, reviewable changes.

---

## 7. Decision defaults and escalation rules

Use these defaults unless a live oracle falsifies them:

- **Collection:** module-expression flattening owns import traversal; command execution consumes built data.
- **Dedup:** semantic origin, not text and not bare strategy name.
- **Identity:** name plus explicit argument kinds plus subject kind; exact subject-sort identity is ignored.
- **Definitions:** ordered list of candidates; all matching candidates schedule.
- **Home:** plain imports preserve donor parsing provenance; transformed expressions compile in the flat
  result grammar.
- **Reflection:** source data is retained; executable structures are not reverse-pretty-printed.
- **Lifecycle:** ordinary module dependency invalidation owns cache freshness.
- **Diagnostics:** preserve recovery/continuation; exact warning prose is deferred.
- **Scope:** point-fix the existing module algebra; do not reopen full D10.

Stop and document before coding past the boundary if any of these occurs:

1. Maude's live behavior for an ordering/conflict case differs from the frozen matrix.
2. Home-correct compilation appears to require retaining foreign-engine IDs or building a second live
   engine.
3. A required transform cannot be expressed without adding strategy-specific renaming/view syntax.
4. The fix changes ordinary equation/rule donation or existing strategy-combinator scheduling.
5. A fixture exposes an unrelated accepted deviation; isolate it rather than weakening this gate.

No completion path may add an accepted diff, custom normalization, ignored fixture, expected failure, or
feature flag that is absent from the normal release binary.

---

## 8. Completion gate

Run from a clean worktree, in this order. A failure is work, not an exception to the goal.

### 8.1 Focused build and smoke

```sh
cargo fmt --all -- --check
cargo test --release -p tnk-frontend strategy
cargo test --release -p tnk-modules
cargo test --release -p tnk-session
cargo test --release -p tnk-repl strategy
cargo build --release -p tnk-repl --features smt-z3
```

Then run `tools/diffmaude.sh` on each of the six new fixtures individually and inspect the normalized output.
The primary two-module repro must print exactly one `S: b` solution with one rewrite under the final
`target/release/tnk-repl`.

### 8.2 Full Rust and differential gates

```sh
cargo test --release --workspace --features smt-z3
tools/audit-scoreboard.sh
tools/legacy-sweep.sh
tools/subsystems-scoreboard.sh
```

Required outcomes:

- all 453 Rust tests pass across 12 suites;
- audit score is `84/84 PASS`, including the six new fixtures;
- legacy sweep remains `87/87 CLEAN`;
- subsystem score is `112/112 PASS` at the default 60-second gate;
- no accepted-diff entry is added or widened.

### 8.3 Regression surfaces that must be named in the closeout

Confirm and report all of these, not merely the aggregate score:

- existing root strategy fixtures (`srewrite`, `dsrewrite`, recursion, parameterized calls, `matchrew`);
- imported ordinary rules/equations and module-expression fixtures;
- `upModule`, `upStratDecls`, `upSds`, `metaSrewrite`, and meta-strategy fixtures;
- the Phase I-S live-oracle/local-interpreter suite;
- stock `model-checker.maude`, `smt.maude`, and `metaInterpreter.maude` load/use gates;
- invalid/conflicting module fixtures continue to later sentinel commands;
- no new panic, timeout, wrong count, nondeterministic order, or cross-engine handle appears.

### 8.4 Documentation and repository closure

- TNK-005 is marked resolved only after the gates pass.
- This document's ledger is completed with actual commands, counts, and commit(s).
- Explicit stale claims in the survey/audit/index are updated; unrelated deferred work stays deferred.
- No `/tmp` probe, debug print, ignored fixture, generated output, or untracked scratch file remains.
- The final worktree is clean after the goal commit.

---

## 9. Completion ledger

Observed on 2026-07-26 against the live Maude 3.5.1 oracle and the final release binary.

### Behavior

- [x] Six oracle fixtures added and individually inspected.
- [x] Direct/transitive/all-mode imports execute.
- [x] Declaration-only, overload, conflict, and multi-definition behavior matches Maude.
- [x] Diamond dedup and definition order/count matrix matches §2.4.
- [x] Definition lhs matching and lhs-to-body binding work.
- [x] Plain-import home grammar collision passes.
- [x] Sum, ordinary renaming, and functional instantiation transform strategies.
- [x] Source/flat reflection and `upModule` strategy fields agree.
- [x] Redefinition invalidates an existing importer.
- [x] Illegal cross-family import ignores the whole import and preserves session continuity.

### Regression gates

- [x] `cargo fmt --all -- --check`
- [x] Seven focused representation tests pass.
- [x] Full release workspace tests with `smt-z3`: **453/453**, 12 suites.
- [x] Audit scoreboard: **84/84 PASS**.
- [x] Legacy sweep: **87/87 CLEAN**.
- [x] Subsystem scoreboard at the default 60-second gate: **112/112 PASS**.
- [x] Root strategy, ordinary module algebra, source/flat META reflection, Phase I-S local interpreters, and stock model-checker/SMT/meta-interpreter surfaces remain green through the focused, audit, legacy, and subsystem gates.
- [x] The primary repro returns exactly one `S: b` solution with one rewrite; a recursive parameterized-call smoke probe also matches the oracle.

### Closeout

- [x] TNK-005 triage entry resolved with retained `A3f`–`A3j` and `A5g` fixtures.
- [x] Survey, audit, crate status comment, migration index, and roadmap status prose updated after behavior passed.
- [ ] Implementation/final-gate commit: `________________`
- [ ] Documentation-ledger commit: `________________`
- [ ] Scratch artifacts removed and clean worktree confirmed.
