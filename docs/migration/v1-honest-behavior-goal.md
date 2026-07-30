# V1 honest-behavior goal — the `/goal` contract

**Status:** completed 2026-07-29.
**Oracle:** Maude 3.5.1 where the behavior is part of Maude's contract; project-defined diagnostics where tnk reports an intentionally unsupported feature.
**Starting baseline (2026-07-29):** optional-Z3 subsystem scoreboard 113/113 PASS, audit scoreboard 98/98 PASS, workspace tests 474 passed and 1 ignored, legacy sweep 87/87 CLEAN.
**Purpose:** make tnk honest and actionable at its supported boundary without implementing the deferred features themselves.

## Goal statement

Eliminate the misleading timing values and silent semantic degradation that would make a tambanokano v1 feel unreliable.

After this goal:

1. No command prints fabricated CPU time, elapsed time, or rewrite rates.
2. Recognized-but-inactive `[memo]` behavior and memo controls are reported clearly.
3. Unsupported `xmatchrew` and conditional strategy definitions fail with stable, user-facing errors rather than implementation-internal wording.
4. A statement dropped during module construction emits an actionable warning instead of disappearing silently.
5. Fatal parse, module, and view failures identify the affected entity and preserve enough cause information for a user to correct the input.
6. Advanced META operations that intentionally remain inert are accurately documented from direct probes.
7. Values, sorts, solution sets, ordering, rewrite counts, module state, and continuation behavior remain unchanged outside the new diagnostics and removal of false timing text.

This is a release-hardening goal. It is not full GAP-002, GAP-003, or GAP-005–009 completion.

## 0. Authority and change discipline

When evidence disagrees, use this order:

1. a direct Maude 3.5.1 versus tnk probe;
2. the current implementation and retained conformance fixtures;
3. this contract;
4. older roadmap, audit, and triage prose.

Never choose behavior from memory. Preserve a contradicting probe and amend this contract before changing semantics.

A semantic defect found during this work must not be hidden behind a warning or broader output normalization. Reproduce it, enter it in the active register, and fix it separately or explicitly expand this goal.

## 1. Binding policy decisions

### 1.1 Timing is suppressed, not implemented

Real timing measurement is outside this goal.

- Remove every fixed `0ms cpu`, `0ms real`, `Decision time: 0ms`, and `~ rewrites/second` value from observable output.
- Commands continue to print exact rewrite and state counts.
- `set show timing off .` remains accepted and silent.
- `set show timing on .` emits exactly one clear warning and leaves timing output disabled.
- No command may print a time or rate unless it was actually measured. Because measurement is out of scope here, no command prints one after this goal.
- Preserve existing blank-line structure except where removing a timing-only line makes a blank line redundant.

Recommended warning:

```text
warning: real timing is not implemented; timing output remains disabled.
```

GAP-003 remains open as “real timing not implemented; misleading timing suppressed.”

### 1.2 Diagnostic meanings

Use these behavioral distinctions:

- `error`: the requested module, view, command, or strategy execution was rejected;
- `warning`: input was accepted but a declaration, statement, or feature was ignored, dropped, or executed with reduced capability;
- advisories and byte-identical Maude warning-text parity remain out of scope.

Nonfatal diagnostics must travel as owned data from parser, build, and module code to `Session`. Frontend and kernel code must not print directly. Rendering order must be deterministic and follow source order.

When available without inventing information, a diagnostic carries:

- severity;
- module or view name;
- source line from existing `Token::line` data;
- statement or declaration kind;
- concise cause.

Do not fabricate a line number when the failing layer no longer has one.

## 2. Required behavior

### 2.1 Honest count rendering

Replace every timing-bearing output form with a count-only form.

Examples:

```text
rewrites: 12
```

```text
states: 5  rewrites: 7
```

This applies to every renderer and continuation path, including:

- `reduce`;
- `rewrite`, `frewrite`, and `erewrite`;
- rewrite `continue`;
- `search`, `smt-search`, and their continuations;
- `match` and `xmatch`;
- `srewrite` and `dsrewrite`;
- unification;
- variants and variant matching/unification;
- narrowing and narrowing continuations;
- model-checking and SAT paths reached through ordinary command rendering;
- zero-result, bounded-result, and exhausted paths.

Acceptance criteria:

1. Rewrite and state counts remain exactly the values produced before this goal.
2. `set show breakdown on` remains composable with count-only rendering.
3. No production formatter contains or emits a placeholder timing or rate value.
4. Existing tests that assert `0ms` output are rewritten to assert the count and semantic result; they are not deleted or weakened.
5. The differential harness gains no broad normalization capable of hiding value, sort, count, ordering, or state differences.
6. `set show timing on .` warns once per command and does not enable timing.
7. `set show timing off .` is silent before and after an attempted enable.

### 2.2 Explicit unsupported memo behavior

Surface syntax must retain enough information to know that an operator declaration used `[memo]`. The parser must no longer consume the attribute without recording that fact. Do not wire it into kernel memoization.

For a source operator declaration using `[memo]`:

- accept and build the declaration as today;
- emit one warning per source operator declaration;
- include module name, source line, and operator name;
- state that evaluation continues without memoization;
- do not repeat the warning merely because the declaration is imported, reached through a diamond, renamed, instantiated, or rebuilt as part of a dependent module.

Recommended message shape:

```text
warning: module `M`, line N: `[memo]` on operator `f` is not implemented; evaluation continues without memoization.
```

Exact wrapping may follow the existing output renderer, but a focused test pins the complete chosen message.

These explicit controls must not remain silent:

- `set clear memo on .`;
- `set clear memo off .`;
- `do clear memo .`;
- `do clear memo M .`.

Each emits one clear warning that memoization is unavailable and the command has no effect. None alters module or Session state.

Acceptance criteria:

1. Normal-form values and sorts remain unchanged.
2. Repeated reductions keep current uncached rewrite counts; no memo hit is fabricated.
3. Source modules entered directly or loaded from files produce the warning.
4. A declaration donated through an import, diamond, renaming, or instantiation does not create a warning storm.
5. A valid command after each memo warning executes normally.
6. Reflected META modules carrying a `memo` attribute may remain inert in this goal, but that boundary is documented.
7. Memo tables, cache hits, clear semantics, trace events, and Maude-compatible memo rewrite counts remain non-goals.

### 2.3 Clear strategy feature errors

`xmatchrew` and conditional strategy definitions remain unimplemented. Their failures must be deliberate and user-facing.

For `xmatchrew`:

- emit exactly one `error:` line;
- name `xmatchrew`;
- state that it is recognized but not implemented;
- expose no phrase such as “engine follow-on,” Rust type name, source path, or implementation plan;
- emit no `Solution`, `No solution`, or partial strategy result;
- leave the Session usable by a subsequent valid command.

For a call whose selected definition is a `csd`:

- emit exactly one `error:` line;
- identify conditional strategy definitions or `csd`;
- state that the feature is recognized but not implemented;
- do not partially execute the strategy body;
- preserve ordinary `sd` overload selection and behavior;
- leave the Session usable.

Recommended minimum messages:

```text
error: `xmatchrew` is recognized but not implemented.
```

```text
error: conditional strategy definitions (`csd`) are recognized but not implemented.
```

More context is permitted only when stable and useful. The message must not imply malformed user syntax.

Acceptance criteria:

1. Cover `xmatchrew` under both `srewrite` and `dsrewrite`.
2. Cover a direct `csd` and an imported `csd`.
3. Run one valid ordinary strategy command after each failure.
4. Preserve parser state, current module, definitions, and continuations.

### 2.4 Actionable statement-drop diagnostics

`load_statements_homed` and equivalent module-building paths must not discard the `Err` explaining why a statement was dropped.

When an equation, membership, or rule is rejected while the containing module remains usable:

- emit one warning;
- identify the defining or home module;
- identify `equation`, `membership`, or `rule`;
- include the first available source line;
- include the actual parse/build rejection reason;
- register no partial statement state;
- continue building the remainder of the module;
- prove that a following valid statement and command still execute.

Recommended message shape:

```text
warning: module `M`, line N: dropped equation: REASON
```

Acceptance criteria:

1. A diamond import produces no duplicate warning within one build.
2. A statement produces at most one identical warning in one build.
3. Dense trace and statement identifiers remain unchanged for retained statements.
4. Maude-compatible warn-and-drop recovery remains intact.
5. Warning wording need not yet be byte-identical to Maude; semantic recovery remains oracle-compatible.
6. Retain focused cases for:
   - a rewrite-condition fragment that is invalid in an equation;
   - an unbound RHS or condition variable;
   - an ill-sorted or unparseable statement followed by a valid statement.

### 2.5 Actionable fatal errors and recovery

For a top-level parse failure, module build failure, or view validation failure:

- emit an `error` or `parse error`;
- name the module or view when known;
- include a nonempty cause;
- include a source line when an existing token provides it;
- never panic;
- never publish a half-built replacement;
- leave the previous valid Session state usable.

Retained scenarios:

1. malformed module input followed by a valid module in a later submission;
2. a module that fails flatten/build followed by a command in the previous valid module;
3. an invalid view followed by a valid view or reduction;
4. a dropped statement inside an otherwise valid module.

Do not redesign the parser around byte spans. Existing token line data is sufficient for this goal.

### 2.6 Accurate compatibility documentation for inert META surfaces

Update the existing project orientation/status documentation with one concise, user-readable “recognized but unsupported/inert” table.

At minimum document:

- `metaParseStrategy`;
- `metaPrettyPrintStrategy`;
- nonempty conditions for `metaMatch`;
- conditional-rule forms of `metaApply`;
- corresponding `metaXmatch` and `metaXapply` boundaries established by direct probes;
- reflected `memo` attributes;
- the nearest supported alternative for each item.

Before documenting a boundary, run a direct Maude 3.5.1 versus tnk probe. Do not repeat a stale claim when the implementation already handles a case. Distinguish:

- a genuinely inert operation;
- a supported proper-residue case;
- the separately accepted DIV-001 AC solution-order difference.

Do not inject runtime warnings into META reductions merely to satisfy this documentation requirement; that would alter reflective semantics and rewrite counts. Documentation plus retained probes is the required treatment.

Update `docs/bug-triage.md` to describe current behavior without adding a resolution narrative:

- keep GAP-002 open for full diagnostics parity;
- keep GAP-003 open for real timing, noting that fabricated timing is suppressed;
- keep GAP-005–009 open except for a boundary genuinely completed with retained evidence;
- do not claim that memoization, `xmatchrew`, `csd`, or conditioned META operations were implemented.

## 3. Implementation invariants

1. No new kernel feature is introduced.
2. No value, sort, binding, solution, state, path, or rewrite-count contract changes.
3. Diagnostics are not emitted from `tnk-core`.
4. Parser and build code return nonfatal diagnostics as data; `Session` owns user-facing rendering.
5. Diagnostics are deterministic and source ordered.
6. Importing or instantiating a declaration does not create warning storms.
7. Unsupported-feature errors cannot poison the current module, continuation registry, or child interpreter registry.
8. Existing `set show advisories off .` inputs continue to parse and remain harmless.
9. No warning conceals an assertion, panic, partial commit, or incorrect result.
10. No output normalization is broadened to hide a semantic difference.

## 4. Explicit non-goals

Do not implement any of the following in this goal:

- real CPU/wall timing or rewrite-rate measurement;
- memo tables, memo hits, clear behavior, or auto-clear behavior;
- `xmatchrew` execution;
- conditional strategy execution;
- `metaParseStrategy` or `metaPrettyPrintStrategy`;
- conditioned `metaMatch` or `metaApply`;
- full warning/advisory parity;
- preregularity, ambiguity, collapse-at-top, import-hygiene, or every other GAP-002 warning;
- ordinary search tracing;
- cancellation or thread-backed I-C work;
- Full Maude, LOOP-MODE, external managers, debugger, or profiler work;
- new normalization for semantic differences.

## 5. Retained evidence

### 5.1 Timing matrix

Exercise at least one command from every distinct renderer in §2.1 and prove:

- rewrite/state counts remain present;
- no `cpu`, `real`, `Decision time`, or `rewrites/second` text appears;
- timing-off is silent;
- timing-on emits the chosen warning once and does not enable timing;
- continuation output uses the same count-only format.

### 5.2 Memo matrix

Prove:

- `[memo]` emits the chosen warning;
- repeated reduction returns the same value and sort with current uncached behavior;
- imports and diamonds do not duplicate the declaration warning;
- `set clear memo` and `do clear memo` warn and change no behavior;
- a valid following command succeeds.

Record the direct Maude memo behavior, but do not claim count parity. The evidence distinguishes value parity from intentionally unavailable caching.

### 5.3 Strategy matrix

Prove clear errors and recovery for:

- `xmatchrew` under `srewrite`;
- `xmatchrew` under `dsrewrite`;
- direct `csd`;
- imported `csd`;
- a valid ordinary strategy command after each failure.

### 5.4 Statement and module diagnostic matrix

Pin complete selected diagnostic text and subsequent recovery for every §2.4 and §2.5 scenario.

### 5.5 META limitations matrix

Retain the direct probes used to establish the documented inert/supported boundary. Compare values and rewrite counts against Maude where supported. Inert cases prove that tnk leaves the operation unreduced rather than partially computing a wrong result.

## 6. Verification gates

All gates must hold on the same final tree:

1. Focused new diagnostic, timing, memo, strategy, recovery, and META-boundary tests pass.
2. `cargo fmt --all --check` passes.
3. The release workspace test suite passes. The starting 474-pass baseline may only grow; the existing ignored test is not silently removed.
4. `tools/audit-scoreboard.sh` remains fully green; starting baseline 98/98.
5. The default release remains green for the solver-free I/M/N/U/V lanes and native T11; the documented optional-Z3 release binary keeps the complete 113-fixture subsystem scoreboard green.
6. `tools/legacy-sweep.sh` remains 87/87 CLEAN. Accepted-difference records remain unchanged unless separately approved.
7. A binary smoke scenario demonstrates:
   - honest count-only output;
   - timing-on warning;
   - memo warning;
   - strategy unsupported error;
   - statement-drop warning;
   - successful valid command after every recoverable failure.
8. No production output path emits a fixed timing or rate placeholder.
9. Project orientation documentation and `docs/bug-triage.md` describe the final behavior without overstating gap closure.

### 6.1 Implementation record

- Every command renderer now emits rewrite/state counts without CPU, wall-clock, decision-time, or rate
  placeholders. Timing-off is silent; timing-on reports that measurement is unavailable and stays disabled.
- `Attrs::memo` preserves source intent. Parser/build failures travel as owned `Diagnostic` values, and
  `Session` source-orders, deduplicates, and renders them. Re-imports, diamonds, renames, instances, and
  dependent rebuilds do not repeat the same source diagnostic; redefining the source may report it again.
- Source memo controls, dropped equations/memberships/rules, fatal module/view failures, `xmatchrew`, and
  `csd` now have stable user-facing outcomes. A strategy rejected before execution preserves the prior
  continuation; successful strategy execution retains normal invalidation behavior.
- Module replacement remains transactional. A failed candidate never replaces the previous source/build,
  current module, reflection state, or executable definitions.
- `conformance/probes/meta-recognized-boundaries.maude` and the orientation table record supported,
  proper-residue, inert, reflected-memo, and separately incompatible partial-AC META boundaries without
  injecting synthetic META warnings.
- The differential normalizer still strips only diagnostic blocks and measured-timing text. Its diagnostic
  terminators were made more precise so warnings cannot consume following command echoes or semantic output.

### 6.2 Completion evidence

- `cargo test -q -p tnk-repl --lib` — **91 passed**, including the complete timing, memo, strategy,
  statement/fatal-recovery, and META-boundary matrices.
- `cargo fmt --all --check` — passed.
- `cargo test --workspace --release` — **479 passed, 1 ignored** across 12 suites.
- `tools/audit-scoreboard.sh` — **98/98 PASS**.
- Default release subsystem lanes — **I 28/28, M 10/10, N 16/16, U 27/27, V 21/21, T11 1/1 PASS**.
- Optional-Z3 `tools/subsystems-scoreboard.sh` — **113/113 PASS**.
- `tools/legacy-sweep.sh` — **87/87 CLEAN**; the four accepted-difference records were not widened.
- `conformance/probes/v1-honest-behavior-smoke.maude` through the release binary produced count-only
  successful results, one timing warning, source/control memo warnings, a dropped-statement warning,
  deliberate strategy/module/view errors, and a successful command after every recoverable failure.
- A final production-source search found no fixed timing/rate formatter. The only `0ms`, `Decision time`,
  or `rewrites/second` literals under `crates/*/src` are the focused test's forbidden-output assertions.
- Direct Maude 3.5.1 and tnk runs of `conformance/probes/meta-recognized-boundaries.maude` established the
  documented supported/inert split; supported ordinary/proper-residue cases match values and counts, while
  unsupported conditioned/strategy cases remain unreduced rather than partially computing.

## 7. Completion definition

This goal is complete only when a user can distinguish, without reading the source:

- a command that executed successfully;
- a command that failed;
- a statement that was dropped while its module survived;
- a recognized feature that is intentionally unavailable;
- an operation that returned a real rewrite or state count;
- an advanced META operation outside the supported boundary.

No recognized feature covered by this goal may fail silently, and no output may present a fabricated measurement as fact.
