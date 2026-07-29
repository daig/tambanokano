# Active behavior triage

**Date:** 2026-07-29
**Purpose:** current, actionable tnk correctness work: confirmed open bugs, accepted divergences that still
need an explicit product decision, deferred compatibility surfaces, and missing regression evidence.

Closed work is intentionally absent. Once an issue matches the reference contract, has retained coverage,
and passes the required gates, remove it from this file. The fixture, focused test, completed goal record, and
git history retain the evidence; resolved IDs are never reused.

## 1. Current baseline

The baseline at this revision is:

- optional-Z3 subsystem scoreboard: **113/113 PASS** at the unchanged per-fixture timeout;
- audit scoreboard: **98/98 PASS**;
- workspace tests: **474 passed, 1 ignored**;
- legacy sweep: **87/87 CLEAN**, including the four ratified accepted-diff records.

These gates cover only their fixtures. They do not overrule the open items below.

## 2. Source-recovery policy

### POL-001 — Reference first, deliberate strictness second

For malformed declarations that Maude accepts with warning-and-ignore recovery, the current parity target is
Maude's semantic behavior:

1. validate user-controlled attributes before selecting a theory-specific kernel representation;
2. ignore or clear the invalid attribute atomically, exactly as Maude does;
3. retain every declaration and valid attribute that Maude retains;
4. keep the session alive and prove that a following valid command still executes;
5. pin value, sort, structure, and rewrite count against the oracle;
6. keep warning text separable from semantic recovery while diagnostics parity remains deferred.

Kernel assertions are invariants, not a source-validation mechanism. Incorrect source must never reach an
arity/kind assertion or terminate the process.

A stricter tnk language policy may later reject source that Maude merely warns about, but only as a separate,
explicit change after the complete reference-recovery family is understood and covered. That change must:

- define the whole validation family rather than special-case one attribute;
- reject transactionally at the frontend/session boundary, never by panic;
- preserve session recovery;
- state whether strictness is unconditional or mode-controlled;
- replace the reference expectation only with an intentional, documented divergence.

Until that policy is adopted, reference recovery is normative.

## 3. Executive active register

| ID | Severity | Classification | Active concern |
|---|---|---|---|
| DIV-001–004 | Accepted | Behavioral divergences | Ratified order/accounting differences remain observable and must stay pinned |
| OUT-001, OUT-003 | Unclassified | Observable differences | Canonical presentation and trace/result formatting families still need isolation and decisions |
| GAP-001–009 | Deferred | Compatibility gaps | Tracing, diagnostics, timing, cancellation, strategy, meta, and broader surface gaps remain |

## 4. Confirmed open bugs

No confirmed implementation bugs remain in the active register at this baseline.

## 5. Ratified accepted divergences

These remain active product decisions, not closed implementation work. Their recorded forms must not widen.

### DIV-001 — AC match solution enumeration order

- **Record:** `conformance/accepted-diffs/acu-match.diff`
- **Behavior:** tnk enumerates the same AC solutions and bindings in a different order.
- **Risk:** order-sensitive consumers observe the difference.
- **Closure:** reproduce Maude's Diophantine enumeration order or keep it user-visible and explicitly accepted.

### DIV-002 — Mixed-symbol ACU search-goal echo order

- **Record:** `conformance/accepted-diffs/objects.diff`
- **Behavior:** a mixed-symbol ACU search goal prints arguments in a different canonical order.
- **Risk:** byte-oriented tools and transcripts differ although the term is equal modulo axioms.

### DIV-003 — `matchrew`/`amatchrew` cumulative rewrite counts

- **Record:** `conformance/accepted-diffs/strategy.diff`
- **Behavior:** eager sub-search scheduling reports different cumulative counts from Maude's parallel odometer.
- **Preserved contract:** values, solution order, and reachability match in the recorded cases.
- **Risk:** count-sensitive analysis and performance accounting differ.

### DIV-004 — Indexed `metaSearch` billing

- **Record:** `conformance/accepted-diffs/prelude-meta.diff`
- **Behavior:** one indexed result reports a different rewrite count because exploration work is billed in a
  different order.
- **Preserved contract:** reflected value, sort, bindings, and solution order match.

Before a release, either keep DIV-001–004 in the user-facing limitations or replace the underlying behavior
and delete the accepted-diff record. A green legacy sweep means only that the divergence has not drifted.

## 6. Other observable differences needing classification

### OUT-001 — Mixed-symbol ACU canonical presentation

Mixed-symbol ACU arguments can print in a different canonical order. A bounded AC `frewrite` can therefore
expose a different intermediate presentation even when the unbounded result and count are order-independent.
Split value/count effects from presentation-only effects, retain minimal probes, then either fix or ratify.

### OUT-003 — Trace/result annotation and wording family

Known examples include statement-body rendering, substitution/canonical order, matched-portion labels, blank
lines, bounded-rewrite sort annotations, zero-solution and `continue` wording, meta-module grouping/order,
hook line wrapping, and AC-equivalent reflected-equation order. A signature-disambiguated `show view` also
prints source sorts where Maude canonicalizes them as kinds. Split these into reproducible issues; do not treat
them as one formatter task or silently absorb them into diagnostic normalization.

The input is retained at `conformance/probes/cross-kind-ill-sorted-output.maude`: Maude 3.5.1 prints the
inapplicable context-free overload as `(f(a2)).B`, while tnk prints `(f(a2)).[B]`; both report kind `[B]`
with zero rewrites. A focused tnk test pins the current spelling, but the probe remains outside byte-parity
scoreboards and is not an accepted divergence until this output family is classified.

## 7. Deferred or missing behavior

These are real compatibility gaps. Their priority is a product decision, but their current boundary must stay
explicit.

### GAP-001 — Ordinary search tracing

`set trace on` still disables tracing for ordinary `search`; per-rule trace blocks are not emitted. Rewrite-
condition nested search tracing already matches Maude and is outside this gap.

### GAP-002 — Diagnostics

Most warning/advisory behavior remains absent: preregularity, collapse-at-top, ambiguity, declaration
recovery, import hygiene, discarded modules, and related messages. The differential harness strips these
blocks, so semantic recovery fixtures do not prove warning-text parity.

### GAP-003 — Real timing and rate reporting

Most commands print fixed `0ms` and unknown-rate tails rather than measured timing. Rewrite counts remain the
meaningful current contract.

### GAP-004 — Cooperative cancellation

Ctrl-C clears an input buffer but cannot cancel a reduction or search already executing. Long-running engine
operations have no shared cancellation token.

### GAP-005 — `xmatchrew`

Extension-match rewriting parses but rejects during strategy resolution because extension residue is not
exposed and reassembled around the rewritten portion.

### GAP-006 — Conditional strategy definitions (`csd`)

`csd` parses but rejects during resolution because runtime condition bindings are not threaded into the
strategy body.

### GAP-007 — Strategy meta parse and print

`metaParseStrategy` and `metaPrettyPrintStrategy` remain inert. Strategy declaration/definition reflection is
not part of this gap.

### GAP-008 — Conditioned and proper-partial meta operations

The remaining established boundaries are:

- non-empty conditions for `metaMatch`;
- conditional-rule forms of `metaApply`;
- proper partial-AC residue contexts for `metaXmatch`.

Non-empty partial substitutions for ordinary `metaApply` are implemented and covered by
`I01-meta-int-apply`; they are not part of this gap.

### GAP-009 — Other deliberately deferred surfaces

- `memo` semantics and controls;
- external managers beyond STD-STREAM;
- LOOP-MODE and Full Maude;
- LaTeX output;
- broader debugger, profiler, show, set-print, and CLI command families.

The optional `PERF-earley-leo-parser` proposal is performance work, not a correctness gap, while the parser's
deterministic effort bound and retained large-term gates remain green.

## 8. Work order

1. Select which GAP items block the next product boundary.
2. Revisit DIV-001–004 and OUT-001/OUT-003 as explicit release decisions.

When an item is complete, remove its body from this file in the same change that lands its retained evidence.
Do not accumulate resolution narratives here.
