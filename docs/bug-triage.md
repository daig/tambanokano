# Known behavior triage

**Date:** 2026-07-26
**Purpose:** standalone triage of currently known tnk bugs, behavioral divergences, robustness failures, accepted differences, and unverified risk areas relevant to the prototype/v0 boundary.
**Evidence boundary:** entries not marked resolved retain the documentation-survey evidence boundary: retained conformance records, source inspection, and the direct probes already run. TNK-001 and TNK-002 were subsequently implemented and reverified against the live Maude oracle and retained regressions.

## 1. How to read this document

A green test or sweep does not mean that tnk is behaviorally identical to Maude on every input:

- The audit scoreboard covers its fixed 77-fixture corpus.
- The legacy sweep calls a fixture **CLEAN** when its current difference is byte-identical to a ratified accepted diff.
- The differential harness removes warning/advisory blocks before comparison.
- Missing features and legal-input corners absent from the fixture corpus are not exercised.
- A timeout is a separate gate from eventual semantic equality.

The entries below use these classifications:

- **Bug:** tnk accepts or encounters the input but crashes, computes a wrong value/sort/normal form, or violates the intended recovery contract.
- **Compatibility rejection:** Maude accepts and executes the input, while tnk rejects it explicitly.
- **Behavioral divergence:** both execute, but observable order, counts, reflection, or presentation differs.
- **Robustness/performance:** semantics may be correct, but termination, interruptibility, or the retained resource gate differs.
- **Deferred surface:** known unimplemented behavior, not an accidental regression.
- **Candidate:** source-admitted risk not yet established by a minimal oracle comparison.

Severity is impact, not implementation order:

- **Critical:** process/session termination on legal or Maude-recoverable input.
- **High:** wrong semantic result, sort, or normal form; or rejection of a practical legal language feature.
- **Medium:** bounded semantic/reflection issue, explicit compatibility rejection, or release-gate failure.
- **Low:** accounting, ordering, diagnostics, or presentation without a wrong solution set/value.
- **Accepted:** a ratified divergence retained intentionally for now.

## 2. Executive triage

| ID | Severity | Classification | Summary | Current status |
|---|---|---|---|---|
| TNK-001 | Critical | Bug | Legal interleaved operator evaluation strategy panics | **Resolved 2026-07-26**; oracle-differential fixture retained |
| TNK-002 | Critical | Bug | Out-of-range `frozen` attribute panics instead of recovering | **Resolved 2026-07-26**; oracle-differential fixture retained |
| TNK-003 | Critical | Bug | Nonbinary `assoc` declaration panics instead of recovering | **Resolved 2026-07-26**; oracle-differential fixture retained |
| TNK-004 | High | Bug | Stuck conditional prevents required branch normalization | **Resolved 2026-07-26**; oracle-differential fixtures retained |
| TNK-005 | High | Compatibility rejection | Imported strategy declarations/definitions disappear during flattening | **Resolved 2026-07-26**; six oracle-differential fixtures retained |
| TNK-006 | Medium | Compatibility rejection | `top` on a non-application strategy errors instead of being ignored | Confirmed by direct oracle/tnk probe |
| TNK-007 | Medium | Bug | Exact `decFloat(_, 0)` fails for extreme subnormals | Confirmed by direct oracle/tnk probe |
| TNK-008 | Medium | Bug | Incomparable membership targets use the wrong tiebreak | Confirmed by direct oracle/tnk probe |
| TNK-009 | Medium | Behavioral divergence | Strategy-module reflection emits the wrong implicit BOOL import mode | Confirmed by direct oracle/tnk probe |
| TNK-010 | Medium | Robustness/performance | I19/I20 no longer reliably satisfy the retained 60-second gate | Confirmed by current gate runs |
| DIV-001 | Accepted | Behavioral divergence | AC match solution order differs | Recorded accepted diff |
| DIV-002 | Accepted | Behavioral divergence | Mixed-symbol ACU search-goal echo differs | Recorded accepted diff |
| DIV-003 | Accepted | Behavioral divergence | `matchrew`/`amatchrew` cumulative counts differ | Recorded accepted diff |
| DIV-004 | Accepted | Behavioral divergence | Indexed `metaSearch` billing differs | Recorded accepted diff |

## 3. Confirmed bugs and compatibility rejections

### TNK-001 — Legal interleaved evaluation strategy panics — RESOLVED

- **Severity:** Critical
- **Classification:** Bug; legal-input process termination
- **Confidence:** Confirmed by direct comparison
- **Status:** Resolved 2026-07-26
- **Primary area:** operator evaluation strategies
- **Implementation:** `tnk-core`, `Signature::set_strategy` and `Runtime::reduce`

#### Summary

Maude permits generalized operator evaluation strategies containing more than one top-rewrite marker (`0`) or otherwise interleaving argument reduction and top reduction. Before the fix, tnk stored only argument positions preceding one implicit final top attempt and asserted on every intermediate `0`.

#### Reproduction used

```maude
fmod GENERAL-STRAT is
  sort S .
  ops a b : -> S .
  op f : S -> S [strat (0 1 0)] .
  eq f(a) = b .
endfm
red in GENERAL-STRAT : f(a) .
```

#### Expected behavior

Maude loads the module and reduces `f(a)` to `b` with one rewrite.

#### Pre-fix behavior

tnk exited with status 101. The assertion reported that `[0, 1, 0]` referenced an argument outside the valid range or contained a non-trailing `0`.

#### Pre-fix impact

- A legal Maude module terminated the entire tnk process during module construction.
- The failure was not isolated to one command; the session was lost.
- General support for the `strat` operator attribute could not be claimed.

#### Resolution

The signature now normalizes the complete strategy into argument and top instructions, including Maude's duplicate/adjacent-zero cleanup, implicit final zero, and eager/lazy/semi-eager classification for flattened associative operators. The iterative reducer executes those instructions in order, computes lazy argument true sorts at the first top attempt, excludes `owise` from intermediate attempts, and restarts the replacement term's own strategy after a successful top rewrite.

Arguments evaluated after a top attempt use Maude-style reducible per-occurrence copies, preserving rewrite counts when subject construction shared the original redex. Fresh ACU/AU applications are normalized before their first top attempt; semi-eager AC reduces each distinct multiset entry once, while semi-eager AU reduces every ordered occurrence.

Permanent coverage lives in `conformance/strat.maude` and the `tnk-frontend` `strat_conforms` test. It covers immediate and delayed top success, skipped arguments, intermediate `owise` suppression, `(1 0 2 0)`, omitted zeroes, normalized duplicates, shared post-top redexes and eager descendants, and semi-eager AC/AU applications with oracle-compatible accounting.

#### Acceptance contract

- [x] The module loads without panic.
- [x] The complete evaluation strategy is preserved.
- [x] The probe reduces to `b` with the oracle-compatible count and sort.
- [x] Other legal forms with no top marker or multiple/interleaved top markers have explicit coverage.

---

### TNK-002 — Out-of-range `frozen` position kills the process — RESOLVED

- **Severity:** Critical
- **Classification:** Bug; recovery/robustness divergence
- **Confidence:** Confirmed by direct comparison
- **Status:** Resolved 2026-07-26
- **Primary area:** declaration validation
- **Implementation path:** `tnk-frontend/src/sig/build_sig.rs` pass B → `tnk-core::Signature::set_frozen`

#### Summary

Previously, a bad `frozen` position that Maude treats as a recoverable declaration mistake reached an engine assertion and terminated tnk.

#### Reproduction used

```maude
fmod BAD-FROZEN is
  sort S .
  op a : -> S .
  op f : S -> S [frozen (2)] .
endfm
red in BAD-FROZEN : f(a) .
```

#### Expected behavior

Maude warns that position `2` is invalid for unary `f`, ignores the `frozen` attribute, retains the operator, and returns `f(a)` normally.

#### Current behavior

`Engine::set_frozen` now validates the complete source position list before mutating the symbol. It returns `false` for an invalid position, preserves any previously installed symbol metadata, and pass B deliberately ignores that failed attribute while retaining the operator declaration. tnk remains silent because warning/advisory delivery is a separate deferred diagnostics surface.

#### Original failure path

The surface parser accepts `2` as a syntactically valid unsigned position and stores `Some([2])`; it cannot reject the value without the operator's arity. Signature pass B has both the declaration and its built symbol, but forwards the vector unchanged. `Signature::set_frozen` then treats the user-controlled range check as an internal invariant and calls `assert!`, so normal module-error handling never gets a recoverable error.

Maude validates at the pre-module boundary. If any explicit position is invalid, it clears the whole accumulated frozen set, does not install the `FROZEN` flag, warns, and keeps the operator declaration. This is atomic attribute recovery: filtering out only the bad position would be wrong when a list contains both valid and invalid positions.

#### Impact before resolution

- A one-character declaration error killed the whole process.
- The warning-normalization policy could not hide the difference because tnk never reached command execution.
- The failure exposed the broader audit target that user-controlled attribute validation must not rely on assertions.

#### Resolution

Validation now lives at the frontend/kernel boundary where the completed operator arity is available. One invalid explicit position rejects the entire candidate attribute rather than filtering the list, and the recoverable result is exposed by the public engine API. The focused kernel regression `invalid_frozen_positions_are_recoverable_and_atomic` covers both fresh and previously configured symbols. `conformance/audit/A3a-rewrite-frozen.maude` retains the unary and mixed valid/invalid live-oracle cases.

#### Acceptance contract

- [x] The module loads without panic.
- [x] `f` remains available with the invalid attribute ignored.
- [x] A mixed valid/invalid position list ignores the entire attribute; it does not retain the valid subset.
- [x] The original command returns `f(a)` with sort `S` and zero rewrites.
- [x] A rewrite-observable mixed-list probe reaches `f(b, d)` with two rewrites, proving that neither argument remained frozen.
- [x] Semantic recovery is independent of diagnostics; Maude's warning remains deferred under the selected v0 diagnostics contract.

---

### TNK-003 — Nonbinary `assoc` declaration kills the process — RESOLVED

- **Severity:** Critical
- **Classification:** Bug; recovery/robustness divergence
- **Resolved:** 2026-07-26
- **Evidence:** oracle-differential fixture retained
- **Primary area:** theory-attribute validation
- **Implementation path:** `tnk-frontend/src/sig/build_sig.rs`

#### Summary

Associativity is meaningful only for a binary declaration. Maude warns when it appears on a ternary operator, clears the compiled attribute, and keeps the operator usable with ordinary free-theory semantics. tnk formerly passed the raw attribute into `Signature::add_op_au`, whose binary-arity invariant panicked.

#### Reproduction used

```maude
fmod BAD-ASSOC is
  sort S .
  op a : -> S .
  op f : S S S -> S [assoc] .
endfm
red in BAD-ASSOC : f(a, a, a) .
red in BAD-ASSOC : f(a, a, f(a, a, a)) .
```

#### Expected behavior

Maude warns that `f` has three rather than two domain sorts, then reduces both terms as ordinary ternary applications with sort `S` and zero rewrites. The nested application remains nested rather than being AU-flattened.

#### Resolution

Signature construction now derives `effective_assoc = raw_assoc && arity == 2` after resolving the declaration's domain. That effective flag drives theory dispatch, compiled `SymbolSyntax`, and constructor-axiom consistency checks. The raw surface declaration remains unchanged for source-faithful display. A nonbinary `assoc` declaration therefore selects a free symbol; the kernel's binary AU/ACU invariant remains asserted rather than being weakened.

Warning emission is still deferred with the broader diagnostics surface. This repair intentionally implements Maude's semantic warning-and-ignore recovery first; strict rejection is recorded separately as a post-parity language-policy proposal.

#### Retained coverage

- `sig::build_sig::tests::nonbinary_assoc_compiles_as_free_theory` checks the effective syntax flag, free-node shape, nesting, sort, and zero rewrite count.
- `conformance/audit/A1b-opdecl-arity.maude` checks the direct and nested commands against the live Maude oracle.

#### Acceptance contract

- [x] The module loads without panic.
- [x] The invalid `assoc` attribute is ignored for compiled semantics.
- [x] The demonstrated ternary operator remains usable with sort `S` and zero rewrites.
- [x] A nested ternary application remains structurally nested, proving free-theory fallback.
- [ ] Sibling `comm`, `idem`, `id`, and `iter` arity/kind recovery cases receive explicit oracle fixtures before the full theory-attribute validation family is considered closed.

---

### TNK-004 — Stuck conditional leaves reducible branches untouched — RESOLVED

- **Severity:** High
- **Classification:** Bug; wrong normal form, count, and sort
- **Resolved:** 2026-07-26
- **Evidence:** oracle-differential fixtures retained
- **Primary area:** built-in conditional evaluation
- **Implementation path:** `tnk-core/src/engine.rs`

#### Summary

When the condition of `if_then_else_fi` is symbolic and cannot select a branch, Maude still reduces every branch before trying user equations. tnk formerly modeled BranchSymbol as only `strat (1 0)`, so a failed selection incorrectly reached the normal-form point with both branches untouched.

#### Reproduction used

With the standard prelude loaded:

```maude
red in BOOL : if X:Bool then (true and false) else (false or true) fi .
```

#### Expected behavior

Maude normalizes both branches and returns:

```text
result Bool: if X:Bool then false else true fi
```

The command performs five rewrites.

#### Resolution

BranchSymbol now installs the intrinsic dynamic strategy `1, 0, 2, 3, ..., n, 0`. It reduces the condition and attempts selection at the first top instruction. A successful selection abandons the old frame, preserving decided-condition laziness. A failed selection suppresses user equations at that intermediate top, continues through fresh per-occurrence reductions of every branch, rebuilds the conditional, and tries ordinary plus `owise` equations only at the final top.

Signature construction also mirrors Maude's BranchSymbol sort completion: for each proper sort `S` in the branch kind it adds a synthetic `condition-sort S ... S -> S` declaration. The rebuilt open conditional therefore acquires `Bool`, not merely kind `[Bool]`, after both Boolean branches normalize.

#### Retained coverage

- `engine::tests::builtin_equality_and_branch_over_bool` covers decided-condition laziness, two independently counted copies of a shared stuck branch, least-sort refinement, and deferred user-equation ordering through a deliberately lazy result operator.
- `conformance/audit/A3e-branch-stuck.maude` pins the live-prelude value, five-rewrite count, and `Bool` result sort against Maude 3.5.1.
- `conformance/prelude-bool.maude` exercises the same contract through the prelude bootstrap and legacy differential path.

#### Acceptance contract

- [x] Both branches reduce when the condition is undecidable.
- [x] The rebuilt conditional contains `false` and `true` in the demonstrated case.
- [x] Result sort `Bool` and rewrite count 5 match the oracle.
- [x] Chosen-condition behavior remains lazy: the unselected branch is not reduced when the condition decides.
- [x] User equations are deferred until after every branch of a stuck conditional has normalized.

---

### TNK-005 — Imported strategy declarations and definitions are unavailable — RESOLVED

- **Severity:** High
- **Classification:** Compatibility rejection
- **Resolved:** 2026-07-26 in `499123e`
- **Evidence:** six oracle-differential fixtures plus focused representation tests
- **Primary areas:** module-expression flattening, strategy definition dispatch, home grammars, reflection, and session lifecycle

#### Summary

The module flattener formerly kept only the root strategy module's own `strat`/`sd` declarations. Ordinary imported sorts, operators, and rules were present, but an imported named strategy was rejected as unknown. Strategy modules therefore did not compose through the same module algebra as their ordinary declarations.

#### Reproduction used

```maude
smod STRAT-BASE is
  sort S .
  ops a b : -> S .
  rl [r] : a => b .
  strat go : @ S .
  sd go := r .
endsm

smod STRAT-USE is
  protecting STRAT-BASE .
endsm

srew in STRAT-USE : a using go .
```

Maude resolves `go` and returns one `S: b` solution with one rewrite. The frozen tnk baseline instead reported that `go` was neither a rule label nor a strategy.

#### Resolution

Strategy declarations and definitions now travel through the module-expression accumulator with stable source origin, source position, and plain-import home provenance. Direct, transitive, all-mode, sum, ordinary-renaming, and functional-instantiation paths preserve or transform the payload in the same order as ordinary module donation. Diamond paths suppress only repeated donations of the same origin; text-identical declarations from independent modules remain distinct. An ordinary module importing a strategy module ignores the complete illegal import and continues processing later input.

The strategy compiler now resolves declaration profiles by argument and subject kinds, retains ordered definition candidates instead of overwriting by name, compiles each definition lhs, matches every compatible candidate, and specializes the body with the shared lhs substitution. Calls remain lazy, so recursive definitions do not expand during resolution. Plain imported definitions parse against a donor grammar whose semantic actions are re-pointed to destination-engine symbol/sort identities; an unmappable donor is skipped rather than parsed under the wrong grammar.

Source and flattened strategy collections remain separate for `upStratDecls`, `upSds`, and `upModule`. The local META-INTERPRETER path consumes the same source-backed representation rather than patching a rebuilt module with a second definition list. Ordinary dependency invalidation rebuilds existing strategy importers after a donor redefinition.

#### Retained coverage

- `conformance/audit/A3f-strategy-import-basic.maude` — direct/transitive `protecting`/`extending`/`including`, declaration-only strategies, illegal cross-family import, and session continuity.
- `conformance/audit/A3g-strategy-import-order.maude` — multiple definitions, local/import weaving, import-order reversal, diamond/repeated-origin dedup, independent conflicts, values, and cumulative counts.
- `conformance/audit/A3h-strategy-definition-dispatch.maude` — kind profiles, same-kind overloads, subject-kind selection, definition-lhs matching, and shared bindings.
- `conformance/audit/A3i-strategy-import-home.maude` — donor-grammar collisions, nested imported calls, unmappable definitions, and recovery.
- `conformance/audit/A3j-strategy-import-transform.maude` — sums, renaming, instantiation, and donor redefinition.
- `conformance/audit/A5g-strategy-import-reflection.maude` — source/flat and transformed strategy projections through the standalone and `upModule` APIs.
- Focused Rust tests pin origin identity, kind profiles, candidate order/shared variables, destination identities, recursive payload transforms, source/flat separation, and importer invalidation.

Binding implementation record: [`migration/tnk-005-strategy-imports-goal.md`](migration/tnk-005-strategy-imports-goal.md).

#### Acceptance contract

- [x] Imported strategy declarations and definitions execute in every legal import mode.
- [x] The motivating probe produces `b` with one rewrite.
- [x] Diamond/repeated origins and independent conflicts follow oracle-derived order and deduplication.
- [x] Overloaded and multi-definition calls retain every matching candidate and lhs binding.
- [x] Plain imports preserve donor grammar semantics without foreign engine identities.
- [x] Sum, ordinary renaming, instantiation, and redefinition preserve strategy behavior.
- [x] Source/flat reflection agrees with execution.
- [x] Illegal imports and malformed donor definitions remain recoverable.

---

### TNK-006 — `top` on a non-application strategy is rejected

- **Severity:** Medium
- **Classification:** Compatibility rejection
- **Confidence:** Confirmed by direct comparison
- **Primary area:** strategy resolution
- **Likely implementation touchpoint:** `tnk-frontend/src/strategy.rs`

#### Summary

Maude treats `top` on a strategy for which the modifier has no meaning as a recoverable misuse: it warns, drops the modifier, and executes the inner strategy. tnk rejects the whole strategy expression.

#### Reproduction used

```maude
mod TOP-STRAT is
  sort S .
  op a : -> S .
endm
srew in TOP-STRAT : a using top(idle) .
```

#### Expected behavior

Maude warns that the top modifier on a non-application strategy is ignored, then returns `a` as the one `idle` solution with zero rewrites.

#### Actual behavior

tnk returns:

```text
error: top(…) of a non-rule strategy is a follow-on
```

#### Impact

- Legal/recoverable Maude input is rejected.
- Warning normalization would otherwise permit exact command-result parity.
- The impact is bounded because the underlying inner strategy is already supported.

#### Current understanding

The resolver pattern-matches `top` only around rule application and treats every other inner strategy as unsupported. The Maude-compatible recovery is to discard the modifier and resolve the inner expression, with an optional diagnostic.

#### Acceptance contract

- `top(idle)` executes as `idle`.
- The result, sort, solution count, and rewrite count match the oracle.
- Applicable `top(rule-or-strategy-application)` semantics remain unchanged.

---

### TNK-007 — Extreme-subnormal exact `decFloat` remains unreduced

- **Severity:** Medium
- **Classification:** Bug; bounded wrong numeric behavior
- **Confidence:** Confirmed by direct comparison
- **Primary area:** float conversion built-in
- **Likely implementation touchpoint:** `tnk-core/src/builtin.rs`, `dec_float_parts`

#### Summary

`decFloat(f, 0)` requests the exact decimal decomposition of a binary float. Normal values and positive requested precisions work. The exact path for an extreme subnormal attempts to convert its power-of-two denominator to `u64`; that conversion cannot represent the denominator and the built-in declines to reduce.

#### Reproduction used

With the standard prelude loaded:

```maude
red in CONVERSION : decFloat(4.9406564584124654e-324, 0) .
```

#### Expected behavior

Maude returns an exact `DecFloat` triple. The observed result line was 783 bytes long.

#### Actual behavior

tnk returns the unreduced application:

```text
result DecFloat: decFloat(4.9406564584124654e-324, 0)
```

#### Impact

- Exact conversion is incomplete over the full finite IEEE-754 domain.
- The issue is narrow: ordinary-range floats and finite positive precision are not implicated by this probe.

#### Current understanding

The algorithm needs the exponent of a power-of-two big-integer denominator, not the denominator represented as a machine integer. Computing the exponent directly would avoid the lossy conversion boundary.

#### Acceptance contract

- Every finite subnormal accepted by the float parser reduces under precision zero.
- The exact sign/digits/exponent triple matches Maude.
- Existing positive-precision rounding and ordinary-range exact cases remain unchanged.

---

### TNK-008 — Incomparable membership targets choose a different sort

- **Severity:** Medium
- **Classification:** Bug; wrong sort in a nonconfluent specification
- **Confidence:** Confirmed by direct comparison
- **Primary area:** membership ordering and connected-component sort indices
- **Likely implementation touchpoint:** membership-table sorting in `tnk-core`

#### Summary

When two applicable memberships lower a kind term to incomparable target sorts, the specification is contradictory/nonconfluent, but Maude still has a deterministic observable tiebreak based on connected-component sort indexing. tnk breaks the tie using declaration-level `SortId` order.

#### Reproduction used

```maude
fmod MB-TIE is
  sorts A B D X Y .
  subsorts X < A B .
  subsorts Y < A D .
  op t : -> [X] .
  mb t : B .
  mb t : D .
endfm
red in MB-TIE : t .
```

#### Expected behavior

Maude performs one membership application and reports sort `D`.

#### Actual behavior

tnk performs one membership application and reports sort `B`.

#### Impact

- A real wrong-sort result is observable.
- The input is intentionally nonconfluent, so the practical scope is narrow.
- This is distinct from multi-top kind-name ordering, which now matches Maude.

#### Current understanding

The membership table sorts incomparable targets by raw `SortId`. It should use the same connected-component order that Maude uses for its constraint table. The already-implemented DFS-derived component index is likely the relevant information, but the exact direction and stable-order rules must remain those established by the probe/reference.

#### Acceptance contract

- The probe returns sort `D` with one rewrite.
- Comparable targets continue to apply smallest-target-first.
- Declaration order and component order are separately tested.

---

### TNK-009 — Strategy reflection uses the wrong implicit BOOL import mode

- **Severity:** Medium
- **Classification:** Behavioral divergence; wrong reflected value
- **Confidence:** Confirmed by direct comparison
- **Primary area:** `upModule` and implicit-import reflection
- **Likely implementation touchpoint:** source-backed module up-translation

#### Summary

Strategy-module reflection now works substantially beyond what older documentation claims: `upModule`, `upStratDecls`, and `upSds` compute real strategy declarations/definitions. One structural difference remains in the direct probe: the automatic BOOL import is emitted with the wrong import mode.

#### Reproduction shape

A small `smod SM` containing a sort, constants, a labelled rule, `strat go`, and `sd go := r` was reflected with:

```maude
red in META-LEVEL : upModule('SM, false) .
red in META-LEVEL : upStratDecls('SM, false) .
red in META-LEVEL : upSds('SM, false) .
```

#### Expected behavior

The reflected strategy module begins with:

```text
including 'BOOL .
```

#### Actual behavior

tnk emits:

```text
protecting 'BOOL .
```

The strategy declarations and definition otherwise matched in the observed diff.

#### Impact

- Reflected module values are structurally different.
- Meta-programs that inspect import modes can branch differently.
- A reflect/down-translate round trip can encode a different import contract.

#### Current understanding

The implicit BOOL injection path loses or substitutes the import mode when producing source/reflected module data. This should be handled independently from the broader, now-working strategy reflection implementation.

#### Acceptance contract

- The direct strategy-module probe has no import-mode diff.
- Ordinary modules and explicit BOOL imports retain their correct modes.
- `upStratDecls` and `upSds` remain unchanged.

---

### TNK-010 — Local meta-interpreter fixtures miss the retained timeout gate

- **Severity:** Medium
- **Classification:** Robustness/performance
- **Confidence:** Confirmed by current gate runs
- **Primary area:** nested non-flat local meta-interpreters
- **Relevant fixtures:** `I19-russian-dolls-nonflat`, `I20-russian-dolls-nonflat2`

#### Summary

The I-S documentation states that all 27 fixtures pass the retained per-fixture 60-second gate. On the surveyed checkout/machine, the combined subsystem run reported 110/112 because I19 and I20 timed out. I19 passed in isolation at 59.77 seconds. I20 still timed out in isolation at 60.32 seconds and passed with an extended timeout in 82.01 seconds.

#### Expected behavior

All I-S fixtures complete with matching output under the recorded 60-second limit.

#### Actual behavior

- I19 is timing-sensitive and effectively on the boundary.
- I20 misses the limit.
- I20's output matches the oracle when given more time; no semantic difference was observed.

#### Impact

- The current “27/27 retained gate green” status is inaccurate.
- CI or slower machines can fail nondeterministically even when semantics are correct.
- The nested interpreter path may be impractical for prototype users at modest nesting depth.

#### Current understanding

This is a performance regression or an inadequately calibrated gate, not an established semantic bug. Triage must decide whether the 60-second invariant is part of v0 correctness. Raising the timeout without understanding the regression would change the contract rather than restore it.

#### Acceptance contract

One of the following must be chosen explicitly:

1. Restore I19/I20 below the retained 60-second limit with their exact outputs unchanged; or
2. Revise the gate with a documented reason and a replacement performance invariant.

## 4. Ratified accepted divergences

These are known differences, not discoveries to hide behind the word “clean.” `tools/legacy-sweep.sh` verifies that they have not drifted beyond their recorded forms.

### DIV-001 — AC match solution enumeration order

- **Status:** Accepted
- **Record:** `conformance/accepted-diffs/acu-match.diff`
- **Behavior:** tnk enumerates AC matcher solutions in a different order from Maude.
- **Preserved contract:** the solution set and bindings are programmatically set-equal.
- **Risk:** order-sensitive scripts or users can observe the difference even though the mathematical solution set is complete.
- **Closure condition:** reproduce Maude's Diophantine enumeration order, or keep the divergence explicitly documented.

### DIV-002 — Mixed-symbol ACU search-goal echo order

- **Status:** Accepted
- **Record:** `conformance/accepted-diffs/objects.diff`
- **Behavior:** a search-goal echo containing a mixed-symbol ACU multiset prints arguments in a different order.
- **Preserved contract:** the terms are equal modulo the operator's axioms; computation is not known to differ in that fixture.
- **Risk:** byte-oriented tools and transcript comparisons observe the difference.

### DIV-003 — `matchrew`/`amatchrew` cumulative rewrite counts

- **Status:** Accepted
- **Record:** `conformance/accepted-diffs/strategy.diff`
- **Behavior:** eager sub-search execution collapses or shifts cumulative per-solution rewrite counts relative to Maude's parallel task/odometer schedule.
- **Preserved contract:** values, solution order, and reachability match in the recorded case.
- **Risk:** count-sensitive analysis and performance accounting differ.
- **Current understanding:** the faithful repair is a scheduler change, not a constant/count adjustment.

### DIV-004 — Indexed `metaSearch` billing

- **Status:** Accepted
- **Record:** `conformance/accepted-diffs/prelude-meta.diff`
- **Behavior:** one indexed meta-search result reports a different rewrite count because lazy exploration and meta-down rule order account work differently.
- **Preserved contract:** reflected value, sort, bindings, and solution order match in the recorded case.
- **Risk:** reflective tools that treat rewrite counts as semantic metadata observe the difference.

## 5. Other known observable differences

These are established residual families, but this document does not claim that every member was freshly re-probed during the follow-up.

### OUT-001 — Mixed-symbol ACU canonical presentation

- Mixed-symbol ACU arguments can print in a different canonical order.
- A bounded AC `frewrite` can therefore expose a different intermediate term order even when the unbounded result and rewrite count are order-independent.
- Same-symbol multisets are more conformant than the broad old documentation suggests.

### OUT-002 — Strategy command echo can lose required parentheses

- An expression such as `(r1 | r2) !` can echo as `r1 | r2 !`.
- The executed strategy is the parsed original; the echo denotes a different strategy if reparsed.
- This is more serious than whitespace-only presentation because the printed command does not round-trip semantically.

### OUT-003 — Trace/result annotation and wording differences

Known examples include some statement-body rendering, substitution/canonical order, matched-portion labels, blank lines, bounded rewrite sort annotations, zero-solution wording, `continue` wording, and meta-module grouping/order. These should be split into reproducible issues before repair rather than treated as one formatter task.

## 6. Deferred or missing behavior

These are real compatibility gaps. They are not all accidental bugs and may remain explicit v0 limitations.

### GAP-001 — Search tracing

`set trace on` does not emit Maude's per-rule trace blocks from ordinary `search` or from a rewrite condition's nested search. Results and counts are not known to be changed by this omission.

### GAP-002 — Diagnostics

Most warning/advisory behavior is absent: preregularity, collapse-at-top, ambiguity, declaration recovery, import hygiene, discarded modules, and related messages. The current differential harness intentionally strips diagnostics, so the green corpus cannot establish this surface.

### GAP-003 — Real timing/rate reporting

The REPL generally prints fixed `0ms` and unknown `~ rewrites/second` text rather than measured timing. Counts remain the meaningful part of the current contract.

### GAP-004 — Interrupting a running command

Ctrl-C abandons the current input buffer but cannot cancel an executing reduction/search. This is tied to deferred Phase I-C cooperative cancellation and thread coordination.

### GAP-005 — `xmatchrew`

Extension-match rewriting is parsed but rejected during strategy resolution. The missing mechanism is extension-residue exposure and reassembly of the rewritten matched portion.

### GAP-006 — Conditional strategy definitions (`csd`)

`csd` syntax is parsed, but definitions reject during resolution because runtime condition bindings are not passed into the strategy body.

### GAP-007 — Strategy meta parse/print

`metaParseStrategy` and `metaPrettyPrintStrategy` remain inert. `upModule`, `upStratDecls`, and `upSds` should not be grouped into this gap: they now compute, subject to TNK-009.

### GAP-008 — Conditional and partial meta operations

Current source-admitted boundaries include:

- non-empty conditions for `metaMatch`;
- conditional-rule and partial-substitution forms of `metaApply`;
- proper partial AC contexts for `metaXmatch`.

These stay inert rather than returning a known-wrong value. Each needs an independent fixture and contract.

### GAP-009 — Other deliberately deferred surfaces

- `memo` semantics and memo controls;
- external managers beyond STD-STREAM;
- LOOP-MODE;
- Full Maude;
- LaTeX output;
- broader debugger/profile/show/set-print/CLI command families.

These belong in the feature/issue collection, not in a claim that the implemented core is malfunctioning.

## 7. Unverified candidates

The following remain risks, not confirmed bugs. They should not be presented as factual limitations until a minimal Maude/tnk comparison establishes the input and behavior.

### RISK-001 — Recursive parameterized strategy calls

The current resolver uses bounded inline expansion. Recursive parameterized definitions may reject or hit the expansion bound, but no direct oracle probe is recorded here.

### RISK-002 — Unusual cross-kind overload grouping

A source comment warns about cross-kind declaration groups. A direct basic overload with distinct domain/range kinds worked correctly and did not reach the old assertion. Only a narrower grouping case, if one exists, remains suspect.

### RISK-003 — Exotic AC/iter membership extension

Broad source comments about CUI collapse and iter membership are stale for the direct common probes: CUI collapse produced the same solution set, and iter membership produced the same result/count. More exotic extension compositions remain unverified.

### RISK-004 — View validation and unusual map/module-expression forms

Source-admitted boundaries include connected-component/subsort preservation, operator-map type checks, theory proof obligations, disambiguated source op maps, renamed/instantiated theory imports, and instantiation over a module-sum base.

### RISK-005 — Reflection boundaries

Potential partial behavior remains around flat builtin closures, non-mixfix print options, structured module expressions, and op-to-term view reflection. Several older reflection comments have already proven stale, so each requires a fresh probe.

### RISK-006 — Re-entrant condition GC

A code path notes incomplete rooting for re-entrant rewrite-condition state when the low-level engine is embedded with GC enabled. The REPL's cited path has GC disabled. No current end-to-end failure is established.

### RISK-007 — Garbage-term Earley complexity

The audit records a latent exponential blowup for genuinely unparseable terms against a large grammar. A common trigger was removed, but the general complexity problem is not known to be bounded. This follow-up did not re-run that expensive reproducer.

## 8. Triage recommendations

### 8.1 Process-safety group

TNK-001, TNK-002, and TNK-003 are resolved with retained fixtures. No confirmed declaration-recovery process-safety defect remains in this survey. A complete sweep should still cover sibling theory and position attributes when that broader validation work is selected; those are unverified risk candidates, not established bugs.

### 8.2 Semantic-correctness group

TNK-004 is resolved with retained value, count, sort, laziness, and equation-ordering coverage. TNK-007 and TNK-008 remain genuine but sharply bounded numeric/nonconfluent wrong-computation corners.

### 8.3 Strategy composition group

TNK-005 is resolved with compositional-import, ordering, transform, reflection, lifecycle, and recovery fixtures. TNK-006 remains a legal-input compatibility failure. TNK-001's operator-evaluation machinery is resolved independently; GAP-005/GAP-006 and RISK-001 remain separate proposals so strategy-language work does not silently become an unbounded rewrite.

### 8.4 Reflection group

TNK-009 is a small, observed structural mismatch within otherwise newly working strategy reflection. It should not be used to relabel the entire strategy-reflection surface as inert.

### 8.5 Performance group

TNK-010 requires an explicit product/gate decision. Semantic conformance after 82 seconds does not satisfy a documented 60-second invariant, but changing the invariant is not the same as fixing a regression.

### 8.6 Fixture policy

Before changing implementation, preserve every confirmed direct probe as a retained fixture with:

- accepted input;
- expected value and sort;
- rewrite/solution count where relevant;
- process exit/termination expectation;
- diagnostic normalization policy;
- timeout where relevant.

The TNK-001 probes are retained in `conformance/strat.maude`, the TNK-002 probes in `conformance/audit/A3a-rewrite-frozen.maude`, the TNK-003 probes in `conformance/audit/A1b-opdecl-arity.maude`, the TNK-004 probes in `conformance/audit/A3e-branch-stuck.maude` plus `conformance/prelude-bool.maude`, and the TNK-005 matrix in `conformance/audit/A3f`–`A3j` plus `A5g`. The remaining direct survey probes have not yet all been added to the permanent corpus.

## 9. Prototype/v0 decision view

This document does not set release priority. It exposes the decisions:

- **How much sibling declaration-recovery validation is required for v0?** The confirmed TNK-002 and TNK-003 panics are resolved; adjacent theory-attribute cases remain unverified risk candidates rather than confirmed defects.
- **Can v0 claim open-term functional reduction?** TNK-004 no longer blocks this claim for BranchSymbol: its symbolic-condition value, count, and sort contract is retained against the oracle.
- **Can v0 claim compositional strategy modules?** Yes for the retained import modes, ordering/conflict matrix, home parsing, sum/renaming/instantiation transforms, reflection, and session invalidation covered by TNK-005. The separate TNK-006 generalized-`top` deviation remains.
- **Are narrow numeric/nonconfluent/reflection corners acceptable as documented limitations?** This governs TNK-007–009.
- **Is the 60-second I-S gate binding?** This governs TNK-010.
- **Do ratified accepted diffs remain accepted for v0?** If yes, DIV-001–004 must appear in the user-facing limitations document rather than only in conformance internals.

The cleanest release statement, pending those decisions, is: the retained mainstream corpus is green, but tnk is not bug-free and still has confirmed wrong-normal-form behavior, legal-input rejection, bounded numeric/sort, reflection, accounting/order, diagnostics, and performance differences.
