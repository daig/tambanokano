# Known behavior triage

**Date:** 2026-07-26
**Purpose:** standalone triage of currently known tnk bugs, behavioral divergences, robustness failures, accepted differences, and unverified risk areas relevant to the prototype/v0 boundary.
**Evidence boundary:** entries marked resolved were implemented and reverified on 2026-07-26 against focused live-Maude probes, the cited reference-source paths, and retained oracle-differential fixtures. Unresolved gaps and risks retain the documentation-survey evidence boundary: retained conformance records, source inspection, and the direct probes already run.

## 1. How to read this document

A green test or sweep does not mean that tnk is behaviorally identical to Maude on every input:

- The audit scoreboard is a growing corpus (88 fixtures after the four TNK-006–009 regressions landed); historical 77/77 records describe the frozen 2026-07-05 manifest, not a fixed denominator.
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
| TNK-006 | Medium | Compatibility rejection | `top` on a non-application errors instead of being ignored | **Resolved 2026-07-26**; direct/named/non-application matrix retained |
| TNK-007 | Medium | Bug | Exact `decFloat(_, 0)` fails when the canonical denominator exceeds `u64` | **Resolved 2026-07-26**; finite-range boundary matrix retained |
| TNK-008 | Medium | Bug | Incomparable membership targets use the wrong tiebreak | **Resolved 2026-07-26**; component-index/order matrix retained |
| TNK-009 | Medium | Behavioral divergence | Automatic BOOL imports use the wrong mode across module kinds | **Resolved 2026-07-26**; source/flat reflection matrix retained |
| TNK-010 | Medium | Robustness/performance | I19/I20 no longer reliably satisfy the retained 60-second gate | **Resolved 2026-07-26**; gate restored without widening timeout |
| TNK-011 | High | Bug | Collapsing memberships are not offered to compatible subject roots | **Resolved 2026-07-27**; oracle matrix and trace retained |
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

### TNK-006 — `top` on a non-application strategy is rejected — RESOLVED

- **Severity:** Medium
- **Classification:** Compatibility rejection
- **Confidence:** Resolved by reference-source inspection and direct oracle matrices
- **Primary area:** strategy surface recovery and resolution
- **Implementation touchpoints:** `tnk-frontend/src/strategy.rs`, `tnk-session/src/lib.rs`
- **Retained fixture:** `conformance/audit/A3k-top-recovery.maude`

#### Historical behavior

Maude treats `top` on a strategy for which the modifier has no meaning as recoverable misuse: it warns, drops the modifier, and executes the inner strategy. tnk rejected the whole expression with:

```text
error: top(…) of a non-rule strategy is a follow-on
```

The minimal `top(idle)` probe therefore produced one zero-rewrite `idle` solution on Maude and an error on tnk.

#### Source and boundary findings

The reference parser handles `MAKE_TOP` in `Mixfix/mixfixParser.cc`: it dynamically casts the already-built child to `ApplicationStrategy`. A direct rule application accepts `setTop()`; every other strategy class emits a warning and is returned unchanged. This happens before named strategy-call expansion, so `top(call)` means `call`, not “expand the call and apply its body only at the subject root.”

The broader differential matrix separated three cases:

- `top(r)` around a direct rule application remains operative: `r : a => b` cannot rewrite below `f`, so `f(a)` has no solution;
- `top(via-rule)` around a named zero-argument strategy is discarded before expansion: the call body `r` rewrites below `f`, yielding `f(b)` in one rewrite;
- `top(idle)` is echoed and executed as `idle`, yielding `f(a)` with zero rewrites.

tnk's surface tree has both explicit `Call` nodes and unresolved bare `Apply` nodes whose rule-vs-call meaning is determined from the loaded module. Merely accepting every `Top(Apply)` would therefore preserve `top` incorrectly on zero-argument named calls.

#### Resolution

`discard_inapplicable_top` recursively normalizes the owned command AST before both command echo and execution. It preserves the modifier only for `all` or an `Apply` whose label resolves to at least one rule; otherwise it replaces the wrapper with its child. The resolver also retains a defensive non-rule fallback for direct library callers that bypass session normalization.

#### Verification

`A3k-top-recovery.maude` retains all three distinctions against Maude 3.5.1. The focused post-fix diff is empty: direct `top(r)` has no solution, the named call yields `f(b)` with one rewrite, and ignored `top(idle)` yields `f(a)` with zero rewrites. Warning text remains intentionally outside the normalized differential contract.

---
### TNK-007 — Exact `decFloat(_, 0)` fails beyond a machine-sized denominator — RESOLVED

- **Severity:** Medium
- **Classification:** Bug; bounded wrong numeric behavior
- **Confidence:** Resolved by source inspection and a finite-range boundary matrix
- **Primary area:** float conversion built-in
- **Implementation touchpoint:** `tnk-core/src/builtin.rs`, `dec_float_parts`
- **Retained fixture:** `conformance/audit/A2k-decfloat-exact.maude`

#### Historical behavior

`decFloat(f, 0)` requests the exact decimal decomposition of a binary float. The original direct probe used the least positive subnormal:

```maude
red in CONVERSION : decFloat(4.9406564584124654e-324, 0) .
```

Maude returned a 783-byte exact `DecFloat` result. tnk left the application unreduced.

#### Source and boundary findings

The first description was too narrow: the failure was not specific to extreme subnormals. `dec_float_parts` obtained the exact arbitrary-precision rational, then converted its canonical power-of-two denominator to `u64` merely to call `trailing_zeros`. It therefore returned `None` whenever the reduced denominator was $2^k$ with $k > 63$. Ordinary finite values such as `0.00001` and `1.0e-20` crossed the same boundary; `0.1` ($k = 55$) did not.

The exact conversion needs the exponent `k`, not a machine representation of the integer $2^k$. For a normal IEEE-754 value, `k` follows from the encoded exponent and the trailing zeros of the 53-bit significand. For a subnormal, the fraction is scaled by $2^{-1074}$ and the same trailing-zero cancellation yields the canonical denominator exponent. The existing arbitrary-precision numerator then gives decimal digits `num * 5^k` and decimal exponent `digits.len() - k`.

This derivation covers every nonzero finite `f64`, including the least normal and least subnormal values, without allocating the unnecessary big denominator. Zero retains its dedicated result. Non-finite values still decline the built-in as before, and positive precision continues through the existing scientific-format rounding path.

#### Resolution

`exact_float_denominator_exponent` derives `k` directly from the IEEE-754 encoding. The precision-zero path no longer calls `to_u64()` on the denominator; it uses the derived exponent with the existing arbitrary-precision numerator and power-of-five calculation.

#### Verification

`A2k-decfloat-exact.maude` compares `0.1`, `0.00001`, `±1.0e-20`, the least normal, and the least subnormal at precision zero, plus a positive-precision least-subnormal control. All exact sign/digit/exponent triples and rewrite counts match Maude 3.5.1; the positive-precision control confirms that rounding stayed on the prior path.

---
### TNK-008 — Incomparable membership targets choose a different sort — RESOLVED

- **Severity:** Medium
- **Classification:** Bug; wrong sort in a nonconfluent specification
- **Confidence:** Resolved by reference-source inspection and order-isolating oracle matrices
- **Primary area:** membership constraint ordering
- **Implementation touchpoints:** `tnk-core/src/engine.rs`, `tnk-core/src/sort.rs`
- **Retained fixture:** `conformance/audit/B3b-membership-order.maude`

#### Historical behavior

With two applicable memberships lowering a kind term to incomparable `B` and `D`, Maude performed one membership application and reported `D`; tnk reported `B`. The specification is intentionally contradictory/nonconfluent, but the selected sort is still observable.

#### Source and boundary findings

The earlier “partial order plus declaration fallback” model was wrong. Maude's `Core/sortConstraintTable.cc:58-68` sorts every constraint by descending `Sort::index()`—“largest index (smallest sort) first.” Sort indices are unique within a connected component, so they provide a deterministic total order even for incomparable targets. Membership declaration order is not the tiebreak.

tnk already exposed the corresponding DFS/topological per-component index as `SortTable::component_index`, but its constraint comparator used subsort reachability for comparable pairs and raw global `SortId` for incomparable pairs. Raw `SortId` reflects unrelated registration/allocation order and can disagree with Maude's component-local index.

The confirmation matrix isolated the rules:

- reversing the two incomparable membership declarations does not change Maude's selected `D`;
- swapping the independent `X < A B` and `Y < A D` declaration lines changes their component indices and changes Maude's selected incomparable target to `B`;
- when `B < D`, the genuinely smaller target `B` is selected first and the reduction still takes one membership rewrite.

This is separate from kind-name ordering and does not claim confluence for contradictory specifications.

#### Resolution

The membership table now sorts by descending `component_index`, exactly matching the reference comparator. Rust's stable sort retains source order only when target sorts are identical; distinct component sorts have distinct indices.

#### Verification

`B3b-membership-order.maude` retains both incomparable membership declaration orders, the subsort-edge-order variant, and the comparable control. Each command has an empty Maude 3.5.1 diff: the first two cases report `D`, the edge-order variant and comparable control report `B`, and every case performs one rewrite.

---
### TNK-009 — Automatic BOOL imports use the wrong mode — RESOLVED

- **Severity:** Medium
- **Classification:** Behavioral divergence; wrong source/reflected module value
- **Confidence:** Resolved by reference-source inspection and module-kind/mode matrices
- **Primary area:** standing-prelude automatic import injection
- **Implementation touchpoint:** `tnk-session/src/lib.rs`
- **Retained fixture:** `conformance/audit/C6d-implicit-bool-mode.maude`

#### Historical behavior

The issue was first observed while reflecting a strategy module: `upModule`, `upStratDecls`, and `upSds` all computed, but Maude's automatic import was:

```text
including 'BOOL .
```

while tnk emitted:

```text
protecting 'BOOL .
```

The strategy declarations and definitions otherwise matched.

#### Source and boundary findings

The initial reflection-specific diagnosis was too narrow. `upModule` was faithfully exposing a wrong surface import that `Session::enter_module` injected into every entered module while `set include BOOL on` was active. The injected AST node used `ImportMode::Protecting`; Maude's `SyntacticPreModule::finishModule` obtains its automatic imports from the owner and processes the BOOL entry as `INCLUDING`.

The same mismatch therefore affected functional, system, strategy, and object module source before reflection. It was not a loss inside `upModule` or strategy-field translation.

Automatic-import ordering also matters. With automatic BOOL enabled, the generated `including BOOL` is inserted before an explicit `protecting BOOL`; source `upImports` retains both entries in that order. With automatic imports disabled, no generated import appears and an explicit `protecting BOOL` remains protecting.

#### Resolution

The session now injects `ImportMode::Including`. No meta/reflection special case was added; source and flat reflection inherit the corrected module representation.

#### Verification

`C6d-implicit-bool-mode.maude` covers functional, system, and strategy modules; `upImports` and source-form `upModule`; an explicit BOOL import while automatic inclusion is on; `set include BOOL off`; and an explicit protecting import while automatic inclusion is off. Automatic-only cases report `including`; automatic plus explicit reports `including` followed by `protecting`; the no-import case is empty; and the explicit-off case reports `protecting`, all with empty Maude 3.5.1 diffs. The retained TNK-005 `A5g` fixture separately pins unchanged strategy declarations and definitions.

---
### TNK-010 — Local meta-interpreter fixtures miss the retained timeout gate — RESOLVED

- **Severity:** Medium
- **Classification:** Robustness/performance
- **Confidence:** Resolved by targeted profiling and the unchanged retained gate
- **Primary area:** repeated Earley chart dedup in nested reflected-module parsing
- **Relevant fixtures:** `I19-russian-dolls-nonflat`, `I20-russian-dolls-nonflat2`
- **Implementation touchpoint:** `tnk-frontend/src/cfparser/earley.rs`

#### Historical gate evidence

The initial survey's combined subsystem run reported 110/112 because I19 and I20 hit the per-fixture 60-second timeout. I19 passed in isolation at 59.77 seconds. I20 timed out at 60.32 seconds and, with `TIMEOUT_SECS=180`, produced exact oracle output in 82.01 seconds. A later full run happened to pass both at the default limit, confirming timing sensitivity rather than removing the release-gate risk.

No semantic divergence was found; widening the gate would have changed the contract rather than fixed the observed regression.

#### Investigation findings

The I20 fixture was split at its five nesting-level commands without changing the module prefix. Before the repair, level 0 completed in 5.80 seconds while level 4 took 23.26 seconds. This localized the growth to repeated nested reflected-module work rather than one fixed startup cost.

A 10-second `/usr/bin/sample` capture of the level-4 process put `tnk_frontend::cfparser::earley::parse` at the dominant sampled stack. Its `HashSet<Item>` dedup path repeatedly reached `core::hash::BuildHasher::hash_one`/hashbrown table operations. Repeated `tnk_modules::meta::MetaDescent::module_pieces` and flattening were visible secondary work, but the profile did not point to the interpreter scheduler or rewrite loop as the primary regression.

An Earley `Item` is only `(prod: u32, dot: u16, origin: u32)`. The hash sets are never iteration-order authorities: insertion-ordered `Vec<Item>` sets drive recognizer work and forest extraction, while the hash tables answer membership only. SipHash therefore imposed substantial general-purpose hashing cost without providing a semantic ordering property.

#### Resolution

The chart uses a deterministic, allocation-free integer hasher specialized for the three compact indices. It mixes the derived `Hash` calls for `u32`/`u16` directly. The recognizer vectors, item identity, chart contents, parse ordering, and forest extraction are unchanged.

#### Verification

On the same workstation and release binary:

- the isolated level-4 probe dropped from 23.26 to 8.69 seconds;
- `tools/subsystems-scoreboard.sh -p I20` passed with exact output in 26.10 seconds;
- `tools/subsystems-scoreboard.sh -p I19` passed with exact output in 24.98 seconds.

Both retained fixtures are again comfortably below the unchanged 60-second per-fixture limit. No timeout or fixture contract was widened.

### TNK-011 — Collapsing memberships are indexed only at their syntactic top — RESOLVED

- **Severity:** High
- **Classification:** Bug; wrong value, least sort, and rewrite count
- **Confidence:** Confirmed by direct Maude 3.5.1 comparisons
- **Status:** Resolved 2026-07-27
- **Primary area:** sort-constraint indexing across ACU/AU/CUI collapse
- **Completed goal:** [`migration/tnk-011-collapse-memberships-goal.md`](migration/tnk-011-collapse-memberships-goal.md)

Before the repair, `push_membership` stored each executable `mb`/`cmb` only under
`lhs.top_symbol()`. A lhs such as `a * X` over `[comm id: z]` therefore worked on a rooted
`a * b` node but was never offered to the bare `a` node it matches with `X = z`. The omission
changed values as well as accounting: without the refinement `a : Special`, a sorted equation
such as `eq wrap(S:Special) = b` could not match.

The signature now owns every compiled `SortConstraint` once in a dense, declaration-ordered arena.
Direct-symbol and collapsing-result-kind indexes contain constraint IDs. Registration classifies
ACU/two-sided-AU identity and CUI identity/idempotent roots; least-sort computation allocation-free
merges the direct and collapse streams by descending component-local target-sort index and declaration
ID. Each constraint remains in exactly one stream, and the existing whole matcher rejects conservative
false-positive offers.

`conformance/audit/B3c-membership-collapse.maude` retains the direct Maude matrix: values, least sorts,
counts, unconditional and conditional collapse, recursive survivors, identity re-entry, noncollapse
controls, direct/collapse ordering, downstream sorted matching, and the complete membership trace with
`X --> z` and `Whole: a`. Focused frontend and REPL assertions consume the same fixture. The final gates
passed: the live oracle diff, all 458 workspace tests, and the 89/89 audit scoreboard.

The closure is deliberately limited to **ACU/two-sided-AU/CUI collapsing membership indexing**.
Associative one-sided `left id:`/`right id:` collapse remains a separate matcher gap.

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

`metaParseStrategy` and `metaPrettyPrintStrategy` remain inert. `upModule`, `upStratDecls`, and `upSds` should not be grouped into this gap: they compute, and TNK-009's automatic BOOL mode is now retained against the oracle.

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

### RISK-001 — Recursive parameterized strategy calls (closed)

The resolver no longer performs bounded inline expansion: it retains named calls in `RStrat::Call` and opens
matching, specialized definition bodies through the runtime `CallGenerator`. A direct 256-level decreasing
parameter recursion probe matches Maude 3.5.1 exactly (one `S: b` solution, one rewrite, then exhaustion).
This behavior has direct oracle evidence but no retained conformance fixture.

### RISK-002 — Unusual cross-kind overload grouping (closed)

The narrower same-domain-kind case also conforms. Direct probes covered identical domain sorts with different
range kinds and incomparable subsorts from one domain kind with different range kinds; contextual
disambiguation selected both declarations, and equations attached to each declaration reduced exactly like
Maude 3.5.1. The frontend keys symbol groups by name, domain kinds, and range kind, so different range kinds
cannot reach the kernel's same-group assertion. One adjacent output-only divergence remains for an
unconstrained ambiguous ill-sorted parse: tnk prints the computed error-sort suffix `.[B]` where Maude prints
the selected declaration suffix `.B`; contextual terms and reduction semantics agree.

### RISK-003 — Resolved as TNK-011

The exotic composition probes established the collapse-indexing bug closed by TNK-011. The repair covers
ACU/two-sided-AU/CUI candidate indexing while preserving the already-working iter/CUI/AC matcher composition.
The independently confirmed one-sided-AU matcher boundary remains outside that closure.

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

TNK-004, TNK-007, and TNK-008 are resolved with retained value, count, sort, numeric-boundary, and ordering coverage. No confirmed wrong-normal-form, exact-float, or membership-tiebreak defect remains from this survey; adjacent source-admitted risks remain separate.

### 8.3 Strategy composition group

TNK-005 and TNK-006 are resolved with compositional-import, ordering, transform, reflection, lifecycle, recovery, and generalized-`top` fixtures. TNK-001's operator-evaluation machinery is resolved independently; GAP-005/GAP-006 and RISK-001 remain separate proposals so strategy-language work does not silently become an unbounded rewrite.

### 8.4 Reflection group

TNK-009 is resolved at the automatic-import source: functional, system, and strategy source/flat reflection now preserve Maude's `including BOOL` mode. This remains independent from the still-inert strategy meta parse/pretty-print operations.

### 8.5 Performance group

TNK-010 is resolved without changing the product gate: targeted profiling removed SipHash from Earley item dedup, and I19/I20 now pass exact output in 24.98/26.10 seconds under the retained 60-second limit on the surveyed workstation.

### 8.6 Fixture policy

Before changing implementation, preserve every confirmed direct probe as a retained fixture with:

- accepted input;
- expected value and sort;
- rewrite/solution count where relevant;
- process exit/termination expectation;
- diagnostic normalization policy;
- timeout where relevant.

The TNK-001 probes are retained in `conformance/strat.maude`, TNK-002 in `A3a-rewrite-frozen`, TNK-003 in `A1b-opdecl-arity`, TNK-004 in `A3e-branch-stuck` plus `conformance/prelude-bool.maude`, TNK-005 in `A3f`–`A3j` plus `A5g`, TNK-006 in `A3k-top-recovery`, TNK-007 in `A2k-decfloat-exact`, TNK-008 in `B3b-membership-order`, and TNK-009 in `C6d-implicit-bool-mode`. TNK-010 remains pinned by subsystem fixtures I19/I20 and their unchanged 60-second harness gate.

## 9. Prototype/v0 decision view

This document does not set release priority. It exposes the decisions:

- **How much sibling declaration-recovery validation is required for v0?** The confirmed TNK-002 and TNK-003 panics are resolved; adjacent theory-attribute cases remain unverified risk candidates rather than confirmed defects.
- **Can v0 claim open-term functional reduction?** TNK-004 no longer blocks this claim for BranchSymbol: its symbolic-condition value, count, and sort contract is retained against the oracle.
- **Can v0 claim compositional strategy modules?** Yes for the retained import modes, ordering/conflict matrix, home parsing, sum/renaming/instantiation transforms, reflection, session invalidation, and generalized-`top` recovery covered by TNK-005/TNK-006.
- **Do the surveyed numeric/nonconfluent/reflection corners remain release limitations?** No: TNK-007–009 are resolved and retained; broader unverified candidates remain classified separately.
- **Is the 60-second I-S gate binding?** It remains binding and unchanged; TNK-010 restored I19/I20 beneath it.
- **Do ratified accepted diffs remain accepted for v0?** If yes, DIV-001–004 must appear in the user-facing limitations document rather than only in conformance internals.

The clean release statement is narrower than “bug-free”: every confirmed TNK-001–010 issue in this survey is resolved and retained, while accepted accounting/order differences, explicit deferred surfaces, diagnostics gaps, and unverified candidates remain documented.
