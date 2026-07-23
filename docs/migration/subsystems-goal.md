# Subsystems goal — symbolic engine, SMT & model checking, meta-interpreters (the `/goal` contract)

This document is the **contract for the next goal**: scope, phase ordering, objective gates, decision
points, and completion criteria for the three subsystems chosen after the correctness goal closed
(2026-07-05, `correctness-goal.md` — all five criteria hold; see the ledger header in `fable-audit.md`).
The goal driver re-reads THIS file each session. Feature background: `fable-audit.md` §2 and
`roadmap.md` phases G2–G5. Method: the same oracle-in-the-loop discipline that closed the correctness
goal — this document deliberately specifies *what must be true*, not *how to build it*; implementation
shape is the implementer's call within the recorded decisions.

**Goal statement.** Implement, in order: (S) the symbolic engine (order-sorted unification → variants →
narrowing), then (T) SMT integration and (M) the LTL model checker (independent of each other, either
order or interleaved), then (I) the session layer and meta-interpreters (local synchronous mode, then
the async/thread mode — the project's first deliberate behavioral divergence from the reference,
deliberately sequenced **last** so the byte-comparable baseline stays frozen while all
byte-comparable features land).

**Ordering rationale (recorded, do not relitigate):** S/T/M are engine-internal and validated through
the existing synchronous, oracle-diffable surfaces. Phase I contains the two baseline-disturbing
items (the session-extraction refactor of the command plumbing, and implementation-defined async
scheduling). Sequencing them last keeps every diff during S/T/M attributable, lets the
meta-interpreter protocol wire against real capabilities instead of stubs, and confines the
divergence question to one phase with its own containment machinery.

---

## 1. Metric and gates

### 1.1 Frozen invariants (every phase, every commit — regressions are failures)

- **F1** `tools/audit-scoreboard.sh` → `SCOREBOARD n/n PASS`, all pass (77/77 as of 2026-07-06 —
  the denominator grows per §1.2 of `correctness-goal.md` and may never shrink; 74 at goal start).
- **F2** `tools/legacy-sweep.sh` → `LEGACY 87/87 CLEAN` (accepted-diff recordings in
  `conformance/accepted-diffs/` compare byte-exact; drift fails).
- **F3** `cargo test --release` fully green.
- **F4** Stock `term-order.maude` / `machine-int.maude` / `linear.maude` load clean through the binary.

### 1.2 The new instrument

- **`conformance/subsystems/<ID>.maude`** — fixtures for this goal, run by
  **`tools/subsystems-scoreboard.sh`** (same `diffmaude.sh` harness and normalization; 60s/fixture;
  `-p PREFIX` selects one frozen sub-phase, e.g. `-p U`; prints `SUBSYSTEMS <n>/<m> PASS`, exit 0 iff
  n = m). ID prefixes: `U*` unification, `V*` variants, `N*` narrowing, `T*` SMT, `M*` model checker,
  `I*` meta-interpreters (local mode only — async mode is not oracle-diffable and gates via §1.3).
- **Per-phase seeding (each phase's step 0, committed before its first feature commit):** enumerate
  the fixture sources — the reference suite (`~/code/maude-lang/maude/tests/`: the directories gated
  on that subsystem per the audit's §3.8 tally), the Maude 3.5.1 manual's worked examples for the
  chapter, and fresh minimal probes — then **freeze that phase's manifest by appending it to §2 of
  this document in the same commit as the fixtures**. Every fixture is oracle-verified at authoring
  (shows the documented reference behavior) and expected to FAIL initially. A fixture may be added
  later (denominator grows; that is honesty, not regression) but never removed or weakened without a
  user decision recorded here. Reference-suite tests that depend on *excluded* features (external IO,
  process interpreters, LOOP-MODE interaction, diagnostics text) are listed per phase with a one-line
  reason — exclusions are enumerated, never silent.
- **Secondary indicator (report, don't gate):** the reference-suite clean-pass count
  (`fable-audit.md` §3.8 baseline: 8 of 231; ~100 gated on these subsystems).

### 1.3 The async-mode gate (phase I only)

Async mode is validated by **differential self-check**, not oracle diff: cargo tests drive identical
request scripts through local-synchronous mode (the oracle-anchored reference) and async mode under
the **deterministic test schedule** (replies injected only at rewrite-quantum boundaries, arrival
order) and assert identical reply sets and per-request counts. Timing/interleaving is
implementation-defined per the conformance-boundary statement in D12.

### 1.4 Completion criteria (all six; then the goal is done)

1. `tools/subsystems-scoreboard.sh` exits 0 over the frozen per-phase manifests.
2. Frozen invariants F1–F4 hold simultaneously with (1).
3. The async differential self-check suite is green.
4. `metaInterpreter.maude`, `smt.maude`, and `model-checker.maude` load through the binary and their
   documented entry points compute (no inert-op regressions on the surfaces this goal claims).
5. Decision records updated: **D12 written before phase-I code**; D6 and D7 carry binding
   resolutions (or recorded fallback switches) from their gate spikes.
6. This document's §5 status ledger carries a commit hash per completed phase item.

---

## 2. Phase manifests

Definition-of-done per item; frozen fixture lists are appended here by each phase's step 0.

### Phase S — symbolic engine (first; internal order S0→S1→S2→S3 is a dependency chain)

- **S0 — BDD spike (gate, before any S1 code).** Prototype the order-sorted-unification sort
  computation (`SortBdds` + AllSat) on `biodivine-lib-bdd` per D6. Deliverable: a spike report in
  `docs/migration/reports/` with measured numbers and a go/no-go; on no-go, record the fallback
  choice as a D6 amendment. No production code before the gate resolves.
- **S1 — order-sorted unification.** `unify` command + `metaUnify`/`metaDisjointUnify` compute
  reference-identical unifier sets **in reference order** (enumeration order is observable and is
  part of the pass criterion — the discipline that closed the AC matcher applies verbatim:
  close-to-reference port where order is load-bearing, unit tests on emitted *sequences*, a naive
  cross-check path where feasible). Constraints established here for the whole phase: **one central
  fresh-variable generator** (the `#n`/`%n`/`@n` families) before a second consumer exists; the
  **incompleteness flag** threaded through results from day one (its warning *text* remains phase-E,
  but the flag must flow unify→variant→narrow end-to-end).
- **S2 — variants.** `get variants`, `variant unify`, `variant match` + meta counterparts; folding
  variant narrowing (most-general + descendant eviction) reference-identical including variant
  numbering/order.
- **S3 — narrowing.** `vu-narrow`/`fvu-narrow` (v3 semantics only, per roadmap) with
  reference-identical solutions, order, and counts.

#### Phase-S manifest (frozen 2026-07-05; expanded to 63 fixtures on 2026-07-19 when three mixed reference fixtures were split at the S1/S2 boundary)

**U\* — unification (S1), 27 fixtures; 676 substantive commands; 27/27 PASS on 2026-07-19.**
Reference-suite lifts (verbatim except for the documented base/variant splits): `U01-unification`,
`U02-unification2`, `U03-unification3`, `U04-assoc-unification`, `U05-au-unification`,
`U06-au-irred-unification`, `U07-au-a-edge-cases`, `U08-cu-unification` (from `tests/Misc/`),
`U09-meta-unify`, `U10-legacy-meta-unify`, `U11-check-unifiers` (from `tests/Meta/`). `U05` and
`U08` now retain only their base `unify` commands; `U11` retains only its `metaUnify` checker. Their
variant halves are `V13`, `V14`, and `V12` respectively, so S1 has an executable gate without weakening
S2. Manual ch. 13 worked examples (where the printed manual disagrees with the live 3.5.1 oracle, the
oracle is ground truth): `U-ch13-01` … `U-ch13-15`. Fresh probe: `U-probe-01-maximal-sorts`
(incomparable maximal lower bounds → one unifier per maximal sort, in reference order). The
`U-ch13-07-iter-comm` `s_^k` input notation landed with S1.

**V\* — variants (S2), 21 fixtures; 289 substantive commands; 21/21 PASS on 2026-07-19.**
Reference-suite lifts: `V01-variant-unification`, `V02-variant-matching`,
`V03-filtered-variant-unification`, `V04-meseguer-finite-variant`, `V05-variant-narrowing`
(despite the name: `get variants`) from `tests/Misc/`; `V06-meta-get-variant`,
`V07-legacy-meta-get-variant`, `V08-meta-variant-unify`, `V09-meta-variant-unify2`,
`V10-legacy-meta-variant-unify`, `V11-meta-variant-match` from `tests/Meta/`; split reference halves:
`V12-check-variant-unifiers`, `V13-au-variant-unification`, `V14-cu-variant-unification`. Manual ch. 14:
`V-ch14-01` … `V-ch14-06`. Fresh probe: `V-probe-01-idem-variants`. The formerly inert V09
`metaVariantUnify` loop now terminates with reference-identical cached results.

**N\* — narrowing (S3), 15 completion fixtures + 1 post-close regression; 169 substantive primary
commands; live gate 16/16 PASS on 2026-07-21.**
Reference-suite lifts: `N01-narrow` (`vu-narrow`/`fvu-narrow`), `N02-narrow2` (`{fold}`/`{vfold}`)
from `tests/Misc/`; `N03-meta-narrow` (`metaNarrowingApply`/`metaNarrowingSearch`/
`metaNarrowingSearchPath` + legacy `metaNarrow`) from `tests/Meta/`. Manual ch. 15: `N-ch15-01` …
`N-ch15-11` (`N-ch15-07/08` include the oracle's deterministic `set verbose on` state/folding trace).
Fresh probe: `N-probe-01-vu-narrow-basic`; its unreachable fourth query is frozen with depth bound 3
(`No solution.`, 9 rewrites) rather than an expected timeout. All 168 primary commands also pass in
isolation. Legacy `metaNarrow` is served by the oracle-equivalent v3 result adapter; the retired
`metaNarrow2` remains an explicit non-goal. No fixture exclusions or accepted divergences.
Post-close `N-probe-02-multi-root-zero-step` guards the `=>*` zero-step solution from every disjunct;
it grew the live denominator without changing the frozen S3 completion contract.

**Enumerated exclusions (phase-S seeding; nothing silent).**
- `tests/Meta/metaInt*` (17 files) and `tests/Meta/russianDolls*` (non-`Proc` variants) —
  meta-interpreter surface: seeded at phase I as `I*` fixtures (local mode only, per §1.2).
- `tests/Meta/metaProc*` (17 files) and `russianDolls*Proc*` — OS-process interpreter backend:
  §6 non-goal (D5/D12 territory).
- `tests/Misc/smtTest` — phase T seeding.
- `tests/Misc/dekker` (and the model-checker examples) — phase M seeding.
- `tests/Misc/initialEqualityPredicate` — not gated on the symbolic engine: its gap was the `.=.`
  decompose semantics, found during this seeding, fixed, and landed as **audit** fixtures
  E1a/E1b/E2a (fable-audit.md §3.10; audit denominator 74 → 77).
- Manual examples skipped inside chapters are listed per-file in the fixtures' headers or were
  prose-only (no runnable command/output pair); ch. 13 §13.4.6 verbose diagnostics and the
  381-unifier dump are representative examples.

### Phase T — SMT (complete 2026-07-23; core independent of M; T6 uses completed S2)

#### Binding six-step execution sequence

For one serial workstream, stay on the earliest incomplete step; a later step never justifies weakening
an earlier gate. T6 is technically parallel-safe, but the recorded serial order remains:

1. **Freeze the Phase-T contract (T0a — DONE 2026-07-21).** Split and oracle-run every
   in-scope non-debug `smtTest`/manual command, enumerate the debugger exclusion, and freeze the
   manifest before any production SMT code.
2. **Install the SMT language substrate (T1 — DONE 2026-07-21).** All 25 hooks, exact SMT number
   leaves, per-module metadata, and the pinned `smt.maude` are live.
3. **Implement and close `check` (T2–T3 — DONE 2026-07-21).** The pure `SmtEngine` seam, Null
   backend, feature-gated z3 translator/backend, and every theory/error fixture pass.
4. **Implement and close `smt-search` (T4 — DONE 2026-07-23).** The dedicated source-ordered rule
   view, root-only/no-reduction state machine, constraints, exact output, restrictions, and
   `continue` pass.
5. **Finish the reflected SMT surface (T5 — DONE 2026-07-23).** Cached `metaCheck` and
   `metaSmtSearch`, counters, bounds, failure, and continuation behavior pass.
6. **Deliver native variant satisfiability (T6 — DONE 2026-07-23).** T6a–T6g landed: pinned old
   Linux oracle, independent contract, eligibility/constructor/finite-sort/formula core, compatible
   `VAR-SAT-TOOL` facade, and both differential lanes.

#### Phase-T manifest (frozen 2026-07-21)

**T01–T10 — 10 fixtures; 118 substantive commands; 10/10 Yices2 oracle/self-diff PASS.**
This frozen oracle contract remains the T1–T5 byte boundary; the production closure adds T11 below.

- `T01-check-boolean` (12), `T02-check-integer` (19), `T03-check-real` (19), and
  `T04-check-real-integer` (11): the four solver theories from `tests/Misc/smtTest.maude`.
- `T05-smt-search` (27): every non-debug object search, continuation, invalid-bound, and
  restriction case, including the ordinary setup search preceding the second debugger block.
- `T06-meta-check` (8) and `T07-meta-smt-search` (10): every non-debug reflected SMT command;
  both are mandatory T5 scope.
- `T08-manual-ch16` (4): every executable `check` example in manual §16.5.
- `T09-bignum-rational` (6): arbitrary-precision integer coefficients, exact rational
  canonicalization/signs, and integer-to-real coercion.
- `T10-fresh-names` (2): two-step source-base-name allocation (`#1-X`, `#2-Y`), numbering,
  ordering, and accumulated constraints.
- `T11-variant-satisfiability` (27): native FVP/OS-compact constructor satisfiability and validity,
  including eligibility, finite/empty domains, AC/C/CUI/ACU/AU constructors, variants, and overloads.
  Its expected file records both the native contract and the pinned Maude-2.7 prototype results.

`T01`–`T07` contain all **106** non-debug command occurrences in the reference `smtTest`; the sole
F4-owned exclusion is exactly eight debugger commands at source lines 230–234 and 237–239
(`debug smt-search`, `debug cont`, four `step`s, and two `resume`s). The four manual commands and
eight independent number/fresh probes bring the denominator to 118. Every fixture was run through
the Yices2 rebuild; `TNK_BIN=~/.local/bin/maude tools/subsystems-scoreboard.sh -p T` reported 10/10.

**Cursor: Phase T complete (2026-07-23); M0 fixture seeding is complete; next serial cursor is M1.**
The Phase-T record remains frozen in `remaining-plans/04-smt.md` §§4–8.

- **T0a–T5 closed:** the optional z3 0.20.2 lane passes T01–T10—10 fixtures / 118 byte-exact
  commands—covering all non-debug object `check`/`smt-search`, `metaCheck`, and `metaSmtSearch`
  semantics plus manual, number, and fresh-name probes. The eight debugger commands remain the sole
  explicit F4 exclusion. The default build is still pure Rust, parses the same surface, and degrades
  to `undecided`/no solutions without linking z3.
- **T6 closed:** production is a native Rust FVP/OS-compact constructor-variant decision procedure
  using S2, exposed through the source-compatible `VAR-SAT-TOOL` facade. The untouched official
  archive is checksum-gated external reference material and passes its 27-result lane; the native
  lane passes 27/27. The checked-in contract explicitly corrects three prototype defects
  (membership eligibility and existential/universal empty-domain semantics) and accepts only the
  recorded reflective rewrite-count/old-wrapper boundary. No prototype source is copied; T6 links
  neither z3 nor model checking.
- **Phase gate:** `TNK_BIN=target/smt-z3/release/tnk-repl
  tools/subsystems-scoreboard.sh -p T` reports **11/11 PASS**. The retained audit, legacy, U, V, and
  N gates remain green.

### Phase M — model checker (independent; selected after T for serial work, parallel-safe)

#### Phase-M manifest (frozen 2026-07-23)

**M01–M10 — 10 fixtures; 49 commands; Maude-3.5.1 oracle/self-diff 10/10 PASS.**

- `M01-toggle` (3): smallest true, Qid-labelled lead-in/cycle, and nil-lead-in results.
- `M02-ltl-operators` (17): all primitive/derived LTL connectives, unlabeled arcs, and
  `LTL-SIMPLIFIER`.
- `M03-deadlock-multi-rule` (2): synthesized deadlock self-loop and a two-rules/one-target arc
  with a stable shared label.
- `M04-manual-mutex` (7), `M05-manual-rrobin` (3), `M06-manual-ltl-plus` (1), and
  `M10-sat-taut` (7): every terminating executable command family in manual Chapter 12,
  including exact counterexample/witness/model/false/prime-implicant output.
- `M07-reference-dekker` (3), `M08-reference-dining-philosophers5` (3), and
  `M09-reference-dining-philosophers6` (3): exact remaining model-checker-gated reference
  sources. M05 simultaneously covers the fourth source, `ObjectOriented/rrobin`.

The reference-suite denominator is therefore complete: `Misc/dekker` and
`ObjectOriented/{rrobin,dining-philosophers5,dining-philosophers6}`; no suite file is excluded.
The sole manual exclusion is `MODEL-CHECK-BAD-EX`, whose purpose is to demonstrate nontermination
on an infinite reachable-state set and which cannot meet the 60-second harness bound.

M03 deliberately does not freeze which of two *differently-labelled* rules names a shared arc:
Maude's pointer-ordered `set<Rule*>` alternated the representative across process runs (two
mismatches in a 12-pair oracle self-diff). The stable fixture uses duplicate rules with one label;
tnk determinizes the otherwise-unstable case by lowest source rule id. Every other label, lasso,
result term/sort, and rewrite count remains byte-exact.

**M0 is complete; M1 is next.** No production model-checker code landed with the manifest.
The current binary accepts all 49 commands but leaves `SatSolverSymbol`/`ModelCheckerSymbol`
applications unreduced, so `tools/subsystems-scoreboard.sh -p M` is intentionally 0/10.
M1–M7 must port the exact Gastin–Oddoux pipeline + nested DFS, share `Search`'s successor core,
bind both hooks, and close all 10 fixtures. Detailed cursor: `remaining-plans/05-model-checking.md`.

### Phase I — sessions & meta-interpreters (last; internal order I0→I1→I2→I3→I4)

- **I0 — decision record D12, before code.** Must state: async is *coordination only* — evaluation is
  blocking CPU work on thread-confined engines (engines are created on their thread and never move;
  their non-`Send` internals are a deliberate compile-time guarantee, not a defect); the core
  session API is **runtime-agnostic** (plain threads + channels; any async-executor integration is a
  thin adapter, never a `tnk-core`/session dependency); the **conformance boundary**: message
  protocols, per-request results, and counts are conformance targets — inter-message scheduling is
  implementation-defined; the sole recorded trigger for a future *process* backend (a sandboxing
  requirement: memory/crash isolation or per-child resource limits), which would arrive as an
  embedding-host service per D5, never engine code.
- **I1 — session extraction.** A library `Session` (module/view databases, dependency invalidation,
  command evaluation, include/load semantics — everything currently in the REPL that is not
  line-editing or terminal concerns) with the REPL rebuilt as its thinnest consumer. Gate: F1–F4
  green with **zero fixture drift** — this refactor must be observationally invisible.
- **I2 — local synchronous meta-interpreters.** The interpreter-manager external object on the
  existing message seam (the standard-stream precedent); children are Sessions; requests/replies
  cross as serialized meta-terms. `metaInterpreter.maude` loads; the reference's *local-mode*
  examples are oracle-diffable and become `I*` fixtures. Protocol verbs for capabilities this goal
  ships (unify/variants/SMT) are live; anything beyond stays declared-but-inert, never misfiring.
- **I3 — cancellation at safe points.** A cooperative cancellation token checked at the engine's
  amortized safe points (reduce loop head, search loop, matcher enumeration, condition evaluation).
  Shared infrastructure with the future Ctrl-C item. Gate: the D2-era throughput benchmarks
  (`examples/peano`, fib) within noise (bar: ≤ 2% on reduce throughput).
- **I4 — async/thread mode.** The `newProcess`-flag semantics on the thread backend with the
  documented deltas from D12 (no memory/abort isolation; cooperative abandonment; panic containment
  — pin the unwinding-panic build setting as part of this item). Deterministic test schedule
  mandatory (§1.3); the differential self-check suite is this item's definition of done.

---

## 3. Decision points

- **D12** (I0) — content checklist above; written and committed before phase-I implementation.
- **D6** bound at S0. **D7 is bound:** refreshed gate run 2026-07-21
  (`spikes/smt-spike/`, `reports/T0-smt-spike.md`) uses `z3` 0.20.2 / `z3-sys` 0.11 and proved
  incremental push/pop equivalent to a fresh solver across 894 randomized state-tree nodes; all
  fixture-shaped Boolean/integer/real/coercion probes are green against the Yices2 oracle. The
  production placement and feature-lane decisions are recorded in `remaining-plans/04-smt.md` §8.
- RATIFIED 2026-07-05: D9/D10/D11, D12, and the criterion-3 amendment
  (`conformance/accepted-diffs/README.md`).

## 4. Working rules (carried over; deltas in bold)

- Fixtures first: every feature lands with its now-passing fixture(s); scoreboards (§1.1 + §1.2) +
  `cargo test --release` before every commit; never pin our own output as expected — the live oracle
  is ground truth, and **enumeration/solution order is part of the expected output** wherever the
  reference exhibits a deterministic order.
- **Frozen-baseline rule:** F1–F4 stay green at every commit of every phase; a fix that breaks them
  is wrong regardless of what it enables.
- **Cross-check discipline** for order-observable enumerators (unifiers, variants, narrowing steps):
  sequence-level unit tests + a slow reference path kept live for differential testing until the
  suite is byte-conformant (the Diophantine-port pattern).
- **Build hygiene:** z3 (and any BDD native fallback) behind cargo features; the default feature set
  builds pure-Rust and passes F1–F4 with the new subsystems' pure-Rust parts active.
- Subagent pattern as before: mechanical breadth (fixture authoring, reference-source reading,
  line-for-line ports against a written spec) fans out; design decisions and final oracle
  verification stay in the main loop.
- Ledger: completed items get a commit hash in §5; newly discovered deviations in *shipped* surfaces
  go to `fable-audit.md` as new findings with fixtures (denominator grows).
- No implementation-time estimates anywhere (project rule).

## 5. Status ledger (append commit hashes as items complete)

- [x] S0 BDD spike + D6 resolution — ee77559 (GO; report `reports/S0-bdd-spike.md`)
- [x] S1 unification — working tree 2026-07-19 (`tools/subsystems-scoreboard.sh -p U`: 27/27;
  676 commands; commit hash to append when committed)
- [x] S2 variants — working tree 2026-07-19 (`tools/subsystems-scoreboard.sh -p V`: 21/21;
  289 commands; commit hash to append when committed)
- [x] S3 narrowing — working tree 2026-07-21 (`tools/subsystems-scoreboard.sh -p N`: 16/16,
  including one post-close regression; `tools/diffmaude-command.py`: 169/169 isolated commands;
  commit hash to append when committed)
- [x] T0 z3/Yices2 spike + D7 resolution — refreshed working tree 2026-07-21 (`z3` 0.20.2;
  894-node incremental≡fresh gate; `reports/T0-smt-spike.md`)
- [x] T0a SMT fixture manifest — working tree 2026-07-21 (10 fixtures, 118 commands;
  Yices2 oracle/self-diff 10/10; eight debugger commands are the sole F4 exclusion; commit hash
  to append when committed)
- [x] T1 SMT language substrate — working tree 2026-07-21 (25 operators, exact SMT number leaves,
  per-signature metadata, byte-identical shipped `smt.maude`; default audit 77/77 and cargo 399/399)
- [x] T2–T3 SMT backend + object `check` — working tree 2026-07-21 (default Null degradation;
  optional z3 0.20.2; 6 fixtures / 71 checks byte-exact, plus BAD_DAG probe)
- [x] T4–T5 SMT search and mandatory meta surfaces — working tree 2026-07-23 (T05–T07:
  3/3 fixtures, 45 byte-exact object/meta commands; default Null degradation retained)
- [x] T6 variant-satisfiability library — working tree 2026-07-23 (native and external-oracle lanes
  27/27 each; complete Phase-T scoreboard 11/11; three prototype corrections recorded in T11)
- [x] M0 model-checker fixture manifest — working tree 2026-07-23 (10 fixtures / 49 commands;
  oracle self-diff 10/10, inert-hook production baseline 0/10; no production code)
- [ ] M1 LogicFormula DAG + temporal descent —
- [ ] M2 local LTL BDD facade —
- [ ] M3 VWAA → GBA → Büchi pipeline —
- [ ] M4 nested DFS + synthetic System gate —
- [ ] M5 shared StateGraph + hooks + toggle slice —
- [ ] M6 complete modelCheck fixture closure —
- [ ] M7 satSolve/tautCheck fixture closure —
- [x] I0 D12 recorded — 2026-07-05 (`03-open-decisions.md`)
- [ ] I1 session extraction —
- [ ] I2 local meta-interpreters —
- [ ] I3 cancellation —
- [ ] I4 async mode + differential suite —

## 6. Non-goals (explicit; do not drift into these)

External file/socket/process IO and OS-process meta-interpreter backends (D5/D12 territory — harness
era); the fully-featured interactive harness itself and Full Maude or its replacement (dedicated
later pass, per user decision 2026-07-05); LOOP-MODE interaction (harness era); the diagnostics/warning
surface and the interactive tool surface (`show`/`set print`/debugger —
roadmap E/F) except where a shipped subsystem's own output requires a specific line; the
matchrew/exploration-schedule odometer (recorded accepted divergence, revisit with strategy
reflection); performance work beyond the stated gates.
