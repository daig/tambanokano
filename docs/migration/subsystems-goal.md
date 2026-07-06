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

- **F1** `tools/audit-scoreboard.sh` → `SCOREBOARD 74/74 PASS` (denominator may grow per §1.2 of
  `correctness-goal.md`; it may never shrink).
- **F2** `tools/legacy-sweep.sh` → `LEGACY 87/87 CLEAN` (accepted-diff recordings in
  `conformance/accepted-diffs/` compare byte-exact; drift fails).
- **F3** `cargo test --release` fully green.
- **F4** Stock `term-order.maude` / `machine-int.maude` / `linear.maude` load clean through the binary.

### 1.2 The new instrument

- **`conformance/subsystems/<ID>.maude`** — fixtures for this goal, run by
  **`tools/subsystems-scoreboard.sh`** (same `diffmaude.sh` harness, same normalization, 60s/fixture,
  prints `SUBSYSTEMS <n>/<m> PASS`, exit 0 iff n = m). ID prefixes: `U*` unification, `V*` variants,
  `N*` narrowing, `T*` SMT, `M*` model checker, `I*` meta-interpreters (local mode only — async mode
  is not oracle-diffable and gates via §1.3).
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

### Phase T — SMT (after S; soft dependency: variant satisfiability layers on S2)

- `check` and `smt-search` against the `z3` crate behind the D7 `SmtEngine` trait,
  **feature-gated**: the default build stays pure-Rust and green without z3 installed (CI implication
  recorded in the working rules). Variant satisfiability lands as a `.maude` library over S2.
  `smt.maude` loads; its `SMT_Symbol` hooks compute. Fixtures: reference-suite SMT directory +
  manual examples; byte-exact including model/`sat`/`unsat` rendering.

### Phase M — model checker (independent of S and T; may interleave with T)

- LTL→Büchi (Gastin–Oddoux per roadmap) + nested-DFS emptiness with **counterexample output
  byte-exact** to the reference (paths are deterministic; they are the pass criterion, not just the
  verdict). `SatSolverSymbol`/`ModelCheckerSymbol` id-hooks bound so `model-checker.maude` loads and
  computes. Reuses the existing state-graph machinery; the search/state-graph GC discipline note in
  the roadmap risk register applies.

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
- **D6** binds at S0 (spike gate); **D7** binds at phase T start (confirm z3 incremental push/pop
  matches `smt-search` pruning before the trait is frozen).
- Awaiting user ratification, carried from the correctness goal: D9/D10/D11 and the criterion-3
  amendment (`conformance/accepted-diffs/README.md`). None block this goal.

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

- [ ] S0 BDD spike + D6 resolution —
- [ ] S1 unification —
- [ ] S2 variants —
- [ ] S3 narrowing —
- [ ] T SMT —
- [ ] M model checker —
- [ ] I0 D12 recorded —
- [ ] I1 session extraction —
- [ ] I2 local meta-interpreters —
- [ ] I3 cancellation —
- [ ] I4 async mode + differential suite —

## 6. Non-goals (explicit; do not drift into these)

External file/socket/process IO and OS-process meta-interpreter backends (D5/D12 territory — harness
era); the fully-featured interactive harness itself and Full Maude or its replacement (dedicated
later pass, per user decision 2026-07-05); LOOP-MODE/LEXICAL real implementations (harness era);
the diagnostics/warning surface and the interactive tool surface (`show`/`set print`/debugger —
roadmap E/F) except where a shipped subsystem's own output requires a specific line; the
matchrew/exploration-schedule odometer (recorded accepted divergence, revisit with strategy
reflection); performance work beyond the stated gates.
