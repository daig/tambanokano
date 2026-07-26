# Decision Record — foundational choices (D1–D8) + correctness/subsystem decisions (D9–D12)

The load-bearing tech decisions, ordered by blast radius. **D1–D4 and D8 are in force and validated** by the
built engine (Phase 0/1 — the `Resolution`/`Amendment` notes record how); **D5 (IO/`mio`), D6 (BDD), D7 (SMT)
are forward decisions** that bind when their Phase-2/3 consumers land (`roadmap.md`). Each carries its
rationale + the phase it was/will be revisited. See `01-architecture-map.md` §4 for how they thread through
the layers.

---

## D1 — Engine model: instance-based, not global singleton
**Decision.** The runtime universe (term arena + GC + symbol/sort/module tables + interpreter state) is
an instantiable `Engine` value, **not** a global singleton. No global mutable statics (unlike C++ Maude,
whose GC and `Interpreter` are global).
- Descent functions (`metaReduce` etc.) run as an **in-heap sub-context of the same `Engine`** (meta-module
  built in the same arena, GC-protected) — preserving Maude's "don't copy big modules" efficiency.
- True meta-interpreters (ch. 19) are **separate `Engine` instances** communicating by term translation
  (which up/down already does).
- `DagId`/`SymbolId` are **engine-relative newtypes**, never mixed across engines (enforced by construction).

**Why.** Retrofitting instances onto a global design later is a near-total rewrite (A1). Cost now is just
threading `&mut Engine`, which is idiomatic Rust. Enables parallelism (one engine per thread) and clean tests.
**Impact.** Every API is a method on `&mut Engine`. **Revisit:** validated in **Phase 0**.

## D2 — GC flavor: non-moving mark-sweep with stable ids
**Decision.** Tracing GC over an index-arena, specifically **non-moving mark-and-(lazy-)sweep** with an
explicit root set (RAII `RootGuard`). `DagId`s are **stable for a node's lifetime**. Generational/copying GC
is deferred as a possible later optimization; `Rc`+cycle-collection is rejected.

**Why.** Faithful to Maude (its speed rests on bump-allocation + non-moving lazy sweep + tuned slop); stable
ids are required by hash-consing, memo tables, and the search/state graphs that key on node identity. Moving
GC would invalidate raw indices and force a relocation/indirection layer.
**Impact.** Arena = `Vec`-backed slots + free list + mark bitset; roots registered/unregistered via guards.
**Revisit:** **Phase 0** — this is the central **go/no-go benchmark** (must approach C++ throughput).

**Amendment (Phase-0 review, 2026-06-20).** The review found that "stable ids + non-moving slot reuse"
is sound only if the root discipline is airtight, yet (a) no `RootGuard` exists — `gc` trusts a hand-passed
root list, and (b) slot reuse is *silently* undetectable (a recycled `DagId` reads a valid-but-wrong node).
Decision: at **Phase-1 opening**, implement the `RootGuard`/root registry **and** add a slot generation tag
+ per-arena engine id, checked under `cfg(debug_assertions)` (turning silent reuse / cross-engine misuse
into immediate panics in dev/test at ~zero release cost). The **release-mode** generational default stays
open, to be decided by benchmarking an 8-byte handle vs `examples/peano.rs`. Co-design this with the
iterative reducer (its explicit work-stack *is* the discoverable root set for safe-point GC).

**Resolution (Phase-1 Stage A2, 2026-06-20; commits `7f8df37`, `f8b1c0d`).** Implemented as amended:
the iterative reducer (A1) supplies the discoverable work-stack; `RootGuard`/root registry and the
debug-gated slot-generation + per-arena-id checks landed in A2, plus opt-in safe-point GC during `reduce`.
**Release default decided by benchmark: keep the bare 4-byte `u32` handle (checks compiled out in release).**
Forcing the full generational machinery into an *optimized* build (`-C debug-assertions=on`, a 12-byte
`raw+gen+arena` handle + checks — a conservative upper bound on the amendment's 8-byte `raw+gen`) cost
**~28% reduce throughput** (6.75 → 4.84 M rewrites/s) and **~60% GC-mark throughput** (280 → 111 M nodes/s)
on `examples/peano`, far above the ~5% bar for flipping the go/no-go-critical throughput metric. The
debug-gated checks remain the dev/test safety net; equality/ordering/hashing are raw-only in *both* profiles
so behavior is identical. A release-checked 8-byte handle (behind a `gen-checks` cargo feature, for code that
enables `gc_interval` in release) is **deferred** until release-mode safe-point GC is actually used; the
`set_gc_interval` rooting contract is documented in the meantime.

## D3 — Dispatch boundary: enums for the closed hot set, `dyn` at open seams
**Decision.** `Symbol`/`DagNode`/`Term` and the fixed theory set (Free/ACU/AU/CUI/S/NA/Var/BuiltIn) are
**enums with composed data** (sort/equation/rule/strategy/memo tables as fields), giving monomorphized hot
paths. `Box<dyn …>` is used only where heterogeneity is genuine: **residual subproblem trees**
(`Subproblem`) and the **open external-object manager** seam. `LhsAutomaton`/`RhsAutomaton`/`ConditionFragment`/
`StrategyExpression` are enums (closed) unless a concrete case forces otherwise.

**Why.** Replaces C++ multiple-inheritance virtual hierarchies; keeps the per-rewrite dispatch off vtables.
**Impact.** No trait objects on the hottest data structures. **Revisit:** pin each trait/enum in **Phase 0**.

## D4 — Bignum: `malachite`, wrapped
**Decision.** Use **`malachite`** (pure Rust) for unbounded `Int`/`Nat`/`Rat`, behind a thin `tnk-core::num`
wrapper (`Int`/`Nat`/`Rat` newtypes). `Float` stays IEEE `f64`. `rug` (GMP) is a benchmarked escape hatch;
`num-bigint` the fallback if a strictly permissive license is required.

**Why.** Pure Rust → trivial builds/CI/cross-compilation; perf within a small factor of GMP; its
`Natural`/`Integer`/`Rational` mirror NAT/INT/RAT. Maude's hot loop is rewriting+GC, not bignum arithmetic.
**Impact.** Bignum type appears in the `DagNode` `S`/number variants → wrapper defined in Phase 0.
**Revisit:** **Phase 1** (confirm with a number-heavy benchmark; verify malachite's license suits us).

## D5 — External IO: **host-owned IO via embedding** (supersedes the in-engine `mio` reactor)
**Decision (revised 2026-06-30).** Do **not** build an in-engine reactor or the FILE/SOCKET/PROCESS
managers. Keep the engine a pure, instance-based rewriting kernel and let a **host program embed it and own
all IO** — the host runs the event loop and does file/socket/process/terminal IO with native Rust
(`std::fs`/`std::net`/`std::process`/`tokio`, its choice), calling the engine for computation. The minimal
embedding-IO API (a Model-B "drain external requests / inject replies" surface) is **deliberately left
undesigned for now** — to be specified when we take up embedding in earnest.

The in-engine **`mio` reactor + `ExternalObject` managers + `signal-hook`** plan below is **shelved**, not
deleted — recoverable if we ever want to run arbitrary existing Maude IO `.maude` files unmodified (which is
the only thing that strictly needs the engine to speak the `fileManager`/`socketManager` protocols itself).

**Why.** (1) The engine is *already built for this* — `Engine { sig, rt }` is instance-owned with **no global
mutable state and no direct IO**; the STD-STREAM work (Phase 2.5-C) already routes `write`→a buffer and
`getLine`←a buffer the host drives, i.e. it is already host-mediated, not syscall-based. (2) It matches where
Maude's value actually is (pure rewriting/search/model-checking) and how it is mainly used; raw file/socket/
process IO is a minority capability. (3) It avoids rebuilding a worse `tokio`/`PseudoThread` and the whole
signal/suspend-resume surface — the four most expensive, least-conformance-friendly phases collapse to one
small API. (4) Aligns with **D1** (instance-based, no globals). Trade-off: the IO *conformance target*
changes — "a faithful pure engine a host drives," not "byte-identical to Maude running an `openFile`
program" (that would require the host, or a shelved manager layer, to speak the exact protocols).

*Shelved plan (for reference):* a single-threaded deterministic **`mio`** reactor (owned `Reactor`: `Poll` +
fd→manager map + timer heap); `erewrite` interleaves rewriting quanta with `reactor.poll()`; Ctrl-C/SIGCHLD
via `signal-hook`→`AtomicBool` at safe points; managers implement an `ExternalObject` trait; no `tokio`.
**Revisit:** when embedding is taken up (design the Model-B API then) — see `objects-io-plan.md` §4-C…E.

## D6 — BDD: `biodivine-lib-bdd`, pure Rust and engine-local
**Decision.** Use pure-Rust **`biodivine-lib-bdd`** for order-sorted unification (`SortBdds`/AllSat).
The backend is a normal `tnk-core` dependency rather than a feature: S1's `unify` contract requires it in
every build. Backend-specific operations are contained in `sort_bdds.rs`; BuDDy FFI remains only a recorded
fallback.

**Why.** Pure Rust keeps builds portable and avoids BuDDy's global-state clash with the multi-engine model
(D1). Per-problem `BddVariableSet` values preserve engine isolation.

**Resolution (2026-07-05, S0 gate — binding).** Spike ran (`spikes/bdd-spike/`, report
`docs/migration/reports/S0-bdd-spike.md`): full `SortBdds` + sort functions + maximality + AllSat slice on
`biodivine-lib-bdd` 0.5.27, validated against pointwise semantics and brute-force maximal sets. **GO.**
Per-problem sort-solving ~100–350µs at realistic scale (656µs at a 128-sort stress case); AllSat ~2–5ns per
solution; enumeration-order fidelity by ROBDD canonicity + a verbatim port of the reference walk. The
production implementation uses fused apply-quantify, order-preserving block shift (one
precondition-documented `unsafe`), and substitute, and is wired through `unify/problem.rs`. The 27/27 S1
gate resolved the fallback question: BuDDy FFI is unmotivated.

## D7 — SMT: feature-gated `z3` 0.20.2 behind `SmtEngine`
**Decision.** Use `z3` 0.20.2 behind a narrow solver trait
(`assert_dag`/`check_dag`/`clear`/`push`/`pop`). SMT fresh-variable construction is pure tnk code,
not a backend method. The concrete backend lives under `tnk-core`'s optional `smt-z3` feature;
`tnk-repl` forwards it. The default build has a `NullSmtEngine`, remains pure Rust, and
loads/parses/degrades the SMT surface without libz3. Build the z3 lane in a separate target directory
and select its binary through the harness's existing `TNK_BIN` override.

**Why.** z3 covers Maude's QF_LIA/QF_LRA/mixed surface and has sound incremental push/pop.
Keeping the trait inside core avoids a dependency cycle; gating only the concrete translator/backend
keeps all frontend, metadata, number, and search code testable in the default build.

**Resolution (2026-07-21 refresh of the T0 gate — binding).** `spikes/smt-spike/` and
`reports/T0-smt-spike.md` now compile against `z3` 0.20.2 / `z3-sys` 0.11 and brew `libz3`.
Incremental push/pop equals fresh-solver-per-node verdicts across 894 randomized search-tree nodes;
all fixture-shaped Boolean/integer/real/coercion probes match the Yices2 oracle, including bignum and
exact-rational string mapping. Maude's observable SMT surface is verdict/state/substitution/
constraint only—never model values—so backend identity does not leak into fixture bytes.

**Scope correction (refreshed 2026-07-21).** Variant satisfiability still belongs after S2 and is
independent of the solver backend. The official 2016 `var-sat-rel3.tgz` prototype is now recovered
and checksum-pinned, but it targets Maude 2.7, does not compute through current variant result tuples,
and its prototype-owned files have no explicit license. Binding T6 choice: use it as an executable
semantic oracle only; implement a new native Rust decision procedure behind a source-compatible
`VAR-SAT-TOOL` Maude facade, with no z3/model-checker/Full-Maude dependency and no source reuse.

## D8 — Naming: codename `tambanokano`, `tnk-` crate prefix
**Decision.** Repo/umbrella codename **`tambanokano`**; crates prefixed **`tnk-`** (`tnk-core`,
`tnk-frontend`, `tnk-modules`, `tnk-engine`, `tnk-symbolic`, `tnk-meta`; binary `tnk`). Internal modules
named by layer. "Maude compatibility" is a **spec target**, not the product identity — "maude" is not baked
into crate names. The final public language name is deferred.

**Why.** This becomes its own extensible language; avoids identity/trademark entanglement with SRI's Maude.
**Impact.** Mechanical to rename later thanks to the prefix. **Confirmed 2026-06-19:** `tambanokano` is the
project name and `tnk` the accepted crate prefix. **Revisit:** only the final public *language* name
(distinct from the project name) remains deferred, after Phase 0/1.

## D9 — Ambiguity policy: warn-and-pick (RATIFIED 2026-07-05)
**Decision (2026-07-02, correctness-goal default).** On an ambiguous term, tnk picks a deterministic
first parse and computes (the warning text arrives with the phase-E diagnostics sink), instead of
hard-erroring. **Hard constraint:** the pick must match the oracle's pick on the C5 fixture cases
(`f a g` → `(f a) g`; non-assoc `a + b + c` → `(a + b) + c` — the oracle picks left/first, verified
live); if the Earley enumeration cannot structurally reproduce Maude's pick, STOP and escalate rather
than shipping a divergent pick. Reproducing MSCP's full pick order (option a) is deliberately NOT
attempted up front; revisit if differential testing surfaces real-world inputs where the pick differs.
**Status: RATIFIED by user 2026-07-05.** The hard constraint stands: a divergent pick found by
differential testing is an escalation, never shipped.

## D10 — Statement representation: home-grammar point-fix ONLY (RATIFIED 2026-07-05; rework stays open)
**Decision (2026-07-02, correctness-goal default).** Imported statement bubbles are parsed against
their **home module's** grammar/var scope and installed into the flattened module (removes the
context-dependent module-validity class: X-capture, importer-signature × imported-statement-text,
META-MODULE+RAT coexistence / stock term-order.maude). The **full compiled-module-algebra rework**
(import-stable compiled statements, Maude's semantic module algebra — unlocking build-time
typechecking of parameterized modules, source-form `show module`, full meta fidelity) is a separate
**user decision** and is deliberately NOT started. **Status: point-fix adopted as the D1a
implementation target; RATIFIED by user 2026-07-05. The full compiled-module-algebra rework remains a
separate, open user decision (revisit at the harness era). Known residual of the point-fix model:
statements donated by renamed/instantiated modules still parse against the merged grammar
(fable-audit.md §3.10 E2 fixed the command-grammar half).**

## D11 — REPL identity: standing prelude + file commands (RATIFIED 2026-07-05)
**Decision (2026-07-02, correctness-goal default).** The REPL (tool layer) gets: a standing prelude
loaded by default at startup, `set include BOOL on/off` semantics (BOOL auto-injection per prelude
line 3233), `load`/`sload` with a `MAUDE_LIB`-style search path, and the `-no-prelude`/`-no-banner`
CLI flags. The **engine/library layer stays prelude-free** (consistent with D5's host-embedding
stance): all of this is REPL-layer plumbing, none of it engine-deep. **Status: adopted as the C6
implementation target; RATIFIED by user 2026-07-05.**

## D12 — Meta-interpreter concurrency: coordination-only async on thread-confined engines (RECORDED 2026-07-05, ahead of phase I)

**Decision (user, 2026-07-05; recorded per subsystems-goal.md §2 I0 before any phase-I code).**

1. **Async is coordination only.** Evaluation is blocking CPU work performed on **thread-confined
   engines**: an engine (interpreter/Session) is created on its thread and never moves. The engine's
   non-`Send` internals (`Rc`, cell-based arenas) are a **deliberate compile-time guarantee** of that
   confinement, not a defect to engineer away.
2. **The core session API is runtime-agnostic.** Concurrency is plain threads + channels. Any
   async-executor integration (tokio or otherwise) is a thin adapter *outside* the core: neither
   `tnk-core` nor the session layer ever grows an executor dependency.
3. **Conformance boundary.** Message protocols, per-request results, and per-request rewrite counts
   are conformance targets (local synchronous mode is oracle-diffable; async mode must agree with it
   under the deterministic test schedule, §1.3 of the goal). Inter-message scheduling — timing and
   interleaving across concurrent requests — is implementation-defined.
4. **Process backend trigger.** The sole recorded trigger for a future OS-process interpreter backend
   is a **sandboxing requirement** (memory/crash isolation or per-child resource limits). If it
   arrives, it arrives as an embedding-host service per D5 — never as engine code.

**Why.** Rewriting is CPU-bound with no engine-internal await points, so an async runtime buys nothing
inside evaluation; thread confinement makes the single-threaded engine sound without locks; the
boundary statement keeps async mode testable (differential self-check) while conceding only what
Maude itself never specified (its own interleaving is scheduler-dependent).
**Impact.** Phase-I shape: I1 Session extraction (observationally invisible), I2 local synchronous
children (oracle-diffable), I3 cooperative cancellation at safe points, I4 the thread-backed
`newProcess` semantics with documented deltas (no memory/abort isolation; cooperative abandonment;
panic containment with the unwinding-panic build setting pinned). **Revisit:** only via the recorded
process-backend trigger.

**Phase-boundary clarification (user, 2026-07-23; binding).** Phase I is two
separately opened and closed goals. **I-S** extracts the reusable Session and completes
local synchronous meta-interpreters under live-oracle differential testing; it must
close and yield with no cancellation/thread/channel implementation present. **I-C**
starts only from that recorded closure and adds cancellation plus thread-backed
coordination, using permanent local mode as its executable semantic specification.
Concurrent work may not duplicate or alter Session/interpreter semantics. Detailed
gates: `remaining-plans/06-sessions-meta-interpreters.md`.
