# Decision Record — foundational choices (Stage 1)

Status: **accepted as working defaults** (Stage 1). Each decision is deliberately revisitable at the
phase noted under *Revisit*; agreeing now fixes the defaults so scaffolding can proceed without churn.
Ordered by implementation blast radius (most pervasive first). See `01-architecture-map.md` §4 and
`02-migration-plan.md` for how these are woven in.

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

## D5 — External IO: own a `mio` reactor
**Decision.** A single-threaded, deterministic **`mio`** reactor (owned `Reactor` struct: `Poll` + fd→manager
map + timer heap) drives external objects; `erewrite` interleaves rewriting quanta with `reactor.poll()`.
Control-C/SIGCHLD via `signal-hook` setting an `AtomicBool` checked at safe points. Managers implement an
`ExternalObject` trait. `tokio` is **not** adopted now.

**Why.** Matches Maude's cooperative single-threaded interleave with no async function-coloring across a
synchronous CPU-bound engine; lighter and deterministic.
**Impact.** Shapes `engine::io` and `ObjectSystemRewritingContext`. **Revisit:** **Phase 2**; reconsider
`tokio` only for a future heavily-networked direction.

## D6 — BDD: `biodivine-lib-bdd` behind a facade, feature-gated
**Decision.** Use pure-Rust **`biodivine-lib-bdd`** behind a `bdd` facade trait (var/and/or/not/restrict/
exists-forall/compose/AllSat), under a `symbolic` feature. Used only by order-sorted unification (`SortBdds`),
ACU Diophantine selection, and LTL→Büchi labels — all Phase 3. BuDDy-FFI kept as a per-op fallback.

**Why.** BDDs don't touch core rewriting (deferrable); pure Rust keeps the build clean; manager-less BDDs
avoid BuDDy's global-state clash with the multi-engine model (D1).
**Impact.** Facade isolates the choice across three consumers. **Revisit:** **Phase 3** — prototype the
`SortBdds` sort-function + AllSat path first to confirm perf.

## D7 — SMT: `z3` crate default, behind a trait
**Decision.** Default to the **`z3` crate** behind `trait SmtEngine` (assert/check/push/pop/fresh-var),
**runtime/feature-selectable** (not build-time-fixed as in C++). cvc5/yices2 remain feature alternates.
Variant satisfiability stays a `.maude` library over variant unification.

**Why.** Best Rust SMT bindings; superset of Maude's theories (QF_LIA/QF_LRA/mixed); solid incremental
push/pop for `smt-search`.
**Impact.** Per-backend work is `DagNode → solver term` translation + sort mapping, isolated by the trait.
**Revisit:** **Phase 3** (confirm Z3 incremental semantics match `smt-search`'s pruning).

## D8 — Naming: codename `tambanokano`, `tnk-` crate prefix
**Decision.** Repo/umbrella codename **`tambanokano`**; crates prefixed **`tnk-`** (`tnk-core`,
`tnk-frontend`, `tnk-modules`, `tnk-engine`, `tnk-symbolic`, `tnk-meta`; binary `tnk`). Internal modules
named by layer. "Maude compatibility" is a **spec target**, not the product identity — "maude" is not baked
into crate names. The final public language name is deferred.

**Why.** This becomes its own extensible language; avoids identity/trademark entanglement with SRI's Maude.
**Impact.** Mechanical to rename later thanks to the prefix. **Confirmed 2026-06-19:** `tambanokano` is the
project name and `tnk` the accepted crate prefix. **Revisit:** only the final public *language* name
(distinct from the project name) remains deferred, after Phase 0/1.
