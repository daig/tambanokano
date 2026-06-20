# Phase 0 results — go/no-go: **GO**

Phase 0 built a free-theory vertical slice of the kernel and benchmarked it against the reference
C++ Maude. The three load-bearing decisions are validated:
- **D1** instance-based `Engine` (no globals) — the whole slice runs on owned `Engine` values.
- **D2** non-moving mark-sweep GC over an index arena with stable ids — see GC numbers below.
- **D3** enum-dispatch `DagNode`/`Symbol` over the closed theory set — no vtables on the hot path.

## Conformance (tnk-core vs reference C++ Maude, identical theories)
Fixtures: `conformance/peano.maude`, `conformance/fib.maude`. Same operators, same equations.

| workload | result | rewrites (tnk-core) | rewrites (Maude) |
|---|---|---|---|
| `2 + 2` | `s^4 0` | 3 | 3 |
| `3 * 4` | `s^12 0` | 21 | 21 |
| `fib(22)` | `17711` (`s^17711 0`) | 186579 | **186579** |

Canonical forms **and** rewrite counts match exactly — strong evidence the reduction semantics are
faithful for the free theory.

## Throughput (Apple Silicon / aarch64, Rust 1.94 `--release`)
Measured via `cargo run --release --example peano 22 30 2000000`:

| metric | tnk-core (Phase 0, naive) | reference Maude |
|---|---|---|
| reduce | **7.1 M rewrites/s** | 57.7 M rewrites/s |
| GC mark | **207 M nodes/s** | — |
| GC sweep | **149 M nodes/s** | — |
| memory | arena bounded at ~491k nodes across 30× fib(22) (GC reclaims between reductions) | — |

## Verdict — GO
- **Correctness:** exact conformance with Maude on the test theories.
- **Memory model:** GC is fast (hundreds of M nodes/s) and keeps memory bounded — the D2 concern
  ("can a Rust arena+mark-sweep keep up?") is answered **yes**. No perf cliff.
- **Reduce throughput:** ~8× behind Maude — but with a deliberately *naive* engine. The gap is
  attributable to deferred optimizations (below), not to the arena/GC architecture.

## Phase 1 optimization backlog (to close the ~8× reduce gap)
1. **Discrimination-net `LhsAutomaton`** (A2) — replace the per-equation linear match scan.
2. **Inline / `SmallVec` argument storage** — eliminate the per-node heap `Vec` allocation
   (currently the dominant allocator cost).
3. **Compiled `RhsAutomaton`** — stop cloning the rhs `Term` on every rewrite.
4. **In-place destructive rewrite** (`overwriteWith`) — cut garbage vs. the functional rebuild.
5. **Safe-point GC during `reduce`** (RAII `RootGuard` + context-tracked roots) — bound memory
   *within* a single large reduction, not only between top-level reductions.

These are exactly the C++ techniques catalogued in reports A1/A2; Phase 0 deliberately shipped the
correct-but-naive version first to de-risk the architecture before optimizing.
