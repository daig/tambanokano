# Phase 0 review — consolidated synthesis & triage

Inputs: **R0** (maintainer self-review), **R1** (GC/memory soundness), **R3** (API & extensibility),
and **R2** (rewriting semantics). Individual reports in this folder. `cargo test` green, `cargo clippy`
clean, no `unsafe`.

## Consensus verdict
The **chassis is right and on-plan** — `Id<T>` typed handles, the arena + mark/sweep tracer split, the
enum-over-theories `DagNode`, the no-globals `Engine`, the order-sorted poset/kind/`leq` core, and the
node-cached sort + `REDUCED` flag all extend cleanly and should be kept. The go/no-go (memory model
works, conforms to Maude, no perf cliff) stands.

But the review reframes what Phase 0 proved: it validated the **memory/GC/sort/dispatch** lower half.
The **matching-architecture** half — the theory-plugin seam every later theory needs — was deliberately
stubbed and is the next real risk. And a handful of Phase-0 *shapes*, if grown on, will force the
reduce/rewrite core to be rewritten twice. The cheapest time to reshape them is now, on ~600 lines.

The single most important correction to our decisions: **"stable ids + non-moving slot reuse + no
generation tag" is sound only if the GC root discipline is airtight — and right now nothing enforces it,
no `RootGuard` exists, and a missed root is *silent wrong answers*, not a crash.**

Two concrete correctness escalations from the semantics pass: (a) **recursion depth** — `reduce` is
native-recursive on *subject* depth, so it hard-crashes (process `SIGABRT`) at ≈`fib(25)` release /
`fib(24)` debug, and our shipped benchmark/fixture `fib(22)` sits *just below the cliff* — the most urgent
latent bug. (b) the **`REDUCED` flag goes stale across `add_equation`**: reduce a term, add an equation,
reduce again → silently returns the *old* normal form — a soundness hole reachable from the public API,
in exactly the incremental/REPL flow we target.

---

## Tier 1 — Fix now (cheap, high-confidence, low-risk) — **APPLIED 2026-06-20**
*(commits `64bf364`, `223faa7`, `783590d`; 22 tests green, clippy clean. Item 6 deferred to Tier 2.D.)*
1. **Mark-on-push in `mark_reachable`** (`engine.rs:119`) — currently pushes children unconditionally and
   marks on pop, so a node shared by *k* parents is pushed *k* times → GC mark stack is O(edges), not
   O(nodes). One-line fix using the "newly-marked" bool `Arena::mark` already returns. *(R1 M2)*
2. **Make GC primitives crate-private** (`arena.rs`: `mark`/`is_marked`/`clear_marks`/`sweep` → `pub(crate)`;
   the `arena` module too) — they're an ordered protocol that silently corrupts if reordered; only
   `Engine::gc` sequences them. *(R1 L2, R3 M4)*
3. **Encapsulate invariant-bearing fields** (`dag.rs` `DagNode{sort,flags,term}` & `Free{symbol,args}`;
   `symbol.rs` `Symbol{...}`) → `pub(crate)` + read-only getters; provide a checked `set_reduced`. Public
   `pub sort`/`pub flags` today let callers mark an unreduced node `REDUCED` (→ wrong normal form) or
   desync the cached sort. *(R3 H4)*
4. **Checked `make_free` arity** (`engine.rs:78`) — replace the `debug_assert_eq!` with an always-on
   `assert!` (build already heap-allocates, so it's free); release currently `zip`-truncates and silently
   builds a malformed node. *(R0 F4, R3 H2)*
5. **Subsort-cycle detection in `Sorts::close`** (`sort.rs`) — `a<b<a` is silently accepted as mutual
   `leq`; Maude rejects it. *(R0 F5, R3 M3)*
6. **(deferred → Tier 2.D)** Debug-gated generation + engine-id checks — moved to the Phase-1 arena-safety
   work so they are co-designed with the `RootGuard`/root registry (they are one change). *(R1 M1, R3 C2/L1, R0 F1/F6)*
7. **`#[must_use]`** on `match_pattern`/`deep_equal`/`reduce`/`gc`. *(R3 L2)*
8. **`marks.fill(false)`** instead of the per-element loop in `clear_marks`. *(R1 L3)*
9. **Tests:** error-sort propagation *through* `reduce`; subsort-cycle rejection; a bounded deep-term
   reduce (documents the depth limit until Tier 2.E). *(R0 F9)*
10. **[soundness] Version the `REDUCED` flag against the equation set** (`engine.rs`, `dag.rs`) — bump an
    engine epoch in `add_equation`, stamp it when marking a node reduced, and treat a node as reduced only
    at the current epoch. Fixes the silent stale-normal-form bug (reduce → `add_equation` → reduce). *(R2 H2)*
11. **No-op rewrite guard** — break the `reduce` loop when `try_rewrite_top` yields a term structurally
    equal to the redex (e.g. `eq a = a`) so it can't spin forever allocating; optionally a step bound. *(R2 M5)*

## Tier 2 — Settle before Phase 1's first non-free theory (design-level; cheap now, expensive later)
These are the "rewrite the core twice if deferred" items. Order matters: do A–D before AC/conditions/rules.

- **A. Matcher/`Subproblem` seam.** Define `LhsAutomaton` + a resumable, multi-solution `Subproblem`
  (iterator over `&mut Subst`); re-derive `try_rewrite_top`/`reduce` to drive a *solution stream*
  (`while let Some(()) = solutions.next() { ...check condition... }`). Route the existing free matcher
  through it (still single-solution). Unblocks both AC (multi-solution) and conditional equations
  (backtrack into the next solution). Discrimination net stays a later perf item behind the same seam.
  *(R3 C1, R0 F3)*
- **B. Signature/runtime borrow split.** Separate an immutable `Signature`/`Module` (sorts, symbols,
  statements) from a mutable `Context`/runtime (dag arena + `Subst`) so `&Signature` + `&mut Arena`
  coexist and the defensive clones (`rhs.clone()` — 186k/`fib(22)`, `children().to_vec()`) disappear.
  *(R3 H1)*
- **C. Traversal visitor.** Replace `children() -> &[DagId]` with `for_each_child(impl FnMut(DagId))`
  (GC) and `children() -> impl Iterator<Item=DagId>` (equality/reduce) so ACU `(term,mult)` / red-black
  tree / S-successor reps fit without editing GC + equality + reduce. *(R3 H3)*
- **D. Arena-safety pair.** Implement the D2 `RootGuard`/root registry (register on construct, unregister
  on `Drop`); add a **slot generation + per-arena engine id checked under `cfg(debug_assertions)`** (turns
  silent slot-reuse / cross-engine handle bugs into immediate panics in dev/test, ~zero release cost); and
  decide the *release* generational-id default by **benchmarking** an 8-byte handle vs `examples/peano.rs` —
  all before turning on safe-point GC. *(R1 C1/H1/M1, R3 C2/L1/M5, R0 F1/F6)*
- **E. Iterative reduce/match (explicit work-stack) — CRITICAL, do first.** `reduce`/`reduce_args`/
  `deep_equal` recurse on *subject* depth and hard-crash (process `SIGABRT`) at ≈`fib(25)` release /
  `fib(24)` debug — `fib(22)` (our benchmark) is 1–3 steps under the cliff. Convert to explicit work-stacks
  (as `mark_reachable` already is). The explicit stack also *is* the discoverable root set for D's
  safe-point GC, so do E with D. Interim: a documented depth note + keep example defaults well below the
  cliff. *(R2 C1, R0 F2, R1 M3, R3 M1)*

## Tier 3 — Deferred (track; legitimately Phase-1+ planned work)
- Multi-declaration `Symbol` + compiled sort decision diagram (overloading/least sort); `leq` via
  `fixedbitset` not `BTreeSet`. Isolated to `compute_free_sort` + `Sorts`. *(R3 M2)*
- Fallible construction boundary (`close`/`add_op`/`add_equation` → `Result` with diagnostics) when the
  parser feeds user input. *(R3 M3, R0 F7)*
- `expect`/`panic!` → `Result` at the eventual user-input boundary; document panics meanwhile. *(R3 L3)*
- Node niche-packing / SmallVec inline args (with backlog #2). *(R3 L4)*

## Decision-record update (amends D2)
Adopt: **generational slot tag + per-arena engine id, checked under `cfg(debug_assertions)` now**;
**release-mode** generational ids remain *open*, to be decided by a benchmark during Tier 2.D — not
defaulted to "off" by habit. Add a `RootGuard` API as the supported way to hold roots (the bare
`gc(roots)` iterator becomes an internal/advanced entry point). This will be written into
`03-open-decisions.md` (D2) once the debug-gated checks land.

## What's solid (do not re-litigate)
Arena accounting (live count, marks/slots lockstep, slot reuse, mark-newly-marked short-circuit);
the iterative, sharing-terminating GC marker; sort closure (components + transitive + error sort);
reduce + `REDUCED` soundness *for unconditional equations*; exact-rewrite-count conformance with Maude;
`Id<T>` typed-handle design; enum-`DagNode`; instance-`Engine`; `Subst` reuse. No `unsafe`, no UB —
worst case is a panic or wrong answer, never memory unsafety.
