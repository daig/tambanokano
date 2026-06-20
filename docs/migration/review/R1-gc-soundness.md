# R1 — GC / memory soundness review

**Framing:** there is **no `unsafe` and no UB anywhere** in this slice. Every access is a
bounds-checked `Vec` index or an `enum` match. So the worst outcome of any bug below is a **panic or
a silently wrong answer**, never a corrupt pointer or memory-unsafety. The entire risk surface is
*logical* use-after-free: a stable `DagId` reading a valid-but-wrong node — precisely the failure
mode the "stable ids, no generational tags" decision (D2) trades for, and it is currently
**completely undetected**.

## CRITICAL

### C1 — GC root set is an unenforced caller obligation; omitting a live root is silent corruption, not a panic
`engine.rs:109-115` (`gc`), `arena.rs:55-67` (`alloc`), `arena.rs:69-74` (`get`).

`gc(roots)` trusts the caller to enumerate *every* live `DagId`. A freed slot goes onto a LIFO free
list and is handed back by the **very next** `make_free`/`alloc` (`free.pop()`). Because the reused
slot is `Slot::Occupied` again, `Arena::get` returns it with **no panic**. The stale id and the new
id are bit-identical (`==`), so every accessor silently aliases the wrong node. The arena's own test
asserts this recycling (`reused == gone`).

The doc comment claims this is safe — "because the GC only frees unreachable nodes, no live id ever
dangles" — but **nothing enforces the antecedent.** "GC frees only unreachable" is true *relative to
the roots the caller passed*. The promised `RootGuard` (D2) **is not implemented**.

Minimal failing scenario (compiles, no panic, wrong result), public API only:
```rust
let ka = e.make_const(a);   // live; caller keeps `ka`
e.gc(Vec::new());           // caller forgot to root `ka`  -> slot freed
let kb = e.make_const(b);   // pops the same slot -> kb == ka
// e.node(ka).symbol() now returns `b`, not `a`. No panic.
```

**Fix:** implement the D2 root API — an internal root registry on `Engine`; `RootGuard` handles that
register on creation / unregister on `Drop`; `gc()` marks from the registry (plus explicit extra
roots) rather than a hand-passed list.

## HIGH

### H1 — In-flight temporaries (the term being reduced, substitution contents) are unrootable
`engine.rs:147-201` (`reduce`/`reduce_args`/`try_rewrite_top`), `term.rs` (`instantiate`, `Subst`).

`reduce` holds live ids in locals (`current`, `next`), `reduce_args` in a `Vec<DagId>`, `instantiate`
in `arg_ids`, and matching stashes ids in `Subst.bindings`. **None are roots.** Latent today only
because `gc` is never invoked from inside `alloc`/`make_free`/`reduce` (manual-only). The instant GC
becomes allocation-triggered (D2's perf model, backlog #5), a half-built rhs / pending vector / `Subst`
binding can be swept mid-rewrite → C1-style silent corruption in the hot loop. There is presently no
place to register these temporaries. **Fix:** root the reduce working set (or conservatively scan an
explicit in-flight stack) when auto-GC lands; decide/stub it now.

### H2 — Cross-engine id misuse is silent, contradicting D1's "enforced by construction"
`id.rs:13-29`, `engine.rs:91-93`. `Id<T>` carries only a `u32` + `PhantomData<fn() -> T>` — no engine
identity. Feeding `e1`'s `DagId` to `e2.node(id)` indexes `e2`'s arena: if in-bounds-and-occupied it
silently returns the wrong engine's node. The D1 "enforced by construction" claim is false for the
dangerous (in-bounds) case. **Fix:** a debug-only per-arena id stamped into `Id` and checked in `get`,
or brand the `Engine` with a generative lifetime tag.

## MEDIUM

### M1 — Reconsider generational indices to convert C1/H1/H2 into immediate panics
`id.rs`, `arena.rs`. Today there is **zero reuse detection**, and even the "safe" accessors
(`contains`/`try_get`) return `true`/`Some` for a stale-but-reused id. A generation per slot (bumped
on free), mirrored in `Id`, makes a stale handle mismatch → `get` panics at the point of misuse.
**Cost:** `Id` 4→8 bytes, doubling the hot `args: Vec<DagId>`; D2 deferred it for throughput, and this
is the go/no-go benchmark. **Recommended:** add generation checking under `cfg(debug_assertions)` now
(near-zero release cost); benchmark an 8-byte release id before deciding the release default. "Stable
u32 id + silent reuse + manual roots + no detection" is the worst combination to ship a foundation on.

### M2 — Mark stack is O(edges), not O(nodes); wide/shared DAGs blow up transient memory
`engine.rs:119-126`. `mark_reachable` marks **on pop** and `extend_from_slice`s all children
**unconditionally**, so a node reachable via *k* in-edges is pushed *k* times. Peak stack is
O(reachable edges); a DAG exists to share, so edges ≫ nodes is normal. The unary-chain benchmark
(fan-out 1) never exercises this. **Fix:** mark-on-push — `if mark(c) { stack.push(c) }` — bounding the
stack at O(nodes). [Applied in Tier-1.]

### M3 — Recursion depth = term depth in reduce/match/instantiate/deep_equal → stack-overflow abort
`engine.rs:147-181`, `term.rs`. `reduce`→`reduce_args`→`reduce`, plus `match_pattern`/`deep_equal`/
`instantiate`, recurse on the native stack proportional to term depth; a deep term overflows and
**aborts the process** (not a catchable panic). `mark_reachable` is correctly iterative — the same
treatment is needed here. **Fix:** explicit work-stacks, or a depth guard.

## LOW

- **L1 — `marks`/`slots` parallel Vecs coupled by convention** (`arena.rs`). Length lockstep is
  maintained, but folding the mark bit into the slot / node flags makes desync unrepresentable and
  improves sweep locality (Maude keeps the mark bit in node flags).
- **L2 — Unsequenced GC primitives are fully public** (`arena.rs`). `mark`/`clear_marks`/`sweep` `pub`
  on a `pub mod`; out-of-order use corrupts. Make them `pub(crate)`, expose only `Engine::gc`.
  [Applied in Tier-1.]
- **L3 — Mark storage/perf** (`arena.rs`). `marks: Vec<bool>` is 1 byte/slot; a bitset is 8× denser
  and clears via memset; at minimum `marks.fill(false)`. [fill(false) applied in Tier-1.]

## What's genuinely correct (worth keeping)
- No `unsafe`, no UB. A stale id yields a wrong node or a panic, never memory-unsafety.
- `get`/`get_mut` panic on a `Free` slot — catches use-after-free in the common (not-yet-reused) case.
- Type-level id safety within an engine: `Id<DagNode>` vs `Id<Symbol>` can't be confused, while `Id`
  stays `Copy`/`Send`/`Sync` and u32-small.
- `mark_reachable` is iterative and terminates on sharing/cycles via `mark`'s newly-marked return.
- Accounting is balanced and drift-free: `live` +1 per `alloc`, −1 per reclaimed slot; `gc` always
  `clear_marks` before marking; `sweep` runs destructors via `on_free`.
- LIFO free list → O(1) alloc with good reuse and a bounded high-water mark.

## Bottom line
The arena is memory-*safe*; it is not soundness-*enforcing*. "Stable ids + non-moving reuse + no
generational tag" is sound only if the root discipline is airtight — currently backed by neither the
promised `RootGuard` (C1) nor any reuse detection (M1), and unable to protect in-flight reduction
temporaries (H1). Before Phase 1 adds allocation-triggered GC: (1) implement the `RootGuard`/root
registry; (2) add `cfg(debug_assertions)` generational + engine-id checks so C1/H1/H2 become panics in
dev/test; (3) benchmark a release-mode 8-byte generational id and decide deliberately. M2/M3 are cheap,
independent hardening. *(M2, L2, and L3's `fill` were applied in the Tier-1 pass; C1/H1/M1/M3 + the
RootGuard are scheduled for Phase-1 opening — see `05-review-synthesis.md` Tier 2.D/E.)*
