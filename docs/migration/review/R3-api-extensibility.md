# R3 — API & extensibility review

Lens: Rust API/idiom/safety **and** extensibility (the latter weighted highest). Scope:
`crates/tnk-core/src/*.rs` + `examples/peano.rs`, assessed against `reports/A1`–`A3`, the
architecture map, the migration plan (esp. §8 guardrails), and the D1–D3 decision record.

Phase 0 is explicitly a "validated probe, not a foundation to preserve" (`02-migration-plan.md` §8).
This review therefore grades findings by **how much they will distort or block Phase 1+ if the new
code is allowed to grow on the current shapes**, not as defects in a shipping product. `cargo clippy
--all-targets` is clean and there is no `unsafe`; every finding below is design-level, not a lint.

## Verdict in one line
The *chassis* is right and matches the decisions — `Id<T>`, the arena+mark/sweep, the
enum-over-theories `DagNode`, the no-globals `Engine`, the order-sorted poset/kind/`leq` core, and
node-cached sort+`REDUCED` all extend cleanly. The *seams* that AC/conditions/rules need are **absent,
not merely naive**: there is no matcher/`Subproblem` abstraction, the rewrite driver is hard-wired to
single-solution boolean matching, `Engine` bundles signature+runtime (already forcing defensive
clones), and node traversal is hard-coded to `&[DagId]`. These should be shaped *before* theories are
added, or the reduce/rewrite core gets rewritten twice.

---

## Sound foundations — keep as-is
Worth stating so Phase 1 doesn't "rewrite" these by reflex:
- **`Id<T>`** (`src/id.rs`): phantom-typed, `Copy`, `u32`-sized, no exposed arithmetic, hand-written
  trait impls avoiding spurious `T: Trait` bounds. Textbook typed-index handle. Matches D1.
- **`Arena` mark/sweep primitives** (`src/arena.rs`): `clear_marks`→`mark`(returns newly-marked)→
  `sweep(on_free)` is a clean tracer-driver split; `on_free` callback already supports releasing
  external resources later. The iterative marker (`mark_reachable`, `src/engine.rs:119`) correctly
  avoids native recursion on shared DAG structure.
- **Enum-over-theories `DagNode`/`NodeTerm`** (`src/dag.rs`): the `enum` shape is exactly D3; adding
  `Acu{…}`/`Au{…}`/`S{…}`/`Var{…}`/`BuiltIn` arms is additive (the *arms* are not the problem — see
  H3 for the traversal contract that is).
- **Sort poset/kind/`leq` core** (`src/sort.rs`): union-find components + synthesized error sorts +
  BFS transitive closure is A3's "PORT (data)". Node-cached least sort + `REDUCED` flag mirrors Maude.
- **No-globals `Engine`** (`src/engine.rs`) and **`Subst` reuse via `reset`** (`src/term.rs:68`):
  D1-faithful and matches Maude's reused-substitution scratchpad.

---

## Critical

### C1 — No matcher/`Subproblem` seam; the rewrite driver is hard-wired to single-solution matching
`src/term.rs:84` (`match_pattern(&self, pat, subject, subst) -> bool`) and its only consumer
`src/engine.rs:185` (`try_rewrite_top`).

**Concern (extensibility, highest-impact).** Phase 0 has *no* theory-plugin abstraction at all — no
`LhsAutomaton`, no `Subproblem`, no two-phase `match()`→residual-`solve()`, no `ExtensionInfo`. That is
expected for the *free* matcher (the guardrails call it throwaway). The real problem is that the
**driver is shaped around a single yes/no answer**:
- `match_pattern` returns `bool`. AC matching is intrinsically *multi-solution* (A2 §1: the `xmatch`
  example yields 12; "the engine must enumerate"). The signature has no room for a residual subproblem
  or a next-solution call.
- `try_rewrite_top` (`src/engine.rs:191`) does `if match { chosen = rhs; break }` — it commits to the
  first match of the first matching equation and cannot **backtrack into a different solution of the
  same equation**. Once equations gain conditions (and once AC yields several substitutions), the
  correct loop is "for each solution of this lhs, try the condition; on failure get the next solution".
  That control structure is absent.
- `match_pattern(&self, …)` is a stack-recursive function over an immutable engine. A2 §4 flags that
  `Subproblem::solve` must hold residual state (bipartite graph, Diophantine system) *across* resume
  calls while mutating the substitution — i.e. an **owned, resumable state machine**, not recursion.

So adding AC/conditions is not "extend `match_pattern`" — it is introducing the matcher seam *and*
re-deriving `try_rewrite_top`/`reduce` to consume a **solution iterator**.

**Recommendation — fix the *shape* now, defer the *content*.** Before any second theory lands, define
the seam and route the existing free matcher through it: `enum LhsAutomaton`, a `Subproblem` modeled as
a resumable iterator over `&mut Subst` (A2 §3, arch-map §4.3), and rewrite `try_rewrite_top` to drive
`while let Some(()) = solutions.next() { …check condition… }` even though Phase-0 free matching yields
exactly one solution. This keeps the reduce core from being rewritten twice. (The compiled
discrimination net itself stays a perf item — backlog #1 — and can come later behind the same seam.)

### C2 — Arena reuses slots with no generation tag → silent logical use-after-free once safe-point GC lands
`src/arena.rs:5-6` (generational tags deferred), `:55-67` (`alloc` reuses `free.pop()`), `:69-74`
(`get` panics only on a *freed* slot, not on a *recycled* one).

**Concern (safety).** A reclaimed slot returns to the free list and is reused by the next `alloc` with
**the same `DagId`** (the test at `:185` even asserts the id is recycled). The safety argument in the
module doc — "the GC only frees unreachable nodes, so no live id ever dangles" — holds *only* while GC
runs between top-level reductions with the complete root set passed in (as `examples/peano.rs:113`
does). Phase 1 backlog #5 (`04-phase0-results.md`) is **safe-point GC during `reduce`** with
context-tracked roots. The moment GC can run mid-reduction, any in-flight `DagId` that the root
tracking misses does not dangle into a freed slot (which would panic) — it resolves to a **recycled,
well-typed but wrong node**, i.e. silent corruption with no panic and no `unsafe` to grep for.
Generational ids are the standard guard and A1/D2 only *deferred* them, not ruled them out.

**Recommendation — fix before the Phase-1 GC work.** Either (a) make `DagId` carry a generation
(`raw: u32` + `gen: u32`, or pack into 64 bits) and have `get` validate it, or at minimum (b) a
`debug_assert!`-gated generation check so the safe-point-GC bring-up surfaces missed roots immediately.
Pair this with C2's sibling, M5 (RootGuard). Doing it now is cheap; retrofitting after the in-place
rewrite + safe-point GC code exists is not.

---

## High

### H1 — `Engine` bundles signature + runtime → split-borrow friction is already forcing defensive clones
`src/engine.rs:16-24` (one struct owns `sorts` + `symbols` + `dags` + `equations`), symptomatic sites
`src/engine.rs:194` (`chosen = Some(eq.rhs.clone())`) and `src/engine.rs:163`
(`node.children().to_vec()`).

**Concern (extensibility + perf).** Both clones exist purely to release an immutable borrow of `self`
before a `&mut self` call: you cannot hold `&Equation` (borrow of `self.equations`) while calling
`instantiate(&mut self)`, nor iterate a borrowed `&[DagId]` while calling `reduce(&mut self)`. The
root cause is that the *static signature* (sorts/symbols/equations) and the *mutable runtime* (the dag
arena + substitution) live in one `&mut Engine`. Every Phase-1 feature re-hits this exact wall:
condition evaluation (read the condition while building/reducing dags), rule rewriting (borrow the rule
table while mutating the dag spine), and AC `solve` (hold pattern/subproblem refs while mutating the
substitution — A2 §4 names this explicitly). The `rhs.clone()` is also a real per-rewrite cost
(186k rhs-tree clones in `fib(22)`; `04-phase0-results.md` backlog #3).

**Recommendation — do the split early (it is already on the roadmap; §8 says "don't entrench the
bundling", but the current code entrenches it).** Separate a borrow-immutable `Signature`/`Module`
(sorts, symbols, statements) from a `Context`/runtime owning `&mut Arena` + `Subst`, so `&Signature`
and `&mut Arena` coexist and the clones disappear. Even an internal first step — grouping the arena
behind a sub-struct so `&self.signature` + `&mut self.dags` can be borrowed disjointly — unblocks the
pattern. Defer the full `Module`/`RewritingContext` names, but establish the borrow seam before
conditions/rules, or the clone-to-dodge-the-borrow idiom proliferates through the new code.

### H2 — `make_free` arity check is `debug_assert` → release builds silently construct malformed nodes
`src/engine.rs:64` (`pub fn make_free`), `:78` (`debug_assert_eq!(sym.arity(), args.len(), …)`), and
the downstream `:79-83` where `compute_free_sort` does `sym.domain.iter().zip(args)`.

**Concern (safety/API).** `make_free` is the primary *public* node constructor. In release the arity
assert vanishes, and the subsequent `zip` **silently truncates to the shorter side** — so a node built
with the wrong argument count is accepted, its cached sort computed from a prefix of the domain, and a
structurally invalid `NodeTerm::Free` (where `args.len() != symbol.arity()`) enters the DAG. Every
later consumer (matching, `children()`, GC) then trusts an invariant that was never enforced. This is
the exact "silent malformed node in release" the brief flags.

**Recommendation — fix now; it is nearly free.** The node build already heap-allocates a `Vec`, so an
always-on `assert!` (or returning `Result<DagId, ArityError>`) costs one integer compare in the noise.
Prefer a real `assert!` for the internal id-based constructor, or a checked builder if `make_free`
stays public. Do not ship a release-silent invariant on a `pub` constructor.

### H3 — `children() -> &[DagId]` traversal contract won't serve ACU multiset / tree / S-successor reps
`src/dag.rs:45-49` (`children(&self) -> &[DagId]`), consumers `src/engine.rs:124` (GC marker,
`extend_from_slice`), `src/engine.rs:163` (`reduce_args`), `src/term.rs:124` (`deep_equal`).

**Concern (extensibility).** Adding theory arms to the enum is additive (good), but the **traversal
seam is hard-coded to "borrow a contiguous slice of plain `DagId`"**, and the planned reps cannot
provide that (A1 §2, A2 §2): ACU's flat rep is `(DagId, multiplicity)` *pairs* (not `&[DagId]`); ACU's
red-black `TreeDagNode` has **no contiguous array to borrow** (only iteration); S-theory stores
`s^n(arg)` as `(count: BigInt, arg)` (one stored child standing for *n*). The C++ design uses a
`markArguments` *visitor* precisely because there is no universal slice (A1 §2). Today GC, `deep_equal`,
and `reduce_args` all bake in the slice, so each must be reworked when a non-`&[DagId]` arm appears.

**Recommendation — introduce the visitor/iterator seam now (cheap, localizes the blast radius).**
Replace `children() -> &[DagId]` with a traversal that does not assume contiguity — e.g. a
`fn for_each_child(&self, f: impl FnMut(DagId))` for GC marking, and (edition 2024 supports RPITIT) a
`fn children(&self) -> impl Iterator<Item = DagId>` for equality/reduction. Route the current free arm
through it. Then ACU/S arms are pure additions instead of edits to GC + equality + reduce.

### H4 — Encapsulation: invariant-bearing fields are `pub`, contradicting the crate-internal coupling model
`src/dag.rs:32-34` (`DagNode { pub sort, pub flags, pub term }`), `:40` (`Free { pub symbol, pub
args }`), `src/symbol.rs:15-17` (`Symbol { pub name, pub domain, pub range }`).

**Concern (API/safety).** These fields encode invariants the engine maintains: `sort` is "computed
once at construction", `flags`/`REDUCED` gate whether reduction is skipped, and `args` length must
equal arity. Exposing them `pub` lets any caller set `REDUCED` on an unreduced node (→ skipped
reduction → wrong normal form), overwrite the cached `sort`, or swap `term`/mutate `args` without
recomputing the sort — all silently. The migration plan (§1) explicitly intends tnk-core internals to
be **crate-internal** ("theories need kernel internals → Rust crate-internal visibility"); the C++
`friend` access becomes `pub(crate)`, not `pub`. The current full-`pub` surface is the opposite of that
design, and accessors already exist (`children()`, `symbol()`).

**Recommendation — fix now (mechanical, and sets the discipline before downstream crates depend on the
fields).** Make these `pub(crate)` and expose read-only getters (`sort()`, `flags()`, an arity-checked
mutator for `set_reduced`). `Id::from_raw`/`index` are already correctly `pub(crate)` — mirror that.
(`Symbol`'s flat struct is itself a placeholder for A3's composed `SymbolCore`, so this is partly
moot there, but the visibility habit should start now.)

---

## Medium

### M1 — Native recursion over unbounded user-term depth (stack-overflow risk)
`src/engine.rs:147` (`reduce`) → `:161` (`reduce_args`), `src/term.rs:113` (`deep_equal`), `:84`
(`match_pattern`), `:130` (`instantiate`).

**Concern.** `mark_reachable` was deliberately made iterative (`src/engine.rs:119`), but `reduce`,
`deep_equal`, `match_pattern`, and `instantiate` recurse on the native stack. `reduce`/`deep_equal`
depth is bounded by *subject* depth, which is unbounded user data (a `s^n 0` chain reduces n-deep —
the benchmark even builds `s^2_000_000`, only avoiding overflow because it GCs rather than reduces it).
A user reducing a deep term overflows the stack. Maude uses explicit stacks (redexStack / stack
machine) partly for this.

**Recommendation — defer but track.** Acceptable for the free-theory spike; convert the reduce and
equality paths to explicit work-stacks (as `mark_reachable` already is) when the reduce loop is
re-derived for in-place rewrite (backlog #4). Match/instantiate depth is bounded by *pattern* size
(author-controlled), so lower urgency there.

### M2 — Single-declaration `Symbol` + placeholder `compute_free_sort`; `leq` via `BTreeSet`
`src/symbol.rs:14-18` (`domain: Vec<SortId>`, `range: SortId` — one declaration), `src/engine.rs:76`
(`compute_free_sort`), `src/sort.rs:40` (`geq: Vec<BTreeSet<SortId>>`), `:88` (`leq`).

**Concern (extensibility).** Ad-hoc/subsort overloading (A3) needs *multiple* declarations per symbol
plus the compiled `sortDiagram` + `findMinSortIndex` least-sort/preregularity computation; the current
"one decl, sort = `range` (else kind error)" must be replaced. A3 also specifies `leqSorts` as a
`fixedbitset`, not `BTreeSet` (correctness is fine; allocation/lookup cost is not). **Good news:** the
"node sort = operator range" assumption the guardrails warn about is **isolated** to
`compute_free_sort` — nothing else hardcodes it (everything reads the cached `sort_of`), so the
diagram is a localized swap.

**Recommendation — defer (planned Phase 1), but two cheap habits now:** (a) keep all sort queries going
through `Sorts`/`sort_of` (already true) so the diagram drops in behind the same API; (b) when
overloading lands, reshape `Symbol` to hold `Vec<OpDeclaration>` + a diagram handle rather than bolting
a second declaration onto the flat struct.

### M3 — No fallible construction API; build paths panic or silently accept bad input
`src/sort.rs:99` (`close()` — no subsort-cycle detection), `src/engine.rs:131` (`add_equation` — no
validation), `:132` (`.expect("equation lhs must be an application")`), `src/term.rs:73` (`Subst::get`
indexes), `:132` (`.expect("unbound variable in instantiation")`).

**Concern (API/correctness).** Two concrete gaps: (1) `close()` runs union-find + BFS closure with a
`seen`-set, so a **cyclic** subsort declaration `a < b < a` is silently accepted as `a ≤ b ∧ b ≤ a`
(two distinct sorts mutually `≤`), which Maude rejects — A3 calls for "Kahn topological sort that
returns `Result` on cycles". (2) `add_equation` validates nothing: `nr_vars` correctness, that rhs
variables ⊆ lhs variables, and that var indices are in range are all unchecked, so a malformed equation
panics far away at reduce time (`instantiate`'s `expect`, or `Subst::get`'s index). Today this is
masked because statements are hand-built in tests, but the Phase-1 parser will feed *user* input.

**Recommendation — defer the algorithms, but plan the signatures now.** When the parser arrives the
construction boundary (`close`, `add_op`, `add_equation`) must return `Result` with real diagnostics
(cycle, arity, unbound-rhs-var, preregularity warnings). Add cycle detection to `close()` as the first
increment. Keep programmer-error `assert!`s (e.g. "add after close") as-is.

### M4 — `pub` mechanism surface invites order-sensitive misuse
`src/arena.rs` (whole `Arena` is `pub` with `get_mut`, raw `mark`/`sweep`), `src/term.rs:84`
(`match_pattern` is `impl Engine`, `pub`).

**Concern.** The GC protocol (`clear_marks`→`mark`→`sweep`) is a 3-call ordering that silently
misbehaves if reordered, and `Arena::get_mut` hands out `&mut DagNode` (re-exposing the H4 invariants).
Matching living as `impl Engine` in `term.rs` also cements the H1 bundling and is where A2 wants a
`theory/` module instead.

**Recommendation — defer/low-cost.** Consider `pub(crate)` for the `arena` module (the example only
needs `Engine`/`Term`/`DagId`/`SymbolId`), and plan to move matching into a `theory` module behind the
C1 seam rather than `impl Engine`.

### M5 — GC root API has no RAII RootGuard / context-tracked roots
`src/engine.rs:109` (`gc(roots: impl IntoIterator<Item = DagId>)`).

**Concern (extensibility).** The caller must enumerate *all* roots at the call site, so `gc` is only
safe **between** top-level reductions (as the example uses it). D2/the plan call for an RAII
`RootGuard` + context-tracked roots so GC can run at safe points *within* a reduction (backlog #5)
without freeing in-flight intermediates (`current`, partially-rebuilt arg vectors). This is the
mechanism whose absence makes C2 dangerous.

**Recommendation — defer, but co-design with C2.** Introduce `RootGuard` (register on construct, drop
= unregister) together with generational ids before turning on safe-point GC; they are the same piece
of work.

---

## Low

### L1 — Cross-engine `Id` mixing is convention-only
`src/id.rs:4-5` ("Ids from different engines must not be mixed; … enforced by convention"). With D1
meta-interpreters being separate `Engine`s (Phase 3), an `Id` from engine A used against engine B
silently indexes the wrong node. Brand-by-lifetime (`Id<'e, T>`) is ergonomically heavy; an
engine-tag in debug builds is a lighter guard. **Defer**, document the sharp edge.

### L2 — Missing `#[must_use]` on side-effecting / result-returning fns
`match_pattern`/`deep_equal` return `bool` (ignoring the result of a match that also mutates `subst` is
a bug), and `reduce`/`gc` return values easy to drop (`src/engine.rs:147,109`; `src/term.rs:84,113`).
Add `#[must_use]`. **Fix now (trivial).**

### L3 — `expect`/`panic!` in otherwise-`pub` API
`src/arena.rs:62,72,79`, `src/engine.rs:132`, `src/term.rs:132`. Fine as internal-invariant guards,
but they are reachable through public methods and undocumented as panicking. **Defer**; document
panics, and convert the ones on the eventual user-input boundary to `Result` (see M3).

### L4 — `Id`/`DagNode` cache-footprint not yet niche-packed
A1 §4 flags node compactness as a real micro-opt (`sort` index + flags should niche-pack). `NodeFlags`
is a `u8` and `DagNode` carries `SortId`(u32)+`NodeFlags`(u8)+enum; fine for Phase 0. **Defer** to the
SmallVec/inline-args work (backlog #2), just don't let the node grow casually.

---

## Forced-rework vs. fine-as-is (summary)

| Phase-0 decision | Extends cleanly? | Action |
|---|---|---|
| `enum NodeTerm` over theories | Yes (arms are additive) | Keep (D3) |
| `children() -> &[DagId]` traversal | **No** — multiset/tree/S reps can't supply a slice | Rework to visitor/iterator **before** theories (H3) |
| `match_pattern -> bool`, recursive | Throwaway *and* no seam; driver is single-solution | Introduce `LhsAutomaton`/`Subproblem` + iterator-driven `try_rewrite_top` **first** (C1) |
| `Engine` bundles signature+runtime | **No** — split-borrow friction, clones | Split `Signature`/`Context` **before** conditions/rules (H1) |
| `compute_free_sort` / one decl per symbol | Isolated placeholder | Swap for sort diagram + multi-decl `Symbol` (planned, M2) |
| Sort poset/kind/`leq` core | Yes | Keep; add cycle-detection + `Result` + bitset (M2/M3) |
| Arena slot reuse, no generation | Unsafe once safe-point GC lands | Add generation tag / RootGuard **before** backlog #5 (C2/M5) |
| `pub` node/symbol fields | Contradicts crate-internal model | `pub(crate)` + getters now (H4) |
| Functional `reduce`, recursive | Stack-overflow on deep subjects | Explicit work-stack with the in-place-rewrite rework (M1) |
| `Id<T>`, arena mark/sweep, no-globals `Engine`, `Subst` reuse | Yes | Keep |

**Through-line:** the four items to settle *before* Phase 1 adds its first non-free theory are the
matcher seam (C1), the signature/runtime borrow split (H1), the traversal visitor (H3), and the
arena-safety pair (C2/M5) — each is far cheaper to shape on the small Phase-0 code than to retrofit
after AC/conditions/rules are built on the current shapes. Everything else is either a mechanical
hardening (H2, H4, L2) or legitimately deferrable planned work (M2, M3, M5, M1).
