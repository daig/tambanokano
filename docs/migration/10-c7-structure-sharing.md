# 10 — C7: structure sharing (construction dedup + normal-form forwarding)

**Bootstrap doc for a fresh session.** This is the complete plan + motivation for the Phase 1.5 **C7**
residual (deferred from `09-correctness-phase.md` §2.1). Read 09 §2.1 C7 first for the boundary; this doc has
the diagnosis, the two-part design, the ordered implementation plan with file anchors, and the verification.

## 0. Where we are (HEAD state)

Phase 1.5 is otherwise complete: **C1/C5/C8/C9/C10/C11/C12 done, C2 struck, C3 verified, C4 single-top done,
C6/F-2 done.** 214 tests, `clippy -D warnings` clean, `fib(22)=186579` (~6–8 M rw/s, session-noisy). Tree
clean. The C7 construction-sharing-only attempt was implemented, **proven insufficient, and reverted** —
commit `88f7f0c` ("C7 re-scoped"). Nothing C7-related is in the tree now; start fresh from this plan.

Reference C++: Maude at `~/code/maude-lang/Maude/src`; binary at `~/Downloads/Maude-3/maude`. Differential
discipline (the oracle): every claim checked against `~/Downloads/Maude-3/maude -no-banner <f> < /dev/null`.

## 1. The problem and the proven diagnosis

C7: our `rewrites:` count (and the reduction *work*) diverges from Maude when a term has a **repeated
reducible subterm**. Maude reduces each shared subterm **once**; we reduce it **per reference**.

Differential repros (recreate `share.maude`; note: keep `(` away from the start of a `***` comment — `*** (`
opens a Maude bracketed comment and silently eats the file):

```maude
fmod SHARE is
  sorts E P .
  ops a b : -> E [ctor] .
  op g : E -> E .
  op <_,_> : E E -> P [ctor] .
  op f : E -> P .
  var X : E .
  eq g(a) = b .
  eq f(X) = < g(X), g(X) > .
endfm
red < g(a), g(a) > .   --- subject dup:  Maude rewrites 1, ours 2
red f(a) .             --- RHS dup:       Maude rewrites 2, ours 3  (f's rhs g(X) appears twice)
```
(Original repro also: `mb mkA : Sml`, `red < mkA, mkA >` = Maude 1 / ours 2.) Result + least sort are
**identical** in every case; only the count (and work) differ.

### Why construction sharing alone does NOT fix it (proven)

Two reduction models:

- **Maude — in-place rewriting on a shared DAG.** Args are pointers; identical subterms are one node.
  Reducing a node *rewrites it in place* (`g(a)`'s node becomes `b`) and sets a REDUCED flag. `reduce(d)`
  checks the flag first, so a node reduced via one parent is done for *every* parent → each shared node
  reduces exactly once (count semantics **and** the structure-sharing perf optimization).
- **Ours — out-of-place rewriting on an index arena.** Node content is immutable (only `sort`/`reduced_epoch`
  mutate — a deliberate invariant, `dag.rs`). When `g(a)` rewrites to `b` the reduce frame *abandons* `g(a)`
  and moves to a fresh `b`; the original node is never touched. `reduced_epoch` is stamped only on a node
  that reaches normal form **without** rewriting (it IS its own nf); a rewritten redex is never stamped. So
  a shared `g(a)`, reduced via one parent, stays unstamped, and the next parent re-reduces it.

**Proof that construction sharing is inert:** the reverted attempt added a `NodeTerm`-keyed dedup memo on
`alloc_node` (enabled around the subject build + a flagged RHS). Instrumenting the dedup-hit path showed it
**fired (3 hits — the duplicates DID collapse to one node)**, yet the count was unchanged (2 and 3). So the
gap is the **reduction model**, not construction. We chose out-of-place for Rust idiom (no aliased mutation
of shared nodes); that idiom drops Maude's "reduce each shared node once" optimization — which is both a
count-conformance gap and a missing perf optimization for shared-reducible workloads. (fib has no sharing,
so the benchmark never exposed it, and fib will be unaffected by the fix.)

## 2. The design — two halves, BOTH required

Either half alone is inert (we just proved construction sharing alone is; forwarding alone gives nothing
because the duplicates are still distinct nodes each forwarding to its own result).

### Half 1 — construction-time structural dedup (makes the duplicates one node)

Maude shares the **subject** (`term2dag`) and **RHS** (`RhsBuilder` CSE). Mirror that with a
construction-scoped memo (NOT a persistent table — GC-clean, no separate pinning):

- `Runtime.dedup: Option<HashMap<NodeTerm, DagId>>` (None by default).
- `alloc_node` (the single allocation funnel, `engine.rs` ~830) gains a branch: when `dedup.is_some()`, look
  up the `NodeTerm`; return the existing id on a hit, else `alloc_raw` + insert. The default `None` path —
  the whole reduce hot path — is one `is_some()` branch. (`alloc_node` already takes a precomputed `sort`;
  two identical terms have the same base sort, so keying on the `NodeTerm` alone is correct.)
- Bottom-up construction makes the key *shallow*: children are deduped first, so identical subtrees share
  the same child ids → identical parent `NodeTerm`s → dedup hit. No deep structural hashing.
- Enabled around exactly two windows, **neither of which is a GC safe point**, so the memo never holds a
  stale id:
  - **Subject:** `Engine::begin_dedup()` / `end_dedup()` (public; set `rt.dedup = Some(HashMap::new())` /
    `None`) wrapped around `build_dag` at its two callers in `frontend/load.rs` (`reduce_command` ~306,
    `match_command` ~344). End the window *before* `reduce`.
  - **RHS:** a compile-time flag `CompiledEquation.rhs_shares: bool` (set in `push_equation` ~696 via a
    `term_has_repeated_subterm(&rhs)` scan). In `try_equations` (~1727) gate the rhs `instantiate`: if
    `rhs_shares`, `let saved = self.dedup.replace(HashMap::new()); … instantiate …; self.dedup = saved;`
    else the plain path. fib's `s(N+M)` has no repeat → flag false → zero overhead.

Derives needed for the memo key: `NodeTerm` → add `Clone, PartialEq, Eq, Hash` (`dag.rs` ~31); `Nat` → add
`Hash` (`num.rs` ~20; `NaValue` already has it). For the `rhs_shares` scan: `Term` + `Var` → add
`PartialEq, Eq, Hash` (`term.rs` ~14/21).

`term_has_repeated_subterm(t)`: true iff some `Op` subterm appears (by structural value) at ≥2 positions —
`HashSet<&Term>` walk, skip bare `Var` (already shares via subst). Over-approximating is safe (only enables
the memo); no false negatives.

### Half 2 — normal-form forwarding (makes that one node reduce once)

The Rust-idiomatic equivalent of Maude's in-place rewrite — the **thunk-update / indirection-node** pattern,
and really the *missing half of our existing `reduced_epoch` memo* (which already means "self is the normal
form" for non-rewritten nodes). **Do NOT overwrite node content** (breaks the render-after trace) and **do
NOT use a separate `HashMap` reduce-memo** (pins memory → fights C6 bounded-memory; GC id-reuse hazard).

- Extend the reduced stamp: a node reduced at the current epoch records its **normal form** `nf` — itself if
  it didn't rewrite, the rewrite result if it did. Representation options (pick during impl): add
  `nf: DagId` to `DagNode` valid iff `reduced_epoch == eq_epoch` (self-normal sets `nf = self`); or
  `nf: Option<DagId>` (None = self). `nf` is **metadata**, set via `get_mut` exactly like `sort`/`epoch` — no
  aliased *content* mutation, so the invariant holds.
- `reduce`/the loop's "child already reduced" check (`engine.rs` ~1457, currently `if
  node(child).reduced_epoch == eq_epoch { child_result = Some(child) }`) becomes: if reduced at epoch, deliver
  `node(child).nf` (the forward target) instead of `child`.
- `ReduceFrame` (~82) gains `start: DagId` — the id the frame was first pushed for, **preserved across the
  rewrite-replace** (`*stack.last_mut() = new_reduce_frame(next)` ~1520 must copy `start` over; or update the
  existing frame in place rather than replacing). On frame completion (normal-form point, ~1543, where it
  stamps `reduced_epoch`), also set `node(start).nf = rebuilt` (the final nf) and
  `node(start).reduced_epoch = eq_epoch`. (Intermediate rewrite results b, c… are freshly built / unshared,
  so only the frame's *start* needs memoizing.)
- **GC:** `safe_point_gc` / `mark_reachable` (~1346/~1378) must also mark a reduced node's `nf` (it is not a
  structural child — `g(a)`'s children are `[a]`, not `b` — so the generic `children()` visitor misses it).
  `nf` is then alive only while its forwarding node is alive (freed with it) → bounded, no C6 conflict.

### Why forwarding is the right shape (vs. the alternatives)

| property | forwarding (chosen) | in-place overwrite (Maude) | separate HashMap memo |
|---|---|---|---|
| trace-safe (redex content preserved for render-after) | **yes** | no (corrupts held ids) | yes |
| GC | `nf` on node, marked while live, freed with it | n/a | **pins** every reduced subterm → fights C6 |
| aliased content mutation | none (`nf` is metadata) | yes | none |

## 3. Implementation order

1. Derives: `NodeTerm` (dag.rs), `Nat` (num.rs), `Term`+`Var` (term.rs). Build.
2. Half 2 first (forwarding) — it's the load-bearing part and testable on its own with *manually shared*
   nodes (build `<d, d>` with the same `DagId` via the kernel API, no construction sharing needed):
   - `DagNode.nf` + init; `ReduceFrame.start`; the completion set; the child-reduced-check read; GC mark.
   - Kernel test: build a shared reducible node referenced twice, reduce, assert it reduced **once** (count).
3. Half 1 (construction dedup): `Runtime.dedup`, `alloc_node` split, `begin/end_dedup`, `CompiledEquation.
   rhs_shares` + `push_equation` + `term_has_repeated_subterm`, `try_equations` gate, `load.rs` subject
   wrapping.
4. Differential: `share.maude` (both → 1 and 2), the `mb mkA` repro (→1); add `conformance/correctness-
   sharing.maude` + a `conform_render`/repl test.
5. **fib measurement** (the risk): `cargo run --release -q --example peano 22 5 100`. Setting `nf` per
   reduced node adds work ≈ the existing epoch stamp; fib has no sharing so forwards never re-hit. If fib
   regresses materially, gate forwarding: only set/follow `nf` for nodes built through the dedup memo (mark
   them) — i.e., only shared nodes carry forwards.
6. Full suite + `clippy -D` + **all condition/trace fixtures byte-identical** (forwarding must not change the
   trace — `conditional`/`cmb`/`match-cond`/`owise`/`trace-*`). Re-verify `fib(22)=186579`.

## 4. Gotchas / facts established this session

- **Construction sharing alone is inert** (proven via dedup-hit instrumentation — see §1). Don't ship it
  without forwarding.
- **ACU `a+a` already merges** to one element with multiplicity 2 (reduced once); **bare-variable `X*X`
  already shares** via the substitution (instantiate returns the one binding). So C7 only bites a repeated
  **compound** subterm under a **free / AU / CUI** op. Keeps the dedup's common case simple.
- **Trace is render-after** (`tnk-repl/src/trace.rs` + kernel `TraceEvent` stream holds redex/result *ids*,
  rendered post-hoc from node content). This is why in-place overwrite is forbidden and forwarding (side
  pointer, content untouched) is required. `reconstruct_whole` (`set trace whole`) reads frame *content* and
  rebuilds — it must NOT follow `nf` forwards (reads raw content). The pretty-printer renders the ids it is
  handed and never follows forwards.
- **`alloc_node` is the single funnel** (`engine.rs` ~830, takes `sort` + `NodeTerm`); all `make_*`/`rebuild`
  route through it, so the dedup goes in exactly one place. It currently does the `gc_interval` alloc-counter
  bump — keep that in `alloc_raw` (a dedup *hit* allocates nothing, so it must not bump the counter).
- **Maude `*** (` bracketed-comment trap**: a `(` immediately after `***` opens `***(...)` and unbalanced
  parens swallow the rest of the file. Keep parens out of the first position of `***` comment lines in
  fixtures (use `---` line comments inside terms if needed).
- The perf upside is **workload-dependent** (shared-reducible structure only) and does **not** close the
  Maude throughput gap (that's compiled matching). fib is the neutral case.
- Condition-term duplicates (`ceq/cmb … if <g(X),g(X)> = …`) are the same mechanism (dedup the condition
  `instantiate` in `solve_condition`), but rarer; out of scope for the first pass — note as a sub-residual or
  extend the `rhs_shares`-style gate to conditions if it proves to matter.

## 5. Done-when

`share.maude` + the `mb mkA` repro + `correctness-sharing.maude` byte-identical to the reference (counts
included); all existing tests + condition/trace fixtures unchanged; `fib(22)=186579` with throughput within
noise (or forwarding gated to shared nodes if not); `clippy -D` clean. Then update `09` §2.1 C7 → DONE and
the memory index.
