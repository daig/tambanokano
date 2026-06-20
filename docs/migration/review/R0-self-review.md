# R0 — Phase 0 self-review (maintainer pass)

Close read of the committed `tnk-core` slice. Findings ranked by how much they threaten the
*foundation* (i.e. would force rework or cause silent wrongness later), not by immediate breakage —
Phase 0 itself passes all tests and conforms to Maude.

## Critical / foundational

**F1. GC root-safety is a silent-corruption hazard, and it blocks safe-point GC.**
`Engine::gc(roots)` (`engine.rs:109`) trusts the caller to pass *every* live root. Miss one and
reachable nodes are swept; their slots are then recycled by later `alloc` (`arena.rs` reuse path), so
pre-existing `DagId`s silently point at *different* nodes — wrong results, no panic. It's safe today
only because `gc` runs at quiescent points (between top-level reductions, result re-rooted). But the
deferred "safe-point GC during `reduce`" item *requires* knowing the entire in-flight root set: the
`current`/`next` nodes, every pending node in the `reduce`/`reduce_args` recursion, and substitution
contents — none of which the current recursive design tracks. So this is both a latent footgun and a
concrete blocker for bounding memory within a single large reduction.
→ **Reconsider D2's "no generational tags."** Generational indices (slotmap-style: a u32 generation in
the handle + slot, compared on access) convert this whole bug class from silent corruption into a clean
panic, for ~one extra word and one compare. For a foundation everything rests on, that safety is worth
it. Also design explicit root tracking (a root stack / `RootGuard`) alongside the iterative reduce (F2).

**F2. Recursive reduction/matching → stack overflow on deep terms.**
`reduce`, `reduce_args` (`engine.rs:147,161`), and `match_pattern`/`deep_equal`/`instantiate`
(`term.rs`) all recurse on term structure. Peano `s`-chains and Fibonacci already build terms thousands
deep; `fib(22)` recursed several-thousand frames and survived only on the default ~8 MB stack. `fib(30)`,
factorials, or reducing a long `s`-chain will overflow the stack (a crash, not a handled error).
→ Convert the hot traversals to explicit work-stacks. This also makes the live root set *discoverable*
(the explicit stack *is* the roots), which is exactly what F1's safe-point GC needs — so F1 and F2 should
be solved together.

## High

**F3. The theory-plugin abstraction — the central later-phase pattern — is not yet exercised.**
Phase 0 hardcodes `NodeTerm::Free` and a bespoke recursive `match_pattern`. The entire downstream
architecture (report A2) hinges on a `LhsAutomaton`/`Subproblem` trait seam: two-phase match returning a
residual subproblem whose `solve()` lazily enumerates *multiple* solutions under backtracking — which AC
matching needs (bipartite + Diophantine, lazy subproblems). None of that shape exists yet, and the
current single-solution boolean matcher doesn't gesture at it.
→ Not a defect in Phase 0 (deliberately deferred), but it tempers the "foundation proven" claim: the
**memory/GC/sort/dispatch** lower half is validated; the **matching-architecture** half is the next and
still-unproven risk. Recommend a Phase-1 *tracer bullet*: introduce the `LhsAutomaton`/`Subproblem`
traits and reimplement the free theory behind them (single-solution) *before* tackling AC, to validate
the seam (esp. the `&mut Substitution`-shared-across-backtracking borrow pattern A2 flagged) on easy mode.

## Medium

**F4. `make_free` arity check is debug-only.** `compute_free_sort` (`engine.rs:78`) uses
`debug_assert_eq!` for arity; in release, a wrong-arity call silently builds a malformed node (`zip`
truncates the domain/arg check and the node stores mismatched args). `make_free` is public API.
→ Either return a `Result`/always-check, or document it as an internal invariant and expose a checked
constructor. Low blast radius now (we own all callers), but it's a public footgun.

**F5. Subsort cycles are silently accepted.** `Sorts::close` (`sort.rs`) runs union-find + BFS closure
with no cycle check; `a < b, b < a` yields mutually-`leq` sorts instead of an error (Maude rejects this).
→ Add a cycle check in `close()` returning/flagging an error.

## Low / nits

- **F6. Cross-engine `Id` misuse is undetectable** (`id.rs`) — a `DagId` from engine A used in engine B
  indexes silently. Generational tags (F1) don't fix cross-engine; a debug-only engine id would. Defer.
- **F7. Equation order = insertion order** (`engine.rs:191` first-match). Fine and matches our tests, but
  document it; Maude's selection (specificity, `owise`) differs and may surface when porting real modules.
- **F8. `Subst::get` panics on out-of-range index** (`term.rs`) — internal invariant; fine but note.
- **F9. Test gaps:** no test for error-sort propagation *through reduce*, for deep-term behavior (F2), or
  for equation overlap. Add a few.

## What is genuinely solid (don't re-litigate)
- Arena bookkeeping: `live` count, `marks`/`slots` length lockstep, slot-reuse, mark-newly-marked
  short-circuit — all correct and tested.
- Sort closure: union-find components + BFS transitive closure + per-kind error sort — correct, tested.
- Reduce + REDUCED flag is **sound for unconditional equations**: a node is canonical iff its args are
  canonical and no top equation applies — exactly the invariant `reduce` maintains.
- Conformance: identical canonical forms *and* rewrite counts vs reference Maude is strong evidence the
  free-theory semantics are faithful.
- Enum-dispatch `DagNode`, instance-`Engine`, `Term`(static)/`DagNode`(runtime) split — clean and on-plan.

## Triage recommendation
Fix now (cheap, foundational): **F4** (checked make_free), **F5** (cycle check), **F9** (a couple tests),
and adopt **F1's generational-index decision** (revise D2; implement the handle/slot generation — small).
Schedule as Phase-1 opening work (bigger, design-level): **F2 + F1-roots** (iterative reduce + explicit
root tracking + safe-point GC) and **F3** (the LhsAutomaton/Subproblem tracer bullet). Defer F6/F7/F8 with
notes.
