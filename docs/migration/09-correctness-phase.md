# Phase 1.5 — Evaluator Correctness (audit & fixes)

**A dedicated correctness-hardening phase between Phase 1 (complete) and Phase 2 (parameterized
programming + rules + the real prelude).** Phase 1 made the evaluator *broad* and conformance-verified on
idiomatic modules; this phase makes it *faithful in the corners* — it differential-audits the evaluator
against the reference binary and fixes semantic divergences (results, sorts, rewrite counts, termination)
**before** Phase 2 builds new machinery (rules, views) on top of it.

**Why now, not later.** Every divergence here is *cheapest to fix today*: the codebase is the smallest it
will ever be, the analysis is in-context, and Phase 2 will add code that reads sorts and lives in the same
reduce-loop/matcher neighborhood — so a sort-model change made *after* rules forces re-verifying rules too.
None of these are blocking idiomatic code (that's why Phase 1 passed), but they are **release blockers** for
a "byte-identical to the reference" engine.

> **STATUS.** Scaffolding + **C1 (eager→lazy sort/membership computation)** fully planned below. C1 is the
> front-and-center item — the deepest of the known divergences (it alone causes a *termination* difference)
> and the root cause of full-trace deviation #2 (membership `Whole:`). The remaining audit items (§3) are
> placeholders to be filled by a systematic differential sweep of the evaluator.

Read order: this doc → `08-full-trace-plan.md` §status (the deviation that surfaced C1) → the code seams
cited in §2.

---

## 1. Methodology (carried forward from the Phase-0/Stage-A discipline)

- **Differential testing against the reference binary** is the oracle, not memory or reasoning. Each
  candidate divergence becomes a minimal `.maude` module run through both `~/Downloads/Maude-3/maude
  -no-banner <f> < /dev/null` and our REPL/engine, diffing **result value, result sort, rewrite count, and
  termination**.
- **Scope = semantics, not formatting.** Print-order / spacing / echo differences are tracked as trace or
  pretty-printer deviations (see `08` §status), not here. This phase is about *answers*: does the engine
  compute the same normal form, the same least sort, the same `rewrites:` count, and halt on the same
  inputs as Maude?
- **Each item is written up as:** problem + reproducing evidence → root cause (with file:line on both
  sides) → target model → implementation seams → risk/interaction checklist → verification checklist.
- **Boundary honesty.** For each divergence, state precisely *which class of modules* it affects and which
  it provably does not, so the fix's value (and the cost of punting) is grounded, not guessed.

---

## 2. C1 — Eager → lazy sort / membership computation  **[front and center]**

### 2.1 The divergence

Our evaluator applies **membership axioms eagerly, at node construction**; Maude applies them **lazily, at
the reduce "normal-form" point** (`computeTrueSort`). The two models agree on the normal-form *value* and
*sort* of every term, but differ observably when a membership matches a term an equation also reduces:

| Class | Test (`mb`/`cmb` on a **reducible** op) | Maude | Ours (eager) | Severity |
|---|---|---|---|---|
| count | `red g(a)` · `mb g(X):Small` + `eq g(a)=big` | `1` rewrite, `big` | `2` rewrites, `big` | over-count |
| count | `red g(a)` · `eq g(a)=g(b)`, both carry `mb` | `2`, `g(b)` | `3`, `g(b)` | over-count |
| **termination** | `red g(a)` · `cmb g(X):Small if loops=tt` · `eq loops=loops` · `eq g(a)=big` | **halts → `big`** | **diverges (hangs)** | **correctness** |
| trace | any of the above | (no `mb` step) | extra `… becomes …` step; `Whole:` omittable | formatting |

(All four reproduced live; see the session transcript / re-create from the table.) The **termination** row
is the real correctness gap: Maude reduces `g(a) → big` *before* the conditional membership's looping
condition is ever evaluated; we evaluate the `cmb` eagerly at construction and loop.

**Boundary (verified).** The divergence requires a membership whose top symbol *also has equations*
(a "reducible-operator membership"). For memberships on **irreducible constructors** — the idiom; the
manual's `SortedList` example; **the entire Maude prelude declares zero `mb`/`cmb`** — the two models are
provably identical (the constructor term *is* a normal form, so both apply its membership exactly once, at
the same point). So C1 is confined to an unusual (and, for the looping case, ill-coherent) pattern — but it
is real, and the *value*-correctness argument (below) is why it never surfaced in Phase-1 conformance.

**Why the value is always the same** (so this is "count + termination", never "wrong answer"): the
membership-refined sort of any given structural form is computed identically by both engines. Eager merely
*additionally* refines forms that then get reduced away — and those forms' sorts never reach the normal
form (a reduced child is re-sorted; a strat-kept child gets the same membership in both). So the result
term and its reported least sort always agree; only *which doomed intermediate refinements are evaluated at
all* differs, which is what drives the count and (for `cmb` conditions) termination.

### 2.2 Root cause (both sides)

**Ours (`crates/tnk-core/src/engine.rs`).** `alloc_node_constrained` (≈820) runs at *every* node
construction and, when the module has any memberships, calls `constrain_to_smaller_sort` (≈836) — applying
membership axioms (and `cmb` condition reductions) to the freshly built node, counting each as a rewrite.
`make_free`/`make_acu`/`make_s`/`make_na`/`rebuild` all route through it, so the initial term (`build_dag`)
and every reduce-time rebuild refine sorts immediately.

**Maude (`/Users/dai/code/maude-lang/Maude/src`).** A freshly built `DagNode` has `sortIndex =
SORT_UNKNOWN` (no sort, no membership at construction). Sorts are computed during reduction:
```cpp
// DagNode::reduce (Interface/dagNode.hh:570)
if (!(topSymbol->eqRewrite(topSymbol, this, context)))   // rewrite to fixpoint FIRST
  { setReduced(); topSymbol->fastComputeTrueSort(this, context); break; }  // THEN true sort
```
`fastComputeTrueSort` (`Interface/symbol2.hh:29`) → `slowComputeTrueSort` (`Interface/symbol.cc:74`) =
`computeBaseSort` (structural) **then** `constrainToSmallerSort` (`Core/sortConstraintTable.cc:120`).
Crucially `computeTrueSort` applies **memberships only, never equations**, and runs on the *normal form* —
so Maude never refines a term it is about to reduce away.

### 2.3 Target model (the design)

Adopt Maude's timing, with one deliberate simplification we can afford:

- **Keep eager *base* sort** (structural, pure, context-free, cheap). Every node still carries at least its
  base sort the instant it is built, so `sort_of` stays a total read — we don't need Maude's `SORT_UNKNOWN`
  state or its on-demand base-sort machinery. *(This is the one genuine benefit of the current model; we
  retain it.)*
- **Defer membership refinement** to the reduce **normal-form point**. When `try_rewrite_top` returns
  `None` for a node (no equation applies → it is a normal form), *then* compute its true sort.
- **At the normal-form point, recompute the base sort from the node's *current* children, then constrain.**
  The recompute is **essential**, not redundant: a child refined *in place* at its own normal-form point
  does **not** propagate to a parent that was not rebuilt (the reduce loop keeps `original` when `args ==
  orig`). So the parent must recompute its base sort from the now-refined children before constraining.
  This is exactly `fastComputeTrueSort = computeBaseSort + constrainToSmallerSort`.

  *Worked example* (`red f(g(a))`, `f`/`g` equation-free, `mb g(X):Small`, overloaded `f:Small->RS` /
  `f:Big->RB`): build with base sorts (`g(a):Big`, `f(g(a)):RB`); reduce refines `g(a)` to `Small` in
  place at its normal-form point; at `f`'s normal-form point we *recompute* `f`'s base sort from
  `g(a):Small` → `RS`, then constrain → `RS`. Without the recompute we would wrongly keep `RB`. Maude
  gets `RS`. ✓
- **Membership-free modules are untouched.** Gate the entire normal-form sort step on
  `!sig.memberships.is_empty()` — `fib`/`peano`/the prelude get exactly today's hot path (base sort at
  construction, no normal-form step, no per-rewrite cost).

### 2.4 Implementation seams

1. **Construction → base sort only.** Split `alloc_node_constrained` (≈820): keep `alloc_node` (base sort,
   no membership) as the universal allocator; remove the eager `constrain_to_smaller_sort` call. All
   `make_*`/`rebuild` now build with base sorts only. (Mechanically: callers stop going through the
   "constrained" variant.)
2. **Reduce normal-form point → `finalize_true_sort`.** In `reduce` (the line `self.dags.get_mut(rebuilt)
   .reduced_epoch = sig.eq_epoch();`, ≈1448), *before* stamping the node reduced, when
   `!sig.memberships.is_empty()`: recompute `rebuilt`'s base sort from its current children (`free_sort` /
   `compute_sort` over the children's *now-refined* sorts), then `constrain_to_smaller_sort(rebuilt)`. This
   is the one new call site; it mirrors `DagNode::reduce`'s `fastComputeTrueSort`. Membership applications
   counted here (as today, but now only on forms that actually reach normal form).
3. **Custom-strat skipped args → recursive `compute_true_sort`.** Maude's `complexStrategy`
   (`FreeTheory/freeSymbol.cc:503-505`) calls `computeTrueSort` on **all** args at the strat `0` step, even
   ones the strategy never reduced — refining their sorts *without* applying equations. Our reduce skips
   non-strategy args entirely, so they never reach a normal-form point. Add a recursive
   `compute_true_sort(node)` (refine subterm sorts bottom-up, no equations) and call it on the
   strat-skipped args at the top-rewrite step. **Standard strat needs nothing extra** (all args are
   reduced → refined via seam 2); this seam only fires for ops with a non-standard `strat`, which is why it
   is its own step and gets its own differential test (§2.6).
4. **`build_dag` (frontend) — no change.** It uses the same `make_*` API, so it automatically builds with
   base sorts only; `red`/`match` reduce the term, which refines it. (Confirm `reduce_command` /
   `match_command` read sorts only off the *reduced* result — they do today.)
5. **Bonus — closes full-trace deviation #2.** With memberships firing *inside the reduce loop*, the reduce
   frame stack is available at membership application, so the `Membership` trace event can carry a
   reconstructed whole-root term (`reconstruct_whole`, as `Old:`/`New:` already do for equations) → render
   the `Whole:` line. Fold this into the change and update `08` §status (remove deviation #2).

### 2.5 Risk / interaction checklist (the delicate part)

- **[#1] Matcher reading an un-reduced node's sort.** With lazy refinement, an un-reduced node carries only
  its base sort. Audit every `sort_of` / `leq(sort_of(...), v.sort)` read in matching and overload
  resolution and confirm it only ever reads a node that has reached its normal-form point (innermost
  reduction guarantees a redex's *children* are reduced+refined before the redex's equations/variables are
  matched; conditions reduce their subjects first). This is the load-bearing assumption — verify it
  explicitly, don't assume.
- **AC / `iter` membership matching.** `constrain_to_smaller_sort`'s match path currently has theory
  follow-ups; ensure the normal-form constrain handles ACU/AU/CUI/S nodes (it runs on the same node either
  way, so this should be timing-neutral — verify).
- **`cmb` condition evaluation moves from build-time to reduce-time.** The existing F-2 mitigation (GC
  disabled during condition eval) already covers condition reduction *during* reduce, so this is in scope
  of the current GC contract — confirm no new GC-rooting gap.
- **Shared subterms refined in place.** A shared node refined once (gated by `reduced_epoch`) is seen by
  all parents; each parent recomputes its base sort at *its own* normal-form point, so the refinement
  propagates. Confirm the `reduced_epoch` cache doesn't skip a parent's recompute.
- **Sort reported by `red` / `match`.** `result <Sort>:` and match bindings read the *reduced* top/subterms
  → refined. Verify on a membership module.
- **No-op / fixpoint of the recompute.** Recompute+constrain must be idempotent at the normal-form point
  (it is: base sort is a pure function of children; constrain is a fixpoint loop). Confirm it can't loop.

### 2.6 Verification checklist

- **All existing conformance fixtures** pass — value, sort, **and rewrite count** — especially
  `conformance/{membership,cmb,match-cond,owise,conditional}.maude` (the count is the sensitive part).
- **New differential fixtures** for the previously-divergent cases, now matching Maude:
  `conformance/correctness-mb-reducible.maude` (the `g(a)`/`eq g(a)=big` count → `1`), and a **termination**
  case (`cmb` on a reducible op with a divergent condition) that now *halts* with the same result as Maude.
- **Strat × membership** differential test (the seam-3 interaction — currently untested anywhere): a custom
  `strat` op over a membership-bearing arg; confirm the skipped arg's sort is refined to match Maude.
- **Full trace suite** still byte-matches; **add the membership `Whole:` line** under `set trace whole on`
  and diff it (closes deviation #2).
- **Perf:** `fib(22) = 17711 (186579 rewrites)` unregressed (`cargo run --release --example peano 22 1
  100`) — membership-free, so it must be byte-for-byte the same hot path; plus a membership-heavy reduce as
  a sanity timing.
- `cargo test` all four crates green; `cargo clippy --all-targets -- -D warnings` clean.

### 2.7 Outcome

One change closes **three** known divergences — the membership over-count, the `cmb`-on-reducible-op
*termination* gap, and full-trace deviation #2 (`Whole:`) — and removes the corresponding "documented
deviation" notes from `08`. The eager model's only real benefit (a total `sort_of`) is retained via the
kept eager *base* sort.

---

## 3. Further evaluator-audit items  *(scaffolding — to be filled by a differential sweep)*

This phase is meant to *shake out* divergences, not just fix the one we found. C1 was discovered
incidentally (via the trace `Whole:` gap); the rest of the evaluator deserves a deliberate sweep. Each
candidate below becomes a `C<n>` section once a minimal differential test confirms (or refutes) it.

Candidate probes (unconfirmed — prioritize by writing the differential test first):
- **C2? F-1 no-op rewrite guard.** A self-rewriting `eq a = a` (or a rule producing an identical term) —
  does Maude detect the no-op and stop, or loop? We currently loop. Cheap to fix if real; another
  spurious-non-termination axis adjacent to C1's. (`07` §F-1.)
- **C3? Non-confluent / order-dependent membership & equation application.** Incomparable applicable
  membership targets, or owise/condition interplay where application order is observable. Confirm our
  smallest-first order matches Maude's beyond the locked cases.
- **C4? Error-sort / kind computation.** `[Sort]` error-sort naming and propagation (we already know one
  cosmetic naming divergence, `overload.maude` task #8); audit whether kind-level results ever differ
  *semantically*, not just in the printed bracket name.
- **C5? AC / `iter` membership matching completeness.** Memberships whose lhs is a theory term
  (matching modulo ACU/AU/S) — currently a noted follow-up; confirm coverage or scope it.
- **C6? Substitution-size / re-entrant reduce edge cases.** Deep/condition-nested reductions, the F-2
  engine-global GC root set (also a Phase-2 `rew`/`search` prerequisite — slot it here).
- *(add as the sweep surfaces them.)*

---

## 4. Sequencing

1. **C1 first** (this doc, §2) — it is the deepest known divergence and is cheapest now.
2. Then the **§3 sweep** — expand C2+ as differential tests confirm divergences; fix in cheapness order.
3. **F-2 (engine-global condition-reduce GC root set)** lands in this phase too — it is both a deferred
   Stage-B item *and* a prerequisite for bounded-memory `rew`/`search` in Phase 2.
4. Only then **Phase 2** (parameterized programming + rules + the real prelude), built on a faithful
   evaluator. If Phase 2 opens with *rules* (reduce-loop/matcher territory), C1 must precede it so the two
   verify together; if it opens with *parameterization* (module-system territory), C1 may interleave but
   should still land before rules.

**Conformance discipline (unchanged):** every fix is validated against the reference binary — value, sort,
rewrite count, and termination — not from memory. Grow `conformance/` with a `correctness-*.maude` fixture
per fixed item.
