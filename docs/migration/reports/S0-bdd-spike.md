# S0 — BDD spike: `SortBdds` + AllSat on `biodivine-lib-bdd` (gate report)

Phase-S step 0 of `subsystems-goal.md`: prototype the order-sorted-unification sort
computation on `biodivine-lib-bdd` per D6, measure, and decide go/no-go before any S1
production code. **Verdict: GO** (§6). Spike code: `spikes/bdd-spike/` (standalone crate,
not a workspace member; F1–F4 untouched). Library: `biodivine-lib-bdd` **0.5.27**
(pure Rust, no-`unsafe`-free but manager-less and `Send`-compatible). Hardware: Apple M5,
release build.

## 1. What was prototyped

The complete BDD-facing slice of order-sorted unification, ported from the reference:

| Reference source | Spike counterpart |
|---|---|
| `src/Core/sortBdds.cc` constructor (per-component gt relation, per-sort leq relations, bit encoding) | `SortBdds::new` |
| `src/Core/sortTable.cc` `linearComputeSortFunctionBdds` (per-symbol sort functions) | `SortBdds::build_sort_fn` |
| `SortBdds::operatorCompose` / `DagNode::computeGeneralizedSort` (bit-vector composition over a term) | `operator_compose` / `Problem::generalized_sort` |
| `src/Higher/unificationProblem.cc` `findOrderSortedUnifiers` (`unifier` constraint + `maximal` via per-variable forall-nand) | `Problem::build_maximal` |
| `src/Utility/allSat.cc` (enumeration walk: low-first DFS + don't-care binary counting) | `AllSat` (verbatim port on `BddPointer` traversal) |

Production will additionally port `recursiveComputeSortFunctionBdds` (the sort-diagram
walk; the reference computes *both* algorithms on every symbol and uses the recursive
result, so the spike's linear-only cost is a lower bound within ~2× of the real profile).
`S_Symbol` opts out of precomputed sort functions entirely (handles iterated stacks in
`computeGeneralizedSort`); that is S1 logic, not a BDD-capability question.

## 2. BuDDy-isms and their biodivine replacements

BuDDy has three primitives biodivine lacks natively. All three have working replacements,
exercised and validated in the spike:

| BuDDy | Replacement | Notes |
|---|---|---|
| `bdd_replace` (block remap, upward: cached relation → a free variable's real block) | `unsafe rename_variables` on a clone | Sound because the shift is **order-preserving**: real blocks sit above both scratch blocks, and blocks shift as units. Validated: produces the *identical canonical BDD* as building the relation directly from the subsort bitsets, in every validation scenario. O(nodes) relabel; 2.6–13× faster than direct DNF rebuild (§4, B4). |
| `bdd_replace` (downward: `unifier`'s fv-block → scratch, for the maximality step) | functional replace: `exists B . (f ∧ (B ↔ B'))` via one fused `binary_op_with_exists` | The downward move is *not* order-preserving (it crosses other real blocks), so the unsafe relabel is inapplicable; the functional form is safe and cheap at these sizes. |
| `bdd_veccompose` (simultaneous substitution; used by `operatorCompose` and `applyLeqRelation`) | sequential `Bdd::substitute` chain | Sound here because substituted functions never mention any pending scratch variable (scratch and real blocks are disjoint). Costs one fused op per domain bit instead of one pass total — the one measurable gap vs BuDDy (§5). |
| `bdd_appall(f, g, nand, vars)` (maximality quantifier) | `Bdd::binary_op_with_for_all(f, g, nand, vars)` | Native fused op; direct equivalent. |

Everything else (index cubes, DNF-of-cubes relations, `if_then_else` for the linear sort
function, node counts) maps one-to-one.

## 3. Enumeration-order fidelity (the S1 pass criterion)

Unifier enumeration order is observable and part of the S1 pass criterion. The spike's
`AllSat` is a line-for-line port of the reference walk (low-branch-first DFS, don't-care
set in variable-index order, binary counting over don't-cares, node-stack backtrack).
The order argument:

1. ROBDDs are **canonical**: same boolean function + same variable order ⇒ identical DAG,
   regardless of library.
2. The `maximal` BDD contains only the real (per-free-variable) variables — all scratch is
   quantified or substituted away — and the real blocks are allocated in the same relative
   order as Maude's. Scratch placement therefore cannot affect the enumerated order.
3. Identical DAG + identical walk ⇒ identical assignment sequence.

Validated in-spike: assignment sets match brute force exactly and counts match
`exact_cardinality` (which independently confirms no don't-care under- or over-counting;
the antichain scenarios force don't-care expansion through both the flip and reset paths).
Order itself gets its live-oracle confirmation from the S1 fixtures — that is where the
reference's unifier order becomes byte-observable.

## 4. Measured numbers (median of 5)

**Validation (all pass):** number-tower sort functions exhaustively match pointwise
semantics; maximal solution sets match brute force on the tower (free and bound-term
cases), 10 seeded random modules (end-to-end), and a 3-antichain diamond (9 = 3² maximal
solutions); the rename-remap path produces structurally identical BDDs everywhere.

**B1 — relations per component (gt + all leq):** 8 sorts 22µs → 32 sorts 280µs →
128 sorts 2.6ms (gt 568 nodes, leq 2062 nodes total). One-time per module.

**B2 — per-symbol sort function (linear):** 29–98µs for 16-sort components at arity 1–3;
347µs worst measured (32 sorts, arity 4, 8 declarations, 457 nodes).

**B3 — prelude-scale module (25 components, 300 symbols, eager):** 3.15ms total,
5631 nodes. Maude builds sort functions lazily per symbol touched by unification, so
this eager number is the worst case; the lazy per-symbol cost is B2.

**B4/B6 — per-unification-problem sort solving (constraint + maximality build):**

| scenario | direct-DNF remap | rename remap |
|---|---|---|
| 16 sorts, 2 free vars | 173µs | 79µs |
| 16 sorts, 10 free vars | 1.03ms | 331µs |
| 32 sorts, 5 free vars | 1.18ms | 286µs |
| 128 sorts, 5 free vars | 8.4ms | **656µs** |

**B7 — AllSat enumeration throughput:** 38,416 maximal solutions enumerated in 81µs
(~2–5ns/solution across antichain scenarios; counts exactly m^k as constructed).

**B5 — generalized sort of a deep term (veccompose-chain emulation):** number-tower `+`,
complete binary terms: ~33µs per symbol application, linear in term size (255
applications = 8.5ms).

## 5. Analysis against need

Per-problem cost is what matters: `unify`/variant/narrowing fixtures run hundreds to
thousands of unification problems. At realistic scale (≤32 sorts/component, ≤10 free
variables) a problem's full sort-solve is **~100–350µs** with the rename path — orders of
magnitude inside any observable budget, and the maximal-BDD sizes (10–42 nodes) show no
blowup tendency. The 128-sort stress case (larger than anything in the prelude or the
reference suite) is 656µs.

The one real gap vs BuDDy is the veccompose emulation inside `computeGeneralizedSort`:
~33µs per symbol application means a pathological 1000-node bound term would cost ~30ms
per problem. If S1 oracle fixtures ever surface that, the escape hatch is a native
`veccompose` — a straightforward memoized recursion over biodivine's public node arrays,
behind the facade, with no API consequences. Not needed to pass the gate; recorded as a
known optimization seam.

`substitute`'s per-call `support_set` scan and biodivine's allocate-per-op model are
visible in microbenchmarks but irrelevant at these node counts.

## 6. Go/no-go and D6 resolution deltas

**GO** on `biodivine-lib-bdd` 0.5.27; the BuDDy-FFI per-op fallback stays recorded in D6
but nothing observed here motivates it. Deltas to fold into the D6 facade design at S1:

1. The facade op list gains: **fused apply-quantify** (`binary_op_with_for_all/exists`),
   **order-preserving block shift** (the one place `unsafe` enters — isolated behind the
   facade with its precondition documented), and **substitute** (the veccompose seam).
2. Cached relations follow Maude's layout (scratch blocks low, real variables high);
   upward remaps use the block shift, the one downward remap (maximality) uses the
   functional exists-iff form.
3. `BddVariableSet` is fixed-size per instance; the facade must own universe (re)creation
   when a problem needs more real variables than allocated (cached relations relabel
   cleanly since widening preserves order — a production detail, not a risk).
4. AllSat is implemented over node traversal (not biodivine's own iterators) to preserve
   the reference walk; enumeration-order ground truth lands with the S1 oracle fixtures.
