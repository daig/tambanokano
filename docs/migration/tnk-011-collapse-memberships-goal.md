# TNK-011 goal — collapsing membership indexing

**Status:** completed 2026-07-27.
**Oracle:** Maude 3.5.1.
**Primary issue record:** `docs/bug-triage.md`, TNK-011.

## Goal statement

Make executable `mb`/`cmb` axioms whose ACU or two-sided-AU lhs can collapse under `id:`, or whose CUI
lhs can collapse under `id:`/`idem`, participate in least-sort computation at every compatible subject root.
A collapsed membership must produce Maude-compatible result terms, least sorts, rewrite counts, condition behavior, statement order, and traces,
including when the surviving operand collapses recursively through another supported theory.

This is an indexing repair. The existing ACU/AU/CUI/S matchers remain the semantic authority once a constraint
is selected.

## Confirmed failure and semantic impact

Before the repair, the kernel stored a membership only under `lhs.top_symbol()`. Therefore this legal
constraint was never offered to the bare `a` node:

```maude
sorts E Special .
subsort Special < E .
ops z a b : -> E [ctor] .
op _*_ : E E -> E [comm id: z] .
var X : E .
mb a * X : Special .
```

Maude applies the membership to `a` with `X = z`, lowers its sort to `Special`, and counts one rewrite. Before
TNK-011, tnk left `a : E` and counted zero. This was not count-only: the missed true sort changed overload
selection and sorted equation matching. In the downstream control, Maude returned `b` in two rewrites while
tnk left `wrap(a)` with zero:

```maude
op wrap : E -> E .
op wrap : Special -> Special .
var S : Special .
eq wrap(S) = b .
red wrap(a) .
```

The same top-indexing defect is confirmed for:

- ACU with a two-sided identity;
- AU with a two-sided identity;
- CUI with a two-sided identity;
- CUI idempotence without an identity;
- CUI collapse whose surviving operand is iter-rooted;
- recursive survivors, including CUI-over-AU and CUI-over-CUI collapse.

The matchers are not the defect in this scope. These already match Maude when reached:

- an iter membership containing a nested CUI-collapse pattern;
- a rooted CUI `cmb` containing iter plus a nonlinear AC subpattern;
- ordinary iter memberships, including surplus successors absorbed by a variable.

## Reference semantics

Maude preprocesses every sort constraint, computes whether its lhs can collapse at the top, and then:

- offers a noncollapsing, nonvariable lhs only to its syntactic top symbol;
- offers a collapsing lhs to the symbol tables broadly;
- lets each symbol reject impossible candidates;
- orders accepted constraints smallest-target-sort first before compilation.

Binding source: Maude `Core/module.cc`, `Module::indexSortConstraints`; recursive collapse analysis lives in
`ACU_Term::analyseCollapses2`, `AU_Term::analyseCollapses2`, and `CUI_Term::analyseCollapses2`.

A direct port of tnk's current `collapse_targets` result is insufficient. That helper is an equation-oriented,
shallow approximation: for `(a ; L) * Y` it records only the AU top symbol, not the recursively reachable
constant `a`; for `(a * X) * Y` it can record no extra symbol because the immediate survivor has the same top.
Both memberships apply to bare `a` in Maude.

## Required design

### Store each compiled constraint once

Replace the owned `HashMap<SymbolId, Vec<SortConstraint>>` layout with:

- one dense, declaration-ordered arena of compiled `SortConstraint`s;
- direct per-symbol indexes containing constraint IDs;
- collapse-candidate indexes by result kind containing constraint IDs.

The existing dense membership ID remains the trace/source metadata key and should also address the arena.
Do not clone a compiled lhs automaton or compiled condition once per compatible symbol.

### Index conservatively, filter semantically

For this goal, an lhs is collapse-capable when its top matcher already supports the relevant collapse:

- ACU with a two-sided `id:`;
- AU with a **two-sided** `id:`;
- CUI with `id:` or `idem`.

A noncollapsing membership stays in its syntactic-symbol index. A collapse-capable membership goes into the
collapse index for the kind of its target sort. At runtime, every node of that kind considers those candidates;
the compiled matcher rejects statically impossible collapses. This conservative envelope handles recursive
survivors without duplicating Maude's recursive `collapseSymbols` analysis and without an
$O(\text{symbols}\times\text{constraints})$ table.

The syntactic and collapse candidate streams must be merged without allocation in the existing observable
order:

1. descending component-local target-sort index (smallest target first);
2. declaration order for equal target keys.

A constraint belongs to exactly one stream, preventing duplicate trials at its own top symbol.

### Preserve the execution model

Do not enable synthetic extension in `membership_applies`; membership matching remains whole-match with
`ext_allowed = false`. AC extension counts continue to arise from bottom-up normalization of retained parse
shape. This change only makes a constraint visible at roots its lhs can collapse to.

Preserve:

- normal-form-time membership application;
- strict sort lowering and fixpoint restart;
- one rewrite per successful lowering;
- `cmb` matcher-solution backtracking and condition counts;
- membership trace IDs, substitutions, and `Whole:` reconstruction;
- the no-membership fast path.

Both source loading and meta-level down-installation already use the same `Engine::add_membership` APIs; the
repair belongs below those entry points.

## Acceptance matrix

Retain the matrix in the ordinary membership-theory conformance fixture or a dedicated adjacent fixture. Every
row must compare directly with Maude 3.5.1.

| Case | Expected result | Rewrites | Contract defended |
|---|---|---:|---|
| ACU `mb a, S : Special`, subject `a` | `Special: a` | 1 | ACU identity collapse indexing |
| AU `mb a L : Special`, subject `a` | `Special: a` | 1 | AU two-sided identity collapse indexing |
| CUI `mb a * X : Special`, subject `a` | `Special: a` | 1 | CUI identity collapse indexing |
| Same CUI membership, subject `a * b` | `Special: a * b` | 2 | child collapse plus rooted application/count |
| CUI `mb g(X, X) : Special` with `[comm idem]`, subject `a` | `Special: a` | 1 | idempotent collapse indexing |
| `mb (s X) * Y : Special`, subject `s a` | `Special: s a` | 1 | collapse to an iter-rooted survivor |
| `cmb (s X) * Y : Special if X = a`, subject `s a` | `Special: s a` | 1 | conditional collapsed membership |
| `mb (a ; L) * Y : Special`, subject `a` | `Special: a` | 1 | recursive CUI-over-AU survivor |
| `mb (a * X) * Y : Special`, subject `a` | `Special: a` | 1 | recursive same-symbol survivor |
| `mb X * Y : Special`, subjects `a` and identity `z` | `Special` for both | 1 each | offer-to-kind and identity re-entry safety |
| Ground `mb a * b : Special`, subject `a` | unchanged `E: a` | 0 | conservative index has no false application |
| Sorted `wrap(S)` downstream control | `E: b` | 2 | missed membership no longer changes value |

Also retain the already-passing exotic controls:

- iter membership with a nested CUI-collapse operand;
- rooted CUI conditional membership with nested iter/nonlinear-AC operands;
- existing direct iter membership result/count matrix.

At least one collapsed-membership trace must show the original `mb`/`cmb`, collapse binding (including the
identity binding), old/new sorts, and stable statement ID exactly as Maude does.

## Focused verification

The implementation is not complete until all of the following pass:

1. live-oracle diff for the retained collapse-membership matrix;
2. the dedicated `tnk_011_collapsing_memberships_conform` matrix plus the existing `correctness_membership_theory_conforms` baseline;
3. existing membership-order tests, especially TNK-008's incomparable-target fixture;
4. existing CUI/ACU/AU equation-collapse fixtures, proving equation indexing did not regress;
5. existing iter and cross-theory membership fixtures;
6. membership and conditional-membership trace fixtures;
7. workspace tests after the focused behavior is green.

## Implementation record

- `Signature::memberships` is a dense arena containing each compiled constraint exactly once.
- `direct_memberships` indexes ordinary constraints by lhs top symbol; `collapsing_memberships` indexes
  collapse-capable constraints by result kind. Both store arena IDs.
- `add_membership` classifies ACU/two-sided-AU identity and CUI identity/idempotence from the compiled
  top symbol. One-sided AU is intentionally excluded.
- `constrain_node_with` merges direct and collapse ID slices without allocation using
  `membership_precedes`: descending component-local target-sort index, then declaration ID.
- Whole-match semantics, strict lowering/restart, condition backtracking, trace metadata, and the
  no-membership fast path remain unchanged.
- `conformance/audit/B3c-membership-collapse.maude` is the retained Maude 3.5.1 matrix. The focused
  frontend assertion checks every value/sort/count row; the REPL assertion checks downstream behavior
  and the collapsed identity-binding trace.

### Completion evidence

- `tools/diffmaude.sh conformance/audit/B3c-membership-collapse.maude -v` — exact oracle parity.
- `cargo test -q -p tnk-frontend tnk_011_collapsing_memberships_conform` — 1 passed.
- `cargo test -q -p tnk-repl collapsing_membership_fixture_through_repl` — 1 passed.
- `cargo test -q --workspace` — 458 passed across 12 suites.
- `tools/audit-scoreboard.sh` — `SCOREBOARD 89/89 PASS`.

## Explicit boundaries

This goal does **not** claim all possible identity theories are complete.

- Associative one-sided `left id:`/`right id:` collapsing memberships are a separate confirmed matcher gap.
  Even when an enclosing iter membership invokes the AU matcher directly, tnk does not let the legal edge
  identity disappear. Fixing that requires side-aware AU pattern compilation/enumeration, not only indexing.
- Diagnostic/advisory wording for “collapse at top” remains part of the diagnostics gap.
- Bare-variable memberships remain nonexecutive under the existing frontend rule.
- Equation/rule collapse indexing, unification, and variant behavior are unchanged.
- No new membership extension mode is introduced.

Closure wording must say “ACU/two-sided-AU/CUI collapsing membership indexing,” not “all collapse matching,”
until the one-sided AU follow-on has its own implementation and oracle matrix.

## Completion condition

TNK-011 is resolved only when the retained oracle matrix demonstrates correct values, sorts, counts,
conditional behavior, ordering, and trace identity; the compiled-constraint arena avoids per-symbol matcher
copies; existing membership/equation/iter gates remain green; and the stale residual comments are replaced by
the precise one-sided-AU boundary above.
