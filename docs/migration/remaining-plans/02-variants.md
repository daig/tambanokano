# Phase S2 — Variants (folding variant narrowing) — implementation record

**Status: DONE (2026-07-19).** `crates/tnk-core/src/variant.rs` owns the layered folding search,
subsumption, variant unification, and variant matching; `tnk-frontend` and `tnk-repl` expose every
object-level command and continuation; `tnk-modules/src/meta.rs` implements the current and legacy
meta surfaces with persistent caches. `tools/subsystems-scoreboard.sh -p V` verifies all 21 fixtures
(289 substantive commands) byte-for-byte against Maude 3.5.1. The frozen gates are simultaneously
green: audit 77/77, legacy 87/87, 394 release tests, and all three stock libraries. The staged plan
below preserves the preimplementation source/behavior map; present-tense “missing” claims are historical.

Ground truth used throughout: the reference source in `~/code/maude-lang/maude/src/Higher/` +
`Mixfix/` + `Meta/`, run live against the frozen fixtures `conformance/subsystems/V*.maude` via the
Yices2 oracle (`~/.local/bin/maude`, `MAUDE_LIB=~/code/maude-lang/maude/src/Main`). Every output
shape and number quoted below was produced by that oracle during this investigation.

---

## 1. Subsystem overview

**Commands** (REPL surface, all with an optional `[bound]` and an optional
`such that <t1>, …, <tn> irreducible` constraint suffix):

| command | reference driver | mode |
|---|---|---|
| `get variants [b] in M : t .` | `Mixfix/getVariants.cc` | incremental narrowing, folding |
| `get irredundant variants [b] in M : t .` | `Mixfix/getVariants.cc` | full narrowing up front, minimal set |
| `variant unify [b] in M : l =? r /\ … .` | `Mixfix/variantUnify.cc` | `UNIFICATION_MODE` |
| `filtered variant unify [b] in M : … .` | `Mixfix/variantUnify.cc` | `IRREDUNDANT_MODE`, minimal (most-general) unifiers |
| `variant match [b] in M : p <=? s .` | `Mixfix/variantMatch.cc` | `MATCH_MODE` |

**Meta functions** (all live through dedicated `MetaOp` variants and persistent caches in
`crates/tnk-modules/src/meta.rs`):

- `metaGetVariant(M, T, TermList, FamilyQid, Nat)` / `metaGetIrredundantVariant(…)` →
  `Variant?` (`{term, subst, familyQid, parentIndex, moreInLayer}` or `noVariant`) —
  `Meta/metaVariant.cc`.
- `metaVariantUnify(M, UnifProblem, TermList, FamilyQid, VariantOptionSet, Nat)` →
  `UnificationPair?` (`{subst, familyQid}`, or `noUnifier` / `noUnifierIncomplete`);
  `metaVariantDisjointUnify(…)` → `UnificationTriple?` — `Meta/metaVariantUnify.cc`.
- `metaVariantMatch(M, MatchProblem, GroundTermList, FamilyQid, VariantOptionSet, Nat)` →
  `Substitution?` — `Meta/metaVariantMatch.cc`.
- Legacy forms with a **Nat** family argument instead of a Qid
  (`Meta/legacyMetaVariant.cc`, `legacyMetaVariantUnify.cc`) — same result sorts.

**Role in the language.** Folding variant narrowing (Escobar–Sasse–Meseguer) computes the *variants*
of a term modulo an equational theory `E ∪ Ax` (equations flagged `[variant]`, applied as rules
modulo the built-in axioms `Ax`). For theories with the **finite variant property** (FVP) the set is
finite; the machinery also gives a bounded approximation for non-FVP theories. On top of variant
generation sit: **variant unification** (unify `l =? r` by narrowing `eq(l,r)` to `tt`, manual §14.8),
**variant matching** (rhs treated ground), and **filtered** unification (Escobar–Sapiña *most general
variant unifiers*). S2 is the substrate for S3 narrowing (which folds *states* the same way) and for
phase-T variant satisfiability (a `.maude` library over variant unification).

**What the 21 V\* fixtures exercise**:

- Free + AC only: `V01` (unify+irreducible), `V02` (match), `V05` (get variants + frozen args),
  `V06`/`V07` (meta get variant, Qid vs Int family), `V08`/`V10` (meta unify, Qid vs Int),
  `V11` (meta match), `V-ch14-01` (free, non-FVP, `[bound]`), `V-ch14-02` (AC XOR: 7 irredundant
  variants, irreducibility, filtered=1), `V-ch14-03` (mb ignored during narrowing),
  `V-ch14-05` (abelian group, **47**+4 irredundant variants — heavy eviction), `V-probe-01` (AC idem).
- AC + free with the *filtered* filter's nested search: `V03` (P1–P20), `V09` (delay/filter option
  flags via a recursive `getUnifiers` loop — the caching stress).
- ACU: `V-ch14-04` (vending machine: irredundant/plain/filtered/constrained unify + match).
- Associative A: `V-ch14-06` (`_:_ [assoc ctor]`, incomplete unification and warnings).
- Split reference-suite halves moved out of the S1 gate: `V12-check-variant-unifiers` (META A/AC/ACU),
  `V13-au-variant-unification` (18 AU commands from U05), and `V14-cu-variant-unification` (CUI commands
  from U08).
- `V04` is a large multi-module FVP battery (BOOL-FVP free; NAT-AC-MONUS AC; NAT-ACU-MONUS/INT-ACU
  ACU; INT-OFFSET-\* AC/ACU; HF-SETS AC; NAT-PRES AC/ACU) with `[1]`/`[23]` bounds.

---

## 2. Reference approach (folding variant narrowing)

### 2.1 The engine: `VariantSearch` (`Higher/variantSearch.{hh,cc}`)

One class, parameterized by a `Flags` bitmask (`variantSearch.hh:45-54`:
`UNIFICATION_MODE`, `IRREDUNDANT_MODE`, `SUBSUMPTION_MODE`, `MATCH_MODE`, `CHECK_VARIABLE_NAMES`,
plus GC-ownership bits). It is a **layered breadth-first variant narrowing** with a folder.

Constructor (`variantSearch.cc:119-333`):
1. Copy + index-variables the target dag (`:143-151`); `nrVariantVariables` = its variable count.
2. If `CHECK_VARIABLE_NAMES`, reject a target/blocker variable whose name collides with the fresh
   range (`:162-206`, the "unsafe variable name … in variant narrowing problem" warning — see
   `V06`'s `%1:XOR` case which returns `noVariant`).
3. Rename each original variable to a fresh **`firstVariableFamily`** variable, reduce the result to
   normal form, and insert it as **variant 0** (the reflexive variant), parent `NONE`
   (`:213-296`). In `UNIFICATION_MODE`, if the two sides are already equal it inserts the trivial
   unifier and stops (`:248-270`).
4. `frontier = [0]`, `currentIndex = 1`, `useFirstVariableFamily = false`.
5. If `IRREDUNDANT_MODE | SUBSUMPTION_MODE | MATCH_MODE`: expand **all** layers up front
   (`do expandLayer() while !frontier.empty()`, `:305-332`) so no already-emitted variant can later
   be evicted; `MATCH_MODE` also compiles matching automata (`prepareForVariantMatching`).

`expandLayer` (`:397-421`) narrows every surviving variant in the current frontier by one step, swaps
in the new frontier, and **toggles `useFirstVariableFamily`** — so the fresh-variable family
*alternates per layer*. `expandVariant` (`:423-509`) drives the per-node narrowing and reduces each
new variant term before folding it in.

### 2.2 The two variable families (conformance-load-bearing)

`variantSearch.cc:128-129`:
```
firstVariableFamily  = (incomingVariableFamily == 0) ? 1 : 0;
secondVariableFamily = (incomingVariableFamily == 2 || incomingVariableFamily == NONE) ? 1 : 2;
```
Families are `#`=0 (unify), `%`=1 (variant), `@`=2 (narrow) — same ordering as tnk's
`fresh.rs::VariableFamily`. `incomingVariableFamily` is the family the **caller reserves** (its own
variables might be in it), so the search must *avoid* it: the command passes `NONE`; the meta passes
the Qid argument's family (so at the meta level the Qid is a *disallowed* family, not the family to
use). Layer *k* uses: layer 0 (reflexive) = `firstVariableFamily`; then layers alternate
`second, first, second, …` (because `useFirstVariableFamily` starts `false` and flips each
`expandLayer`).

Verified against four independent fixtures:
- `get variants` (incoming `NONE` → first `#`, second `%`): reflexive `#`, layers `%,#,%,…`
  (`V-ch14-01` variants 1/3/5/7 = `#1`,`%1`,`#1`,`%1`; probe variant 1 `#`, variant 2 `%`).
- `metaGetVariant(…, '#, …)` (incoming `#`=0 → first `%`, second `@`): variant 0 uses `%`, layer-1
  variants use `@` (`V06`). `metaGetVariant(…, '@, …)` (incoming `@`=2 → first `#`): variant 0 uses
  `#` (`V06`).
- `metaVariantUnify(…, '#, …)`: index-0 unifier from the first narrowing layer uses `@` (second
  family), index-2 uses `%` (first family) — `V08`.

Within a variant, fresh variables restart at 1 in the layer's family and are numbered in
variable-index (first-encounter) order — the same variable-ordering S1 already reproduces for
unifiers. tnk's `FreshVariableGenerator::fresh_name(index, family)` (`fresh.rs:85`) already prints
`<prefix><index+1>`.

### 2.3 One-step variant narrowing: `VariantNarrowingSearchState` (`Higher/variantNarrowingSearchState.cc`)

For a variant `(term, subst)`:
- Index variables above the module's variables (`:98-99`); the variables of the *term* are the
  "interesting" ones. A `UnifierFilter(firstTargetSlot, nrInterestingVariables)` (`:112`) keeps only
  unifiers most-general on the interesting variables (this is `Higher/unifierFilter.cc`, the same
  filter that backs S1 `irredundant unify`).
- In `UNIFICATION_MODE`, also unify the two sides of the pairing directly (`:117-140`) — a "virtual
  rewrite to tt" that yields a variant *unifier* (position 0, equation `NONE`).
- For every **non-variable position** in the term (`:142-179`), for every executable module
  equation with the **`[variant]` attribute** whose lhs is in the right kind, build a
  `NarrowingUnificationProblem` (= full order-sorted `E∪Ax` unification of the subterm and the eq
  lhs) and collect its unifiers into the filter.
- Reducibility pruning (`:216-227` and `:253-267`): discard a unifier if any interesting-variable
  binding of the accumulated substitution is `reducibleByVariantEquation` — i.e. still contains a
  variant-equation redex. This is the finite-variant folding condition. Also (`:272-289`) discard if
  instantiating a **blocker dag** (the `such that … irreducible` constraint) becomes reducible.
- `findNextVariant` (`:238-358`) then, per surviving unifier: computes the accumulated substitution
  `subst ∘ unifier`, and for an equation index builds the narrowed term = eq rhs instantiated with the
  redex replaced at the position (`rebuildAndInstantiateDag`, `:317`); for equation `NONE` (unify
  mode) returns a null term signalling a unifier.

### 2.4 The folder: `VariantFolder` (`Higher/variantFolder.{hh,cc}`)

A `map<int, RetainedVariant*>` (`mostGeneralSoFar`, keyed by dense generation index). A variant is
stored as a `Vector<DagNode*>` = *[substitution bindings…, variant term]* and treated uniformly.

- `insertVariant(variant, index, parentIndex, family)` (`:83-170`): (1) if the variant `isSubsumed`
  by an existing one, drop it (return false — it is *not* expanded). (2) Otherwise compile it and
  **evict** every non-ancestor variant it subsumes, *plus* the descendants of anything evicted
  (`existingVariantsSubsumed` propagation across the index-ordered map, `:108-153`) — the ancestor
  guard stops a variant evicting its own lineage. Returns true (→ added to the frontier).
- `subsumes(retained, variant)` (`:172-220`) = **matching modulo axioms**: it matches the retained
  variant's compiled `LhsAutomaton`s (built in reverse, term part first — `:334-405`) against the new
  variant's dags with **one shared** substitution across all components (`SubproblemAccumulator`). So
  "retained subsumes new" ⟺ "new is an `Ax`-instance of retained on term *and* substitution jointly".
- `findNextSurvivingVariant` (`:222-233`) walks the map by increasing index; `getCurrentVariant`
  (`:235-263`) returns the family + `parentIndex` + `moreInLayer` (next surviving variant is in the
  same `layerNumber`).

`VariantSearch::findNextVariant` (`variantSearch.cc:88-117`) assigns external display numbers
0,1,2,… to survivors in surviving-index order (`internalIndexToExternalIndex`), which is BFS/layer
order. Internal indices are dense over *all* generated variants (including subsumed ones), so external
"Variant N" = the N-th survivor.

### 2.5 Unify / filtered / match layers

- **Plain `variant unify`** = `VariantSearch` in `UNIFICATION_MODE`; `findNextUnifier`
  (`variantSearch.cc:57-80`) walks survivors whose vector length equals `nrVariantVariables` (a
  variant with a fully-solved term is a unifier).
- **`filtered variant unify`** = `FilteredVariantUnifierSearch : public VariantSearch`
  (`filteredVariantUnifierSearch.cc`): collect all plain unifiers, then a `VariantUnifierFilter`
  (`variantUnifierFilter.{hh,cc}`) keeps a minimal set under **`E∪Ax`-subsumption** — each retained
  unifier owns its *own* `VariantSearch` in `SUBSUMPTION_MODE` over the encoded unifier tuple, and
  `retained.subsumes(other) = variants->isSubsumed(other)` (`variantUnifierFilter.hh:110-114`). This
  is strictly stronger than the folder's `Ax`-subsumption; it can be incomplete (→ "Filtering was
  incomplete" advisory).
- **`variant match`** = `MATCH_MODE`: full variant set up front, then `VariantMatchingProblem`
  (`variantMatchingProblem.cc:112-196`) matches the (ground-treated) subject against each retained
  variant's *term*, and fills any variant-substitution variable not bound by the term match with a
  fresh **`#` (family 0)** variable avoiding those already in the subject (`:78-103`, `:143-181`).

### 2.6 Output / protocol semantics that must be byte-exact

- Commands echo, then per result: `Variant N` / `Unifier N` / `Matcher N`, then (non-irredundant /
  non-filtered only) a per-result `rewrites: …` line, then `<Sort>: <term>` (variants only) and the
  substitution lines `<var> --> <binding>`. Terminators: `No variants.`/`No more variants.`,
  `No unifiers.`/`No more unifiers.`, `No matchers.`/`No more matchers.`
  (`getVariants.cc:112-204`, `variantUnify.cc:124-239`, `variantMatch.cc`).
- **Stats placement**: irredundant/filtered/match print `rewrites: …` **once** right after the echo
  (all work is up front — `getVariants.cc:96-102`, `variantUnify.cc:108-114`); plain get-variants and
  plain unify print `rewrites: …` **per result** and a final total. The rewrite counts are not the
  timing tail the harness strips — they must match.
- **Incompleteness**: emits `Warning: …incomplete unification algorithm(s)` and (per instance)
  `Warning: Unification modulo the theory of operator _:_ …` — **the diff harness strips all
  `Warning:`/`Advisory:` lines**, so at the *command* level incompleteness affects only *which*
  variants appear, not visible text. At the *meta* level it is load-bearing: `metaVariantUnify`
  returns `noUnifierIncomplete` vs `noUnifier` (distinguished in `V09`), and `upNoVariant(incomplete)`.
- Memberships are **not** used during narrowing (`V-ch14-03`: `X:Empty * Y:Empty` gives 2 variants;
  the `mb mt : Empty` does not instantiate variables to `mt`) — narrowing uses `[variant]` equations
  only; sorts come from the sort machinery.
- Meta encodings (verified live): `Variant` = `{term, subst, familyQid, parentIndex, moreInLayer}`
  (`V06`); `UnificationPair` = `{subst, familyQid}`, `UnificationTriple` adds the disjoint-rename
  (`V08`) — **identical shape to S1's `metaUnify` results**, only the family qid varies by layer.

---

## 3. What tnk already has to build on

- **The E∪Ax-unification primitive** — `crates/tnk-core/src/unify/problem.rs`:
  `UnifyProblem::new(env, equations: Vec<(DagId,DagId)>, specs: Vec<VarSpec>, family, base:&str)`
  (`:81`), `find_next(env) -> Option<Vec<DagId>>` (`:153`), `is_incomplete()` (`:135`),
  `nr_free_variables()` (`:140`), `last_var_index_decimal()` (`:147`), `gc_roots()` (`:329`). This *is*
  `NarrowingUnificationProblem`: to narrow, unify one variant-eq lhs against one subterm with the
  layer's `family` and a `base` above the module's variables. Free/variable/S/CUI/AC/ACU/A/AU are all
  complete and sequence-verified by S1. `UnifyEnv`/`NameCodes` provide the required family/base control.
- **The folding primitive** — `crates/tnk-core/src/unify/filter.rs`: `subsumes(e, retained, candidate)`
  (`:69-87`) already implements *"candidate is an `E`-instance of retained modulo the theory"* by
  re-slotting `retained`'s variables and **freezing** `candidate`'s variables to fresh ground
  constants, then reusing `UnifyProblem` — one-sided unification = matching modulo axioms. `irredundant`
  (`:30-49`) is the drop-if-subsumed / evict-then-append loop. This generalizes directly to variant
  folding: extend the binding vector with the variant *term* as one more component and run the same
  joint test. The filter file's own doc-comment already notes it is "closely related to variant
  folding's most-general test".
- **The irredundant unifier filter** — the same `filter.rs::irredundant` is exactly the
  `UnifierFilter` that `VariantNarrowingSearchState` uses to keep most-general unifiers per step.
- **Fresh-variable families** — `crates/tnk-core/src/fresh.rs`: the single generator with `#`/`%`/`@`
  families, `variable_name_conflict` (the `CHECK_VARIABLE_NAMES` warning), `parse_fresh_name`,
  `belongs_to_family`, and a `base_number` for meta counter resumption. The `%` family is already
  reserved for variants (comment at `fresh.rs:1-13`).
- **The descent seam + reused meta encoders** — `crates/tnk-core/src/descent.rs` (`DescentOps`,
  `MetaCtx`) and `crates/tnk-modules/src/meta.rs`: `metaSearch` (`:460-498`) is the template — down
  module + terms, run an engine op, up-encode. **The S1 meta up-encoders for `UnificationPair` /
  `UnificationTriple` / `noUnifier` / `noUnifierIncomplete` already exist** (metaUnify is done) and are
  reused verbatim; only `upVariant` / `upNoVariant` and the `VariantOptionSet` (delay/filter)
  down-translation are new. `VariableFamily` is already threaded through meta up-encoding
  (`meta.rs:317-325`). S1 added a specialized `MetaUnifyCache`, but it lives only for one
  `MetaDescent`/top-level reduction and keys by dag identity. S2 needs the reference's persistent,
  structurally keyed, bounded cached-state behavior across top-level commands and repeated calls inside
  one reduction (see §5, V06/V09/V12); `metaSearch` still recomputes from index 0.
- **The command/continuation driver** — `crates/tnk-repl/src/lib.rs`: the `Continuation` enum
  (`:87-96`, `Rewrite`/`Search`) + `SearchSession` + `run_search_session` (`:999-1013`) are the
  `[bound]`/`continue` template; the `Command::Unify` arm (`:598-655`) already collects unifiers up to
  a bound, runs the `filter::irredundant` path, and renders via `render_unifier`. `unify_command` /
  `UnifyCommand` / `render_unifier` live in `crates/tnk-frontend/src/load.rs:1085-1187`.
- **Lazy-BFS + GC template** — `crates/tnk-core/src/search.rs`: `Search` with a `frontier: VecDeque`,
  `next_solution`, `state_term`, `path`, `graph`, and a `RootGuard` pinned per discovered state
  (`:36,105,202`). `crates/tnk-core/src/root.rs` + `engine.rs:2205-2222` give `engine.root(id)`
  (RAII `RootGuard`) and `gc(extra_roots)`.

---

## 4. Architectural fit & divergence analysis

- **VariantSearch → a lazy folding iterator.** Model it as a Rust struct owning: the target's
  `NarrowingVariableInfo` (variable order), the `VariantFolder`, a `frontier: Vec<usize>`, `currentIndex`,
  `useFirstVariableFamily`, the two computed families, and the `is_incomplete` accumulator. `findNextVariant`
  / `findNextUnifier` are `Option`-returning methods (A8's "iterator" recommendation). The four modes
  are best expressed as thin adapters over a shared core (A8 §2): plain-generate, unify (adds the
  two-sides unification + length test), match (full-set + a matcher), filtered (full-set + the unifier
  filter) — this removes the pervasive `if (flags & …)` and makes each surface statically distinct.
- **VariantFolder → `BTreeMap<usize, RetainedVariant>`.** Dense `usize` indices (children > parents).
  Descendant eviction is the same forward-pass-with-`parentIndex`-propagation as the C++ (a `BTreeMap`
  iterates in key order, so a parent is always visited before its child). `moreInLayer` from
  `layerNumber = parent.layer + 1`. Each `RetainedVariant` holds its dag vector plus **`RootGuard`s**
  pinning those dags; dropping the `RetainedVariant` on eviction releases them — the GC discipline the
  roadmap risk register item 9 asks for, and exactly how `search.rs` already pins states. The variant
  frontier + folder is the explicit discoverable root set at command boundaries (D2).
- **Folder subsumption must use genuine matching modulo axioms.** Maude's folder matches the retained
  `[bindings…, term]` vector against the candidate with one shared substitution and may produce an
  associative extension. Frozen-subject unification is not an equivalent implementation: Maude's
  associative unifier is intentionally incomplete while its associative matcher is complete. S1
  completed the kernel matching arms for Free/ACU/AU/CUI/S, including one-sided identity collapse.
  Reuse/generalize that matching machinery for conjunctions over the whole vector. Keep `filter.rs`
  for its actual job — filtering step unifiers — rather than making it the folder primitive.
- **Fresh-variable family reservation.** `%` (family 1) is reserved for variants and `@` (family 2)
  for narrowing already; the two-family alternation uses `{first, second}` drawn from the three
  families avoiding `incomingVariableFamily`. No new family machinery — `fresh.rs` is sufficient; the
  variant layer only chooses *which* family index to pass to `UnifyProblem::new` per layer, and drives
  `base` to restart numbering per variant.
- **New primitives tnk must add (do not exist today):**
  1. The `[variant]` **equation attribute** — not parsed/stored today (no flag on the surface or compiled
     equation). Parse and preserve it through flattening, renaming, views, compilation, and
     `upModule`/down-module reflection; `V06` compares named-module and `upModule` calls directly.
     Expose only executable (not `[nonexec]`) variant equations to narrowing/reducibility.
  2. `reducibleByVariantEquation(dag)` — "does any `[variant]` equation lhs match (modulo axioms) at
     any subterm". A matching-*existence* query restricted to variant equations. tnk has a reduce loop
     but no exposed "is there a redex for this equation subset" primitive; this is a focused addition
     (walk positions, try each variant-eq lhs matcher).
  3. A **dag position iterator** (`PositionState` analog) — enumerate non-variable subterm positions
     of the variant term, and a position-addressed rebuild (`rebuildAndInstantiateDag` analog) to
     construct the narrowed term. tnk builds dags but has no generic position-addressed replace for
     symbolic use.
  4. **Command grammar + `Command` arms** — `get [irredundant] variants`, `[filtered] variant unify`,
     `variant match`, each with `[bound]` and the `such that … irreducible` constraint (the existing
     `Command::Unify` has `bound`/`irredundant` but no constraint). Today `variant unify` mis-parses
     as plain `Command::Unify` (verified: the probe echoes `unify …` and uses `#1`, not `%1`); this is
     an accidental partial acceptance, not a stub, and must be replaced.
  5. Split the `metaVariant*` ops out of `MetaOp::Deferred` into real `MetaOp` variants
     (`symbol.rs:300-347`), mirroring how S1 split out `MetaOp::Unify`.

---

## 5. Feasibility & risk

**Overall: feasible and well-supported by the completed S1, with variant-search/folder ordering and
persistent meta-state as the main risks.** All 21 fixtures now have their unification prerequisites.
The unifier, matcher arms, families, GC, and command-driver templates exist.

- **AU dependency — closed.** The A/AU solver, identity/collapse behavior, incompleteness flag, and
  exact pre-filter sequence pass the S1 gate. The same S1 work completed the A/AU matcher, so folding
  has a genuine complete matching path instead of depending on frozen-subject unification.
- **Associative folding remains the deepest algorithmic check (V-ch14-06/V13).** Maude uses complete
  matching modulo A/AU for folding but its deliberately incomplete A-unification sequence for each
  narrowing step. Preserve that split: call the kernel matcher for folder subsumption and
  `reducibleByVariantEquation`, and call `UnifyProblem` for narrowing. The missing Rust primitive is
  shared-substitution conjunction matching over `[bindings…, term]`, including associative extension;
  it is an S2 composition layer over existing matchers, not another unifier.
- **Numbering / order byte-exactness (all fixtures).** The family alternation, per-variant restart of
  fresh numbering, external survivor numbering, `parentIndex`/`moreInLayer`, and the per-result vs
  up-front `rewrites:` counts are all observable. The families and variable ordering reduce to S1
  mechanisms already verified; the rewrite counts come from the existing reduce engine. Risk is
  moderate and handled by the sequence-level cross-check (§7). The `get variants` (non-irredundant)
  incremental mode *can* emit a variant that a later layer would evict — confirm no fixture depends on
  a post-emission eviction (the FVP fixtures are irredundant/converge; `V-ch14-01`/`V04` bounded
  approximations are the ones to watch).
- **Filtered unify's nested search (`V03`, `V-ch14-04`, parts of `V09`).** `VariantUnifierFilter`
  spins up a fresh `SUBSUMPTION_MODE VariantSearch` per retained unifier — a recursive use of the whole
  engine. Correct but heavy; `V03` deliberately comments out P9/P10/P13 as "too slow", so the fixture
  target is only the fast subset — tnk must match those and no worse. `V-ch14-05` (47 irredundant
  variants) stresses eviction throughput but not the nested filter.
- **Persistent meta-state is required, not an optional optimization (V06/V09/V12).** The reference
  `MetaOpCache` retains four search states, compares the meta operation's useful arguments
  structurally (not by dag id), ignores the solution-index tail, resumes when
  `lastSolutionNr <= requested`, and restarts when the caller asks for an earlier index. This behavior
  is byte-visible in rewrite counts: the live oracle reports 3 rewrites for V06's first
  `metaGetVariant` result and 6 for the resumed second result. It is also necessary for termination:
  V09 and V12 repeatedly call the same indexed operation within recursive equations and currently
  exceed 60 seconds. Generalize/move the S1 cache so it survives top-level commands, supports at least
  the reference's four interleaved states, roots its structural keys and search dags for GC, and
  transfers only newly performed rewrite counts into each outer reduction. Dag-id identity and a
  single `Option` cache are both insufficient.
- **Termination.** FVP theories converge because folding + the interesting-variable reducibility check
  bound the search; non-FVP theories (`V-ch14-01`, some `V04`) rely on the user `[bound]` and the
  continuation. The reducibility-pruning check (`reducibleByVariantEquation`) is what makes FVP finite —
  getting it right is essential to avoid non-termination.

---

## 6. Implementation plan (staged; smallest vertical slice first)

**S2.0 — plumbing (no algorithm yet).**
- Parse + preserve the `[variant]` equation attribute through module transforms, compilation, and
  meta `upModule`/down-module round trips; expose the executable-variant-equation set.
- Add the command grammar + `Command` arms for `get [irredundant] variants`,
  `[filtered] variant unify`, `variant match`, each with `[bound]` and `such that … irreducible`.
- Extend `tools/diffmaude-command.py`'s command-start recognition for those forms. It currently sees
  210 of the V corpus's 289 top-level substantive commands and silently omits 79 `get`/`filtered`/
  `variant match` commands from command isolation.
- Split `metaVariant*` (and legacy forms) out of `MetaOp::Deferred` into real `MetaOp` variants
  (still returning `None` until wired) so dispatch is explicit.
- Gate: F1–F4 stay green; fixtures still FAIL but now via the real command path.

**S2.1 — core folding + `get variants` (the first verifiable slice).**
- Position iterator over the variant term + `reducibleByVariantEquation`.
- One-step `VariantNarrowingSearchState`: per position × variant-eq, `UnifyProblem` (layer family +
  base), collect through the generalized `filter.rs` unifier filter, prune by interesting-variable
  reducibility and by blocker dags, build the narrowed term by position-addressed rebuild.
- `VariantFolder` (`BTreeMap`, generalized `subsumes` over `[bindings…, term]`, ancestor-guarded
  descendant eviction, `RootGuard` pins, `layerNumber`/`moreInLayer`).
- `VariantSearch` driver: reflexive variant (rename → reduce → insert as index 0, `firstVariableFamily`),
  layered BFS with the family toggle, incremental (`get variants`) vs up-front (`get irredundant
  variants`) expansion, external survivor numbering, incompleteness OR.
- Wire `get variants` / `get irredundant variants` output (per-result vs up-front stats) + the
  `[bound]`→`continue` continuation (new `Continuation::Variant`).
- **First green fixtures:** `V-probe-01`, `V-ch14-01`, `V-ch14-02` (irredundant + irreducible),
  `V-ch14-03` (mb ignored), `V-ch14-05` (47 variants — eviction), and the `get variants` parts of
  `V04`/`V05`.

**S2.2 — `variant unify` + `filtered variant unify`.**
- `UNIFICATION_MODE`: identity-unifier short-circuit; per step also unify the two sides directly;
  `findNextUnifier` = survivors with fully-solved term. Plain unify + `[bound]`/continue.
- `filtered`: `VariantUnifierFilter` with a nested `SUBSUMPTION_MODE VariantSearch` per retained
  unifier (`E∪Ax`-subsumption); up-front stats; "Filtering was complete/incomplete" (stripped).
- **Fixtures:** `V01`, `V03`, `V-ch14-02` (filtered=1), `V-ch14-04` (plain/filtered/constrained),
  `V-probe-01` unify, and `V14` (CUI enumeration/order).

**S2.3 — `variant match`.**
- `MATCH_MODE`: full variant set up front; match the ground-treated subject against each retained
  variant's term; fill unbound variant-substitution variables with fresh `#`-family variables avoiding
  subject variables.
- **Fixtures:** `V02`, `V-ch14-04` match.

**S2.4 — meta family + persistent indexed state.**
- `metaGetVariant` / `metaGetIrredundantVariant`, `metaVariantUnify` /
  `metaVariantDisjointUnify`, `metaVariantMatch`, + the legacy Int-family forms. Reuse S1 up-encoders
  for `UnificationPair`/`Triple`/`noUnifier`/`noUnifierIncomplete`; add `upVariant`/`upNoVariant` and
  the `VariantOptionSet` (delay/filter) down-translation; compute the result family qid from the
  surviving variant.
- Land the four-entry, structurally keyed, GC-rooted state cache with this slice. Resume forward
  indexes, reuse equal indexes without advancing, restart backward indexes, and transfer incremental
  rewrite counts exactly. Do not stage a recompute-from-0 version: it cannot satisfy V06 counts and
  V09/V12 termination.
- **Fixtures:** `V06`,`V07`,`V08`,`V10`,`V11`,`V12`, then the recursive cache stress in `V09`.

**S2.5 — associative (`V-ch14-06`, `V13`).**
- Compose the completed S1 A/AU unifier for narrowing with the completed A/AU matcher for folding and
  reducibility. Validate Maude's intentionally incomplete unifier sequence separately from complete
  fold matching. Highest-risk S2 slice; do after the free/AC/ACU sequence is stable.

---

## 7. Verification

- **Oracle diff.** All **21 V fixtures / 289 top-level substantive commands** through
  `tools/subsystems-scoreboard.sh -p V` (wraps `tools/diffmaude.sh`, 60s/fixture, byte-exact modulo
  the stripped set: separators, banner, timing tails, and `Warning:`/`Advisory:` blocks). The
  command-isolation helper must recognize all 289 before sequence debugging is considered trustworthy.
  The stripped `Warning:` lines mean command-level incompleteness is validated only through *which*
  variants appear; meta-level `noUnifier`/`noUnifierIncomplete` is validated directly.
- **Sequence-level unit tests** (the discipline that closed S1 / the AC matcher): assert the emitted
  variant *sequence* — for each variant the (term, substitution, family, parentIndex, moreInLayer)
  tuple in order — on small theories (IDEM, XOR, NAT-VARIANT) where the expected sequence is copied
  from the oracle. Same for unifier and matcher sequences and for the meta indexed accessors.
- **Naive cross-check** (Diophantine-port pattern, keep live until byte-conformant): a brute-force
  variant enumerator — narrow without folding to a depth bound, then post-filter with the same
  `subsumes` primitive — must yield the same *set* as the folding search on FVP theories; the folding
  search must additionally match the *order/numbering*. This isolates folding/eviction bugs from
  unification bugs.
- **Regression net.** F1 (`audit-scoreboard.sh` 77/77), F2 (`legacy-sweep.sh` 87/87), F3
  (`cargo test --release`), F4 (stock libraries) green at every commit; fixtures land with their
  now-passing feature (working rules §4).

### S2 completion gate

S2 is complete only when all of the following hold on the same working tree:

1. `tools/subsystems-scoreboard.sh -p V` reports **21/21 PASS**, with no timeout and no fixture or
   substantive command removed or weakened.
2. `tools/audit-scoreboard.sh` remains **77/77**, `tools/legacy-sweep.sh` remains **87/87**,
   `cargo test --release` passes, and the stock libraries still load through tnk.
3. The frozen V fixtures pin the variant, unifier, matcher, family/parent/layer, incomplete-result,
   continuation, and forward/equal/backward meta-cache sequences directly against the live oracle.
4. Every S2 command and `metaVariant*` hook reaches the real implementation; there is no accidental
   plain-`unify` parse, deferred hook, recompute-from-zero fallback, or fixture-specific branch.
5. The migration status ledger is refreshed with the observed fixture/command totals and any
   deliberately accepted divergence. S2 has no planned accepted divergence.

---

## 8. Resolved constraints and remaining implementation checks

1. **Meta variant-search state caching is mandatory.** Use the reference-equivalent four-entry,
   structurally compared, forward-resuming cache described in §5. Cache capacity, key equality,
   backward-index restart, GC rooting, and incremental rewrite-count transfer are correctness
   requirements, not tuning choices.
2. **Folding subsumption for A/AU uses genuine matching modulo axioms.** Frozen-subject unification is
   ruled out because its completeness contract differs. Generalize the completed matcher to solve the
   retained vector under one substitution and validate it on `V-ch14-06`/`V13`.
3. **Reproducing Maude's incomplete A-unification enumeration (V-ch14-06).** Byte-exact match to
   Maude's incomplete associative unifier order/count remains the least-canonical target in the
   suite. If the S1 solver diverges under the S2 narrowing call pattern, fix it or escalate under the
   D9 rule; never pin a Rust-only sequence.
4. **Modes may be adapters or an internal enum.** This is an implementation choice provided the
   observable contracts stay distinct: incremental plain generation, full-set irredundant/match,
   term-only subsumption folding, and full retained-unifier filtering. Do not encode behavior in
   unrelated REPL flags.
5. **Share primitives with S3, not search policy.** Make position walking, rebuild/instantiate,
   reducibility, joint matching, and folder subsumption reusable. S3 folds whole narrowing states and
   has a different graph/continuation contract, so do not force both searches into one state type.
