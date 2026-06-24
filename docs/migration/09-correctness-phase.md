# Phase 1.5 — Evaluator Correctness (audit & fixes)

**A dedicated correctness-hardening phase between Phase 1 (complete) and Phase 2 (parameterized
programming + rules + the real prelude).** Phase 1 made the evaluator *broad* and conformance-verified on
idiomatic modules; this phase makes it *faithful in the corners* — it differential-audits the engine
against the reference binary and fixes divergences (results, sorts, rewrite counts, termination, **and the
parse/print fidelity needed for byte-identical I/O**) **before** Phase 2 builds new machinery on top.

**Why now, not later.** Every divergence here is *cheapest to fix today*: the codebase is the smallest it
will ever be, the analysis is in-context, and Phase 2 will add code in the same reduce-loop / matcher /
pretty-printer neighborhood — so a fix made *after* rules forces re-verifying rules too. None of these
block *idiomatic* code (that's why Phase 1 passed), but they are **release blockers** for a "byte-identical
to the reference" engine, and the panicking one (C8) blocks a textbook spec class outright.

> **STATUS.** Done so far: **C1** (eager→lazy `mb` sort model, commit `160b956`), **C8** (cross-theory
> alien matching: ACU `75454a9` / AU `f2b025d` / free `4a0cea6`), **C5** (theory-lhs membership matching —
> covered by C8's shared seam), and **C9 / C10 / C11** (the frontend-fidelity cluster — float / glued-minus /
> rational printing; the command echo now pretty-prints the normalized parsed term, as Maude does), and
> **C12** (the pretty-printer's deep-chain stack overflow → iterative work-stack; `fib(22)` now prints), and
> **C6 / F-2** (engine-global condition-reduce GC root set — bounded-memory re-entrant conditions, a Phase-2
> `rew`/`search` prerequisite). **Every probe is now resolved:** **C2** struck (Maude loops on `eq a = a` too —
> the F-1 guard would *diverge*), **C3** verified (we match on every well-formed order-dependent case), **C4**
> done for single-top kinds (`[Nat]`); all §2.3. **Open = only idiom-rare residuals:** **C13** (long-output
> line-wrapping, lowest), **C7** (subject-DAG sharing, count-only), and the shared C3/C4 multi-top
> component-index order (Maude's unported `ConnectedComponent` sort index). The
> as-built records are the commits
> + `08-full-trace-plan.md` §status + the code; this doc tracks **pending** work + the confirmed residual edges.

Read order: this doc → `07-stageB-plan.md` §"Deferred follow-ups" (the parked B1 matcher items behind C8)
→ the cited code seams.

---

## 1. Methodology (carried forward from the Phase-0/Stage-A discipline)

- **Differential testing against the reference binary** is the oracle, not memory or reasoning. Each
  candidate becomes a minimal `.maude` module run through both `~/Downloads/Maude-3/maude -no-banner <f> <
  /dev/null` and our REPL/engine, diffing **result value, result sort, rewrite count, and termination**.
- **Two tracks, both in scope here.** (a) *Evaluator semantics* — the same normal form, least sort,
  `rewrites:` count, and halting as Maude (C2–C8, the core of the phase). (b) *Frontend fidelity* — the
  lexer accepts what Maude accepts and the pretty-printer prints what Maude prints, byte-for-byte (C9–C11).
  Track (b) lives entirely in `tnk-frontend` (lexer + pretty-printer); the value is always already correct,
  only the surface text/parse differs. (Pure cosmetic items with *no* fidelity goal — e.g. ACU print-order
  — stay noted in `08`, not here.)
- **Each item is written up as:** problem + reproducing evidence → root cause (file:line, both sides) →
  fix sketch → boundary (which modules it affects, which it provably doesn't).
- **Boundary honesty.** State precisely which class of modules each divergence affects, so the fix's value
  (and the cost of punting) is grounded, not guessed.

---

## 2. Known correctness issues (pending)

All confirmed items and probes are now resolved (C1/C5/C8/C9/C10/C11/C12 done, C6/F-2 done, C2 struck, C3
verified, C4 done for single-top kinds); only idiom-rare residuals remain (C7, C13, the C3/C4 multi-top
order). The entries below are kept as the as-built record + the residual boundaries. C-numbers are stable
discovery-order IDs, not priority ranks.

### 2.1 Confirmed — evaluator

#### C8 — Cross-theory "alien subterm" matching  **[DONE — was a HIGH-severity panic]**

A pattern lhs with a **non-ground, non-variable subterm under any theory operator** (AC/AU/S/CUI) — or a
theory-rooted subterm under a free operator — (an "alien" in Maude's terms) was unsupported: a **loud panic
at module load**. The parked B1 cross-theory-composition follow-up (`07-stageB-plan.md` §"Deferred
follow-ups"; loud-guarded, never silently wrong — audit F-A). Maude matches each alien recursively via its
own `LhsAutomaton` (`NonGroundAlien`), composing the child subproblems into the shared substitution. **Now
uniform across all five axes** — alien under ACU / AU / S / CUI, and theory-under-free.

The matching **order is from the source, not tuned**: for `reduce`, `ACU_GreedyMatcher` scans the subject's
canonically-sorted args (`findFirstPotentialMatch` + the `partialCompare … != LESS` walk) and binds each
alien to the **first (smallest) matching element**, which fixes the rewrite count. The full Diophantine
subproblem is the backtracking closure for `match`/conditions (set-compared, so order-free there).

- **ACU direction — DONE.** Alien subterms under an ACU op (`eq s M + N = s (M + N)`, textbook commutative
  Peano `+`/`*`) and theory-rooted subterms under an ACU op (`eq (a + b) ; c = d`) match. `acu.rs` gained an
  `AcuAlien` category + a greedy-first backtracking enumerator (single alien + collector, multiple aliens,
  multiplicities, non-linear-across-levels via binding-subtraction, identity, extension). Verified vs the
  reference — reduce **counts** + `match` **sets** — `conformance/correctness-ac-alien.maude` (2/3/3/4/4, 8/13).
- **AU direction — DONE.** Aliens under an `assoc` op (`eq (s M) L = M L`, list/sequence processing),
  multiple aliens (`eq (s M)(s N) = …`), and **non-linear** AU variables (`eq X X = X`) match. `au.rs` gained
  an `Alien` element + a `complex` binding-aware path (`rec_complex`) parallel to the pure positional one,
  with the matched-size-0 identity no-op skipped (it otherwise rewrites a term to itself forever — the AU
  analog of the ACU skip). Verified vs the reference — `conformance/correctness-au-alien.maude`. The order
  (leftmost-alien / maximal-collector) falls out of ascending enumeration + the stable maximal-matched-first
  sort = Maude's greedy order.
- **Free-top direction — DONE.** A theory-rooted subterm under a free op (`eq f(a X) = X` AU, `eq g(a ; X)
  = X` AC, `eq h(a X, b Y) = X Y` two aliens) now matches. The `theory.rs:65` guard is gone:
  `Runtime::match_skeleton` matches the free skeleton + binds variables and collects the theory-rooted
  aliens as `(pattern, subject)` pairs; a new `LhsAutomaton::FreeWithAliens` + `Subproblem::Sequence`
  (`SequenceSubproblem`) composes their sub-automata by nested backtracking (Maude's `SubproblemSequence`).
  The all-free hot path stays a separate `Free` variant on `match_pattern` (fib untouched). Verified —
  `conformance/correctness-free-alien.maude`.
- **S + CUI directions — DONE (uniformity).** A theory-rooted subterm under an `iter` op (`s (a + X)`) or
  a `comm` op (`(a + X) ; Y`) now matches — the last two axes, previously loud panics (`s.rs:67` / `cui.rs`).
  The recorded-enumeration core was extracted into one shared primitive,
  `theory::enumerate_alien_solutions` (match each `(pattern, subject)` alien through the full seam, compose
  by nested backtracking, snapshot bindings); the free `Sequence`, the S non-variable sub-pattern, and the
  CUI argument pairings all route through it — no `match_pattern` "free-only islands" left. The S
  bare-variable absorption path (fib/numbers) is untouched. Verified — `conformance/correctness-cross-theory.maude`.
- **Residual (not C8).** A `match`/`xmatch` order caveat: AC/AU solution *sets* match the reference but the
  enumeration *order* differs in places (the deferred Diophantine order, set-compared per the B1 discipline);
  `reduce` counts conform because they use Maude's greedy first solution. **C5** (AC/`iter` *membership*-lhs
  matching) was the membership-side cousin sharing this machinery — now confirmed done (see §2.3 C5). The
  single-element ACU collapse with identity (`s M + N <=? s e`) is a separate pre-existing deferred gap
  (`07` §collapse), which also drives the C5 collapse-count residual.

#### C7 — Subject-DAG sharing of repeated subterms  **[confirmed, count-only]**

Maude hash-conses identical ground subterms when it builds the subject DAG, so a membership on a *repeated*
reducible subterm is applied (and counted) once; our `build_dag` builds a tree, so it counts once per
occurrence. Repro: `mb mkA : Sml` over `op <_,_> : Elem Elem -> P`, `red < mkA, mkA >` = **1** rewrite in
Maude, **2** in ours (result `< mkA, mkA > : P`, `mkA : Sml`, identical in both). Surfaced while verifying
C1 seam 3 (`pick(tt, mkA, mkA)`), but **independent of C1** — the old eager model had the same gap, and it
fires with or without `strat`.
- **Boundary.** Count-only (result value + least sort always faithful). Applies to any repeated *reducible*
  subterm — under a membership *or* an equation, in the **subject** *and* in an **RHS**: probed (2026-06-24)
  `eq g(a)=b`, `red < g(a), g(a) >` = Maude **1** / ours **2**; `eq f(X)=< g(X), g(X) >`, `red f(a)` = Maude
  **2** / ours **3** (Maude's `RhsBuilder` shares the RHS duplicate too). Idiom-rare: a bare-variable
  duplicate (`X * X`) already shares via the substitution, and an ACU duplicate (`a + a`) already merges to
  one element with multiplicity 2 — so only a repeated *compound* under a free/AU/CUI op diverges.
- **Fix is DEEPER than first assessed — it is the out-of-place reduction model, not construction sharing.**
  Implemented construction-time structural dedup (a `NodeTerm`-keyed memo on `alloc_node`, enabled around the
  subject build + a flagged RHS; verified it *does* collapse the duplicates — instrumented dedup hits) and it
  **did not move the count.** Root cause: our `reduce` is **out-of-place** — when `g(a)` rewrites to `b` the
  frame moves to a fresh `b` and the original `g(a)` node is never stamped reduced, so a *shared* `g(a)` is
  re-reduced once per parent reference. Maude counts once because it rewrites **in place** (the node becomes
  `b`, marked reduced, seen by every ref). So matching the count needs either **(a) in-place reduction** —
  a foundational reduce-loop rework that also breaks the **render-after trace** (which holds redex/result
  *ids* and would re-render mutated nodes; it would have to snapshot terms instead) — or **(b) an id-keyed
  reduce memo** (redex→nf), which conflicts with **bounded-memory reduction (C6)** by pinning every reduced
  subterm and entangles with GC id-reuse. Both are disproportionate to an idiom-rare, count-only divergence,
  so C7 stays deferred as a deliberate foundational item (bundle with any future reduce-loop work). The
  construction-dedup exploration was reverted (no standalone payoff).

#### C9 / C10 / C11 — frontend fidelity (parse / print) — **DONE**

All three were `tnk-frontend`-only (value/sort/count always already correct); all differentially verified
byte-identical to the reference binary (echo + result), conformance fixtures added.
- **C9 — float printing.** `render_float` now ports Maude's `doubleToString` (`Utility/macros.cc`): 17
  significant digits, mantissa normalized to `[1,10)` with trailing zeros stripped, signed exponent only when
  nonzero (`1.0e+4`, `2.5e-1`, `1.0000000000000001e-1`). Fixture `correctness-float-print.maude` (the old
  `float.maude` only used format-coincident values like `1.0`/`2.0`).
- **C10 — glued prefix-minus.** `-7` now lexes as one `SMALL_NEG` token (`TokKind::NegNumber`) parsed via the
  `-_` minus op (`Terminal::SmallNeg` → `Action::MakeInteger`, mirroring `SMALL_NAT`→`MAKE_NATURAL`), exactly
  as Maude. A spaced `-` stays its own token (subtraction unaffected); `5 -7` fails to parse just as the
  reference binary rejects it. Fixture `correctness-glued-minus.maude`.
- **C11 — rational printing.** A `DivisionSymbol` node whose args are integer numerals (Maude's `isRat`)
  prints compactly as `num/den`; a `0/N` (Zero numerator) is *not* a rational and stays spaced (`0 / 5`).
  `rat_conforms` upgraded from value-only to printed-text (`conform_render`).
- **Echo, as a rider.** The reduce-command echo (`reduce in M : … .`) now pretty-prints the *normalized parsed
  term* (new `command_echo`), which is what Maude echoes — so special constants collapse in the echo too
  (`100.0` → `1.0e+2`, `2 / 4` → `2/4`, `- 3` → `-3`). The only residual echo divergence is the pre-existing
  **AC print-order** cosmetic difference (our `SymbolId` order vs Maude's `orderInt`; `08` §status), now also
  visible in echoes of 3+-element AC terms — multiset-identical, order-only, no conformance fixture hits it.

### 2.2 Confirmed — output formatting

#### C12 — Deep ctor-chain stack overflow in the pretty-printer — **DONE**

Was: rendering a very deep chain of *plain free* constructors overflowed the stack — the *evaluator* was
always fine (verified: `reduce` is iterative since A1 and provably completes — `fib(22)` = 186579 rewrites;
`sort_of` is a cached O(1) read; `instantiate`/`match` recurse on shallow pattern depth, not subject depth),
but the recursive DAG printer (`print`→`print_app`→child, one frame per level) blew the ~8 MB stack on
`fib(22)`'s 17711-deep `s^17711(0)` result. **Fixed** by converting the `pretty.rs` walk to an explicit
heap work-stack (`Item`/`Work`, `run_stack`/`layout*`) — the same transform A1 applied to `reduce`/
`deep_equal`; contained to the printer, no evaluator change, byte-identical on all existing render/
round-trip/trace tests. `fib(22)` now prints its 17711-successor result (== Maude's value + rewrite count).

#### C13 — Long-output line-wrapping  **[confirmed, the C12 residual]**

Maude wraps a long printed term across lines at a column limit (default ~72), continuing with a 4-space
indent; we print the whole term on one line. So `fib(22)`'s result is value-identical but laid out
differently (Maude: many wrapped lines; ours: one ~35 KB line). Display-only, value/sort/count always
correct, and it only triggers on very long results (idiom-rare — no conformance fixture in the byte-diff
suite hits it). **Fix:** port Maude's output line-wrapper (the `format`/`PrintSettings` line-length logic) in
the REPL/pretty layer. Lowest-priority of the open items.

### 2.3 Unconfirmed candidate probes  *(write the differential test first)*

Each becomes a confirmed `C<n>` item with a repro, or is struck out, once probed.
- **C2 — F-1 no-op rewrite guard — STRUCK (no divergence; must NOT implement).** Differentially refuted
  (2026-06-24): Maude **loops** on `eq a = a` and `eq f(X) = f(X)` exactly as we do — confirmed both
  empirically (the reference binary prints the `reduce in …` echo then spins, no result; ours likewise) and
  in the source. `DagNode::reduce` (`Interface/dagNode.hh:563`) is `while (!isReduced()) { if (!eqRewrite(…))
  { setReduced(); … break; } }` — it exits *only* when `eqRewrite` returns false (no equation applied); and
  `FreeSymbol::eqRewrite`→`discriminationNet.applyReplace` returns true on every applied equation, with **no**
  `result == redex` short-circuit anywhere in the rewrite path. A non-terminating spec is *supposed* to loop,
  and we already match Maude byte-for-byte up to the loop. **Adding the F-1 guard would make us halt where
  Maude loops — a brand-new divergence — so it must not be added.** (F-1 was a Phase-0 *robustness* suggestion,
  not a conformance requirement; it is incompatible with the byte-faithfulness goal.) The real robustness
  concern it gestured at is **interruptibility** — Maude aborts a runaway `reduce` on SIGINT back to the
  prompt, whereas our REPL can't yet interrupt an in-progress reduce. That is a separate, legitimate item
  (signal-checked reduce loop), tracked apart from the (rejected) no-op guard. Not fixture-able (it loops).
- **C3 — order-dependent equation & membership application — VERIFIED (matches on every well-formed spec;
  one narrow ill-formed-spec residual).** Probed (2026-06-24) the order-observable cases:
  - **Equations — MATCH (byte-identical).** The *first-declared matching* equation fires (declaration order,
    not specificity): `eq f(a)=b . eq f(X)=c .` → `f(a) = b`, but the swapped `eq f(X)=c . eq f(a)=b .` →
    `f(a) = c`; the non-confluent `eq a=b . eq a=c .` → `b`; a conditional fallback (`ceq … if c` then a
    plain `eq`) takes the first whose condition holds. These are the *common* real cases (overlapping
    specific/general patterns) and we reproduce Maude exactly.
  - **Comparable membership targets — MATCH.** Smallest-sort-first, correct count: `mb x:B . mb x:A .`
    (A < B) → sort `A`, 1 rewrite (drops straight to A, no double count).
  - **Incomparable membership targets — NARROW DIVERGENCE (ill-formed specs only).** `mb x:A . mb x:B .`
    with A, B incomparable (a *contradictory* membership — no element is both) → Maude picks **B**, we pick
    **A** (1 rewrite in both). Maude orders sort constraints by `sort->index()` **descending** (smallest sort
    = largest index first; `Core/sortConstraintTable.cc::sortConstraintLt`), and for incomparable targets the
    tiebreak is Maude's *component sort index* (a topological numbering) — which our declaration-order
    `SortId` doesn't replicate. Idiom-rare (well-formed specs never assert contradictory memberships),
    result-sort-only (count matches), silent in both. **Fix (if ever needed):** port Maude's component
    sort-index + `sortConstraintLt`. Deferred — disproportionate to an ill-formed-spec edge.
  - The `g(a), g(a)` count-doubling found while probing (Maude 3 rw, ours 6) is **C7** (subject-DAG sharing
    of the repeated reducible subterm), not an ordering issue.
- **C4 — error-sort / kind naming — DONE (single-top kinds, the common case); narrow multi-top residual.**
  Audited (2026-06-24): the divergence was purely the printed kind LABEL — **no semantic difference**. Both
  engines compute the same kind/component (`g(0+0)` is kind-level in both; the equation `g(0)` does not match
  the kind-level arg in either; the *values* are identical) — only the `[…]` representative-sort name
  differed. **Fixed:** the kernel now names a kind after its MAXIMAL sorts (Maude's `printKind`: the
  component's top sorts), not the first-declared member, so `overload.maude` `red 0 + 0` prints `[Nat]`
  byte-identically (`sort.rs::close`; `overload_conforms` updated). **Residual (rare, cosmetic):** for a
  kind-level term in a *multi-top* component the ORDER of the listed maximal sorts is Maude's component
  sort-index — a DFS-topological numbering (declared `A B D`, all maximal → Maude `[B,D,A]`); we list them in
  declaration order (`[A,B,D]`). **Same root cause as the C3 incomparable-membership tiebreak** — both need
  Maude's unported `ConnectedComponent` sort index (`Core/sort.cc::registerConnectedSorts` + `appendSort`);
  deferred together. Single-top kinds (every well-formed signature) are exact.
- **C5 — AC / `iter` membership-lhs matching — DONE (covered by C8).** Memberships compile to the same
  `LhsAutomaton` and match via the same seam as equations (`SortConstraint.lhs`, engine.rs:49/768/888), so
  C8's cross-theory matching covers their lhs. Differentially verified vs the reference — AC (non-linear
  `mb X + X`, alien `mb s M + N`), AU (`mb a L`, alien `mb (s M) L`), iter/S (`mb s s s X`) —
  `conformance/correctness-membership-theory.maude`. **Two residual edges, both pre-existing / orthogonal,
  not membership-specific:** (a) **collapse matching** — when a membership pattern collapses under an
  identity (`mb a L : Lst` with `[id: nil]`), Maude also applies it to the collapsed sub-element (`a`,
  `L=nil`), so the *count* is higher than ours (sort/value still correct); Maude itself warns on such
  patterns; the deferred `07` §collapse gap, which affects equations too. (b) ~~a theory-rooted sub-pattern
  under an `iter` successor~~ — **now closed** as part of C8's uniform cross-theory composition (the S/CUI
  directions): `mb s (a + X) : Foo` matches modulo AC under the successor. So only (a), collapse matching,
  remains — and it never blocked idiomatic membership specs.
- **C6 / F-2 — engine-global condition-reduce GC root set — DONE (commit `0af1a93`).** A condition
  fragment is evaluated by re-entering `reduce`; that nested reduce's `safe_point_gc` saw only its *own*
  frame stack, so with in-reduction GC on a collection could sweep the outer reduction's live state
  (sibling subtrees held only in ancestor frames, the match bindings, the redex). The old mitigation
  disabled GC for the whole condition solve — correct, but it can't bound a single long-running condition,
  and it's the wrong model for Phase-2 `rew`/`search` (which re-enter `reduce` extensively). **Fixed** by
  keeping GC enabled and rooting the outer context (Maude marks from all active rewriting contexts): a new
  `Runtime.protected` vec, marked by `safe_point_gc`, onto which `condition_holds` pushes the outer frames'
  roots (each `original` — transitively its unreduced children — + strategy-reduced `args`), the match
  bindings, and the redex (threaded via both the equation route `try_rewrite_top`→`try_equations` and the
  `cmb` route `compute_true_sort`/`constrain_to_smaller_sort`→`membership_applies`); plus `RootGuard`s in
  `solve_condition` for its own intermediates (the reduced `l` pinned across `r`'s reduction, with `r`
  instantiated after; the reduced subject pinned across a `:=` recursion). Gated on `gc_interval`, so the
  GC-off REPL/bench hot path is untouched (zero overhead). Two kernel corruption tests (equality + `:=`)
  reduce `pair(a, cond(b))` under frequent GC and recover the result intact — **proven load-bearing**
  (disabling just the frame-push sweeps the outer sibling; the missing intermediate root surfaced as a
  freed-node panic before the `RootGuard`s). All condition fixtures stay byte-identical to the reference;
  214 tests, fib(22) unregressed. **Unblocks bounded-memory Phase-2 `rew`/`search`.**

---

## 3. Sequencing

1. **C8 — DONE** (was the highest-severity item, a panic on idiomatic AC/AU/free specs), and **C5 — DONE**
   (AC/`iter` membership-lhs matching, covered by C8's shared matcher seam; confirmed differentially).
2. **C9–C11 — DONE** (frontend fidelity: float / glued-minus / rational printing + the normalized command
   echo; all differentially byte-identical, fixtures added).
3. **C12 — DONE** (pretty-printer deep-chain overflow → iterative work-stack; evaluator was never affected).
   Its residual **C13** (long-output line-wrapping) is display-only and lowest priority.
4. **C6 / F-2 — DONE** (engine-global condition-reduce GC root set; keeps GC on during conditions while
   protecting the outer context — bounded-memory re-entrant reduction, the Phase-2 `rew`/`search`
   prerequisite). Earlier sweep outcomes: **C2 struck** (Maude loops on `eq a = a` too — the F-1 guard would
   diverge); **C3 verified** (we match on every well-formed order-dependent case); **C4 done** for single-top
   kinds (name by maximal sort → `[Nat]`).
5. **Remaining = idiom-rare residuals only** (none block Phase 2): **C7** (subject-DAG sharing, count-only —
   do when the term-builder is open); **C13** (long-output line-wrapping); the shared **C3/C4 multi-top
   component-index order** (Maude's unported `ConnectedComponent` sort index — closes both at once).
6. **Phase 2** (parameterized programming + rules + the real prelude), built on a faithful engine.

**Conformance discipline (unchanged):** every fix is validated against the reference binary — value, sort,
rewrite count, and termination — not from memory. Grow `conformance/` with a `correctness-*.maude` fixture
per fixed item (C1 already added `correctness-mb-reducible.maude` + `correctness-strat-mb.maude`).
