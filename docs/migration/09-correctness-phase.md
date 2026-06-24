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

> **STATUS.** **C1 (eager→lazy `mb` sort model) is DONE** (commit `160b956`) — it closed the
> reducible-membership over-count, the `cmb`-on-reducible *termination* gap, and the membership `Whole:`
> trace line. The as-built record is the commit + `08-full-trace-plan.md` §status + the kernel/`load.rs`
> code; it is intentionally *not* re-documented here (this doc tracks **pending** work only). Everything
> in §2 below is open: **C8** is the priority (a hard panic on idiomatic input); **C9–C11** are the cheap
> frontend-fidelity cluster; **C7** is confirmed but count-only; **C2–C6** are unconfirmed probes.

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

Fix in roughly this order: severity first (C8 panics), then the cheap frontend cluster (C9–C11), then the
confirmed-but-narrow C7, then the unconfirmed probes (C2–C6). C-numbers are stable discovery-order IDs, not
priority ranks.

### 2.1 Confirmed — evaluator

#### C8 — Cross-theory "alien subterm" matching  **[DONE — was a HIGH-severity panic]**

A pattern lhs with a **non-ground, non-variable subterm under an AC/AU operator** — or a theory-rooted
subterm under a free operator — (an "alien" in Maude's terms) was unsupported: a **loud panic at module
load**. The parked B1 cross-theory-composition follow-up (`07-stageB-plan.md` §"Deferred follow-ups";
loud-guarded, never silently wrong — audit F-A). Maude matches each alien recursively via its own
`LhsAutomaton` (`NonGroundAlien`), composing the child subproblems into the shared substitution.

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
- **Residual (not C8).** A `match`/`xmatch` order caveat: AC/AU solution *sets* match the reference but the
  enumeration *order* differs in places (the deferred Diophantine order, set-compared per the B1 discipline);
  `reduce` counts conform because they use Maude's greedy first solution. **C5** (AC/`iter` *membership*-lhs
  matching) is the membership-side cousin sharing this machinery — still open. The single-element ACU collapse
  with identity (`s M + N <=? s e`) is a separate pre-existing deferred match-only gap (`07` §collapse).

#### C7 — Subject-DAG sharing of repeated subterms  **[confirmed, count-only]**

Maude hash-conses identical ground subterms when it builds the subject DAG, so a membership on a *repeated*
reducible subterm is applied (and counted) once; our `build_dag` builds a tree, so it counts once per
occurrence. Repro: `mb mkA : Sml` over `op <_,_> : Elem Elem -> P`, `red < mkA, mkA >` = **1** rewrite in
Maude, **2** in ours (result `< mkA, mkA > : P`, `mkA : Sml`, identical in both). Surfaced while verifying
C1 seam 3 (`pick(tt, mkA, mkA)`), but **independent of C1** — the old eager model had the same gap, and it
fires with or without `strat`.
- **Boundary.** Count-only (result value + least sort always faithful); needs a *repeated* subterm that
  *also* carries a reducible membership — idiom-rare (repeated constructors don't reduce, so no membership
  fires twice on them anyway).
- **Fix.** Hash-cons identical subterms in `build_dag` (and reduce's rebuild) — a term-builder change that
  touches matching's structure-sharing assumptions, so a deliberate item, not a rider.

### 2.2 Confirmed — frontend fidelity (parse / print; value always correct)

These don't change the computed value/sort/count — they break *byte-identical* surface I/O. Grouped because
they live in `tnk-frontend` (lexer + pretty-printer), not the evaluator. **The float printer (C9) will block
Phase 2's real `FLOAT` prelude** — every float result misprints — so it is the most load-bearing of the three.

#### C9 — Float printing

Maude renders `f64` via its own `doubleToString` (a normalized scientific form); we use Rust's default
`Display`. Same bits, different text:

| `red` | Maude | Ours |
|---|---|---|
| `1.0 / 3.0` | `3.3333333333333331e-1` | `0.3333333333333333` |
| `100.0 * 100.0` | `1.0e+2`* | `100.0` |
| `1.0 / 4.0` | `2.5e-1` | `0.25` |
| `1.0e16` | `1.0e+16` | `10000000000000000.0` |

(*`1.0e+2` from `100.0 * 100.0`.) **Fix:** port Maude's float→string into the NA-value pretty-printer. The
`conformance/float.maude` fixture only exercises format-coincident values (`1.0`/`2.0`/`3.0`), so it passes
today — a coverage gap; widen it once the printer matches.

#### C10 — Glued prefix-minus lexing

`-7 quo 2` → our lexer/parser errors (`no parse`); `- 7 quo 2` (spaced) works; Maude accepts both. The
B4.5e negative-*float* lexer fix (`-1.5`) didn't extend to integer numerals glued to a prefix `-_`.
- **Fix.** Lexer/mixfix handling of a prefix `-` glued to an integer numeral (cheapest of the three).

#### C11 — Rational printing

`red 2 / 4` → Maude `1/2`, ours `1 / 2`. The rational is normalized correctly (value faithful); Maude
prints rational special-constants compactly (no spaces around `/`) via the `DivisionSymbol`'s special
printing, where we render the generic mixfix `_/_`. **Fix:** special-constant printing for rationals (same
pretty-printer neighborhood as C9; check whether other special constants share the path).

### 2.3 Unconfirmed candidate probes  *(write the differential test first)*

Each becomes a confirmed `C<n>` item with a repro, or is struck out, once probed.
- **C2 — F-1 no-op rewrite guard.** A self-rewriting `eq a = a` (or a rule producing an identical term): does
  Maude detect the no-op and stop, or loop? We currently loop. Cheap if real; another spurious-non-termination
  axis adjacent to C1's. (`07` §F-1.)
- **C3 — Non-confluent / order-dependent membership & equation application.** Incomparable applicable
  membership targets, or owise/condition interplay where application order is observable. Confirm our
  smallest-first order matches Maude's beyond the locked cases.
- **C4 — Error-sort / kind computation.** `[Sort]` error-sort naming and propagation (one known cosmetic
  naming divergence, `overload.maude` task #8); audit whether kind-level results ever differ *semantically*,
  not just in the printed bracket name.
- **C5 — AC / `iter` membership-lhs matching completeness.** Memberships whose lhs is a theory term (matching
  modulo ACU/AU/S). The membership-side cousin of **C8** — likely the same matcher work; schedule together.
- **C6 — Substitution-size / re-entrant reduce edge cases.** Deep/condition-nested reductions, the F-2
  engine-global GC root set (also a Phase-2 `rew`/`search` prerequisite — slot it here).

---

## 3. Sequencing

1. **C8 — DONE** (was the highest-severity item, a panic on idiomatic AC/AU/free specs). It shares matcher
   machinery with **C5** (AC/`iter` membership-lhs matching), which is the natural next pickup.
2. **C9–C11** (frontend fidelity) — cheap and independent; C10 (glued-minus lexer) is the smallest, C9
   (float printer) the most load-bearing for Phase 2's prelude.
3. **C7** (subject-DAG sharing) — confirmed but count-only and idiom-rare; do when the term-builder is
   already open.
4. **C2–C6 sweep** — confirm/refute each with a differential test, fix in cheapness order.
5. **F-2 (engine-global condition-reduce GC root set)** lands in this phase too — a deferred Stage-B item
   *and* a prerequisite for bounded-memory `rew`/`search` in Phase 2 (folded into C6).
6. Only then **Phase 2** (parameterized programming + rules + the real prelude), built on a faithful engine.

**Conformance discipline (unchanged):** every fix is validated against the reference binary — value, sort,
rewrite count, and termination — not from memory. Grow `conformance/` with a `correctness-*.maude` fixture
per fixed item (C1 already added `correctness-mb-reducible.maude` + `correctness-strat-mb.maude`).
