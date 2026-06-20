# Phase 1 — plan & fresh-session kickoff

**Read this first when starting the Phase 1 session.** It is the single entry point: it tells you how
to re-acquire context, what the code currently is, and the exact ordered agenda. Everything it
references already exists in this repo or in the two reference trees.

> **STATUS (updated post-Stage-A):** Phase 1 **Stage A is COMPLETE** — all five foundation reshapes in
> §3 are done and adversarially reviewed (commits `7f8df37` A1, `f8b1c0d` A2 + `758ebf9` D2-resolved,
> `12d60c2` A3, `6e1b8da` A4, `13219cf` A5; 37 tests, reduce ≈8.3 M rw/s, `fib(22)`=186579 == reference).
> §3 below is now history (kept for rationale). **For the breadth work (Stage B), the live plan is
> [`07-stageB-plan.md`](07-stageB-plan.md)** — it records the *as-built* Stage-A seams that B1–B5 plug
> into and supersedes §4 below. A thorough Stage-A audit is scheduled before Stage B begins.

---

## 0. Re-acquire context (do this at the start of the session)

**Reference trees (outside this repo):**
- C++ ground truth (~200k LOC): `/Users/dai/code/maude-lang/Maude/src`
- Maude 3.1 manual (feature/semantics authority): `/Users/dai/Downloads/Maude-3/book/extracted_manual/manual.md`
- Reference `maude` binary for conformance diffing: `/Users/dai/Downloads/Maude-3/maude`
  (run: `~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null`)

**Docs in this repo (`docs/migration/`), in read order:**
1. `01-architecture-map.md` — the subsystem map + the 10 cross-cutting C++→Rust decisions.
2. `03-open-decisions.md` — **D1–D8 are locked; do not re-litigate** (incl. the D2 amendment on GC roots/generational handles).
3. `02-migration-plan.md` §2 (phases), §7 (Phase 0 = GO), **§8 (anti-overfitting guardrails — what to replace, not preserve)**.
4. `review/05-review-synthesis.md` — the Phase 0 review triage; its **Tier 2** *is* the opening work below.
5. Per-subsystem deep-dives, pulled in as each milestone starts: `reports/A2` (theories/matching), `A3` (sorts), `A4` (parser), `A5` (modules), `A7` (built-ins), `A1` (kernel), `A6` (operational, Phase 2), `A8` (symbolic, Phase 3).

**The code:** `crates/tnk-core`. Sanity check the starting point: `cargo test -p tnk-core` (22 pass),
`cargo clippy --all-targets` (clean), `cargo run --release --example peano` (the go/no-go bench).

**The memory:** `maude-rust-migration.md` (project paths, status, this agenda in brief).

---

## 1. Where Phase 0 left the code (your starting point)

`tnk-core` is a working but deliberately narrow vertical slice: an index-arena + non-moving
mark-sweep GC, the order-sorted sort poset/kinds, a **free-theory-only** term/dag/symbol model, a
recursive structural matcher, and an eager innermost `reduce`. It conforms *exactly* to reference
Maude on Peano `+`/`*`/`fib` (canonical forms **and** rewrite counts) and was adversarially reviewed
and hardened (review Tier-1: GC mark-on-push, field encapsulation, epoch-versioned `REDUCED`, checked
arity, subsort-cycle rejection).

**Prototype shortcuts to replace, not build on** (`02` §8): free-only `DagNode`; placeholder
"sort = operator range"; naive recursive single-solution matcher; functional (allocating) reduce with
no safe-point GC; `Engine` bundles signature + runtime; no conditions, no operator attributes, no parser.

---

## 2. Phase 1 goal & end milestone

**Goal:** *functional Maude you can write as text and run.* The full equational engine (matching modulo
`assoc`/`comm`/`id`/`idem`), built-in data types, a lexer + mixfix parser, and a basic module system,
behind a REPL.

**End milestone (done-when):** load real **functional** modules from `.maude` text (the non-parameterized
prelude fragments) and `reduce`/`match` them, differential-tested against the reference binary — same
canonical forms and rewrite counts. At that point it stops being "call Rust functions" and becomes
"write Maude, get answers."

---

## 3. Stage A — re-shape the foundation FIRST (review Tier 2; before any new theory)

Do these in order, as small tested commits, *before* adding a second theory or the parser. Each is far
cheaper on today's ~700-line kernel than after AC/conditions/rules grow on the current shapes. Full
rationale: `review/05-review-synthesis.md` Tier 2 + `R1`/`R3`.

**A1 — Iterative reducer (do first; it's the one real crash).** `reduce`/`reduce_args`/`deep_equal`
recurse on *subject depth* and abort the process at ≈`fib(25)` (release). Convert to explicit
work-stacks (as `mark_reachable` already is). *Done-when:* reducing `s^1_000_000 0` and `fib(30)` no
longer overflows; the `peano` benchmark throughput is unchanged. *(refs: review R2 C1, R0 F2; A1)*

**A2 — Arena safety: `RootGuard` + safe-point GC.** Add an `Engine` root registry; `RootGuard` registers
on construct / unregisters on `Drop`; `gc()` marks from the registry. Add a slot generation + per-arena
engine id checked under `cfg(debug_assertions)`. Then allow GC at safe points *inside* the (now
iterative) reducer, rooting the in-flight work-stack. Benchmark an 8-byte handle before deciding the
release-mode generational default (D2 amendment). *Done-when:* GC during one large reduction keeps memory
bounded; a missed-root/cross-engine misuse panics in debug. *(refs: D2 amendment, R1 C1/H1/M1, R3 C2/M5)*

**A3 — Matcher seam (`LhsAutomaton` / `Subproblem`).** Introduce the theory-plugin seam: two-phase
`match()` returning a residual `Subproblem` whose `solve()` is a **resumable, multi-solution** iterator
over `&mut Subst`; re-derive `try_rewrite_top`/`reduce` to drive a *solution stream*
(`while let Some(()) = solutions.next() { …check condition… }`). Route the existing free matcher through
it (still single-solution). This is what AC matching and conditional equations need. *Done-when:* the
free theory + Peano conformance still pass, now through the seam. *(refs: R3 C1, R0 F3; A2 §2)*

**A4 — Signature/runtime borrow split.** Separate an immutable `Signature`/`Module` (sorts, symbols,
statements) from a mutable runtime/`Context` (dag arena + `Subst`), so `&Signature` + `&mut Arena`
coexist. *Done-when:* the defensive clones (`rhs.clone()`, `children().to_vec()`) are gone; conditions/
rules have a borrow home. *(refs: R3 H1; A1, A5)*

**A5 — Child-traversal visitor.** Replace `DagNode::children() -> &[DagId]` with a visitor/iterator
(`for_each_child(impl FnMut(DagId))` for GC; `children() -> impl Iterator` for equality/reduce) so the
non-slice term reps (ACU `(term,mult)`, red-black tree, `iter` successor) fit. *Done-when:* GC/equality/
reduce go through the visitor; adding a non-slice arm needs no edits to them. *(refs: R3 H3; A1, A2)*

---

## 4. Stage B — breadth: the real functional engine

With Stage A's seams in place, add capability. Each pulls heavily from its deep-dive report.

**B1 — Equational theories** *(A2).* **[Superseded by `07`; status: ACU/AU/CUI DONE, S+NA moved to B3.]**
Add the theory enum arms behind the A3 seam + A5 visitor: **ACU**
(the big one — flat vs red-black dag reps, bipartite + Diophantine multiset matcher, lazy subproblems),
then **AU**, **CUI**, **S/iter** (stacked-successor numbers, needs bignum), **NA**. Port the persistent
structures. *Done-when:* matching modulo `assoc`/`comm`/`id`/`idem` conforms to the binary (use the
manual's `xmatch`/`match` examples as the conformance suite).

**B2 — Membership/conditional logic + sort diagram + attributes** *(A3).* Replace the placeholder sort
computation with the per-symbol **sort decision diagram** (ad-hoc overloading, least sort, preregularity);
add memberships (`mb`/`cmb`), conditional equations, and operator attributes (`ctor`, `strat`, `memo`,
`frozen`, `owise`, `special`). *Done-when:* overloaded/subsorted modules get the right least sorts; a
conditional functional module reduces correctly.

**B3 — Built-in data** *(A7).* The `special (id-hook …)` seam → a typed `enum SpecialOp`; implement
`BOOL`, `NAT`, `INT`, `RAT`, `FLOAT`, `STRING`, `QID` on `malachite` bignums (D4). *Done-when:* the
predefined numeric/string modules reduce and conform.

**B4 — Frontend** *(A4).* Lexer (`logos` or hand-written) incl. tokens/bubbles; surface parser; the
user-extensible **per-module mixfix grammar** + the **Earley-Leo** CF parser with prec/gather/format;
pretty-printer (the inverse). *Done-when:* a `.maude` functional module parses to the same terms the
hand-built fixtures produce; round-trips through pretty-print.

**B5 — Module system + REPL** *(A5).* Module database; `protecting`/`extending`/`including` import +
flatten; summation `+`; renaming `*`. A REPL with `reduce`/`red`/`match`/`trace`/`show` and `set`
options. *Done-when:* the **end milestone** — load functional prelude modules from text and run them,
conformance-checked vs the binary.

*(Parameterized programming — theories/views/parameterized modules — is large and is scheduled for
**Phase 2** alongside rules/search per `02-migration-plan.md` §2; keep B5 to non-parameterized modules.)*

---

## 5. Conformance discipline (carry the Phase-0 habit forward)

Every "port" is validated against the reference binary, not from memory. Grow `conformance/` (already has
`peano.maude`, `fib.maude`) from: the prelude (`/Users/dai/Downloads/Maude-3/prelude.maude`), the manual's
worked examples, and `/Users/dai/code/maude-lang/Maude/tests`. Diff canonical forms **and** rewrite
counts. This is the safety net behind every Stage-B claim.

---

## 6. Locked decisions (one-liners; full text in `03-open-decisions.md`)

D1 instance `Engine` (no globals). · D2 non-moving mark-sweep GC + stable ids; **amendment:** add
`RootGuard` + debug-gated generational/engine-id checks (Stage A2), release handle by benchmark. ·
D3 enum-dispatch for the closed theory set; `dyn` only at open seams. · D4 `malachite` bignums. ·
D5 `mio` IO reactor (Phase 2). · D6 `biodivine-lib-bdd` (Phase 3). · D7 `z3` SMT (Phase 3). ·
D8 project `tambanokano`, `tnk-` crate prefix.

---

## 7. Risks / watch-items carried into Phase 1

- **AC matching correctness × performance** — the bipartite/Diophantine matcher + collapse (`id:`/`idem`)
  cases are intricate; build the conformance suite from `xmatch` before optimizing (A2 §4).
- **Borrow pattern under backtracking** — `Subproblem::solve` mutates a shared `Subst` while holding
  pattern refs; the A3 seam + A4 split must make this ergonomic without per-step clones (A2 §4).
- **Parser fidelity** — Leo DRP + prec/gather + bubble boundaries + ambiguity *ordering* are subtle and
  observable; differential-test the parser on the whole prelude before trusting it (A4 §4).
- **Sort-diagram tie-breaking** — least-sort under overloading must match Maude's "earlier declaration"
  rule exactly (A3).

---

## 8. Suggested first moves in the new session

1. Read §0's docs (15 min) and run the three sanity checks in §1.
2. Create a Phase-1 task list from §3 (Stage A) — five tasks, in order.
3. Start with **A1 (iterative reducer)**: it's self-contained, removes the one crash, and its explicit
   work-stack is the substrate A2 builds on. Commit per item, `cargo test` + conformance green at each.
4. Only after Stage A is green, open Stage B with **B1 (ACU)** — the largest single piece.
