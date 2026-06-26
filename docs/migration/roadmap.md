# Roadmap — what remains (Phase 2 and beyond)

Phase 1 (functional engine) and Phase 1.5 (correctness hardening) are complete. This is the forward plan.
Each phase ends at a runnable, conformance-verified milestone and grows the `conformance/` suite. The C++
subsystem detail behind each item is in `reports/A1–A8`; the foundational tech choices are in
`03-open-decisions.md` (D5/D6/D7 are the still-pending forward decisions).

## Phase 2 — System modules + modularity

The jump from a *functional* engine to a *rewriting* one, plus the module algebra that lets the real
prelude load.

1. **Rules + rewriting (Pillar A) — DONE.** `rl`/`crl` (incl. the rewrite `=>` condition, the one
   condition kind that had been missing), `rewrite` (rule-fair) / `frewrite` (position-fair, frozen-aware),
   `search` (`=>1`/`=>+`/`=>*`/`=>!`, `such that`, bound `[n,m]`, `show path`/`show search graph`),
   `continue` — all byte-conformant against the reference (`conformance/{rewrite,frewrite,crl,search,
   rewrite-cond}.maude`). The kernel grew a separate rule table (never consulted by `reduce`), a shared
   `drive_match` seam, a lazy hash-consed state-transition graph (`search.rs`), and the rewrite-condition's
   nested `=>*` search. Built on the bounded-memory re-entrant reduction C6/F-2 unblocked. **Remaining for
   Phase 2:** *object-message-fair* `frewrite`/`erewrite` (needs the object system, item 5); `frozen`'s
   lazy-`strat` interaction + on-the-fly colon variables + search/rewrite-condition trace (`gaps.md`).
   Reference: `reports/A6-operational.md`.
2. **Parameterized programming.** Theories (`fth`/`th`), views, parameterized modules/views, instantiation,
   `X$Elt`, nested instantiation — the bulk of the module work, and the gate for the container prelude
   (`LIST`/`SET`/`MAP`/`ARRAY`). Builds on the existing pure-flatten transform (`tnk-modules`). Reference:
   `reports/A5-modules-parameterization-repl.md`. **Risk:** parameterization corner cases (free vs bound
   params, theory/module views, parameterized views) — differential-test from the prelude.
3. **The real prelude.** Wire the `.maude` prelude/library on top of (1)+(2): `BOOL`/`NAT`/`INT`/`RAT`/
   `FLOAT`/`STRING`/`QID` are built; add the containers + basic theories (`TRIV`/`STRICT-*-ORDER`/`TOTAL-*`/
   `DEFAULT`) + standard views + the Diophantine solver. Ports as data (only the hooks are wired).
4. **Strategy language** (`srew`/`dsrew`, combinators, `matchrew`, calls, strategy modules). Reference:
   `reports/A6-operational.md`.
5. **Objects / external IO** (configurations, classes/messages, fair object-message rewriting; standard
   streams / files / sockets / processes; Ctrl-C). Brings in the **D5** `mio` reactor + `signal-hook`
   decision. Reference: `reports/A6-operational.md`.

**Milestone:** Core-Maude system-module level; the prelude library loads & runs end-to-end.

## Phase 3 — Reflection, symbolic reasoning, verification (full parity)

1. **Reflection / meta-level.** `META-LEVEL` descent functions (`metaReduce`/`metaRewrite`/`metaApply`/
   `metaMatch`/`metaSearch`/…), up/down maps, meta-interpreters (nested interpreter objects). Per **D1**,
   descent runs as an in-heap sub-context of the same engine; true meta-interpreters are separate engines.
   Reference: `reports/A7-meta-builtins.md`.
2. **Symbolic.** Order-sorted **unification** modulo axioms; **variants** + variant unification; **narrowing**
   (`vu-narrow`/`fvu-narrow`). Brings in the **D6** pure-Rust BDD backend (`biodivine-lib-bdd`) for the
   order-sorted unifier, ACU Diophantine selection, and LTL labels. Reference: `reports/A8-symbolic-smt-ltl.md`.
3. **SMT + verification.** `check`/`smt-search` over the **D7** `z3` trait backend (+ variant satisfiability as
   a `.maude` library); **LTL model checking** (LTL→Büchi via Gastin-Oddoux + nested DFS, counterexamples);
   invariant model checking via search. Reference: `reports/A8-symbolic-smt-ltl.md`.
4. **OO + Full Maude** as a frontend desugaring pass + a `.maude` meta-level library.

**Milestone:** Maude 3 feature parity across the manual; conformance suite green.

## Ports vs. rethink (for the as-yet-unbuilt layers)

**PORT faithfully** (the algorithm is sound and data-oriented): `rewrite`/`frewrite` traversal & fairness;
the AC **bipartite + Diophantine** matcher (currently a naive backtracking stand-in — see `gaps.md`); variant
**folding** (most-general + descendant eviction); narrowing (v3 only); **LTL→Büchi** + nested-DFS model
checking; the parameter/view instantiation algebra; the `.maude` prelude.

**RETHINK** (the C++ idiom does not survive Rust): backtracking via pointers/`goto` → iterators / resumable
state machines; module donation + manual module-GC → the pure flatten transform already in `tnk-modules`;
the meta descent fn-ptr table → an enum/registry; SMT build-time backend pick → the **D7** runtime trait;
the global poll-reactor + signal plumbing → the **D5** `mio` reactor.

**DROP** (no parity-v1 obligation): `FullCompiler` (experimental C++ codegen); the dead narrowing
generations (keep v3); `freePreNet` codegen; LaTeX/XML pretty buffers; `LOOP-MODE`; redundant BDD debug
cross-checks.

## Risk register (forward items)

1. **Parameterization corner cases** (Phase 2) — the bulk of the module work; free vs bound params,
   theory/module views, parameterized views, nested instantiation. → Conformance from the prelude + manual.
2. **AC/collapse matching at scale** — the naive matcher is correct but un-optimized; porting Maude's
   bipartite/Diophantine matcher is a perf prerequisite for heavy AC search. → Differential `xmatch`/`search`.
3. **BDD backend maturity** (Phase 3) gates all symbolic features. → Prototype `biodivine-lib-bdd` early
   (the `SortBdds` sort-function + AllSat path) before committing.
4. **Incompleteness propagation** (assoc unification) — must thread unify→variant→narrow as a flag so the
   right warnings fire end-to-end.
5. **Fresh-variable families** (`#n`/`%n`) — centralize in one generator.
6. **Search/state-graph memory** — the bounded-memory re-entrant reduction (C6/F-2) is in place; the state
   graph itself needs the same GC discipline.

## Conformance strategy (cross-cutting, unchanged)

Every "PORT" claim above is validated against the C++ binary, not from memory: same input through
`~/Downloads/Maude-3/maude` and our build, diffing canonical output. Seed new fixtures from the prelude, the
manual's worked examples, and `~/code/maude-lang/Maude/tests`.
