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
   nested `=>*` search. Built on the bounded-memory re-entrant reduction C6/F-2 unblocked. The two frontend
   niceties surfaced during A are also cleared — file-load mixing `set`/`show` mid-file, and on-the-fly
   `X:Sort` colon variables. **Remaining for Phase 2:** *object-message-fair* `frewrite`/`erewrite` (needs
   the object system, item 5); `frozen`'s lazy-`strat` interaction + search/rewrite-condition trace
   (`gaps.md`). Reference: `reports/A6-operational.md`.
2. **Parameterized programming (Pillar B) — the *mechanism* (B-i…B-iv) is DONE; "Axis A" finishes it.**
   Theories, views, parameterized modules, instantiation — the whole mechanism is a `tnk-modules`
   `PreModule → PreModule` transform; the kernel (`build_module`/grammar) is **unchanged** (a structured
   sort name `List{X}` / parameter sort `X$Elt` is just a string-keyed sort). All byte-conformant vs the
   binary (`conformance/{theory-nonexec,theory-import,view-good,param-module,instantiation}.maude`).
   - **(B-i) theories `fth`/`th` — DONE** (`91285d7`): reuse `PreModule` + an orthogonal `is_theory` flag;
     `[nonexec]` axioms parse but are skipped when loading the engine (proof obligations, never fire).
   - **(B-ii) views — DONE** (`dcc5dca`): `ViewDecl` (sort + op→op/op→term maps), `ViewDb` + signature
     `validate_view` (the target-sort check = Maude's `failed to find sort …` warning); `show view`.
   - **(B-iii) parameterized modules + `X$Elt` + structured sorts — DONE** (`5e01fc5`): the `{X :: T}`
     parameter list; a `sort_name()` parser assembling `Base{args}`; the *parameter copy* flatten
     (`s ↦ X$s`, reusing the rename machinery).
   - **(B-iv) instantiation `M{V}` — DONE** (`ac6b30e`): `ModuleExpr::Instantiation`; the view-table threaded
     through `flatten`; the instance substitutes `X$s ↦` the view's sort image and `Base{…X…} ↦ Base{…V…}`,
     importing the view's target. **Common case** (single/multi-param module-view, sort-only views).

   **Axis A — the remaining *parameterization* work (the deferred B-iv corner cases). NEXT.** Each is
   **self-contained** — provable with hand-rolled modules (no real prelude), so each is a small increment in
   the B-i…iv rhythm. Noted inline in `flatten.rs`:
   - **A1 view operator maps** (`op f to g`, `op 0 to term 0.0`) — small; extend `instantiate_decls` to
     rewrite op names + statement bubbles. Forced by `DEFAULT`/`Float0`, `ARRAY`.
   - **A2 parameterized view target** (`view List{X} … to LIST{X}`) — medium. Forced by nested containers.
   - **A3 import-vs-view-target dedup** (a base `protecting NAT` instantiated by a view targeting `NAT`) —
     small; *probably already handled* by the shared `visited` set, but **unverified** (needs a clean,
     well-typed differential test). Forced by every real `LIST{Nat}`.
   - **A4 theory- vs module-declared sorts** in the parameter copy (a theory `protecting BOOL` must keep
     `Bool`, not `X$Bool`) — medium; needs sort provenance. Forced by `SORTABLE-LIST` (STRICT-TOTAL-ORDER).
   - **A5 free-vs-bound nested instantiation** (`LIST{List{Nat}}`; a param-module importing a param-module)
     — **the hard one** (A5 §4 top risk); deserves real care.
   - Related parser gaps: the structured colon-var `X:List{Nat}` / kind `[Y$Elt]` sorts, and `mb` over a
     structured sort.
   - **Built-engine edge already found** (`gaps.md`): instantiation flattens `M`'s statement *bubbles* into
     the instance and builds them there, so it never builds `M` standalone — a statement ill-typed in `M`
     but well-typed after instantiation is wrongly accepted (Maude builds+rejects `M` once). Ill-formed-spec
     only; well-formed prelude modules typecheck in `M`.

   **Conformance source:** `~/Downloads/Maude-3/prelude.maude` (3,234 lines — **zero rules**, so
   parameterization is the critical path to it). **Reference:** `reports/A5-modules-parameterization-repl.md`.
3. **The real prelude — loading the actual library. Depends on a NEW substrate, not just Pillar B.** The
   container prelude (`LIST`/`SET`/`MAP`/`ARRAY` + `TRIV`/`STRICT-*-ORDER`/`TOTAL-*`/`DEFAULT` + the 39
   standard views) needs **Axis A** *and* this item's substrate — empirically, the real `BOOL` (base of
   everything) does **not** load today, blocked on two distinct features:
   - **Polymorphic operators (`poly` / the `Universal` sort)** — `op if_then_else_fi : Bool Universal
     Universal -> Universal [poly (2 3 0)]`, `_==_`/`_=/=_ : Universal Universal -> Bool [poly (1 2)]`. A
     `Universal`-typed op is instantiated per connected component. This is the actual `BOOL`→`NAT`→`LIST`
     blocker and unlocks far more than containers (`==`/`=/=`/`if_then_else_fi` everywhere). The
     `SystemTrue`/`SystemFalse` hooks and kind variables (`var B : [Bool]`) come with it.
   - **Wiring the `.maude` prelude as data** — our `BOOL`/`NAT`/`INT`/`RAT`/`FLOAT`/`STRING`/`QID` are built
     from hand-rolled per-fixture signatures today; this loads Maude's actual modules (only the hooks wired).
   - The **Diophantine solver** is *separable* — an AC-matcher throughput optimization (`gaps.md`); the naive
     matcher already gives correct counts. Needed for heavy AC `search` at scale, not for the prelude to load.

   So **"load `LIST{Nat}` from the real prelude" = Axis A ∩ this substrate** — it is not a pure-Pillar-B task.
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

1. **Parameterization corner cases** (Phase 2, "Axis A" — the B-iv deferrals) — free vs bound params (A5,
   the deepest), theory/module-declared sorts (A4), parameterized views (A2), op-maps (A1), the
   import/target dedup (A3). Each is self-contained (hand-rolled fixtures, no real prelude). → Differential.
2. **`poly`/`Universal` polymorphism** (Phase 2 item 3) gates loading the *real* `BOOL`→`NAT`→`LIST` chain
   (a `Universal`-typed op instantiated per connected component); a separate feature from parameterization.
   → Differential against `prelude.maude`'s `TRUTH`/`BOOL`/`NAT`.
3. **AC/collapse matching at scale** — the naive matcher is correct but un-optimized; porting Maude's
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
