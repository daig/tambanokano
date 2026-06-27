# Roadmap — what remains (Phase 2 and beyond)

Phase 1 (functional engine) and Phase 1.5 (correctness hardening) are complete. This is the forward plan.
Each phase ends at a runnable, conformance-verified milestone and grows the `conformance/` suite. The C++
subsystem detail behind each item is in `reports/A1–A8`; the foundational tech choices are in
`03-open-decisions.md` (D5/D6/D7 are the still-pending forward decisions).

## Phase 2 — System modules + modularity

The jump from a *functional* engine to a *rewriting* one, plus the module algebra that lets the real
prelude load.

1. **Rules + rewriting (Pillar A) — DONE.** `rl`/`crl` (incl. the `=>` rewrite-condition), `rewrite`
   (rule-fair) / `frewrite` (position-fair, frozen-aware), `search` (`=>1`/`=>+`/`=>*`/`=>!`, `such that`,
   bounds, `show path`/`graph`), `continue` — all byte-conformant (`conformance/{rewrite,frewrite,crl,
   search,rewrite-cond}.maude`). Built on a separate rule table (never read by `reduce`), the shared
   `drive_match` seam, and a lazy hash-consed state-transition graph (`search.rs`). **Still open (Phase 2):**
   object-message-fair `frewrite`/`erewrite` (needs objects, item 5); `frozen`'s lazy-`strat` interaction +
   search/rewrite-condition trace (`gaps.md`). Reference: `reports/A6-operational.md`.
2. **Parameterized programming (Pillar B) — DONE (mechanism + all of "Axis A").** Theories `fth`/`th`,
   views (sort + op→op/op→term maps), parameterized modules (`{X :: T}`, `X$Elt`, structured sorts `List{X}`),
   and instantiation `M{V}` — including every Axis-A corner case: view op-maps (A1), import/target dedup (A3),
   theory/module-declared sorts (A4), and the entangled hard pair **parameterized views + free-vs-bound nested
   instantiation** (A2/A5 — all three C++ argument kinds: module-view, by-parameter, theory-view; incl.
   `LIST{List{Nat}}` nesting, cross-kind ad-hoc overloading with `(t).Sort` disambiguation, and structured-sort
   memberships). The whole layer is a pure `tnk-modules` `PreModule → PreModule` transform — the kernel
   (`build_module`/grammar) is **unchanged** (`List{X}` / `X$Elt` are string-keyed sorts). All byte-conformant
   (`conformance/{theory-*,view-*,param-*,instantiation-*}.maude`). Residuals (orthogonal, in `gaps.md`):
   identity-collapse rewrite **count** (the AC matcher, reproduces non-parameterized) + the chained-import
   last-level substitution. Reference: `reports/A5-modules-parameterization-repl.md`.
3. **The real prelude — `poly`/`Universal` + loading the actual library. ← IN PROGRESS: the gateway is DONE
   (M0–M2).** The real `BOOL`, `NAT`, and `LIST{Nat}` now load and reduce **byte-identically** to the
   reference (`conformance/prelude-{bool,nat,list}.maude`). The poly/Universal + container substrate that was
   the gateway is built; `poly-universal-prelude.md` is now mostly a record of it. What landed:
   - **`poly` / the `Universal` sort** — a `Universal`-typed op (`_==_`/`_=/=_`/`if_then_else_fi`) is expanded
     into one concrete instance **per connected component** (eager per-kind, in `build_sig` after
     `close_sorts`); no new kernel reduction code (the existing `Equality`/`Branch` special ops reduce each
     instance). The `SystemTrue`/`SystemFalse` anchors and bare-boolean conditions came with it. **(M0)**
   - **NAT built-ins** — the `~>` partial arrow + the arithmetic / bitwise / shift codes
     (`xor`/`&`/`|`/`sd`/`modExp`/`>>`/`<<`) over `malachite` bignums. **(M1)**
   - **The container substrate** — module-local variable aliases (the flattener was leaking imported `var`s,
     mistyping `LIST`'s `append`) and **AU identity-collapse matching** (a pattern `E L` matches a singleton
     `c` as `c nil`) — the two things `LIST{Nat}` needed beyond the existing Pillar-B module algebra. **(M2)**

   **Remaining prelude work, in dependency order:**
   - **(a) Finish the container library** — `EXT-BOOL` → `SET` → `MAP` → `ARRAY` (+ `LIST-AND-SET`). Two small,
     well-understood capabilities unblock all of them: the **`[Sort]` kind notation** (`var B : [Bool]`,
     `op undefined : -> [Y$Elt]` — resolve `[S]` to S's kind/error sort; the long-noted `X:[Foo]` gap), and
     **ACU/CUI identity-collapse matching** — the direct analog of the AU collapse just done (`(E, S)` against a
     singleton set; `acu.rs`/`cui.rs` carry the identical `_ => return None`). ARRAY also leans on the DEFAULT
     theory/views (already building). This completes the parameterized data-structure library.
   - **(b) The remaining built-in data types** — `INT` (`abs`, signed `-_`), `RAT`, `FLOAT` (more float codes),
     `STRING`/`QID` (`ascii`/`find`/`upperCase`/…), `CONVERSION`; plus the leaf special ops
     (`CommutativeDecomposeEqualitySymbol` for INITIAL-EQUALITY-PREDICATE, `RandomOpSymbol`/`CounterSymbol`).
     Each is mostly *wiring a few more built-in op codes* — the same NAT-codes pattern (a typed `enum` arm +
     bignum/string op, differentially verified per code). Breadth, not depth.
   - **(c) The reflective wall — `META-LEVEL`** (META-TERM/MODULE/VIEW/LEVEL + descent functions
     `metaReduce`/`metaApply`/…). A major new subsystem (= Phase 3 item 1), gated on STRING/QID. This is where
     "load the prelude" meets reflection; the prelude's `.maude` source ports as-is once the hooks exist.
   - Residuals, off the reduce path (`gaps.md`): the parameterized **sortable-list views** parse gap
     (`expected 'to', found "{"`); the **`xmatch`-with-extension** over-enumeration; the ≥3-operand-infix
     number-fold rewrite-**count** delta. The **Diophantine solver** stays separable (an AC-matcher throughput
     optimization; the naive matcher already gives correct counts), needed for heavy AC `search`, not to load.
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

1. **Parameterization corner cases** (Phase 2, "Axis A" — the B-iv deferrals) — **RESOLVED**: A1–A5 all
   landed, differentially verified with hand-rolled fixtures. The one residual is a rewrite-**count** delta
   from identity-collapse matching (item 3 below — orthogonal to parameterization, reproduces without it).
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
