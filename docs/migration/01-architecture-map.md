# Maude — Architecture & Feature Map (the reference, + our build status)

*Source of truth: `~/code/maude-lang/Maude/src` (~200k LOC C++, 24 subsystems) + the Maude 3.1
manual. Per-subsystem deep-dives in `reports/A1`…`A8`.* This doubles as the **parity map**: the layer table
(§2) and feature inventory (§3) describe what Maude is; the cross-cutting decisions (§4) are our porting
strategy (now largely realized — see `03-open-decisions.md`).

> **Build status (Phase 1 + 1.5 complete).** **L0 Kernel**, **L1 Sorts**, **L2 Theories+matching**, **L3
> Built-ins** — DONE (the matcher uses naive backtracking, not Maude's bipartite/Diophantine solver — a perf
> gap, `gaps.md`). **L5 Frontend** (lexer/mixfix-grammar/Earley parser/pretty-printer) and **L6 Modules**
> (non-parameterized: import/flatten/`+`/rename) — DONE. **L4 Operational** (rules/search/strategies/objects/
> IO), **L6 parameterization** (theories/views/instantiation), **L7 Reflection/meta**, **L8 Symbolic** — NOT
> STARTED (Phase 2/3, `roadmap.md`). Feature inventory (§3) = the Phase-2/3 to-do list.

## 1. What Maude is (the spine)
Maude is a high-performance engine for **two nested logics**: *membership equational logic*
(MEqL) ⊆ *rewriting logic* (RWL).
- A **functional module** = equational theory `(Σ, E∪A)` — signature `Σ` (sorts, subsorts, kinds,
  overloaded ops), equations+memberships `E`, equational axioms `A` (`assoc`/`comm`/`id`/`idem`).
  Computation = **equational simplification**: apply `E` left-to-right *modulo* `A` to a canonical form.
- A **system module** = rewrite theory `(Σ, E∪A, φ, R)` — adds frozen-arg map `φ` and rules `R`.
  Computation = **rewriting**: interleave equational simplification with rule application, modulo `A`.
- Semantics is **initial-model**; executability rests on Church-Rosser + termination (equations) and
  **coherence** (rules vs equations). Maude is also **reflective** — modules/theories are data at the
  meta-level, which is what makes it a logical *framework*.

Everything in the codebase is a layer over this: represent terms → compute their sorts → match/rewrite
them modulo axioms → drive that with rules/search/strategies → parse/print/modularize the surface
language → reflect it → add symbolic reasoning (unification/variants/narrowing/SMT/LTL).

## 2. Layered architecture (bottom-up) with the dominant Rust verdict

| Layer | C++ subsystems | Role | Rust verdict (headline) |
|---|---|---|---|
| **L0 Kernel & memory** | `Core`,`Interface`,`Variable` | `Term`(static) vs `DagNode`(runtime hash-consed DAG); mark-sweep GC arena; `Substitution`; `RewritingContext`; reduce loop; stack-machine path | **RETHINK** memory → index-arena + mark-sweep GC; **enum-dispatch** theories |
| **L1 Order-sorted types** | `Core/sort*` | sorts, subsort poset, kinds=connected components (error supersorts), preregularity, sort decision-diagrams, memberships, ctors, `SortBdds` | **PORT** the diagram/least-sort algorithms; **RETHINK** poset build & multiple-inheritance |
| **L2 Equational theories & matching** | `FreeTheory`,`ACU_`,`AU_`,`CUI_`,`S_`,`NA_` + `*_Persistent` | per-axiom term reps + matching automata; free discrimination net; AC bipartite+Diophantine matcher; per-theory unification primitives | **PORT** algorithms; **RETHINK** virtual hierarchy → enums + narrow traits |
| **L3 Built-in data** | `BuiltIn` | number/string/float/equality/branch ops bound to prelude via `special(id-hook…)` | **RETHINK** binding → typed `enum SpecialOp`; **PORT** arithmetic (bignum crate) |
| **L4 Operational layer** | `Higher`(search),`StrategyLanguage`,`ObjectSystem`,`IO_Stuff` | rules, `rewrite`/`frewrite`(fair), `search`+state-graph, strategy language, object/config fair rewriting, external objects (sockets/files/processes) | **PORT** traversal/search logic; **RETHINK** `goto`-coroutines→iterators, process graph→arena, poll-reactor→`mio` |
| **L5 Frontend** | `Mixfix`(parse half),`Parser` | flex lexers + bison surface grammar; user-extensible per-module mixfix grammar; **Earley+Leo** CF parser w/ prec/gather; bubbles; pretty-printing | **RETHINK** lexer/surface (hand-written/`logos`); **ADAPT/PORT** the Earley-Leo algorithm (no crate does it) |
| **L6 Modules & parameterization** | `Mixfix`(module half) | module DB, flatten-by-"donation", import modes, `+`/rename/instantiate, theories/views/parameterized modules & views, caches | **RETHINK** donation→pure flatten fn + `Rc`/dirty-set; **PORT** the expression AST & param algebra |
| **L7 Reflection / meta** | `Meta` | META-TERM/MODULE/VIEW/LEVEL, up/down maps, descent functions, meta-interpreters | **ADAPT** reify/reflect as traits; **RETHINK** descent fn-ptr table → enum/registry; prelude ports as-is |
| **L8 Symbolic & verification** | `Higher`(unify/variant/narrow),`SMT`,`Temporal` | order-sorted unification, folding variants, narrowing, SMT (CVC4/Yices), LTL→Büchi model checking | **PORT** algorithms; **RETHINK** SMT backend→Z3+trait, BDD→pure-Rust crate |

## 3. Feature inventory (parity targets)
- **Type system:** sorts, subsorts, kinds, ad-hoc/subsort overloading, preregularity, memberships
  (`mb`/`cmb`), constructors (`ctor`), polymorphic ops (`poly`), partiality via kinds.
- **Functional:** equations (`eq`/`ceq`), matching & simplification **modulo** `assoc comm id idem`;
  op attrs `assoc comm id: idem iter ctor poly format ditto strat memo frozen special`; stmt attrs
  `label metadata nonexec owise print`.
- **System:** rules (`rl`/`crl`) incl. rewrite conditions; `rewrite`, `frewrite` (position/object-message
  fair), `search` (`=>1/=>+/=>*/=>!`, `such that`, bounds, `show path`/`graph`), `continue`.
- **Predefined data:** `BOOL`, `NAT`, `INT`, `RAT`, `FLOAT` (GMP/IEEE), `STRING`, `QID`, machine ints,
  random/counter, conversions; containers `LIST`/`SET`/`MAP`/`ARRAY`, basic theories
  `TRIV`/`STRICT-*-ORDER`/`TOTAL-*`/`DEFAULT` + standard views; Diophantine solver.
- **Modules:** `protecting`/`extending`/`including`; summation `+`; renaming `*(...)`; parameterized
  programming (theories `fth`/`th`, views, parameterized modules/views, instantiation).
- **Objects/IO:** configurations, classes/messages, fair object-message rewriting; external objects —
  standard streams, files, sockets, processes; control-C handling.
- **Strategies:** strategy language (`srew`/`dsrew`, combinators, `matchrew`, calls, strategy modules,
  parameterized strategies); internal (meta-level) strategies.
- **Verification:** invariant model checking via search; **LTL** model checking (counterexamples);
  LTL satisfiability/tautology.
- **Symbolic:** order-sorted **unification** modulo axioms; **variants** & variant unification;
  **narrowing** (`vu-narrow`/`fvu-narrow`); **SMT** (`check`, `smt-search`) + variant satisfiability.
- **Reflection:** `META-LEVEL` descent functions (`metaReduce`/`metaRewrite`/`metaApply`/`metaMatch`/
  `metaSearch`/`metaUnify`/`metaGetVariant`/`metaParse`/`metaPrettyPrint`/sort ops…), up/down,
  **meta-interpreters** (nested interpreter objects, incl. remote).
- **Surface/UX:** user-definable mixfix syntax w/ `prec`/`gather`/`format`; pretty-printer; full command
  set, `set`/`show` options; tracing, term coloring, debugger, profiler.
- **Extensions:** Full Maude (OO modules, tuples, parameterized views) — historically a `.maude`
  metaprogram, OO now largely a Core desugaring pass.

## 4. The cross-cutting C++→Rust decisions (load-bearing; every layer touches these)

1. **Memory = index-arena + tracing GC, NOT `Rc`, NOT raw pointers.** The runtime DAG becomes a
   `Vec`-backed arena keyed by `DagId(u32)`; GC = non-moving mark-sweep over the arena with an explicit
   root set (RAII `RootGuard`). Handles give cheap shared aliasing + in-place rewrite without `unsafe`.
   The arena lives in an **instance-based `Engine`** (no global statics; `DagId` engine-relative) — see D1/D2.
   *Foundational: terms, substitutions, search states, meta all use arena handles.*
   **Risk #1 = matching Maude's bump-allocation throughput** (500k–several M rewrites/s).
2. **Dispatch = enum for the closed hot set; traits only at open seams.** Replace the C++ multiple-
   inheritance virtual hierarchies (`Symbol` is-a `SortTable`+`EquationTable`+`RuleTable`+…) with:
   `Symbol`/`DagNode`/`Term` as **enums** over the fixed theories (Free/ACU/AU/CUI/S/NA/Var/BuiltIn) +
   **composed** table structs as fields; **narrow traits** (`LhsAutomaton`, `Subproblem`,
   `RhsAutomaton`, `ConditionFragment`, `StrategyExpression`, `SmtEngine`, external-object managers)
   where genuine polymorphism is needed — closed ones as enums, open ones (external objects, residual
   subproblem trees) as `Box<dyn>`.
3. **Backtracking/enumeration = explicit iterators / resumable state machines.** The `match()`→
   `Subproblem::solve(findFirst)` protocol and the `goto`-resumed search/condition coroutines all
   enumerate lazily; model uniformly as `Iterator`/hand-rolled state enums. (Matching, unification,
   variants, narrowing, search, descent solution-streams.)
4. **Parser = drop flex/bison.** Hand-write the lexer (or `logos`) and a recursive-descent/Pratt surface
   parser; **port the Earley+Leo prec/gather/bubble CF parser** (unique to Maude — no crate replicates
   it). Replace the lexer↔parser global-state handshake for bubbles with an explicit API.
5. **Module flattening = pure functions + reference-counted caches.** Replace in-place "donation" of raw
   `Term*` and the `Entity::User`/`regretToInform`/`protectCount` manual module-GC with `flatten(...) ->
   FlatModule` producing fresh arena terms + `Rc`/dirty-set cache invalidation + explicit provenance.
6. **The `special(id-hook…)` seam = typed `enum SpecialOp`** resolved at module-build time; built-ins
   become arms of symbol reduction, not attached C function pointers.
7. **Bignums** → **`malachite`** (pure Rust) behind a `tnk-core::num` wrapper; `rug` (GMP) as a benchmarked escape hatch (decision **D4**).
8. **BDDs are cross-cutting** (order-sorted unifier filtering, ACU Diophantine selection, LTL Büchi
   labels) → pure-Rust **`biodivine-lib-bdd`** behind a `bdd` facade, feature-gated; BuDDy FFI as fallback (decision **D6**).
9. **SMT backend** → the **`z3` crate** behind a `trait SmtEngine`, runtime/feature-selectable (not build-time-fixed as C++) (decision **D7**).
10. **External IO/concurrency** → an owned **`mio`** reactor + `signal-hook` (single-threaded deterministic
    interleave), replacing the global poll-reactor + signal plumbing; `tokio` only for a future networked direction (decision **D5**).

## 5. Keep-as-data / drop list (no backward compat)
- **Keep as data, port ~verbatim:** the `.maude` **prelude/library** (only wire the hooks); the Full
  Maude metaprogram (ships as a `.maude` library on the meta-level); OO modules become a **frontend
  desugaring pass**.
- **Drop for parity-v1:** `FullCompiler` (experimental C++ codegen); the two **dead narrowing
  generations** (keep v3 only); `freePreNetFullCompiler` codegen; LaTeX/XML pretty buffers (defer);
  `LOOP-MODE` (deprecated; defer); tecla line-editor (→ `rustyline`); redundant BDD debug cross-checks;
  all the C++ idioms in §4 (unions, placement-new, `dynamic_cast` dispatch, intrusive lists, fn-ptr
  tables, global mutable statics).
