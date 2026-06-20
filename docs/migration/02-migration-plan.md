# Maude → Rust — Migration Plan (Stage-1 proposal)

Companion to `01-architecture-map.md`. Goal: idiomatic Rust, **core feature parity**, no backward
compatibility. Strategy: **reimplement from the spec (manual) using the C++ as the reference
implementation**, not a line-by-line transliteration — the C++ idioms (§4 of the map) don't survive
the borrow checker, but the *algorithms* port cleanly.

## 1. Proposed Cargo workspace
Crate boundaries follow the dependency DAG and the `pub(crate)` coupling (theories need kernel
internals — C++ `friend` access → Rust crate-internal visibility, so the heart stays one crate).

```
tambanokano/                   # cargo workspace (codename; see D8)
  crates/
    tnk-core/    # L0+L1+L2+L3 — the tightly-coupled heart (one crate, many modules)
      dag/        arena, DagId (engine-relative), gc (non-moving mark-sweep + root set), hashcons, memo
      term/       Term tree, term2dag
      sort/       poset+kinds, sort-diagram least-sort/preregularity, ctor, membership, bdd(feat)
      symbol/     Symbol enum + composed tables (sort/eq/rule/strat/memo), theory tag
      subst/      Substitution, local bindings
      num/        Int/Nat/Rat newtype wrapper over malachite (D4)
      context/    RewritingContext, the reduce loop, eval control (strat/memo/frozen)
      theory/     traits (LhsAutomaton/Subproblem/RhsAutomaton/ExtensionInfo/UnifSubproblem)
                  + free/ acu/ au/ cui/ s/ na/  (+ persistent structures) + diophantine
      builtin/    typed SpecialOp seam, number/string/float/equality/branch
    tnk-frontend/  # L5 — lexer, surface parser, mixfix grammar build, Earley-Leo cfparser, build_term, pretty
    tnk-modules/   # L6 — module/view DB, flatten, import modes, renaming, parameterization, caches
    tnk-engine/    # L4 — rules, rewrite/frewrite, search+state-graph, strategy lang, objects, mio IO
    tnk-symbolic/  # L8 — unify, variant, narrow, smt(z3), ltl(buchi+nested-dfs), shared bdd facade
    tnk-meta/      # L7 — reify/reflect, descent functions, meta-interpreters
    tnk-repl/      # bin `tnk` — Engine instance, command enum, CLI, REPL (rustyline)
  prelude/       # the .maude library shipped as assets (ported ~verbatim; hooks wired in tnk-core::builtin)
  conformance/   # differential test harness vs the C++ `maude` binary
```
Workspace dep order: `tnk-core` → {`tnk-frontend`,`tnk-engine`,`tnk-symbolic`} → `tnk-modules` → `tnk-meta` → `tnk-repl`.
(`tnk-modules` depends on `tnk-frontend`+`tnk-core`; `tnk-engine`/`tnk-symbolic` depend on `tnk-core`; `tnk-meta` depends on all.)

## 2. Phased delivery (each phase = a runnable, testable system)
Dependency-driven; every phase ends at a demoable milestone and grows the conformance suite.

### Phase 0 — Foundations spike (de-risk §4.1–4.3) — *the make-or-break phase*
Build the **vertical slice for the free theory only**: dag arena + mark-sweep GC; `Term`/`DagNode`/
`Symbol` enums (Free + Variable + a stub builtin); order-sorted sorts (poset, kinds, sort-diagram,
least-sort, preregularity); free-theory matching (discrimination net) + `RhsAutomaton`; the equational
reduce loop; just enough module construction (hand-built in tests, no parser yet).
**Milestone:** reduce a hand-built Peano `NAT` functional module to canonical form; micro-benchmark the
GC/reduce loop vs C++ on a known workload. **This validates decisions #1/#2/#3 before scaling.**

### Phase 1 — Core functional Maude
Add the remaining **equational theories** (ACU, AU, CUI, S, NA) + persistent structures — the biggest
algorithmic chunk; the **built-in data** ops + bignums (BOOL/NAT/INT/RAT/FLOAT/STRING/QID working); the
full **frontend** (lexer, surface parser, per-module mixfix grammar + Earley-Leo parser, pretty-printer);
basic **module system** (import/flatten, summation, renaming); REPL with `reduce`/`match`/`trace`/`show`.
**Milestone:** load & run real *functional* prelude modules (non-parameterized) from text; parity on
equational simplification incl. matching modulo axioms.

### Phase 2 — System modules + modularity
Rules + `rewrite`/`frewrite` + `search` + state-transition graph; object/configuration system + external
objects/IO (sockets/files/processes, control-C); **parameterized programming** (theories, views,
parameterized modules/views, instantiation) → the **full prelude loads** (LIST/SET/MAP/ARRAY…); the
**strategy language**.
**Milestone:** full Core-Maude system-module level; prelude library loads & runs end-to-end.

### Phase 3 — Reflection, symbolic reasoning, verification (full parity)
The **meta-level** (META-LEVEL descent functions, up/down, meta-interpreters); order-sorted
**unification** + **variants** + **narrowing** (brings in the BDD backend); **SMT** (Z3); **LTL model
checking**; OO desugaring + Full Maude as a `.maude` library.
**Milestone:** Maude 3 feature parity across the manual; conformance suite green.

## 3. What ports directly vs. must be rethought (consolidated)

**PORT (algorithm is sound & data-oriented — reimplement faithfully):**
sort decision-diagrams + least-sort/preregularity; free **discrimination net**; **AC bipartite +
Diophantine** matcher; variant **folding** (most-general + descendant eviction); narrowing (v3);
**LTL→Büchi** (Gastin-Oddoux) + **nested DFS** model checking; `rewrite`/`frewrite` traversal & fairness;
the **Earley+Leo** parse algorithm + prec/gather/default computation; bignum arithmetic; the parameter/
view instantiation algebra; the `.maude` prelude.

**RETHINK (C++ idiom doesn't survive Rust — redesign):**
memory model & GC (raw-ptr DAG + placement-new + intrusive roots → arena+handles+RAII roots); all the
**multiple-inheritance virtual hierarchies** (→ enums + composition + narrow traits); **backtracking via
pointers/`goto`** (→ iterators); **flex/bison** (→ hand-written lexer/surface + ported Earley); module
**donation + manual module GC** (→ pure flatten + `Rc`/dirty-set); meta **descent fn-ptr table** (→
enum/registry); **SMT** CVC4/Yices build-time pick (→ Z3 + runtime trait); **external IO** global poll
reactor + signals (→ `mio`/`tokio`); the `special` **hook attachment** (→ typed enum).

**DROP:** FullCompiler; dead narrowing generations; freePreNet C++ codegen; LaTeX/XML buffers, LOOP-MODE,
tecla (defer/replace); BDD debug cross-checks.

## 4. Risk register (highest first)
1. **GC/allocator throughput (existential).** Maude's speed is bump-allocation + non-moving lazy sweep +
   tuned slop. A naive arena/collector regresses badly. → Mitigate in **Phase 0** with benchmarks; design
   for cache-compact nodes (niche-pack sort index/flags); keep the option of a generational/region scheme.
2. **Shared-mutable aliasing of DAG nodes** (in-place flag/sort mutation on shared nodes) is borrow-
   checker-hostile. → The arena-index + interior-mutability decision is load-bearing; settle it in Phase 0.
3. **AC/collapse matching correctness** (multi-solution, extension, `id:`/`idem` collapse) is intricate.
   → Differential conformance tests from the manual's `xmatch`/`search` examples.
4. **Parser fidelity** (Leo DRP + prec/gather + bubbles + ambiguity *ordering* is observable). → Differential
   test the parser against C++ Maude on the whole prelude before trusting it.
5. **Parameterization corner cases** (free vs bound params, theory/module views, parameterized views,
   `X$Elt`, nested instantiation) — the bulk of the module work. → Conformance from prelude + ch.6/7.
6. **BDD backend** (pure-Rust maturity vs FFI) gates all symbolic features. → Prototype `biodivine-lib-bdd`
   early in Phase 3 (or Phase 0 spike if convenient).
7. **Incompleteness propagation** (assoc unification) threaded unify→variant→narrow as a flag — must be
   preserved end-to-end so the right warnings fire.
8. **Fresh-variable families** (`#n`/`%n`) bookkeeping — centralize in one `FreshVariableGenerator`.

## 5. Conformance strategy (cross-cutting, starts Phase 0)
A `conformance/` harness runs the same input through the **C++ `maude` binary**
(`~/Downloads/Maude-3/maude`) and the Rust build, diffing canonical output. Seed it from: the prelude,
the manual's worked examples, and the existing `~/code/maude-lang/Maude/tests`. This is the safety net for
every "PORT" claim above — algorithms are ported against observed behavior, not from memory.

## 6. Locked decisions (working defaults — full rationale in `03-open-decisions.md`)
Agreed Stage 1; each revisitable at the noted phase.
- **D1 Engine model:** instance-based `Engine`, no global statics; engine-relative `DagId`; meta runs in-heap;
  meta-interpreters = separate engines. *(revisit: Phase 0)*
- **D2 GC:** non-moving mark-sweep + stable ids; generational deferred. *(go/no-go benchmark: Phase 0)*
- **D3 Dispatch:** enums for the closed theory set; `Box<dyn>` only for residual subproblem trees + the
  external-object seam. *(pin: Phase 0)*
- **D4 Bignum:** `malachite` behind a `tnk-core::num` wrapper; `rug` as escape hatch. *(revisit: Phase 1)*
- **D5 External IO:** owned `mio` reactor + `signal-hook`; not `tokio`. *(revisit: Phase 2)*
- **D6 BDD:** `biodivine-lib-bdd` behind a `bdd` facade, feature-gated. *(revisit: Phase 3)*
- **D7 SMT:** `z3` crate behind `trait SmtEngine`, runtime/feature-selectable. *(revisit: Phase 3)*
- **D8 Naming:** project name `tambanokano` (confirmed), `tnk-` crate prefix; final public *language* name deferred. *(revisit: post Phase 0/1)*

## 7. Status: Phase 0 complete (go/no-go = GO)
Phase 0 shipped a free-theory vertical slice and validated the architecture against the reference C++
binary — see `04-phase0-results.md`. Next is **Phase 1** (core functional Maude): the remaining
equational theories (esp. AC/ACU matching), built-in data + bignums, the lexer/mixfix parser, and a
basic module system — opening with the deferred optimizations (discrimination net, inline args, compiled
rhs, in-place rewrite, safe-point GC).

## 8. Guardrails for Phase 1+ — do not overfit to the Phase 0 prototype
Phase 0 code is a **validated probe, not a foundation to preserve**. It took deliberate shortcuts to
de-risk quickly; several are *wrong as long-term design* and must be re-derived from the full spec
(reports `A1`–`A8` + the manual), not extended out of convenience. Treat the following as **expected
rewrites**, and don't let new code grow to depend on their current shape:

- **`DagNode` is free-only.** Real nodes vary per theory (ACU flat array *and* red-black tree, S-theory
  bignum, variables, built-in constants). The node representation will be reshaped; the generic arena/GC
  stays, the `enum` arms are not final.
- **One declaration per symbol; sort = `range`.** `compute_free_sort` is a placeholder. Overloading + the
  sort decision diagram (least sort, preregularity, and preregularity *modulo axioms*) replace it. Nothing
  should assume "a node's sort is its operator's range sort."
- **Naive recursive matcher.** `match_pattern` is throwaway — it becomes per-theory compiled automata
  (discrimination net for free; bipartite + Diophantine for AC). Don't depend on its recursion/shape.
- **Functional reduce.** `reduce(id) -> id` with no in-place rewrite and no mid-reduction GC is a
  simplification. In-place destructive rewrite + safe-point GC (RootGuard + context-tracked roots) will
  change the reduction strategy and signatures.
- **Unconditional, eager-only, no attributes.** Conditions (eqs/mb/rules), evaluation strategies
  (`strat`/`frozen`/`memo`), and statement attributes are absent and need first-class support.
- **`Engine` bundles signature + runtime.** The eventual split is a static `Module` (sorts/symbols/
  statements) vs. a runtime `RewritingContext` over the arena; don't entrench the bundling.

**Principle: let the architecture map drive the code, not the prototype.** Phase 0 proved *feasibility*;
it does not define the *design*.
