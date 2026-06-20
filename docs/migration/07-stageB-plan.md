# Phase 1 Stage B — plan & the as-built foundation it builds on

**Read this first when starting Stage B** (the breadth work — the real functional engine). Stage A (the
foundation reshape, review Tier 2) is **complete and adversarially reviewed**; this doc records the
*seams it produced* — the internal API Stage B plugs into — and the ordered **B1–B5** agenda. It
supersedes `06-phase1-plan.md` §3–§4 for the breadth work (`06` remains the Phase-1 overview; its §3
Stage A is now done).

> Sequencing note: a thorough **audit of Stage A** is scheduled for a separate session *before* Stage B
> begins. Treat §1 below as "Stage A as-built today"; if the audit refines a seam, update §1 first. The
> seams were each reviewed at commit time (no semantic divergence found), so they should be stable.

---

## 0. Re-acquire context (start of the Stage B session)

**Reference trees (outside this repo) — unchanged from `06` §0:**
- C++ ground truth: `/Users/dai/code/maude-lang/Maude/src`
- Maude 3.1 manual: `/Users/dai/Downloads/Maude-3/book/extracted_manual/manual.md`
- Reference `maude` binary for conformance: `~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null`
- Prelude (the .maude library to port/conform against): `/Users/dai/Downloads/Maude-3/prelude.maude`

**Docs read order:** `01-architecture-map.md` (esp. layers **L1/L2/L3/L5/L6** and cross-cutting
decisions #2/#3/#4/#5/#6/#7) → `02-migration-plan.md` §2 (phases) + §3 (PORT/RETHINK/DROP) →
**this doc** → then the per-milestone deep-dive *as each B item starts*: `reports/A2` (B1 theories/
matching), `A3` (B2 sorts/membership/attrs), `A7` (B3 built-in data — §1/§2 *BuiltIn seam* part only;
the meta half is Phase 3), `A4` (B4 parser), `A5` (B5 modules+REPL — *non-parameterized* part only;
parameterization is Phase 2). Decisions: `03-open-decisions.md` (D1–D8; **D2 resolved** = 4-byte
release handle; D4 `malachite`).

**The code:** `crates/tnk-core` (Stage A as-built). Sanity check before starting:
- `cargo test -p tnk-core` → 37 pass; `cargo clippy --all-targets -- -D warnings` → clean.
- `cargo run --release --example peano` → `fib(20)` ≈ **8.3 M rewrites/s**, GC mark ≈ 350 M nodes/s.
- `cargo run --release --example peano 22 1 100` → `fib(22) = 17711 (186579 rewrites)` == reference.

**The memory:** `maude-rust-migration.md` (status, the Stage-A commit map, this agenda in brief).

---

## 1. Stage A as-built — the seams Stage B plugs into

**Do not re-derive these; build on them.** Stage A reshaped the kernel *precisely so that the theories,
conditions, built-ins, and parser are additive*. The internal API:

### 1.1 Engine = `Signature` (immutable during reduction) + `Runtime` (mutable) — A4 (`6e1b8da`)
`engine.rs`: `pub struct Engine { sig: Signature, rt: Runtime }` is a thin facade re-exposing the
public API. Internals:
- `Signature { sorts: Sorts, symbols: Arena<Symbol>, equations: HashMap<SymbolId, Vec<CompiledEquation>>, eq_epoch: u32 }`
- `Runtime { dags: Arena<DagNode>, rewrite_count, roots, gc_interval, allocs_since_gc }`
- The reduction/matching methods are `impl Runtime` taking `&Signature` (`reduce`, `try_rewrite_top`,
  `make_free`, `compute_free_sort`, `match_pattern`, `instantiate`); `deep_equal` is runtime-only.

**Why B needs it:** a rewrite holds `&sig.equations` (the matched `&eq.rhs`) while `&mut`-borrowing the
runtime to build nodes — *no clone*. **This is the borrow home for B2's conditional equations**: the
condition is reduced via `&mut Runtime` while the equation table stays borrowed through `&Signature`.
AC residue-node construction (B1) gets `&mut Runtime` the same way.

### 1.2 Matcher seam: `LhsAutomaton` / `Subproblem` + solution-stream driver — A3 (`12d60c2`)
`theory.rs` (crate-private, closed enums — decision D3):
- `enum LhsAutomaton { Free(Term) }` — `compile(lhs: Term)`; `match_(&self, &Runtime, &Signature, subject, &mut Subst) -> Option<Subproblem>` (two-phase: bind the forced part, return a residual).
- `enum Subproblem { FreeOnce { pending } }` — `next(&mut self, &Runtime, &mut Subst) -> bool` (a resumable solution enumerator; free theory yields one).
- The driver is `Runtime::try_rewrite_top`:
  ```text
  for eq in eqs { reset subst; let Some(mut sp) = eq.lhs.match_(..) else continue;
      while sp.next(..) { /* accept first solution */ return Some(instantiate(&eq.rhs, ..)); } }
  ```
  (`#[allow(clippy::never_loop)]` marks the loop as intentionally multi-iteration-in-the-future.)

**Why B needs it / how B extends it:**
- **B1 (ACU/AU/CUI/S/NA):** add `LhsAutomaton::Acu(..)` / `Subproblem::Acu(..)` arms. AC matching is
  *multi-solution* → `next()` yields several substitutions on successive calls. The driver loop already
  consumes a stream — no reduce-core rewrite. ACU's residual `Subproblem` owns its bipartite graph +
  Diophantine system (no borrows of the engine; `&Runtime`/`&mut` passed per `next`). When `next` must
  allocate residue nodes, widen its `&Runtime` to `&mut Runtime` (a crate-internal change — these enums
  are `pub(crate)`, so it is not a public-API break).
- **B2 (conditional equations):** the `while sp.next(..)` body becomes
  `if condition_holds(sig, rt, subst) { accept } else { continue }` — i.e. backtrack into the next
  solution on condition failure. `condition_holds` reduces condition fragments via `rt.reduce(sig, ..)`
  (the A4 borrow home). `CompiledEquation` gains a compiled condition; `Equation` (public) gains it too.
- Discrimination net (free-theory perf) is a *later* optimization behind this same seam — it changes how
  `match_` finds candidate equations, not the driver.

### 1.3 Child traversal visitor — A5 (`13219cf`)
`dag.rs`: `DagNode::children(&self) -> impl Iterator<Item = DagId>` and
`for_each_child(&self, impl FnMut(DagId))` replace the old `&[DagId]` slice. GC (`mark_reachable` via
`children().extend`), `reduce` (`new_reduce_frame` via `children().collect`), and `deep_equal` (via
`symbol()` + pairwise `children()`) are all theory-agnostic.

**Why B needs it / contract for B reps:** a new `NodeTerm` arm (ACU multiset of `(DagId, mult)`,
S `(count, arg)`, red-black tree) implements `children()`/`for_each_child` and is a *pure addition* —
GC/reduce/equality are untouched. **Two contracts the new reps must honour:**
- For `deep_equal` to stay correct, `children()` must yield the **full, canonically-ordered child
  sequence** (ACU: the flattened multiset with repeats, in canonical order — Maude keeps ACU nodes
  canonical, so pairwise comparison is equality).
- A theory whose node carries **scalar payload that is not a child id** (the **S-theory's successor
  `count`**) needs **theory-specific equality**, not `deep_equal` — exactly as matching is per-theory.
  (Documented on `deep_equal`.) Plan an equality dispatch when S lands.

### 1.4 Arena safety: generational handles + RootGuard + safe-point GC — A2 (`f8b1c0d`)
`id.rs`/`arena.rs`/`root.rs`/`engine.rs`: debug-gated `(generation, arena_id)` on `Id` (bare `u32` in
release — **D2 resolved**); `RootGuard` (RAII, `Rc<RefCell<RootRegistry>>`, does not borrow the engine);
`gc(extra_roots)` always marks the registry; opt-in `set_gc_interval` runs GC at the reduce loop head
rooting `walk(stack) ∪ child_result ∪ registry`.

**Conformance discipline for B:** any `DagId` a caller holds across a later reduction/allocation — incl.
a prior reduction's result, or terms held by the (future) module DB / REPL / meta — **must be pinned
with `Engine::root`** if `gc_interval` is set. New theory reps are new `NodeTerm` arms the arena/GC
already trace via the visitor; nothing in A2 needs changing for B.

### 1.5 Iterative reducer — A1 (`7f8df37`)
`engine.rs`: `reduce` is an explicit `ReduceFrame` work-stack (no subject-depth native recursion);
`deep_equal` is a pair-stack. `match_pattern`/`instantiate` stay recursive (bounded by *pattern/rhs*
depth, author-controlled — superseded by B1's compiled automata for the hot path). B reductions inherit
this loop unchanged.

### 1.6 Placeholders Stage B explicitly replaces (do not entrench)
| As-built (Stage A) | Replaced by |
|---|---|
| `Engine::compute_free_sort` (sort = op `range`, else kind error sort) | **B2** per-symbol **sort decision diagram** (least sort, preregularity, overloading) |
| `Symbol { name, domain, range }` — *one* declaration | **B2** multi-declaration `Symbol` + diagram handle (ad-hoc/subsort overloading) |
| `NodeTerm { Free }` only | **B1** `Acu`/`Au`/`Cui`/`S`/`Na` arms (+ a built-in/number arm for **B3**) |
| `Equation { lhs, rhs, nr_vars }` (unconditional) | **B2** conditional `eq`/`ceq` + memberships `mb`/`cmb`; op/stmt attributes |
| no built-ins | **B3** `enum SpecialOp` bound from `special(id-hook …)`; `malachite` bignums |
| hand-built modules in tests | **B4** parser + **B5** module system load `.maude` text |

---

## 2. The ordered agenda — B1 → B5

Each item: **goal · plugs into · what's new · done-when (conformance) · refs · risks.** Keep building
hand-constructed test modules (as Stage A did) for B1–B3; the parser (B4) is what makes the *end
milestone* "load `.maude` text" possible. Conformance is always against the reference binary.

### B1 — Equational theories (ACU, AU, CUI, S, NA) + persistent structures  *(the largest single piece)*
- **Goal:** matching & rewriting **modulo** `assoc`/`comm`/`id:`/`idem`.
- **Plugs into:** §1.2 matcher seam (new `LhsAutomaton`/`Subproblem` arms, multi-solution `next`),
  §1.3 visitor (new `NodeTerm` arms yielding canonical children), §1.1 `&mut Runtime` for residue nodes.
- **What's new:** **ACU first** — flat `ACU_DagNode` (`SmallVec<(DagId, u32)>`) vs red-black
  `ACU_TreeDagNode` above a size threshold; the **bipartite + Diophantine** multiset matcher; lazy
  subproblems; `MatchStrategy` selection (GROUND_OUT/LONE_VARIABLE/…); collapse matching (`id:`/`idem`).
  Then **AU** (deque + extension), **CUI**, **S** (stacked-successor numbers — needs bignum, ties to B3;
  S equality is theory-specific per §1.3), **NA** (trivial). Port the persistent structures
  (`rpds`/`im` — **open: which crate**). New module(s): `theory/{acu,au,cui,s,na}` + `diophantine`.
- **Done-when:** matching modulo the axioms conforms to the binary — **build the conformance suite from
  the manual's `xmatch`/`match` worked examples *before* optimizing** (the multi-solution counts, e.g.
  the 12-solution `xmatch`, are the spec).
- **Refs:** `A2` (the whole report); arch-map L2 + decision #3.
- **Risks (highest):** AC collapse correctness (`id:`/`idem` infinite classes); multi-solution
  completeness with extension under sort constraints; the greedy fast-path vs full-search tradeoff;
  flat↔tree rep switch + persistent-structure/GC interplay. Differential-test relentlessly.

### B2 — Sort decision diagram + memberships + conditional logic + operator attributes
- **Goal:** correct least sorts under overloading; conditional equations/memberships; op attributes.
- **Plugs into:** §1.1 (`reduce(&Signature, &mut Runtime)` evaluates conditions while the eq table is
  borrowed); §1.2 (the `while sp.next` condition-check + backtrack); replaces §1.6 `compute_free_sort`.
- **What's new:** per-symbol **sort decision diagram** (`findMinSortIndex`, preregularity, *preregularity
  modulo axioms*); **multi-declaration `Symbol`** (ad-hoc/subsort overloading) + the "earliest
  declaration" least-sort tie-break; memberships (`mb`/`cmb`); conditional equations (`ceq` — the
  condition is a list of fragments: equational, sort-test, matching, [rule for Phase 2]); operator
  attributes (`ctor`, `strat`, `memo`, `frozen`, `owise`, `special`, `assoc/comm/id:/idem` → wire to B1).
  `Equation`/`CompiledEquation` gain a condition; `Symbol` gains `Vec<OpDeclaration>` + a diagram handle;
  `leq` likely moves to `fixedbitset` (R3 M2).
- **Done-when:** overloaded/subsorted modules get the right least sorts (conform to the binary's `sort`/
  `parse` output); a conditional functional module reduces correctly with the right rewrite counts;
  `owise`/`strat`/`frozen`/`memo` behave per the manual.
- **Refs:** `A3` (whole report); arch-map L1 + decision #2/#3; review R3 M2 (multi-decl + bitset).
- **Risks:** least-sort "earliest declaration" must match Maude exactly (a watch-item); condition
  evaluation re-entering reduction (the A4 borrow home is the enabler — confirm no per-step clones);
  `owise` semantics; preregularity-modulo-axioms once B1's AC sorts exist.

### B3 — Built-in data types + bignums
- **Goal:** `BOOL`, `NAT`, `INT`, `RAT`, `FLOAT`, `STRING`, `QID` working.
- **Plugs into:** a new `NodeTerm`/symbol arm for built-in constants + the symbol-reduction path; B1's S
  theory (succ/`iter`) for NAT; B2's attribute parsing (`special`).
- **What's new:** parse `special (id-hook …)` into a typed **`enum SpecialOp`** at module-build time
  (resolving op/term hooks to symbol ids) — decision #6; built-in reduction becomes an arm of symbol
  reduction (not a fn-pointer); arithmetic on **`malachite`** behind `tnk-core::num` (D4); the predefined
  numeric/string modules. `NumberOp`/`Equality`/`Branch`/string/float per `A7` §2.
- **Done-when:** the predefined numeric/string prelude modules reduce and conform (numeric results,
  rewrite counts, `if_then_else_fi`, equality).
- **Refs:** `A7` §1/§2 (BuiltIn seam — *not* the meta half), decision #6/#7 (D4); arch-map L3.
- **Risks:** RAT/FLOAT edge cases; conformance of conversions; tying succ/`iter` (S theory) to NAT.

### B4 — Frontend: lexer + mixfix parser + pretty-printer
- **Goal:** parse `.maude` *functional* modules to the same terms the hand-built fixtures produce; round-trip via pretty-print.
- **Plugs into:** B2 sorts/components feed grammar build; `build_term` returns kernel arena terms
  (§1.1/§1.5); B5 consumes the parsed `PreModule`.
- **What's new:** hand-written (or `logos`) lexer incl. tokens/**bubbles** (replace the flex/bison global
  handshake with an explicit API — decision #4); recursive-descent/Pratt **surface** parser; the
  user-extensible **per-module mixfix grammar** built from the signature (prec/gather/format, OBJ3
  defaults); the **Earley + Leo (DRP)** CF parser (port the algorithm; no crate does prec/gather/Leo);
  the pretty-printer (the inverse). New crate `tnk-frontend` (per `02` §1).
- **Done-when:** a `.maude` functional module parses to the same terms as the fixtures; pretty-print
  round-trips; **differential-test the parser on the whole prelude before trusting it**.
- **Refs:** `A4` (whole report); arch-map L5 + decision #4.
- **Risks (high):** Leo DRP + prec/gather interaction (trickiest, least-documented C++); **ambiguity
  *ordering* is observable** (Maude takes the first of two parses — preserve forest-extraction order);
  bubble boundaries need grammar context (clean API without globals is the key design call).

### B5 — Module system (non-parameterized) + REPL  *(the Phase-1 end milestone)*
- **Goal:** load real functional prelude modules from text and `reduce`/`match` them.
- **Plugs into:** B4 (parsed `PreModule`), B1–B3 (the engine they flatten into), §1.4 (root module-DB
  terms if safe-point GC is on).
- **What's new:** module database; `protecting`/`extending`/`including` import + **flatten** (as a *pure
  function* producing fresh arena terms — decision #5, not C++ "donation"); summation `+`; renaming
  `*(...)`; a REPL (`rustyline`) with `reduce`/`red`/`match`/`trace`/`show` + `set` options.
  **Parameterized programming (theories/views/parameterized modules) is Phase 2 — keep B5 to
  non-parameterized modules.** New crates `tnk-modules`, `tnk-repl`.
- **Done-when (the milestone):** load the non-parameterized functional prelude fragments from `.maude`
  text and `reduce`/`match`, differential-tested vs the binary — *same canonical forms and rewrite
  counts*. "Write Maude, get answers."
- **Refs:** `A5` (the module half — skip §parameterization for now); arch-map L6 + decision #5.
- **Risks:** flatten/cache coherence (`Rc` + dirty-set vs rebuild); term ownership across modules
  (deep-copy vs shared arena — coordinate with the kernel arena).

---

## 3. Conformance discipline (carry the Phase-0/Stage-A habit forward)
Every "port" is validated against the reference binary, not from memory. Grow `conformance/` (has
`peano.maude`, `fib.maude`) from: the prelude (`/Users/dai/Downloads/Maude-3/prelude.maude`), the
manual's worked examples (esp. **`xmatch`/`match` for B1**, `sort`/`parse` for B2), and
`/Users/dai/code/maude-lang/Maude/tests`. Diff canonical forms **and** rewrite counts. Until the parser
(B4) lands, keep using hand-built modules in Rust tests + the reference binary on the equivalent
`.maude`, as Stage A did (e.g. the `fib(22) = 186579` lock).

## 4. Open decisions / risks specific to Stage B
- **Persistent-structure crate for ACU/AU** (`rpds` vs `im`) — pick during B1 by benchmarking against the
  GC/arena model (the tree rep must trace through the §1.3 visitor).
- **`Subproblem::next` borrow widening** to `&mut Runtime` when AC allocates residue nodes — crate-internal (the enums are `pub(crate)`); do it when B1 needs it.
- **Equality dispatch** for the S-theory (scalar `count` ≠ child id) — `deep_equal` is not enough (§1.3).
- **`leq` representation** (`BTreeSet` → `fixedbitset`) — with B2's larger sort sets (R3 M2).
- **Parser ambiguity ordering** — observable; lock with differential tests (B4).
- **Where built-in constants live** in `NodeTerm` (a `BuiltIn` arm vs per-type arms) — decide at B3.
- The `gen-checks` release feature (D2) stays deferred unless release-mode safe-point GC is actually used.

## 5. Suggested first moves (post-audit)
1. Read §0 docs + run the §0 sanity checks; skim §1 against the actual `crates/tnk-core` to confirm the
   seams are as described (the audit may have refined them).
2. Open **B1 with ACU** — the largest piece and the one the whole seam was built for. Before writing the
   matcher, **build the `xmatch`/`match` conformance suite** from the manual so multi-solution behavior
   is pinned. Add the `Acu` arms behind the §1.2 seam + §1.3 visitor; commit per sub-step (flat rep →
   tree rep → bipartite/Diophantine → collapse), conformance green at each.
3. Then B2 (sort diagram + conditions — conditions exercise the solution-stream's condition path), B3
   (built-ins), B4 (parser), B5 (modules + REPL = the milestone).
