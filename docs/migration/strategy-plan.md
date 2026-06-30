# Phase 2.4 — Strategy language: implementation plan

The strategy language (`srewrite`/`dsrewrite`, the combinator set, strategy modules `smod`/`sth` with
`strat`/`sd`/`csd`, strategy calls) is greenfield — only the `strat` *operator attribute* (eager-strategy
positions) exists today; the strategy *language* does not. Reference: `reports/A6-operational.md` §"Strategy
language" + the C++ `src/StrategyLanguage/`. Oracle: `~/Downloads/Maude-3/maude` (`srewrite`/`dsrewrite`).

## Surface (probed against the reference)

```
smod M is protecting N . strat s : @ Sort . strats a b : Nat @ Sort . sd s := E . csd s := E if C . endsm
srewrite [in M :] T using E .      dsrewrite [in M :] T using E .
```
Output per command: blank line, then `Solution k\nrewrites: K …\nresult S: V\n` per solution, then
`No more solutions.\nrewrites: K …`; or `No solution.\nrewrites: K …` when there are none.

**Combinators** (precedence: atom > unary `* + !` and ternary `? :` > `;` > `|`; `;`/`|` right-assoc):
- `idle` (pass through → the subject), `fail` (no solution).
- `all` (apply any rule once, anywhere — every one-step rewrite), application `L[σ]{E,…}` (rule label `L`,
  optional initial substitution `σ`, substrategies for the rule's rewrite conditions), `top(E)` (only at the
  top), `one(E)` (only the first solution of `E`).
- `E ; F` (sequence: `F` on each result of `E`), `E | F` (union of all solutions).
- `E *` (zero-or-more = `idle | (E ; E*)`), `E +` (= `E ; E*`).
- `E ? F : G` (if `E` has ≥1 solution → `F` on each; else `G` on the original) — primitive; sugar:
  `try(E)=E?idle:fail`, `not(E)=E?fail:idle`, `test(E)=E?idle:fail` (no-rewrite check), `or-else(E,F)=E?idle:F`,
  `E ! = E ? (E !) : idle` (normalization to fixpoint).
- `match P s.t. C` / `xmatch` / `amatch` (test: top / extension / anywhere — no rewrite).
- `matchrew P s.t. C by x1 using E1, …` (match `P`, run `Eᵢ` on subterm `xᵢ`, rebuild).
- strategy `call` (named `s` / `s(args)`, resolved against `sd`/`csd` definitions).

## Architecture

A **work-queue solution search** (mirrors the C++ process model as an explicit state machine, A6's "RETHINK
highest risk"):
- `StrategySearch { queue, engine, seen, … }`; a *task* = `(dag, cont, …)` where `cont` is a stack of
  resolved strategy frames to apply in order. `next_solution()` pops a task; if `cont` is empty the `dag` is a
  solution; else it `decompose`s the top frame (idle→continue, fail→drop, `;`→push both, `|`→fork two tasks,
  `*`→fork idle-path + unfold, application→one task per one-step rewrite, …). Fair (`srewrite`) = `VecDeque`
  (BFS); dfs (`dsrewrite`) = stack (LIFO). Cycle detection: a `seen` set of `(hashcons(dag), cont-signature)`.
- **Counts**: drive every rule application + result reduction through the engine; read the engine's cumulative
  `rewrites()` at each solution emit. Order (BFS/DFS) → count, matching Maude's `srew`/`dsrew` counts.
- **Branch `?:`**: evaluate the test `E` to exhaustion via a nested `StrategySearch` (eager for the test — the
  lazy task-watch is a refinement; terminating tests are the norm). `matchrew` runs substrategies via nested
  searches on the bound subterms, then rebuilds.

## Phases (each ends at a conformance-verified milestone; commit per phase)

- **A — Parsing + AST. DONE.** Surface `StratExpr` enum + `StratDecl`/`StratDef`; `smod`/`sth` modules; the
  `srewrite`/`dsrewrite … using …` commands. Strategy-expr grammar with the precedence above.
- **B — Core interpreter. DONE.** A recursive solution enumerator (not the work-queue — see Status);
  `idle`/`fail`/application(`L`)/`all`/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+ derived)/`match`/`amatch` tests;
  the `srewrite`/`dsrewrite` REPL commands + output format. Conformance: the probed cases.
- **C — Definitions + calls. DONE.** `strat` decls + `sd`; resolve a parameterless call to its definition,
  recursion, `(dag, name)` cycle detection.
- **D — matchrew + conditions + substitutions + params. DONE.** `matchrew`/`amatchrew … [such that …] by … using
  …` (by-list cartesian product); **conditional rules** in application (equality/sort/matching fragments solved
  natively by a frontend `solve_frags` over the kernel's `ConditionFragment`s; rewrite `=>` fragments driven by
  the application's substrategies `L{E,…}`); the **application substitution** `L[x<-t]`; the `xmatch` test;
  **parameterized calls** `s(args)` via inline parameter→argument token substitution. A linearize-then-post-check
  matcher (`match_extend`) gives non-linear condition matching without seeding the kernel matcher. Conformance:
  21 added srew/dsrew cases, all values/order byte-identical (Maude 3.5.1).
- **E — meta + docs. DECISION: documented as a follow-on** (this plan's sanctioned outcome). The strategy *language*
  is complete (A–D); the strategy *meta* layer (`upStratDecls`/`upSds`/`metaParseStrategy`/`metaPrettyPrintStrategy`)
  is the META-LEVEL tower's **Stage-5 strategy tail**, kept inert. It is a META stage, not a wire-up — see
  `gaps.md` for the three concrete prerequisites (sort-aware constructor resolution; a non-desugaring parse so
  `try`/`not`/`test`/`or-else` survive round-trip; the StratExpr→Strategy up-translation + its inverse). Final
  roadmap/gaps updated.

## Status (final)
The interpreter is the **process + task model** of the Architecture section above (a `VecDeque` of
`(term, pending, task)` processes; FIFO for the fair `srewrite`, LIFO for `dsrewrite`; branch/`one`/`!` as
interleaved child tasks). It was first built as an eager recursive enumerator (matching `dsrewrite` only), then
rebuilt as the process queue once the C++ `StrategyLanguage/` scheduling was reverse-engineered — the FIFO ring
vs LIFO stack, the n-ary union/seq decompose timing, the per-step rule application, the slave-count task
exhaustion. **Fair `srewrite` is now byte-exact** — value, order, AND per-solution cumulative rewrite count, in
both modes (`strategy_fair_counts_through_repl`).

## Known hazards / deferrals (final state)
- **Eager sub-search count** — `matchrew`/`amatchrew` + conditional rewrite-condition substrategies run their
  sub-searches eagerly within a step, so their per-solution *count* can collapse when interleaved with parallel
  unequal-depth work (values/order/reachability faithful). Maude's parallel `SubtermTask`/`rewriteTask` odometer
  is the faithful mechanism; pinned via `dsrewrite` where the eager count coincides.
- **`one`/`!` order after a union** — a narrow forwarding-order swap of two solutions at the same count.
- **`xmatchrew`** — extension-match *rewriting* needs the engine to expose an extension match's residue for
  reassembly (narrow, assoc/AC-only). The `xmatch` *test* is done. Errors clearly at resolve.
- **`csd`** — a conditional strategy definition's runtime condition bindings must flow into the body, which the
  syntactic parameter-substitution mechanism cannot express. Errors clearly at resolve.
- **Strategy meta** — Phase E, above.
