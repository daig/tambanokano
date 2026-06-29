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

- **A — Parsing + AST.** Surface `StratExpr` enum + `StratDecl`/`StratDef`; `smod`/`sth` modules; the
  `srewrite`/`dsrewrite … using …` commands. Strategy-expr grammar with the precedence above. (Echo-testable.)
- **B — Core interpreter.** The work-queue search; `idle`/`fail`/application(`L`)/`all`/`top`/`;`/`|`/`*`/`+`/
  `?:`(+ derived)/`match` tests; the `srewrite`/`dsrewrite` REPL commands + output format. Conformance: the
  probed cases.
- **C — Definitions + calls.** `strat` decls + `sd`/`csd`; resolve a call to its definition (match the call
  term + `@ Sort`), recursion, cycle detection.
- **D — matchrew + rewrite-condition strategies.** `matchrew … by … using …`; application with substrategies
  for a rule's rewrite conditions; `one`.
- **E — meta + docs.** Wire `upStratDecls`/`upSds`/`metaParseStrategy`/`…` now that strats exist (or document
  as a follow-on); final roadmap/gaps.

## Known hazards / deferrals
- Exact `srew`/`dsrew` rewrite-count parity rides the queue order (gaps.md already accepts search-count
  divergences) — match where tractable, document deltas.
- Infinite test strategy inside `?:`/`!` (eager test eval) — terminating tests are the norm; the lazy
  task-watch model is the refinement.
- `matchrew`/conditional-`csd` need the condition machinery (shared with `ceq`/`crl`).
