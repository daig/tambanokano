# tambanokano — docs

A from-scratch **Rust reimplementation of Maude** (a rewriting-logic / membership-equational-logic engine
and language), built as the base for a new extensible rewrite-system language. Not a line-by-line port:
Maude (C++) is the **conformance spec**, verified differentially against the reference binary, but the
design is re-derived for Rust (instance-based engine, index-arena GC, enum-dispatched theories — see the
decisions doc).

## Status

**Phase 1 + Phase 1.5 complete.** The functional engine is conformance-faithful on every well-formed module:
- **Kernel** (`tnk-core`): index-arena + mark-sweep GC; the free / ACU / AU / CUI / S(iter) / NA theories;
  order-sorted least sorts + memberships; conditional equations (`ceq`/`cmb`/`owise`/`:=`); operator
  attributes (`ctor`/`strat`); built-in data (BOOL/NAT/INT/RAT/FLOAT/STRING/QID) over `malachite` bignums;
  structure sharing (construction dedup + normal-form forwarding); cross-theory alien-subterm matching; full
  `trace`.
- **Frontend** (`tnk-frontend`): lexer → surface parser → per-module mixfix grammar → Earley parser → term
  build → Maude-faithful pretty-printer.
- **Modules** (`tnk-modules`): import/flatten (`protecting`/`extending`/`including`), summation `+`, renaming, theories/views/parameterized instantiation, and compositional strategy declarations/definitions.
- **REPL** (`tnk-repl`): `reduce`/`match`/`xmatch`, `show`/`select`/`set trace`, file load, output line-wrapping.

**Symbolic phase S complete (2026-07-21).** `tnk-core::unify` implements order-sorted unification modulo
free/S/CUI/AC/ACU/A/AU; `tnk-core::variant` provides layered variants, subsumption, filtered variant
unification/matching, and the shared one-step machinery; `tnk-core::narrow` owns the rooted, resumable v3
narrowing graph with fold/vfold, history, paths, goal unification, and centralized fresh-variable
families. Object commands, continuations/state displays, current and legacy `metaUnify*`/`metaVariant*`,
the in-scope `metaNarrow*` operations, and their persistent caches are live. Durable byte-exact gates:
S1 is 27/27 fixtures and 676 commands; S2 is 21/21 and 289; the live S3 gate is 16/16 (15 completion
fixtures plus one post-close regression), and all 169 primary commands also pass independently.

**Phase 2 in progress.** Pillar A (the *rewriting* layer) is **done**: rules (`rl`/`crl` incl. the rewrite
`=>` condition), `rewrite`/`frewrite`, `search` (+ state graph, `such that`, `show path`/`graph`),
`continue` — all conformance-verified, so system modules (`mod`) run. Pillar B (parameterized programming) is
**done**, mechanism and corner cases: theories `fth`/`th`, views, parameterized modules + `X$Elt` + structured
sorts, instantiation `M{V}`, and the whole "Axis A" — view op-maps, import/target dedup, theory/module sorts,
and the entangled hard pair **parameterized views + free-vs-bound nested instantiation** (all three argument
kinds — module-view, by-parameter, theory-view — incl. `LIST{List{Nat}}` nesting, cross-kind ad-hoc
overloading with `(t).Sort` disambiguation, and structured-sort memberships). All a pure `tnk-modules`
`PreModule` transform, all conformance-verified. **The real Maude prelude loads and reduces byte-identically**
— the whole data library (`BOOL`/`NAT`/`INT`/`RAT`/`FLOAT`/`STRING`/`QID`/`CONVERSION`, and the container
library `EXT-BOOL`/`SET`/`MAP`/`ARRAY`) *and* **the reflection core**: `META-LEVEL` builds, and its descent
family (`metaReduce`/`metaRewrite`/`metaApply`/`metaMatch`/`metaSearch`/`metaSearchPath`/… + the
`format`-attribute display) computes byte-identically. The META `up*`/query/parse layer, the strategy
language, LEXICAL hooks, and the object system (`omod`/`erewrite`/STD-STREAM) have since landed too.
**Phase T / SMT complete (2026-07-23).** The optional z3 lane implements the full typed SMT
language, exact number leaves, query-local incremental `check`, root-only constraint-bearing
`smt-search`, `continue`, and cached `metaCheck`/`metaSmtSearch`; T01–T10 are byte-exact over all
118 frozen commands. The default build remains pure Rust and degrades those solver queries to
`undecided`/no solutions. Native FVP/OS-compact variant satisfiability and the source-compatible
`VAR-SAT-TOOL` facade pass 27/27 contract results without z3, model checking, or copied prototype
source; the untouched pinned Maude-2.7 oracle also passes its separately recorded 27 results.
The complete Phase-T scoreboard is **11/11 PASS**. **Phase M / model checking is complete
(2026-07-23):** M0–M7 provide the exact LTL→Büchi pipeline, nested DFS, shared state graph,
typed model/SAT hooks, lassos, verbose statistics, and SAT prime implicants. The frozen
Maude-3.5.1 gate is **10/10 fixtures / 50 commands PASS**, including M05 round-robin,
M08/M09 dining philosophers, and all eight M10 `satSolve`/`tautCheck` commands.

**Phase I-S / local synchronous meta-interpreters is complete (2026-07-24).**
`tnk-session::Session` is the reusable, host-owned semantic layer; `tnk-repl` is its thin
terminal adapter. The production external-message seam suspends and resumes object-message
passes without exposing engine-local handles, while Session owns isolated local child
interpreters and the supported lifecycle, module/view, evaluation, search, symbolic, and
continuation protocols. The frozen live-oracle gate is **27/27 fixtures PASS**, including
walking-skeleton, pass-boundary, lifecycle/error, multi-child isolation, and GC probes.
The retained release, audit, legacy, U/V/N/T/M gates remain green. The selected goal has
stopped here: cancellation and thread-backed `newProcess` coordination remain the separate,
unstarted Phase I-C.

**TNK-005 / compositional strategy-module imports is complete (2026-07-26).**
Named `strat`/`sd` payloads now preserve oracle-derived origin, order, overload/lhs dispatch, donor-home parsing, transforms, reflection, and session invalidation across the supported module algebra. The six-fixture `A3f`–`A3j`/`A5g` matrix is byte-identical to Maude; the binding record is `tnk-005-strategy-imports-goal.md`.

**The verified current state—including every known deviation—is `../../fable-audit.md`** (status
refreshed 2026-07-26); the forward plan is `roadmap.md`.

## Crate layout

```
tnk-core      kernel: arena/GC, theories, matcher seam, sort system, reduce loop, built-ins, trace
   ↑
tnk-frontend  lexer, mixfix grammar + parser, term builder, pretty-printer
   ↑
tnk-modules   module DB + flatten (a pure PreModule→PreModule transform), summation, renaming
   ↑
tnk-session   persistent modules/views, command evaluation, reflection caches, continuations
   ↑
tnk-repl      thin terminal adapter: color/wrapping policy, line editing, prompts, CLI
```

## The living docs (and what each is for)

| Doc | Kind | Contents |
|---|---|---|
| `README.md` (this) | orientation | what it is, status, crate map, doc index, the conformance discipline |
| `architecture map`<br>(`01-architecture-map.md`) | current + reference | Maude's layered architecture, the feature inventory (with build status), and the cross-cutting C++→Rust strategy |
| `decisions`<br>(`03-open-decisions.md`) | motivation | binding decisions **D1–D12**: engine/GC/dispatch/data backends, host-owned IO, naming, correctness defaults, REPL identity, and Phase-I concurrency |
| `../../fable-audit.md` | conformance ground truth | the 2026-07-01 differential audit vs Maude 3.5.1 — verified deviations, missing features, non-obvious fix constraints (supersedes the retired `gaps.md`) |
| `roadmap.md` | remaining plan | correctness-first completion plan (post-audit): panics/wrong values → counts → input acceptance → the two architecture reworks → diagnostics/tool surface → new subsystems |
| `correctness-goal.md` | goal contract | the frozen fixture manifest + scoreboard metric, decision defaults, and completion criteria driving the correctness goal (`/goal`) |
| `subsystems-goal.md` | subsystem contract | completed S/T/M/I-S ledger; future I-C scope, invariants, manifests, and gates |
| `tnk-005-strategy-imports-goal.md` | completed goal contract | closed TNK-005 `/goal`: oracle matrix, module/strategy invariants, implementation record, retained fixtures, and verified completion gates |
| `tnk-011-collapse-memberships-goal.md` | completed goal contract | closed TNK-011 `/goal`: ACU/two-sided-AU/CUI collapse indexing, single-compile arena, retained oracle/trace matrix, explicit one-sided-AU boundary, and verified completion gates |
| `remaining-plans/` | implementation records | source-verified plans and completion notes for AU, variants, narrowing, SMT, model checking, and the split synchronous/concurrent Phase I |
| `reports/A1–A8` | reference | per-subsystem deep-dives of the **C++ reference** — the detail behind the gaps and the roadmap |

The detailed **current behavior** lives in the code (the crates carry thorough module/function doc comments);
these docs are orientation, motivation, gaps, and plan — not a re-explanation of the source.

## Conformance discipline (the oracle, unchanged since Phase 0)

Every behavioral claim is checked **differentially against the reference binary**, never from memory:

```sh
MAUDE_LIB=~/code/maude-lang/maude/src/Main ~/.local/bin/maude -no-banner <file.maude < /dev/null
./target/release/tnk-repl <file.maude < /dev/null
```

diffing **result value, result sort, rewrite count, termination**, and (where it matters) byte-for-byte
output. The `conformance/` directory holds the regression fixtures (`*.maude`), each transcribed from the
reference; `correctness-*.maude` pin a specific fixed divergence. Reference sources: C++ at
`~/code/maude-lang/maude/src`, binary at `~/.local/bin/maude`. Sanity anchor: `fib(22) = 186579` rewrites.
