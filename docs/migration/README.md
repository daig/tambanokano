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
- **Modules** (`tnk-modules`): import/flatten (`protecting`/`extending`/`including`), summation `+`, renaming.
- **REPL** (`tnk-repl`): `reduce`/`match`/`xmatch`, `show`/`select`/`set trace`, file load, output line-wrapping.

**Symbolic phases S1 + S2 complete (2026-07-19).** `tnk-core::unify` implements order-sorted unification
modulo free/S/CUI/AC/ACU/A/AU; `tnk-core::variant` adds layered folding variant narrowing, irredundant
subsumption, variant unification, matching, blockers, and centralized fresh-variable families. All
object-level and current/legacy `metaUnify*`/`metaVariant*` surfaces are live, including resumable command
enumeration and persistent meta caches. Durable gates: S1 is 27/27 fixtures and 676 byte-exact commands;
S2 is 21/21 and 289. S3 narrowing is READY and next, with 15 frozen fixtures and 168 primary commands.

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
**The verified current state — including every known deviation — is `../../fable-audit.md`** (status
refreshed 2026-07-19); the forward plan is `roadmap.md`.

## Crate layout

```
tnk-core      kernel: arena/GC, theories, matcher seam, sort system, reduce loop, built-ins, trace
   ↑
tnk-frontend  lexer, mixfix grammar + parser, term builder, pretty-printer + output wrapper
   ↑
tnk-modules   module DB + flatten (a pure PreModule→PreModule transform), summation, renaming
   ↑
tnk-repl      the interactive shell (lib + bin); reuses everything below
```

## The living docs (and what each is for)

| Doc | Kind | Contents |
|---|---|---|
| `README.md` (this) | orientation | what it is, status, crate map, doc index, the conformance discipline |
| `architecture map`<br>(`01-architecture-map.md`) | current + reference | Maude's layered architecture, the feature inventory (with build status), and the cross-cutting C++→Rust strategy |
| `decisions`<br>(`03-open-decisions.md`) | motivation | the foundational decisions **D1–D8** (engine model, GC, dispatch, bignum, IO, BDD, SMT, naming) + why |
| `../../fable-audit.md` | conformance ground truth | the 2026-07-01 differential audit vs Maude 3.5.1 — verified deviations, missing features, non-obvious fix constraints (supersedes the retired `gaps.md`) |
| `roadmap.md` | remaining plan | correctness-first completion plan (post-audit): panics/wrong values → counts → input acceptance → the two architecture reworks → diagnostics/tool surface → new subsystems |
| `correctness-goal.md` | goal contract | the frozen fixture manifest + scoreboard metric, decision defaults, and completion criteria driving the correctness goal (`/goal`) |
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
