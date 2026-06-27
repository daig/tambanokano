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

**Phase 2 in progress.** Pillar A (the *rewriting* layer) is **done**: rules (`rl`/`crl` incl. the rewrite
`=>` condition), `rewrite`/`frewrite`, `search` (+ state graph, `such that`, `show path`/`graph`),
`continue` — all conformance-verified, so system modules (`mod`) run. Pillar B (parameterized programming) is
**done**, mechanism and corner cases: theories `fth`/`th`, views, parameterized modules + `X$Elt` + structured
sorts, instantiation `M{V}`, and the whole "Axis A" — view op-maps, import/target dedup, theory/module sorts,
and the entangled hard pair **parameterized views + free-vs-bound nested instantiation** (all three argument
kinds — module-view, by-parameter, theory-view — incl. `LIST{List{Nat}}` nesting, cross-kind ad-hoc
overloading with `(t).Sort` disambiguation, and structured-sort memberships). All a pure `tnk-modules`
`PreModule` transform, all conformance-verified. **Next:** the *real* container prelude additionally needs
`poly`/`Universal` polymorphism (a separate feature). Then strategies + objects/IO. See `roadmap.md`.

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
| `gaps.md` | known gaps | where the **built** engine differs from / simplifies Maude — accepted cosmetic divergences + deferred optimizations |
| `roadmap.md` | remaining plan | Phase 2 (system modules + parameterization + strategies + prelude) and Phase 3 (reflection + symbolic + verification) |
| `reports/A1–A8` | reference | per-subsystem deep-dives of the **C++ reference** — the detail behind the gaps and the roadmap |

The detailed **current behavior** lives in the code (the crates carry thorough module/function doc comments);
these docs are orientation, motivation, gaps, and plan — not a re-explanation of the source.

## Conformance discipline (the oracle, unchanged since Phase 0)

Every behavioral claim is checked **differentially against the reference binary**, never from memory:

```
~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null   # reference (C++)
./target/debug/tnk-repl <file>.maude < /dev/null                # ours
```

diffing **result value, result sort, rewrite count, termination**, and (where it matters) byte-for-byte
output. The `conformance/` directory holds the regression fixtures (`*.maude`), each transcribed from the
reference; `correctness-*.maude` pin a specific fixed divergence. Reference sources: C++ at
`~/code/maude-lang/Maude/src`, binary at `~/Downloads/Maude-3/maude`. Sanity anchor: `fib(22) = 186579`
rewrites.
