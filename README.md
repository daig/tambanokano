<p align="center">
  <img src="assets/tnk.png" alt="tambanokano" width="220">
</p>

<h1 align="center">tambanokano</h1>

<p align="center">
  <strong>TNK</strong> — a Rust runtime for rewriting logic and membership equational logic
</p>

<p align="center">
  <a href="docs/book.md">Book</a>
  ·
  <a href="docs/cheatsheet.md">Quick Reference</a>
  ·
  <a href="docs/manual.md">Reference</a>
  ·
  <a href="CHANGELOG.md">Changelog</a>
  ·
  <a href="LICENSE">MIT</a>
</p>

---

tambanokano (TNK) is a Rust runtime for rewriting logic and membership equational logic. It provides a textual source and command surface for its documented feature set, plus reusable kernel, frontend, module, and session APIs.

Start with [The TNK Book](docs/book.md) for a guided, nonnormative path through modeling, search, verification, and Rust hosting. Keep [TNK Quick Reference](docs/cheatsheet.md) nearby for syntax, command selection, controls, and high-impact gotchas. Use the [TNK Language and System Reference](docs/manual.md) for exact syntax and semantics, API and state-transition contracts, feature status, and completeness/resource boundaries.

## Quick start

Requirements:

- Rust 1.90 or newer (edition 2024)
- a C toolchain for transitive native build dependencies
- optional: Z3 when enabling `smt-z3`
- optional: a Maude installation for the stock prelude and historical differential regression checks

Build the workspace:

```sh
cargo build --workspace --release
```

Create `hello.maude`:

```maude
fmod BOOLISH is
  sort Bool .
  ops true false : -> Bool [ctor] .
  op not_ : Bool -> Bool .
  eq not true = false .
  eq not false = true .
endfm

reduce not true .
```

Run it without an external prelude:

```sh
./target/release/tnk-repl -no-banner -no-prelude hello.maude
```

The command produces:

```text
reduce in BOOLISH : not true .
rewrites: 1
result Bool: false
```

With no file argument, `tnk-repl` starts an interactive session. It buffers multi-line modules, provides line editing and history on a terminal, and preserves resumable command state between submissions.

## Maude libraries

The core libraries do not load a prelude implicitly. The executable looks for `prelude.maude` in `MAUDE_LIB` and then the current directory unless `-no-prelude` is supplied.

For the bundled companion libraries and an external Maude installation:

```sh
export MAUDE_LIB="$PWD/share/maude-gpl:$PWD/share/tnk:/path/to/maude/src/Main"
./target/release/tnk-repl -no-banner program.maude
```

`share/maude-gpl` contains GPLv2-or-later Maude library sources. `share/tnk` contains the MIT-licensed TNK variant-satisfiability facade. See [NOTICE](NOTICE) before redistributing either directory.

## Command surface

The executable accepts:

```text
tnk-repl [-no-prelude] [-no-banner] [FILE]
```

The principal command families are:

- `reduce`, `rewrite`, `frewrite`, and `erewrite`
- `match`, `xmatch`, and rule application
- breadth-first `search` with graph and path inspection
- fair `srewrite` and depth-first `dsrewrite`
- order-sorted `unify` and irredundant unification
- variants, variant unification/matching, and narrowing
- SMT checks/search with a null backend or optional Z3 backend
- LTL model checking and satisfiability through loaded hooks
- module/view definition, imports, summation, renaming, and parameter instantiation
- metalevel reduction, rewriting, search, reflection, and child interpreters

See the [command catalogue](docs/manual.md#appendix-a--command-catalogue) and [feature matrix](docs/manual.md#23-current-feature-classification) for syntax, result contracts, continuation behavior, and explicit limits.

## Rust APIs

The primary embedding boundary is `tnk_session::Session`:

```rust
use tnk_session::Session;

let mut session = Session::new();
session.eval(
    "fmod BOOLISH is sort B . ops t f : -> B . endfm",
    false,
);

let result = session.eval("reduce t .", false);
assert_eq!(
    result.output,
    "reduce in BOOLISH : t .\nrewrites: 0\nresult B: t"
);
```

Workspace crates:

| Crate | Role |
|---|---|
| `tnk-core` | DAG runtime, order-sorted types, theories, rewriting, symbolic algorithms, SMT, and LTL |
| `tnk-frontend` | lexer, surface parser, mixfix grammar, term/command builders, strategy engine, and pretty-printer |
| `tnk-modules` | module and view databases, import flattening, renaming, instantiation, and reflection support |
| `tnk-session` | persistent modules, command execution, continuations, diagnostics, and external-object state |
| `tnk-repl` | terminal adapter and executable |

`tnk_core::Engine` is available for syntax-free embedding. IDs and DAG handles are engine-relative; callers must follow the lifecycle and rooting preconditions in [§22 of the reference](docs/manual.md#22-kernel-api).

Strict host-provided Rust reducers can participate in ordinary equational normalization. Register an immutable capability catalog before any module is built, then attach a strict eager operator with `HostFunctionSymbol`:

```rust
use tnk_core::host::{HostFunctionCatalog, codecs};
use tnk_session::Session;

let catalog = HostFunctionCatalog::builder()
    .register_typed1(
        "text.uppercase",
        codecs::string(),
        codecs::string(),
        |input| input.to_ascii_uppercase(),
    )
    .expect("register text.uppercase")
    .build();
let mut session = Session::builder().host_functions(catalog).build();
```

```maude
op <Strings> : -> String [ctor special (id-hook StringSymbol)] .
op uppercase : String -> String
  [special (id-hook HostFunctionSymbol (text.uppercase)
            op-hook stringSymbol (<Strings> : ~> String))] .
```

TNK normalizes every direct argument before the callback. Typed adapters borrow decoded byte-string inputs as `&[u8]` without cloning or allocating an input buffer, invoke the callback only after every argument decodes, and encode its owned `Vec<u8>` result through the resolved `stringSymbol`. A decode miss or `StrictOutcome::Decline` falls through to equations; a returned term is sort-checked, counted once, recorded as `RewriteKind::HostFunction` with the canonical key in structured and rendered traces, and normalized by TNK. Every other rewrite event has no host key. Canonical keys contain at least two dot-separated lowercase segments; each starts with `a`–`z`, contains only lowercase ASCII letters, digits, and interior `-`, and never ends in `-`. The lower-level `tnk_core::host::StrictReducer` API provides scoped DAG inspection and theory-aware free/ACU/AU/CUI construction without exposing raw `DagId` or `Engine` handles; an observed top `SymbolId` is comparison-only and cannot be passed to a builder. Reducers are trusted pure deterministic synchronous code: panics are not contained or converted, and TNK supplies no callback cancellation, timeout, or resource bound. See [Reference §16.1.1](docs/manual.md#1611-strict-rust-reducers) for the complete callback, fault atomicity, purity, and attachment contracts.

## Optional Z3 backend

The default build has no native SMT dependency and returns `Unknown` for SMT decisions. Enable Z3 across the workspace with:

```sh
cargo build --workspace --release --features tnk-repl/smt-z3
```

The `smt-z3` feature uses the `z3` crate without enabling one of its bundled build profiles, so Z3 must be available to that crate's normal discovery mechanism.

## Stability and boundaries

Version 0.1.0 makes the semantic clauses marked **Stable** in the reference release contracts. Rust module paths, exhaustive enum shapes, terminal presentation details, variants/narrowing, reflection, object-system behavior, and other surfaces marked **Experimental** may evolve within the 0.x series.

Notable explicit boundaries:

- `xmatchrew` and conditional strategy definitions (`csd`) are rejected.
- Memoization attributes and controls have no execution semantics.
- Conditional narrowing rules and several non-ground identity/idempotence unification cases are unsupported.
- There is no evaluation cancellation API or concurrency guarantee.
- Without `smt-z3`, SMT answers are `Unknown`.
- Custom Rust reduction is limited to trusted, pure, deterministic strict-eager reducers; lazy evaluator control, stateful callbacks, dynamic plugins, and sandboxing are not provided.

The complete list is [§24, Unsupported and intentionally absent behavior](docs/manual.md#24-unsupported-and-intentionally-absent-behavior).

## Documentation

- [The TNK Book](docs/book.md) — guided, nonnormative instruction through mental models, progressive workflows, extended examples, and exercises
- [TNK Quick Reference](docs/cheatsheet.md) — compact syntax, command, control, capability, and modeling-gotcha recall
- [Language and System Reference](docs/manual.md) — normative syntax, semantics, APIs, feature states, diagnostics, resource limits, and command catalogue
- [CHANGELOG](CHANGELOG.md) — release notes
- [NOTICE](NOTICE) — licensing boundaries and redistributed companion libraries
- [Developer issue index](docs/development/issues/README.md) — pending decisions, selected engineering work, known gaps, and intended features

## License

Original TNK source and project materials are MIT licensed under [LICENSE](LICENSE). This repository is a license aggregate: bundled Maude library sources and specified prelude-derived conformance fixtures are GPLv2-or-later. See [NOTICE](NOTICE) for the exact boundary.
