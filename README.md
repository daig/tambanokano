# tambanokano

tambanokano (TNK) is a Rust runtime for rewriting logic and membership equational logic. It provides a textual source and command surface for its documented feature set, plus reusable kernel, frontend, module, and session APIs.

Start with [The TNK Book](docs/book.md) for a guided, nonnormative path through modeling, search, verification, and Rust hosting. Use the [TNK Language and System Reference](docs/manual.md) for exact syntax and semantics, API and state-transition contracts, feature status, and completeness/resource boundaries.

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

The complete list is [§24, Unsupported and intentionally absent behavior](docs/manual.md#24-unsupported-and-intentionally-absent-behavior).

## Documentation

- [The TNK Book](docs/book.md) — guided, nonnormative instruction through mental models, progressive workflows, extended examples, and exercises
- [Language and System Reference](docs/manual.md) — normative syntax, semantics, APIs, feature states, diagnostics, resource limits, and command catalogue
- [CHANGELOG](CHANGELOG.md) — release notes
- [NOTICE](NOTICE) — licensing boundaries and redistributed companion libraries
- [Developer issue index](docs/development/issues/README.md) — pending decisions, selected engineering work, known gaps, and intended features

## License

Original TNK source and project materials are MIT licensed under [LICENSE](LICENSE). This repository is a license aggregate: bundled Maude library sources and specified prelude-derived conformance fixtures are GPLv2-or-later. See [NOTICE](NOTICE) for the exact boundary.
