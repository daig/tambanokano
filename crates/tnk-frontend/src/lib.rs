//! `tnk-frontend` — the tambanokano frontend.
//!
//! Turns `.maude` *functional-module* text into `tnk-core` engine state (and, later, back via the
//! pretty-printer). A two-level pipeline (Maude's design): a fixed surface syntax (modules, declarations,
//! commands) over a hand-written [`lex`]er, then a per-module **mixfix** grammar built from the
//! signature and parsed by a plain Earley parser. The frontend is the **sole owner of surface syntax**
//! (prec/gather/mixfix tokens) — `tnk-core` stores only semantics — so it records its own `SymbolSyntax`
//! tables as it drives the kernel's constructor API.
//!
//! See `docs/migration/reports/A4-parser-mixfix.md` and `docs/migration/07-stageB-plan.md` §2 B4.

pub mod build_term;
pub mod cfparser;
pub mod grammar;
pub mod lex;
pub mod load;
pub mod sig;
pub mod surface;
