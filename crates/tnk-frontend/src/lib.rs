//! `tnk-frontend` — the tambanokano frontend.
//!
//! Turns `.maude` module text into `tnk-core` engine state (and back via the
//! pretty-printer). A two-level pipeline: a fixed surface syntax (modules,
//! declarations, commands) over a hand-written [`lex`]er, then a per-module
//! **mixfix** grammar built from the signature and parsed by a plain Earley
//! parser. The frontend is the **sole owner of surface syntax**
//! (prec/gather/mixfix tokens) — `tnk-core` stores only semantics — so it
//! records its own `SymbolSyntax` tables as it drives the kernel's constructor API.
//!

pub mod build_term;
pub mod cfparser;
pub mod grammar;
pub mod lex;
pub mod load;
pub mod oo_complete;
pub mod pretty;
pub mod rename_terms;
pub mod sig;
pub mod strategy;
pub mod surface;
