//! `tnk-frontend` — the tambanokano frontend.
//!
//! Parses module text into `tnk-core` engine state and renders engine terms through the
//! pretty-printer. A two-level pipeline parses fixed surface syntax (modules,
//! declarations, commands) with the hand-written [`lex`]er, then parses terms with a
//! per-module **mixfix** grammar and a plain Earley parser. The frontend owns surface
//! syntax (precedence, gather bounds, and mixfix tokens), while `tnk-core` stores the
//! executable semantics. Frontend `SymbolSyntax` tables retain the information needed
//! by the grammar and pretty-printer.
//! Catalog-aware loaders accept an immutable [`tnk_core::host::HostFunctionCatalog`] before signature
//! construction; catalog-unaware entry points use an empty catalog.
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
