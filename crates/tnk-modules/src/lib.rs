//! `tnk-modules` — the tambanokano module system (B5, non-parameterized).
//!
//! The frontend ([`tnk_frontend`]) turns one `fmod … endfm` into one isolated `Engine`. This crate adds
//! the layer above it: a [`ModuleDb`](db::ModuleDb) of parsed modules and a **flattener** that resolves a
//! module's transitive `protecting`/`extending`/`including` import closure (plus summation `+` and
//! renaming `* (…)`) into ONE combined module, which the unchanged frontend pipeline then builds.
//!
//! Flattening is a **pure `PreModule → PreModule` transform** (decision #5 — not the C++ in-place
//! "donation"): the import modes do not change which declarations are imported (a semantic-check
//! annotation only), so all three flatten identically. [`load::load_program`] is the file-level entry,
//! and the basis for the B5 REPL (`tnk-repl`) next round.

pub mod db;
pub mod flatten;
pub mod load;
pub mod rename;
pub mod view;
