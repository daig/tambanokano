//! `tnk-core` — the tambanokano kernel.
//!
//! Covers layers **L0–L3** of the migration map (`docs/migration/01-architecture-map.md`):
//! the `Term`(static) / `DagNode`(runtime) representation, the garbage-collected node
//! arena, the order-sorted type system, the equational theories, and equational reduction.
//!
//! Foundational decisions live in `docs/migration/03-open-decisions.md`:
//! - **D1** instance-based [`engine::Engine`] (no global state); ids are engine-relative.
//! - **D2** non-moving mark-sweep GC over an index [`arena::Arena`]; ids are stable for a
//!   node's lifetime.
//! - **D3** enum-dispatch for the closed theory set; `dyn` only at open seams.

pub mod arena;
pub mod dag;
pub mod engine;
pub mod id;
pub mod root;
pub mod sort;
pub mod symbol;
pub mod term;
