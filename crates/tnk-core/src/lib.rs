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
// The matcher seam (A3) and the ACU theory (B1) are engine-internal for now — no public API surface
// yet (review: keep the closed LhsAutomaton/Subproblem enums crate-private until a cross-crate
// consumer exists).
pub(crate) mod acu;
pub(crate) mod au;
// B3: built-in operator reduction (the `special (id-hook …)` seam).
pub(crate) mod builtin;
pub(crate) mod cui;
// B3: arbitrary-precision arithmetic (D4 `malachite`) behind a wrapper; the bignum backend is never
// named outside `num`.
pub(crate) mod num;
pub(crate) mod s;
pub(crate) mod theory;
