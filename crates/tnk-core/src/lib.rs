//! `tnk-core` — the tambanokano kernel.
//!
//! Term/DAG representation, garbage-collected node arena, order-sorted type
//! system, equational theories, and equational reduction, plus the higher
//! rewriting/search/symbolic layers built on that foundation.
//!
//! Design defaults used throughout the crate:
//! - instance-based [`engine::Engine`] (no global state); ids are engine-relative
//! - non-moving mark-sweep GC over an index [`arena::Arena`]; ids are stable for a
//!   node's lifetime
//! - enum-dispatch for the closed theory set; `dyn` only at open seams

pub mod arena;
pub mod dag;
pub mod descent;
pub mod engine;
pub mod external;
pub mod fresh;
pub mod id;
pub mod ltl;
pub mod root;
// Variant-based narrowing rule descriptors and symbolic state search.
pub mod narrow;
// Resumable rule-fair and position-fair rewriting sessions.
pub mod rewrite;
// Reachable-state graph and breadth-first search.
pub mod search;
pub mod smt;
pub mod sort;
pub mod symbol;
// Symbolic root rewriting with accumulated SMT constraints.
pub mod smt_search;
pub mod term;
// Theory matchers are engine internals; public callers use the Engine matching/reduction APIs.
pub(crate) mod acu;
pub(crate) mod acu_matcher;
pub(crate) mod au;
// Built-in operator reduction through `special (id-hook …)`.
pub(crate) mod builtin;
pub(crate) mod cui;
pub(crate) mod diophantine;
// Contejean–Devie minimal-solution enumeration for ACU unification.
pub(crate) mod int_system;
// Arbitrary-precision arithmetic (`malachite`) behind a crate-private wrapper; the backend is never
// named outside `num`. `Nat` is re-exported because compact static `Term::Iter` nodes expose their
// scalar count to frontend printers and module transforms.
pub(crate) mod num;
pub use num::{Nat, double_to_string};
pub(crate) mod s;
// Sort-BDD computation used by order-sorted unification.
pub(crate) mod sort_bdds;
pub(crate) mod theory;
pub use theory::RewriteMatchContext;
// Order-sorted unification: solved forms, per-theory solvers, and deterministic enumeration.
// Public so the frontend can provide fresh-variable name codes; object-level `unify` and the
// META-LEVEL unification family enter through Engine methods.
pub mod unify;
// Folding variant narrowing and its resumable breadth-first search.
pub mod variant;
// Native variant satisfiability over constructor decompositions.
pub mod variant_sat;
