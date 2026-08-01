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
// S3: variant-based narrowing rule descriptors and symbolic state search.
pub mod narrow;
// Pillar A: resumable `rewrite`/`frewrite` sessions over the rule machinery in `engine`.
pub mod rewrite;
// Pillar A-iv: the reachable-state graph + breadth-first `search`.
pub mod search;
pub mod smt;
pub mod sort;
pub mod symbol;
// T4: symbolic root rewriting with accumulated SMT constraints.
pub mod smt_search;
pub mod term;
// The matcher seam (A3) and the ACU theory (B1) are engine-internal for now — no public API surface
// yet (review: keep the closed LhsAutomaton/Subproblem enums crate-private until a cross-crate
// consumer exists).
pub(crate) mod acu;
pub(crate) mod acu_matcher;
pub(crate) mod au;
// B3: built-in operator reduction (the `special (id-hook …)` seam).
pub(crate) mod builtin;
pub(crate) mod cui;
pub(crate) mod diophantine;
// S1c: Contejean–Devie minimal-solution (Hilbert-basis) enumerator for ACU unification.
pub(crate) mod int_system;
// B3: arbitrary-precision arithmetic (D4 `malachite`) behind a wrapper; the bignum backend is never
// named outside `num`. `Nat` is re-exported because compact static `Term::Iter` nodes expose their
// scalar count to frontend printers and module transforms.
pub(crate) mod num;
pub use num::{Nat, double_to_string};
pub(crate) mod s;
// S1 (subsystems goal): the order-sorted-unification sort computation (SortBdds + AllSat).
pub(crate) mod sort_bdds;
pub(crate) mod theory;
pub use theory::RewriteMatchContext;
// S1 (subsystems goal): order-sorted unification — solved-form core, per-theory solvers, and the
// enumeration driver. `pub` so the frontend can supply a `NameCodes` source for fresh variables;
// the object-level `unify` command and `metaUnify` reach it through `Engine` methods.
pub mod unify;
// S2: folding variant narrowing and its resumable breadth-first search.
pub mod variant;
// T6: native variant satisfiability over FVP/OS-compact constructor decompositions.
pub mod variant_sat;
