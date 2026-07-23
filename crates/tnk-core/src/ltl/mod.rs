//! Linear-temporal-logic formulae, automata, and model checking.
//!
//! Phase M keeps the temporal pipeline inside the kernel: formula descent and automata consume the
//! active engine's DAGs directly, while frontend-resolved hook symbols remain typed values.

// Staged temporal layers land before M5-M7 consume them through production hooks.
#![allow(dead_code)]

pub(crate) mod bdd;
mod buchi;
mod formula;
mod model_check;
mod nat_set;
mod scc;
mod transition;
mod vwaa;

pub use formula::TemporalHooks;
