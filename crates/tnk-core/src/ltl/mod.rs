//! Linear-temporal-logic formulae, automata, and model checking.
//!
//! Phase M keeps the temporal pipeline inside the kernel: formula descent and automata consume the
//! active engine's DAGs directly, while frontend-resolved hook symbols remain typed values.

// M1-M3 land the temporal pipeline before M4-M7 consume it through production hooks.
#![allow(dead_code)]

pub(crate) mod bdd;
mod buchi;
mod formula;
mod nat_set;
mod scc;
mod transition;
mod vwaa;

pub use formula::TemporalHooks;
