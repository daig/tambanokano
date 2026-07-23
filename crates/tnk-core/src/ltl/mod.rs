//! Linear-temporal-logic formulae, automata, and model checking.
//!
//! Phase M keeps the temporal pipeline inside the kernel: formula descent and automata consume the
//! active engine's DAGs directly, while frontend-resolved hook symbols remain typed values.

mod formula;
pub(crate) mod bdd;


pub use formula::TemporalHooks;
