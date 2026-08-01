//! Linear-temporal-logic formulae, automata, and model checking.
//!
//! Formula descent and automata consume the active engine's DAGs directly, while frontend-resolved hook
//! symbols remain typed values.

pub(crate) mod bdd;
mod buchi;
mod formula;
pub(crate) mod model_check;
mod nat_set;
pub(crate) mod sat_solve;
mod scc;
mod transition;
mod vwaa;

pub use formula::TemporalHooks;
