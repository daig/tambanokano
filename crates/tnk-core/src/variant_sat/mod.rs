//! Native variant-satisfiability decision procedure for FVP/OS-compact constructor theories.
//!
//! This is independent of solver SMT: it uses folding variants, order-sorted unification, and
//! finite constructor-sort analysis. The META facade down-translates reflected terms once and calls
//! this module with a query-local formula.

mod analysis;
mod decision;
mod formula;

pub use analysis::{
    ConstructorAnalysis, Eligibility, EligibilityRejection, SortClassification, SortOverrides,
};
pub use decision::{Decision, VariantSatQuery, decide};
pub use formula::{Branch, Dnf, Formula, Literal};
