//! DFS driver over [`WordLevel`] decision levels.
//!
//! Port of Maude's `Utility/wordSystem.{hh,cc}`.

use super::word_level::WordLevel;
use super::{FAILURE, INCOMPLETE, SUCCESS, Word};

/// Resumable solver for a system of constrained word equations.
pub(crate) struct WordSystem {
    current: Box<WordLevel>,
    level_stack: Vec<Box<WordLevel>>,
    incompleteness_flag: u8,
}

impl WordSystem {
    /// Construct a root level. Fresh abstract variables introduced by PIG-PUG begin at
    /// `nr_variables`; `nr_equations` preallocates the indexed word-equation slots.
    pub(crate) fn new(
        nr_variables: usize,
        nr_equations: usize,
        identity_optimizations: bool,
    ) -> Self {
        Self {
            current: Box::new(WordLevel::initial(
                nr_variables,
                nr_equations,
                identity_optimizations,
            )),
            level_stack: Vec::new(),
            incompleteness_flag: 0,
        }
    }

    pub(crate) fn set_theory_constraint(&mut self, variable: usize, theory_index: usize) {
        self.current.set_theory_constraint(variable, theory_index);
    }

    /// Set a word-length upper bound; zero means unbounded.
    pub(crate) fn set_upper_bound(&mut self, variable: usize, upper_bound: usize) {
        self.current.set_upper_bound(variable, upper_bound);
    }

    pub(crate) fn set_take_empty(&mut self, variable: usize) {
        self.current.set_take_empty(variable);
    }

    pub(crate) fn add_assignment(&mut self, variable: usize, value: Word) {
        self.current.add_assignment(variable, value);
    }

    pub(crate) fn add_equation(&mut self, index: usize, lhs: Word, rhs: Word) {
        self.current.add_equation(index, lhs, rhs);
    }

    pub(crate) fn add_null_equation(&mut self, word: Word) {
        self.current.add_null_equation(word);
    }

    /// Enumerate the next solution. The result is a bitwise combination of [`SUCCESS`] and
    /// [`INCOMPLETE`]; zero denotes exhausted complete failure.
    pub(crate) fn find_next_solution(&mut self) -> u8 {
        loop {
            let (flags, child) = self.current.find_next_partial_solution();
            if flags & INCOMPLETE != 0 {
                self.incompleteness_flag = INCOMPLETE;
            }
            if flags & SUCCESS != 0 {
                if let Some(child) = child {
                    let previous = std::mem::replace(&mut self.current, child);
                    self.level_stack.push(previous);
                } else {
                    return SUCCESS | self.incompleteness_flag;
                }
            } else if let Some(previous) = self.level_stack.pop() {
                self.current = previous;
            } else {
                return FAILURE | self.incompleteness_flag;
            }
        }
    }

    /// Read the assignment for an original abstract variable after a successful call.
    pub(crate) fn assignment(&self, variable: usize) -> &[usize] {
        self.current.assignment(variable)
    }

    /// Number of variables in the current complete solution, including generated abstract variables.
    pub(crate) fn nr_variables(&self) -> usize {
        self.current.nr_variables()
    }
}
