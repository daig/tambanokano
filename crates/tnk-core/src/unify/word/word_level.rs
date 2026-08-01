//! One resumable level in the system-of-word-equations search.
//!

use std::cell::RefCell;
use std::collections::{BTreeSet, VecDeque};
use std::rc::Rc;

use super::constraint::VariableConstraint;
use super::pigpug::{ConstraintMap, LINEAR, NONLINEAR, PigPug, STRICT_LEFT_LINEAR, Subst};
use super::{FAILURE, SUCCESS, Word};

const NOT_YET_CHOSEN: i32 = -2;
const NO_EQUATION: i32 = -1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LevelType {
    Initial,
    Selection,
    PigPug,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Result {
    Fail,
    Done,
    Changed,
    Continue,
    Unsafe,
}

#[derive(Clone, Default)]
struct Equation {
    lhs: Word,
    rhs: Word,
}

#[derive(Default)]
struct SelectionDedup {
    identity_variables: Vec<usize>,
    final_combinations: BTreeSet<usize>,
}

pub(super) struct WordLevel {
    level_type: LevelType,
    identity_optimizations: bool,
    constraint_map: ConstraintMap,
    null_equations: VecDeque<Word>,
    partial_solution: Subst,
    unsafe_assignments: BTreeSet<usize>,
    unsolved_equations: Vec<Equation>,
    chosen_equation: i32,
    pig_pug: Option<PigPug>,
    identity_variables: Vec<usize>,
    selection: usize,
    nr_selections: usize,
    selection_dedup: Option<Rc<RefCell<SelectionDedup>>>,
}

impl WordLevel {
    pub(super) fn initial(
        nr_variables: usize,
        nr_equations: usize,
        identity_optimizations: bool,
    ) -> Self {
        Self::new(
            LevelType::Initial,
            nr_variables,
            nr_equations,
            identity_optimizations,
            Some(Rc::new(RefCell::new(SelectionDedup::default()))),
        )
    }

    fn new(
        level_type: LevelType,
        nr_variables: usize,
        nr_equations: usize,
        identity_optimizations: bool,
        selection_dedup: Option<Rc<RefCell<SelectionDedup>>>,
    ) -> Self {
        Self {
            level_type,
            identity_optimizations,
            constraint_map: vec![VariableConstraint::default(); nr_variables],
            null_equations: VecDeque::new(),
            partial_solution: (0..nr_variables).map(|i| vec![i]).collect(),
            unsafe_assignments: BTreeSet::new(),
            unsolved_equations: vec![Equation::default(); nr_equations],
            chosen_equation: NOT_YET_CHOSEN,
            pig_pug: None,
            identity_variables: Vec::new(),
            selection: 0,
            nr_selections: 0,
            selection_dedup,
        }
    }

    pub(super) fn set_theory_constraint(&mut self, variable: usize, theory_index: usize) {
        self.constraint_map[variable].set_theory_constraint(theory_index);
    }

    pub(super) fn set_upper_bound(&mut self, variable: usize, upper_bound: usize) {
        self.constraint_map[variable].set_upper_bound(upper_bound);
    }

    pub(super) fn set_take_empty(&mut self, variable: usize) {
        self.constraint_map[variable].set_take_empty();
    }

    pub(super) fn add_assignment(&mut self, variable: usize, value: Word) {
        if self.partial_solution[variable].len() == 1
            && self.partial_solution[variable][0] == variable
        {
            self.partial_solution[variable] = value;
        } else {
            let rhs = self.partial_solution[variable].clone();
            self.unsolved_equations.push(Equation { lhs: value, rhs });
        }
    }

    pub(super) fn add_equation(&mut self, index: usize, lhs: Word, rhs: Word) {
        self.unsolved_equations[index] = Equation { lhs, rhs };
    }

    pub(super) fn add_null_equation(&mut self, word: Word) {
        self.null_equations.push_back(word);
    }

    pub(super) fn assignment(&self, variable: usize) -> &[usize] {
        &self.partial_solution[variable]
    }

    pub(super) fn nr_variables(&self) -> usize {
        self.partial_solution.len()
    }

    pub(super) fn find_next_partial_solution(&mut self) -> (u8, Option<Box<WordLevel>>) {
        if self.selection != 0 {
            return self.explore_selections();
        }
        if self.chosen_equation == NOT_YET_CHOSEN {
            if !self.simplify() {
                return (FAILURE, None);
            }
            if self.level_type != LevelType::PigPug && !self.level_feasible_without_collapse() {
                return if self.level_type == LevelType::Initial {
                    self.try_selection()
                } else {
                    (FAILURE, None)
                };
            }
            if self.level_type == LevelType::Selection && !self.insert_combination() {
                return (FAILURE, None);
            }
            let linearity = self.choose_equation();
            if self.chosen_equation == NO_EQUATION {
                return (SUCCESS, None);
            }
            self.make_pig_pug(linearity);
        }
        if self.pig_pug.is_none() {
            return if self.level_type == LevelType::Initial {
                self.try_selection()
            } else {
                (FAILURE, None)
            };
        }
        let mut unifier = Subst::new();
        let mut new_constraint_map = ConstraintMap::new();
        let (flags, next_fresh_variable) = self
            .pig_pug
            .as_mut()
            .unwrap()
            .get_next_unifier(&mut unifier, &mut new_constraint_map);
        let Some(next_fresh_variable) = next_fresh_variable else {
            if self.level_type == LevelType::Initial {
                let (selection_flags, child) = self.try_selection();
                return (selection_flags | flags, child);
            }
            return (flags, None);
        };
        let child = self.make_new_level(unifier, new_constraint_map, next_fresh_variable);
        (flags, Some(Box::new(child)))
    }

    fn simplify(&mut self) -> bool {
        if self.level_type == LevelType::Initial && !self.handle_initial_occurs_check_failure() {
            return false;
        }
        if self.level_type != LevelType::PigPug && !self.handle_null_equations() {
            return false;
        }
        if !self.fully_expand_assignments() {
            return false;
        }
        loop {
            match self.simplify_equations() {
                Result::Fail => return false,
                Result::Done => break,
                _ => {}
            }
        }
        true
    }

    fn make_new_level(
        &self,
        unifier: Subst,
        new_constraint_map: ConstraintMap,
        next_fresh_variable: usize,
    ) -> Self {
        let equation_count = self
            .unsolved_equations
            .iter()
            .filter(|equation| !equation.lhs.is_empty())
            .count();
        let mut next = Self::new(
            LevelType::PigPug,
            next_fresh_variable,
            equation_count - 1,
            self.identity_optimizations,
            None,
        );
        next.constraint_map = new_constraint_map;
        for (i, current) in self.partial_solution.iter().enumerate() {
            let value = if unifier[i].len() == 1 && unifier[i][0] == i {
                current.clone()
            } else {
                unifier[i].clone()
            };
            next.add_assignment(i, value);
        }
        let mut equation_index = 0;
        for (i, equation) in self.unsolved_equations.iter().enumerate() {
            if i != self.chosen_equation as usize && !equation.lhs.is_empty() {
                next.add_equation(equation_index, equation.lhs.clone(), equation.rhs.clone());
                equation_index += 1;
            }
        }
        next
    }

    fn choose_equation(&mut self) -> u8 {
        self.chosen_equation = NO_EQUATION;
        for i in 0..self.unsolved_equations.len() {
            if self.unsolved_equations[i].lhs.is_empty() {
                continue;
            }
            let (lhs_occurs, lhs_nonlinear) =
                self.check_unconstrained_variables(&self.unsolved_equations[i].lhs);
            let (rhs_occurs, rhs_nonlinear) =
                self.check_unconstrained_variables(&self.unsolved_equations[i].rhs);
            if lhs_occurs.is_disjoint(&rhs_occurs) {
                if lhs_nonlinear.is_empty() {
                    self.chosen_equation = i as i32;
                    return if rhs_nonlinear.is_empty() {
                        LINEAR
                    } else {
                        STRICT_LEFT_LINEAR
                    };
                }
                if rhs_nonlinear.is_empty() {
                    let equation = &mut self.unsolved_equations[i];
                    std::mem::swap(&mut equation.lhs, &mut equation.rhs);
                    self.chosen_equation = i as i32;
                    return STRICT_LEFT_LINEAR;
                }
                self.chosen_equation = i as i32;
            }
            if self.chosen_equation == NO_EQUATION {
                self.chosen_equation = i as i32;
            }
        }
        NONLINEAR
    }

    fn check_unconstrained_variables(&self, word: &Word) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let mut occurs = BTreeSet::new();
        let mut nonlinear = BTreeSet::new();
        for &variable in word {
            if self.constraint_map[variable].is_unbounded() && !occurs.insert(variable) {
                nonlinear.insert(variable);
            }
        }
        (occurs, nonlinear)
    }

    fn make_pig_pug(&mut self, linearity: u8) {
        let equation = &self.unsolved_equations[self.chosen_equation as usize];
        let nr_variables = self.partial_solution.len();
        let use_equate_optimization = self.identity_optimizations
            && linearity == LINEAR
            && self.unsolved_equations.len() == 1;
        self.pig_pug = Some(PigPug::new(
            &equation.lhs,
            &equation.rhs,
            &self.constraint_map,
            nr_variables - 1,
            nr_variables,
            linearity,
            use_equate_optimization,
        ));
    }

    // Assignment checking and expansion: normal (collapse-free) case.

    fn check_assignment_normal_case(&mut self, i: usize) -> Result {
        let upper_bound = self.constraint_map[i].upper_bound();
        if upper_bound == 0 {
            return Result::Done;
        }
        let word_size = self.partial_solution[i].len();
        if word_size == 0 {
            return Result::Done;
        }
        if word_size == 1 {
            let rhs = self.partial_solution[i][0];
            if rhs == i {
                return Result::Done;
            }
            let mut rhs_constraint = self.constraint_map[rhs];
            if !rhs_constraint.intersect(self.constraint_map[i]) {
                return Result::Fail;
            }
            if self.constraint_map[rhs] == rhs_constraint {
                return Result::Done;
            }
            self.constraint_map[rhs] = rhs_constraint;
            return Result::Changed;
        }
        if word_size > upper_bound {
            return Result::Fail;
        }
        let new_bound = upper_bound - word_size + 1;
        let mut result = Result::Done;
        for &variable in &self.partial_solution[i] {
            let bound = self.constraint_map[variable].upper_bound();
            if bound == 0 || new_bound < bound {
                self.constraint_map[variable].set_upper_bound(new_bound);
                result = Result::Changed;
            }
        }
        result
    }

    fn check_assignments_normal_case(&mut self) -> bool {
        for i in 0..self.partial_solution.len() {
            if self.check_assignment_normal_case(i) == Result::Fail {
                return false;
            }
        }
        true
    }

    fn really_expand_assignment_normal_case(&mut self, i: usize) -> bool {
        let old = self.partial_solution[i].clone();
        let mut new_word = Word::new();
        for variable in old {
            debug_assert_ne!(variable, i);
            let assigned = &self.partial_solution[variable];
            if assigned.len() == 1 && assigned[0] == variable {
                new_word.push(variable);
            } else if Self::append_check_occurs(&mut new_word, assigned, i) {
                return false;
            }
        }
        self.partial_solution[i] = new_word;
        true
    }

    fn expand_assignment_normal_case(&mut self, i: usize) -> Result {
        for &variable in &self.partial_solution[i] {
            if variable == i {
                debug_assert_eq!(self.partial_solution[i].len(), 1);
                return Result::Done;
            }
            let assigned = &self.partial_solution[variable];
            if assigned.len() != 1 || assigned[0] != variable {
                return if self.really_expand_assignment_normal_case(i) {
                    Result::Changed
                } else {
                    Result::Fail
                };
            }
        }
        Result::Done
    }

    fn expand_assignments_normal_case(&mut self) -> Result {
        let mut changed = false;
        for i in 0..self.partial_solution.len() {
            match self.expand_assignment_normal_case(i) {
                Result::Fail => return Result::Fail,
                Result::Changed => changed = true,
                _ => {}
            }
        }
        if changed {
            Result::Changed
        } else {
            Result::Done
        }
    }

    fn expand_assignments_to_fixed_point_normal_case(&mut self) -> bool {
        loop {
            match self.expand_assignments_normal_case() {
                Result::Fail => return false,
                Result::Done => break,
                _ => {}
            }
        }
        self.check_assignments_normal_case()
    }

    // Assignment checking and expansion: collapse case.

    fn check_assignment_collapse_case(&mut self, i: usize) -> Result {
        self.unsafe_assignments.remove(&i);
        let upper_bound = self.constraint_map[i].upper_bound();
        if upper_bound == 0 {
            return Result::Done;
        }
        let word = self.partial_solution[i].clone();
        let word_size = word.len();
        if word_size == 0 {
            return Result::Done;
        }
        if word_size == 1 {
            let rhs = word[0];
            if rhs == i {
                return Result::Done;
            }
            let mut rhs_constraint = self.constraint_map[rhs];
            if !rhs_constraint.intersect(self.constraint_map[i]) {
                return Result::Fail;
            }
            if self.constraint_map[rhs] == rhs_constraint {
                return Result::Done;
            }
            self.constraint_map[rhs] = rhs_constraint;
            return Result::Changed;
        }
        let needed_bound = word
            .iter()
            .filter(|&&variable| !self.constraint_map[variable].can_take_empty())
            .count();
        if needed_bound > upper_bound {
            return Result::Fail;
        }
        if needed_bound == upper_bound {
            let mut changed = false;
            for variable in word {
                if self.constraint_map[variable].can_take_empty() {
                    changed |= self.make_empty_assignment(variable);
                } else if self.constraint_map[variable].upper_bound() != 1 {
                    self.constraint_map[variable].set_upper_bound(1);
                    changed = true;
                }
            }
            if changed {
                return if self.handle_null_equations() {
                    Result::Changed
                } else {
                    Result::Fail
                };
            }
            return Result::Done;
        }
        if word_size > upper_bound {
            self.unsafe_assignments.insert(i);
            return Result::Done;
        }
        let mut result = Result::Done;
        let bound_for_take_empty = upper_bound - needed_bound;
        for variable in word {
            let new_bound = if self.constraint_map[variable].can_take_empty() {
                bound_for_take_empty
            } else {
                bound_for_take_empty + 1
            };
            let old_bound = self.constraint_map[variable].upper_bound();
            if old_bound == 0 || new_bound < old_bound {
                self.constraint_map[variable].set_upper_bound(new_bound);
                result = Result::Changed;
            }
        }
        result
    }

    fn check_assignments_collapse_case(&mut self) -> Result {
        let mut changed = false;
        for i in 0..self.partial_solution.len() {
            match self.check_assignment_collapse_case(i) {
                Result::Fail => return Result::Fail,
                Result::Changed => changed = true,
                _ => {}
            }
        }
        if changed {
            Result::Changed
        } else {
            Result::Done
        }
    }

    fn check_assignments_to_fixed_point_collapse_case(&mut self) -> bool {
        loop {
            match self.check_assignments_collapse_case() {
                Result::Fail => return false,
                Result::Done => return true,
                _ => {}
            }
        }
    }

    fn really_expand_assignment_collapse_case(&mut self, i: usize) -> bool {
        let old = self.partial_solution[i].clone();
        let mut new_word = Word::new();
        let mut occurs_check_failure = false;
        for variable in old {
            debug_assert_ne!(variable, i);
            if self.unsafe_assignments.contains(&variable) {
                new_word.push(variable);
            } else {
                let assigned = &self.partial_solution[variable];
                if assigned.len() == 1 && assigned[0] == variable {
                    new_word.push(variable);
                } else {
                    occurs_check_failure |= Self::append_check_occurs(&mut new_word, assigned, i);
                }
            }
        }
        if occurs_check_failure {
            return self.resolve_occurs_check_failure(i, &new_word);
        }
        self.partial_solution[i] = new_word;
        match self.check_assignment_collapse_case(i) {
            Result::Done => true,
            Result::Changed => self.check_assignments_to_fixed_point_collapse_case(),
            _ => false,
        }
    }

    fn expand_assignment_collapse_case(&mut self, i: usize) -> Result {
        let word = self.partial_solution[i].clone();
        for variable in word {
            if variable == i {
                debug_assert_eq!(self.partial_solution[i].len(), 1);
                return Result::Done;
            }
            if !self.unsafe_assignments.contains(&variable) {
                let assigned = &self.partial_solution[variable];
                if assigned.len() != 1 || assigned[0] != variable {
                    return if self.really_expand_assignment_collapse_case(i) {
                        Result::Changed
                    } else {
                        Result::Fail
                    };
                }
            }
        }
        Result::Done
    }

    fn expand_assignments_collapse_case(&mut self) -> Result {
        let mut changed = false;
        for i in 0..self.partial_solution.len() {
            match self.expand_assignment_collapse_case(i) {
                Result::Fail => return Result::Fail,
                Result::Changed => changed = true,
                _ => {}
            }
        }
        if changed {
            Result::Changed
        } else {
            Result::Done
        }
    }

    fn expand_assignments_to_fixed_point_collapse_case(&mut self) -> bool {
        if !self.check_assignments_to_fixed_point_collapse_case() {
            return false;
        }
        loop {
            match self.expand_assignments_collapse_case() {
                Result::Fail => return false,
                Result::Done => return true,
                _ => {}
            }
        }
    }

    fn fully_expand_assignments(&mut self) -> bool {
        if self.level_type == LevelType::PigPug {
            self.expand_assignments_to_fixed_point_normal_case()
        } else {
            self.expand_assignments_to_fixed_point_collapse_case()
        }
    }

    fn append_check_occurs(new_word: &mut Word, word: &Word, variable: usize) -> bool {
        let mut occurs = false;
        for &item in word {
            new_word.push(item);
            occurs |= item == variable;
        }
        occurs
    }

    fn handle_initial_occurs_check_failure(&mut self) -> bool {
        for i in 0..self.partial_solution.len() {
            let word = self.partial_solution[i].clone();
            if word.len() > 1 && word.contains(&i) && !self.resolve_occurs_check_failure(i, &word) {
                return false;
            }
        }
        true
    }

    // Null equations and collapse-resolved occurs checks.

    fn make_empty_assignment(&mut self, variable: usize) -> bool {
        if self.partial_solution[variable].is_empty() {
            return false;
        }
        if self.partial_solution[variable].len() != 1
            || self.partial_solution[variable][0] != variable
        {
            self.null_equations
                .push_back(self.partial_solution[variable].clone());
        }
        self.partial_solution[variable].clear();
        true
    }

    fn handle_null_equations(&mut self) -> bool {
        debug_assert_ne!(self.level_type, LevelType::PigPug);
        while let Some(word) = self.null_equations.pop_front() {
            for variable in word {
                if self.constraint_map[variable].can_take_empty() {
                    self.make_empty_assignment(variable);
                } else {
                    return false;
                }
            }
        }
        true
    }

    fn resolve_occurs_check_failure(&mut self, index: usize, new_value: &Word) -> bool {
        debug_assert_ne!(self.level_type, LevelType::PigPug);
        let mut nr_occurrences = 0;
        for &variable in new_value {
            if variable == index {
                nr_occurrences += 1;
            } else if self.constraint_map[variable].can_take_empty() {
                self.make_empty_assignment(variable);
            } else {
                return false;
            }
        }
        debug_assert!(nr_occurrences >= 1);
        if nr_occurrences > 1 {
            if self.constraint_map[index].can_take_empty() {
                self.partial_solution[index].clear();
            } else {
                return false;
            }
        } else {
            self.partial_solution[index] = vec![index];
        }
        self.handle_null_equations()
    }

    // Equation simplification.

    fn simplify_equations(&mut self) -> Result {
        let mut changed = false;
        for i in 0..self.unsolved_equations.len() {
            match self.simplify_equation(i) {
                Result::Fail => return Result::Fail,
                Result::Changed => {
                    changed = true;
                    if !self.fully_expand_assignments() {
                        return Result::Fail;
                    }
                }
                _ => {}
            }
        }
        if changed {
            Result::Changed
        } else {
            Result::Done
        }
    }

    fn expand_word(&self, old_word: &Word) -> Word {
        let mut new_word = Word::new();
        for &variable in old_word {
            if self.unsafe_assignments.contains(&variable) {
                new_word.push(variable);
            } else {
                new_word.extend_from_slice(&self.partial_solution[variable]);
            }
        }
        new_word
    }

    fn update_remainder(&self, word: &mut Word, left: usize, right: usize) {
        if left > right {
            return;
        }
        for item in &mut word[left..=right] {
            if !self.unsafe_assignments.contains(item) {
                *item = self.partial_solution[*item][0];
            }
        }
    }

    fn copy_back(source: &Word, left: usize, right: usize) -> Word {
        source[left..=right].to_vec()
    }

    fn check_for_null(&mut self, lhs: &Word, rhs: &Word) -> Result {
        debug_assert_ne!(self.level_type, LevelType::PigPug);
        if lhs.is_empty() {
            if rhs.is_empty() {
                return Result::Done;
            }
            self.null_equations.push_back(rhs.clone());
            return Result::Changed;
        }
        if rhs.is_empty() {
            self.null_equations.push_back(lhs.clone());
            return Result::Changed;
        }
        Result::Continue
    }

    fn simplify_equation(&mut self, equation_index: usize) -> Result {
        if self.unsolved_equations[equation_index].lhs.is_empty() {
            return Result::Done;
        }
        let mut new_lhs = self.expand_word(&self.unsolved_equations[equation_index].lhs);
        let mut new_rhs = self.expand_word(&self.unsolved_equations[equation_index].rhs);
        if self.level_type == LevelType::PigPug {
            debug_assert!(!new_lhs.is_empty());
            debug_assert!(!new_rhs.is_empty());
        } else {
            let result = self.check_for_null(&new_lhs, &new_rhs);
            if result == Result::Changed && !self.handle_null_equations() {
                return Result::Fail;
            }
            if result != Result::Continue {
                self.unsolved_equations[equation_index] = Equation::default();
                return result;
            }
        }
        let mut lhs_left = 0;
        let mut lhs_right = new_lhs.len() - 1;
        let mut rhs_left = 0;
        let mut rhs_right = new_rhs.len() - 1;
        match self.check_for_singleton(&new_lhs, lhs_left, lhs_right, &new_rhs, rhs_left, rhs_right)
        {
            Result::Fail => return Result::Fail,
            Result::Unsafe => return Result::Done,
            Result::Continue => {}
            result => {
                self.unsolved_equations[equation_index] = Equation::default();
                return result;
            }
        }
        let mut changed = false;
        loop {
            let result = self.cancel_variables(new_lhs[lhs_left], new_rhs[rhs_left]);
            if result == Result::Fail {
                return Result::Fail;
            }
            if result == Result::Done {
                break;
            }
            lhs_left += 1;
            rhs_left += 1;
            if result == Result::Changed {
                changed = true;
                self.update_remainder(&mut new_lhs, lhs_left, lhs_right);
                self.update_remainder(&mut new_rhs, rhs_left, rhs_right);
            }
            match self
                .check_for_singleton(&new_lhs, lhs_left, lhs_right, &new_rhs, rhs_left, rhs_right)
            {
                Result::Fail => return Result::Fail,
                Result::Unsafe => {
                    self.unsolved_equations[equation_index] = Equation {
                        lhs: Self::copy_back(&new_lhs, lhs_left, lhs_right),
                        rhs: Self::copy_back(&new_rhs, rhs_left, rhs_right),
                    };
                    return if changed {
                        Result::Changed
                    } else {
                        Result::Done
                    };
                }
                Result::Continue => {}
                result => {
                    self.unsolved_equations[equation_index] = Equation::default();
                    return if changed { Result::Changed } else { result };
                }
            }
        }
        loop {
            let result = self.cancel_variables(new_lhs[lhs_right], new_rhs[rhs_right]);
            if result == Result::Fail {
                return Result::Fail;
            }
            if result == Result::Done {
                break;
            }
            lhs_right -= 1;
            rhs_right -= 1;
            if result == Result::Changed {
                changed = true;
                self.update_remainder(&mut new_lhs, lhs_left, lhs_right);
                self.update_remainder(&mut new_rhs, rhs_left, rhs_right);
            }
            match self
                .check_for_singleton(&new_lhs, lhs_left, lhs_right, &new_rhs, rhs_left, rhs_right)
            {
                Result::Fail => return Result::Fail,
                Result::Unsafe => {
                    self.unsolved_equations[equation_index] = Equation {
                        lhs: Self::copy_back(&new_lhs, lhs_left, lhs_right),
                        rhs: Self::copy_back(&new_rhs, rhs_left, rhs_right),
                    };
                    return if changed {
                        Result::Changed
                    } else {
                        Result::Done
                    };
                }
                Result::Continue => {}
                result => {
                    self.unsolved_equations[equation_index] = Equation::default();
                    return if changed { Result::Changed } else { result };
                }
            }
        }
        let lhs = Self::copy_back(&new_lhs, lhs_left, lhs_right);
        let rhs = Self::copy_back(&new_rhs, rhs_left, rhs_right);
        if self.level_type == LevelType::PigPug && !self.feasible_without_collapse(&lhs, &rhs) {
            return Result::Fail;
        }
        self.unsolved_equations[equation_index] = Equation { lhs, rhs };
        if changed {
            Result::Changed
        } else {
            Result::Done
        }
    }

    fn cancel_variables(&mut self, lhs_variable: usize, rhs_variable: usize) -> Result {
        if lhs_variable == rhs_variable {
            return Result::Continue;
        }
        let lhs_constraint = self.constraint_map[lhs_variable];
        let rhs_constraint = self.constraint_map[rhs_variable];
        if lhs_constraint.upper_bound() == 1 && rhs_constraint.upper_bound() == 1 {
            let forced = self.level_type == LevelType::PigPug
                || !(lhs_constraint.can_take_empty()
                    || self.unsafe_assignments.contains(&lhs_variable)
                    || rhs_constraint.can_take_empty()
                    || self.unsafe_assignments.contains(&rhs_variable));
            if forced {
                debug_assert_eq!(self.partial_solution[lhs_variable], vec![lhs_variable]);
                self.partial_solution[lhs_variable][0] = rhs_variable;
                let result = if self.level_type == LevelType::PigPug {
                    self.check_assignment_normal_case(lhs_variable)
                } else {
                    self.check_assignment_collapse_case(lhs_variable)
                };
                return if result == Result::Fail {
                    Result::Fail
                } else {
                    Result::Changed
                };
            }
        }
        Result::Done
    }

    fn check_for_singleton(
        &mut self,
        lhs: &Word,
        lhs_left: usize,
        lhs_right: usize,
        rhs: &Word,
        rhs_left: usize,
        rhs_right: usize,
    ) -> Result {
        let mut singleton = false;
        if lhs_left == lhs_right {
            let variable = lhs[lhs_left];
            if !self.unsafe_assignments.contains(&variable) {
                return self.make_assignment(variable, rhs, rhs_left, rhs_right);
            }
            singleton = true;
        }
        if rhs_left == rhs_right {
            let variable = rhs[rhs_left];
            if !self.unsafe_assignments.contains(&variable) {
                return self.make_assignment(variable, lhs, lhs_left, lhs_right);
            }
            return Result::Unsafe;
        }
        if singleton {
            Result::Unsafe
        } else {
            Result::Continue
        }
    }

    fn make_assignment(
        &mut self,
        variable: usize,
        source: &Word,
        left: usize,
        right: usize,
    ) -> Result {
        debug_assert_eq!(self.partial_solution[variable], vec![variable]);
        if left == right && source[left] == variable {
            return Result::Done;
        }
        let value = source[left..=right].to_vec();
        if self.level_type == LevelType::PigPug {
            if value.contains(&variable) {
                return Result::Fail;
            }
            self.partial_solution[variable] = value;
            return if self.check_assignment_normal_case(variable) == Result::Fail {
                Result::Fail
            } else {
                Result::Changed
            };
        }
        let occurs = value.contains(&variable);
        self.partial_solution[variable] = value.clone();
        if occurs {
            return if self.resolve_occurs_check_failure(variable, &value) {
                Result::Changed
            } else {
                Result::Fail
            };
        }
        if self.check_assignment_collapse_case(variable) == Result::Fail {
            Result::Fail
        } else {
            Result::Changed
        }
    }

    // Collapse-free feasibility.

    fn feasible_without_collapse(&self, lhs: &Word, rhs: &Word) -> bool {
        let mut counts = vec![0i32; self.partial_solution.len()];
        for &variable in lhs {
            counts[variable] += 1;
        }
        for &variable in rhs {
            counts[variable] -= 1;
        }
        let mut lhs_min = 0i64;
        let mut lhs_max = 0i64;
        let mut rhs_min = 0i64;
        let mut rhs_max = 0i64;
        const UNBOUNDED: i64 = i64::MAX;
        for (variable, &balance) in counts.iter().enumerate() {
            if balance > 0 {
                lhs_min += i64::from(balance);
                if lhs_max != UNBOUNDED {
                    let bound = self.constraint_map[variable].upper_bound();
                    lhs_max = if bound == 0 {
                        UNBOUNDED
                    } else {
                        lhs_max + bound as i64 * i64::from(balance)
                    };
                }
            } else if balance < 0 {
                rhs_min -= i64::from(balance);
                if rhs_max != UNBOUNDED {
                    let bound = self.constraint_map[variable].upper_bound();
                    rhs_max = if bound == 0 {
                        UNBOUNDED
                    } else {
                        rhs_max - bound as i64 * i64::from(balance)
                    };
                }
            }
        }
        lhs_min <= rhs_max && rhs_min <= lhs_max
    }

    fn level_feasible_without_collapse(&self) -> bool {
        self.unsafe_assignments.is_empty()
            && self
                .unsolved_equations
                .iter()
                .all(|equation| self.feasible_without_collapse(&equation.lhs, &equation.rhs))
    }

    // Identity selection.

    fn system_linear(&self) -> bool {
        let mut pseudo_constrained = BTreeSet::new();
        for &i in &self.unsafe_assignments {
            pseudo_constrained.extend(self.partial_solution[i].iter().copied());
        }
        let mut seen = BTreeSet::new();
        for equation in &self.unsolved_equations {
            if equation.lhs.is_empty() {
                continue;
            }
            for &variable in equation.lhs.iter().chain(&equation.rhs) {
                if self.constraint_map[variable].is_unbounded()
                    && !pseudo_constrained.contains(&variable)
                    && !seen.insert(variable)
                {
                    return false;
                }
            }
        }
        true
    }

    fn compute_pinches(&self, pincher: &Word, pinched: &Word, variables: &mut BTreeSet<usize>) {
        let pincher_size = pincher.len();
        let pinched_size = pinched.len();
        if !self.constraint_map[pincher[0]].is_unbounded() {
            for &variable in &pinched[..pinched_size - 1] {
                if !self.constraint_map[variable].can_take_empty() {
                    break;
                }
                variables.insert(variable);
            }
        }
        if !self.constraint_map[pincher[pincher_size - 1]].is_unbounded() {
            for i in (1..pinched_size).rev() {
                let variable = pinched[i];
                if !self.constraint_map[variable].can_take_empty() {
                    break;
                }
                variables.insert(variable);
            }
        }
        for i in (1..pincher_size).rev() {
            if !self.constraint_map[pincher[i]].is_unbounded()
                && !self.constraint_map[pincher[i - 1]].is_unbounded()
            {
                for j in (1..pinched_size - 1).rev() {
                    variables.insert(pinched[j]);
                }
                break;
            }
        }
    }

    fn determine_pinched_variables(&self) -> BTreeSet<usize> {
        let mut variables = BTreeSet::new();
        for equation in &self.unsolved_equations {
            if !equation.lhs.is_empty() {
                self.compute_pinches(&equation.lhs, &equation.rhs, &mut variables);
                self.compute_pinches(&equation.rhs, &equation.lhs, &mut variables);
            }
        }
        for &i in &self.unsafe_assignments {
            variables.extend(self.partial_solution[i].iter().copied());
        }
        variables
    }

    fn choose_variables_to_select_from(&mut self) {
        let pinched = if self.identity_optimizations && self.system_linear() {
            Some(self.determine_pinched_variables())
        } else {
            None
        };
        for i in 0..self.partial_solution.len() {
            let binding = &self.partial_solution[i];
            if self.constraint_map[i].can_take_empty()
                && binding.len() == 1
                && binding[0] == i
                && pinched
                    .as_ref()
                    .is_none_or(|variables| variables.contains(&i))
            {
                self.identity_variables.push(i);
            }
        }
        if let Some(state) = &self.selection_dedup {
            state.borrow_mut().identity_variables = self.identity_variables.clone();
        }
    }

    fn try_selection(&mut self) -> (u8, Option<Box<WordLevel>>) {
        self.choose_variables_to_select_from();
        let nr_identity_variables = self.identity_variables.len();
        self.nr_selections = (1usize << nr_identity_variables) - 1;
        if nr_identity_variables == 0 {
            (FAILURE, None)
        } else {
            self.explore_selections()
        }
    }

    fn explore_selections(&mut self) -> (u8, Option<Box<WordLevel>>) {
        self.selection += 1;
        if self.selection > self.nr_selections {
            return (FAILURE, None);
        }
        let equation_count = self
            .unsolved_equations
            .iter()
            .filter(|equation| !equation.lhs.is_empty())
            .count();
        let mut next = Self::new(
            LevelType::Selection,
            self.partial_solution.len(),
            equation_count,
            self.identity_optimizations,
            self.selection_dedup.clone(),
        );
        next.constraint_map = self.constraint_map.clone();
        let mut identity_index = 0;
        let mut bit_mask = 1usize;
        for i in 0..self.partial_solution.len() {
            if identity_index < self.identity_variables.len()
                && i == self.identity_variables[identity_index]
            {
                let old_bit_mask = bit_mask;
                identity_index += 1;
                bit_mask <<= 1;
                if self.selection & old_bit_mask != 0 {
                    next.add_assignment(i, Word::new());
                    continue;
                }
            }
            next.add_assignment(i, self.partial_solution[i].clone());
        }
        let mut equation_index = 0;
        for equation in &self.unsolved_equations {
            if !equation.lhs.is_empty() {
                next.add_equation(equation_index, equation.lhs.clone(), equation.rhs.clone());
                equation_index += 1;
            }
        }
        (SUCCESS, Some(Box::new(next)))
    }

    fn insert_combination(&self) -> bool {
        let state = self.selection_dedup.as_ref().unwrap();
        let identity_variables = state.borrow().identity_variables.clone();
        let mut code = 0usize;
        let mut bit_mask = 1usize;
        let mut index = 0;
        for i in 0..self.partial_solution.len() {
            if index < identity_variables.len() && i == identity_variables[index] {
                if self.partial_solution[i].is_empty() {
                    code |= bit_mask;
                }
                index += 1;
                bit_mask <<= 1;
            }
        }
        state.borrow_mut().final_combinations.insert(code)
    }
}
