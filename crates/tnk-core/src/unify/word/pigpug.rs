//! PigPug search for one constrained word equation. Each step compares the leading variables and
//! branches among peeling one side from the other or equating them.
//!
//! Move order, stack updates, backtracking, cycle detection, and extraction order determine the
//! observable solution order.

use std::collections::{BTreeMap, BTreeSet};

use super::constraint::VariableConstraint;
use super::{FAILURE, INCOMPLETE, SUCCESS, Word};

pub(super) type ConstraintMap = Vec<VariableConstraint>;
pub(super) type Subst = Vec<Word>;

pub(super) const NONLINEAR: u8 = 0;
pub(super) const STRICT_LEFT_LINEAR: u8 = 1;
pub(super) const STRICT_RIGHT_LINEAR: u8 = 2;
pub(super) const LINEAR: u8 = STRICT_LEFT_LINEAR | STRICT_RIGHT_LINEAR;

const RHS_PEEL: u8 = 1;
const LHS_PEEL: u8 = 2;
const EQUATE: u8 = RHS_PEEL | LHS_PEEL;
const FINAL: u8 = 4;
const EQUATE_FINAL: u8 = EQUATE | FINAL;
const LHS_TAKES_ALL: u8 = FINAL | RHS_PEEL;
const RHS_TAKES_ALL: u8 = FINAL | LHS_PEEL;
const BASIC_MOVES: u8 = RHS_PEEL | LHS_PEEL;
const ALL_MOVES: u8 = BASIC_MOVES | FINAL;
const RHS_ASSIGN: u8 = 8;
const PUSH_LHS: u8 = 16;
const PUSH_RHS: u8 = 32;
const PUSH_CONSTRAINT_MAP: u8 = 64;
const CANCEL: u8 = 128;

const NOT_ENTERED: i8 = -1;
const FAIL: i8 = 0;
const LHS_DONE: i8 = 1;
const RHS_DONE: i8 = 2;
const OK: i8 = 4;

#[derive(Clone)]
struct Unificand {
    index: usize,
    word: Word,
}

#[derive(Clone, Copy, Default)]
struct StateInfo {
    on_stack: bool,
    on_cycle: bool,
    on_live_path: bool,
}

pub(super) struct PigPug {
    last_original_variable: usize,
    fresh_variable_start: usize,
    linearity: u8,
    equate_optimization: bool,
    cycle_detection: bool,
    depth_bound: Option<usize>,
    incompleteness_flag: u8,
    lhs_stack: Vec<Unificand>,
    rhs_stack: Vec<Unificand>,
    constraint_stack: Vec<ConstraintMap>,
    path: Vec<u8>,
    word_map: BTreeMap<Vec<i64>, usize>,
    state_info: Vec<StateInfo>,
    traversal_stack: Vec<usize>,
}

impl PigPug {
    pub(super) fn new(
        lhs: &Word,
        rhs: &Word,
        constraint_map: &ConstraintMap,
        last_original_variable: usize,
        fresh_variable_start: usize,
        linearity: u8,
        equate_optimization: bool,
    ) -> Self {
        debug_assert!(lhs.len() >= 2);
        debug_assert!(rhs.len() >= 2);
        debug_assert_ne!(linearity, STRICT_RIGHT_LINEAR);
        let cycle_detection = linearity & STRICT_LEFT_LINEAR == 0
            && Self::variable_occurrences_bounded_by_2(
                lhs,
                rhs,
                last_original_variable,
                constraint_map,
            );
        let depth_bound = if linearity & STRICT_LEFT_LINEAR == 0 && !cycle_detection {
            Some(lhs.len() + rhs.len())
        } else {
            None
        };
        Self {
            last_original_variable,
            fresh_variable_start,
            linearity,
            equate_optimization,
            cycle_detection,
            depth_bound,
            incompleteness_flag: 0,
            lhs_stack: vec![Unificand {
                index: 0,
                word: lhs.clone(),
            }],
            rhs_stack: vec![Unificand {
                index: 0,
                word: rhs.clone(),
            }],
            constraint_stack: vec![constraint_map.clone()],
            path: Vec::new(),
            word_map: BTreeMap::new(),
            state_info: Vec::new(),
            traversal_stack: Vec::new(),
        }
    }

    fn variable_occurrences_bounded_by_2(
        lhs: &Word,
        rhs: &Word,
        max_variable: usize,
        constraints: &ConstraintMap,
    ) -> bool {
        let mut counts = vec![0u8; max_variable + 1];
        for &variable in lhs.iter().chain(rhs) {
            if constraints[variable].is_unbounded() {
                counts[variable] += 1;
                if counts[variable] > 2 {
                    return false;
                }
            }
        }
        true
    }

    /// Return `(outcome flags, next fresh variable)`. The second component is `None` on exhaustion.
    pub(super) fn get_next_unifier(
        &mut self,
        unifier: &mut Subst,
        constraint_map: &mut ConstraintMap,
    ) -> (u8, Option<usize>) {
        loop {
            let initial_result = if self.path.is_empty() { OK } else { FAIL };
            let result = if self.cycle_detection {
                self.run_with_cycle_detection(initial_result)
            } else {
                self.run(initial_result)
            };
            if result == FAIL {
                return (FAILURE | self.incompleteness_flag, None);
            }
            if let Some(next) = self.extract_unifier(unifier, constraint_map) {
                return (SUCCESS | self.incompleteness_flag, Some(next));
            }
        }
    }

    fn run(&mut self, mut result: i8) -> i8 {
        loop {
            if result == OK {
                result = self.first_move();
            } else if result == FAIL || self.completed(result) == FAIL {
                if self.path.is_empty() {
                    break;
                }
                result = self.next_move();
            } else {
                return result;
            }
        }
        FAIL
    }

    fn first_move(&mut self) -> i8 {
        loop {
            let result = self.cancel();
            if result == FAIL {
                break;
            }
            if result != OK {
                return result;
            }
        }
        if !self.feasible() {
            return FAIL;
        }
        if self
            .depth_bound
            .is_some_and(|bound| self.path.len() >= bound)
        {
            self.incompleteness_flag = INCOMPLETE;
            return FAIL;
        }
        let result = self.rhs_peel();
        if result != FAIL {
            return result;
        }
        let result = self.lhs_peel();
        if result != FAIL {
            return result;
        }
        self.equate()
    }

    fn next_move(&mut self) -> i8 {
        let previous_move = self.undo_move() & BASIC_MOVES;
        if previous_move == EQUATE {
            return FAIL;
        }
        if previous_move == RHS_PEEL {
            let result = self.lhs_peel();
            if result != FAIL {
                return result;
            }
        }
        if self.equate_optimization && self.double_peel_possible() {
            return FAIL;
        }
        self.equate()
    }

    fn double_peel_possible(&self) -> bool {
        let lhs = self.lhs_stack.last().unwrap();
        let rhs = self.rhs_stack.last().unwrap();
        let lhs_var = lhs.word[lhs.index];
        let lhs_next = lhs.word[lhs.index + 1];
        let rhs_var = rhs.word[rhs.index];
        let rhs_next = rhs.word[rhs.index + 1];
        let constraints = self.constraint_stack.last().unwrap();
        (constraints[lhs_var].is_unbounded() && constraints[rhs_next].is_unbounded())
            || (constraints[rhs_var].is_unbounded() && constraints[lhs_next].is_unbounded())
    }

    fn cancel(&mut self) -> i8 {
        let lhs = self.lhs_stack.last().unwrap();
        let rhs = self.rhs_stack.last().unwrap();
        if lhs.word[lhs.index] != rhs.word[rhs.index] {
            return FAIL;
        }
        self.lhs_stack.last_mut().unwrap().index += 1;
        self.rhs_stack.last_mut().unwrap().index += 1;
        self.path.push(EQUATE | CANCEL);
        let lhs = self.lhs_stack.last().unwrap();
        if lhs.index + 1 == lhs.word.len() {
            return LHS_DONE;
        }
        let rhs = self.rhs_stack.last().unwrap();
        if rhs.index + 1 == rhs.word.len() {
            return RHS_DONE;
        }
        OK
    }

    fn rhs_peel(&mut self) -> i8 {
        let lhs = self.lhs_stack.last().unwrap();
        let lhs_var = lhs.word[lhs.index];
        let lhs_upper_bound = self.constraint_stack.last().unwrap()[lhs_var].upper_bound();
        if lhs_upper_bound == 1 {
            return FAIL;
        }
        let rhs = self.rhs_stack.last().unwrap();
        let rhs_var = rhs.word[rhs.index];
        self.rhs_stack.last_mut().unwrap().index += 1;
        let mut movement = RHS_PEEL;
        if !(lhs_upper_bound == 0 && self.linearity & STRICT_LEFT_LINEAR != 0) {
            if Self::check_unificand_2(&mut self.rhs_stack, lhs_var, rhs_var, 0) {
                movement |= PUSH_RHS;
            }
            if Self::check_unificand_2(&mut self.lhs_stack, lhs_var, rhs_var, 1) {
                movement |= PUSH_LHS;
            }
        } else {
            debug_assert!(!Self::check_unificand_2(
                &mut self.rhs_stack,
                lhs_var,
                rhs_var,
                0
            ));
            debug_assert!(!Self::check_unificand_2(
                &mut self.lhs_stack,
                lhs_var,
                rhs_var,
                1
            ));
        }
        if self.check_constraint_map_variable(lhs_var, rhs_var) {
            movement |= PUSH_CONSTRAINT_MAP;
        }
        self.path.push(movement);
        let rhs = self.rhs_stack.last().unwrap();
        if rhs.index + 1 == rhs.word.len() {
            RHS_DONE
        } else {
            OK
        }
    }

    fn lhs_peel(&mut self) -> i8 {
        let rhs = self.rhs_stack.last().unwrap();
        let rhs_var = rhs.word[rhs.index];
        let rhs_upper_bound = self.constraint_stack.last().unwrap()[rhs_var].upper_bound();
        if rhs_upper_bound == 1 {
            return FAIL;
        }
        let lhs = self.lhs_stack.last().unwrap();
        let lhs_var = lhs.word[lhs.index];
        self.lhs_stack.last_mut().unwrap().index += 1;
        let mut movement = LHS_PEEL;
        if rhs_upper_bound == 0 && self.linearity & STRICT_RIGHT_LINEAR != 0 {
            debug_assert!(!Self::check_unificand_2(
                &mut self.lhs_stack,
                rhs_var,
                lhs_var,
                0
            ));
            debug_assert!(!Self::check_unificand_2(
                &mut self.rhs_stack,
                rhs_var,
                lhs_var,
                1
            ));
        } else {
            if Self::check_unificand_2(&mut self.rhs_stack, rhs_var, lhs_var, 1) {
                movement |= PUSH_RHS;
            }
            if rhs_upper_bound == 0 && self.linearity & STRICT_LEFT_LINEAR != 0 {
                debug_assert!(!Self::check_unificand_2(
                    &mut self.lhs_stack,
                    rhs_var,
                    lhs_var,
                    0
                ));
            } else if Self::check_unificand_2(&mut self.lhs_stack, rhs_var, lhs_var, 0) {
                movement |= PUSH_LHS;
            }
        }
        if self.check_constraint_map_variable(rhs_var, lhs_var) {
            movement |= PUSH_CONSTRAINT_MAP;
        }
        self.path.push(movement);
        let lhs = self.lhs_stack.last().unwrap();
        if lhs.index + 1 == lhs.word.len() {
            LHS_DONE
        } else {
            OK
        }
    }

    fn equate(&mut self) -> i8 {
        let lhs = self.lhs_stack.last().unwrap();
        let rhs = self.rhs_stack.last().unwrap();
        let lhs_var = lhs.word[lhs.index];
        let rhs_var = rhs.word[rhs.index];
        let constraints = self.constraint_stack.last().unwrap();
        let lhs_constraint = constraints[lhs_var];
        let rhs_constraint = constraints[rhs_var];
        let mut meet = lhs_constraint;
        if !meet.intersect(rhs_constraint) {
            return FAIL;
        }
        self.lhs_stack.last_mut().unwrap().index += 1;
        self.rhs_stack.last_mut().unwrap().index += 1;
        let mut movement = EQUATE;
        if rhs_constraint == meet {
            if self.linearity & STRICT_LEFT_LINEAR != 0 && lhs_constraint.is_unbounded() {
                debug_assert!(!Self::check_unificand(
                    &mut self.lhs_stack,
                    lhs_var,
                    rhs_var
                ));
                debug_assert!(!Self::check_unificand(
                    &mut self.rhs_stack,
                    lhs_var,
                    rhs_var
                ));
            } else {
                if Self::check_unificand(&mut self.lhs_stack, lhs_var, rhs_var) {
                    movement |= PUSH_LHS;
                }
                if Self::check_unificand(&mut self.rhs_stack, lhs_var, rhs_var) {
                    movement |= PUSH_RHS;
                }
            }
        } else if lhs_constraint == meet {
            movement |= RHS_ASSIGN;
            if Self::check_unificand(&mut self.rhs_stack, rhs_var, lhs_var) {
                movement |= PUSH_RHS;
            }
            if self.linearity & STRICT_LEFT_LINEAR != 0 && rhs_constraint.is_unbounded() {
                debug_assert!(!Self::check_unificand(
                    &mut self.lhs_stack,
                    rhs_var,
                    lhs_var
                ));
            } else if Self::check_unificand(&mut self.lhs_stack, rhs_var, lhs_var) {
                movement |= PUSH_LHS;
            }
        } else {
            self.constraint_stack
                .push(self.constraint_stack.last().unwrap().clone());
            movement |= PUSH_CONSTRAINT_MAP;
            if rhs_constraint.is_unbounded() {
                movement |= RHS_ASSIGN;
                if Self::check_unificand(&mut self.rhs_stack, rhs_var, lhs_var) {
                    movement |= PUSH_RHS;
                }
                if self.linearity & STRICT_LEFT_LINEAR != 0 {
                    debug_assert!(!Self::check_unificand(
                        &mut self.lhs_stack,
                        rhs_var,
                        lhs_var
                    ));
                } else if Self::check_unificand(&mut self.lhs_stack, rhs_var, lhs_var) {
                    movement |= PUSH_LHS;
                }
                self.constraint_stack.last_mut().unwrap()[lhs_var] = meet;
            } else {
                if self.linearity & STRICT_LEFT_LINEAR != 0 && lhs_constraint.is_unbounded() {
                    debug_assert!(!Self::check_unificand(
                        &mut self.lhs_stack,
                        lhs_var,
                        rhs_var
                    ));
                    debug_assert!(!Self::check_unificand(
                        &mut self.rhs_stack,
                        lhs_var,
                        rhs_var
                    ));
                } else {
                    if Self::check_unificand(&mut self.lhs_stack, lhs_var, rhs_var) {
                        movement |= PUSH_LHS;
                    }
                    if Self::check_unificand(&mut self.rhs_stack, lhs_var, rhs_var) {
                        movement |= PUSH_RHS;
                    }
                }
                self.constraint_stack.last_mut().unwrap()[rhs_var] = meet;
            }
        }
        self.path.push(movement);
        let lhs = self.lhs_stack.last().unwrap();
        if lhs.index + 1 == lhs.word.len() {
            return LHS_DONE;
        }
        let rhs = self.rhs_stack.last().unwrap();
        if rhs.index + 1 == rhs.word.len() {
            RHS_DONE
        } else {
            OK
        }
    }

    fn check_unificand(stack: &mut Vec<Unificand>, old_var: usize, new_var: usize) -> bool {
        let current = stack.last().unwrap();
        if !current.word[current.index..].contains(&old_var) {
            return false;
        }
        let word = current.word[current.index..]
            .iter()
            .map(|&variable| {
                if variable == old_var {
                    new_var
                } else {
                    variable
                }
            })
            .collect();
        stack.push(Unificand { index: 0, word });
        true
    }

    fn check_unificand_2(
        stack: &mut Vec<Unificand>,
        old_var: usize,
        new_var: usize,
        offset: usize,
    ) -> bool {
        let current = stack.last().unwrap();
        let Some(relative) = current.word[current.index + offset..]
            .iter()
            .position(|&variable| variable == old_var)
        else {
            return false;
        };
        let found = current.index + offset + relative;
        let mut word = Vec::with_capacity(current.word.len() - current.index + 2);
        word.extend_from_slice(&current.word[current.index..found]);
        word.push(new_var);
        word.push(old_var);
        for &variable in &current.word[found + 1..] {
            if variable == old_var {
                word.push(new_var);
            }
            word.push(variable);
        }
        stack.push(Unificand { index: 0, word });
        true
    }

    fn check_constraint_map_variable(&mut self, known_big: usize, other: usize) -> bool {
        let constraints = self.constraint_stack.last().unwrap();
        debug_assert!(!constraints[known_big].has_theory_constraint());
        let upper_bound = constraints[known_big].upper_bound();
        if upper_bound == 0 {
            return false;
        }
        debug_assert_ne!(upper_bound, 1);
        let mut next = constraints.clone();
        let new_upper_bound = upper_bound - 1;
        next[known_big].set_upper_bound(new_upper_bound);
        let other_upper_bound = constraints[other].upper_bound();
        if other_upper_bound == 0 || other_upper_bound > new_upper_bound {
            next[other].set_upper_bound(new_upper_bound);
        }
        self.constraint_stack.push(next);
        true
    }

    fn check_constraint_map_unificand(&mut self, known_big: usize, other: &Unificand) -> bool {
        let constraints = self.constraint_stack.last().unwrap();
        debug_assert!(!constraints[known_big].has_theory_constraint());
        let upper_bound = constraints[known_big].upper_bound();
        if upper_bound == 0 {
            return false;
        }
        debug_assert_ne!(upper_bound, 1);
        let new_upper_bound = upper_bound - 1;
        let needs_update = other.word[other.index..].iter().any(|&variable| {
            let bound = constraints[variable].upper_bound();
            bound == 0 || bound > new_upper_bound
        });
        if !needs_update {
            return false;
        }
        let mut next = constraints.clone();
        for &variable in &other.word[other.index..] {
            let bound = constraints[variable].upper_bound();
            if bound == 0 || bound > new_upper_bound {
                next[variable].set_upper_bound(new_upper_bound);
            }
        }
        self.constraint_stack.push(next);
        true
    }

    fn feasible(&self) -> bool {
        let mut counts = vec![0i32; self.last_original_variable + 1];
        let lhs = self.lhs_stack.last().unwrap();
        for &variable in &lhs.word[lhs.index..] {
            counts[variable] += 1;
        }
        let rhs = self.rhs_stack.last().unwrap();
        for &variable in &rhs.word[rhs.index..] {
            counts[variable] -= 1;
        }
        let constraints = self.constraint_stack.last().unwrap();
        let mut lhs_min = 0i64;
        let mut lhs_max = 0i64;
        let mut rhs_min = 0i64;
        let mut rhs_max = 0i64;
        const UNBOUNDED: i64 = i64::MAX;
        for (variable, &balance) in counts.iter().enumerate() {
            if balance > 0 {
                lhs_min += i64::from(balance);
                if lhs_max != UNBOUNDED {
                    let bound = constraints[variable].upper_bound();
                    lhs_max = if bound == 0 {
                        UNBOUNDED
                    } else {
                        lhs_max + bound as i64 * i64::from(balance)
                    };
                }
            } else if balance < 0 {
                rhs_min -= i64::from(balance);
                if rhs_max != UNBOUNDED {
                    let bound = constraints[variable].upper_bound();
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

    fn completed(&mut self, status: i8) -> i8 {
        let lhs = self.lhs_stack.last().unwrap().clone();
        let rhs = self.rhs_stack.last().unwrap().clone();
        if status == LHS_DONE {
            let lhs_var = lhs.word[lhs.index];
            if rhs.index + 1 == rhs.word.len() {
                let rhs_var = rhs.word[rhs.index];
                if lhs_var == rhs_var {
                    return status;
                }
                let constraints = self.constraint_stack.last().unwrap();
                let lhs_constraint = constraints[lhs_var];
                let rhs_constraint = constraints[rhs_var];
                let mut meet = lhs_constraint;
                if meet.intersect(rhs_constraint) {
                    if rhs_constraint == meet {
                        self.path.push(EQUATE | FINAL);
                    } else if lhs_constraint == meet {
                        self.path.push(EQUATE | FINAL | RHS_ASSIGN);
                    } else {
                        let mut next = constraints.clone();
                        next[rhs_var] = meet;
                        self.constraint_stack.push(next);
                        self.path.push(EQUATE | FINAL | PUSH_CONSTRAINT_MAP);
                    }
                    return status;
                }
            } else if self.feasible() {
                let mut movement = LHS_TAKES_ALL;
                if self.check_constraint_map_unificand(lhs_var, &rhs) {
                    movement |= PUSH_CONSTRAINT_MAP;
                }
                self.path.push(movement);
                return status;
            }
        } else {
            debug_assert_eq!(status, RHS_DONE);
            if self.feasible() {
                let rhs_var = rhs.word[rhs.index];
                let mut movement = RHS_TAKES_ALL;
                if self.check_constraint_map_unificand(rhs_var, &lhs) {
                    movement |= PUSH_CONSTRAINT_MAP;
                }
                self.path.push(movement);
                return status;
            }
        }
        FAIL
    }

    fn undo_move(&mut self) -> u8 {
        let mut movement = self.path.pop().unwrap();
        if movement & FINAL != 0 {
            if movement & PUSH_CONSTRAINT_MAP != 0 {
                self.constraint_stack.pop();
            }
            movement = self.path.pop().unwrap();
        }
        if movement & PUSH_LHS != 0 {
            self.lhs_stack.pop();
        }
        if movement & LHS_PEEL != 0 {
            self.lhs_stack.last_mut().unwrap().index -= 1;
        }
        if movement & PUSH_RHS != 0 {
            self.rhs_stack.pop();
        }
        if movement & RHS_PEEL != 0 {
            self.rhs_stack.last_mut().unwrap().index -= 1;
        }
        if movement & PUSH_CONSTRAINT_MAP != 0 {
            self.constraint_stack.pop();
        }
        movement
    }

    fn make_state_key(&self) -> Vec<i64> {
        let constraints = self.constraint_stack.last().unwrap();
        let lhs = self.lhs_stack.last().unwrap();
        let rhs = self.rhs_stack.last().unwrap();
        let mut key = Vec::with_capacity(2 * (lhs.word.len() + rhs.word.len()) + 1);
        for &variable in &lhs.word[lhs.index..] {
            key.push(variable as i64);
            key.push(constraints[variable].upper_bound() as i64);
        }
        key.push(-1);
        for &variable in &rhs.word[rhs.index..] {
            key.push(variable as i64);
            key.push(constraints[variable].upper_bound() as i64);
        }
        key
    }

    fn first_move_with_cycle_detection(&mut self) -> i8 {
        loop {
            let result = self.cancel();
            if result == FAIL {
                break;
            }
            if result != OK {
                return result;
            }
        }
        if !self.feasible() {
            return NOT_ENTERED;
        }
        let key = self.make_state_key();
        if self.on_cycle(key) {
            return NOT_ENTERED;
        }
        let result = self.rhs_peel();
        if result != FAIL {
            return result;
        }
        let result = self.lhs_peel();
        if result != FAIL {
            return result;
        }
        self.equate()
    }

    fn next_move_with_cycle_detection(&mut self) -> i8 {
        let previous = self.undo_move();
        let basic = previous & BASIC_MOVES;
        if basic == EQUATE {
            return if previous & CANCEL != 0 {
                NOT_ENTERED
            } else {
                FAIL
            };
        }
        if basic == RHS_PEEL {
            let result = self.lhs_peel();
            if result != FAIL {
                return result;
            }
        }
        self.equate()
    }

    fn run_with_cycle_detection(&mut self, mut result: i8) -> i8 {
        loop {
            if result == OK {
                result = self.first_move_with_cycle_detection();
                if result == FAIL {
                    self.depart();
                }
                continue;
            }
            if (result == LHS_DONE || result == RHS_DONE) && self.completed(result) != FAIL {
                self.confirmed_live();
                return result;
            }
            if self.path.is_empty() {
                break;
            }
            result = self.next_move_with_cycle_detection();
            if result == FAIL {
                self.depart();
            }
        }
        FAIL
    }

    /// True means the state closes a cycle and must not be entered.
    fn on_cycle(&mut self, key: Vec<i64>) -> bool {
        if let Some(&index) = self.word_map.get(&key) {
            if self.state_info[index].on_stack {
                for &state_number in self.traversal_stack.iter().rev() {
                    let state = &mut self.state_info[state_number];
                    state.on_cycle = true;
                    if state.on_live_path {
                        self.incompleteness_flag = INCOMPLETE;
                    }
                    if state_number == index {
                        break;
                    }
                }
                return true;
            }
            self.state_info[index].on_stack = true;
            self.traversal_stack.push(index);
            false
        } else {
            let state_number = self.state_info.len();
            self.word_map.insert(key, state_number);
            self.state_info.push(StateInfo {
                on_stack: true,
                ..StateInfo::default()
            });
            self.traversal_stack.push(state_number);
            false
        }
    }

    fn depart(&mut self) {
        let index = self.traversal_stack.pop().unwrap();
        self.state_info[index].on_stack = false;
    }

    fn confirmed_live(&mut self) {
        for &state_number in &self.traversal_stack {
            let state = &mut self.state_info[state_number];
            state.on_live_path = true;
            if state.on_cycle {
                self.incompleteness_flag = INCOMPLETE;
            }
        }
    }

    fn extract_unifier(
        &self,
        unifier: &mut Subst,
        constraint_map: &mut ConstraintMap,
    ) -> Option<usize> {
        let mut lhs_stack_index = 0;
        let mut rhs_stack_index = 0;
        let mut lhs_index = 0;
        let mut rhs_index = 0;
        *unifier = (0..=self.last_original_variable).map(|i| vec![i]).collect();
        for &movement in &self.path {
            let lhs = &self.lhs_stack[lhs_stack_index];
            let rhs = &self.rhs_stack[rhs_stack_index];
            let lhs_var = lhs.word[lhs_index];
            let rhs_var = rhs.word[rhs_index];
            match movement & ALL_MOVES {
                RHS_PEEL => {
                    if !self.compose_2(unifier, lhs_var, rhs_var) {
                        return None;
                    }
                    rhs_index += 1;
                }
                LHS_PEEL => {
                    if !self.compose_2(unifier, rhs_var, lhs_var) {
                        return None;
                    }
                    lhs_index += 1;
                }
                EQUATE | EQUATE_FINAL => {
                    if movement & RHS_ASSIGN != 0 {
                        self.compose(unifier, rhs_var, lhs_var);
                    } else if lhs_var != rhs_var {
                        self.compose(unifier, lhs_var, rhs_var);
                    }
                    lhs_index += 1;
                    rhs_index += 1;
                }
                LHS_TAKES_ALL => {
                    if !self.compose_final(unifier, lhs_var, &rhs.word, rhs_index) {
                        return None;
                    }
                }
                RHS_TAKES_ALL => {
                    if !self.compose_final(unifier, rhs_var, &lhs.word, lhs_index) {
                        return None;
                    }
                }
                _ => unreachable!("invalid internal PIG-PUG move"),
            }
            if movement & PUSH_LHS != 0 {
                lhs_stack_index += 1;
                lhs_index = 0;
            }
            if movement & PUSH_RHS != 0 {
                rhs_stack_index += 1;
                rhs_index = 0;
            }
        }
        let occurs_in_range: BTreeSet<usize> = unifier
            .iter()
            .flat_map(|word| word.iter().copied())
            .collect();
        let mut next_variable = self.fresh_variable_start;
        let mut renaming = vec![usize::MAX; self.last_original_variable + 1];
        *constraint_map = self.constraint_stack.first().unwrap().clone();
        let final_constraints = self.constraint_stack.last().unwrap();
        for i in 0..=self.last_original_variable {
            let word = &unifier[i];
            if word.len() == 1 && word[0] == i {
                renaming[i] = i;
                constraint_map[i] = final_constraints[i];
            } else if occurs_in_range.contains(&i) {
                renaming[i] = next_variable;
                next_variable += 1;
                constraint_map.push(final_constraints[i]);
            }
        }
        for word in unifier {
            for variable in word {
                *variable = renaming[*variable];
            }
        }
        Some(next_variable)
    }

    fn compose(&self, subst: &mut Subst, old_var: usize, replacement: usize) {
        for word in subst {
            for variable in word {
                if *variable == old_var {
                    *variable = replacement;
                }
            }
        }
    }

    fn compose_2(&self, subst: &mut Subst, old_var: usize, replacement: usize) -> bool {
        let constraints = self.constraint_stack.first().unwrap();
        for (i, word) in subst.iter_mut().enumerate() {
            let Some(first) = word.iter().position(|&variable| variable == old_var) else {
                continue;
            };
            let mut next = Vec::with_capacity(word.len() + 1);
            next.extend_from_slice(&word[..first]);
            next.push(replacement);
            next.push(old_var);
            for &variable in &word[first + 1..] {
                if variable == old_var {
                    next.push(replacement);
                }
                next.push(variable);
            }
            let bound = constraints[i].upper_bound();
            if bound != 0 && next.len() > bound {
                return false;
            }
            *word = next;
        }
        true
    }

    fn compose_final(
        &self,
        subst: &mut Subst,
        old_var: usize,
        replacement: &Word,
        index: usize,
    ) -> bool {
        let constraints = self.constraint_stack.first().unwrap();
        for (i, word) in subst.iter_mut().enumerate() {
            let Some(first) = word.iter().position(|&variable| variable == old_var) else {
                continue;
            };
            let mut next = Vec::new();
            next.extend_from_slice(&word[..first]);
            for &variable in &word[first..] {
                if variable == old_var {
                    next.extend_from_slice(&replacement[index..]);
                } else {
                    next.push(variable);
                }
            }
            let bound = constraints[i].upper_bound();
            if bound != 0 && next.len() > bound {
                return false;
            }
            *word = next;
        }
        true
    }
}
