//! Minimal-solution enumeration for a homogeneous linear Diophantine system — Maude's `IntSystem`
//! (`src/Utility/intSystem.{hh,cc}` + `intContejeanDevie.cc`), the **Contejean–Devie** algorithm,
//! `int` version (optimized for the small multiplicities of unification).
//!
//! Given equations `E` over `n` non-negative integer variables and per-variable upper bounds, it
//! enumerates the **minimal** solutions (the Hilbert basis of the solution cone under the bounds).
//! ACU unification builds one such system per unification problem and reads the basis off in
//! discovery order — that order is load-bearing (it fixes the AC-unifier enumeration order), so this
//! is a line-faithful port of the reference search.

// Consumed by the ACU unification subproblem (S1c), landing next; unit-tested standalone meanwhile.
#![allow(dead_code)]

use std::collections::BTreeSet;

/// Maude's `UNBOUNDED` (`INT_MAX`) — a per-variable "no upper bound".
pub(crate) const UNBOUNDED: i32 = i32::MAX;

/// One search-tree node.
#[derive(Clone)]
struct State {
    /// Current assignment to each variable (length `nr_variables`).
    assignment: Vec<i32>,
    /// Residue of each equation under `assignment` (length `eqns.len()`).
    residue: Vec<i32>,
    /// Variables that can no longer be incremented.
    frozen: BTreeSet<usize>,
}

impl State {
    fn empty(nr_variables: usize, nr_eqns: usize) -> State {
        State {
            assignment: vec![0; nr_variables],
            residue: vec![0; nr_eqns],
            frozen: BTreeSet::new(),
        }
    }
}

/// A resumable minimal-solution enumerator. Build with [`insert_eqn`](Self::insert_eqn) /
/// [`set_upper_bounds`](Self::set_upper_bounds), then call
/// [`find_next_minimal_solution`](Self::find_next_minimal_solution) repeatedly.
pub(crate) struct IntSystem {
    nr_variables: usize,
    eqns: Vec<Vec<i32>>,
    upper_bounds: Vec<i32>,
    solutions: Vec<Vec<i32>>,
    states: Vec<State>,
    stack_pointer: usize,
    current: State,
    initialized: bool,
}

impl IntSystem {
    pub(crate) fn new(nr_variables: usize) -> IntSystem {
        IntSystem {
            nr_variables,
            eqns: Vec::new(),
            upper_bounds: Vec::new(),
            solutions: Vec::new(),
            states: Vec::new(),
            stack_pointer: 0,
            current: State::empty(0, 0),
            initialized: false,
        }
    }

    /// Add an equation (coefficients over the variables; zero-padded to `nr_variables`).
    pub(crate) fn insert_eqn(&mut self, eqn: &[i32]) {
        let mut e = vec![0; self.nr_variables];
        e[..eqn.len()].copy_from_slice(eqn);
        self.eqns.push(e);
    }

    /// Set the per-variable upper bounds (pass [`UNBOUNDED`] for none). If never called, all
    /// variables are unbounded.
    pub(crate) fn set_upper_bounds(&mut self, bounds: &[i32]) {
        self.upper_bounds = bounds.to_vec();
    }

    fn initialize_upper_bounds(&mut self) {
        if self.upper_bounds.is_empty() {
            self.upper_bounds = vec![UNBOUNDED; self.nr_variables];
        } else {
            debug_assert_eq!(self.upper_bounds.len(), self.nr_variables, "row size differs");
        }
    }

    /// `arg1 >= arg2` componentwise.
    fn greater_equal(arg1: &[i32], arg2: &[i32]) -> bool {
        arg1.iter().zip(arg2).all(|(&a, &b)| a >= b)
    }

    /// A vector is minimal iff it is not `>=` any solution found so far.
    fn minimal(&self, arg: &[i32]) -> bool {
        !self.solutions.iter().any(|v| Self::greater_equal(arg, v))
    }

    fn is_zero(arg: &[i32]) -> bool {
        arg.iter().all(|&i| i == 0)
    }

    /// Scalar product of `arg` (indexed by equation) with variable `var_nr`'s column.
    fn scalar_product(&self, arg: &[i32], var_nr: usize) -> i32 {
        self.eqns.iter().zip(arg).map(|(v, &a)| v[var_nr] * a).sum()
    }

    fn initialize(&mut self) {
        self.initialize_upper_bounds();
        let nr_equations = self.eqns.len();
        self.states = Vec::with_capacity(self.nr_variables);
        let mut frozen: BTreeSet<usize> = BTreeSet::new();
        for i in 0..self.nr_variables {
            let mut assignment = vec![0; self.nr_variables];
            assignment[i] = 1;
            let residue: Vec<i32> = self.eqns.iter().map(|v| v[i]).collect();
            debug_assert!(self.upper_bounds[i] > 0, "zero upper bound");
            // Invariant: a variable at its upper bound is frozen.
            if self.upper_bounds[i] == 1 {
                frozen.insert(i);
            }
            self.states.push(State { assignment, residue, frozen: frozen.clone() });
            frozen.insert(i);
        }
        self.current = State::empty(self.nr_variables, nr_equations);
        self.stack_pointer = self.nr_variables;
        self.initialized = true;
    }

    /// Ensure `states[index]` is writable (the search stack grows past `nr_variables`).
    fn ensure_state(&mut self, index: usize) {
        while self.states.len() <= index {
            self.states.push(State::empty(self.nr_variables, self.eqns.len()));
        }
    }

    /// The next minimal solution, or `None` when the basis is exhausted.
    pub(crate) fn find_next_minimal_solution(&mut self) -> Option<Vec<i32>> {
        if !self.initialized {
            self.initialize();
        }
        while self.stack_pointer > 0 {
            self.stack_pointer -= 1;
            let sp = self.stack_pointer;
            if Self::is_zero(&self.states[sp].residue) {
                let solution = self.states[sp].assignment.clone();
                self.solutions.push(solution.clone());
                return Some(solution);
            }
            self.expand_state(sp);
        }
        None
    }

    /// Process the state at `sp`: run the forced-assignment checks, then expand by incrementing
    /// non-frozen variables. Ported from the `retry:`/`skip:` control flow of the reference.
    fn expand_state(&mut self, sp: usize) {
        'retry: loop {
            // Check that each equation still has a non-frozen coefficient that can move its residue
            // toward zero; detect single-variable forced assignments.
            for eq in 0..self.eqns.len() {
                let d = self.states[sp].residue[eq];
                let mut ok = d == 0;
                let mut nfnz_count = 0;
                let mut last_nfnz = usize::MAX;
                for i in 0..self.nr_variables {
                    if !self.states[sp].frozen.contains(&i) {
                        let c = self.eqns[eq][i];
                        if c != 0 {
                            nfnz_count += 1;
                            last_nfnz = i;
                            ok = ok || (d * c < 0);
                        }
                    }
                }
                if !ok {
                    return; // dead end (skip)
                }
                if nfnz_count == 1 {
                    // Equation `eq` has a single nonzero non-frozen coefficient left.
                    if d == 0 {
                        self.states[sp].frozen.insert(last_nfnz);
                        continue 'retry;
                    }
                    // Force `last_nfnz`.
                    let c = self.eqns[eq][last_nfnz];
                    if d % c == 0 {
                        let delta = -d / c;
                        debug_assert!(delta > 0, "delta = {delta}");
                        self.states[sp].assignment[last_nfnz] += delta;
                        if self.states[sp].assignment[last_nfnz] <= self.upper_bounds[last_nfnz]
                            && self.minimal(&self.states[sp].assignment.clone())
                        {
                            for e in 0..self.eqns.len() {
                                self.states[sp].residue[e] += delta * self.eqns[e][last_nfnz];
                            }
                            self.states[sp].frozen.insert(last_nfnz);
                            // Re-examine this (possibly-solution) state on the next iteration.
                            self.stack_pointer += 1;
                        }
                    }
                    return; // skip
                }
            }
            break;
        }

        // State survived: expand by incrementing each eligible non-frozen variable. Save the state
        // into `current` first (the reference swaps).
        std::mem::swap(&mut self.current, &mut self.states[sp]);
        for i in 0..self.nr_variables {
            if !self.current.frozen.contains(&i)
                && self.scalar_product(&self.current.residue, i) < 0
            {
                self.current.assignment[i] += 1;
                if self.minimal(&self.current.assignment.clone()) {
                    let new_sp = self.stack_pointer;
                    self.ensure_state(new_sp);
                    let n = &mut self.states[new_sp];
                    n.assignment.clone_from(&self.current.assignment);
                    n.residue.clear();
                    for (e, v) in self.eqns.iter().enumerate() {
                        n.residue.push(self.current.residue[e] + v[i]);
                    }
                    // Maintain the upper-bound-⇒-frozen invariant for the new state.
                    let mut frozen = self.current.frozen.clone();
                    if self.current.assignment[i] == self.upper_bounds[i] {
                        frozen.insert(i);
                    }
                    n.frozen = frozen;
                    self.stack_pointer += 1;
                }
                self.current.assignment[i] -= 1;
                // Freeze `i` in the remaining descendants whether minimal or not.
                self.current.frozen.insert(i);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn all_solutions(sys: &mut IntSystem) -> Vec<Vec<i32>> {
        let mut out = Vec::new();
        while let Some(s) = sys.find_next_minimal_solution() {
            out.push(s);
        }
        out
    }

    /// `x + y - z = 0` (i.e. `x + y = z`) over 3 variables, bound each by 3. Minimal solutions:
    /// `(1,0,1)` and `(0,1,1)` — every solution is a non-negative combination of these.
    #[test]
    fn sum_equation_basis() {
        let mut sys = IntSystem::new(3);
        sys.insert_eqn(&[1, 1, -1]);
        sys.set_upper_bounds(&[3, 3, 3]);
        let sols = all_solutions(&mut sys);
        let set: BTreeSet<Vec<i32>> = sols.iter().cloned().collect();
        assert_eq!(
            set,
            [vec![1, 0, 1], vec![0, 1, 1]].into_iter().collect::<BTreeSet<_>>(),
            "Hilbert basis of x + y = z"
        );
        // Minimality: no solution dominates another.
        for a in &sols {
            for b in &sols {
                if a != b {
                    assert!(!IntSystem::greater_equal(a, b), "{a:?} dominates {b:?}");
                }
            }
        }
    }

    /// `2x - y = 0` (y = 2x), bound x by 2, y by 4. Minimal solution: `(1, 2)`.
    #[test]
    fn scaled_equation() {
        let mut sys = IntSystem::new(2);
        sys.insert_eqn(&[2, -1]);
        sys.set_upper_bounds(&[2, 4]);
        let sols = all_solutions(&mut sys);
        assert_eq!(sols, vec![vec![1, 2]]);
    }

    /// The AC unification system for `X + X + Y =? A + B + C` — variables X,Y (lhs, coeff on the
    /// count of each rhs subject) against subjects A,B,C (each count 1). Here we model the classic
    /// `f(X,Y) =? f(a,b)` shape: `X + Y = a + b` with a,b distinct columns is a matching system, but
    /// for the minimal-basis check we use the homogeneous form and confirm the basis is non-empty and
    /// minimal. (Full ACU-order validation is the fixture's job.)
    #[test]
    fn two_var_two_subject() {
        // X - a - b = 0 won't do (that's matching); use x + y = w with bounds to get a small basis.
        let mut sys = IntSystem::new(3);
        sys.insert_eqn(&[1, 1, -2]);
        sys.set_upper_bounds(&[2, 2, 1]);
        let sols = all_solutions(&mut sys);
        // x + y = 2w, w<=1: w=1 needs x+y=2 → (2,0,1),(1,1,1),(0,2,1); w=0 → (0,0,0) excluded (not
        // reached from the unit-seed search). Minimal ones (no domination): (2,0,1),(1,1,1),(0,2,1)
        // are mutually non-dominating.
        assert!(!sols.is_empty());
        for a in &sols {
            for b in &sols {
                if a != b {
                    assert!(!IntSystem::greater_equal(a, b));
                }
            }
        }
    }
}
