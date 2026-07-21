//! Diophantine system solver for AC/ACU matching (Eker 2002, JAR 28(1)).
//!
//! A **close line-for-line port** of Maude's `Utility/diophantineSystem.{hh,cc}`. Given an
//! `n`-component vector of positive integers `R` (row coefficients = variable multiplicities) and an
//! `m`-component vector of positive integers `C` (column values = residual subject multiplicities),
//! a solution is an `n×m` natural-number matrix `M` with `R * M = C` — `M[i,j]` is the number of
//! copies of subject `j` assigned to variable `i`. Each row's sum is constrained to `[minSize,
//! maxSize]` (a variable's binding size; the extension row is `[0, extBound]`).
//!
//! The **enumeration order is load-bearing**: it fixes the AC solution order, which fixes downstream
//! `reduce`/`search`/`xmatch` rewrite counts. The algorithm sorts `R` descending by coefficient
//! (ties broken by ascending `maxSize`), solves one row at a time backtracking, and within a row
//! tries selections **smallest first** (`multisetSelect` / `multisetComplex`), the last row taking
//! the remainder. A system is **simple** iff some `R_i == 1` with `maxSize >=` the largest column
//! value (⇒ any natural number is a linear combination of any final segment of the sorted `R`, ruling
//! out one cause of dead-ends); otherwise **complex**, keeping a per-row **solubility vector** to
//! prune infeasible partial solutions early.
//!
//! This is a pure integer solver — no engine dependency — unit-tested against hand-derived sequences
//! and the C++ reference (see the tests below).

/// Maude's `UNBOUNDED` sentinel (`macros.hh`: `INT_MAX`) — a stand-in for +infinity on a row's
/// `maxSize`; [`precompute`](DiophantineSystem::precompute) substitutes the column sum for it.
pub(crate) const UNBOUNDED: i32 = i32::MAX;

/// Maude's `DiophantineSystem::INSOLUBLE` — sentinel in a solubility vector for "no natural-number
/// assignment exists".
const INSOLUBLE: i32 = -1;

/// Per-column selection state within a row: the solution value is `base + extra` (`base` is 0 for
/// simple systems; the solubility-forced minimum for complex ones), with `extra <= max_extra`.
#[derive(Clone, Copy, Default)]
struct Select {
    base: i32,
    extra: i32,
    max_extra: i32,
}

/// A solubility-vector entry (complex systems): the min/max `K` such that `value - K*coeff` can be
/// expressed as a natural-number linear combination over the remaining (lower-coefficient) rows.
#[derive(Clone, Copy)]
struct Soluble {
    min: i32,
    max: i32,
}

/// One row of the system: a variable's coefficient and size bounds, plus match-time selection state.
struct Row {
    name: usize, // original insertion index (the key `solution(row, _)` maps through row_permute)
    coeff: i32,  // R component (variable multiplicity)
    min_size: i32, // minimum acceptable row sum
    min_product: i32, // coeff * min_size
    min_leave: i32, // minimum sum that must be left for remaining (later) rows
    max_size: i32, // maximum acceptable row sum
    max_product: i32, // coeff * max_size
    max_leave: i32, // maximum sum that may be left for remaining rows
    current_size: i32,
    current_max_size: i32,
    selection: Vec<Select>,
    soluble: Vec<Soluble>, // solubility vector (complex systems only)
}

/// A resumable solver for `R * M = C`. Build it with [`insert_row`](Self::insert_row) /
/// [`insert_column`](Self::insert_column), then call [`solve`](Self::solve) repeatedly: the first call
/// finds the first solution, each later call the next, returning `false` once exhausted. Read the
/// current solution with [`solution`](Self::solution). Adding rows/columns after the first `solve` is
/// a bug (asserted in debug).
pub(crate) struct DiophantineSystem {
    rows: Vec<Row>,
    columns: Vec<i32>,
    row_permute: Vec<usize>,
    column_sum: i32,
    max_column_value: i32,
    closed: bool,
    complex: bool,
    failed: bool,
}

impl DiophantineSystem {
    pub(crate) fn new(est_rows: usize, est_columns: usize) -> Self {
        DiophantineSystem {
            rows: Vec::with_capacity(est_rows),
            columns: Vec::with_capacity(est_columns),
            row_permute: Vec::new(),
            column_sum: 0,
            max_column_value: 0,
            closed: false,
            complex: false,
            failed: false,
        }
    }

    pub(crate) fn insert_row(&mut self, coeff: i32, min_size: i32, max_size: i32) {
        debug_assert!(!self.closed, "system closed");
        debug_assert!(coeff > 0, "bad row coefficient");
        debug_assert!(min_size >= 0 && min_size <= max_size, "bad row size bounds");
        let name = self.rows.len();
        self.rows.push(Row {
            name,
            coeff,
            min_size,
            min_product: 0,
            min_leave: 0,
            max_size,
            max_product: 0,
            max_leave: 0,
            current_size: 0,
            current_max_size: 0,
            selection: Vec::new(),
            soluble: Vec::new(),
        });
    }

    pub(crate) fn insert_column(&mut self, value: i32) {
        debug_assert!(!self.closed, "system closed");
        debug_assert!(value > 0, "bad column value");
        self.columns.push(value);
        self.column_sum += value;
        if value > self.max_column_value {
            self.max_column_value = value;
        }
    }

    // Part of the faithful API surface (Maude's `rowCount`); the no-alien driver tracks the extension
    // row by its known original index instead, so this is unused until the xmatch extension work.
    #[allow(dead_code)]
    pub(crate) fn row_count(&self) -> usize {
        self.rows.len()
    }

    #[cfg(test)]
    pub(crate) fn column_count(&self) -> usize {
        self.columns.len()
    }

    /// `M[row, column]` of the current solution (`solve` must have returned `true`). `row` is the
    /// **original** insertion index; it is mapped through `row_permute` to the sorted position.
    pub(crate) fn solution(&self, row: usize, column: usize) -> i32 {
        debug_assert!(self.closed && !self.failed, "no current solution");
        let s = &self.rows[self.row_permute[row]].selection[column];
        s.base + s.extra
    }

    /// Find the first (if not yet closed) or next solution; `false` when exhausted.
    pub(crate) fn solve(&mut self) -> bool {
        let find_first = !self.closed;
        if find_first && !self.precompute() {
            return false;
        }
        debug_assert!(!self.failed, "attempt to solve failed system");
        if self.complex {
            self.solve_complex(find_first)
        } else {
            self.solve_simple(find_first)
        }
    }

    /// Sort rows in order of **descending** coefficients, ties split by **ascending** maximum sum.
    fn row_lt(i: &Row, j: &Row) -> bool {
        let t = j.coeff - i.coeff;
        if t != 0 {
            t < 0
        } else {
            (i.max_size - j.max_size) < 0
        }
    }

    /// Check for trivial failure, sort `R`, fill `row_permute`, compute `minLeave`/`maxLeave`, allocate
    /// selection vectors; for a complex system also build solubility vectors and check each column.
    fn precompute(&mut self) -> bool {
        let nr_rows = self.rows.len();
        debug_assert!(nr_rows > 0, "no rows");
        let nr_columns = self.columns.len();
        debug_assert!(nr_columns > 0, "no columns");
        self.closed = true;

        let mut sum_of_min_products: i64 = 0;
        let mut sum_of_max_products: i64 = 0;
        for r in &mut self.rows {
            if r.max_size == UNBOUNDED {
                r.max_size = self.column_sum; // good substitute for infinity!
            }
            r.min_product = r.min_size * r.coeff;
            sum_of_min_products += i64::from(r.min_product);
            r.max_product = r.max_size * r.coeff;
            sum_of_max_products += i64::from(r.max_product);
        }
        if sum_of_min_products > i64::from(self.column_sum)
            || sum_of_max_products < i64::from(self.column_sum)
        {
            self.failed = true;
            return false;
        }
        self.rows.sort_by(|a, b| {
            if Self::row_lt(a, b) {
                std::cmp::Ordering::Less
            } else if Self::row_lt(b, a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        self.row_permute = vec![0; nr_rows];
        let mut min_total = 0;
        let mut max_total = 0;
        for i in (0..nr_rows).rev() {
            let r = &mut self.rows[i];
            self.row_permute[r.name] = i;
            r.min_leave = min_total;
            r.max_leave = max_total;
            r.selection = vec![Select::default(); nr_columns];
            min_total += r.min_product;
            max_total += r.max_product;
        }
        if self.rows[nr_rows - 1].coeff > 1
            || self.rows[nr_rows - 1].max_size < self.max_column_value
        {
            // Complex case.
            self.build_solubility_vectors();
            for j in 0..nr_columns {
                let v = self.columns[j] as usize;
                if self.rows[0].soluble[v].min < 0 {
                    self.failed = true;
                    return false;
                }
            }
            self.complex = true;
        }
        true
    }

    /// Build the solubility vectors via dynamic programming (descending over rows).
    fn build_solubility_vectors(&mut self) {
        let nr_rows = self.rows.len();
        let mcv = self.max_column_value;
        // Solubility vector for the last row.
        {
            let r = &mut self.rows[nr_rows - 1];
            r.soluble = vec![
                Soluble {
                    min: INSOLUBLE,
                    max: INSOLUBLE
                };
                (mcv + 1) as usize
            ];
            let coeff = r.coeff;
            r.soluble[0] = Soluble { min: 0, max: 0 };
            let mut count = 0;
            let mut j = 0;
            while j <= mcv && count <= r.max_size {
                r.soluble[j as usize] = Soluble {
                    min: count,
                    max: count,
                };
                count += 1;
                j += coeff;
            }
        }
        // Remaining vectors in descending order. `next` = row i's vector (being built), `prev` = row
        // i+1's (already built). Since `t = j - coeff < j` and j ascends, `next[t]` is ready.
        for i in (0..nr_rows - 1).rev() {
            let coeff = self.rows[i].coeff;
            let max_size = self.rows[i].max_size;
            let mut next = vec![
                Soluble {
                    min: INSOLUBLE,
                    max: INSOLUBLE
                };
                (mcv + 1) as usize
            ];
            for j in 0..=mcv {
                let ju = j as usize;
                let t = j - coeff;
                let prev_j_min = self.rows[i + 1].soluble[ju].min;
                let next_t_min = if t >= 0 {
                    next[t as usize].min
                } else {
                    INSOLUBLE
                };
                if t >= 0 && next_t_min != INSOLUBLE && next_t_min < max_size {
                    let next_t_max = next[t as usize].max;
                    next[ju].min = if prev_j_min == INSOLUBLE {
                        next_t_min + 1
                    } else {
                        0
                    };
                    if next_t_max < max_size {
                        next[ju].max = next_t_max + 1;
                    } else {
                        let mut new_max = max_size;
                        let mut k = j - max_size * coeff;
                        while self.rows[i + 1].soluble[k as usize].min == INSOLUBLE {
                            new_max -= 1;
                            k += coeff;
                        }
                        debug_assert!(new_max >= next_t_min + 1, "bad newMax");
                        next[ju].max = new_max;
                    }
                } else {
                    let v = if prev_j_min == INSOLUBLE {
                        INSOLUBLE
                    } else {
                        0
                    };
                    next[ju] = Soluble { min: v, max: v };
                }
            }
            self.rows[i].soluble = next;
        }
    }

    /// For each initial segment of the unsolved portion of `R`, verify there is a large-enough sum of
    /// large-enough columns to rule out a certain failure. `false` ⇒ this partial solution must fail.
    fn viable(&self, row_nr: usize) -> bool {
        let nr_rows = self.rows.len();
        let nr_columns = self.columns.len();
        let mut local_sum_of_min_products = 0;
        for i in row_nr..nr_rows.saturating_sub(1) {
            // no need to consider last row
            let t = self.rows[i].min_product;
            if t > 0 {
                local_sum_of_min_products += t;
                let lower_limit = self.rows[i].coeff;
                let mut local_column_sum = 0;
                let mut okay = false;
                for j in 0..nr_columns {
                    let c = self.columns[j];
                    if c >= lower_limit {
                        local_column_sum += c;
                        if local_column_sum >= local_sum_of_min_products {
                            okay = true;
                            break;
                        }
                    }
                }
                if !okay {
                    return false;
                }
            }
        }
        true
    }

    // ---- simple case -------------------------------------------------------

    fn solve_simple(&mut self, mut find_first: bool) -> bool {
        if self.rows.len() > 1 {
            let penultimate = self.rows.len() - 2;
            let mut i = if find_first { 0 } else { penultimate };
            loop {
                find_first = self.solve_row_simple(i, find_first);
                if find_first {
                    if i == penultimate {
                        break;
                    }
                    i += 1;
                } else {
                    if i == 0 {
                        break;
                    }
                    i -= 1;
                }
            }
        }
        if find_first {
            self.solve_last_row_simple();
        } else {
            self.failed = true;
        }
        find_first
    }

    fn solve_last_row_simple(&mut self) {
        let last = self.rows.len() - 1;
        let nr_columns = self.columns.len();
        for i in 0..nr_columns {
            self.rows[last].selection[i].extra = self.columns[i];
        }
    }

    fn solve_row_simple(&mut self, row_nr: usize, find_first: bool) -> bool {
        if find_first {
            if !self.viable(row_nr) {
                return false;
            }
            let coeff = self.rows[row_nr].coeff;
            let nr_columns = self.columns.len();
            let mut column_total = 0;
            let mut max_sum = 0;
            for i in 0..nr_columns {
                self.rows[row_nr].selection[i].extra = 0;
                let t = self.columns[i];
                column_total += t;
                if t >= coeff {
                    let q = t / coeff;
                    max_sum += q;
                    self.rows[row_nr].selection[i].max_extra = q;
                } else {
                    self.rows[row_nr].selection[i].max_extra = 0;
                }
            }
            let min_size = self.rows[row_nr].min_size.max(ceiling_division(
                column_total - self.rows[row_nr].max_leave,
                coeff,
            ));
            let max_size = max_sum.min(self.rows[row_nr].max_size).min(floor_division(
                column_total - self.rows[row_nr].min_leave,
                coeff,
            ));
            if min_size > max_size {
                return false;
            }
            self.rows[row_nr].current_size = min_size;
            self.rows[row_nr].current_max_size = max_size;
        } else {
            if Self::multiset_select(&mut self.rows[row_nr], &mut self.columns, false) {
                return true;
            }
            if self.rows[row_nr].current_size == self.rows[row_nr].current_max_size {
                return false;
            }
            self.rows[row_nr].current_size += 1;
        }
        Self::multiset_select(&mut self.rows[row_nr], &mut self.columns, true) // always succeeds
    }

    /// Find a selection from a multiset (simple case): undo the previous selection until some element
    /// can be increased by one without exceeding the overall selection size, then make up the size by
    /// selecting the earliest elements available.
    fn multiset_select(row: &mut Row, bag: &mut [i32], find_first: bool) -> bool {
        let bag_length = bag.len();
        let mut undone;
        if !find_first {
            if row.current_size > 0 {
                undone = 0;
                for j in 0..bag_length {
                    debug_assert!(row.selection[j].extra <= row.selection[j].max_extra);
                    let t = row.selection[j].extra;
                    if undone > 0 && t < row.selection[j].max_extra {
                        row.selection[j].extra += 1;
                        undone -= 1;
                        bag[j] -= row.coeff;
                        return Self::multiset_select_forwards(row, bag, undone);
                    }
                    if t > 0 {
                        row.selection[j].extra = 0;
                        undone += t;
                        bag[j] += t * row.coeff;
                    }
                }
            }
            return false;
        }
        undone = row.current_size;
        Self::multiset_select_forwards(row, bag, undone)
    }

    fn multiset_select_forwards(row: &mut Row, bag: &mut [i32], mut undone: i32) -> bool {
        let mut j = 0;
        while undone > 0 {
            debug_assert!(j < bag.len(), "overran bag");
            let t = undone.min(row.selection[j].max_extra);
            if t > 0 {
                row.selection[j].extra = t;
                undone -= t;
                bag[j] -= t * row.coeff;
            }
            j += 1;
        }
        true
    }

    // ---- complex case ------------------------------------------------------

    fn solve_complex(&mut self, mut find_first: bool) -> bool {
        if self.rows.len() > 1 {
            let penultimate = self.rows.len() - 2;
            let mut i = if find_first { 0 } else { penultimate };
            loop {
                find_first = self.solve_row_complex(i, find_first);
                if find_first {
                    if i == penultimate {
                        break;
                    }
                    i += 1;
                } else {
                    if i == 0 {
                        break;
                    }
                    i -= 1;
                }
            }
        }
        if find_first {
            self.solve_last_row_complex();
        } else {
            self.failed = true;
        }
        find_first
    }

    fn solve_last_row_complex(&mut self) {
        let last = self.rows.len() - 1;
        let nr_columns = self.columns.len();
        for i in 0..nr_columns {
            let t = self.rows[last].soluble[self.columns[i] as usize].min;
            debug_assert!(t != INSOLUBLE, "solubility bug");
            self.rows[last].selection[i].extra = t;
        }
    }

    fn solve_row_complex(&mut self, row_nr: usize, find_first: bool) -> bool {
        let nr_columns = self.columns.len();
        let coeff = self.rows[row_nr].coeff;
        if find_first {
            if !self.viable(row_nr) {
                return false;
            }
            let mut column_total = 0;
            let mut max_sum = 0;
            let mut min_sum = 0;
            for i in 0..nr_columns {
                let t = self.columns[i];
                let min = self.rows[row_nr].soluble[t as usize].min;
                let max = self.rows[row_nr].soluble[t as usize].max;
                debug_assert!(
                    min != INSOLUBLE && max != INSOLUBLE && min <= max,
                    "solubility bug"
                );
                self.rows[row_nr].selection[i].base = min;
                self.rows[row_nr].selection[i].extra = 0;
                self.rows[row_nr].selection[i].max_extra = max - min;
                column_total += t;
                min_sum += min;
                max_sum += max;
            }
            let min_size = min_sum
                .max(self.rows[row_nr].min_size)
                .max(ceiling_division(
                    column_total - self.rows[row_nr].max_leave,
                    coeff,
                ));
            let max_size = max_sum.min(self.rows[row_nr].max_size).min(floor_division(
                column_total - self.rows[row_nr].min_leave,
                coeff,
            ));
            if min_size > max_size {
                return false;
            }
            self.rows[row_nr].current_size = min_size - min_sum;
            self.rows[row_nr].current_max_size = max_size - min_sum;
            for i in 0..nr_columns {
                if self.rows[row_nr].selection[i].base > 0 {
                    self.columns[i] -= self.rows[row_nr].selection[i].base * coeff;
                    debug_assert!(self.columns[i] >= 0, "value -ve");
                }
            }
        } else {
            // The non-selected part's solubility is that of the NEXT row (soluble2 in C++).
            let done = {
                let (this_row, next_soluble) = split_row_and_soluble(&mut self.rows, row_nr);
                Self::multiset_complex(this_row, &mut self.columns, next_soluble, false)
            };
            if done {
                return true;
            }
            self.rows[row_nr].current_size += 1;
        }
        while self.rows[row_nr].current_size <= self.rows[row_nr].current_max_size {
            let done = {
                let (this_row, next_soluble) = split_row_and_soluble(&mut self.rows, row_nr);
                Self::multiset_complex(this_row, &mut self.columns, next_soluble, true)
            };
            if done {
                return true;
            }
            self.rows[row_nr].current_size += 1;
        }
        for i in 0..nr_columns {
            if self.rows[row_nr].selection[i].base > 0 {
                self.columns[i] += self.rows[row_nr].selection[i].base * coeff;
                debug_assert!(self.columns[i] <= self.max_column_value, "value too big");
            }
        }
        false
    }

    /// Find a selection from a multiset (complex case): like `multiset_select`, but respecting the
    /// solubility constraints of the non-selected part (`soluble` = the next row's solubility vector).
    /// A faithful emulation of the C++ `multisetComplex`, whose `backtrack:`/`forwards:` labels + gotos
    /// become a two-mode state machine sharing `undone` (and re-scanning `j` from 0 on each entry).
    fn multiset_complex(
        row: &mut Row,
        bag: &mut [i32],
        soluble: &[Soluble],
        find_first: bool,
    ) -> bool {
        let bag_length = bag.len();
        let mut undone: i32;
        let mut mode: Mode;
        if !find_first {
            if row.current_size > 0 {
                undone = 0;
                mode = Mode::Backtrack;
            } else {
                return false;
            }
        } else {
            undone = row.current_size;
            mode = Mode::Forwards;
        }
        loop {
            match mode {
                Mode::Backtrack => {
                    let mut advanced = false;
                    let mut j = 0;
                    while j < bag_length {
                        debug_assert!(row.selection[j].extra <= row.selection[j].max_extra);
                        let t = row.selection[j].extra;
                        if undone > 0 && t < row.selection[j].max_extra {
                            let mut c = bag[j];
                            let mut e = 1;
                            let mut found = false;
                            while e <= undone {
                                c -= row.coeff;
                                if soluble[c as usize].min != INSOLUBLE {
                                    row.selection[j].extra = t + e;
                                    bag[j] = c;
                                    undone -= e;
                                    found = true;
                                    break;
                                }
                                e += 1;
                            }
                            if found {
                                advanced = true;
                                break; // goto forwards
                            }
                        }
                        if t > 0 {
                            row.selection[j].extra = 0;
                            undone += t;
                            bag[j] += t * row.coeff;
                        }
                        j += 1;
                    }
                    if advanced {
                        mode = Mode::Forwards;
                    } else {
                        return false;
                    }
                }
                Mode::Forwards => {
                    let mut j = 0;
                    let mut dead = false;
                    while undone > 0 {
                        debug_assert!(j < bag_length, "overran bag");
                        let t = row.selection[j].max_extra;
                        if t <= undone {
                            if t > 0 {
                                row.selection[j].extra = t;
                                undone -= t;
                                bag[j] -= t * row.coeff;
                            }
                        } else {
                            row.selection[j].extra = undone;
                            bag[j] -= undone * row.coeff;
                            undone = 0;
                            if soluble[bag[j] as usize].min == INSOLUBLE {
                                dead = true;
                                break; // goto backtrack
                            }
                        }
                        j += 1;
                    }
                    if dead {
                        mode = Mode::Backtrack;
                    } else {
                        return true;
                    }
                }
            }
        }
    }
}

/// The two labels of `multisetComplex` (`backtrack:` / `forwards:`), emulated as a state machine.
enum Mode {
    Backtrack,
    Forwards,
}

/// Borrow `rows[row_nr]` mutably and `rows[row_nr + 1].soluble` immutably at the same time (the
/// complex solver needs the current row's selection state and the *next* row's solubility vector).
fn split_row_and_soluble(rows: &mut [Row], row_nr: usize) -> (&mut Row, &[Soluble]) {
    let (left, right) = rows.split_at_mut(row_nr + 1);
    (&mut left[row_nr], &right[0].soluble)
}

/// `ceil(a / b)` for `b > 0`, matching Maude's `ceilingDivision` (handles negative `a`).
fn ceiling_division(a: i32, b: i32) -> i32 {
    debug_assert!(b > 0);
    if a >= 0 { (a + b - 1) / b } else { -((-a) / b) }
}

/// `floor(a / b)` for `b > 0`, matching Maude's `floorDivision` (handles negative `a`).
fn floor_division(a: i32, b: i32) -> i32 {
    debug_assert!(b > 0);
    if a >= 0 { a / b } else { -(((-a) + b - 1) / b) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Collect the full solution sequence as a `Vec` of `n×m` matrices (row-major by original row
    /// index), driving `solve()` to exhaustion.
    fn all_solutions(sys: &mut DiophantineSystem, nr_rows: usize) -> Vec<Vec<Vec<i32>>> {
        let nr_cols = sys.column_count();
        let mut out = Vec::new();
        while sys.solve() {
            let mut m = vec![vec![0; nr_cols]; nr_rows];
            for r in 0..nr_rows {
                for c in 0..nr_cols {
                    m[r][c] = sys.solution(r, c);
                }
            }
            out.push(m);
        }
        out
    }

    /// `X + Y <=? a + b + c`, both variables of size 1..3. Hand-traced from the C++ `solveSimple`
    /// (see module docs): minimal-X-size first, within a size by ascending column selection. This is
    /// the load-bearing AC solution order.
    #[test]
    fn two_vars_three_singletons_sequence() {
        let mut sys = DiophantineSystem::new(2, 3);
        sys.insert_row(1, 1, 3); // X  (row 0)
        sys.insert_row(1, 1, 3); // Y  (row 1)
        sys.insert_column(1);
        sys.insert_column(1);
        sys.insert_column(1);
        let sols = all_solutions(&mut sys, 2);
        // Each entry: [X row, Y row] over columns (a, b, c).
        let expected = vec![
            vec![vec![1, 0, 0], vec![0, 1, 1]], // X=a,  Y=b+c
            vec![vec![0, 1, 0], vec![1, 0, 1]], // X=b,  Y=a+c
            vec![vec![0, 0, 1], vec![1, 1, 0]], // X=c,  Y=a+b
            vec![vec![1, 1, 0], vec![0, 0, 1]], // X=a+b,Y=c
            vec![vec![1, 0, 1], vec![0, 1, 0]], // X=a+c,Y=b
            vec![vec![0, 1, 1], vec![1, 0, 0]], // X=b+c,Y=a
        ];
        assert_eq!(sols, expected);
    }

    /// Same solution *set* but with a repeated column value: `X + Y <=? a + a + b` (column a has
    /// value 2, column b value 1). Verifies multiplicity handling.
    #[test]
    fn two_vars_repeated_column() {
        let mut sys = DiophantineSystem::new(2, 2);
        sys.insert_row(1, 1, 3);
        sys.insert_row(1, 1, 3);
        sys.insert_column(2); // a with multiplicity 2
        sys.insert_column(1); // b
        let sols = all_solutions(&mut sys, 2);
        // X grows smallest-first; within a size, columns are selected earliest-first (col a before b).
        let expected = vec![
            vec![vec![1, 0], vec![1, 1]], // X=a,     Y=a+b
            vec![vec![0, 1], vec![2, 0]], // X=b,     Y=a+a
            vec![vec![2, 0], vec![0, 1]], // X=a+a,   Y=b
            vec![vec![1, 1], vec![1, 0]], // X=a+b,   Y=a
        ];
        assert_eq!(sols, expected);
    }

    /// A single collector variable takes everything: `X <=? a + b`, size 0..2. One solution.
    #[test]
    fn lone_collector_takes_all() {
        let mut sys = DiophantineSystem::new(1, 2);
        sys.insert_row(1, 0, 2);
        sys.insert_column(1);
        sys.insert_column(1);
        let sols = all_solutions(&mut sys, 1);
        assert_eq!(sols, vec![vec![vec![1, 1]]]);
    }

    /// Coefficient-2 variable: `2X + Y <=? a + a + b + b` where a,b each have value 2.
    /// X (coeff 2) must take whole copies; enumerated with X descending in the sorted order
    /// (higher coeff sorts first). Verifies the coefficient handling + ordering.
    #[test]
    fn coeff_two_variable() {
        // R = [2, 1], C = [2, 2].  R*M = C  =>  2*M[0,j] + M[1,j] = C[j].
        let mut sys = DiophantineSystem::new(2, 2);
        sys.insert_row(2, 0, 2); // X (coeff 2)  row 0
        sys.insert_row(1, 0, 4); // Y (coeff 1)  row 1
        sys.insert_column(2);
        sys.insert_column(2);
        let sols = all_solutions(&mut sys, 2);
        // Valid (M[0,j], M[1,j]) per column j with value 2: (0,2) or (1,0).
        // So X in {none, a, b, a+b} and Y takes the rest. All 4 combos are valid.
        // Order: X (higher coeff, row 0) solved outer, smallest first.
        let expected = vec![
            vec![vec![0, 0], vec![2, 2]], // X=empty,  Y=a a b b
            vec![vec![1, 0], vec![0, 2]], // X=a,      Y=b b
            vec![vec![0, 1], vec![2, 0]], // X=b,      Y=a a
            vec![vec![1, 1], vec![0, 0]], // X=a+b,    Y=empty
        ];
        assert_eq!(sols, expected);
    }

    /// Forces the **complex** path: no coefficient-1 row (all coeffs > 1), so the solubility vectors
    /// are exercised. `2X + 3Y <=? 12` (single column value 12). Solutions: 2x+3y=12, x,y>=0:
    /// (x,y) in {(0,4),(3,2),(6,0)}. Rows sorted desc coeff => Y(3) row0, X(2) row1.
    #[test]
    fn complex_two_coeffs_single_column() {
        let mut sys = DiophantineSystem::new(2, 1);
        sys.insert_row(2, 0, 6); // X coeff 2
        sys.insert_row(3, 0, 4); // Y coeff 3
        sys.insert_column(12);
        let sols = all_solutions(&mut sys, 2);
        // solution[row0=X_orig?].  Rows reported by ORIGINAL index: row0=X(coeff2), row1=Y(coeff3).
        // 2*X + 3*Y = 12.  Enumerated by the sorted-desc-coeff outer loop (Y outer).
        // Y smallest first: y=0 => x=6; y=2 => x=3; y=4 => x=0.
        let expected = vec![
            vec![vec![6], vec![0]], // X=6, Y=0
            vec![vec![3], vec![2]], // X=3, Y=2
            vec![vec![0], vec![4]], // X=0, Y=4
        ];
        assert_eq!(sols, expected);
    }

    /// An infeasible system yields no solutions: `3X <=? 5` has no natural solution.
    #[test]
    fn infeasible_system() {
        let mut sys = DiophantineSystem::new(1, 1);
        sys.insert_row(3, 0, 5);
        sys.insert_column(5);
        assert_eq!(all_solutions(&mut sys, 1).len(), 0);
    }
}
