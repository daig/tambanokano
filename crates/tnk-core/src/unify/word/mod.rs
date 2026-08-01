//! Pure-integer associative and associative-with-identity word unification. The solver separates
//! packed variable constraints, system-level search, equation levels, and PigPug prefix moves.

mod constraint;
mod pigpug;
mod word_level;
mod word_system;

pub(crate) use word_system::WordSystem;

pub(crate) type Word = Vec<usize>;

pub(crate) const FAILURE: u8 = 0;
pub(crate) const SUCCESS: u8 = 1;
pub(crate) const INCOMPLETE: u8 = 2;

#[cfg(test)]
mod tests {
    use super::{INCOMPLETE, SUCCESS, WordSystem};

    fn solution(system: &WordSystem, originals: usize) -> Vec<Vec<usize>> {
        (0..originals)
            .map(|i| system.assignment(i).to_vec())
            .collect()
    }

    #[test]
    fn strict_left_linear_sequence_follows_move_order() {
        // A B =? X Y. The three elementary unifiers are emitted in
        // RHS_PEEL, LHS_PEEL, EQUATE order.
        let mut system = WordSystem::new(4, 1, false);
        system.add_equation(0, vec![0, 1], vec![2, 3]);
        let mut actual = Vec::new();
        while system.find_next_solution() & SUCCESS != 0 {
            actual.push(solution(&system, 4));
        }
        assert_eq!(
            actual,
            vec![
                vec![vec![2, 4], vec![1], vec![2], vec![4, 1]],
                vec![vec![0], vec![4, 3], vec![0, 4], vec![3]],
                vec![vec![2], vec![3], vec![2], vec![3]],
            ]
        );
    }

    #[test]
    fn identity_selections_follow_nonempty_bitmask_order() {
        let mut system = WordSystem::new(2, 0, false);
        system.set_take_empty(0);
        system.set_take_empty(1);
        let mut actual = Vec::new();
        while system.find_next_solution() & SUCCESS != 0 {
            actual.push(solution(&system, 2));
        }
        assert_eq!(
            actual,
            vec![
                vec![vec![0], vec![1]],
                vec![vec![], vec![1]],
                vec![vec![0], vec![]],
                vec![vec![], vec![]],
            ]
        );
    }

    #[test]
    fn multiple_equations_simplify_to_a_single_solution() {
        let mut system = WordSystem::new(4, 2, false);
        system.add_equation(0, vec![0, 1], vec![2, 3]);
        system.add_equation(1, vec![0], vec![2]);
        assert_eq!(system.find_next_solution(), SUCCESS);
        assert_eq!(
            solution(&system, 4),
            vec![vec![2], vec![3], vec![2], vec![3]]
        );
        assert_eq!(system.find_next_solution(), 0);
    }

    #[test]
    fn depth_bounded_nonlinear_search_reports_incomplete() {
        // Variable 0 occurs three times, selecting depth-bounded rather than cycle-detected search.
        let mut system = WordSystem::new(3, 1, false);
        system.add_equation(0, vec![0, 0, 0], vec![1, 1, 2, 1]);
        let mut solutions = Vec::new();
        let final_flags = loop {
            let flags = system.find_next_solution();
            if flags & SUCCESS == 0 {
                break flags;
            }
            solutions.push(solution(&system, 3));
        };
        assert!(!solutions.is_empty());
        assert_eq!(final_flags & INCOMPLETE, INCOMPLETE);
    }

    #[test]
    fn cycle_detected_infinite_family_reports_incomplete() {
        let mut system = WordSystem::new(2, 1, false);
        system.add_equation(0, vec![0, 1], vec![1, 0]);
        let mut count = 0;
        let final_flags = loop {
            let flags = system.find_next_solution();
            if flags & SUCCESS == 0 {
                break flags;
            }
            count += 1;
        };
        assert!(count > 0);
        assert_eq!(final_flags & INCOMPLETE, INCOMPLETE);
    }

    #[test]
    fn constraints_nulls_and_existing_assignments_share_the_fixed_point() {
        let mut system = WordSystem::new(3, 0, false);
        system.set_take_empty(0);
        system.set_take_empty(1);
        system.set_theory_constraint(2, 9);
        system.add_assignment(0, vec![1]);
        system.add_null_equation(vec![0]);
        assert_eq!(system.find_next_solution(), SUCCESS);
        assert_eq!(solution(&system, 3), vec![vec![], vec![], vec![2]]);
        assert_eq!(system.nr_variables(), 3);
        assert_eq!(system.find_next_solution(), 0);
    }
}
