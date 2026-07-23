//! Owned, query-local Boolean formulas and streaming DNF normalization.

use crate::term::Term;

/// An equality (`positive == true`) or disequality (`positive == false`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    pub lhs: Term,
    pub rhs: Term,
    pub positive: bool,
}

/// A Boolean formula over equality and disequality literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Literal(Literal),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
}

/// One conjunction in disjunctive normal form.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Branch {
    pub positive: Vec<(Term, Term)>,
    pub negative: Vec<(Term, Term)>,
}

/// A streaming iterator over the branches of a formula's disjunctive normal form.
///
/// The iterator performs a depth-first, left-to-right traversal. It keeps only the
/// unexplored alternatives and the partial conjunctions needed to resume them;
/// it never constructs the complete DNF.
#[derive(Debug)]
pub struct Dnf {
    nodes: Vec<Node>,
    work: Vec<State>,
}

#[derive(Debug)]
enum Node {
    Literal(Literal),
    And(Vec<NodeId>),
    Or(Vec<NodeId>),
}

type NodeId = usize;

#[derive(Debug, Clone)]
struct State {
    /// A LIFO stack of formulas still to conjoin into `branch`.
    pending: Vec<NodeId>,
    branch: Branch,
}

impl Formula {
    /// Convert this formula to a streaming sequence of DNF branches.
    ///
    /// Implication and equivalence are eliminated, negation is pushed to the
    /// literals, and nested conjunctions and disjunctions are flattened before
    /// iteration begins.
    pub fn into_dnf(self) -> Dnf {
        Dnf::new(normalize(self, false))
    }

    /// Negate this formula and return it in negation normal form.
    ///
    /// The result contains only [`Formula::Literal`], [`Formula::And`], and
    /// [`Formula::Or`]. Nested occurrences of the same connective are flattened.
    pub fn negated(self) -> Formula {
        normalize(self, true)
    }
}

impl Dnf {
    fn new(formula: Formula) -> Self {
        let mut nodes = Vec::new();
        let root = lower(formula, &mut nodes);
        Self {
            nodes,
            work: vec![State {
                pending: vec![root],
                branch: Branch::default(),
            }],
        }
    }
}

impl Iterator for Dnf {
    type Item = Branch;

    fn next(&mut self) -> Option<Self::Item> {
        'work: loop {
            let mut state = self.work.pop()?;

            loop {
                let Some(node_id) = state.pending.pop() else {
                    return Some(state.branch);
                };

                match &self.nodes[node_id] {
                    Node::Literal(literal) => {
                        let pair = (literal.lhs.clone(), literal.rhs.clone());
                        if literal.positive {
                            state.branch.positive.push(pair);
                        } else {
                            state.branch.negative.push(pair);
                        }
                    }
                    Node::And(children) => {
                        // Reverse insertion makes the leftmost child the next one processed.
                        state.pending.extend(children.iter().rev().copied());
                    }
                    Node::Or(children) => {
                        let Some((&first, rest)) = children.split_first() else {
                            // An empty disjunction contributes no branch.
                            continue 'work;
                        };
                        // Keep the leftmost alternative in the current state and put
                        // later alternatives on the work stack in reverse order.
                        for child in rest.iter().rev().copied() {
                            let mut alternative = state.clone();
                            alternative.pending.push(child);
                            self.work.push(alternative);
                        }
                        state.pending.push(first);
                    }
                }
            }
        }
    }
}

impl std::iter::FusedIterator for Dnf {}

/// Produce a flattened negation-normal form. `negated` records whether the
/// current subformula occurs under an odd number of negations.
fn normalize(formula: Formula, negated: bool) -> Formula {
    match formula {
        Formula::Literal(mut literal) => {
            if negated {
                literal.positive = !literal.positive;
            }
            Formula::Literal(literal)
        }
        Formula::Not(inner) => normalize(*inner, !negated),
        Formula::And(children) => {
            let children = children.into_iter().map(|child| normalize(child, negated));
            if negated {
                disjunction(children)
            } else {
                conjunction(children)
            }
        }
        Formula::Or(children) => {
            let children = children.into_iter().map(|child| normalize(child, negated));
            if negated {
                conjunction(children)
            } else {
                disjunction(children)
            }
        }
        Formula::Implies(lhs, rhs) => {
            let lhs = *lhs;
            let rhs = *rhs;
            if negated {
                // ~(lhs => rhs) = lhs /\ ~rhs
                conjunction([normalize(lhs, false), normalize(rhs, true)])
            } else {
                // lhs => rhs = ~lhs \/ rhs
                disjunction([normalize(lhs, true), normalize(rhs, false)])
            }
        }
        Formula::Iff(lhs, rhs) => {
            let lhs = *lhs;
            let rhs = *rhs;
            let reverse_lhs = lhs.clone();
            let reverse_rhs = rhs.clone();

            if negated {
                // Negate (lhs => rhs) /\ (rhs => lhs), preserving its
                // deterministic left-to-right expansion order.
                disjunction([
                    conjunction([normalize(lhs, false), normalize(rhs, true)]),
                    conjunction([normalize(reverse_rhs, false), normalize(reverse_lhs, true)]),
                ])
            } else {
                conjunction([
                    disjunction([normalize(lhs, true), normalize(rhs, false)]),
                    disjunction([normalize(reverse_rhs, true), normalize(reverse_lhs, false)]),
                ])
            }
        }
    }
}

fn conjunction(children: impl IntoIterator<Item = Formula>) -> Formula {
    let mut flattened = Vec::new();
    for child in children {
        match child {
            Formula::And(nested) => flattened.extend(nested),
            child => flattened.push(child),
        }
    }
    Formula::And(flattened)
}

fn disjunction(children: impl IntoIterator<Item = Formula>) -> Formula {
    let mut flattened = Vec::new();
    for child in children {
        match child {
            Formula::Or(nested) => flattened.extend(nested),
            child => flattened.push(child),
        }
    }
    Formula::Or(flattened)
}

/// Lower NNF into stable node indices so iterator states can share formula
/// structure without self-references or cloning whole subformulas.
fn lower(formula: Formula, nodes: &mut Vec<Node>) -> NodeId {
    let node = match formula {
        Formula::Literal(literal) => Node::Literal(literal),
        Formula::And(children) => Node::And(
            children
                .into_iter()
                .map(|child| lower(child, nodes))
                .collect(),
        ),
        Formula::Or(children) => Node::Or(
            children
                .into_iter()
                .map(|child| lower(child, nodes))
                .collect(),
        ),
        Formula::Not(_) | Formula::Implies(_, _) | Formula::Iff(_, _) => {
            unreachable!("formula must be in negation normal form before lowering")
        }
    };
    let id = nodes.len();
    nodes.push(node);
    id
}

#[cfg(test)]
mod tests {
    use super::{Branch, Formula, Literal};
    use crate::sort::SortId;
    use crate::term::Term;

    fn term(index: u32) -> Term {
        Term::var(index, SortId::from_raw(0))
    }

    fn literal(index: u32, positive: bool) -> Formula {
        Formula::Literal(Literal {
            lhs: term(index),
            rhs: term(index + 100),
            positive,
        })
    }

    fn branch(positive: &[u32], negative: &[u32]) -> Branch {
        Branch {
            positive: positive
                .iter()
                .map(|&index| (term(index), term(index + 100)))
                .collect(),
            negative: negative
                .iter()
                .map(|&index| (term(index), term(index + 100)))
                .collect(),
        }
    }

    #[test]
    fn streams_cartesian_products_in_left_to_right_order() {
        let formula = Formula::And(vec![
            Formula::Or(vec![
                literal(1, true),
                Formula::Or(vec![literal(2, false), literal(3, true)]),
            ]),
            Formula::Or(vec![literal(4, false), literal(5, true)]),
        ]);

        let branches: Vec<_> = formula.into_dnf().collect();

        assert_eq!(
            branches,
            vec![
                branch(&[1], &[4]),
                branch(&[1, 5], &[]),
                branch(&[], &[2, 4]),
                branch(&[5], &[2]),
                branch(&[3], &[4]),
                branch(&[3, 5], &[]),
            ]
        );
    }

    #[test]
    fn negation_eliminates_implication_and_flattens_conjunctions() {
        let formula = Formula::Implies(
            Box::new(Formula::And(vec![
                literal(1, true),
                Formula::And(vec![literal(2, false)]),
            ])),
            Box::new(Formula::Not(Box::new(literal(3, true)))),
        );

        assert_eq!(
            formula.negated(),
            Formula::And(vec![literal(1, true), literal(2, false), literal(3, true),])
        );
    }

    #[test]
    fn equivalence_expansion_is_streamed_in_deterministic_order() {
        let formula = Formula::Iff(Box::new(literal(1, true)), Box::new(literal(2, true)));

        let branches: Vec<_> = formula.into_dnf().collect();

        assert_eq!(
            branches,
            vec![
                branch(&[], &[1, 2]),
                branch(&[1], &[1]),
                branch(&[2], &[2]),
                branch(&[2, 1], &[]),
            ]
        );
    }

    #[test]
    fn empty_connectives_have_boolean_identity_semantics() {
        let mut truth = Formula::And(Vec::new()).into_dnf();
        assert_eq!(truth.next(), Some(Branch::default()));
        assert_eq!(truth.next(), None);
        assert_eq!(truth.next(), None);

        assert_eq!(Formula::Or(Vec::new()).into_dnf().next(), None);
        assert_eq!(Formula::And(Vec::new()).negated(), Formula::Or(Vec::new()));
        assert_eq!(Formula::Or(Vec::new()).negated(), Formula::And(Vec::new()));
    }
}
