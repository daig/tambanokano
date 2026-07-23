// M2 lands the BDD facade before M3-M7 consume it; keep the staged module warning-free.
#![allow(dead_code)]

use biodivine_lib_bdd::{Bdd as RawBdd, BddPointer, BddVariable, BddVariableSet};

/// Engine-local BDD variable context. Variable `i` is proposition `i` throughout Phase M.
pub(crate) struct BddContext {
    variables: BddVariableSet,
}

/// A canonical Boolean function whose backend representation stays inside this module.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Bdd {
    raw: RawBdd,
}

/// An opaque cursor into one [`Bdd`]. The biodivine pointer type never crosses the facade.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BddNode {
    raw: BddPointer,
}

impl BddContext {
    pub(crate) fn new(variable_count: usize) -> Self {
        let variable_count = u16::try_from(variable_count).expect("too many LTL propositions");
        assert!(
            variable_count < u16::MAX - 1,
            "too many LTL propositions"
        );
        Self {
            variables: BddVariableSet::new_anonymous(variable_count),
        }
    }

    pub(crate) fn variable_count(&self) -> usize {
        self.variables.num_vars() as usize
    }

    pub(crate) fn true_bdd(&self) -> Bdd {
        Bdd {
            raw: self.variables.mk_true(),
        }
    }

    pub(crate) fn false_bdd(&self) -> Bdd {
        Bdd {
            raw: self.variables.mk_false(),
        }
    }

    pub(crate) fn ithvar(&self, variable: usize) -> Bdd {
        Bdd {
            raw: self.variables.mk_var(self.variable(variable)),
        }
    }

    pub(crate) fn nithvar(&self, variable: usize) -> Bdd {
        Bdd {
            raw: self.variables.mk_not_var(self.variable(variable)),
        }
    }

    pub(crate) fn not(&self, value: &Bdd) -> Bdd {
        self.assert_context(value);
        Bdd {
            raw: value.raw.not(),
        }
    }

    pub(crate) fn and(&self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        self.assert_pair(lhs, rhs);
        Bdd {
            raw: lhs.raw.and(&rhs.raw),
        }
    }

    pub(crate) fn or(&self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        self.assert_pair(lhs, rhs);
        Bdd {
            raw: lhs.raw.or(&rhs.raw),
        }
    }

    pub(crate) fn implies(&self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        self.assert_pair(lhs, rhs);
        Bdd {
            raw: lhs.raw.imp(&rhs.raw),
        }
    }

    pub(crate) fn equivalent(&self, lhs: &Bdd, rhs: &Bdd) -> bool {
        self.assert_pair(lhs, rhs);
        lhs == rhs
    }

    fn variable(&self, index: usize) -> BddVariable {
        assert!(index < self.variable_count(), "BDD variable out of range");
        BddVariable::from_index(index)
    }

    fn assert_context(&self, value: &Bdd) {
        assert_eq!(
            value.raw.num_vars(),
            self.variables.num_vars(),
            "BDD belongs to a different variable context"
        );
    }

    fn assert_pair(&self, lhs: &Bdd, rhs: &Bdd) {
        self.assert_context(lhs);
        self.assert_context(rhs);
    }
}

impl Bdd {
    pub(crate) fn is_true(&self) -> bool {
        self.raw.is_true()
    }

    pub(crate) fn is_false(&self) -> bool {
        self.raw.is_false()
    }

    pub(crate) fn root(&self) -> BddNode {
        BddNode {
            raw: self.raw.root_pointer(),
        }
    }

    pub(crate) fn is_zero(&self, node: BddNode) -> bool {
        node.raw.is_zero()
    }

    pub(crate) fn is_one(&self, node: BddNode) -> bool {
        node.raw.is_one()
    }

    pub(crate) fn variable(&self, node: BddNode) -> Option<usize> {
        (!node.raw.is_zero() && !node.raw.is_one())
            .then(|| self.raw.var_of(node.raw).to_index())
    }

    pub(crate) fn low(&self, node: BddNode) -> Option<BddNode> {
        self.variable(node).map(|_| BddNode {
            raw: self.raw.low_link_of(node.raw),
        })
    }

    pub(crate) fn high(&self, node: BddNode) -> Option<BddNode> {
        self.variable(node).map(|_| BddNode {
            raw: self.raw.high_link_of(node.raw),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_variable_constants_and_terminal_navigation() {
        let context = BddContext::new(0);
        let t = context.true_bdd();
        let f = context.false_bdd();
        assert_eq!(context.variable_count(), 0);
        assert!(t.is_true());
        assert!(f.is_false());
        assert!(t.is_one(t.root()));
        assert!(f.is_zero(f.root()));
        assert_eq!(t.variable(t.root()), None);
        assert_eq!(f.low(f.root()), None);
        assert_eq!(f.high(f.root()), None);
    }

    #[test]
    fn literals_preserve_variable_and_polarity() {
        let context = BddContext::new(3);
        let positive = context.ithvar(1);
        let negative = context.nithvar(1);

        assert_eq!(positive.variable(positive.root()), Some(1));
        assert!(positive.is_zero(positive.low(positive.root()).unwrap()));
        assert!(positive.is_one(positive.high(positive.root()).unwrap()));
        assert_eq!(negative.variable(negative.root()), Some(1));
        assert!(negative.is_one(negative.low(negative.root()).unwrap()));
        assert!(negative.is_zero(negative.high(negative.root()).unwrap()));

        let direct = BddVariableSet::new_anonymous(3);
        assert_eq!(positive.raw, direct.mk_var(BddVariable::from_index(1)));
        assert_eq!(negative.raw, direct.mk_not_var(BddVariable::from_index(1)));
    }

    #[test]
    fn boolean_ops_match_backend_truth_tables_and_canonicity() {
        let context = BddContext::new(2);
        let x = context.ithvar(0);
        let y = context.ithvar(1);
        let not_x = context.not(&x);
        let lhs = context.not(&context.and(&x, &y));
        let rhs = context.or(&not_x, &context.not(&y));
        assert!(context.equivalent(&lhs, &rhs), "De Morgan must be canonical");

        let direct = BddVariableSet::new_anonymous(2);
        let direct_x = direct.mk_var(BddVariable::from_index(0));
        let direct_y = direct.mk_var(BddVariable::from_index(1));
        assert_eq!(context.and(&x, &y).raw, direct_x.and(&direct_y));
        assert_eq!(context.or(&x, &y).raw, direct_x.or(&direct_y));
        assert_eq!(not_x.raw, direct_x.not());
        assert_eq!(context.implies(&x, &y).raw, direct_x.imp(&direct_y));

        assert!(context.and(&x, &context.not(&x)).is_false());
        assert!(context.or(&x, &context.not(&x)).is_true());
        assert!(context.implies(&x, &x).is_true());
        assert!(!context.equivalent(&x, &y));
    }

    #[test]
    fn multi_level_navigation_matches_backend_links() {
        let context = BddContext::new(3);
        let x0 = context.ithvar(0);
        let x1 = context.ithvar(1);
        let nx2 = context.nithvar(2);
        let formula = context.and(&x0, &context.or(&x1, &nx2));

        let root = formula.root();
        assert_eq!(formula.variable(root), Some(0));
        assert!(formula.is_zero(formula.low(root).unwrap()));
        let at_one = formula.high(root).unwrap();
        assert_eq!(formula.variable(at_one), Some(1));
        assert!(formula.is_one(formula.high(at_one).unwrap()));
        let at_two = formula.low(at_one).unwrap();
        assert_eq!(formula.variable(at_two), Some(2));
        assert!(formula.is_one(formula.low(at_two).unwrap()));
        assert!(formula.is_zero(formula.high(at_two).unwrap()));

        let direct_root = formula.raw.root_pointer();
        assert_eq!(root.raw, direct_root);
        assert_eq!(
            formula.low(root).unwrap().raw,
            formula.raw.low_link_of(direct_root)
        );
        assert_eq!(
            formula.high(root).unwrap().raw,
            formula.raw.high_link_of(direct_root)
        );
    }
}
