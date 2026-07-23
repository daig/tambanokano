// M1 lands formula descent before M2-M7 consume it; keep the staged module warning-free.
#![allow(dead_code)]

use crate::dag::{DagId, DagNode};
use crate::engine::{Engine, Runtime};
use crate::root::RootGuard;
use crate::symbol::SymbolId;
use std::collections::HashMap;

/// The eight symbols attached to Maude's `TemporalSymbol` base class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TemporalHooks {
    pub true_symbol: SymbolId,
    pub false_symbol: SymbolId,
    pub not_symbol: SymbolId,
    pub next_symbol: SymbolId,
    pub and_symbol: SymbolId,
    pub or_symbol: SymbolId,
    pub until_symbol: SymbolId,
    pub release_symbol: SymbolId,
}

pub(crate) type FormulaId = usize;

/// One structurally interned formula node. Its discriminant order follows `LogicFormula::Op`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FormulaKind {
    Proposition(usize),
    True,
    False,
    Not(FormulaId),
    Next(FormulaId),
    And(FormulaId, FormulaId),
    Or(FormulaId, FormulaId),
    Until(FormulaId, FormulaId),
    Release(FormulaId, FormulaId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FormulaNode {
    pub kind: FormulaKind,
    pub propositional: bool,
}

/// Append-only, first-insertion-numbered formula DAG.
#[derive(Debug, Default)]
pub(crate) struct LogicFormula {
    nodes: Vec<FormulaNode>,
    index: HashMap<FormulaKind, FormulaId>,
}

impl LogicFormula {
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn node(&self, id: FormulaId) -> FormulaNode {
        self.nodes[id]
    }

    pub(crate) fn make_proposition(&mut self, proposition: usize) -> FormulaId {
        self.intern(FormulaKind::Proposition(proposition))
    }

    pub(crate) fn make_true(&mut self) -> FormulaId {
        self.intern(FormulaKind::True)
    }

    pub(crate) fn make_false(&mut self) -> FormulaId {
        self.intern(FormulaKind::False)
    }

    pub(crate) fn make_not(&mut self, arg: FormulaId) -> FormulaId {
        self.intern(FormulaKind::Not(arg))
    }

    pub(crate) fn make_next(&mut self, arg: FormulaId) -> FormulaId {
        self.intern(FormulaKind::Next(arg))
    }

    pub(crate) fn make_and(&mut self, lhs: FormulaId, rhs: FormulaId) -> FormulaId {
        self.intern(FormulaKind::And(lhs, rhs))
    }

    pub(crate) fn make_or(&mut self, lhs: FormulaId, rhs: FormulaId) -> FormulaId {
        self.intern(FormulaKind::Or(lhs, rhs))
    }

    pub(crate) fn make_until(&mut self, lhs: FormulaId, rhs: FormulaId) -> FormulaId {
        self.intern(FormulaKind::Until(lhs, rhs))
    }

    pub(crate) fn make_release(&mut self, lhs: FormulaId, rhs: FormulaId) -> FormulaId {
        self.intern(FormulaKind::Release(lhs, rhs))
    }

    fn intern(&mut self, kind: FormulaKind) -> FormulaId {
        if let Some(&id) = self.index.get(&kind) {
            return id;
        }
        let propositional = match kind {
            FormulaKind::Proposition(_) | FormulaKind::True | FormulaKind::False => true,
            FormulaKind::Not(arg) => self.nodes[arg].propositional,
            FormulaKind::And(lhs, rhs) | FormulaKind::Or(lhs, rhs) => {
                self.nodes[lhs].propositional && self.nodes[rhs].propositional
            }
            FormulaKind::Next(_) | FormulaKind::Until(_, _) | FormulaKind::Release(_, _) => false,
        };
        let id = self.nodes.len();
        self.nodes.push(FormulaNode {
            kind,
            propositional,
        });
        self.index.insert(kind, id);
        id
    }
}

struct RootedProposition {
    dag: DagId,
    _root: RootGuard,
}

/// A formula plus its root node and first-encounter-ordered, GC-pinned propositions.
pub(crate) struct BuiltFormula {
    pub formula: LogicFormula,
    pub root: FormulaId,
    propositions: Vec<RootedProposition>,
}

impl BuiltFormula {
    pub(crate) fn propositions_len(&self) -> usize {
        self.propositions.len()
    }

    pub(crate) fn proposition(&self, index: usize) -> DagId {
        self.propositions[index].dag
    }
}

/// Minimal read-only DAG operations needed by temporal descent. Both implementations are statically
/// dispatched; this lets M1 tests use `Engine` and later kernel hooks use the active `Runtime`.
pub(crate) trait FormulaDag {
    fn formula_node(&self, id: DagId) -> &DagNode;
    fn formula_hash(&self, id: DagId) -> u64;
    fn formula_equal(&self, lhs: DagId, rhs: DagId) -> bool;
    fn formula_root(&self, id: DagId) -> RootGuard;
}

impl FormulaDag for Engine {
    fn formula_node(&self, id: DagId) -> &DagNode {
        self.node(id)
    }

    fn formula_hash(&self, id: DagId) -> u64 {
        self.dag_hash(id)
    }

    fn formula_equal(&self, lhs: DagId, rhs: DagId) -> bool {
        self.deep_equal(lhs, rhs)
    }

    fn formula_root(&self, id: DagId) -> RootGuard {
        self.root(id)
    }
}

impl FormulaDag for Runtime {
    fn formula_node(&self, id: DagId) -> &DagNode {
        self.node(id)
    }

    fn formula_hash(&self, id: DagId) -> u64 {
        self.dag_hash(id)
    }

    fn formula_equal(&self, lhs: DagId, rhs: DagId) -> bool {
        self.deep_equal(lhs, rhs)
    }

    fn formula_root(&self, id: DagId) -> RootGuard {
        self.root(id)
    }
}

struct Builder<'a, D> {
    dag: &'a D,
    hooks: &'a TemporalHooks,
    formula: LogicFormula,
    propositions: Vec<RootedProposition>,
    proposition_buckets: HashMap<u64, Vec<usize>>,
}

impl<D: FormulaDag> Builder<'_, D> {
    fn descend(&mut self, dag: DagId) -> Option<FormulaId> {
        let node = self.dag.formula_node(dag);
        let symbol = node.symbol();

        if symbol == self.hooks.true_symbol || symbol == self.hooks.false_symbol {
            if node.children().next().is_some() {
                return None;
            }
            return Some(if symbol == self.hooks.true_symbol {
                self.formula.make_true()
            } else {
                self.formula.make_false()
            });
        }

        if symbol == self.hooks.not_symbol || symbol == self.hooks.next_symbol {
            let mut children = node.children();
            let arg = children.next()?;
            if children.next().is_some() {
                return None;
            }
            let arg = self.descend(arg)?;
            if symbol == self.hooks.not_symbol {
                if !matches!(self.formula.node(arg).kind, FormulaKind::Proposition(_)) {
                    return None;
                }
                return Some(self.formula.make_not(arg));
            }
            return Some(self.formula.make_next(arg));
        }

        if symbol == self.hooks.and_symbol || symbol == self.hooks.or_symbol {
            let mut children = node.children();
            let first = children.next()?;
            let second = children.next()?;
            let mut result = self.descend(first)?;
            let second = self.descend(second)?;
            result = if symbol == self.hooks.and_symbol {
                self.formula.make_and(result, second)
            } else {
                self.formula.make_or(result, second)
            };
            for child in children {
                let child = self.descend(child)?;
                result = if symbol == self.hooks.and_symbol {
                    self.formula.make_and(result, child)
                } else {
                    self.formula.make_or(result, child)
                };
            }
            return Some(result);
        }

        if symbol == self.hooks.until_symbol || symbol == self.hooks.release_symbol {
            let mut children = node.children();
            let lhs = children.next()?;
            let rhs = children.next()?;
            if children.next().is_some() {
                return None;
            }
            let lhs = self.descend(lhs)?;
            let rhs = self.descend(rhs)?;
            return Some(if symbol == self.hooks.until_symbol {
                self.formula.make_until(lhs, rhs)
            } else {
                self.formula.make_release(lhs, rhs)
            });
        }

        Some(self.make_proposition(dag))
    }

    fn make_proposition(&mut self, dag: DagId) -> FormulaId {
        let hash = self.dag.formula_hash(dag);
        if let Some(indices) = self.proposition_buckets.get(&hash) {
            for &index in indices {
                if self.dag.formula_equal(self.propositions[index].dag, dag) {
                    return self.formula.make_proposition(index);
                }
            }
        }

        let index = self.propositions.len();
        self.propositions.push(RootedProposition {
            dag,
            _root: self.dag.formula_root(dag),
        });
        self.proposition_buckets
            .entry(hash)
            .or_default()
            .push(index);
        self.formula.make_proposition(index)
    }
}

pub(crate) fn build_formula<D: FormulaDag>(
    dag: &D,
    hooks: &TemporalHooks,
    root: DagId,
) -> Option<BuiltFormula> {
    let mut builder = Builder {
        dag,
        hooks,
        formula: LogicFormula::default(),
        propositions: Vec::new(),
        proposition_buckets: HashMap::new(),
    };
    let root = builder.descend(root)?;
    Some(BuiltFormula {
        formula: builder.formula,
        root,
        propositions: builder.propositions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::SortId;

    struct TestSymbols {
        sort: SortId,
        hooks: TemporalHooks,
        p: SymbolId,
        q: SymbolId,
        atom: SymbolId,
    }

    fn setup() -> (Engine, TestSymbols) {
        let mut engine = Engine::new();
        let sort = engine.add_sort("Formula");
        engine.close_sorts();
        let true_symbol = engine.add_op("True", vec![], sort);
        let false_symbol = engine.add_op("False", vec![], sort);
        let not_symbol = engine.add_op("~", vec![sort], sort);
        let next_symbol = engine.add_op("O", vec![sort], sort);
        let and_symbol = engine.add_op_au("and", vec![sort, sort], sort, None);
        let or_symbol = engine.add_op_au("or", vec![sort, sort], sort, None);
        let until_symbol = engine.add_op("U", vec![sort, sort], sort);
        let release_symbol = engine.add_op("R", vec![sort, sort], sort);
        let p = engine.add_op("p", vec![], sort);
        let q = engine.add_op("q", vec![], sort);
        let atom = engine.add_op("atom", vec![sort], sort);
        (
            engine,
            TestSymbols {
                sort,
                hooks: TemporalHooks {
                    true_symbol,
                    false_symbol,
                    not_symbol,
                    next_symbol,
                    and_symbol,
                    or_symbol,
                    until_symbol,
                    release_symbol,
                },
                p,
                q,
                atom,
            },
        )
    }

    #[test]
    fn structural_propositions_collapse_in_first_encounter_order() {
        let (mut engine, symbols) = setup();
        let p1_leaf = engine.make_const(symbols.p);
        let p1 = engine.make_free(symbols.atom, vec![p1_leaf]);
        let p2_leaf = engine.make_const(symbols.p);
        let p2 = engine.make_free(symbols.atom, vec![p2_leaf]);
        assert_ne!(p1, p2);
        assert!(engine.deep_equal(p1, p2));
        let q = engine.make_const(symbols.q);
        let root = engine.make_au(symbols.hooks.and_symbol, vec![p1, p2, q]);

        let built = build_formula(&engine, &symbols.hooks, root).unwrap();
        assert_eq!(built.propositions_len(), 2);
        assert!(engine.deep_equal(built.proposition(0), p1));
        assert_eq!(built.proposition(1), q);
        assert_eq!(built.formula.len(), 4);
        assert_eq!(built.formula.node(0).kind, FormulaKind::Proposition(0));
        assert_eq!(built.formula.node(1).kind, FormulaKind::And(0, 0));
        assert_eq!(built.formula.node(2).kind, FormulaKind::Proposition(1));
        assert_eq!(built.formula.node(3).kind, FormulaKind::And(1, 2));
        assert!(built.formula.node(1).propositional);
        assert!(built.formula.node(3).propositional);
        assert_eq!(built.root, 3);
    }

    #[test]
    fn repeated_formula_nodes_share_and_nary_ops_fold_left() {
        let (mut engine, symbols) = setup();
        let p = engine.make_const(symbols.p);
        let q = engine.make_const(symbols.q);
        let conjunction1 = engine.make_au(symbols.hooks.and_symbol, vec![p, q]);
        let conjunction2 = engine.make_au(symbols.hooks.and_symbol, vec![p, q]);
        let root = engine.make_au(symbols.hooks.or_symbol, vec![conjunction1, conjunction2, p]);

        let built = build_formula(&engine, &symbols.hooks, root).unwrap();
        assert_eq!(built.formula.node(0).kind, FormulaKind::Proposition(0));
        assert_eq!(built.formula.node(1).kind, FormulaKind::Proposition(1));
        assert_eq!(built.formula.node(2).kind, FormulaKind::And(0, 1));
        assert_eq!(built.formula.node(3).kind, FormulaKind::Or(2, 2));
        assert_eq!(built.formula.node(4).kind, FormulaKind::Or(3, 0));
        assert!(built.formula.node(4).propositional);
        assert_eq!(built.root, 4);
    }

    #[test]
    fn flags_match_logic_formula_and_not_accepts_only_atomic_propositions() {
        let (mut engine, symbols) = setup();
        let p = engine.make_const(symbols.p);
        let q = engine.make_const(symbols.q);
        let not_p = engine.make_free(symbols.hooks.not_symbol, vec![p]);
        let next_q = engine.make_free(symbols.hooks.next_symbol, vec![q]);
        let root = engine.make_au(symbols.hooks.or_symbol, vec![not_p, next_q]);
        let built = build_formula(&engine, &symbols.hooks, root).unwrap();

        assert!(built.formula.node(0).propositional); // p
        assert!(built.formula.node(1).propositional); // ~p
        assert!(built.formula.node(2).propositional); // q
        assert!(!built.formula.node(3).propositional); // O q
        assert!(!built.formula.node(built.root).propositional); // ~p \/ O q

        let true_dag = engine.make_const(symbols.hooks.true_symbol);
        let invalid_not = engine.make_free(symbols.hooks.not_symbol, vec![true_dag]);
        assert!(build_formula(&engine, &symbols.hooks, invalid_not).is_none());
    }

    #[test]
    fn temporal_binary_ops_and_constants_have_reference_flags() {
        let (mut engine, symbols) = setup();
        let true_dag = engine.make_const(symbols.hooks.true_symbol);
        let false_dag = engine.make_const(symbols.hooks.false_symbol);
        let true_formula = build_formula(&engine, &symbols.hooks, true_dag).unwrap();
        let false_formula = build_formula(&engine, &symbols.hooks, false_dag).unwrap();
        assert_eq!(
            true_formula.formula.node(true_formula.root).kind,
            FormulaKind::True
        );
        assert!(true_formula.formula.node(true_formula.root).propositional);
        assert_eq!(
            false_formula.formula.node(false_formula.root).kind,
            FormulaKind::False
        );
        assert!(false_formula.formula.node(false_formula.root).propositional);

        let p = engine.make_const(symbols.p);
        let q = engine.make_const(symbols.q);
        for (symbol, expected) in [
            (symbols.hooks.until_symbol, FormulaKind::Until(0, 1)),
            (symbols.hooks.release_symbol, FormulaKind::Release(0, 1)),
        ] {
            let dag = engine.make_free(symbol, vec![p, q]);
            let built = build_formula(&engine, &symbols.hooks, dag).unwrap();
            assert_eq!(built.formula.node(built.root).kind, expected);
            assert!(!built.formula.node(built.root).propositional);
        }
    }

    #[test]
    fn unknown_top_is_one_atomic_proposition_and_pins_its_subtree() {
        let (mut engine, symbols) = setup();
        let p = engine.make_const(symbols.p);
        let next_p = engine.make_free(symbols.hooks.next_symbol, vec![p]);
        let unknown = engine.make_free(symbols.atom, vec![next_p]);
        let built = build_formula(&engine, &symbols.hooks, unknown).unwrap();
        assert_eq!(built.formula.len(), 1);
        assert_eq!(
            built.formula.node(built.root).kind,
            FormulaKind::Proposition(0)
        );
        assert_eq!(built.propositions_len(), 1);
        assert_eq!(built.proposition(0), unknown);

        engine.gc([]);
        assert_eq!(engine.node(built.proposition(0)).symbol(), symbols.atom);
    }

    #[test]
    fn malformed_recognized_operators_are_rejected() {
        let (mut engine, symbols) = setup();
        let p = engine.make_const(symbols.p);
        let unary = engine.add_op("unary", vec![symbols.sort], symbols.sort);
        let unary_dag = engine.make_free(unary, vec![p]);
        let constant = engine.add_op("constant", vec![], symbols.sort);
        let constant_dag = engine.make_const(constant);

        let mut hooks = symbols.hooks;
        hooks.until_symbol = unary;
        assert!(build_formula(&engine, &hooks, unary_dag).is_none());

        hooks = symbols.hooks;
        hooks.not_symbol = constant;
        assert!(build_formula(&engine, &hooks, constant_dag).is_none());

        hooks = symbols.hooks;
        hooks.and_symbol = unary;
        assert!(build_formula(&engine, &hooks, unary_dag).is_none());
    }
}
