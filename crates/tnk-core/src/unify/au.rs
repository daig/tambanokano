//! Associative / associative-with-identity unification — Maude's
//! `AU_UnificationSubproblem2`. The DAG-facing bridge abstracts ordered AU arguments into a pure
//! [`WordSystem`], then materializes each word solution without changing its enumeration order.

use super::word::{INCOMPLETE, SUCCESS, Word, WordSystem};
use super::{
    Marker, PendingStack, SavedSubst, UnifyContext, UnifyEnv, compute_solved_form, is_ground,
    last_variable_in_chain, var_index,
};
use crate::dag::{DagId, NodeTerm};
use crate::diophantine::UNBOUNDED;
use crate::engine::Engine;
use crate::sort::{KindId, SortId};
use crate::symbol::SymbolId;
use crate::term::Term;
use std::collections::BTreeSet;

struct Assignment {
    variable: usize,
    value: Word,
}

struct Unification {
    lhs: Word,
    rhs: Word,
}

pub(crate) struct AuSubproblem {
    top: SymbolId,
    subterms: Vec<DagId>,
    assignments: Vec<Assignment>,
    unifications: Vec<Unification>,
    null_equations: Vec<Word>,
    marked_subterms: BTreeSet<usize>,
    word_system: Option<WordSystem>,
    fresh_variables: Vec<Option<DagId>>,
    pre_solve: SavedSubst,
    saved_subst: SavedSubst,
    saved_pending: Marker,
}

impl AuSubproblem {
    pub(crate) fn new(top: SymbolId) -> Self {
        Self {
            top,
            subterms: Vec::new(),
            assignments: Vec::new(),
            unifications: Vec::new(),
            null_equations: Vec::new(),
            marked_subterms: BTreeSet::new(),
            word_system: None,
            fresh_variables: Vec::new(),
            pre_solve: Vec::new(),
            saved_subst: Vec::new(),
            saved_pending: 0,
        }
    }

    pub(crate) fn gc_roots(&self) -> Vec<DagId> {
        self.subterms
            .iter()
            .copied()
            .chain(self.fresh_variables.iter().copied().flatten())
            .chain(self.pre_solve.iter().copied().flatten())
            .chain(self.saved_subst.iter().copied().flatten())
            .collect()
    }

    fn is_identity(&self, e: &Engine, dag: DagId) -> bool {
        e.symbol(self.top)
            .identity()
            .is_some_and(|id| e.is_identity(id, dag))
    }

    /// Replace a variable by the last variable in its binding chain, but do not eagerly substitute
    /// an in-theory binding. An identity-bound representative vanishes from the abstract word.
    fn dag_to_abstract(&mut self, e: &Engine, ctx: &UnifyContext, mut dag: DagId) -> Option<usize> {
        if var_index(e, dag).is_some() {
            let representative = last_variable_in_chain(e, ctx, dag);
            if e.symbol(self.top).identity().is_some()
                && let Some(subject) = ctx.value(var_index(e, representative).unwrap() as usize)
                && self.is_identity(e, subject)
            {
                return None;
            }
            dag = representative;
        }
        if let Some(index) = self.subterms.iter().position(|&d| e.deep_equal(dag, d)) {
            return Some(index);
        }
        let index = self.subterms.len();
        self.subterms.push(dag);
        Some(index)
    }

    /// Abstract a flattened AU node in its stored left-to-right argument order.
    fn assoc_to_abstract(&mut self, e: &Engine, ctx: &UnifyContext, dag: DagId) -> Word {
        let args = match &e.node(dag).term {
            NodeTerm::Au { symbol, args } => {
                debug_assert_eq!(*symbol, self.top);
                args.clone()
            }
            _ => unreachable!("assoc_to_abstract on a non-AU node"),
        };
        let mut word = Vec::with_capacity(args.len());
        for arg in args {
            if let Some(index) = self.dag_to_abstract(e, ctx, arg) {
                word.push(index);
            }
        }
        word
    }

    pub(crate) fn add_unification(
        &mut self,
        e: &Engine,
        ctx: &UnifyContext,
        lhs: DagId,
        rhs: DagId,
        marked: bool,
    ) {
        debug_assert_eq!(e.node(lhs).symbol(), self.top);
        debug_assert!(
            e.symbol(self.top).identity().is_some()
                || e.node(rhs).symbol() == self.top
                || var_index(e, rhs).is_some()
        );
        debug_assert!(e.symbol(self.top).identity().is_some() || !marked);

        // Abstract the lhs first. This is load-bearing: first-encounter indices determine the word
        // solver's original-variable order and therefore fresh-variable creation and enumeration.
        let lhs_abstract = self.assoc_to_abstract(e, ctx, lhs);
        if e.node(rhs).symbol() == self.top {
            let rhs_abstract = self.assoc_to_abstract(e, ctx, rhs);
            match (lhs_abstract.is_empty(), rhs_abstract.is_empty()) {
                (true, true) => {}
                (true, false) => self.null_equations.push(rhs_abstract),
                (false, true) => self.null_equations.push(lhs_abstract),
                (false, false) => self.unifications.push(Unification {
                    lhs: lhs_abstract,
                    rhs: rhs_abstract,
                }),
            }
            return;
        }

        let rhs_index = if self.is_identity(e, rhs) {
            None
        } else {
            self.dag_to_abstract(e, ctx, rhs)
        };
        if lhs_abstract.is_empty() {
            if let Some(index) = rhs_index {
                self.null_equations.push(vec![index]);
            }
        } else if let Some(index) = rhs_index {
            self.assignments.push(Assignment {
                variable: index,
                value: lhs_abstract,
            });
            if marked {
                self.marked_subterms.insert(index);
            }
        } else {
            self.null_equations.push(lhs_abstract);
        }
    }

    fn make_word_system(&mut self, e: &Engine, ctx: &UnifyContext) {
        let identity_optimizations = e.symbol(self.top).identity().is_some()
            && !unequal_identity_collapse(e, self.top, true)
            && !unequal_identity_collapse(e, self.top, false);
        let mut system = WordSystem::new(
            self.subterms.len(),
            self.unifications.len(),
            identity_optimizations,
        );
        let identity_symbol = identity_top_symbol(e, self.top);
        let sort_bounds = e.signature().acu_sort_bounds(self.top);

        for (i, &subterm) in self.subterms.iter().enumerate() {
            if let Some(index) = var_index(e, subterm) {
                let sort = e.sort_of(subterm);
                if let Some(value) = ctx.value(index as usize) {
                    let symbol = e.node(value).symbol();
                    if is_ground(e, value) {
                        system.set_theory_constraint(i, symbol.index());
                        continue;
                    }
                    if super::acu::is_stable(e, symbol) {
                        system.set_theory_constraint(i, symbol.index());
                        if identity_symbol == Some(symbol)
                            && e.signature().acu_take_identity(self.top, sort)
                        {
                            system.set_take_empty(i);
                        }
                        continue;
                    }
                }

                if self.marked_subterms.contains(&i) {
                    system.set_upper_bound(i, 1);
                } else if let Some(&bound) = sort_bounds.get(&sort)
                    && bound != UNBOUNDED
                {
                    system.set_upper_bound(i, bound as usize);
                }
                if e.symbol(self.top).identity().is_some()
                    && e.signature().acu_take_identity(self.top, sort)
                {
                    system.set_take_empty(i);
                }
                continue;
            }

            let symbol = e.node(subterm).symbol();
            if is_ground(e, subterm) {
                system.set_theory_constraint(i, symbol.index());
                continue;
            }
            if super::acu::is_stable(e, symbol) {
                system.set_theory_constraint(i, symbol.index());
                if identity_symbol == Some(symbol) {
                    system.set_take_empty(i);
                }
                continue;
            }
            if self.marked_subterms.contains(&i) {
                system.set_upper_bound(i, 1);
            }
            if e.symbol(self.top).identity().is_some() {
                system.set_take_empty(i);
            }
        }

        for word in &self.null_equations {
            system.add_null_equation(word.clone());
        }
        for assignment in &self.assignments {
            system.add_assignment(assignment.variable, assignment.value.clone());
        }
        for (index, unification) in self.unifications.iter().enumerate() {
            system.add_equation(index, unification.lhs.clone(), unification.rhs.clone());
        }
        self.word_system = Some(system);
    }

    /// Turn an existing solved form `X |-> f(...)` back into an abstract assignment so every
    /// decision in this theory is solved simultaneously.
    fn unsolve(&mut self, e: &Engine, ctx: &mut UnifyContext, index: usize) {
        let variable = ctx
            .variable_node(index)
            .expect("in-theory binding has no tracked variable");
        let value = ctx.value(index).expect("unsolving an unbound variable");
        ctx.bind(index, None);
        let variable = self
            .dag_to_abstract(e, ctx, variable)
            .expect("an unbound variable cannot abstract to identity");
        let value = self.assoc_to_abstract(e, ctx, value);
        self.assignments.push(Assignment { variable, value });
    }

    pub(crate) fn solve(
        &mut self,
        env: &mut UnifyEnv,
        find_first: bool,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        if find_first {
            self.pre_solve = ctx.clone_subst();
            let slots = ctx.n_slots();
            for index in 0..slots {
                if let Some(value) = ctx.value(index)
                    && env.e.node(value).symbol() == self.top
                {
                    self.unsolve(env.e, ctx, index);
                }
            }
            self.make_word_system(env.e, ctx);
            self.saved_subst = ctx.clone_subst();
            self.saved_pending = pending.checkpoint();
        } else {
            pending.restore(self.saved_pending);
            ctx.restore_from_clone(&self.saved_subst);
        }

        loop {
            let result = self
                .word_system
                .as_mut()
                .expect("AU word system not initialized")
                .find_next_solution();
            if result & INCOMPLETE != 0 {
                pending.flag_as_incomplete(self.top);
            }
            if result & SUCCESS == 0 {
                break;
            }
            if self.build_solution(env, ctx, pending) {
                return true;
            }
            pending.restore(self.saved_pending);
            ctx.restore_from_clone(&self.saved_subst);
        }
        ctx.restore_from_clone(&self.pre_solve);
        false
    }

    fn build_solution(
        &mut self,
        env: &mut UnifyEnv,
        ctx: &mut UnifyContext,
        pending: &mut PendingStack,
    ) -> bool {
        let kind = env.e.sorts().kind_of(range_sort(env.e, self.top));
        let word_system = self
            .word_system
            .as_ref()
            .expect("AU word system not initialized");
        self.fresh_variables.clear();
        self.fresh_variables
            .resize(word_system.nr_variables(), None);

        let mut reused = BTreeSet::new();
        for (i, &subterm) in self.subterms.iter().enumerate() {
            let value = word_system.assignment(i);
            if value.len() == 1 && var_index(env.e, subterm).is_some() {
                let abstract_variable = value[0];
                if self.fresh_variables[abstract_variable].is_none() {
                    self.fresh_variables[abstract_variable] = Some(subterm);
                    reused.insert(i);
                }
            }
        }

        for (i, &subterm) in self.subterms.iter().enumerate() {
            if reused.contains(&i) {
                continue;
            }
            let value = word_system.assignment(i);
            let (dag, in_theory) = match value {
                [] => (identity_dag(env.e, self.top), true),
                [abstract_variable] => (
                    abstract_to_fresh_variable(
                        &mut self.fresh_variables,
                        *abstract_variable,
                        env,
                        ctx,
                        kind,
                    ),
                    false,
                ),
                _ => {
                    let mut args = Vec::with_capacity(value.len());
                    for &abstract_variable in value {
                        args.push(abstract_to_fresh_variable(
                            &mut self.fresh_variables,
                            abstract_variable,
                            env,
                            ctx,
                            kind,
                        ));
                    }
                    (env.e.make_au(self.top, args), true)
                }
            };

            if var_index(env.e, subterm).is_some() {
                let representative = last_variable_in_chain(env.e, ctx, subterm);
                if ctx
                    .value(var_index(env.e, representative).unwrap() as usize)
                    .is_none()
                    && in_theory
                {
                    ctx.unification_bind(env.e, representative, dag);
                    continue;
                }
            }
            if !compute_solved_form(env, subterm, dag, ctx, pending) {
                return false;
            }
        }
        true
    }
}

fn abstract_to_fresh_variable(
    fresh_variables: &mut [Option<DagId>],
    index: usize,
    env: &mut UnifyEnv,
    ctx: &mut UnifyContext,
    kind: KindId,
) -> DagId {
    if let Some(dag) = fresh_variables[index] {
        dag
    } else {
        let dag = ctx.make_fresh_variable(env, kind);
        fresh_variables[index] = Some(dag);
        dag
    }
}

fn range_sort(e: &Engine, symbol: SymbolId) -> SortId {
    e.symbol(symbol).decls()[0].range
}

fn identity_dag(e: &mut Engine, symbol: SymbolId) -> DagId {
    let identity = e
        .symbol(symbol)
        .identity()
        .expect("empty A-word without an identity");
    e.make_identity(identity)
}

fn identity_top_symbol(e: &Engine, symbol: SymbolId) -> Option<SymbolId> {
    let identity = e.symbol(symbol).identity()?;
    Some(match e.signature().identity_term(identity) {
        Term::Var(_) => unreachable!("an identity term must be ground"),
        Term::Na { symbol, .. } | Term::Op { symbol, .. } | Term::Iter { symbol, .. } => *symbol,
    })
}

/// `BinarySymbol::hasUnequal{Left,Right}IdentityCollapse`: whether collapsing the identity on the
/// selected side can change the other argument's sort.
fn unequal_identity_collapse(e: &Engine, symbol: SymbolId, identity_on_left: bool) -> bool {
    let Some(identity) = e.symbol(symbol).identity() else {
        return false;
    };
    let signature = e.signature();
    let identity_sort = signature.identity_sort(identity);
    let kind = signature.sorts().kind_of(range_sort(e, symbol));
    signature
        .sorts()
        .kind(kind)
        .members
        .iter()
        .copied()
        .any(|sort| {
            let args = if identity_on_left {
                [identity_sort, sort]
            } else {
                [sort, identity_sort]
            };
            signature.compute_sort(symbol, &args) != sort
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fresh::VariableFamily;
    use crate::unify::NameCodes;
    use std::collections::HashMap;

    #[derive(Default)]
    struct TestNames {
        codes: HashMap<String, u32>,
    }

    impl NameCodes for TestNames {
        fn code(&mut self, name: &str) -> u32 {
            if let Some(&code) = self.codes.get(name) {
                code
            } else {
                let code = self.codes.len() as u32;
                self.codes.insert(name.to_owned(), code);
                code
            }
        }
    }

    fn solve_all(
        env: &mut UnifyEnv,
        nr_original: usize,
        lhs: DagId,
        rhs: DagId,
    ) -> Vec<Vec<Option<DagId>>> {
        let mut ctx = UnifyContext::new(nr_original, VariableFamily::Unify);
        let mut pending = PendingStack::new();
        assert!(compute_solved_form(env, lhs, rhs, &mut ctx, &mut pending));
        let mut result = Vec::new();
        let mut first = true;
        while pending.solve(env, first, &mut ctx) {
            result.push((0..nr_original).map(|i| ctx.value(i)).collect());
            first = false;
        }
        result
    }

    fn variable(env: &mut UnifyEnv, name: &str, sort: SortId, index: u32) -> DagId {
        let code = env.names.code(name);
        env.e.make_var(sort, code, index)
    }

    #[test]
    fn assoc_abstraction_preserves_argument_order_and_lhs_first_indices() {
        let mut e = Engine::new();
        let sort = e.add_sort("S");
        e.close_sorts();
        let f = e.add_op_au("f", vec![sort, sort], sort, None);
        let x = e.make_var(sort, 10, 0);
        let y = e.make_var(sort, 11, 1);
        let z = e.make_var(sort, 12, 2);
        let lhs = e.make_au(f, vec![x, y]);
        let rhs = e.make_au(f, vec![z, x]);
        let ctx = UnifyContext::new(3, crate::fresh::VariableFamily::Unify);
        let mut problem = AuSubproblem::new(f);

        problem.add_unification(&e, &ctx, lhs, rhs, false);

        assert_eq!(problem.subterms, [x, y, z]);
        assert_eq!(problem.unifications.len(), 1);
        assert_eq!(problem.unifications[0].lhs, [0, 1]);
        assert_eq!(problem.unifications[0].rhs, [2, 0]);
    }

    #[test]
    fn identity_bound_arguments_are_eliminated_during_abstraction() {
        let mut e = Engine::new();
        let sort = e.add_sort("S");
        e.close_sorts();
        let nil = e.add_op("nil", vec![], sort);
        let f = e.add_op_au("f", vec![sort, sort], sort, Some(nil));
        let x = e.make_var(sort, 10, 0);
        let y = e.make_var(sort, 11, 1);
        let term = e.make_au(f, vec![x, y]);
        let mut ctx = UnifyContext::new(2, crate::fresh::VariableFamily::Unify);
        ctx.bind(0, Some(e.make_const(nil)));
        let mut problem = AuSubproblem::new(f);

        assert_eq!(problem.assoc_to_abstract(&e, &ctx, term), [0]);
        assert_eq!(problem.subterms, [y]);
    }

    #[test]
    fn strict_left_linear_a_enumerates_delannoy_order() {
        let mut e = Engine::new();
        let sort = e.add_sort("List");
        e.close_sorts();
        let f = e.add_op_au("__", vec![sort, sort], sort, None);
        let mut names = TestNames::default();
        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let a = variable(&mut env, "A", sort, 0);
        let b = variable(&mut env, "B", sort, 1);
        let x = variable(&mut env, "X", sort, 2);
        let y = variable(&mut env, "Y", sort, 3);
        let lhs = env.e.make_au(f, vec![a, b]);
        let rhs = env.e.make_au(f, vec![x, y]);

        let forms = solve_all(&mut env, 4, lhs, rhs);

        assert_eq!(forms.len(), 3);
        let originals = [a, b, x, y];
        let lengths = forms
            .iter()
            .map(|form| {
                std::array::from_fn::<_, 4, _>(|i| {
                    let dag = form[i].unwrap_or(originals[i]);
                    match &env.e.node(dag).term {
                        NodeTerm::Au { args, .. } => args.len(),
                        _ => 1,
                    }
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(lengths, [[2, 1, 1, 2], [1, 2, 2, 1], [1, 1, 1, 1]]);
    }

    #[test]
    fn au_theory_clash_materializes_identity_in_right_to_left_order() {
        let mut e = Engine::new();
        let sort = e.add_sort("Foo");
        e.close_sorts();
        let nil = e.add_op("nil", vec![], sort);
        let h = e.add_op("h", vec![sort], sort);
        let f = e.add_op_au("__", vec![sort, sort], sort, Some(nil));
        let identity = e.make_const(nil);
        let mut names = TestNames::default();
        let mut env = UnifyEnv {
            e: &mut e,
            names: &mut names,
        };
        let x = variable(&mut env, "X", sort, 0);
        let y = variable(&mut env, "Y", sort, 1);
        let z = variable(&mut env, "Z", sort, 2);
        let lhs = env.e.make_au(f, vec![x, y]);
        let rhs = env.e.make_free(h, vec![z]);

        let forms = solve_all(&mut env, 3, lhs, rhs);

        assert_eq!(forms.len(), 2);
        let alien = env.e.make_free(h, vec![z]);
        assert!(
            env.e
                .deep_equal(forms[0][0].expect("X must be assigned"), identity)
        );
        assert!(
            env.e
                .deep_equal(forms[0][1].expect("Y must be assigned"), alien)
        );
        assert!(
            env.e
                .deep_equal(forms[1][0].expect("X must be assigned"), alien)
        );
        assert!(
            env.e
                .deep_equal(forms[1][1].expect("Y must be assigned"), identity)
        );
    }
}
