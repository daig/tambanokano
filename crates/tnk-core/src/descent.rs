//! The META-LEVEL descent seam.
//!
//! A descent function (`metaReduce`/`metaApply`/…) is a [`SpecialOp::Meta`](crate::symbol::SpecialOp)
//! that, mid-reduction, down-translates its meta-term arguments into a real object module, runs an engine
//! operation in it, and up-translates the result. Building the object module needs the whole frontend
//! pipeline (parse/flatten/build) + the module database, which live *above* `tnk-core` — but the trigger
//! is inside this crate's reduce loop. So the loop calls *up* through a trait object:
//!
//! * [`DescentOps`] is the seam, implemented by `tnk_modules::meta::MetaDescent` and used by
//!   `tnk-session`. The reduce path threads a `&mut dyn DescentOps`; `try_special` hands a `Meta` redex to it.
//! * [`MetaCtx`] is what the handler gets to read the redex's meta-terms and build the up-result *in the
//!   current engine* — a public, minimal view over the otherwise crate-private `Runtime`/`Signature`.
//!   (Building the throwaway *object* sub-module is a separate `Engine` the handler owns; it never touches
//!   `MetaCtx`.)
//!
//! [`NullDescent`] is the no-op used on every reduce path that is not a top-level descent command (so the
//! kernel and its tests need no module database): a descent redex then simply stays at the kind level.

use crate::dag::{DagId, NaValue, NodeRepr};
use crate::engine::{Runtime, Signature};
use crate::host::ReducerFault;
use crate::root::RootGuard;
use crate::smt::SmtType;
use crate::sort::SortId;
use crate::symbol::{MetaHooks, MetaOp, SpecialOp, SymbolClass, SymbolId, Theory};

/// The current engine seen by a descent handler: reading the redex's meta-term arguments and building the
/// up-translated result, both in the engine that is reducing. A thin public facade over `&mut Runtime` +
/// `&Signature` (both crate-private) exposing exactly the DAG read/build operations descent needs.
pub struct MetaCtx<'a> {
    pub(crate) rt: &'a mut Runtime,
    pub(crate) sig: &'a Signature,
}

impl MetaCtx<'_> {
    /// The top symbol of node `id`.
    pub fn top(&self, id: DagId) -> SymbolId {
        self.rt.node(id).symbol()
    }
    /// The child DAGs of node `id` (free/ACU/AU/CUI args, in canonical order; empty for a leaf).
    pub fn children(&self, id: DagId) -> Vec<DagId> {
        self.rt.node(id).children().collect()
    }
    /// The scalar-payload view of node `id` (an `App`, an `iter` `s^count`, or a string/qid/float value).
    pub fn repr(&self, id: DagId) -> NodeRepr<'_> {
        self.rt.node(id).repr()
    }
    /// The canonical (mixfix) name of symbol `sym`.
    pub fn name(&self, sym: SymbolId) -> &str {
        self.sig.symbol(sym).name()
    }
    /// Whether every declaration of `sym` is a constructor (`[ctor]`).
    pub fn is_constructor(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_constructor()
    }
    /// The least sort of node `id` (computed at construction).
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.rt.node(id).sort
    }
    /// The name of sort `s`.
    pub fn sort_name(&self, s: SortId) -> &str {
        self.sig.sorts().name(s)
    }
    /// SMT classification of a sort in the current signature.
    pub fn smt_type(&self, sort: SortId) -> Option<SmtType> {
        self.sig.smt_info().sort_type(sort)
    }
    /// Stable identity of the current engine's DAG/root domain. A descent implementation that caches
    /// `DagId`s across calls must scope those keys to this identity.
    pub fn context_id(&self) -> usize {
        self.rt.context_id()
    }

    /// Structural equality in the current meta-module engine. DAG ids from separately parsed commands
    /// need not be pointer-equal even when they denote the same reflected term.
    pub fn deep_equal(&self, lhs: DagId, rhs: DagId) -> bool {
        self.rt.deep_equal(lhs, rhs)
    }
    /// Stable structural hash paired with [`deep_equal`](Self::deep_equal). Equal DAGs hash equally;
    /// callers must still resolve collisions with `deep_equal`.
    pub fn dag_hash(&self, id: DagId) -> u64 {
        self.rt.dag_hash(id)
    }
    /// Pin a meta-term DAG while a persistent descent cache holds its id across commands.
    pub fn root(&self, id: DagId) -> crate::root::RootGuard {
        self.rt.root(id)
    }

    /// Build an atomic constant (string / quoted-id / float) for `sym`.
    pub fn make_na(&mut self, sym: SymbolId, value: NaValue) -> DagId {
        self.rt.make_na(self.sig, sym, value)
    }
    /// Record the first ascent of a synthesized quoted identifier. Complete `name:Sort` payloads are
    /// ranked lazily, so META-level AC sets compare them by ascent order.
    pub fn rank_qid(&mut self, text: &str) {
        self.rt.register_qid_rank(text);
    }
    /// Build an application of `sym` to `args`, dispatching on the operator's theory (free / ACU / AU /
    /// CUI canonicalization) — the up-result's `_[_]` / `_,_` / `{_,_}` constructors.
    pub fn app(&mut self, sym: SymbolId, args: Vec<DagId>) -> DagId {
        self.rt.rebuild(self.sig, sym, args)
    }
    /// Build an overloaded constant at an explicit declaration range. Nullary overloads have no
    /// argument sorts from which ordinary `app` construction could select the intended declaration.
    pub fn constant_at_sort(&mut self, name: &str, sort_name: &str) -> Option<DagId> {
        let sort = (0..self.sig.sorts().num_sorts())
            .map(|index| SortId::from_raw(index as u32))
            .find(|&sort| self.sig.sorts().name(sort) == sort_name)?;
        let symbol = self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol
                    .decls()
                    .iter()
                    .any(|decl| decl.domain.is_empty() && decl.range == sort))
            .then_some(id)
        })?;
        Some(self.rt.make_const_at_sort(self.sig, symbol, sort))
    }
    /// Build an `iter` successor `sym^count(arg)` in the current engine (`downTerm`'s `'s_^n[t]`).
    pub fn make_iter(&mut self, sym: SymbolId, count: u64, arg: DagId) -> DagId {
        self.rt
            .make_s(self.sig, sym, crate::num::Nat::from_u64(count), arg)
    }
    /// Materialize the exact `zeroTerm` attached to an `iter` successor.
    /// Resolve the concrete `iter` symbol that owns a `zeroTerm`, avoiding unrelated same-name
    /// overloads selected by the generic name/arity table.
    pub fn resolve_iter(&self, name: &str) -> Option<SymbolId> {
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name && self.sig.succ_zero(id).is_some()).then_some(id)
        })
    }
    /// The successor family whose zero term is `symbol`, if any.
    pub fn iter_zero_owner(&self, symbol: SymbolId) -> Option<String> {
        self.sig.symbols_iter().find_map(|(candidate, owner)| {
            (self.sig.succ_zero(candidate) == Some(symbol)).then(|| owner.name().to_string())
        })
    }
    /// Resolve the zero symbol owned by a named successor family without an ambiguous `0` lookup.
    pub fn resolve_iter_zero(&self, owner: &str) -> Option<SymbolId> {
        self.sig.succ_zero(self.resolve_iter(owner)?)
    }
    pub fn iter_zero(&mut self, succ: SymbolId) -> Option<DagId> {
        let zero = self.sig.succ_zero(succ)?;
        let domain = *self.sig.symbol(succ).decls().first()?.domain.first()?;
        let sort = self
            .sig
            .symbol(zero)
            .decls()
            .iter()
            .map(|decl| decl.range)
            .find(|&range| self.sig.sorts().leq(range, domain))?;
        Some(self.rt.make_const_at_sort(self.sig, zero, sort))
    }
    /// Build an `iter` successor with a **decimal** (unbounded) count, used when a Nat-family
    /// `metaUnify` next-index does not fit `u64`. `None` if `count` is not a decimal numeral.
    pub fn make_iter_decimal(&mut self, sym: SymbolId, count: &str, arg: DagId) -> Option<DagId> {
        Some(
            self.rt
                .make_s(self.sig, sym, crate::num::Nat::from_decimal(count)?, arg),
        )
    }
    /// Resolve an operator by canonical name + arity in the **current** module (the engine the redex is
    /// reducing in) — for building result constants (`true`/`false`/`leastSort`'s qids resolve from
    /// [`MetaHooks`]) and down-translating `downTerm`'s argument into this module. `None` if undeclared.
    pub fn resolve_op(&self, name: &str, arity: usize) -> Option<SymbolId> {
        self.sig.resolve_symbol(name, arity)
    }
    /// Resolve an overloaded application by canonical name and actual argument sorts. A reflected
    /// associative application may carry three or more already-flattened arguments even though its
    /// operator is binary; in that case, resolve the homogeneous binary declaration whose domain
    /// accepts the first argument on the left and every remaining argument on the right.
    pub fn resolve_op_for_args(&self, name: &str, args: &[DagId]) -> Option<SymbolId> {
        let argument_sorts: Vec<_> = args.iter().map(|&arg| self.sort_of(arg)).collect();
        let exact = self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.arity() == args.len()
                && symbol.decls().iter().any(|decl| {
                    argument_sorts
                        .iter()
                        .zip(&decl.domain)
                        .all(|(&actual, &declared)| self.sig.sorts().leq(actual, declared))
                }))
            .then_some(id)
        });
        if exact.is_some() || args.len() < 3 {
            return exact;
        }
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.arity() == 2
                && matches!(symbol.theory(), Theory::Acu | Theory::Au)
                && symbol.decls().iter().any(|decl| {
                    self.sig.sorts().leq(argument_sorts[0], decl.domain[0])
                        && argument_sorts[1..]
                            .iter()
                            .all(|&actual| self.sig.sorts().leq(actual, decl.domain[1]))
                }))
            .then_some(id)
        })
    }
    /// Resolve an operator by portable object-system roles as well as name and arity. External META
    /// envelopes need this discriminator because protocol constructors can share textual signatures
    /// while only the `[msg]` declaration participates in object-message scheduling.
    pub fn resolve_op_with_oo(
        &self,
        name: &str,
        arity: usize,
        roles: [bool; 4],
    ) -> Option<SymbolId> {
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            let oo = symbol.oo;
            (symbol.name() == name
                && symbol.arity() == arity
                && [oo.config, oo.object, oo.message, oo.portal] == roles)
                .then_some(id)
        })
    }
    /// Resolve an overloaded application by portable object-system roles and actual argument sorts.
    /// Unlike [`Self::resolve_op_with_oo`], this distinguishes same-name/arity protocol constructors
    /// such as the `Nat`-count and `Bool`-completion forms of `noSuchResult`.
    pub fn resolve_op_with_oo_for_args(
        &self,
        name: &str,
        arity: usize,
        roles: [bool; 4],
        args: &[DagId],
    ) -> Option<SymbolId> {
        if args.len() != arity {
            return None;
        }
        let argument_sorts: Vec<_> = args.iter().map(|&arg| self.sort_of(arg)).collect();
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            let oo = symbol.oo;
            (symbol.name() == name
                && symbol.arity() == arity
                && [oo.config, oo.object, oo.message, oo.portal] == roles
                && symbol.decls().iter().any(|decl| {
                    argument_sorts
                        .iter()
                        .zip(&decl.domain)
                        .all(|(&actual, &declared)| self.sig.sorts().leq(actual, declared))
                }))
            .then_some(id)
        })
    }
    /// Portable object-system role bits in `config, object, message, portal` order.
    pub fn symbol_oo_roles(&self, sym: SymbolId) -> [bool; 4] {
        let oo = self.sig.symbol(sym).oo;
        [oo.config, oo.object, oo.message, oo.portal]
    }
    /// The reflection hook table installed in the current signature. External managers use the same
    /// down/up vocabulary as ordinary META-LEVEL descent, but are triggered by object messages rather
    /// than by one particular `SpecialOp::Meta` redex.
    pub fn meta_hooks(&self) -> Option<std::rc::Rc<MetaHooks>> {
        self.sig.symbols_iter().find_map(|(_, symbol)| {
            let SpecialOp::Meta { hooks, .. } = symbol.special()? else {
                return None;
            };
            Some(hooks.clone())
        })
    }
    /// Whether `sym` is an **associative** operator (ACU or AU). A flat (≥3-arg) meta-term over an
    /// assoc op is legal — the op is declared binary but a nested application denotes the same flattened
    /// term — so `down_term_ctx` resolves the binary symbol and folds the flat args onto it.
    pub fn symbol_is_assoc(&self, sym: SymbolId) -> bool {
        matches!(self.sig.symbol(sym).theory(), Theory::Acu | Theory::Au)
    }
    /// Whether `sym` is commutative. Transported META constructors retain this bit so newly built
    /// declaration sets canonicalize in the same order as the source engine.
    pub fn symbol_is_commutative(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_commutative()
    }
    /// Whether `sym` is the compact unary successor of the S (`iter`) theory.
    pub fn symbol_is_iter(&self, sym: SymbolId) -> bool {
        matches!(self.sig.symbol(sym).theory(), Theory::S)
    }
    /// The arity (declared domain length) of symbol `sym`.
    pub fn arity(&self, sym: SymbolId) -> usize {
        self.sig.symbol(sym).arity()
    }
    pub fn symbol_is_command_variable(&self, sym: SymbolId) -> bool {
        matches!(self.sig.symbol(sym).class(), SymbolClass::Variable { .. })
    }
    /// Add `n` object-level rewrites to this engine's count. The enclosing special-operation dispatch
    /// counts the descent rewrite separately.
    pub fn add_rewrites(&mut self, n: u64) {
        self.rt.add_rewrites(n);
    }
    /// Classify `n` already-counted rewrites as variant narrowing steps.
    pub fn add_variant_narrowing_subcount(&mut self, n: u64) {
        self.rt.add_variant_narrowing_subcount(n);
    }
    /// Classify `n` already-counted rewrites as narrowing steps.
    pub fn add_narrowing_subcount(&mut self, n: u64) {
        self.rt.add_narrowing_subcount(n);
    }
    /// Current `(membership, rule, variant-narrowing, narrowing)` subcounts.
    pub fn rewrite_breakdown(&self) -> (u64, u64, u64, u64) {
        self.rt.rewrite_breakdown()
    }
    /// Current rewrite count of the transport/current engine.
    pub fn rewrites(&self) -> u64 {
        self.rt.rewrites()
    }
    /// Restore a saved count after an intentionally uncharged auxiliary computation.
    pub fn restore_rewrites(&mut self, count: u64) {
        self.rt.rewrite_count = count;
    }
    /// Pin a DAG for the lifetime of the returned guard.
    pub(crate) fn pin(&self, id: DagId) -> RootGuard {
        self.rt.root(id)
    }
}

/// The descent seam: evaluate a `SpecialOp::Meta` redex. Implemented in the frontend (which owns the
/// build pipeline + module database); the kernel only ever holds a `&mut dyn DescentOps`.
pub trait DescentOps {
    /// Evaluate descent function `op` applied at `redex` (whose top symbol carries `hooks`), returning the
    /// result DAG built in `ctx`, or `None` if it does not reduce (a partial/undefined application — the
    /// redex stays at the kind level). A nested semantic failure is returned unchanged.
    fn descend(
        &mut self,
        ctx: &mut MetaCtx,
        op: MetaOp,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Result<Option<DagId>, ReducerFault>;
}

/// The no-op descent handler: every descent redex stays unreduced. Used on all reduce paths that are not
/// a top-level descent command, so the kernel (and its tests) needs no module database.
pub struct NullDescent;

impl DescentOps for NullDescent {
    fn descend(
        &mut self,
        _: &mut MetaCtx,
        _: MetaOp,
        _: &MetaHooks,
        _: DagId,
    ) -> Result<Option<DagId>, ReducerFault> {
        Ok(None)
    }
}
