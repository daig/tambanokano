//! The META-LEVEL descent seam (Phase 3.1).
//!
//! A descent function (`metaReduce`/`metaApply`/…) is a [`SpecialOp::Meta`](crate::symbol::SpecialOp)
//! that, mid-reduction, down-translates its meta-term arguments into a real object module, runs an engine
//! operation in it, and up-translates the result. Building the object module needs the whole frontend
//! pipeline (parse/flatten/build) + the module database, which live *above* `tnk-core` — but the trigger
//! is inside this crate's reduce loop. So the loop calls *up* through a trait object:
//!
//! * [`DescentOps`] is the seam, implemented in the frontend (`tnk_frontend::meta`). The reduce path
//!   threads a `&mut dyn DescentOps` and [`try_special`](crate::engine) hands a `Meta` redex to it.
//! * [`MetaCtx`] is what the handler gets to read the redex's meta-terms and build the up-result *in the
//!   current engine* — a public, minimal view over the otherwise crate-private [`Runtime`]/[`Signature`].
//!   (Building the throwaway *object* sub-module is a separate `Engine` the handler owns; it never touches
//!   `MetaCtx`.)
//!
//! [`NullDescent`] is the no-op used on every reduce path that is not a top-level descent command (so the
//! kernel and its tests need no module database): a descent redex then simply stays at the kind level.

use crate::dag::{DagId, NaValue, NodeRepr};
use crate::engine::{Runtime, Signature};
use crate::sort::SortId;
use crate::symbol::{MetaHooks, MetaOp, SymbolId};

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
    /// The least sort of node `id` (computed at construction).
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.rt.node(id).sort
    }
    /// The name of sort `s`.
    pub fn sort_name(&self, s: SortId) -> &str {
        self.sig.sorts().name(s)
    }

    /// Build an atomic constant (string / quoted-id / float) for `sym`.
    pub fn make_na(&mut self, sym: SymbolId, value: NaValue) -> DagId {
        self.rt.make_na(self.sig, sym, value)
    }
    /// Build an application of `sym` to `args`, dispatching on the operator's theory (free / ACU / AU /
    /// CUI canonicalization) — the up-result's `_[_]` / `_,_` / `{_,_}` constructors.
    pub fn app(&mut self, sym: SymbolId, args: Vec<DagId>) -> DagId {
        self.rt.rebuild(self.sig, sym, args)
    }
    /// Build an `iter` successor `sym^count(arg)` in the current engine (`downTerm`'s `'s_^n[t]`).
    pub fn make_iter(&mut self, sym: SymbolId, count: u64, arg: DagId) -> DagId {
        self.rt.make_s(self.sig, sym, crate::num::Nat::from_u64(count), arg)
    }
    /// Resolve an operator by canonical name + arity in the **current** module (the engine the redex is
    /// reducing in) — for building result constants (`true`/`false`/`leastSort`'s qids resolve from
    /// [`MetaHooks`]) and down-translating `downTerm`'s argument into this module. `None` if undeclared.
    pub fn resolve_op(&self, name: &str, arity: usize) -> Option<SymbolId> {
        self.sig.resolve_symbol(name, arity)
    }
    /// The arity (declared domain length) of symbol `sym`.
    pub fn arity(&self, sym: SymbolId) -> usize {
        self.sig.symbol(sym).arity()
    }
    /// Add `n` to this engine's rewrite counter — a descent function reports the object-level reduction's
    /// rewrites as part of its own (Maude's `metaReduce` count = the object rewrites + 1 for the descent
    /// itself, the `+1` coming from the normal `try_special` increment).
    pub fn add_rewrites(&mut self, n: u64) {
        self.rt.add_rewrites(n);
    }
}

/// The descent seam: evaluate a `SpecialOp::Meta` redex. Implemented in the frontend (which owns the
/// build pipeline + module database); the kernel only ever holds a `&mut dyn DescentOps`.
pub trait DescentOps {
    /// Evaluate descent function `op` applied at `redex` (whose top symbol carries `hooks`), returning the
    /// result DAG built in `ctx`, or `None` if it does not reduce (a partial/undefined application — the
    /// redex stays at the kind level).
    fn descend(
        &mut self,
        ctx: &mut MetaCtx,
        op: MetaOp,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId>;
}

/// The no-op descent handler: every descent redex stays unreduced. Used on all reduce paths that are not
/// a top-level descent command, so the kernel (and its tests) needs no module database.
pub struct NullDescent;

impl DescentOps for NullDescent {
    fn descend(&mut self, _: &mut MetaCtx, _: MetaOp, _: &MetaHooks, _: DagId) -> Option<DagId> {
        None
    }
}
