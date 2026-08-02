//! Strict host-provided Rust reducers.
//!
//! A [`StrictReducer`] is invoked only after the active engine has normalized every direct argument
//! under the standard eager strategy. Reducers inspect scoped DAG views, may decline to ordinary
//! equations, or build a same-engine result through [`StrictReduceCtx`].

use crate::dag::{ChildIter, DagId, NaValue, NodeRepr, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::smt::SmtNumber;
use crate::sort::SortId;
use crate::symbol::{SymbolClass, SymbolId};
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Arc;

/// A validated, canonical host-function registry key.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct HostFunctionKey(Arc<str>);

impl HostFunctionKey {
    /// Parse the canonical grammar shared by Rust registration and source hooks.
    ///
    /// A key has at least two `.`-separated segments. Every segment starts with lowercase ASCII,
    /// contains only lowercase ASCII letters, digits, and interior `-`, and never ends in `-`.
    pub fn parse(value: impl AsRef<str>) -> Result<Self, HostFunctionRegistrationError> {
        let value = value.as_ref();
        let valid_segment = |segment: &str| {
            let mut bytes = segment.bytes();
            matches!(bytes.next(), Some(b'a'..=b'z'))
                && bytes
                    .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
                && !segment.ends_with('-')
        };
        if !value.contains('.') || !value.split('.').all(valid_segment) {
            return Err(HostFunctionRegistrationError::InvalidKey(value.to_string()));
        }
        Ok(Self(Arc::from(value)))
    }

    /// Return the canonical key bytes as text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Debug for HostFunctionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("HostFunctionKey")
            .field(&self.as_str())
            .finish()
    }
}

impl fmt::Display for HostFunctionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Dense identity of a reducer within one immutable catalog.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HostFunctionId(u32);

impl HostFunctionId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Dense identity of a resolved host attachment within one built signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HostBindingId(u32);

impl HostBindingId {
    pub(crate) fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("host binding table exceeded u32"))
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Catalog construction failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostFunctionRegistrationError {
    InvalidKey(String),
    DuplicateKey(HostFunctionKey),
    InvalidDescriptor(String),
}

impl fmt::Display for HostFunctionRegistrationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidKey(key) => write!(f, "invalid host-function key `{key}`"),
            Self::DuplicateKey(key) => write!(f, "duplicate host-function key `{key}`"),
            Self::InvalidDescriptor(message) => {
                write!(f, "invalid strict reducer descriptor: {message}")
            }
        }
    }
}

impl Error for HostFunctionRegistrationError {}

/// A declaration-relative sort used by a supporting hook requirement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HookSort {
    Argument(usize),
    Result,
}

/// Required resolved operator hook and its declaration-relative profile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpHookRequirement {
    purpose: Arc<str>,
    domain: Arc<[HookSort]>,
    range: HookSort,
    range_also_compatible_with: Arc<[HookSort]>,
}

impl OpHookRequirement {
    pub fn purpose(&self) -> &str {
        &self.purpose
    }

    pub fn domain(&self) -> &[HookSort] {
        &self.domain
    }

    pub fn range(&self) -> HookSort {
        self.range
    }

    pub(crate) fn range_constraints(&self) -> impl Iterator<Item = HookSort> + '_ {
        std::iter::once(self.range).chain(self.range_also_compatible_with.iter().copied())
    }
}

/// Required ground constant term hook and its declaration-relative sort.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermHookRequirement {
    purpose: Arc<str>,
    sort: HookSort,
}

impl TermHookRequirement {
    pub fn purpose(&self) -> &str {
        &self.purpose
    }

    pub fn sort(&self) -> HookSort {
        self.sort
    }
}

/// Immutable registration metadata for a strict reducer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrictReducerDescriptor {
    arity: usize,
    required_op_hooks: Arc<[OpHookRequirement]>,
    required_term_hooks: Arc<[TermHookRequirement]>,
}

impl StrictReducerDescriptor {
    /// Begin an exact-arity supporting-hook schema.
    ///
    /// Hook purposes and declaration-relative argument positions are validated when the finished
    /// descriptor is registered in a [`HostFunctionCatalogBuilder`].
    pub fn builder(arity: usize) -> StrictReducerDescriptorBuilder {
        StrictReducerDescriptorBuilder {
            arity,
            op_hooks: Vec::new(),
            term_hooks: Vec::new(),
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn required_op_hooks(&self) -> &[OpHookRequirement] {
        &self.required_op_hooks
    }

    pub fn required_term_hooks(&self) -> &[TermHookRequirement] {
        &self.required_term_hooks
    }

    fn validate(&self) -> Result<(), HostFunctionRegistrationError> {
        let mut purposes = std::collections::HashSet::new();
        for requirement in &*self.required_op_hooks {
            if !purposes.insert(requirement.purpose().to_string()) {
                return Err(HostFunctionRegistrationError::InvalidDescriptor(format!(
                    "duplicate hook purpose `{}`",
                    requirement.purpose()
                )));
            }
            for sort in requirement
                .domain()
                .iter()
                .copied()
                .chain(requirement.range_constraints())
            {
                if let HookSort::Argument(position) = sort
                    && position >= self.arity
                {
                    return Err(HostFunctionRegistrationError::InvalidDescriptor(format!(
                        "hook `{}` references argument {position} outside arity {}",
                        requirement.purpose(),
                        self.arity
                    )));
                }
            }
        }
        for requirement in &*self.required_term_hooks {
            if !purposes.insert(requirement.purpose().to_string()) {
                return Err(HostFunctionRegistrationError::InvalidDescriptor(format!(
                    "duplicate hook purpose `{}`",
                    requirement.purpose()
                )));
            }
            if let HookSort::Argument(position) = requirement.sort()
                && position >= self.arity
            {
                return Err(HostFunctionRegistrationError::InvalidDescriptor(format!(
                    "hook `{}` references argument {position} outside arity {}",
                    requirement.purpose(),
                    self.arity
                )));
            }
        }
        Ok(())
    }
}

/// Builder for immutable reducer registration metadata.
///
/// Operator and constant-term purposes share one namespace. Duplicate purposes and
/// [`HookSort::Argument`] positions outside `arity` are retained while building and rejected by
/// [`HostFunctionCatalogBuilder::register`].
pub struct StrictReducerDescriptorBuilder {
    arity: usize,
    op_hooks: Vec<OpHookRequirement>,
    term_hooks: Vec<TermHookRequirement>,
}

impl StrictReducerDescriptorBuilder {
    /// Require one supporting operator with a declaration-relative domain and range.
    ///
    /// The source attachment must supply exactly this purpose and a compatible operator profile.
    pub fn require_op_hook(
        mut self,
        purpose: impl Into<Arc<str>>,
        domain: &[HookSort],
        range: HookSort,
    ) -> Self {
        self.op_hooks.push(OpHookRequirement {
            purpose: purpose.into(),
            domain: Arc::from(domain),
            range,
            range_also_compatible_with: Arc::from([]),
        });
        self
    }

    /// Require one supporting ground constant whose sort is relative to the host declaration.
    ///
    /// The source attachment must supply exactly this purpose and a compatible constant term.
    pub fn require_constant_term_hook(
        mut self,
        purpose: impl Into<Arc<str>>,
        sort: HookSort,
    ) -> Self {
        self.term_hooks.push(TermHookRequirement {
            purpose: purpose.into(),
            sort,
        });
        self
    }

    /// Freeze the accumulated schema.
    ///
    /// This step does not validate duplicate purposes or argument positions; catalog registration
    /// performs that validation and returns [`HostFunctionRegistrationError::InvalidDescriptor`].
    pub fn build(self) -> StrictReducerDescriptor {
        StrictReducerDescriptor {
            arity: self.arity,
            required_op_hooks: self.op_hooks.into(),
            required_term_hooks: self.term_hooks.into(),
        }
    }
}

/// A reducer implementation failure, distinct from an ordinary domain decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReducerFault {
    key: Option<HostFunctionKey>,
    message: Arc<str>,
}

impl ReducerFault {
    pub fn new(message: impl Into<Arc<str>>) -> Self {
        Self {
            key: None,
            message: message.into(),
        }
    }

    pub fn key(&self) -> Option<&HostFunctionKey> {
        self.key.as_ref()
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub(crate) fn for_key(mut self, key: &HostFunctionKey) -> Self {
        if self.key.is_none() {
            self.key = Some(key.clone());
        }
        self
    }
}

impl fmt::Display for ReducerFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(key) = &self.key {
            write!(f, "strict reducer `{key}` failed: {}", self.message)
        } else {
            f.write_str(&self.message)
        }
    }
}

impl Error for ReducerFault {}

/// Safe construction failure inside a reducer callback.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildError(Arc<str>);

impl BuildError {
    fn new(message: impl Into<Arc<str>>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Error for BuildError {}

impl From<BuildError> for ReducerFault {
    fn from(value: BuildError) -> Self {
        ReducerFault::new(value.0)
    }
}

struct ReductionScope;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ScopedDag<'ctx> {
    id: DagId,
    _scope: PhantomData<&'ctx ReductionScope>,
}

impl<'ctx> ScopedDag<'ctx> {
    fn new(id: DagId) -> Self {
        Self {
            id,
            _scope: PhantomData,
        }
    }
}

/// A direct argument proved normal for the active equation epoch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NormalDag<'ctx>(ScopedDag<'ctx>);

impl<'ctx> NormalDag<'ctx> {
    pub fn as_ref(self) -> DagRef<'ctx> {
        DagRef(self.0)
    }
}

/// The strict host redex before its top attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RedexDag<'ctx>(ScopedDag<'ctx>);

impl<'ctx> RedexDag<'ctx> {
    pub fn as_ref(self) -> DagRef<'ctx> {
        DagRef(self.0)
    }
}

/// A safely built same-engine reducer result; not promised equationally normal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BuiltDag<'ctx>(ScopedDag<'ctx>);

impl<'ctx> BuiltDag<'ctx> {
    pub fn as_ref(self) -> DagRef<'ctx> {
        DagRef(self.0)
    }
}

/// A scoped read-only DAG reference carrying no normality claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DagRef<'ctx>(ScopedDag<'ctx>);

/// Public read-only node representation.
#[derive(Debug)]
pub enum DagView<'a, 'ctx> {
    App,
    Iter { count: String, arg: DagRef<'ctx> },
    String(&'a [u8]),
    QuotedIdentifier(&'a str),
    Float(f64),
    SmtNumber(&'a SmtNumber),
    Variable { name: u32 },
}

/// Iterator over scoped child views.
pub struct ChildView<'a, 'ctx> {
    inner: ChildIter<'a>,
    _scope: PhantomData<&'ctx ReductionScope>,
}

impl<'ctx> Iterator for ChildView<'_, 'ctx> {
    type Item = DagRef<'ctx>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|id| DagRef(ScopedDag::new(id)))
    }
}

/// An opaque operator capability tied to one active strict callback.
///
/// Values can only be obtained from [`ScopedHostHooks`]. The invariant callback lifetime prevents
/// a capability from being shortened to another callback scope, while the private fields prevent
/// conversion from or to a raw [`SymbolId`].
///
/// ```compile_fail
/// use tnk_core::host::HostSymbol;
/// use tnk_core::symbol::SymbolId;
///
/// fn forge<'ctx>(raw: SymbolId) -> HostSymbol<'ctx> {
///     HostSymbol::new(raw)
/// }
/// ```
///
/// ```compile_fail
/// use std::any::Any;
/// use tnk_core::host::HostSymbol;
///
/// fn erase_scope<'ctx>(symbol: HostSymbol<'ctx>) -> Box<dyn Any> {
///     Box::new(symbol)
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HostSymbol<'ctx> {
    id: SymbolId,
    _scope: PhantomData<&'ctx mut &'ctx ReductionScope>,
}

impl<'ctx> HostSymbol<'ctx> {
    fn new(id: SymbolId) -> Self {
        Self {
            id,
            _scope: PhantomData,
        }
    }

    /// Test a read-only raw symbol observation without exposing this capability's ID.
    pub fn matches(self, symbol: SymbolId) -> bool {
        self.id == symbol
    }
}

/// Callback-scoped view of the supporting hooks validated for the active host binding.
///
/// ```
/// use tnk_core::host::{
///     ReducerFault, StrictCall, StrictOutcome, StrictReduceCtx,
/// };
///
/// fn wrap<'ctx>(
///     ctx: &mut StrictReduceCtx<'ctx>,
///     call: StrictCall<'ctx>,
/// ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
///     let wrap = call.hooks().op_symbol("wrapSymbol");
///     Ok(StrictOutcome::Reduced(
///         ctx.app(wrap, &[call.argument(0).as_ref()])?,
///     ))
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct ScopedHostHooks<'ctx> {
    resolved: &'ctx ResolvedHostHooks,
    _scope: PhantomData<&'ctx mut &'ctx ReductionScope>,
}

impl<'ctx> ScopedHostHooks<'ctx> {
    fn new(resolved: &'ctx ResolvedHostHooks) -> Self {
        Self {
            resolved,
            _scope: PhantomData,
        }
    }

    /// Resolve a validated supporting operator for construction in this callback.
    ///
    /// # Panics
    ///
    /// Panics if `purpose` is not an operator-hook purpose in the successfully bound descriptor.
    pub fn op_symbol(self, purpose: &str) -> HostSymbol<'ctx> {
        HostSymbol::new(self.resolved.op_symbol(purpose))
    }

    /// Resolve a validated supporting constant term for construction in this callback.
    ///
    /// # Panics
    ///
    /// Panics if `purpose` is not a constant-term-hook purpose in the successfully bound descriptor.
    pub fn term_symbol(self, purpose: &str) -> HostSymbol<'ctx> {
        HostSymbol::new(self.resolved.term_symbol(purpose))
    }
}

/// Immutable binding-time hooks resolved while the containing signature is built.
///
/// Raw lookup is deliberately unavailable outside the crate; callback code obtains scoped
/// [`HostSymbol`] capabilities from [`StrictCall::hooks`] instead:
///
/// ```compile_fail
/// use tnk_core::host::ResolvedHostHooks;
/// use tnk_core::symbol::SymbolId;
///
/// fn detach_symbol(hooks: &ResolvedHostHooks) -> SymbolId {
///     hooks.op_symbol("supportingSymbol")
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::{ResolvedHostHooks, ScopedHostHooks};
///
/// fn activate<'ctx>(hooks: &'ctx ResolvedHostHooks) -> ScopedHostHooks<'ctx> {
///     ScopedHostHooks::new(hooks)
/// }
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ResolvedHostHooks {
    op_hooks: HashMap<Arc<str>, SymbolId>,
    term_symbols: HashMap<Arc<str>, SymbolId>,
}

impl ResolvedHostHooks {
    /// Begin collecting signature-local symbols for one prospective host attachment.
    pub fn builder() -> ResolvedHostHooksBuilder {
        ResolvedHostHooksBuilder::default()
    }

    pub(crate) fn op_symbol(&self, purpose: &str) -> SymbolId {
        self.op_hooks[purpose]
    }

    pub(crate) fn term_symbol(&self, purpose: &str) -> SymbolId {
        self.term_symbols[purpose]
    }

    pub(crate) fn get_op(&self, purpose: &str) -> Option<SymbolId> {
        self.op_hooks.get(purpose).copied()
    }

    pub(crate) fn get_term(&self, purpose: &str) -> Option<SymbolId> {
        self.term_symbols.get(purpose).copied()
    }
    pub(crate) fn op_purposes(&self) -> impl Iterator<Item = &str> {
        self.op_hooks.keys().map(AsRef::as_ref)
    }

    pub(crate) fn term_purposes(&self) -> impl Iterator<Item = &str> {
        self.term_symbols.keys().map(AsRef::as_ref)
    }
}

/// Builder for immutable, signature-local supporting-hook bindings.
///
/// It is a pre-execution staging type: [`SymbolId`] membership and hook profiles are validated by the
/// Engine binding API. A purpose is unique across operator and constant-term hooks.
#[derive(Default)]
pub struct ResolvedHostHooksBuilder {
    op_hooks: HashMap<Arc<str>, SymbolId>,
    term_symbols: HashMap<Arc<str>, SymbolId>,
    duplicate: Option<Arc<str>>,
}

impl ResolvedHostHooksBuilder {
    /// Associate an operator-hook purpose with a signature-local symbol.
    ///
    /// Reusing the purpose, including as a constant-term purpose, makes [`Self::build`] fail.
    pub fn op(mut self, purpose: impl Into<Arc<str>>, symbol: SymbolId) -> Self {
        let purpose = purpose.into();
        if self.op_hooks.insert(purpose.clone(), symbol).is_some()
            || self.term_symbols.contains_key(purpose.as_ref())
        {
            self.duplicate = Some(purpose);
        }
        self
    }

    /// Associate a constant-term-hook purpose with a signature-local symbol.
    ///
    /// Reusing the purpose, including as an operator purpose, makes [`Self::build`] fail.
    pub fn constant_term(mut self, purpose: impl Into<Arc<str>>, symbol: SymbolId) -> Self {
        let purpose = purpose.into();
        if self.term_symbols.insert(purpose.clone(), symbol).is_some()
            || self.op_hooks.contains_key(purpose.as_ref())
        {
            self.duplicate = Some(purpose);
        }
        self
    }

    /// Freeze the purpose map for subsequent Engine validation and binding.
    ///
    /// # Errors
    ///
    /// Returns [`HostBindingError::DuplicateHookPurpose`] if any purpose was added more than once or
    /// in both hook classes.
    pub fn build(self) -> Result<ResolvedHostHooks, HostBindingError> {
        if let Some(purpose) = self.duplicate {
            return Err(HostBindingError::DuplicateHookPurpose(purpose.to_string()));
        }
        Ok(ResolvedHostHooks {
            op_hooks: self.op_hooks,
            term_symbols: self.term_symbols,
        })
    }
}

/// One strict callback invocation.
pub struct StrictCall<'ctx> {
    redex: RedexDag<'ctx>,
    arguments: Vec<NormalDag<'ctx>>,
    argument_sorts: Vec<SortId>,
    result_range: SortId,
    hooks: ScopedHostHooks<'ctx>,
}

impl<'ctx> StrictCall<'ctx> {
    /// Return the complete redex before its final top attempt.
    pub fn redex(&self) -> RedexDag<'ctx> {
        self.redex
    }

    /// Return one current-epoch-normal direct argument.
    ///
    /// # Panics
    ///
    /// Panics if `position >= self.arguments().len()`. Successful attachment guarantees that this
    /// length equals the registered descriptor arity.
    pub fn argument(&self, position: usize) -> NormalDag<'ctx> {
        self.arguments[position]
    }

    /// Return every direct argument in source position order.
    pub fn arguments(&self) -> &[NormalDag<'ctx>] {
        &self.arguments
    }

    /// Return the selected declaration's actual argument sorts.
    pub fn argument_sorts(&self) -> &[SortId] {
        &self.argument_sorts
    }

    /// Return the structurally selected declaration range.
    pub fn result_range(&self) -> SortId {
        self.result_range
    }

    /// Return the callback-scoped view of validated supporting hooks.
    pub fn hooks(&self) -> ScopedHostHooks<'ctx> {
        self.hooks
    }
}

/// A strict reducer outcome.
pub enum StrictOutcome<'ctx> {
    Decline,
    Reduced(BuiltDag<'ctx>),
}

/// Trusted, pure, deterministic host-provided equational reduction.
///
/// Implementations must be referentially transparent for the canonical redex, immutable signature,
/// and catalog binding. A result or decline must not depend on time, I/O, randomness,
/// nondeterministic services, mutable result-affecting host state, or externally visible side effects.
/// `Send + Sync` permits an immutable reducer object to be shared by independent engines; it does not
/// relax those semantic obligations.
///
/// A callback returns [`StrictOutcome::Decline`] only for an ordinary domain/representation miss,
/// [`StrictOutcome::Reduced`] for a same-scope result, or [`ReducerFault`] for an implementation or
/// contract failure. It must not translate implementation failure into decline.
///
/// # Panics
///
/// Callback code is trusted and should not panic. TNK does not catch or convert a callback panic to
/// [`ReducerFault`]; it follows the embedding's Rust unwind/abort policy, with no process-survival,
/// TNK-owned semantic rollback, callback-side-effect rollback, or panic-sandbox guarantee.
///
/// # Cancellation and resources
///
/// Invocation is synchronous. There is no cancellation token, timeout, async yield, preemption, or
/// callback-controlled transaction API. Returning [`ReducerFault`] rolls back the owning TNK semantic
/// checkpoint; callback-authored external side effects are outside that atomicity. A reducer may
/// diverge, block, or exhaust CPU/memory; its author owns termination and resource bounds, and an
/// embedding that requires interruption or accepts untrusted execution must enforce that policy
/// through outer process isolation.
pub trait StrictReducer: Send + Sync + 'static {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault>;
}

/// Narrow callback context for scoped inspection and theory-aware construction.
///
/// The callback boundary deliberately exposes neither raw DAG IDs nor the owning [`Engine`](crate::engine::Engine).
/// Scoped values cannot be forged, converted to raw IDs, retained as `'static`, combined across
/// callback scopes, or used to start nested reduction. Child views cannot be promoted to normal-form
/// proofs, and the context exposes no signature mutation or collection operation:
///
/// ```compile_fail
/// use tnk_core::dag::DagId;
/// use tnk_core::host::DagRef;
///
/// fn expose_id(dag: DagRef<'_>) -> DagId {
///     dag.0.id
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::dag::DagId;
/// use tnk_core::host::DagRef;
///
/// fn forge(id: DagId) -> DagRef<'static> {
///     DagRef::from(id)
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::DagRef;
///
/// fn retain<'ctx>(dag: DagRef<'ctx>) -> DagRef<'static> {
///     dag
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::dag::DagId;
/// use tnk_core::host::BuiltDag;
///
/// fn expose_result(dag: BuiltDag<'_>) -> DagId {
///     dag.into()
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::dag::DagId;
/// use tnk_core::host::StrictReduceCtx;
///
/// fn nested_reduce(ctx: &mut StrictReduceCtx<'_>, dag: DagId) {
///     let _ = ctx.reduce(dag);
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::{DagRef, NormalDag};
///
/// fn promote_child<'ctx>(child: DagRef<'ctx>) -> NormalDag<'ctx> {
///     NormalDag::from(child)
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::StrictReduceCtx;
/// use tnk_core::symbol::SymbolId;
///
/// fn constant_from_captured<'ctx>(
///     ctx: &mut StrictReduceCtx<'ctx>,
///     captured: SymbolId,
/// ) {
///     let _ = ctx.constant(captured);
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::StrictReduceCtx;
/// use tnk_core::symbol::SymbolId;
///
/// fn app_from_raw<'ctx>(ctx: &mut StrictReduceCtx<'ctx>, raw: SymbolId) {
///     let _ = ctx.app(raw, &[]);
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::StrictReduceCtx;
/// use tnk_core::symbol::SymbolId;
///
/// // A SymbolId captured from a different Engine cannot alias an active callback builder symbol.
/// fn string_from_foreign_engine<'ctx>(
///     ctx: &mut StrictReduceCtx<'ctx>,
///     foreign: SymbolId,
/// ) {
///     let _ = ctx.make_string(foreign, b"value");
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::{HostSymbol, StrictReduceCtx};
///
/// fn use_in_shorter_scope<'long, 'short>(
///     ctx: &mut StrictReduceCtx<'short>,
///     foreign: HostSymbol<'long>,
/// ) where
///     'long: 'short,
/// {
///     // Covariance would allow this shortening; HostSymbol is deliberately invariant.
///     let _ = ctx.constant(foreign);
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::HostSymbol;
///
/// fn retain_symbol<'ctx>(symbol: HostSymbol<'ctx>) -> HostSymbol<'static> {
///     symbol
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::{DagRef, HostSymbol, StrictReduceCtx};
///
/// fn mix_dag_scopes<'active, 'foreign>(
///     ctx: &mut StrictReduceCtx<'active>,
///     symbol: HostSymbol<'active>,
///     left: DagRef<'active>,
///     foreign: DagRef<'foreign>,
/// ) {
///     let _ = ctx.app(symbol, &[left, foreign]);
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::StrictReduceCtx;
///
/// fn mutate_signature(ctx: &mut StrictReduceCtx<'_>) {
///     ctx.signature.add_sort("forged");
/// }
/// ```
///
/// ```compile_fail
/// use tnk_core::host::StrictReduceCtx;
///
/// fn collect_during_callback(ctx: &mut StrictReduceCtx<'_>) {
///     ctx.collect();
/// }
/// ```
pub struct StrictReduceCtx<'ctx> {
    pub(crate) runtime: &'ctx mut Runtime,
    pub(crate) signature: &'ctx Signature,
    protected_base: Option<usize>,
    _scope: PhantomData<&'ctx ReductionScope>,
}

impl<'ctx> StrictReduceCtx<'ctx> {
    /// Observe the top symbol of a scoped DAG.
    ///
    /// This raw [`SymbolId`] is read-only: context builders accept only a callback-scoped
    /// [`HostSymbol`] obtained from [`StrictCall::hooks`].
    pub fn top(&self, dag: DagRef<'ctx>) -> SymbolId {
        self.runtime.node(dag.0.id).symbol()
    }

    /// Return the current least sort of a scoped DAG.
    pub fn sort(&self, dag: DagRef<'ctx>) -> SortId {
        self.runtime.sort_of(dag.0.id)
    }

    /// Inspect the public representation of a scoped DAG node.
    pub fn repr<'a>(&'a self, dag: DagRef<'ctx>) -> DagView<'a, 'ctx> {
        match self.runtime.node(dag.0.id).repr() {
            NodeRepr::App => DagView::App,
            NodeRepr::Iter { count, arg } => DagView::Iter {
                count,
                arg: DagRef(ScopedDag::new(arg)),
            },
            NodeRepr::Str(value) => DagView::String(value),
            NodeRepr::Qid(value) => DagView::QuotedIdentifier(value),
            NodeRepr::Float(value) => DagView::Float(value),
            NodeRepr::SmtNum(value) => DagView::SmtNumber(value),
            NodeRepr::Var { name } => DagView::Variable { name },
        }
    }

    /// Iterate over scoped direct children without promoting them to normal-form proofs.
    pub fn children<'a>(&'a self, dag: DagRef<'ctx>) -> ChildView<'a, 'ctx> {
        ChildView {
            inner: self.runtime.node(dag.0.id).children(),
            _scope: PhantomData,
        }
    }

    /// Test whether a normal DAG contains no variables.
    pub fn is_ground(&self, dag: NormalDag<'ctx>) -> bool {
        let mut pending = vec![dag.0.id];
        while let Some(id) = pending.pop() {
            let node = self.runtime.node(id);
            if matches!(node.term, NodeTerm::Var { .. })
                || matches!(
                    self.signature.symbol(node.symbol()).class,
                    SymbolClass::Variable { .. } | SymbolClass::SortVariable
                )
            {
                return false;
            }
            pending.extend(node.children());
        }
        true
    }

    /// Borrow an existing native byte-string payload without cloning its bytes or allocating an input
    /// buffer. Returns `None` for every other normal representation.
    pub fn decode_string<'a>(&'a self, dag: NormalDag<'ctx>) -> Option<&'a [u8]> {
        match &self.runtime.node(dag.0.id).term {
            NodeTerm::Na {
                value: NaValue::Str(value),
                ..
            } => Some(value),
            _ => None,
        }
    }

    /// Borrow an existing quoted-identifier payload. Returns `None` for every other normal
    /// representation.
    pub fn decode_qid<'a>(&'a self, dag: NormalDag<'ctx>) -> Option<&'a str> {
        match &self.runtime.node(dag.0.id).term {
            NodeTerm::Na {
                value: NaValue::Qid(value),
                ..
            } => Some(value),
            _ => None,
        }
    }

    /// Decode an existing native float payload. Returns `None` for every other normal representation.
    pub fn decode_float(&self, dag: NormalDag<'ctx>) -> Option<f64> {
        match &self.runtime.node(dag.0.id).term {
            NodeTerm::Na {
                value: NaValue::Float(bits),
                ..
            } => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }
    fn protect(&mut self, id: DagId) -> BuiltDag<'ctx> {
        self.runtime.protect_strict_callback_value(id);
        BuiltDag(ScopedDag::new(id))
    }

    /// Build a constant through one callback-scoped supporting symbol.
    ///
    /// # Errors
    ///
    /// A scoped [`HostSymbol`] guarantees active-signature membership. Returns [`BuildError`] if the
    /// selected supporting symbol is not nullary.
    pub fn constant(&mut self, symbol: HostSymbol<'ctx>) -> Result<BuiltDag<'ctx>, BuildError> {
        let symbol = symbol.id;
        let declaration = self.signature.host_symbol(symbol).ok_or_else(|| {
            BuildError::new("constant symbol does not belong to the active signature")
        })?;
        if declaration.arity() != 0 {
            return Err(BuildError::new(
                "constant builder received a non-nullary symbol",
            ));
        }
        let id = self.runtime.make_const(self.signature, symbol);
        Ok(self.protect(id))
    }

    /// Build one declaration-arity application through the active signature.
    ///
    /// Construction is theory-aware rather than free-only. The active rebuild selects the canonical
    /// free, ACU, AU, or CUI representation as applicable, including associative flattening,
    /// commutative ordering, multiplicity/idempotence handling, and declared identity removal or
    /// collapse. The returned [`BuiltDag`] is structurally canonical but is not promised equationally
    /// normal.
    ///
    /// # Errors
    ///
    /// A scoped [`HostSymbol`] guarantees active-signature membership. Returns [`BuildError`] if the
    /// argument count differs from the declared arity or no declaration accepts the supplied sorts.
    pub fn app(
        &mut self,
        symbol: HostSymbol<'ctx>,
        arguments: &[DagRef<'ctx>],
    ) -> Result<BuiltDag<'ctx>, BuildError> {
        let symbol = symbol.id;
        let declaration = self.signature.host_symbol(symbol).ok_or_else(|| {
            BuildError::new("application symbol does not belong to the active signature")
        })?;
        if declaration.arity() != arguments.len() {
            return Err(BuildError::new(format!(
                "application arity mismatch: expected {}, got {}",
                declaration.arity(),
                arguments.len()
            )));
        }
        let applicable = declaration.decls().iter().any(|candidate| {
            arguments
                .iter()
                .zip(&candidate.domain)
                .all(|(argument, domain)| {
                    self.signature
                        .sorts()
                        .leq(self.runtime.sort_of(argument.0.id), *domain)
                })
        });
        if !applicable {
            return Err(BuildError::new(format!(
                "no declaration of `{}` accepts the supplied argument sorts",
                declaration.name()
            )));
        }
        let identity = {
            let symbol = self.signature.symbol(symbol);
            symbol
                .identity()
                .or_else(|| symbol.left_identity())
                .or_else(|| symbol.right_identity())
        };
        if let Some(identity) = identity {
            self.runtime.identity_dag(self.signature, identity);
        }
        let ids = arguments.iter().map(|argument| argument.0.id).collect();
        let id = self.runtime.rebuild(self.signature, symbol, ids);
        Ok(self.protect(id))
    }

    /// Encode `bytes` as a newly owned TNK byte-string payload using a callback-scoped nullary marker.
    ///
    /// # Errors
    ///
    /// A scoped [`HostSymbol`] guarantees active-signature membership. Returns [`BuildError`] if the
    /// selected marker is not nullary.
    pub fn make_string(
        &mut self,
        symbol: HostSymbol<'ctx>,
        bytes: &[u8],
    ) -> Result<BuiltDag<'ctx>, BuildError> {
        let symbol = symbol.id;
        let declaration = self.signature.host_symbol(symbol).ok_or_else(|| {
            BuildError::new("string symbol does not belong to the active signature")
        })?;
        if declaration.arity() != 0 {
            return Err(BuildError::new(
                "string builder requires a nullary marker symbol",
            ));
        }
        let id = self
            .runtime
            .make_na(self.signature, symbol, NaValue::Str(bytes.into()));
        Ok(self.protect(id))
    }

    /// Reuse a normal direct argument as the callback result without copying its DAG.
    pub fn reuse(&self, dag: NormalDag<'ctx>) -> BuiltDag<'ctx> {
        BuiltDag(dag.0)
    }
}

impl Drop for StrictReduceCtx<'_> {
    fn drop(&mut self) {
        if let Some(base) = self.protected_base {
            self.runtime.end_strict_callback_scope(base);
        }
    }
}

struct HostFunctionEntry {
    key: HostFunctionKey,
    descriptor: StrictReducerDescriptor,
    reducer: Arc<dyn StrictReducer>,
}

#[derive(Default)]
struct HostFunctionCatalogInner {
    entries: Vec<HostFunctionEntry>,
    by_key: HashMap<HostFunctionKey, HostFunctionId>,
}

/// Immutable, host-owned strict reducer catalog.
#[derive(Clone, Default)]
pub struct HostFunctionCatalog(Arc<HostFunctionCatalogInner>);

impl fmt::Debug for HostFunctionCatalog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HostFunctionCatalog")
            .field("keys", &self.0.by_key.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl HostFunctionCatalog {
    /// Begin assembling an immutable catalog.
    pub fn builder() -> HostFunctionCatalogBuilder {
        HostFunctionCatalogBuilder::default()
    }

    pub fn is_empty(&self) -> bool {
        self.0.entries.is_empty()
    }

    pub fn contains(&self, key: &str) -> bool {
        HostFunctionKey::parse(key)
            .ok()
            .is_some_and(|key| self.0.by_key.contains_key(&key))
    }
    /// Descriptor registered under `key`, for signature builders resolving typed hook contracts.
    pub fn descriptor_for(&self, key: &HostFunctionKey) -> Option<&StrictReducerDescriptor> {
        self.resolve(key).map(|id| self.descriptor(id))
    }

    pub(crate) fn resolve(&self, key: &HostFunctionKey) -> Option<HostFunctionId> {
        self.0.by_key.get(key).copied()
    }

    pub(crate) fn key(&self, id: HostFunctionId) -> &HostFunctionKey {
        &self.0.entries[id.index()].key
    }

    pub(crate) fn descriptor(&self, id: HostFunctionId) -> &StrictReducerDescriptor {
        &self.0.entries[id.index()].descriptor
    }

    pub(crate) fn reducer(&self, id: HostFunctionId) -> &dyn StrictReducer {
        self.0.entries[id.index()].reducer.as_ref()
    }
}

/// One-shot builder for a host-owned reducer capability catalog.
///
/// Registration validates canonical keys and reducer descriptors. [`Self::build`] consumes the
/// builder; the resulting catalog has no mutation or replacement API.
#[derive(Default)]
pub struct HostFunctionCatalogBuilder {
    entries: Vec<HostFunctionEntry>,
    by_key: HashMap<HostFunctionKey, HostFunctionId>,
}

impl HostFunctionCatalogBuilder {
    /// Register one trusted reducer and its exact attachment descriptor.
    ///
    /// # Errors
    ///
    /// Returns [`HostFunctionRegistrationError`] for a malformed key, a duplicate canonical key, or
    /// an invalid descriptor (duplicate purposes or an out-of-arity [`HookSort::Argument`]).
    ///
    /// # Panics
    ///
    /// Panics if the catalog would contain more than `u32::MAX` reducers.
    pub fn register<R: StrictReducer>(
        mut self,
        key: &str,
        reducer: R,
        descriptor: StrictReducerDescriptor,
    ) -> Result<Self, HostFunctionRegistrationError> {
        descriptor.validate()?;
        let key = HostFunctionKey::parse(key)?;
        if self.by_key.contains_key(&key) {
            return Err(HostFunctionRegistrationError::DuplicateKey(key));
        }
        let id = HostFunctionId(
            u32::try_from(self.entries.len()).expect("host function catalog exceeded u32"),
        );
        self.by_key.insert(key.clone(), id);
        self.entries.push(HostFunctionEntry {
            key,
            descriptor,
            reducer: Arc::new(reducer),
        });
        Ok(self)
    }

    /// Register a unary typed TNK byte-string reducer.
    ///
    /// The adapter borrows the existing input payload as `&[u8]` without cloning its bytes or
    /// allocating an input buffer. A representation miss declines without invoking `function`.
    /// Otherwise `function` runs synchronously and returns an owned `Vec<u8>`, which the adapter
    /// encodes as a new TNK byte string through the descriptor-required, signature-resolved
    /// `stringSymbol`. Binding requires that nullary marker to be compatible with the argument and
    /// selected result sorts.
    ///
    /// `function` has the same purity, panic, cancellation, and resource obligations as
    /// [`StrictReducer`]. A later callback panic is not caught or converted to [`ReducerFault`].
    /// # Errors
    ///
    /// Returns [`HostFunctionRegistrationError`] if `key` is malformed or already registered.
    ///
    /// # Panics
    ///
    /// Panics if the catalog would contain more than `u32::MAX` reducers.
    pub fn register_typed1<F>(
        self,
        key: &str,
        _input: codecs::StringCodec,
        _output: codecs::StringCodec,
        function: F,
    ) -> Result<Self, HostFunctionRegistrationError>
    where
        F: for<'a> Fn(&'a [u8]) -> Vec<u8> + Send + Sync + 'static,
    {
        self.register(key, TypedString1 { function }, string_descriptor(1))
    }

    /// Register a binary typed TNK byte-string reducer.
    ///
    /// The adapter borrows both existing payloads as `&[u8]` without cloning their bytes or allocating
    /// input buffers. It decodes **both** arguments before invoking `function`; if either decode misses,
    /// it declines and never calls the function. The owned `Vec<u8>` output is encoded as a new TNK
    /// byte string through the descriptor-required, signature-resolved `stringSymbol`. Binding requires
    /// that nullary marker to be compatible with both argument sorts and the selected result sort.
    ///
    /// `function` has the same purity, panic, cancellation, and resource obligations as
    /// [`StrictReducer`]. A later callback panic is not caught or converted to [`ReducerFault`].
    /// # Errors
    ///
    /// Returns [`HostFunctionRegistrationError`] if `key` is malformed or already registered.
    ///
    /// # Panics
    ///
    /// Panics if the catalog would contain more than `u32::MAX` reducers.
    pub fn register_typed2<F>(
        self,
        key: &str,
        _left: codecs::StringCodec,
        _right: codecs::StringCodec,
        _output: codecs::StringCodec,
        function: F,
    ) -> Result<Self, HostFunctionRegistrationError>
    where
        F: for<'a, 'b> Fn(&'a [u8], &'b [u8]) -> Vec<u8> + Send + Sync + 'static,
    {
        self.register(key, TypedString2 { function }, string_descriptor(2))
    }

    /// Seal the registrations into an immutable, cloneable catalog.
    ///
    /// Supply the catalog before module/signature construction. Changing an implementation later
    /// requires building a new catalog and a new Engine or Session; existing bindings are not replaced.
    pub fn build(self) -> HostFunctionCatalog {
        HostFunctionCatalog(Arc::new(HostFunctionCatalogInner {
            entries: self.entries,
            by_key: self.by_key,
        }))
    }
}

fn string_descriptor(arity: usize) -> StrictReducerDescriptor {
    let mut compatible = Vec::with_capacity(arity);
    compatible.extend((0..arity).map(HookSort::Argument));
    let requirement = OpHookRequirement {
        purpose: Arc::from("stringSymbol"),
        domain: Arc::from([]),
        range: HookSort::Result,
        range_also_compatible_with: compatible.into(),
    };
    StrictReducerDescriptor {
        arity,
        required_op_hooks: vec![requirement].into(),
        required_term_hooks: Arc::from([]),
    }
}

struct TypedString1<F> {
    function: F,
}

impl<F> StrictReducer for TypedString1<F>
where
    F: for<'a> Fn(&'a [u8]) -> Vec<u8> + Send + Sync + 'static,
{
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let Some(input) = ctx.decode_string(call.argument(0)) else {
            return Ok(StrictOutcome::Decline);
        };
        let output = (self.function)(input);
        let symbol = call.hooks().op_symbol("stringSymbol");
        Ok(StrictOutcome::Reduced(ctx.make_string(symbol, &output)?))
    }
}

struct TypedString2<F> {
    function: F,
}

impl<F> StrictReducer for TypedString2<F>
where
    F: for<'a, 'b> Fn(&'a [u8], &'b [u8]) -> Vec<u8> + Send + Sync + 'static,
{
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let Some(left) = ctx.decode_string(call.argument(0)) else {
            return Ok(StrictOutcome::Decline);
        };
        let Some(right) = ctx.decode_string(call.argument(1)) else {
            return Ok(StrictOutcome::Decline);
        };
        let output = (self.function)(left, right);
        let symbol = call.hooks().op_symbol("stringSymbol");
        Ok(StrictOutcome::Reduced(ctx.make_string(symbol, &output)?))
    }
}

pub mod codecs {
    /// Native TNK byte-string codec marker used by typed registration helpers.
    #[derive(Debug, Clone, Copy, Default)]
    pub struct StringCodec;

    /// Select the native TNK byte-string codec for a typed adapter input or output.
    pub fn string() -> StringCodec {
        StringCodec
    }
}

/// A host attachment rejected while binding a signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostBindingError {
    InvalidKey(String),
    MissingCapability(HostFunctionKey),
    SignatureSealed,
    DuplicateBinding,
    DuplicateHookPurpose(String),
    MissingHook(String),
    UnexpectedHook(String),
    InvalidOperator(String),
    InvalidHook(String),
    IncompatibleDeclarations(String),
}

impl fmt::Display for HostBindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidKey(message)
            | Self::InvalidOperator(message)
            | Self::InvalidHook(message)
            | Self::IncompatibleDeclarations(message) => f.write_str(message),
            Self::MissingCapability(key) => write!(f, "missing host capability `{key}`"),
            Self::SignatureSealed => {
                f.write_str("host bindings are sealed after semantic execution begins")
            }
            Self::DuplicateBinding => f.write_str("operator already has a host-function binding"),
            Self::DuplicateHookPurpose(purpose) => {
                write!(f, "duplicate host hook purpose `{purpose}`")
            }
            Self::MissingHook(purpose) => write!(f, "missing required host hook `{purpose}`"),
            Self::UnexpectedHook(purpose) => write!(f, "unexpected host hook `{purpose}`"),
        }
    }
}

impl Error for HostBindingError {}

/// Resolved signature-local host attachment.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedHostBinding {
    pub function: HostFunctionId,
    pub hooks: ResolvedHostHooks,
    pub arity: usize,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn invoke_strict<'ctx>(
    runtime: &'ctx mut Runtime,
    signature: &'ctx Signature,
    redex: DagId,
    arguments: Vec<DagId>,
    argument_sorts: Vec<SortId>,
    result_range: SortId,
    hooks: &'ctx ResolvedHostHooks,
    reducer: &dyn StrictReducer,
) -> Result<StrictOutcome<'ctx>, ReducerFault> {
    let protected_base = runtime.begin_strict_callback_scope(redex, &arguments);
    let call = strict_call(redex, arguments, argument_sorts, result_range, hooks);
    let mut context = StrictReduceCtx {
        runtime,
        signature,
        protected_base,
        _scope: PhantomData,
    };
    reducer.reduce(&mut context, call)
}

pub(crate) fn strict_call<'ctx>(
    redex: DagId,
    arguments: Vec<DagId>,
    argument_sorts: Vec<SortId>,
    result_range: SortId,
    hooks: &'ctx ResolvedHostHooks,
) -> StrictCall<'ctx> {
    StrictCall {
        redex: RedexDag(ScopedDag::new(redex)),
        arguments: arguments
            .into_iter()
            .map(|argument| NormalDag(ScopedDag::new(argument)))
            .collect(),
        argument_sorts,
        result_range,
        hooks: ScopedHostHooks::new(hooks),
    }
}

pub(crate) fn built_id(result: BuiltDag<'_>) -> DagId {
    result.0.id
}
