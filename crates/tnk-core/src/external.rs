//! Engine-neutral transport for synchronous external-object requests and replies.
//!
//! A [`MetaEnvelope`] owns a small graph of reflected META terms. Its node and symbol indices are local
//! to the envelope: no `DagId`, `SymbolId`, `SortId`, root, or engine-owned allocation crosses the
//! parent/child boundary. The parent engine captures a request into an envelope, the host may materialize
//! it in a throwaway transport engine while operating on a child session, and the resulting envelope is
//! rebuilt in the parent only after the child operation has finished.

use std::collections::HashMap;

use crate::dag::{DagId, NaValue, NodeRepr};
use crate::descent::MetaCtx;
use crate::engine::Engine;
use crate::root::RootGuard;
use crate::smt::SmtNumber;
use crate::sort::SortId;
use crate::symbol::{MetaHooks, SymbolId};

/// An envelope-local symbol index. It has no relationship to any engine's `SymbolId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaSymbolRef(u32);

/// An envelope-local node index. It has no relationship to any engine's `DagId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaNodeRef(u32);

/// The engine-neutral description needed to rebuild one reflected symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MetaSymbol {
    pub name: String,
    pub arity: usize,
    pub associative: bool,
    pub commutative: bool,
    pub iter: bool,
    /// Named compact-successor family that owns this zero symbol.
    pub zero_of: Option<String>,
    /// Object-system roles in `config, object, message, portal` order.
    pub oo: [bool; 4],
}

/// One engine-neutral reflected node.
#[derive(Debug, Clone)]
pub enum MetaNode {
    App {
        symbol: MetaSymbolRef,
        args: Vec<MetaNodeRef>,
    },
    Iter {
        symbol: MetaSymbolRef,
        count: String,
        arg: MetaNodeRef,
    },
    Str {
        symbol: MetaSymbolRef,
        value: Vec<u8>,
    },
    Qid {
        symbol: MetaSymbolRef,
        value: String,
    },
    Float {
        symbol: MetaSymbolRef,
        bits: u64,
    },
    SmtNumber {
        symbol: MetaSymbolRef,
        value: SmtNumber,
    },
}

/// Hook purposes expressed in envelope-local symbol indices.
#[derive(Debug, Clone, Default)]
pub struct MetaHookRefs {
    pub ops: HashMap<String, MetaSymbolRef>,
    pub terms: HashMap<String, MetaSymbolRef>,
}

/// A self-contained graph of reflected META terms.
#[derive(Debug, Clone)]
pub struct MetaEnvelope {
    symbols: Vec<MetaSymbol>,
    nodes: Vec<MetaNode>,
    roots: Vec<MetaNodeRef>,
    hooks: MetaHookRefs,
}

impl MetaEnvelope {
    /// Capture `roots` and the current reflection hook table without retaining an engine handle.
    pub fn capture(ctx: &MetaCtx, roots: &[DagId]) -> Option<Self> {
        let hooks = ctx.meta_hooks()?;
        Self::capture_with_hooks(ctx, &hooks, roots)
    }

    fn capture_with_hooks(ctx: &MetaCtx, hooks: &MetaHooks, roots: &[DagId]) -> Option<Self> {
        struct Capture<'a> {
            ctx: &'a MetaCtx<'a>,
            symbols: Vec<MetaSymbol>,
            symbol_ids: HashMap<SymbolId, MetaSymbolRef>,
            nodes: Vec<MetaNode>,
            node_ids: HashMap<DagId, MetaNodeRef>,
        }

        impl Capture<'_> {
            fn symbol(&mut self, symbol: SymbolId) -> MetaSymbolRef {
                if let Some(&found) = self.symbol_ids.get(&symbol) {
                    return found;
                }
                let found = MetaSymbolRef(self.symbols.len() as u32);
                self.symbols.push(MetaSymbol {
                    name: self.ctx.name(symbol).to_string(),
                    arity: self.ctx.arity(symbol),
                    associative: self.ctx.symbol_is_assoc(symbol),
                    commutative: self.ctx.symbol_is_commutative(symbol),
                    iter: self.ctx.symbol_is_iter(symbol),
                    zero_of: self.ctx.iter_zero_owner(symbol),
                    oo: self.ctx.symbol_oo_roles(symbol),
                });
                self.symbol_ids.insert(symbol, found);
                found
            }

            fn node(&mut self, node: DagId) -> Option<MetaNodeRef> {
                if let Some(&found) = self.node_ids.get(&node) {
                    return Some(found);
                }
                let symbol = self.symbol(self.ctx.top(node));
                let captured = match self.ctx.repr(node) {
                    NodeRepr::App => MetaNode::App {
                        symbol,
                        args: self
                            .ctx
                            .children(node)
                            .into_iter()
                            .map(|child| self.node(child))
                            .collect::<Option<Vec<_>>>()?,
                    },
                    NodeRepr::Iter { count, arg } => MetaNode::Iter {
                        symbol,
                        count,
                        arg: self.node(arg)?,
                    },
                    NodeRepr::Str(value) => MetaNode::Str {
                        symbol,
                        value: value.to_vec(),
                    },
                    NodeRepr::Qid(value) => MetaNode::Qid {
                        symbol,
                        value: value.to_string(),
                    },
                    NodeRepr::Float(value) => MetaNode::Float {
                        symbol,
                        bits: value.to_bits(),
                    },
                    NodeRepr::SmtNum(value) => MetaNode::SmtNumber {
                        symbol,
                        value: value.clone(),
                    },
                    // External-object configurations are ground. Refusing a variable here prevents a
                    // name-code or variable-symbol handle from leaking into transport accidentally.
                    NodeRepr::Var { .. } => return None,
                };
                let found = MetaNodeRef(self.nodes.len() as u32);
                self.nodes.push(captured);
                self.node_ids.insert(node, found);
                Some(found)
            }
        }

        let mut capture = Capture {
            ctx,
            symbols: Vec::new(),
            symbol_ids: HashMap::new(),
            nodes: Vec::new(),
            node_ids: HashMap::new(),
        };

        // Sort by purpose so envelope construction is deterministic even though MetaHooks uses HashMap.
        let mut op_hooks: Vec<_> = hooks.ops.iter().collect();
        op_hooks.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let mut term_hooks: Vec<_> = hooks.terms.iter().collect();
        term_hooks.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let hook_refs = MetaHookRefs {
            ops: op_hooks
                .into_iter()
                .map(|(purpose, &symbol)| (purpose.clone(), capture.symbol(symbol)))
                .collect(),
            terms: term_hooks
                .into_iter()
                .map(|(purpose, &symbol)| (purpose.clone(), capture.symbol(symbol)))
                .collect(),
        };
        let roots = roots
            .iter()
            .map(|&root| capture.node(root))
            .collect::<Option<Vec<_>>>()?;
        Some(Self {
            symbols: capture.symbols,
            nodes: capture.nodes,
            roots,
            hooks: hook_refs,
        })
    }

    pub fn root_count(&self) -> usize {
        self.roots.len()
    }

    pub fn root(&self, index: usize) -> Option<MetaNodeRef> {
        self.roots.get(index).copied()
    }

    pub fn node(&self, node: MetaNodeRef) -> &MetaNode {
        &self.nodes[node.0 as usize]
    }

    pub fn symbol(&self, symbol: MetaSymbolRef) -> &MetaSymbol {
        &self.symbols[symbol.0 as usize]
    }

    pub fn top_symbol(&self, node: MetaNodeRef) -> MetaSymbolRef {
        match self.node(node) {
            MetaNode::App { symbol, .. }
            | MetaNode::Iter { symbol, .. }
            | MetaNode::Str { symbol, .. }
            | MetaNode::Qid { symbol, .. }
            | MetaNode::Float { symbol, .. }
            | MetaNode::SmtNumber { symbol, .. } => *symbol,
        }
    }

    pub fn name(&self, node: MetaNodeRef) -> &str {
        &self.symbol(self.top_symbol(node)).name
    }

    pub fn children(&self, node: MetaNodeRef) -> &[MetaNodeRef] {
        match self.node(node) {
            MetaNode::App { args, .. } => args,
            MetaNode::Iter { arg, .. } => std::slice::from_ref(arg),
            MetaNode::Str { .. }
            | MetaNode::Qid { .. }
            | MetaNode::Float { .. }
            | MetaNode::SmtNumber { .. } => &[],
        }
    }

    pub fn qid(&self, node: MetaNodeRef) -> Option<&str> {
        match self.node(node) {
            MetaNode::Qid { value, .. } => Some(value),
            _ => None,
        }
    }

    pub fn string(&self, node: MetaNodeRef) -> Option<&[u8]> {
        match self.node(node) {
            MetaNode::Str { value, .. } => Some(value),
            _ => None,
        }
    }

    /// Reuse this envelope's owned graph and hook table with `node` as its sole root.
    pub fn rooted_at(&self, node: MetaNodeRef) -> Self {
        Self {
            symbols: self.symbols.clone(),
            nodes: self.nodes.clone(),
            roots: vec![node],
            hooks: self.hooks.clone(),
        }
    }
    /// A deterministic structural key for selected envelope nodes. Symbol names, scalar values, child
    /// order, and node shapes participate; engine-local and envelope-local indices do not.
    pub fn structural_key(&self, roots: &[MetaNodeRef]) -> String {
        fn append(envelope: &MetaEnvelope, node: MetaNodeRef, out: &mut String) {
            use std::fmt::Write as _;
            let symbol = envelope.symbol(envelope.top_symbol(node));
            let _ = write!(out, "{}:{}:", symbol.name.len(), symbol.name);
            match envelope.node(node) {
                MetaNode::App { args, .. } => {
                    let _ = write!(out, "a{}[", args.len());
                    for &arg in args {
                        append(envelope, arg, out);
                    }
                    out.push(']');
                }
                MetaNode::Iter { count, arg, .. } => {
                    let _ = write!(out, "i{}:{}[", count.len(), count);
                    append(envelope, *arg, out);
                    out.push(']');
                }
                MetaNode::Str { value, .. } => {
                    let _ = write!(out, "s{}:", value.len());
                    for byte in value {
                        let _ = write!(out, "{byte:02x}");
                    }
                }
                MetaNode::Qid { value, .. } => {
                    let _ = write!(out, "q{}:{}", value.len(), value);
                }
                MetaNode::Float { bits, .. } => {
                    let _ = write!(out, "f{bits:016x}");
                }
                MetaNode::SmtNumber { value, .. } => {
                    let (numerator, denominator) = value.ratio_parts();
                    let _ = write!(out, "n{}:{numerator}/{denominator}", numerator.len());
                }
            }
            out.push(';');
        }

        let mut key = String::new();
        for &root in roots {
            append(self, root, &mut key);
            key.push('|');
        }
        key
    }

    /// Materialize this envelope in a throwaway engine, run `operation`, and capture its optional result
    /// before that engine is dropped. `R` must itself be engine-neutral; the callback's DAG handles are
    /// scoped to this call.
    pub fn transform<R>(
        &self,
        operation: impl FnOnce(&mut MetaCtx, &MetaHooks, &[DagId]) -> (R, Option<DagId>),
    ) -> Option<(R, Option<MetaEnvelope>)> {
        let mut engine = Engine::default();
        let sort = engine.add_sort("%MetaTransport");
        engine.close_sorts();

        let symbols: Vec<SymbolId> = self
            .symbols
            .iter()
            .map(|symbol| {
                let id = if symbol.iter {
                    engine.add_op_iter(symbol.name.clone(), vec![sort], sort)
                } else if symbol.associative && symbol.commutative {
                    engine.add_op_ac(symbol.name.clone(), vec![sort, sort], sort, None)
                } else if symbol.associative {
                    engine.add_op_au(symbol.name.clone(), vec![sort, sort], sort, None)
                } else if symbol.commutative {
                    engine.add_op_cui(
                        symbol.name.clone(),
                        vec![sort, sort],
                        sort,
                        true,
                        false,
                        None,
                    )
                } else {
                    engine.add_op(
                        symbol.name.clone(),
                        std::iter::repeat_n(sort, symbol.arity).collect(),
                        sort,
                    )
                };
                engine.set_oo_flags(id, symbol.oo[0], symbol.oo[1], symbol.oo[2], symbol.oo[3]);
                id
            })
            .collect();

        let mut nodes = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let built = match node {
                MetaNode::App { symbol, args } => engine.make_node(
                    symbols[symbol.0 as usize],
                    args.iter().map(|arg| nodes[arg.0 as usize]).collect(),
                ),
                MetaNode::Iter { symbol, count, arg } => engine.make_iter_decimal(
                    symbols[symbol.0 as usize],
                    count,
                    nodes[arg.0 as usize],
                )?,
                MetaNode::Str { symbol, value } => {
                    engine.make_string(symbols[symbol.0 as usize], value)
                }
                MetaNode::Qid { symbol, value } => {
                    engine.make_qid(symbols[symbol.0 as usize], value)
                }
                MetaNode::Float { symbol, bits } => {
                    engine.make_float(symbols[symbol.0 as usize], f64::from_bits(*bits))
                }
                MetaNode::SmtNumber { symbol, value } => {
                    engine.make_smt_number(symbols[symbol.0 as usize], value.clone())
                }
            };
            nodes.push(built);
        }
        let roots: Vec<DagId> = self
            .roots
            .iter()
            .map(|root| nodes[root.0 as usize])
            .collect();
        let hooks = MetaHooks {
            ops: self
                .hooks
                .ops
                .iter()
                .map(|(purpose, symbol)| (purpose.clone(), symbols[symbol.0 as usize]))
                .collect(),
            terms: self
                .hooks
                .terms
                .iter()
                .map(|(purpose, symbol)| (purpose.clone(), symbols[symbol.0 as usize]))
                .collect(),
        };

        engine.with_meta_ctx(|ctx| {
            let (value, response) = operation(ctx, &hooks, &roots);
            let response = match response {
                Some(root) => Some(Self::capture_with_hooks(ctx, &hooks, &[root])?),
                None => None,
            };
            Some((value, response))
        })
    }

    pub(crate) fn build_roots(&self, ctx: &mut MetaCtx) -> Option<(Vec<DagId>, Vec<RootGuard>)> {
        let hooks = ctx.meta_hooks()?;
        let mut hook_symbol = HashMap::<MetaSymbolRef, SymbolId>::new();
        for (purpose, &symbol) in &self.hooks.ops {
            if let Some(&current) = hooks.ops.get(purpose) {
                hook_symbol.entry(symbol).or_insert(current);
            }
        }
        for (purpose, &symbol) in &self.hooks.terms {
            if let Some(&current) = hooks.terms.get(purpose) {
                hook_symbol.entry(symbol).or_insert(current);
            }
        }
        let symbols = self
            .symbols
            .iter()
            .enumerate()
            .map(|(index, symbol)| {
                let portable = MetaSymbolRef(index as u32);
                hook_symbol.get(&portable).copied().or_else(|| {
                    if let Some(owner) = &symbol.zero_of {
                        ctx.resolve_iter_zero(owner)
                    } else if symbol.iter {
                        ctx.resolve_iter(&symbol.name)
                    } else {
                        ctx.resolve_op_with_oo(&symbol.name, symbol.arity, symbol.oo)
                    }
                })
            })
            .collect::<Option<Vec<_>>>()?;
        self.build_roots_with_symbols(ctx, &symbols, Some(&hook_symbol))
    }

    fn build_roots_with_symbols(
        &self,
        ctx: &mut MetaCtx,
        symbols: &[SymbolId],
        fixed_symbols: Option<&HashMap<MetaSymbolRef, SymbolId>>,
    ) -> Option<(Vec<DagId>, Vec<RootGuard>)> {
        // Every intermediate is pinned until all parents have been constructed. This is required when
        // in-reduction GC is enabled: envelope materialization may itself cross a collection threshold.
        let mut building_roots = Vec::with_capacity(self.nodes.len());
        let mut nodes = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let built = match node {
                MetaNode::App { symbol, args } => {
                    let args: Vec<_> = args.iter().map(|arg| nodes[arg.0 as usize]).collect();
                    let fallback = symbols[symbol.0 as usize];
                    let resolved = if fixed_symbols.is_some_and(|fixed| fixed.contains_key(symbol))
                    {
                        fallback
                    } else if fixed_symbols.is_some() {
                        let descriptor = &self.symbols[symbol.0 as usize];
                        ctx.resolve_op_with_oo_for_args(
                            &descriptor.name,
                            descriptor.arity,
                            descriptor.oo,
                            &args,
                        )
                        .unwrap_or(fallback)
                    } else {
                        fallback
                    };
                    ctx.app(resolved, args)
                }
                MetaNode::Iter { symbol, count, arg } => {
                    ctx.make_iter_decimal(symbols[symbol.0 as usize], count, nodes[arg.0 as usize])?
                }
                MetaNode::Str { symbol, value } => ctx.make_na(
                    symbols[symbol.0 as usize],
                    NaValue::Str(value.clone().into()),
                ),
                MetaNode::Qid { symbol, value } => ctx.make_na(
                    symbols[symbol.0 as usize],
                    NaValue::Qid(value.clone().into()),
                ),
                MetaNode::Float { symbol, bits } => {
                    ctx.make_na(symbols[symbol.0 as usize], NaValue::Float(*bits))
                }
                MetaNode::SmtNumber { symbol, value } => ctx.make_na(
                    symbols[symbol.0 as usize],
                    NaValue::SmtNum(std::rc::Rc::new(value.clone())),
                ),
            };
            nodes.push(built);
            building_roots.push(ctx.pin(built));
        }
        let roots: Vec<DagId> = self
            .roots
            .iter()
            .map(|root| nodes[root.0 as usize])
            .collect();
        let root_guards = roots.iter().map(|&root| ctx.pin(root)).collect();
        Some((roots, root_guards))
    }
}

/// Persistent, engine-neutral META transport owned by one local interpreter. Its private engine keeps
/// cross-request reflection caches valid while its public API exposes only owned envelopes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TransportSymbol {
    descriptor: MetaSymbol,
    /// META hooks are the portable identity of overloaded constructors such as the several `_;_`
    /// operators. Without this discriminator, a universal-sort transport aliases `Substitution`,
    /// `Configuration`, and declaration-set constructors that happen to share name and arity.
    purposes: Vec<String>,
}

pub struct MetaTransport {
    engine: Engine,
    sort: SortId,
    symbols: HashMap<TransportSymbol, SymbolId>,
    hooks: MetaHooks,
}

impl MetaTransport {
    /// Create a transport from the first request and predeclare protocol response operators. Generic
    /// `%externalCallN` wrappers let upper layers invoke existing META descent handlers with a sliced
    /// argument list without adding a second implementation of those operations.
    pub fn new(seed: &MetaEnvelope, protocol_ops: &[(&str, usize, bool)]) -> Self {
        let mut engine = Engine::default();
        let sort = engine.add_sort("%MetaTransport");
        engine.close_sorts();
        let mut transport = Self {
            engine,
            sort,
            symbols: HashMap::new(),
            hooks: MetaHooks::default(),
        };
        transport.ensure_envelope(seed);
        for &(name, arity, message) in protocol_ops {
            transport.ensure_symbol(
                &MetaSymbol {
                    name: name.to_string(),
                    arity,
                    associative: false,
                    commutative: false,
                    iter: false,
                    zero_of: None,
                    oo: [false, false, message, false],
                },
                &[],
            );
        }
        // The first `createInterpreter` request contains no protocol count, but its reply must construct
        // `interpreter(0)`. Later child IDs and RewriteCount replies use the same Peano family.
        for descriptor in [
            MetaSymbol {
                name: "0".to_string(),
                arity: 0,
                associative: false,
                commutative: false,
                iter: false,
                zero_of: Some("s_".to_string()),
                oo: [false; 4],
            },
            MetaSymbol {
                name: "s_".to_string(),
                arity: 1,
                associative: false,
                commutative: false,
                iter: true,
                zero_of: None,
                oo: [false; 4],
            },
        ] {
            transport.ensure_symbol(&descriptor, &[]);
        }
        for arity in 0..=12 {
            transport.ensure_symbol(
                &MetaSymbol {
                    name: format!("%externalCall{arity}"),
                    arity,
                    associative: false,
                    commutative: false,
                    iter: false,
                    zero_of: None,
                    oo: [false; 4],
                },
                &[],
            );
        }
        transport.register_zero_owners();
        transport
    }

    fn ensure_symbol(&mut self, descriptor: &MetaSymbol, purposes: &[String]) -> SymbolId {
        let key = TransportSymbol {
            descriptor: descriptor.clone(),
            purposes: purposes.to_vec(),
        };
        if let Some(&symbol) = self.symbols.get(&key) {
            return symbol;
        }
        let symbol = if descriptor.iter {
            self.engine
                .add_op_iter(descriptor.name.clone(), vec![self.sort], self.sort)
        } else if descriptor.associative && descriptor.commutative {
            self.engine.add_op_ac(
                descriptor.name.clone(),
                vec![self.sort, self.sort],
                self.sort,
                None,
            )
        } else if descriptor.associative {
            self.engine.add_op_au(
                descriptor.name.clone(),
                vec![self.sort, self.sort],
                self.sort,
                None,
            )
        } else if descriptor.commutative {
            self.engine.add_op_cui(
                descriptor.name.clone(),
                vec![self.sort, self.sort],
                self.sort,
                true,
                false,
                None,
            )
        } else {
            self.engine.add_op(
                descriptor.name.clone(),
                std::iter::repeat_n(self.sort, descriptor.arity).collect(),
                self.sort,
            )
        };
        self.engine.set_oo_flags(
            symbol,
            descriptor.oo[0],
            descriptor.oo[1],
            descriptor.oo[2],
            descriptor.oo[3],
        );
        self.symbols.insert(key, symbol);
        symbol
    }

    /// Restore compact-successor zero attachments erased by the engine-neutral symbol descriptors.
    /// Response counts and variant parent indices are built inside this private transport.
    fn register_zero_owners(&mut self) {
        let zeros: Vec<_> = self
            .symbols
            .iter()
            .filter_map(|(key, &zero)| {
                key.descriptor
                    .zero_of
                    .as_ref()
                    .map(|owner| (zero, owner.clone()))
            })
            .collect();
        for (zero, owner) in zeros {
            if let Some(successor) = self.symbols.iter().find_map(|(key, &symbol)| {
                (key.descriptor.iter && key.descriptor.name == owner).then_some(symbol)
            }) {
                self.engine.register_succ_zero(successor, zero);
            }
        }
    }

    fn ensure_envelope(&mut self, envelope: &MetaEnvelope) -> Vec<SymbolId> {
        let mut purposes = HashMap::<MetaSymbolRef, Vec<String>>::new();
        for (purpose, &symbol) in &envelope.hooks.ops {
            purposes
                .entry(symbol)
                .or_default()
                .push(format!("op:{purpose}"));
        }
        for (purpose, &symbol) in &envelope.hooks.terms {
            purposes
                .entry(symbol)
                .or_default()
                .push(format!("term:{purpose}"));
        }
        for identities in purposes.values_mut() {
            identities.sort_unstable();
        }
        let mut symbols = Vec::with_capacity(envelope.symbols.len());
        for (index, descriptor) in envelope.symbols.iter().enumerate() {
            let identities = purposes
                .get(&MetaSymbolRef(index as u32))
                .map(Vec::as_slice)
                .unwrap_or_default();
            symbols.push(self.ensure_symbol(descriptor, identities));
        }
        for (purpose, symbol) in &envelope.hooks.ops {
            self.hooks
                .ops
                .insert(purpose.clone(), symbols[symbol.0 as usize]);
        }
        for (purpose, symbol) in &envelope.hooks.terms {
            self.hooks
                .terms
                .insert(purpose.clone(), symbols[symbol.0 as usize]);
        }
        self.register_zero_owners();
        symbols
    }

    /// Materialize all inputs in this transport, run one callback, and capture its optional reply before
    /// releasing any request roots. Callback DAGs are scoped to this call and cannot enter the response.
    pub fn transact<R>(
        &mut self,
        inputs: &[&MetaEnvelope],
        operation: impl FnOnce(&mut MetaCtx, &MetaHooks, &[Vec<DagId>]) -> Option<(R, Option<DagId>)>,
    ) -> Option<(R, Option<MetaEnvelope>)> {
        let mappings: Vec<Vec<SymbolId>> = inputs
            .iter()
            .map(|envelope| self.ensure_envelope(envelope))
            .collect();
        let hooks = self.hooks.clone();
        self.engine.with_meta_ctx(|ctx| {
            let mut input_roots = Vec::with_capacity(inputs.len());
            let mut input_guards = Vec::new();
            for (envelope, symbols) in inputs.iter().zip(&mappings) {
                let (roots, guards) = envelope.build_roots_with_symbols(ctx, symbols, None)?;
                input_roots.push(roots);
                input_guards.extend(guards);
            }
            let (value, response) = operation(ctx, &hooks, &input_roots)?;
            let response = match response {
                Some(root) => Some(MetaEnvelope::capture_with_hooks(ctx, &hooks, &[root])?),
                None => None,
            };
            drop(input_guards);
            Some((value, response))
        })
    }
}

/// Opaque identity of one suspended external request in a [`Rewriting`](crate::rewrite::Rewriting).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternalRequestToken(pub(crate) u64);

/// Opaque registration for an external target rooted inside one parent engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternalTargetToken(pub(crate) u64);

/// Breakdown subcounts transferred with an external response. They classify work already included in
/// [`ExternalResponse::rewrites`]; they never add to the aggregate independently.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ExternalRewriteBreakdown {
    pub membership_applications: u64,
    pub rule_rewrites: u64,
    pub variant_narrowing_steps: u64,
    pub narrowing_steps: u64,
}

/// An accepted external request result. `reply` is rebuilt only after child computation is complete.
#[derive(Debug, Clone)]
pub struct ExternalResponse {
    pub reply: Option<MetaEnvelope>,
    pub rewrites: u64,
    pub breakdown: ExternalRewriteBreakdown,
}
