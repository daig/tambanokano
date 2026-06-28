//! META-LEVEL descent (Phase 3.1) — the [`DescentOps`] implementation.
//!
//! A descent redex (`metaReduce`/…) hands control here via the kernel's [`MetaCtx`] seam. [`MetaDescent`]
//! holds the module database + interner, so it can **down**-translate the meta-module argument into a real
//! object [`LoadedModule`] (a `PreModule` reconstructed from the meta-term, then the ordinary
//! flatten+build pipeline), down-translate the subject meta-term into that module, run the engine
//! operation, and **up**-translate the result back into the meta-level engine (via `ctx`).
//!
//! Scope so far: `metaReduce`/`metaNormalize` over a module given as an **import expression**
//! (`[Q]` = `sth Q is including Q . … endsth`, the `['NAT]`/`['BOOL]` form) — its sorts/ops/equations come
//! from the imported, db-resolved modules. A meta-module with *inline* declarations (what `upModule`
//! emits) is a follow-on (`down_module` returns `None` for it → the redex stays at the kind level).

use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::descent::{DescentOps, MetaCtx};
use tnk_core::symbol::{MetaHooks, MetaOp};
use tnk_frontend::lex::Interner;
use tnk_frontend::load::{build_loaded_module, LoadedModule};
use tnk_frontend::sig::syntax::BuiltModule;
use tnk_frontend::surface::ast::{Import, ImportMode, ModuleExpr, ModuleKind, PreModule};

use crate::db::ModuleDb;
use crate::flatten::flatten_pre;
use crate::view::ViewDb;

/// The descent handler: the module database/views (to resolve a meta-module's imports) and the interner
/// (to build the object module). Constructed per reduce command and threaded into `reduce_with`.
pub struct MetaDescent<'a> {
    pub interner: &'a mut Interner,
    pub db: &'a ModuleDb,
    pub views: &'a ViewDb,
}

impl DescentOps for MetaDescent<'_> {
    fn descend(
        &mut self,
        ctx: &mut MetaCtx,
        op: MetaOp,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        match op {
            // `metaReduce` and `metaNormalize` differ only in whether membership/sort computation runs;
            // our `reduce` already computes sorts, so both map to the same object reduction here.
            MetaOp::Reduce | MetaOp::Normalize => self.meta_reduce(ctx, hooks, redex),
            _ => None, // other descent functions: Stage 3/4 (or Deferred)
        }
    }
}

impl MetaDescent<'_> {
    /// `metaReduce(M, T)` → `{up(t'), up(leastSort(t'))}` where `t'` is `down(T)` reduced in `down(M)`.
    /// The object reduction's rewrite count is folded into the current command's total (Maude's count).
    fn meta_reduce(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        let subj = down_term(ctx, hooks, kids[1], &mut loaded.built)?;
        loaded.built.engine.reset_rewrites();
        let result = loaded.built.engine.reduce(subj);
        ctx.add_rewrites(loaded.built.engine.rewrites());
        let ut = up_term(ctx, hooks, &loaded.built, result);
        let us = up_sort(ctx, hooks, &loaded.built, result);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// Down-translate a meta-module term to an object [`LoadedModule`]: reconstruct its `PreModule`, then
    /// run the ordinary flatten (against the db) + build. Handles the **import-expression** form (sorts/
    /// ops/equations all `none`, e.g. `[Q]`); a meta-module with inline declarations returns `None`.
    fn down_module(
        &mut self,
        ctx: &MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
    ) -> Option<LoadedModule> {
        let ctor = ctx.name(ctx.top(m)).to_string();
        let (kind, is_theory) = module_kind(&ctor)?;
        let kids = ctx.children(m);
        // Layout (every constructor): [Header, ImportList, SortSet, SubsortDeclSet, OpDeclSet, MembAxSet,
        // EquationSet, (RuleSet), (StratDeclSet, StratDefSet)]. We need the import list (index 1); the
        // declaration children (2..) must all be the empty constant for this import-only path.
        let imports_dag = *kids.get(1)?;
        for &decl in kids.get(2..)? {
            if !is_empty_decl(ctx, hooks, decl) {
                return None; // inline declarations — full down_module is a follow-on
            }
        }
        let imports = down_imports(ctx, hooks, imports_dag)?;
        let pm = PreModule {
            name: "%META%".to_string(),
            kind,
            is_theory,
            params: Vec::new(),
            imports,
            sorts: Vec::new(),
            subsorts: Vec::new(),
            ops: Vec::new(),
            vars: Vec::new(),
            statements: Vec::new(),
        };
        let flat = flatten_pre(&pm, self.db, self.views, self.interner).ok()?;
        build_loaded_module(&flat, self.interner).ok()
    }
}

/// The (kind, is_theory) of a module-constructor operator name (`fmod_is_sorts_.____endfm`, `sth_…`, …).
fn module_kind(ctor: &str) -> Option<(ModuleKind, bool)> {
    if ctor.starts_with("fmod") {
        Some((ModuleKind::Functional, false))
    } else if ctor.starts_with("fth") {
        Some((ModuleKind::Functional, true))
    } else if ctor.starts_with("smod") || ctor.starts_with("mod") {
        Some((ModuleKind::System, false))
    } else if ctor.starts_with("sth") || ctor.starts_with("th") {
        Some((ModuleKind::System, true))
    } else {
        None
    }
}

/// Whether `decl` is an empty declaration set (`none`/`nil` — one of the `emptyXSymbol` hooks).
fn is_empty_decl(ctx: &MetaCtx, hooks: &MetaHooks, decl: DagId) -> bool {
    let sym = ctx.top(decl);
    [
        "emptySortSetSymbol",
        "emptySubsortDeclSetSymbol",
        "emptyOpDeclSetSymbol",
        "emptyMembAxSetSymbol",
        "emptyEquationSetSymbol",
        "emptyRuleSetSymbol",
        "emptyStratDeclSetSymbol",
        "emptyStratDefSetSymbol",
    ]
    .iter()
    .any(|h| hooks.ops.get(*h) == Some(&sym))
}

/// Down-translate an `ImportList` (`__`-flattened `including_.`/`protecting_.`/`extending_.` of a module
/// expression) to a list of [`Import`]s. Only a **named** module expression (a `Qid`) is handled.
fn down_imports(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Option<Vec<Import>> {
    let nil = hooks.ops.get("nilImportListSymbol").copied();
    let cons = hooks.ops.get("importListSymbol").copied();
    let mut out = Vec::new();
    let mut stack = vec![list];
    while let Some(d) = stack.pop() {
        let sym = ctx.top(d);
        if Some(sym) == nil {
            continue;
        }
        if Some(sym) == cons {
            // `__` import list — recurse into its elements (children are already flattened by the AU rep).
            stack.extend(ctx.children(d));
            continue;
        }
        out.push(down_import(ctx, hooks, d)?);
    }
    out.reverse();
    Some(out)
}

/// Down-translate one import `including_./protecting_./extending_.(ModuleExpr)`.
fn down_import(ctx: &MetaCtx, hooks: &MetaHooks, imp: DagId) -> Option<Import> {
    let sym = ctx.top(imp);
    let mode = if hooks.ops.get("protectingSymbol") == Some(&sym) {
        ImportMode::Protecting
    } else if hooks.ops.get("extendingSymbol") == Some(&sym) {
        ImportMode::Extending
    } else if hooks.ops.get("includingSymbol") == Some(&sym)
        || hooks.ops.get("generatedBySymbol") == Some(&sym)
    {
        ImportMode::Including
    } else {
        return None;
    };
    let expr = *ctx.children(imp).first()?;
    Some(Import { mode, expr: down_module_expr(ctx, expr)? })
}

/// Down-translate a module expression. Only a named module (a `Qid` leaf) is handled here.
fn down_module_expr(ctx: &MetaCtx, e: DagId) -> Option<ModuleExpr> {
    match ctx.repr(e) {
        NodeRepr::Qid(name) => Some(ModuleExpr::Named(name.to_string())),
        _ => None,
    }
}

// ---- down/up of terms ----

/// Down-translate a meta-term into a DAG in `target` (the object module). Handles a constant `'c.S`
/// (a `Qid` leaf), an application `'f[args]` (a `metaTermSymbol` node), and the iterated form `'s_^n[t]`.
fn down_term(ctx: &MetaCtx, hooks: &MetaHooks, t: DagId, target: &mut BuiltModule) -> Option<DagId> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    match ctx.repr(t) {
        NodeRepr::Qid(text) => down_constant(text, target),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let head = match ctx.repr(*kids.first()?) {
                NodeRepr::Qid(s) => s.to_string(),
                _ => return None,
            };
            let args = down_arglist(ctx, hooks, *kids.get(1)?, target)?;
            build_app(&head, args, target)
        }
        _ => None,
    }
}

/// Down-translate a `metaTermSymbol` argument list — a `metaArgSymbol` (`_,_`) AU node flattens to its
/// elements; anything else is a single argument.
fn down_arglist(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    list: DagId,
    target: &mut BuiltModule,
) -> Option<Vec<DagId>> {
    let arg_sym = hooks.ops.get("metaArgSymbol").copied();
    if Some(ctx.top(list)) == arg_sym {
        ctx.children(list).into_iter().map(|c| down_term(ctx, hooks, c, target)).collect()
    } else {
        Some(vec![down_term(ctx, hooks, list, target)?])
    }
}

/// Build a constant from a meta `'name.sort` (a `Qid` leaf): look up the arity-0 operator `name`.
fn down_constant(text: &str, target: &mut BuiltModule) -> Option<DagId> {
    let (name, _sort) = text.rsplit_once('.')?;
    let sym = *target.ops.get(&(name.to_string(), 0))?;
    Some(target.engine.make_const(sym))
}

/// Build an application from a meta op-name + down-translated args. An iterated name `base^n` builds the
/// `iter` successor `base^n(arg)`; otherwise the operator is looked up by `(name, arity)`.
fn build_app(head: &str, args: Vec<DagId>, target: &mut BuiltModule) -> Option<DagId> {
    if let Some((base, count)) = head.rsplit_once('^')
        && let Ok(n) = count.parse::<u64>()
    {
        let sym = *target.ops.get(&(base.to_string(), 1))?;
        return Some(target.engine.make_iter(sym, n, *args.first()?));
    }
    let sym = *target.ops.get(&(head.to_string(), args.len()))?;
    Some(target.engine.make_node(sym, args))
}

/// Up-translate an object DAG `t` (in `source`) into a meta-term built in `ctx`.
fn up_term(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match source.engine.node(t).repr() {
        NodeRepr::App => {
            let sym = source.engine.node(t).symbol();
            let name = source.engine.symbol(sym).name().to_string();
            let kids: Vec<DagId> = source.engine.node(t).children().collect();
            if kids.is_empty() {
                // a constant → `'name.sort`
                let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
                ctx.make_na(qid, NaValue::Qid(format!("{name}.{sort}").into()))
            } else {
                let up_args: Vec<DagId> = kids.iter().map(|&k| up_term(ctx, hooks, source, k)).collect();
                let arglist = up_arglist(ctx, hooks, up_args);
                let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
                ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
            }
        }
        NodeRepr::Iter { count, arg } => {
            // `'base^count[up(arg)]` — `^count` only when count > 1 (`s^1` is `'s_[…]`).
            let base = source.engine.symbol(source.engine.node(t).symbol()).name().to_string();
            let head = if count == "1" { base } else { format!("{base}^{count}") };
            let up_arg = up_term(ctx, hooks, source, arg);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
        // String/float constants up to `'"s".String` / `'f.Float`; bare qids to `''q.Sort` — these need
        // the value-dependent classification and are not reached by NAT/BOOL reduction (a follow-on).
        NodeRepr::Str(_) | NodeRepr::Qid(_) | NodeRepr::Float(_) => {
            let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
            ctx.make_na(qid, NaValue::Qid(format!("?.{sort}").into()))
        }
    }
}

/// Join up-translated arguments into a `metaTermSymbol` argument list: a single argument stays itself; two
/// or more become a `metaArgSymbol` (`_,_`) list.
fn up_arglist(ctx: &mut MetaCtx, hooks: &MetaHooks, args: Vec<DagId>) -> DagId {
    if args.len() == 1 {
        args.into_iter().next().unwrap()
    } else {
        ctx.app(hooks.ops["metaArgSymbol"], args)
    }
}

/// Up-translate the least sort of `t` (in `source`) to its meta `Type` — a `Qid` of the sort name.
fn up_sort(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = source.engine.sorts().name(source.engine.sort_of(t)).to_string();
    ctx.make_na(qid, NaValue::Qid(sort.into()))
}
