//! Flatten an import closure into one combined [`PreModule`] — a pure `PreModule → PreModule` transform.
//!
//! Resolve a module's transitive imports (depth-first, **imports before the importer** — matching Maude's
//! donation order, which is what makes rewrite counts conform), merging every module's declarations into
//! one accumulator. Each module is included **exactly once** (a `visited` set keyed by the canonical
//! module expression) so diamonds (`M` imports `A` and `B`, both importing `BASE`) don't duplicate `BASE`.
//! Sorts and variable names are de-duplicated (the frontend's `add_sort` and per-variable grammar
//! production don't dedup); ops/subsorts/statements are appended (the frontend's `(name, arity)` map folds
//! same-name op declarations into overloads). The combined module's own `imports` is empty — it is fully
//! resolved — so the unchanged frontend `build_loaded_module` builds it directly.

use std::collections::{HashMap, HashSet};
use tnk_frontend::lex::{Interner, Token};
use tnk_frontend::surface::ast::{
    ModuleExpr, ModuleKind, OpDecl, OpMap, PreModule, RenameItem, Statement, VarDecl, ViewDecl,
};

use crate::db::ModuleDb;
use crate::rename::apply_renaming;
use crate::view::ViewDb;

/// The renamable declaration bundle of a (sub-)module expression — everything a renaming `* (…)` rewrites.
#[derive(Debug)]
pub struct FlatDecls {
    pub sorts: Vec<String>,
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
}

/// Accumulates merged declarations, de-duplicating sorts and variable names.
#[derive(Default)]
struct Acc {
    sorts: Vec<String>,
    sort_set: HashSet<String>,
    subsorts: Vec<Vec<Vec<String>>>,
    ops: Vec<OpDecl>,
    vars: Vec<VarDecl>,
    var_set: HashSet<String>,
    statements: Vec<Statement>,
}

impl Acc {
    /// Merge a declaration bundle: new sorts/var-names once each, everything else appended.
    fn add(&mut self, d: FlatDecls) {
        for s in d.sorts {
            if self.sort_set.insert(s.clone()) {
                self.sorts.push(s);
            }
        }
        self.subsorts.extend(d.subsorts);
        self.ops.extend(d.ops);
        for v in d.vars {
            let names: Vec<String> =
                v.names.into_iter().filter(|n| self.var_set.insert(n.clone())).collect();
            if !names.is_empty() {
                self.vars.push(VarDecl { names, sort: v.sort });
            }
        }
        self.statements.extend(d.statements);
    }

    fn into_decls(self) -> FlatDecls {
        FlatDecls {
            sorts: self.sorts,
            subsorts: self.subsorts,
            ops: self.ops,
            vars: self.vars,
            statements: self.statements,
        }
    }
}

/// The declaration bundle a module contributes *itself* (excludes its imports — those are collected
/// separately, before it).
fn own_decls(pm: &PreModule) -> FlatDecls {
    FlatDecls {
        sorts: pm.sorts.clone(),
        subsorts: pm.subsorts.clone(),
        ops: pm.ops.clone(),
        vars: pm.vars.clone(),
        statements: pm.statements.clone(),
    }
}

/// Flatten module `name`'s import closure into one combined [`PreModule`] named `name` (empty imports).
/// `views` resolves any parameterized instantiation `M{V}` reached in the closure (B-iv).
pub fn flatten(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<PreModule, String> {
    let mut acc = Acc::default();
    let mut visited = HashSet::new();
    collect_named(name, db, views, &mut acc, &mut visited, interner)?;
    // The flattened module is the root module with its imports inlined, so it keeps the root's kind
    // (`mod` stays a system module — its rules survive flattening) and its theory flag.
    let (kind, is_theory) =
        db.get(name).map(|pm| (pm.kind, pm.is_theory)).unwrap_or((ModuleKind::Functional, false));
    let d = acc.into_decls();
    Ok(PreModule {
        name: name.to_string(),
        kind,
        is_theory,
        // The flattened module is fully resolved: each parameter's copy (its `X$s` sorts) is inlined, so
        // no formal parameters remain.
        params: Vec::new(),
        imports: Vec::new(),
        sorts: d.sorts,
        subsorts: d.subsorts,
        ops: d.ops,
        vars: d.vars,
        statements: d.statements,
    })
}

fn collect_named(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
) -> Result<(), String> {
    if !visited.insert(name.to_string()) {
        return Ok(()); // already merged (diamond)
    }
    let pm = db.get(name).ok_or_else(|| format!("imported module `{name}` is not defined"))?;
    // Parameter copies first (a parameter `X :: T` behaves like an import of a renamed `T`), then the
    // regular imports, then the module's own declarations.
    let params: Vec<(String, String)> =
        pm.params.iter().map(|p| (p.name.clone(), p.theory.clone())).collect();
    for (param, theory) in &params {
        add_parameter_copy(param, theory, db, views, acc, interner)?;
    }
    // The module's own parameters are in scope for its imports: an import `LIST{X}` of a parameter `X`
    // is a *by-parameter* instantiation (Axis-A5 kind 2) — `X` is not a view. Standalone (here) its
    // parameters stay free, so the imports are collected unsubstituted with `X` in scope.
    let scope: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
    for imp in &pm.imports {
        collect_expr(&imp.expr, db, views, acc, visited, interner, &scope)?;
    }
    let pm = db.get(name).expect("present"); // re-borrow after the parameter-copy recursion
    acc.add(own_decls(pm)); // the module's own declarations, after its imports
    Ok(())
}

/// Add a parameter copy of theory `theory` under parameter name `param`: flatten the theory and rename
/// every one of its sorts `s` to the parameter sort `param$s` (Maude's `makeParameterCopy`), so the
/// importing module's body can refer to `X$Elt` and to parameterized sorts. The renaming runs in a fresh
/// scope (a parameter copy is independent of any unrenamed import of the same theory).
///
/// Only **theory-declared** sorts are renamed (A4): a sort the theory gets from an imported *module*
/// (`protecting BOOL` → `Bool`) keeps its name (Maude only qualifies theory-declared sorts as `X$s`), so the
/// body's references to it resolve to the shared module sort.
fn add_parameter_copy(
    param: &str,
    theory: &str,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    interner: &mut Interner,
) -> Result<(), String> {
    let mut tmp = Acc::default();
    let mut tmp_visited = HashSet::new();
    collect_named(theory, db, views, &mut tmp, &mut tmp_visited, interner)?;
    let decls = tmp.into_decls();
    // The sorts that came from an imported module — not renamed.
    let mut module_sorts = HashSet::new();
    module_origin_sorts(theory, db, views, interner, &mut HashSet::new(), &mut module_sorts)?;
    let items: Vec<RenameItem> = decls
        .sorts
        .iter()
        .filter(|s| !module_sorts.contains(s.as_str()))
        .map(|s| RenameItem::Sort { from: s.clone(), to: format!("{param}${s}") })
        .collect();
    let renamed = apply_renaming(decls, &items, interner)?;
    acc.add(renamed);
    Ok(())
}

/// Collect the sorts theory `name` inherits from an imported **module** (vs. a theory) — recursively, so a
/// theory that includes another theory inherits *that* theory's module-origin sorts. These are excluded
/// from the parameter-copy renaming (A4). Only `Named` imports are considered (a renamed/instantiated
/// theory import is a follow-up).
fn module_origin_sorts(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
    seen: &mut HashSet<String>,
    out: &mut HashSet<String>,
) -> Result<(), String> {
    if !seen.insert(name.to_string()) {
        return Ok(());
    }
    let Some(pm) = db.get(name) else { return Ok(()) };
    let imports: Vec<ModuleExpr> = pm.imports.iter().map(|imp| imp.expr.clone()).collect();
    for imp in &imports {
        let ModuleExpr::Named(n) = imp else { continue };
        if db.get(n).is_some_and(|m| m.is_theory) {
            module_origin_sorts(n, db, views, interner, seen, out)?; // an imported theory
        } else {
            // An imported module: every sort in its closure is module-origin.
            let flat = flatten(n, db, views, interner)?;
            out.extend(flat.sorts);
        }
    }
    Ok(())
}

fn collect_expr(
    expr: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
    scope: &[String],
) -> Result<(), String> {
    match expr {
        ModuleExpr::Named(n) => collect_named(n, db, views, acc, visited, interner),
        ModuleExpr::Sum(a, b) => {
            collect_expr(a, db, views, acc, visited, interner, scope)?;
            collect_expr(b, db, views, acc, visited, interner, scope)
        }
        ModuleExpr::Rename(inner, items) => {
            // `A * (R)` is a distinct module from `A`: key it by its canonical form so it merges once,
            // and flatten `inner` in a fresh scope (the renamed content is independent of the unrenamed).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mut tmp = Acc::default();
            let mut tmp_visited = HashSet::new();
            collect_expr(inner, db, views, &mut tmp, &mut tmp_visited, interner, scope)?;
            let renamed = apply_renaming(tmp.into_decls(), items, interner)?;
            acc.add(renamed);
            Ok(())
        }
        ModuleExpr::Instantiation(base, args) => {
            // `M{A, …}` merges once (keyed by its canonical instance name `M{A, …}`).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mname = match &**base {
                ModuleExpr::Named(n) => n.as_str(),
                _ => return Err("the base of an instantiation must be a named module (a nested \
                                 instantiation / renaming base is a follow-up)"
                    .into()),
            };
            instantiate(mname, args, db, views, acc, visited, interner, scope)
        }
    }
}

/// Instantiate the parameterized module `mname` with one argument per parameter, against the enclosing
/// parameter `scope`. Each argument is resolved ([`resolve_arg`]) to a view (kind 3) or a by-parameter
/// binding (kind 2); a view's target is imported, `mname`'s imports are re-instantiated with the bound
/// parameters substituted in (`LIST{X}` with `X ↦ ToN` ⇒ `LIST{ToN}`), and `mname`'s own declarations are
/// merged under the binding — `X$s ↦` the view's sort image of `s` (or `p$s` by parameter), a structured
/// sort `Base{…X…} ↦ Base{…argument name…}` (Maude's instance naming), the view operator maps (A1), and
/// each variable inlined as a colon variable at its instantiated sort.
#[allow(clippy::too_many_arguments)]
fn instantiate(
    mname: &str,
    args: &[ModuleExpr],
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
    scope: &[String],
) -> Result<(), String> {
    let pm = db.get(mname).ok_or_else(|| format!("instantiated module `{mname}` is not defined"))?;
    if pm.params.len() != args.len() {
        return Err(format!(
            "instantiation `{mname}{{…}}` has {} argument(s) but `{mname}` has {} parameter(s)",
            args.len(),
            pm.params.len()
        ));
    }

    // Resolve each argument (against `scope`, so an enclosing parameter is a by-parameter argument rather
    // than a view). A view argument imports its target and binds the parameter to its sort image; a
    // by-parameter argument imports nothing and binds the parameter to a prefix-rename `X$s ↦ p$s`.
    let mut bindings: HashMap<String, ParamBinding> = HashMap::new();
    let mut op_subst: HashMap<String, Vec<Token>> = HashMap::new();
    let mut param_to_arg: HashMap<String, ModuleExpr> = HashMap::new();
    for (param, arg) in pm.params.iter().zip(args) {
        let r = resolve_arg(arg, views, interner, scope)
            .map_err(|e| format!("instantiation `{mname}{{…}}`: {e}"))?;
        if let Some(target) = &r.target {
            collect_expr(target, db, views, acc, visited, interner, scope)?;
        }
        op_subst.extend(r.op_subst);
        param_to_arg.insert(param.name.clone(), arg.clone());
        bindings.insert(param.name.clone(), r.binding);
    }

    // `M`'s regular imports with the parameter substitution applied (a bound parameter `X` in an import
    // `LIST{X}` becomes its argument — `LIST{ToN}` for a view, `LIST{Y}` for an enclosing parameter), then
    // its own declarations under the binding. Deduped via `visited`.
    let imports: Vec<ModuleExpr> =
        pm.imports.iter().map(|imp| subst_params_in_expr(&imp.expr, &param_to_arg)).collect();
    for imp in &imports {
        collect_expr(imp, db, views, acc, visited, interner, scope)?;
    }
    let pm = db.get(mname).expect("present");
    acc.add(instantiate_decls(own_decls(pm), &bindings, &op_subst, interner));
    Ok(())
}

/// One parameter's binding for instantiation. `view_name` is the printed argument name used to name
/// structured sorts (`Base{X} ↦ Base{<view_name>}`): the view name `V` for a view argument, or the
/// enclosing parameter name `p` for a by-parameter argument. A view binding maps each theory sort through
/// `sort_image` (`Elt ↦ Nat`); a [`by_param`](Self::by_param) binding instead prefix-renames `X$s ↦
/// view_name$s` (the parameter survives, renamed — Axis-A5 kind 2).
struct ParamBinding {
    view_name: String,
    sort_image: HashMap<String, String>,
    by_param: bool,
}

/// One instantiation argument resolved to its parameter binding plus the module expression to import for
/// it (Axis-A2/A5). A view argument carries `target = Some(<to-module expression>)`; a **by-parameter**
/// argument (an enclosing parameter passed straight through) carries `target = None` — nothing is imported
/// (the enclosing module's parameter copy already supplied `p$s`).
struct ArgResolution {
    binding: ParamBinding,
    target: Option<ModuleExpr>,
    op_subst: HashMap<String, Vec<Token>>,
}

/// Resolve one instantiation argument against the enclosing parameter `scope`. A bare name in `scope` is a
/// by-parameter argument (kind 2). Otherwise a bare view name resolves to the stored view (kind 3 base
/// case), and a nested instantiation `V{Arg, …}` of a *parameterized* view resolves recursively — each
/// inner argument is resolved, then substituted through `V`'s `to` target and `sort_maps` (`BoxV{ToColor}`
/// ⇒ target `BOX{ToColor}`, image `Elt ↦ Box{ToColor}`).
fn resolve_arg(
    arg: &ModuleExpr,
    views: &ViewDb,
    i: &Interner,
    scope: &[String],
) -> Result<ArgResolution, String> {
    // By-parameter: the argument is an enclosing parameter `p`. The instance keeps a parameter, renamed to
    // `p` (`X$s ↦ p$s`, `Base{X} ↦ Base{p}`); nothing is imported.
    if let ModuleExpr::Named(p) = arg
        && scope.iter().any(|n| n == p)
    {
        return Ok(ArgResolution {
            binding: ParamBinding { view_name: p.clone(), sort_image: HashMap::new(), by_param: true },
            target: None,
            op_subst: HashMap::new(),
        });
    }
    match arg {
        ModuleExpr::Named(view_name) => {
            let v = views.get(view_name).ok_or_else(|| format!("view `{view_name}` is not defined"))?;
            if !v.params.is_empty() {
                return Err(format!(
                    "parameterized view `{view_name}` must be instantiated with arguments"
                ));
            }
            Ok(ArgResolution {
                binding: ParamBinding {
                    view_name: view_name.clone(),
                    sort_image: v.sort_maps.iter().cloned().collect(),
                    by_param: false,
                },
                target: Some(v.to.clone()),
                op_subst: op_subst_of(v, i)?,
            })
        }
        ModuleExpr::Instantiation(base, inner_args) => {
            let ModuleExpr::Named(view_name) = &**base else {
                return Err("an instantiation argument must be a view name or a parameterized-view \
                            instantiation"
                    .into());
            };
            let v = views.get(view_name).ok_or_else(|| format!("view `{view_name}` is not defined"))?;
            if v.params.len() != inner_args.len() {
                return Err(format!(
                    "view `{view_name}{{…}}` has {} argument(s) but `{view_name}` has {} parameter(s)",
                    inner_args.len(),
                    v.params.len()
                ));
            }
            // Resolve each inner argument and bind `V`'s parameter to it, then substitute through `V`'s
            // target/sort-image to derive the view. The inner views' op maps are applied when their own
            // target is instantiated (via `collect_expr(target)`), not threaded here.
            let mut inner: HashMap<String, ParamBinding> = HashMap::new();
            let mut inner_to_arg: HashMap<String, ModuleExpr> = HashMap::new();
            for (vp, ia) in v.params.iter().zip(inner_args) {
                let r = resolve_arg(ia, views, i, scope)?;
                inner_to_arg.insert(vp.name.clone(), ia.clone());
                inner.insert(vp.name.clone(), r.binding);
            }
            let target = subst_params_in_expr(&v.to, &inner_to_arg);
            let sort_image =
                v.sort_maps.iter().map(|(a, b)| (a.clone(), inst_sort(b, &inner))).collect();
            Ok(ArgResolution {
                binding: ParamBinding {
                    view_name: canonical_key(arg),
                    sort_image,
                    by_param: false,
                },
                target: Some(target),
                op_subst: op_subst_of(v, i)?,
            })
        }
        ModuleExpr::Sum(..) | ModuleExpr::Rename(..) => {
            Err("an instantiation argument must be a view name or a parameterized-view instantiation \
                 (a sum/renaming argument is not supported)"
                .into())
        }
    }
}

/// The op-map substitution of a view: each single-token source operator `f` to its target token(s)
/// (`op f to g` / `op f to term t`, A1). A mixfix source op map is a follow-up, rejected loudly.
fn op_subst_of(v: &ViewDecl, i: &Interner) -> Result<HashMap<String, Vec<Token>>, String> {
    let mut op_subst = HashMap::new();
    for m in &v.op_maps {
        let (from, to) = match m {
            OpMap::Op { from, to } | OpMap::Term { from, to } => (from, to),
        };
        match from.as_slice() {
            [tok] => {
                op_subst.insert(i.resolve(tok.sym).to_string(), to.clone());
            }
            _ => return Err(format!("view `{}`: a mixfix operator map is a follow-up", v.name)),
        }
    }
    Ok(op_subst)
}

/// Substitute view parameters into a module expression (a parameterized view's `to` target): replace each
/// `Named(p)` that is a parameter with its argument expression, recursing through sums/renamings/nested
/// instantiations. `BoxV`'s target `BOX{X}` with `X ↦ ToColor` becomes `BOX{ToColor}`.
fn subst_params_in_expr(expr: &ModuleExpr, map: &HashMap<String, ModuleExpr>) -> ModuleExpr {
    match expr {
        ModuleExpr::Named(n) => map.get(n).cloned().unwrap_or_else(|| expr.clone()),
        ModuleExpr::Sum(a, b) => ModuleExpr::Sum(
            Box::new(subst_params_in_expr(a, map)),
            Box::new(subst_params_in_expr(b, map)),
        ),
        ModuleExpr::Rename(inner, items) => {
            ModuleExpr::Rename(Box::new(subst_params_in_expr(inner, map)), items.clone())
        }
        ModuleExpr::Instantiation(base, args) => ModuleExpr::Instantiation(
            Box::new(subst_params_in_expr(base, map)),
            args.iter().map(|a| subst_params_in_expr(a, map)).collect(),
        ),
    }
}

/// Apply the instantiation substitution to a module's own declarations: rewrite every sort name through
/// [`inst_sort`], and rewrite the view's operator maps (A1) into the statement bubbles — each reference to
/// a mapped theory operator `f` becomes the target operator `g` or term `t`.
fn instantiate_decls(
    mut d: FlatDecls,
    bindings: &HashMap<String, ParamBinding>,
    op_subst: &HashMap<String, Vec<Token>>,
    i: &mut Interner,
) -> FlatDecls {
    for s in &mut d.sorts {
        *s = inst_sort(s, bindings);
    }
    for chain in &mut d.subsorts {
        for group in chain {
            for s in group {
                *s = inst_sort(s, bindings);
            }
        }
    }
    for op in &mut d.ops {
        for s in &mut op.domain {
            *s = inst_sort(s, bindings);
        }
        op.range = inst_sort(&op.range, bindings);
    }
    // Instantiate each declared variable's sort, and record `name ↦ instantiated sort` so the variable's
    // occurrences in the statement bubbles can be rewritten to single-token colon variables below. (The
    // declarations are kept for bare-variable use in commands, but the bubbles no longer reference them.)
    let mut var_inline: HashMap<String, String> = HashMap::new();
    for v in &mut d.vars {
        v.sort = inst_sort(&v.sort, bindings);
        for n in &v.names {
            var_inline.insert(n.clone(), v.sort.clone());
        }
    }
    // Rewrite statement bubbles: the views' operator maps (A1); each declared variable inlined as a
    // single-token colon variable at its instantiated sort (`H ↦ H:List{ToN}`); and parameter-sort
    // substitution inside glued source colon variables (`E:X$Elt ↦ E:Box{ToColor}`). The colon-variable
    // form keeps the sort a single token that re-parses against the instance's sorts — essential because a
    // nested instantiation produces two copies of a parameterized module's equations at *different* element
    // sorts, which a shared module-level `var` declaration (deduplicated by name) could not type.
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                *rhs = subst_bubble(rhs, bindings, op_subst, &var_inline, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
            Statement::Mb { lhs, sort, cond, .. } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                *sort = subst_bubble(sort, bindings, op_subst, &var_inline, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                *rhs = subst_bubble(rhs, bindings, op_subst, &var_inline, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
        }
    }
    d
}

/// Rewrite a statement bubble under an instantiation. A token that is a mapped source operator becomes its
/// target token(s) (op→op / op→term, A1). A bare declared-variable token becomes a single-token colon
/// variable at its instantiated sort (`H ↦ H:List{ToN}`, from `var_inline`). A glued source colon variable
/// `name:sort` has its sort instantiated (`E:X$Elt ↦ E:Box{ToColor}`). Each rewritten variable stays one
/// token, so it re-parses as an on-the-fly variable of the instance sort; a `name:sort` whose sort is
/// unaffected by the instantiation is left untouched (so an operator coincidentally containing a colon is
/// safe).
fn subst_bubble(
    bubble: &[Token],
    bindings: &HashMap<String, ParamBinding>,
    op_subst: &HashMap<String, Vec<Token>>,
    var_inline: &HashMap<String, String>,
    i: &mut Interner,
) -> Vec<Token> {
    let mut out = Vec::with_capacity(bubble.len());
    for t in bubble {
        let text = i.resolve(t.sym).to_string();
        if let Some(repl) = op_subst.get(&text) {
            out.extend(repl.iter().copied());
            continue;
        }
        if let Some(sort) = var_inline.get(&text) {
            let mut nt = *t;
            nt.sym = i.intern(&format!("{text}:{sort}"));
            out.push(nt);
            continue;
        }
        if let Some((name, sort)) = text.rsplit_once(':')
            && !name.is_empty()
            && !sort.is_empty()
        {
            let new_sort = inst_sort(sort, bindings);
            if new_sort.as_str() != sort {
                let mut nt = *t;
                nt.sym = i.intern(&format!("{name}:{new_sort}"));
                out.push(nt);
                continue;
            }
        }
        out.push(*t);
    }
    out
}

/// Instantiate one sort name. A parameter sort `X$s` becomes the view's image of `s` (or `p$s` under a
/// by-parameter binding); a structured sort `Base{a, …}` has each argument instantiated (a bare parameter
/// name `X` becomes its view/argument name, the instance-naming rule); anything else is unchanged.
fn inst_sort(name: &str, bindings: &HashMap<String, ParamBinding>) -> String {
    if let Some((base, args)) = split_structured(name) {
        let new_args: Vec<String> = args
            .iter()
            .map(|a| match bindings.get(a.as_str()) {
                Some(b) => b.view_name.clone(), // a bare parameter name → the view / argument name
                None => inst_sort(a, bindings),  // nested structured / parameter sort
            })
            .collect();
        return format!("{base}{{{}}}", new_args.join(","));
    }
    if let Some((param, s)) = name.split_once('$')
        && let Some(b) = bindings.get(param)
    {
        // By-parameter: prefix-rename `X$s ↦ p$s` (the parameter survives). View: the view's sort image.
        return if b.by_param {
            format!("{}${s}", b.view_name)
        } else {
            b.sort_image.get(s).cloned().unwrap_or_else(|| s.to_string())
        };
    }
    name.to_string()
}

/// Split a structured sort name `Base{arg, …}` into its base and top-level (comma-separated, brace-balanced)
/// arguments; `None` if it is not structured.
fn split_structured(name: &str) -> Option<(&str, Vec<String>)> {
    let open = name.find('{')?;
    if !name.ends_with('}') {
        return None;
    }
    let base = &name[..open];
    let inner = &name[open + 1..name.len() - 1];
    let mut args = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    for (k, c) in inner.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => depth -= 1,
            ',' if depth == 0 => {
                args.push(inner[start..k].to_string());
                start = k + 1;
            }
            _ => {}
        }
    }
    args.push(inner[start..].to_string());
    Some((base, args))
}

/// A canonical string for a module expression, used as the `visited` dedup key.
fn canonical_key(expr: &ModuleExpr) -> String {
    match expr {
        ModuleExpr::Named(n) => n.clone(),
        ModuleExpr::Sum(a, b) => format!("({} + {})", canonical_key(a), canonical_key(b)),
        ModuleExpr::Rename(inner, items) => {
            use tnk_frontend::surface::ast::RenameItem;
            let parts: Vec<String> = items
                .iter()
                .map(|it| match it {
                    RenameItem::Sort { from, to } => format!("sort {from} to {to}"),
                    RenameItem::Op { from, to } => format!("op {from} to {to}"),
                })
                .collect();
            format!("({} * ({}))", canonical_key(inner), parts.join(", "))
        }
        ModuleExpr::Instantiation(base, args) => {
            // The canonical instance name `M{A, …}` — Maude's `makeParameterInstanceName`. Each argument
            // is itself a module expression (a view name, a nested instantiation, or a parameter name).
            let parts: Vec<String> = args.iter().map(canonical_key).collect();
            format!("{}{{{}}}", canonical_key(base), parts.join(","))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::tokenize;
    use tnk_frontend::surface::parser::Parser;

    fn db_of(src: &str) -> (ModuleDb, ViewDb, Interner) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let db = ModuleDb::from_modules(s.modules);
        let mut views = ViewDb::new();
        for v in s.views {
            crate::view::validate_view(&v, &db, &mut i).expect("valid view");
            views.insert(v);
        }
        (db, views, i)
    }

    /// A diamond (`TOP` imports `L` and `R`, both protecting `BASE`) includes `BASE`'s declarations
    /// exactly once.
    #[test]
    fn diamond_includes_base_once() {
        let src = "\
fmod BASE is sort S . op a : -> S [ctor] . op f : S -> S . var X : S . eq f(X) = a . endfm
fmod L is protecting BASE . op l : S -> S . endfm
fmod R is protecting BASE . op r : S -> S . endfm
fmod TOP is protecting L . protecting R . endfm
";
        let (db, views, mut i) = db_of(src);
        let flat = flatten("TOP", &db, &views, &mut i).expect("flatten");
        assert_eq!(flat.sorts, ["S"], "BASE's sort S appears once despite two import paths");
        assert_eq!(flat.statements.len(), 1, "BASE's single equation is not duplicated");
        let opnames: Vec<String> =
            flat.ops.iter().map(|o| i.resolve(o.name[0].sym).to_string()).collect();
        assert!(["a", "f", "l", "r"].iter().all(|n| opnames.contains(&n.to_string())));
    }

    /// An import-free module flattens to itself (so `load_program` handles single-module files).
    #[test]
    fn import_free_flattens_to_itself() {
        let (db, views, mut i) = db_of("fmod M is sort S . op a : -> S [ctor] . endfm\n");
        let flat = flatten("M", &db, &views, &mut i).expect("flatten");
        assert!(flat.imports.is_empty());
        assert_eq!(flat.sorts, ["S"]);
    }

    /// B-iii: a parameter `X :: TRIV` makes a parameter copy of `TRIV` — the theory sort `Elt` becomes the
    /// parameter sort `X$Elt` in the flattened module, alongside the module's own structured sort, and no
    /// formal parameters remain.
    #[test]
    fn parameter_copy_introduces_param_sort() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op b : X$Elt -> Box{X} [ctor] . endfm\n",
        );
        let flat = flatten("BOX", &db, &views, &mut i).expect("flatten");
        assert!(flat.sorts.contains(&"X$Elt".to_string()), "X$Elt present: {:?}", flat.sorts);
        assert!(flat.sorts.contains(&"Box{X}".to_string()), "Box{{X}} present: {:?}", flat.sorts);
        assert!(flat.params.is_empty(), "no formal parameters remain after flattening");
    }

    /// B-iv: instantiation `BOX{V}` resolves to the parameter sort's view image and the structured sort's
    /// instance name — `X$Elt ↦ Hue` (the view's `sort Elt to Hue`) and `Box{X} ↦ Box{V}`. The view's
    /// target module's sorts (`Hue`) are imported.
    #[test]
    fn instantiation_substitutes_param_and_structured_sorts() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm\n\
             view V from TRIV to COLOR is sort Elt to Hue . endv\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op wrap : X$Elt -> Box{X} [ctor] . endfm\n\
             fmod USE is protecting BOX{V} . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        assert!(flat.sorts.contains(&"Box{V}".to_string()), "structured instance sort: {:?}", flat.sorts);
        assert!(flat.sorts.contains(&"Hue".to_string()), "view target sort imported: {:?}", flat.sorts);
        assert!(!flat.sorts.contains(&"X$Elt".to_string()), "parameter sort is substituted away");
        assert!(!flat.sorts.contains(&"Box{X}".to_string()), "parameterized sort is instantiated");
        // `wrap` now has domain `Hue` (the view image of `X$Elt`).
        let wrap = flat.ops.iter().find(|o| i.resolve(o.name[0].sym) == "wrap").expect("wrap op");
        assert_eq!(wrap.domain, ["Hue"], "X$Elt domain substituted to the view image");
        assert_eq!(wrap.range, "Box{V}");
    }

    /// Axis-A2/A5: a nested instantiation `BOX{BoxV{ToColor}}` resolves the parameterized-view argument
    /// `BoxV{ToColor}` to a derived ground view (target `BOX{ToColor}`, sort image `Elt ↦ Box{ToColor}`),
    /// so the flattened module carries both element-level instances of `Box` and both `wrap` overloads —
    /// `wrap : Hue -> Box{ToColor}` (the inner target) and `wrap : Box{ToColor} -> Box{BoxV{ToColor}}`.
    #[test]
    fn nested_instantiation_resolves_derived_view() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm\n\
             view ToColor from TRIV to COLOR is sort Elt to Hue . endv\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op wrap : X$Elt -> Box{X} [ctor] . endfm\n\
             view BoxV{X :: TRIV} from TRIV to BOX{X} is sort Elt to Box{X} . endv\n\
             fmod USE is protecting BOX{BoxV{ToColor}} . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        for s in ["Hue", "Box{ToColor}", "Box{BoxV{ToColor}}"] {
            assert!(flat.sorts.contains(&s.to_string()), "sort {s} present: {:?}", flat.sorts);
        }
        // Both `wrap` overloads: the inner `Hue -> Box{ToColor}` and the outer `Box{ToColor} -> Box{…}`.
        let wraps: Vec<(&Vec<String>, &String)> = flat
            .ops
            .iter()
            .filter(|o| i.resolve(o.name[0].sym) == "wrap")
            .map(|o| (&o.domain, &o.range))
            .collect();
        assert!(
            wraps.iter().any(|(d, r)| d.as_slice() == ["Hue"] && r.as_str() == "Box{ToColor}"),
            "inner wrap: {wraps:?}"
        );
        assert!(
            wraps
                .iter()
                .any(|(d, r)| d.as_slice() == ["Box{ToColor}"] && r.as_str() == "Box{BoxV{ToColor}}"),
            "outer wrap: {wraps:?}"
        );
    }

    /// Axis-A5 kind 2: a parameterized module `PAIR{X :: TRIV}` that protects `LIST{X}` by the *enclosing
    /// parameter* `X`. Flattened **standalone** it stays parameterized — the `LIST{X}` import is a
    /// by-parameter instantiation, so `LIST`'s `E$Elt` / `List{E}` are renamed to `X$Elt` / `List{X}`.
    #[test]
    fn by_parameter_import_stays_parameterized() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod LIST{E :: TRIV} is sort List{E} . op cons : E$Elt List{E} -> List{E} [ctor] . endfm\n\
             fmod PAIR{X :: TRIV} is protecting LIST{X} . op two : X$Elt -> List{X} . endfm\n",
        );
        let flat = flatten("PAIR", &db, &views, &mut i).expect("flatten");
        assert!(flat.sorts.contains(&"List{X}".to_string()), "List{{X}} present: {:?}", flat.sorts);
        assert!(flat.sorts.contains(&"X$Elt".to_string()), "X$Elt present: {:?}", flat.sorts);
        // `cons` came from `LIST{X}` with its parameter `E` renamed to `X`: `X$Elt List{X} -> List{X}`.
        let cons = flat.ops.iter().find(|o| i.resolve(o.name[0].sym) == "cons").expect("cons");
        assert_eq!(cons.domain, ["X$Elt", "List{X}"]);
        assert_eq!(cons.range, "List{X}");
    }

    /// An undefined imported module is a loud error.
    #[test]
    fn unknown_import_errors() {
        let (db, views, mut i) = db_of("fmod M is protecting NOPE . endfm\n");
        let err = flatten("M", &db, &views, &mut i).unwrap_err();
        assert!(err.contains("not defined"), "got: {err}");
    }
}
