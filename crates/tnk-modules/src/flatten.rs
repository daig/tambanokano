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
    for imp in &pm.imports {
        collect_expr(&imp.expr, db, views, acc, visited, interner)?;
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
) -> Result<(), String> {
    match expr {
        ModuleExpr::Named(n) => collect_named(n, db, views, acc, visited, interner),
        ModuleExpr::Sum(a, b) => {
            collect_expr(a, db, views, acc, visited, interner)?;
            collect_expr(b, db, views, acc, visited, interner)
        }
        ModuleExpr::Rename(inner, items) => {
            // `A * (R)` is a distinct module from `A`: key it by its canonical form so it merges once,
            // and flatten `inner` in a fresh scope (the renamed content is independent of the unrenamed).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mut tmp = Acc::default();
            let mut tmp_visited = HashSet::new();
            collect_expr(inner, db, views, &mut tmp, &mut tmp_visited, interner)?;
            let renamed = apply_renaming(tmp.into_decls(), items, interner)?;
            acc.add(renamed);
            Ok(())
        }
        ModuleExpr::Instantiation(base, args) => {
            // `M{V, …}` merges once (keyed by its canonical instance name `M{V, …}`).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mname = match &**base {
                ModuleExpr::Named(n) => n.as_str(),
                _ => return Err("the base of an instantiation must be a named module (a nested \
                                 instantiation / renaming base is a follow-up)"
                    .into()),
            };
            instantiate(mname, args, db, views, acc, visited, interner)
        }
    }
}

/// Instantiate the parameterized module `mname` with one view per parameter (B-iv): import each view's
/// target module, then merge `mname`'s own declarations with the parameter substitution applied —
/// `X$s ↦ V`'s sort image of `s`, and a structured sort `Base{…X…} ↦ Base{…V…}` (the parameter name
/// replaced by the view name, Maude's instance naming).
///
/// Scope (B-iv common case): single/multi-parameter **module-view** instantiation with no operator maps
/// (`TRIV`/sort-only views). Deferred — view operator maps (`op f to g` / `op 0 to term t`), a
/// parameterized view target (`to LIST{X}`), and free-vs-bound nested instantiation.
fn instantiate(
    mname: &str,
    args: &[ModuleExpr],
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
) -> Result<(), String> {
    let pm = db.get(mname).ok_or_else(|| format!("instantiated module `{mname}` is not defined"))?;
    if pm.params.len() != args.len() {
        return Err(format!(
            "instantiation `{mname}{{…}}` has {} argument(s) but `{mname}` has {} parameter(s)",
            args.len(),
            pm.params.len()
        ));
    }

    // Bind each parameter to its view, importing the view's target module, and collect the views'
    // operator maps (`op f to g` / `op f to term t`) into one token-substitution (A1).
    let mut bindings: HashMap<String, ParamBinding> = HashMap::new();
    let mut op_subst: HashMap<String, Vec<Token>> = HashMap::new();
    for (param, arg) in pm.params.iter().zip(args) {
        // Increment 1 (parser): only a bare view name is supported here; a nested / parameterized
        // instantiation argument parses but is handled in a later increment (Axis-A2/A5).
        let view_name = match arg {
            ModuleExpr::Named(n) => n.as_str(),
            _ => {
                return Err(format!(
                    "instantiation `{mname}{{…}}`: a nested or parameterized instantiation argument \
                     is not yet supported (Axis-A2/A5)"
                ));
            }
        };
        let v = views
            .get(view_name)
            .ok_or_else(|| format!("instantiation `{mname}{{…}}`: view `{view_name}` is not defined"))?;
        let target = view_target(v)?;
        collect_named(target, db, views, acc, visited, interner)?;
        let sort_image: HashMap<String, String> = v.sort_maps.iter().cloned().collect();
        bindings.insert(param.name.clone(), ParamBinding { view_name: view_name.to_string(), sort_image });
        for m in &v.op_maps {
            let (from, to) = match m {
                OpMap::Op { from, to } | OpMap::Term { from, to } => (from, to),
            };
            // The source op is a single-token name (a mixfix op map is a follow-up). Its references in
            // `M`'s body are rewritten to the target op (`g`) or term (`0.0`).
            match from.as_slice() {
                [tok] => {
                    op_subst.insert(interner.resolve(tok.sym).to_string(), to.clone());
                }
                _ => return Err(format!("view `{}`: a mixfix operator map is a follow-up", v.name)),
            }
        }
    }

    // `M`'s regular imports (deduped via `visited`), then its own declarations with the substitution.
    let imports: Vec<ModuleExpr> = pm.imports.iter().map(|imp| imp.expr.clone()).collect();
    for imp in &imports {
        collect_expr(imp, db, views, acc, visited, interner)?;
    }
    let pm = db.get(mname).expect("present");
    acc.add(instantiate_decls(own_decls(pm), &bindings, &op_subst, interner));
    Ok(())
}

/// One parameter's binding for instantiation: the view name (used to name structured sorts `Base{X}` →
/// `Base{view}`) and the view's sort image map (`Elt ↦ Nat`, used for the parameter sort `X$Elt`).
struct ParamBinding {
    view_name: String,
    sort_image: HashMap<String, String>,
}

/// The target module name of a (B-iv common-case) view — a plain named module.
fn view_target(v: &ViewDecl) -> Result<&str, String> {
    match &v.to {
        ModuleExpr::Named(n) => Ok(n),
        _ => Err(format!("view `{}`: a parameterized view target is a follow-up", v.name)),
    }
}

/// Apply the instantiation substitution to a module's own declarations: rewrite every sort name through
/// [`inst_sort`], and rewrite the view's operator maps (A1) into the statement bubbles — each reference to
/// a mapped theory operator `f` becomes the target operator `g` or term `t`.
fn instantiate_decls(
    mut d: FlatDecls,
    bindings: &HashMap<String, ParamBinding>,
    op_subst: &HashMap<String, Vec<Token>>,
    i: &Interner,
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
    for v in &mut d.vars {
        v.sort = inst_sort(&v.sort, bindings);
    }
    // Apply the operator maps to the statement bubbles (A1). Sort-name substitution into bubbles
    // (`mb t : Sort`, structured colon variables) remains a follow-up.
    if !op_subst.is_empty() {
        for st in &mut d.statements {
            match st {
                Statement::Eq { lhs, rhs, cond, .. } => {
                    *lhs = subst_ops(lhs, op_subst, i);
                    *rhs = subst_ops(rhs, op_subst, i);
                    if let Some(c) = cond {
                        *c = subst_ops(c, op_subst, i);
                    }
                }
                Statement::Mb { lhs, sort, cond, .. } => {
                    *lhs = subst_ops(lhs, op_subst, i);
                    *sort = subst_ops(sort, op_subst, i);
                    if let Some(c) = cond {
                        *c = subst_ops(c, op_subst, i);
                    }
                }
                Statement::Rule { lhs, rhs, cond, .. } => {
                    *lhs = subst_ops(lhs, op_subst, i);
                    *rhs = subst_ops(rhs, op_subst, i);
                    if let Some(c) = cond {
                        *c = subst_ops(c, op_subst, i);
                    }
                }
            }
        }
    }
    d
}

/// Rewrite a statement bubble under an operator-map substitution: each token whose text is a mapped source
/// operator is replaced by the target token(s) (one token for `op f to g`, several for `op f to term t`).
fn subst_ops(bubble: &[Token], op_subst: &HashMap<String, Vec<Token>>, i: &Interner) -> Vec<Token> {
    let mut out = Vec::with_capacity(bubble.len());
    for t in bubble {
        match op_subst.get(i.resolve(t.sym)) {
            Some(repl) => out.extend(repl.iter().copied()),
            None => out.push(*t),
        }
    }
    out
}

/// Instantiate one sort name. A parameter sort `X$s` becomes the view's image of `s`; a structured sort
/// `Base{a, …}` has each argument instantiated (a bare parameter name `X` becomes its view name, the
/// instance-naming rule); anything else is unchanged.
fn inst_sort(name: &str, bindings: &HashMap<String, ParamBinding>) -> String {
    if let Some((base, args)) = split_structured(name) {
        let new_args: Vec<String> = args
            .iter()
            .map(|a| match bindings.get(a.as_str()) {
                Some(b) => b.view_name.clone(), // a bare parameter name → the view name
                None => inst_sort(a, bindings),  // nested structured / parameter sort
            })
            .collect();
        return format!("{base}{{{}}}", new_args.join(","));
    }
    if let Some((param, s)) = name.split_once('$')
        && let Some(b) = bindings.get(param)
    {
        return b.sort_image.get(s).cloned().unwrap_or_else(|| s.to_string());
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

    /// An undefined imported module is a loud error.
    #[test]
    fn unknown_import_errors() {
        let (db, views, mut i) = db_of("fmod M is protecting NOPE . endfm\n");
        let err = flatten("M", &db, &views, &mut i).unwrap_err();
        assert!(err.contains("not defined"), "got: {err}");
    }
}
