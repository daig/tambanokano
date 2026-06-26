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

use std::collections::HashSet;
use tnk_frontend::lex::Interner;
use tnk_frontend::surface::ast::{ModuleExpr, ModuleKind, OpDecl, PreModule, Statement, VarDecl};

use crate::db::ModuleDb;
use crate::rename::apply_renaming;

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
pub fn flatten(name: &str, db: &ModuleDb, interner: &mut Interner) -> Result<PreModule, String> {
    let mut acc = Acc::default();
    let mut visited = HashSet::new();
    collect_named(name, db, &mut acc, &mut visited, interner)?;
    // The flattened module is the root module with its imports inlined, so it keeps the root's kind
    // (`mod` stays a system module — its rules survive flattening).
    let kind = db.get(name).map(|pm| pm.kind).unwrap_or(ModuleKind::Functional);
    let d = acc.into_decls();
    Ok(PreModule {
        name: name.to_string(),
        kind,
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
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
) -> Result<(), String> {
    if !visited.insert(name.to_string()) {
        return Ok(()); // already merged (diamond)
    }
    let pm = db.get(name).ok_or_else(|| format!("imported module `{name}` is not defined"))?;
    for imp in &pm.imports {
        collect_expr(&imp.expr, db, acc, visited, interner)?;
    }
    acc.add(own_decls(pm)); // the module's own declarations, after its imports
    Ok(())
}

fn collect_expr(
    expr: &ModuleExpr,
    db: &ModuleDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
) -> Result<(), String> {
    match expr {
        ModuleExpr::Named(n) => collect_named(n, db, acc, visited, interner),
        ModuleExpr::Sum(a, b) => {
            collect_expr(a, db, acc, visited, interner)?;
            collect_expr(b, db, acc, visited, interner)
        }
        ModuleExpr::Rename(inner, items) => {
            // `A * (R)` is a distinct module from `A`: key it by its canonical form so it merges once,
            // and flatten `inner` in a fresh scope (the renamed content is independent of the unrenamed).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mut tmp = Acc::default();
            let mut tmp_visited = HashSet::new();
            collect_expr(inner, db, &mut tmp, &mut tmp_visited, interner)?;
            let renamed = apply_renaming(tmp.into_decls(), items, interner)?;
            acc.add(renamed);
            Ok(())
        }
    }
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::tokenize;
    use tnk_frontend::surface::parser::Parser;

    fn db_of(src: &str) -> (ModuleDb, Interner) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        (ModuleDb::from_modules(s.modules), i)
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
        let (db, mut i) = db_of(src);
        let flat = flatten("TOP", &db, &mut i).expect("flatten");
        assert_eq!(flat.sorts, ["S"], "BASE's sort S appears once despite two import paths");
        assert_eq!(flat.statements.len(), 1, "BASE's single equation is not duplicated");
        let opnames: Vec<String> =
            flat.ops.iter().map(|o| i.resolve(o.name[0].sym).to_string()).collect();
        assert!(["a", "f", "l", "r"].iter().all(|n| opnames.contains(&n.to_string())));
    }

    /// An import-free module flattens to itself (so `load_program` handles single-module files).
    #[test]
    fn import_free_flattens_to_itself() {
        let (db, mut i) = db_of("fmod M is sort S . op a : -> S [ctor] . endfm\n");
        let flat = flatten("M", &db, &mut i).expect("flatten");
        assert!(flat.imports.is_empty());
        assert_eq!(flat.sorts, ["S"]);
    }

    /// An undefined imported module is a loud error.
    #[test]
    fn unknown_import_errors() {
        let (db, mut i) = db_of("fmod M is protecting NOPE . endfm\n");
        let err = flatten("M", &db, &mut i).unwrap_err();
        assert!(err.contains("not defined"), "got: {err}");
    }
}
