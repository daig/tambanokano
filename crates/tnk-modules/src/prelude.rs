//! Built-in prelude modules, injected into the [`ModuleDb`](crate::db::ModuleDb) on demand.
//!
//! tnk has **no standing prelude** — every module comes from the source file — with ONE exception:
//! `CONFIGURATION`, the object-system substrate that an `omod` auto-imports (Maude's
//! `set oo include CONFIGURATION on`, `prelude.maude:3234`). When a module imports `CONFIGURATION`
//! (directly, or via the `omod` auto-import the surface parser inserts) and the user has **not** defined
//! it, [`ensure_builtins`] parses this built-in copy into the database so flattening can resolve it. A
//! user-defined `CONFIGURATION` (as `conformance/objects.maude` declares) is never overridden.

use tnk_frontend::lex::{Interner, tokenize};
use tnk_frontend::surface::ast::{Import, ModuleExpr};
use tnk_frontend::surface::parser::Parser;

use crate::db::ModuleDb;

/// The object-configuration substrate — **verbatim** from Maude's `prelude.maude:3213-3231` (the
/// `mod CONFIGURATION` block). Supplies `Oid`/`Cid`/`Object`/`Msg`/`Portal`/`Attribute`/`AttributeSet`,
/// the object constructor `<_:_|_>` (its `ObjectConstructorSymbol` id-hook + `attributeSetSymbol`
/// op-hook binding the AttributeSet `_,_`), the configuration soup `__`, the portal `<>`, and `getClass`.
/// A plain `mod` (not `omod`), so its own `getClass` equation is not subject to object-pattern completion.
pub const CONFIGURATION_SRC: &str = "\
mod CONFIGURATION is
  sorts Attribute AttributeSet .
  subsort Attribute < AttributeSet .
  op none : -> AttributeSet  [ctor] .
  op _,_ : AttributeSet AttributeSet -> AttributeSet [ctor assoc comm id: none] .

  sorts Oid Cid Object Msg Portal Configuration .
  subsort Object Msg Portal < Configuration .
  op <_:_|_> : Oid Cid AttributeSet -> Object [ctor object
                                               special (
                                                 id-hook ObjectConstructorSymbol
                                                 op-hook attributeSetSymbol (_,_ : AttributeSet AttributeSet ~> AttributeSet))] .
  op none : -> Configuration [ctor] .
  op __ : Configuration Configuration -> Configuration [ctor config assoc comm id: none] .
  op <> : -> Portal [ctor portal] .

  op getClass : Object -> Cid .
  eq getClass(< O:Oid : C:Cid | A:AttributeSet >) = C:Cid .
endm
";

/// The built-in module source for `name`, if any. `CONFIGURATION` is the only built-in for now.
fn builtin_src(name: &str) -> Option<&'static str> {
    match name {
        "CONFIGURATION" => Some(CONFIGURATION_SRC),
        _ => None,
    }
}

/// Ensure any built-in prelude module named by `imports` is present in `db`, parsing and inserting the
/// built-in copy when the user has not already defined it. Idempotent — a same-named module already in
/// `db` (a user definition, or a previous injection) wins and is left untouched.
pub fn ensure_builtins(imports: &[Import], db: &mut ModuleDb, interner: &mut Interner) {
    let mut names = Vec::new();
    for imp in imports {
        collect_named(&imp.expr, &mut names);
    }
    for name in names {
        if db.get(&name).is_some() {
            continue; // already defined (user or prior injection)
        }
        let Some(src) = builtin_src(&name) else {
            continue;
        };
        let toks = tokenize(src, interner);
        let Ok(parsed) = Parser::new(&toks, interner).parse_source() else {
            continue;
        };
        for bm in parsed.modules {
            if db.get(&bm.name).is_none() {
                db.insert(bm);
            }
        }
    }
}

/// Collect the plain module names referenced by a module expression (through sums / renamings /
/// instantiations), so an import like `CONFIGURATION` or `CONFIGURATION + FOO` is detected.
fn collect_named(expr: &ModuleExpr, out: &mut Vec<String>) {
    match expr {
        ModuleExpr::Named(n) => out.push(n.clone()),
        ModuleExpr::Sum(a, b) => {
            collect_named(a, out);
            collect_named(b, out);
        }
        ModuleExpr::Rename(e, _) => collect_named(e, out),
        ModuleExpr::Instantiation(e, args) => {
            collect_named(e, out);
            for a in args {
                collect_named(a, out);
            }
        }
    }
}
