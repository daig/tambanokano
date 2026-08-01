//! Built-in modules injected into the [`ModuleDb`](crate::db::ModuleDb) on demand.
//!
//! tambanokano keeps the engine prelude-free except for one API-compatible substrate:
//! `CONFIGURATION`, which an `omod` auto-imports (Maude's `set oo include CONFIGURATION on`).
//! When a module imports `CONFIGURATION` and the user has not defined it,
//! [`ensure_builtins`] parses this built-in copy so flattening can resolve it. A
//! user-defined `CONFIGURATION` (as `conformance/objects.maude` declares) is never overridden.
//!
//! The source below is an original, MIT-licensed declaration of that public interface
//! (sorts, operators, and `special` hook names required for object-system interoperability).
//! It is not a verbatim extract of Maude's `prelude.maude`.

use tnk_frontend::lex::{Interner, tokenize};
use tnk_frontend::surface::ast::{Import, ModuleExpr};
use tnk_frontend::surface::parser::Parser;

use crate::db::ModuleDb;

/// Object-system configuration substrate used when an `omod` (or an explicit import) needs
/// `CONFIGURATION` and the session has not already defined it.
///
/// Public names and hook identifiers match the Maude object-system interface so stock modules
/// and differential fixtures remain source-compatible. The module text itself is original to
/// tambanokano (MIT).
pub const CONFIGURATION_SRC: &str = r#"
mod CONFIGURATION is
  *** Object attributes (ACU set with empty identity).
  sorts Attribute AttributeSet .
  subsort Attribute < AttributeSet .
  op none : -> AttributeSet [ctor] .
  op _,_ : AttributeSet AttributeSet -> AttributeSet [ctor assoc comm id: none] .

  *** Configuration soup: objects, messages, and the portal.
  sorts Oid Cid Object Msg Portal Configuration .
  subsorts Object Msg Portal < Configuration .

  op <_:_|_> : Oid Cid AttributeSet -> Object
    [ctor object special (
      id-hook ObjectConstructorSymbol
      op-hook attributeSetSymbol (_,_ : AttributeSet AttributeSet ~> AttributeSet))] .

  op none : -> Configuration [ctor] .
  op __ : Configuration Configuration -> Configuration
    [ctor config assoc comm id: none] .
  op <> : -> Portal [ctor portal] .

  *** Class projection for completed object patterns.
  op getClass : Object -> Cid .
  var OidVar : Oid .
  var CidVar : Cid .
  var Attrs : AttributeSet .
  eq getClass(< OidVar : CidVar | Attrs >) = CidVar .
endm
"#;

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
