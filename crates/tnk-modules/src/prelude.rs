//! Built-in modules injected into the [`ModuleDb`] on demand.
//!
//! The engine is prelude-free except for `CONFIGURATION`, which object modules import automatically.
//! [`ensure_builtins`] installs this declaration only when the module database does not already contain one.

use tnk_frontend::lex::{Interner, tokenize};
use tnk_frontend::surface::ast::{Import, ModuleExpr};
use tnk_frontend::surface::parser::Parser;

use crate::db::ModuleDb;

/// Object-system configuration substrate used when `CONFIGURATION` is imported but not already defined.
/// Its public sorts, operators, and hook identifiers support object-module parsing and execution.
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

/// Return the synthesized source of a built-in module. The current built-in set contains CONFIGURATION.
fn builtin_src(name: &str) -> Option<&'static str> {
    match name {
        "CONFIGURATION" => Some(CONFIGURATION_SRC),
        _ => None,
    }
}

/// Insert each required built-in module that is not already present. Existing definitions always win.
pub fn ensure_builtins(imports: &[Import], db: &mut ModuleDb, interner: &mut Interner) {
    let mut names = Vec::new();
    for imp in imports {
        collect_named(&imp.expr, &mut names);
    }
    for name in names {
        if db.get(&name).is_some() {
            continue;
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
