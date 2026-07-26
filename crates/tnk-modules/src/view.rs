//! View definitions (Pillar B-ii): store + signature-validate `view V from T to M is … endv`.
//!
//! A view maps a source theory `T` to a target module/theory `M` — it is the argument of a parameterized
//! instantiation `M{V}` (B-iv). This module parses-then-stores views and **signature-validates** them:
//! `from` resolves to a theory and `to` to a defined module; every sort the view explicitly maps — plus
//! every theory sort by its identity default — names a sort that exists in the target. That is the check
//! behind Maude's most common view diagnostic (`failed to find sort … to represent …`).
//!
//! Deferred to when B-iv exercises the maps (noted so the gap is explicit): the kind/connected-component
//! and subsort-preservation checks (`View::checkSorts`), operator-mapping type checks (`checkOps` — op maps
//! are parsed and stored but not yet validated), and the theory's axiom proof obligations.

use std::collections::{HashMap, HashSet};
use tnk_frontend::lex::Interner;
use tnk_frontend::surface::ast::{ModuleExpr, ViewDecl};

use crate::db::ModuleDb;
use crate::flatten::flatten;

/// A name → [`ViewDecl`] table — the parsed, validated views of a program.
#[derive(Debug, Default, Clone)]
pub struct ViewDb {
    views: HashMap<String, ViewDecl>,
}

impl ViewDb {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a view (overwriting any previous view of the same name).
    pub fn insert(&mut self, v: ViewDecl) {
        self.views.insert(v.name.clone(), v);
    }

    pub fn get(&self, name: &str) -> Option<&ViewDecl> {
        self.views.get(name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.views.contains_key(name)
    }
}

/// The base module/theory name of a view's `from`/`to`: a plain name, or the base of an instantiation
/// target (`LIST{X}` → `LIST`, Axis-A2). Sums/renamings as a view target are a later increment.
fn expr_base_name(e: &ModuleExpr) -> Result<&str, String> {
    match e {
        ModuleExpr::Named(n) => Ok(n),
        ModuleExpr::Instantiation(base, _) => expr_base_name(base),
        _ => Err(
            "a view's `from`/`to` must be a named module/theory or an instantiation \
                  (sums/renamings are a later increment)"
                .into(),
        ),
    }
}

/// Signature-validate a view against the module database. On success the view is well-formed enough to be
/// stored and (later) used in an instantiation; on failure returns a diagnostic mirroring the reference
/// binary's wording.
pub fn validate_view(
    v: &ViewDecl,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<(), String> {
    let from_name = expr_base_name(&v.from)?;
    let to_name = expr_base_name(&v.to)?;

    let from_pm = db.get(from_name).ok_or_else(|| {
        format!(
            "view `{}`: source theory `{from_name}` is not defined",
            v.name
        )
    })?;
    if !from_pm.is_theory {
        return Err(format!(
            "view `{}`: source `{from_name}` is not a theory",
            v.name
        ));
    }
    db.get(to_name).ok_or_else(|| {
        format!(
            "view `{}`: target module `{to_name}` is not defined",
            v.name
        )
    })?;

    // Flatten the source theory / target module with the REAL view table: a target may itself be
    // built from instantiations (`INT-VECTOR = VECTOR{Int0} * (…)`, stock linear.maude), so an
    // empty table wrongly failed its flatten ("view `Int0` is not defined").
    let from_flat = flatten(from_name, db, views, interner)?;
    let from_sorts: HashSet<&str> = from_flat.sorts.iter().map(String::as_str).collect();

    // Sort-map sources must be sorts of the theory.
    let mut mapped: HashSet<&str> = HashSet::new();
    for (a, _b) in &v.sort_maps {
        if !from_sorts.contains(a.as_str()) {
            return Err(format!(
                "view `{}`: sort `{a}` is not a sort of `{from_name}`",
                v.name
            ));
        }
        mapped.insert(a.as_str());
    }

    // Target-sort existence (Maude's `failed to find sort …`) needs a *flattenable* target. A parameterized
    // view's target references the view's own parameters (`to LIST{X}`) and so cannot be flattened
    // standalone — its sorts are checked when the view is used in an instantiation. For a plain named target
    // (the B-ii common case) keep the full check, including the identity default for unmapped theory sorts.
    if v.params.is_empty()
        && let ModuleExpr::Named(_) = &v.to
    {
        let to_flat = flatten(to_name, db, views, interner)?;
        let to_sorts: HashSet<&str> = to_flat.sorts.iter().map(String::as_str).collect();
        for (a, b) in &v.sort_maps {
            if !to_sorts.contains(b.as_str()) {
                return Err(format!(
                    "view `{}`: failed to find sort {b} in {to_name} to represent sort {a} from {from_name}",
                    v.name
                ));
            }
        }
        for a in &from_flat.sorts {
            if mapped.contains(a.as_str()) {
                continue;
            }
            if !to_sorts.contains(a.as_str()) {
                return Err(format!(
                    "view `{}`: failed to find sort {a} in {to_name} to represent sort {a} from {from_name}",
                    v.name
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::tokenize;
    use tnk_frontend::surface::parser::Parser;

    /// Parse a source into (module DB, views, interner).
    fn setup(src: &str) -> (ModuleDb, Vec<ViewDecl>, Interner) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        (ModuleDb::from_modules(s.modules), s.views, i)
    }

    /// A well-formed view (`Elt` mapped to an existing target sort) validates.
    #[test]
    fn good_view_validates() {
        let (db, views, mut i) = setup(
            "fth TRIV is sort Elt . endfth\n\
             fmod NUM is sort N . op z : -> N [ctor] . endfm\n\
             view ToNum from TRIV to NUM is sort Elt to N . endv\n",
        );
        assert!(validate_view(&views[0], &db, &ViewDb::new(), &mut i).is_ok());
    }

    /// Mapping a theory sort to a sort the target does not have is the binary's `failed to find sort` error.
    #[test]
    fn missing_target_sort_rejected() {
        let (db, views, mut i) = setup(
            "fth TRIV is sort Elt . endfth\n\
             fmod NUM is sort N . op z : -> N [ctor] . endfm\n\
             view Bad from TRIV to NUM is sort Elt to NoSuch . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(
            err.contains("failed to find sort NoSuch in NUM"),
            "got: {err}"
        );
    }

    /// A view whose source is not a theory is rejected.
    #[test]
    fn non_theory_source_rejected() {
        let (db, views, mut i) = setup(
            "fmod A is sort Elt . endfm\n\
             fmod NUM is sort N . endfm\n\
             view V from A to NUM is sort Elt to N . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("is not a theory"), "got: {err}");
    }

    /// An unmapped theory sort defaults to identity and must exist in the target.
    #[test]
    fn unmapped_theory_sort_must_exist_in_target() {
        // The theory declares `Elt` and `Key`; the view maps only `Elt`, so `Key` defaults to identity —
        // absent from NUM ⇒ rejected.
        let (db, views, mut i) = setup(
            "fth TWO is sorts Elt Key . endfth\n\
             fmod NUM is sort N . endfm\n\
             view V from TWO to NUM is sort Elt to N . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("failed to find sort Key in NUM"), "got: {err}");
    }
}
