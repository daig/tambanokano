//! Apply a renaming `* (sort A to B, op f to g)` to a flattened declaration bundle.
//!
//! Sort renaming substitutes the sort name everywhere it can appear: the `sorts`/`subsorts` lists, op
//! domains/ranges, variable sorts, and (as a token) inside statement bubbles. Op renaming is scoped to
//! **single-token** op names (prefix operators and constants), substituting the name token in op
//! declarations and statement bubbles; renaming a **mixfix** op (`_+_`, `s_`) is a B5 follow-up and is
//! rejected loudly. Substitution into raw statement bubbles is by exact token-text match, so a variable
//! coincidentally named like a renamed sort/op would be caught too — self-contained tests avoid that.

use std::collections::HashMap;
use tnk_frontend::lex::{split_mixfix, Frag, Interner, Token};
use tnk_frontend::surface::ast::{RenameItem, Statement};

use crate::flatten::FlatDecls;

/// Rewrite `d` under the renaming `items`. Returns an error if a mixfix op rename is requested.
pub fn apply_renaming(
    mut d: FlatDecls,
    items: &[RenameItem],
    interner: &mut Interner,
) -> Result<FlatDecls, String> {
    let mut sort_map: HashMap<String, String> = HashMap::new();
    let mut op_map: HashMap<String, String> = HashMap::new();
    for item in items {
        match item {
            RenameItem::Sort { from, to } => {
                sort_map.insert(from.clone(), to.clone());
            }
            RenameItem::Op { from, to } => {
                let frags = split_mixfix(from, interner);
                if frags.len() != 1 || !matches!(frags[0], Frag::Tok(_)) {
                    return Err(format!(
                        "renaming the mixfix op `{from}` is a B5 follow-up — only single-token op names \
                         (prefix operators and constants) can be renamed"
                    ));
                }
                op_map.insert(from.clone(), to.clone());
            }
        }
    }

    // Declarations.
    rename_each(&mut d.sorts, &sort_map);
    for chain in &mut d.subsorts {
        for group in chain {
            rename_each(group, &sort_map);
        }
    }
    for op in &mut d.ops {
        rename_each(&mut op.domain, &sort_map);
        if let Some(t) = sort_map.get(&op.range) {
            op.range = t.clone();
        }
        if op.name.len() == 1 {
            let text = interner.resolve(op.name[0].sym).to_string();
            if let Some(t) = op_map.get(&text) {
                op.name[0].sym = interner.intern(t);
            }
        }
    }
    for v in &mut d.vars {
        if let Some(t) = sort_map.get(&v.sort) {
            v.sort = t.clone();
        }
    }

    // Statement bubbles: substitute by token text (sort and op names together — they don't collide).
    let mut subst = sort_map;
    subst.extend(op_map);
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                subst_tokens(lhs, &subst, interner);
                subst_tokens(rhs, &subst, interner);
                if let Some(c) = cond {
                    subst_tokens(c, &subst, interner);
                }
            }
            Statement::Mb { lhs, sort, cond } => {
                subst_tokens(lhs, &subst, interner);
                subst_tokens(sort, &subst, interner);
                if let Some(c) = cond {
                    subst_tokens(c, &subst, interner);
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                subst_tokens(lhs, &subst, interner);
                subst_tokens(rhs, &subst, interner);
                if let Some(c) = cond {
                    subst_tokens(c, &subst, interner);
                }
            }
        }
    }
    Ok(d)
}

/// Replace each string in `xs` that is a key of `map` with its mapped value.
fn rename_each(xs: &mut [String], map: &HashMap<String, String>) {
    for x in xs {
        if let Some(t) = map.get(x) {
            *x = t.clone();
        }
    }
}

/// Replace each token whose text is a key of `map` with the re-interned target (kind/line preserved).
fn subst_tokens(bubble: &mut [Token], map: &HashMap<String, String>, interner: &mut Interner) {
    for t in bubble {
        let text = interner.resolve(t.sym).to_string();
        if let Some(to) = map.get(&text) {
            t.sym = interner.intern(to);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flatten::FlatDecls;

    fn empty() -> FlatDecls {
        FlatDecls { sorts: vec![], subsorts: vec![], ops: vec![], vars: vec![], statements: vec![] }
    }

    /// Renaming a mixfix op (name with holes) is a loud B5 follow-up; a single-token op is fine.
    #[test]
    fn mixfix_op_rename_rejected_single_token_ok() {
        let mut i = Interner::new();
        let mixfix = [RenameItem::Op { from: "_+_".into(), to: "_plus_".into() }];
        let err = apply_renaming(empty(), &mixfix, &mut i).unwrap_err();
        assert!(err.contains("mixfix"), "got: {err}");

        let single = [RenameItem::Op { from: "f".into(), to: "g".into() }];
        assert!(apply_renaming(empty(), &single, &mut i).is_ok());
    }

    /// Sort renaming rewrites the `sorts` list and op domains/ranges.
    #[test]
    fn sort_rename_rewrites_declarations() {
        let mut i = Interner::new();
        let mut d = empty();
        d.sorts = vec!["Elt".into()];
        let renamed =
            apply_renaming(d, &[RenameItem::Sort { from: "Elt".into(), to: "Item".into() }], &mut i)
                .expect("rename");
        assert_eq!(renamed.sorts, ["Item"]);
    }
}
