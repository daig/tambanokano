//! Apply a renaming `* (sort A to B, op f to g)` to a flattened declaration bundle.
//!
//! Sort renaming substitutes the sort name everywhere it can appear: the `sorts`/`subsorts` lists, op
//! domains/ranges, variable sorts, and (as a token) inside statement bubbles. **Single-token** op
//! renaming (prefix operators and constants, `empty to none`) substitutes the name token in op
//! declarations and statement bubbles by exact text. A **mixfix** op renaming (`_,_ to _;_`) cannot be
//! done by text — an operator comma and an argument separator are the same token (`delete(E, (E, S))`,
//! `if E in S' then E, A else A fi`) — so it is done *grammar-aware*: build the source module's parser
//! ([`OpRenamer`]), parse each term bubble, and replace only the literal fragment tokens at the
//! parse-identified operator positions. The renaming's optional `[ … ]` overrides the target op's
//! attributes (the prelude's `op _,_ to _;_ [prec 43]`).

use std::collections::{HashMap, HashSet};
use tnk_frontend::lex::{split_mixfix, tokenize, Frag, Interner, Token};
use tnk_frontend::rename_terms::OpRenamer;
use tnk_frontend::surface::ast::{Attrs, ModuleKind, PreModule, RenameItem, Statement};

use crate::flatten::FlatDecls;

/// Rewrite `d` under the renaming `items`. The grammar-aware mixfix path may fail to build the source
/// module's parser, which is surfaced as an `Err`.
pub fn apply_renaming(
    mut d: FlatDecls,
    items: &[RenameItem],
    interner: &mut Interner,
) -> Result<FlatDecls, String> {
    let mut sort_map: HashMap<String, String> = HashMap::new();
    // Every op rename, as (from canonical name, to canonical name, attribute override).
    let mut op_renames: Vec<(String, String, Attrs)> = Vec::new();
    for item in items {
        match item {
            RenameItem::Sort { from, to } => {
                sort_map.insert(from.clone(), to.clone());
            }
            RenameItem::Op { from, to, attrs } => {
                op_renames.push((from.clone(), to.clone(), attrs.clone()));
            }
        }
    }

    // Single-token op renames (constants/prefix ops) substitute textually everywhere; a mixfix op
    // rename needs grammar-aware term rewriting (only the parser can tell an operator fragment from an
    // argument separator). Build that renamer over the **pre-rename** declarations, before any mutation.
    let mixfix_pairs: Vec<(String, String)> = op_renames
        .iter()
        .filter(|(from, ..)| !is_single_token(from, interner))
        .map(|(from, to, _)| (from.clone(), to.clone()))
        .collect();
    let renamer = OpRenamer::new(&premodule_of(&d), &mixfix_pairs, interner)?;

    // Single-token op map (textual). Applied to statement bubbles and `id:` identity bubbles.
    let single_op_map: HashMap<String, String> = op_renames
        .iter()
        .filter(|(from, ..)| is_single_token(from, interner))
        .map(|(from, to, _)| (from.clone(), to.clone()))
        .collect();
    // Op-declaration rename map: canonical from-name → (target canonical name, attribute override). Covers
    // single + mixfix. The declaration's name is replaced **wholesale** by the target's token vector (see
    // the op loop) — not by per-fragment surgery, which would corrupt a single-token mixfix name like
    // `_+_` (one token, no lexer-punctuation to split it) into a prefix op by overwriting the whole token
    // with the target's first literal fragment.
    let op_decl_map: HashMap<String, (String, Attrs)> = op_renames
        .iter()
        .map(|(from, to, a)| (from.clone(), (to.clone(), a.clone())))
        .collect();

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
        let canon: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
        if let Some((to_name, ovr)) = op_decl_map.get(&canon) {
            // Replace the op's name wholesale with the target's token vector. `tokenize` reproduces the
            // canonical spelling — one token for a hole-bearing name with no lexer-punctuation (`_plus_`,
            // `_;_`), split tokens for a punctuation name (`_,_` → `_ , _`) — so the rebuilt op keeps the
            // target's mixfix shape (holes preserved) rather than collapsing to a prefix op.
            op.name = tokenize(to_name, interner);
            apply_attr_override(&mut op.attrs, ovr);
        }
        // The `id:` identity element is a constant — rename it like any other (single-token op / sort).
        if let Some(idb) = &mut op.attrs.id {
            subst_tokens(idb, &single_op_map, interner);
            subst_tokens(idb, &sort_map, interner);
        }
    }
    for v in &mut d.vars {
        if let Some(t) = sort_map.get(&v.sort) {
            v.sort = t.clone();
        }
    }

    // Constants whose (final) range sort is a rename *target* are instance-specific (`nil : -> NatList`,
    // the renamed `none : -> QidSet`): two instantiations of the same parameterized module (`NAT-LIST` +
    // `QID-LIST` in `META-MODULE`) share the constant's name across distinct kinds, so a bare `nil` in an
    // inlined equation parses ambiguously once both are merged. Sort-qualify each such occurrence as
    // `(nil).NatList` — the parse-time kind selector is a no-op on the built term but disambiguates the
    // overload. (The flattener already inlines *variables* as colon-vars for the same reason; this is the
    // constant analogue.) Only renamed-sort constants are touched, so base constants (`true`, `0`) are not.
    let targets: HashSet<&String> = sort_map.values().collect();
    let const_qual: HashMap<String, Vec<Token>> = d
        .ops
        .iter()
        .filter(|op| op.domain.is_empty() && targets.contains(&op.range))
        .map(|op| {
            let name: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
            // `c` → `( c ) .Sort` with the dotted sort lexed as the qualifier grammar expects
            // (`.NatList`, or `.List`,`{`,`Nat`,`}` for a structured target).
            let suffix = tokenize(&format!(") .{}", op.range), interner);
            (name, suffix)
        })
        .collect();
    let lparen = tokenize("(", interner);

    // Statement bubbles: op renames (mixfix grammar-aware, then textual sorts/single ops), then constant
    // qualification.
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                rewrite_term(lhs, renamer.as_ref(), &sort_map, &single_op_map, &const_qual, &lparen, interner);
                rewrite_term(rhs, renamer.as_ref(), &sort_map, &single_op_map, &const_qual, &lparen, interner);
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
            Statement::Mb { lhs, sort, cond, .. } => {
                rewrite_term(lhs, renamer.as_ref(), &sort_map, &single_op_map, &const_qual, &lparen, interner);
                subst_tokens(sort, &sort_map, interner);
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                rewrite_term(lhs, renamer.as_ref(), &sort_map, &single_op_map, &const_qual, &lparen, interner);
                rewrite_term(rhs, renamer.as_ref(), &sort_map, &single_op_map, &const_qual, &lparen, interner);
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
        }
    }
    Ok(d)
}

/// Expand each bare constant occurrence `c` (a key of `const_qual`) into the sort-qualified `( c ) .Sort`
/// — disambiguating an overload shared across two instantiations. A single left-to-right pass: the
/// emitted constant token is the original (never re-scanned).
fn qualify_constants(
    b: &[Token],
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &Interner,
) -> Vec<Token> {
    if const_qual.is_empty() {
        return b.to_vec();
    }
    let mut out = Vec::with_capacity(b.len());
    for t in b {
        if let Some(suffix) = const_qual.get(interner.resolve(t.sym)) {
            out.extend_from_slice(lparen);
            out.push(*t);
            out.extend_from_slice(suffix);
        } else {
            out.push(*t);
        }
    }
    out
}

/// Rewrite one term bubble: grammar-aware mixfix op renames first (on the pre-rename bubble, via the
/// source parser), then textual sort + single-token op renames, then constant qualification.
#[allow(clippy::too_many_arguments)]
fn rewrite_term(
    b: &mut Vec<Token>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &mut Interner,
) {
    if let Some(r) = renamer {
        *b = r.rewrite(b, interner);
    }
    subst_tokens(b, sort_map, interner);
    subst_tokens(b, single_op_map, interner);
    *b = qualify_constants(b, const_qual, lparen, interner);
}

/// Rewrite a condition bubble (textual sort + single-token op; constant qualification). A mixfix op
/// rename inside a condition fragment is not reached — the prelude has none.
fn rewrite_cond(
    b: &mut Vec<Token>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &mut Interner,
) {
    subst_tokens(b, sort_map, interner);
    subst_tokens(b, single_op_map, interner);
    *b = qualify_constants(b, const_qual, lparen, interner);
}

/// A `PreModule` carrying `d`'s declarations (for building the source parser). Fully flattened, so it has
/// no imports/parameters; system-kind so any rule bubbles parse.
fn premodule_of(d: &FlatDecls) -> PreModule {
    PreModule {
        name: "$RENAME-SRC".to_string(),
        kind: ModuleKind::System,
        is_theory: false,
        is_strategy: false,
        // A scaffold for building the renaming source grammar (no statements are executed here), so
        // object-pattern completion is irrelevant.
        is_object: false,
        params: Vec::new(),
        imports: Vec::new(),
        sorts: d.sorts.clone(),
        subsorts: d.subsorts.clone(),
        ops: d.ops.clone(),
        vars: d.vars.clone(),
        statements: d.statements.clone(),
        strat_decls: Vec::new(),
        strat_defs: Vec::new(),
    }
}

/// Whether `name` is a single-token op name (a constant or prefix operator — no holes).
fn is_single_token(name: &str, interner: &mut Interner) -> bool {
    let frags = split_mixfix(name, interner);
    frags.len() == 1 && matches!(frags[0], Frag::Tok(_))
}

/// Overlay the renaming's attribute overrides onto the target op's attributes (the prelude uses
/// `[prec 43]`; `gather`/`strat` are carried for completeness).
fn apply_attr_override(attrs: &mut Attrs, ovr: &Attrs) {
    if ovr.prec.is_some() {
        attrs.prec = ovr.prec;
    }
    if ovr.gather.is_some() {
        attrs.gather = ovr.gather.clone();
    }
    if ovr.strat.is_some() {
        attrs.strat = ovr.strat.clone();
    }
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
        } else if let Some((name, sort)) = text.rsplit_once(':')
            && !name.is_empty()
            && let Some(to) = map.get(sort)
        {
            // A glued colon variable `name:sort` (e.g. a statement variable inlined by the flattener's
            // `inline_own_vars`): rename its sort component (`A:Elt ↦ A:Item`), as the instantiation
            // path does. The whole-token branch above can't see the sort buried after the `:`.
            t.sym = interner.intern(&format!("{name}:{to}"));
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

    /// A single-token op rename (a constant / prefix op) needs no grammar and applies textually.
    #[test]
    fn single_token_op_rename_ok() {
        let mut i = Interner::new();
        let single =
            [RenameItem::Op { from: "f".into(), to: "g".into(), attrs: Attrs::default() }];
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
