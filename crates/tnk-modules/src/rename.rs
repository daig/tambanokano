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
use tnk_frontend::lex::{Frag, Interner, Sym, Token, split_mixfix, tokenize};
use tnk_frontend::rename_terms::{OpRenamer, ReconTarget, ViewOpMap, ViewOpSubst};
use tnk_frontend::surface::ast::{Attrs, ModuleKind, PreModule, RenameItem, Statement, StratExpr};

use crate::flatten::FlatDecls;

/// One `op … to …` renaming, resolved. `dom_range` (`Some((domain, range))`) restricts the rename to the
/// single overload of `from` with that source signature (arity-disambiguated `op f : A B -> C to g`);
/// `None` renames every overload. `attrs` overrides the target op's attributes.
struct OpRenameSpec {
    from: String,
    to: String,
    dom_range: Option<(Vec<String>, String)>,
    attrs: Attrs,
}

/// Rewrite `d` under the renaming `items`. The grammar-aware mixfix path may fail to build the source
/// module's parser, which is surfaced as an `Err`.
pub fn apply_renaming(
    mut d: FlatDecls,
    items: &[RenameItem],
    interner: &mut Interner,
) -> Result<FlatDecls, String> {
    let mut sort_map: HashMap<String, String> = HashMap::new();
    // Every op rename, as an [`OpRenameSpec`] (from/to canonical names, optional disambiguating signature,
    // attribute override). Statement labels rename separately (`label l to m`).
    let mut op_renames: Vec<OpRenameSpec> = Vec::new();
    let mut label_map: HashMap<String, String> = HashMap::new();
    for item in items {
        match item {
            RenameItem::Sort { from, to } => {
                sort_map.insert(from.clone(), to.clone());
            }
            RenameItem::Op {
                from,
                to,
                dom_range,
                attrs,
            } => {
                op_renames.push(OpRenameSpec {
                    from: from.clone(),
                    to: to.clone(),
                    dom_range: dom_range.clone(),
                    attrs: attrs.clone(),
                });
            }
            RenameItem::Label { from, to } => {
                label_map.insert(from.clone(), to.clone());
            }
        }
    }

    // Every non-disambiguated operator map is reconstructed structurally from the source parse. This is
    // necessary when fixity changes (`pair` → `_+_`): swapping the prefix token in `pair(a,b)` would yield
    // the invalid `+(a,b)`. Signature-disambiguated maps retain the arity-aware surgical renamer.
    let structural_maps: Vec<ViewOpMap> = op_renames
        .iter()
        .filter(|s| s.dom_range.is_none())
        .map(|s| ViewOpMap {
            source: s.from.clone(),
            dom_range: None,
            target: ReconTarget::Op(s.to.clone()),
        })
        .collect();
    let structural = ViewOpSubst::new(&premodule_of(&d), &structural_maps, interner)?;
    let grammar_renames: Vec<(String, Option<usize>, String)> = op_renames
        .iter()
        .filter(|s| s.dom_range.is_some())
        .map(|s| {
            (
                s.from.clone(),
                s.dom_range.as_ref().map(|(d, _)| d.len()),
                s.to.clone(),
            )
        })
        .collect();
    let renamer = OpRenamer::new(&premodule_of(&d), &grammar_renames, interner)?;

    // Single-token op map (textual). Applied to statement bubbles and `id:` identity bubbles.
    let single_op_map: HashMap<String, String> = op_renames
        .iter()
        .filter(|s| s.dom_range.is_none() && is_single_token(&s.from, interner))
        .map(|s| (s.from.clone(), s.to.clone()))
        .collect();

    // Declarations.
    rename_each(&mut d.sorts, &sort_map);
    for chain in &mut d.subsorts {
        for group in chain {
            rename_each(group, &sort_map);
        }
    }
    for op in &mut d.ops {
        // Snapshot the pre-rename signature so an arity-disambiguated rename matches against the source
        // sorts (a sort rename in the same renaming may rewrite the domain below).
        let orig_domain = op.domain.clone();
        let orig_range = op.range.clone();
        rename_each(&mut op.domain, &sort_map);
        if let Some(t) = sort_map.get(&op.range) {
            op.range = t.clone();
        }
        let canon: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
        // Find the rename spec for this declaration: a disambiguated spec matches only the overload whose
        // signature equals the spec's; a plain spec matches every overload of the name.
        if let Some(spec) = op_renames.iter().find(|s| {
            s.from == canon
                && s.dom_range
                    .as_ref()
                    .is_none_or(|(d, r)| *d == orig_domain && *r == orig_range)
        }) {
            // Preserve the OO declaration's separated attribute suffix. `class C | a : S` desugars to
            // `[a, :, _]`; rebuilding `b:_` with `tokenize` alone collapses that source distinction and
            // Maude then prints renamed attributes as `b: value` instead of `b : value`.
            let spaced_attribute_suffix = op.name.len() > 1 && canon.ends_with(":_");
            let suffix = spaced_attribute_suffix.then(|| {
                let n = op.name.len();
                [op.name[n - 2], op.name[n - 1]]
            });
            op.name = tokenize(&spec.to, interner);
            if let (Some(suffix), Some(label)) = (suffix, spec.to.strip_suffix(":_")) {
                op.name = tokenize(label, interner);
                op.name.extend(suffix);
            }
            apply_attr_override(&mut op.attrs, &spec.attrs);
        }
        // Identity attributes are arbitrary ground terms: rewrite their operator occurrences through
        // the same grammar-aware path as statements, then apply textual single-op/sort renames.
        if let Some(idb) = &mut op.attrs.id {
            if let Some(r) = structural.as_ref() {
                *idb = r.rewrite(idb, interner);
            }
            if let Some(r) = renamer.as_ref() {
                *idb = r.rewrite(idb, interner);
            }
            subst_tokens(idb, &single_op_map, interner);
            subst_sort_tokens(idb, &sort_map, interner);
        }
        // `special (op-hook …)` signatures reference OTHER ops by name (build_sig resolves hooks by
        // name), so a renamed referenced op must be tracked — INT * (op s_ : Nat -> NzNat to $succ)
        // must repoint every succSymbol op-hook at $succ or the renamed module loses its builtins
        // (stock machine-int.maude). Sort names inside hook signatures and term-hook constants
        // rename like everything else.
        if let Some(sp) = &mut op.attrs.special {
            for (_purpose, toks) in &mut sp.op_hooks {
                let Some(colon) = toks.iter().position(|t| interner.resolve(t.sym) == ":") else {
                    continue;
                };
                let name_canon: String = toks[..colon]
                    .iter()
                    .map(|t| interner.resolve(t.sym))
                    .collect();
                let arrow = toks.iter().position(|t| interner.resolve(t.sym) == "~>");
                let (dom, rng): (Vec<String>, Option<String>) = match arrow {
                    Some(a) => (
                        toks[colon + 1..a]
                            .iter()
                            .map(|t| interner.resolve(t.sym).to_string())
                            .collect(),
                        toks.get(a + 1).map(|t| interner.resolve(t.sym).to_string()),
                    ),
                    None => (Vec::new(), None),
                };
                if let Some(r) = op_renames.iter().find(|s| {
                    s.from == name_canon
                        && s.dom_range
                            .as_ref()
                            .is_none_or(|(d, rr)| *d == dom && Some(rr) == rng.as_ref())
                }) {
                    let mut new_toks = tokenize(&r.to, interner);
                    new_toks.extend_from_slice(&toks[colon..]);
                    *toks = new_toks;
                }
                subst_sort_tokens(toks, &sort_map, interner);
            }
            for (_purpose, toks) in &mut sp.term_hooks {
                subst_tokens(toks, &single_op_map, interner);
                subst_sort_tokens(toks, &sort_map, interner);
            }
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
    for op in &mut d.ops {
        if let Some(idb) = &mut op.attrs.id {
            *idb = qualify_constants(idb, &const_qual, &lparen, interner);
        }
    }

    // Statement bubbles: op renames (mixfix grammar-aware, then textual sorts/single ops), then constant
    // qualification.
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                rewrite_term(
                    rhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
            Statement::Mb {
                lhs, sort, cond, ..
            } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                subst_sort_tokens(sort, &sort_map, interner);
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                rewrite_term(
                    rhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                if let Some(c) = cond {
                    rewrite_cond(c, &sort_map, &single_op_map, &const_qual, &lparen, interner);
                }
            }
        }
    }

    let rename_identity = format!("{items:?}");
    for decl in &mut d.strat_decls {
        rename_each(&mut decl.domain, &sort_map);
        if let Some(to) = sort_map.get(&decl.subject) {
            decl.subject = to.clone();
        }
        decl.home = None;
        if let Some(origin) = &mut decl.origin {
            origin.push_str(&rename_identity);
        }
    }
    for def in &mut d.strat_defs {
        def.home = None;
        if let Some(origin) = &mut def.origin {
            origin.push_str(&rename_identity);
        }
        for param in &mut def.params {
            rewrite_term(
                param,
                structural.as_ref(),
                renamer.as_ref(),
                &sort_map,
                &single_op_map,
                &const_qual,
                &lparen,
                interner,
            );
        }
        rewrite_strategy_expr(
            &mut def.body,
            structural.as_ref(),
            renamer.as_ref(),
            &sort_map,
            &single_op_map,
            &const_qual,
            &lparen,
            &label_map,
            interner,
        );
        if let Some(cond) = &mut def.cond {
            rewrite_cond(
                cond,
                &sort_map,
                &single_op_map,
                &const_qual,
                &lparen,
                interner,
            );
        }
    }
    // Statement-label renames (`label l to m`): rewrite the label field of each statement (rule/eq/mb).
    if !label_map.is_empty() {
        for st in &mut d.statements {
            let (Statement::Eq { label, .. }
            | Statement::Mb { label, .. }
            | Statement::Rule { label, .. }) = st;
            if let Some(l) = label
                && let Some(to) = label_map.get(l)
            {
                *l = to.clone();
            }
        }
    }
    Ok(d)
}

/// Apply an ordinary module renaming to every term-bearing leaf of a strategy expression. Strategy names
/// themselves require Maude's separate `strat … to …` mapping and are intentionally left unchanged.
#[allow(clippy::too_many_arguments)]
fn rewrite_strategy_expr(
    expr: &mut StratExpr,
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    label_map: &HashMap<String, String>,
    interner: &mut Interner,
) {
    let mut rewrite_term_bubble = |bubble: &mut Vec<Token>| {
        rewrite_term(
            bubble,
            structural,
            renamer,
            sort_map,
            single_op_map,
            const_qual,
            lparen,
            interner,
        );
    };
    match expr {
        StratExpr::Idle | StratExpr::Fail | StratExpr::All => {}
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            if let Some(to) = label_map.get(label) {
                *label = to.clone();
            }
            for (variable, value) in subst {
                rewrite_term_bubble(variable);
                rewrite_term_bubble(value);
            }
            drop(rewrite_term_bubble);
            for child in substrats {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Top(child)
        | StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => {
            drop(rewrite_term_bubble);
            rewrite_strategy_expr(
                child,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
        }
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            drop(rewrite_term_bubble);
            rewrite_strategy_expr(
                left,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
            rewrite_strategy_expr(
                right,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            drop(rewrite_term_bubble);
            for child in [test, success, failure] {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Test { pattern, cond, .. } => {
            rewrite_term_bubble(pattern);
            drop(rewrite_term_bubble);
            if let Some(cond) = cond {
                rewrite_cond(cond, sort_map, single_op_map, const_qual, lparen, interner);
            }
        }
        StratExpr::MatchRew {
            pattern,
            cond,
            subs,
            ..
        } => {
            rewrite_term_bubble(pattern);
            for (variable, _) in subs.iter_mut() {
                rewrite_term_bubble(variable);
            }
            drop(rewrite_term_bubble);
            if let Some(cond) = cond {
                rewrite_cond(cond, sort_map, single_op_map, const_qual, lparen, interner);
            }
            for (_, child) in subs {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Sugar { args, .. } => {
            drop(rewrite_term_bubble);
            for child in args {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Call { args, .. } => {
            for arg in args {
                rewrite_term_bubble(arg);
            }
        }
    }
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
    for (index, t) in b.iter().enumerate() {
        let already_qualified = index > 0
            && index + 2 < b.len()
            && interner.resolve(b[index - 1].sym) == "("
            && interner.resolve(b[index + 1].sym) == ")"
            && interner.resolve(b[index + 2].sym).starts_with('.');
        if !already_qualified && let Some(suffix) = const_qual.get(interner.resolve(t.sym)) {
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
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &mut Interner,
) {
    if let Some(r) = structural {
        *b = r.rewrite(b, interner);
    }
    if let Some(r) = renamer {
        *b = r.rewrite(b, interner);
    }
    subst_sort_tokens(b, sort_map, interner);
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
    subst_sort_tokens(b, sort_map, interner);
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
        } else if let Some((base, count)) = text.rsplit_once('^')
            && !base.is_empty()
            && !count.is_empty()
            && count.bytes().all(|b| b.is_ascii_digit())
            && let Some(to) = map.get(base)
        {
            // An iter application is one lexical token (`g^1000000`), but the renamed symbol is its
            // `g` prefix. Preserve the scalar count while re-rooting the identity/statement at the target
            // operator; treating the whole token as a stale source name makes copied compact identities
            // fail to parse after `op g to h`.
            t.sym = interner.intern(&format!("{to}^{count}"));
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

/// Replace sort names in a token bubble, including structured spellings split by the lexer
/// (`Vector{Int0}` -> `Vector`, `{`, `Int0`, `}`), dotted sort qualifiers, and colon variables.
fn subst_sort_tokens(
    bubble: &mut Vec<Token>,
    map: &HashMap<String, String>,
    interner: &mut Interner,
) {
    struct Mapping {
        source: Vec<Sym>,
        target: Vec<Token>,
        source_name: String,
        target_name: String,
    }

    let mut mappings = Vec::with_capacity(map.len() * 2);
    for (from, to) in map {
        for dotted in [false, true] {
            let source_text = if dotted {
                format!(".{from}")
            } else {
                from.clone()
            };
            let target_text = if dotted { format!(".{to}") } else { to.clone() };
            mappings.push(Mapping {
                source: tokenize(&source_text, interner)
                    .into_iter()
                    .map(|token| token.sym)
                    .collect(),
                target: tokenize(&target_text, interner),
                source_name: from.clone(),
                target_name: to.clone(),
            });
        }
    }
    mappings.sort_by(|left, right| {
        right
            .source
            .len()
            .cmp(&left.source.len())
            .then_with(|| left.source_name.cmp(&right.source_name))
    });

    let mut index = 0;
    while index < bubble.len() {
        // The lexer keeps an on-the-fly variable with a structured sort as one identifier token
        // (`L:List{Nat}`), while `tokenize("List{Nat}")` below necessarily yields several tokens.
        // Handle that exact suffix before the token-sequence matcher.
        if let Some((name, sort)) = interner.resolve(bubble[index].sym).rsplit_once(':')
            && !name.is_empty()
            && let Some(target) = map.get(sort)
        {
            bubble[index].sym = interner.intern(&format!("{name}:{target}"));
            index += 1;
            continue;
        }
        let exact = mappings.iter().find(|mapping| {
            index + mapping.source.len() <= bubble.len()
                && bubble[index..index + mapping.source.len()]
                    .iter()
                    .map(|token| token.sym)
                    .eq(mapping.source.iter().copied())
        });
        let colon = if exact.is_none() {
            let text = interner.resolve(bubble[index].sym);
            text.split_once(':').and_then(|(name, first)| {
                mappings.iter().find_map(|mapping| {
                    let source_first = mapping.source.first().map(|&sym| interner.resolve(sym))?;
                    let rest = &mapping.source[1..];
                    (name.len() + first.len() + 1 == text.len()
                        && first == source_first
                        && index + 1 + rest.len() <= bubble.len()
                        && bubble[index + 1..index + 1 + rest.len()]
                            .iter()
                            .map(|token| token.sym)
                            .eq(rest.iter().copied()))
                    .then(|| (name.to_string(), mapping))
                })
            })
        } else {
            None
        };

        let (consumed, mut replacement) = if let Some(mapping) = exact {
            (mapping.source.len(), mapping.target.clone())
        } else if let Some((name, mapping)) = colon {
            (
                mapping.source.len(),
                tokenize(&format!("{name}:{}", mapping.target_name), interner),
            )
        } else {
            index += 1;
            continue;
        };
        let line = bubble[index].line;
        for token in &mut replacement {
            token.line = line;
        }
        let replacement_len = replacement.len();
        bubble.splice(index..index + consumed, replacement);
        index += replacement_len;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flatten::FlatDecls;
    use tnk_frontend::surface::parser::Parser;

    fn empty() -> FlatDecls {
        FlatDecls {
            sorts: vec![],
            subsorts: vec![],
            ops: vec![],
            vars: vec![],
            statements: vec![],
            strat_decls: vec![],
            strat_defs: vec![],
        }
    }

    /// A single-token op rename (a constant / prefix op) needs no grammar and applies textually.
    #[test]
    fn single_token_op_rename_ok() {
        let mut i = Interner::new();
        let single = [RenameItem::Op {
            from: "f".into(),
            to: "g".into(),
            dom_range: None,
            attrs: Attrs::default(),
        }];
        assert!(apply_renaming(empty(), &single, &mut i).is_ok());
    }

    /// Sort renaming rewrites the `sorts` list and op domains/ranges.
    #[test]
    fn sort_rename_rewrites_declarations() {
        let mut i = Interner::new();
        let mut d = empty();
        d.sorts = vec!["Elt".into()];
        let renamed = apply_renaming(
            d,
            &[RenameItem::Sort {
                from: "Elt".into(),
                to: "Item".into(),
            }],
            &mut i,
        )
        .expect("rename");
        assert_eq!(renamed.sorts, ["Item"]);
    }

    #[test]
    fn sort_rename_rewrites_structured_colon_variable() {
        let mut i = Interner::new();
        let mut bubble = tokenize("L:List{Nat}", &mut i);
        assert_eq!(bubble.len(), 1, "colon variable is one lexer token");
        subst_sort_tokens(
            &mut bubble,
            &HashMap::from([("List{Nat}".to_string(), "NatList".to_string())]),
            &mut i,
        );
        assert_eq!(i.resolve(bubble[0].sym), "L:NatList");
    }

    #[test]
    fn compound_identity_reconstructs_across_fixity_and_iter_renames() {
        let mut i = Interner::new();
        let tokens = tokenize(
            "fmod R is sort S . ops a b : -> S [ctor] . op g : S -> S [ctor iter] . \
             op pair : S S -> S [ctor] . \
             op join : S S -> S [assoc id: pair(g^1000000(a),b)] . endfm",
            &mut i,
        );
        let pm = Parser::new(&tokens, &i)
            .parse_source()
            .expect("parse")
            .modules
            .remove(0);
        let d = FlatDecls {
            sorts: pm.sorts,
            subsorts: pm.subsorts,
            ops: pm.ops,
            vars: pm.vars,
            statements: pm.statements,
            strat_decls: pm.strat_decls,
            strat_defs: pm.strat_defs,
        };
        let op = |from: &str, to: &str| RenameItem::Op {
            from: from.into(),
            to: to.into(),
            dom_range: None,
            attrs: Attrs::default(),
        };
        let renamed = apply_renaming(
            d,
            &[
                RenameItem::Sort {
                    from: "S".into(),
                    to: "T".into(),
                },
                op("a", "x"),
                op("b", "y"),
                op("g", "h"),
                op("pair", "duo"),
                op("join", "merge"),
            ],
            &mut i,
        )
        .expect("rename");
        let join = renamed
            .ops
            .iter()
            .find(|op| op.name.iter().map(|t| i.resolve(t.sym)).collect::<String>() == "merge")
            .expect("join");
        let identity = join.attrs.id.as_ref().expect("identity");
        let text: String = identity.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "duo(h^1000000((x).T),(y).T)");
        tnk_frontend::load::build_loaded_module(&premodule_of(&renamed), &mut i)
            .expect("renamed compound identity builds");
    }
}
