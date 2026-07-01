//! Object-pattern completion (Pillar 2.5-E) — a faithful port of Maude's `ooProcess`/`ooTransform.cc`
//! statement transformer, run by [`load_statements`](crate::load) on the parsed [`Term`]s of an
//! **object module** (`omod`) before they are compiled into engine equations/rules.
//!
//! For each object pattern `< O : C | atts >` in a statement, completion makes the statement match objects
//! that carry *more* than the mentioned attributes, and rules written for a class apply to its subclasses:
//!
//! 1. **Class constant → variable.** If `C` is a class *constant* (an arity-0 ctor ranging on a class
//!    sort — a strict subsort of `Cid`), every occurrence of this object (LHS + RHS/condition) has `C`
//!    replaced by one fresh variable `V:C`. A `V:C` matches any subclass constant (`Savings < Account`),
//!    so the rule is subclass-polymorphic. A class *variable* is left alone.
//! 2. **Attribute-set variable.** The LHS (pattern) object gets a fresh `Atts:AttributeSet` variable
//!    spliced into its attribute set (`bal : N` → `bal : N, Atts`), capturing the object's *other*
//!    attributes; each RHS/condition occurrence of the same object gets that **same** `Atts` variable, so
//!    the extra attributes are carried through.
//! 3. **Missing / extra attributes.** An attribute in the pattern but absent from an RHS occurrence is
//!    copied back to it (so it is preserved); an attribute in some RHS occurrence but absent from the
//!    pattern is added to the pattern as a fresh kind-variable attribute `a(A:[K])` (so the LHS matches
//!    objects that already carry it).
//!
//! Completion is **gated structurally**: it fires only on object patterns whose class argument is a class
//! constant / class-sorted variable, so CONFIGURATION's own `getClass` equation (`< O : C:Cid | A >`, with
//! `Cid` not a class sort) and any non-object statement pass through untouched. It runs only for `omod`s
//! (the [`is_object`](tnk_frontend_ast) flag), matching Maude, but the structural gate makes it a no-op
//! elsewhere regardless.

use std::collections::HashMap;

use tnk_core::engine::OoInfo;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Term, Var};

use crate::build_term::VarIndex;
use crate::sig::syntax::BuiltModule;

/// Where an object occurrence sits, which decides how completion rewrites it (Maude's `GatherMode`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// The statement's left-hand side (and its own object patterns) — the *defining* occurrence.
    Pattern,
    /// A right-hand side or a condition *subject* — carries the shared attribute-set variable.
    Subject,
    /// A condition *pattern* (`:=` lhs, rewrite-condition rhs). An object here disables completion.
    CondPattern,
}

/// One object occurrence's attribute set, decomposed: the individual attribute terms (keyed by their head
/// operator, first-seen order) and the attribute-set variable, if the source already wrote one.
struct Occ {
    attrs: Vec<(SymbolId, Term)>,
    set_var: Option<Var>,
}

/// The gathered facts about one object identity (all occurrences sharing an object name `O`).
struct ObjInfo {
    /// The object name (`arg 0`) — the identity key.
    oid: Term,
    /// The class sort (a strict subsort of `Cid`): the sort of `V` if the class is a constant, or the
    /// declared sort of the class variable.
    class_sort: SortId,
    /// The class argument is a constant (needs replacing with a fresh `V:class_sort` on all occurrences).
    class_is_constant: bool,
    pattern: Occ,
    subjects: Vec<Occ>,
}

/// The precomputed rewrite for one object identity (fresh variables allocated once, applied per occurrence).
struct ObjPlan {
    /// The fresh class variable term to place at `arg 1`, if the class argument was a constant.
    class_replace: Option<Term>,
    /// The attribute-set variable term appended to every occurrence (the existing pattern one, or a fresh
    /// `Atts`).
    atts_var: Term,
    /// The pattern's attribute terms (original + added kind-variable attributes), for RHS missing-copies.
    pattern_attrs: Vec<(SymbolId, Term)>,
    /// Kind-variable attributes to add to the LHS pattern (attributes some RHS has but the pattern lacks).
    added_attrs: Vec<(SymbolId, Term)>,
}

/// Run object-pattern completion on one statement's terms in place. `lhs` is the pattern; `rhs` the
/// right-hand side (equations/rules; `None` for memberships); `cond` the condition fragments. Fresh
/// variables are allocated into `vars` (so the caller's `nr_vars` must be read *after* this runs). A no-op
/// unless the statement contains an object pattern with a class-sorted class argument.
pub fn complete_statement(
    info: &OoInfo,
    m: &BuiltModule,
    vars: &mut VarIndex,
    lhs: &mut Term,
    rhs: Option<&mut Term>,
    cond: &mut [ConditionFragment],
) {
    // --- Gather (immutable walk over lhs / rhs / condition). ---
    let mut objs: Vec<ObjInfo> = Vec::new();
    let mut ignore = false;
    gather(lhs, Mode::Pattern, info, m, &mut objs, &mut ignore);
    if let Some(rhs) = &rhs {
        gather(rhs, Mode::Subject, info, m, &mut objs, &mut ignore);
    }
    for frag in cond.iter() {
        gather_condition(frag, info, m, &mut objs, &mut ignore);
    }
    if ignore || objs.is_empty() {
        return;
    }
    if !check_variables(&objs, lhs, rhs.as_deref(), cond) {
        return;
    }

    // --- Plan (allocate fresh variables per object: V, then Atts, then kind-var A's). ---
    let mut plans: HashMap<Term, ObjPlan> = HashMap::new();
    for obj in &objs {
        // Class constant → a fresh `V:class_sort` variable, shared across all occurrences.
        let class_replace = obj.class_is_constant.then(|| {
            let name = choose_fresh("V", vars);
            Term::var(vars.index_of(&name, obj.class_sort), obj.class_sort)
        });
        // The attribute-set variable: the pattern's own one, or a fresh `Atts:AttributeSet`.
        let atts_var = match &obj.pattern.set_var {
            Some(v) => Term::Var(v.clone()),
            None => {
                let name = choose_fresh("Atts", vars);
                Term::var(vars.index_of(&name, info.attr_set_sort), info.attr_set_sort)
            }
        };
        // Attributes that appear in some RHS/condition occurrence but not in the pattern: add them to the
        // pattern as fresh kind-variable attributes (Maude uses the attribute's domain kind).
        let pattern_syms: Vec<SymbolId> = obj.pattern.attrs.iter().map(|(s, _)| *s).collect();
        let mut added_attrs: Vec<(SymbolId, Term)> = Vec::new();
        for subj in &obj.subjects {
            for (sym, _) in &subj.attrs {
                if !pattern_syms.contains(sym) && !added_attrs.iter().any(|(s, _)| s == sym) {
                    let kind_sort = attribute_kind_sort(m, info, *sym);
                    let name = choose_fresh("A", vars);
                    let var = Term::var(vars.index_of(&name, kind_sort), kind_sort);
                    added_attrs.push((*sym, Term::op(*sym, vec![var])));
                }
            }
        }
        let mut pattern_attrs = obj.pattern.attrs.clone();
        pattern_attrs.extend(added_attrs.iter().cloned());
        plans.insert(
            obj.oid.clone(),
            ObjPlan { class_replace, atts_var, pattern_attrs, added_attrs },
        );
    }

    // --- Transform (mutable walk; rewrite each object occurrence from its plan). ---
    transform(lhs, Mode::Pattern, &plans, info);
    if let Some(rhs) = rhs {
        transform(rhs, Mode::Subject, &plans, info);
    }
    for frag in cond.iter_mut() {
        transform_condition(frag, &plans, info);
    }
}

/// Recursively collect object occurrences from `term` under `mode`.
fn gather(
    term: &Term,
    mode: Mode,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    if let Term::Op { symbol, args } = term {
        if *symbol == info.object_ctor && args.len() == 3 {
            record_object(args, mode, info, m, objs, ignore);
        }
        // Fall through to the general case (an object's arguments — or a soup's other elements — may hold
        // further objects), matching Maude's `gatherObjects`.
        for a in args {
            gather(a, mode, info, m, objs, ignore);
        }
    }
}

/// Record one object occurrence `< oid : class | atts >` (`args` = `[oid, class, atts]`), updating
/// `objs`/`ignore` as Maude's `gatherObjects` does for a fresh vs. repeated object name and a pattern vs.
/// subject position.
fn record_object(
    args: &[Term],
    mode: Mode,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    let (oid, class, atts) = (&args[0], &args[1], &args[2]);
    let existing = objs.iter().position(|o| o.oid == *oid);
    match existing {
        None => match mode {
            Mode::Pattern => {
                // First occurrence, on the LHS — the defining (pattern) occurrence.
                let Some((class_sort, class_is_constant)) = classify_class(class, info, m) else {
                    *ignore = true; // class argument is neither a class constant nor a class-sorted variable
                    return;
                };
                let Some(pattern) = decompose_attr_set(atts, info) else {
                    *ignore = true;
                    return;
                };
                objs.push(ObjInfo { oid: oid.clone(), class_sort, class_is_constant, pattern, subjects: Vec::new() });
            }
            // First seen on a RHS/condition: a "new" object with no LHS occurrence — quietly ignored.
            Mode::Subject => {}
            // An object pattern inside a condition fragment pattern disables completion.
            Mode::CondPattern => *ignore = true,
        },
        Some(idx) => match mode {
            // A duplicate object name on the LHS disables completion.
            Mode::Pattern => *ignore = true,
            Mode::CondPattern => *ignore = true,
            Mode::Subject => match decompose_attr_set(atts, info) {
                Some(occ) => objs[idx].subjects.push(occ),
                None => *ignore = true,
            },
        },
    }
}

/// Gather from a condition fragment, mapping each sub-term to its Maude `GatherMode`.
fn gather_condition(
    frag: &ConditionFragment,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            gather(lhs, Mode::Subject, info, m, objs, ignore);
            gather(rhs, Mode::Subject, info, m, objs, ignore);
        }
        ConditionFragment::SortTest { term, .. } => gather(term, Mode::Subject, info, m, objs, ignore),
        ConditionFragment::Matching { pattern, subject, .. } => {
            gather(pattern, Mode::CondPattern, info, m, objs, ignore);
            gather(subject, Mode::Subject, info, m, objs, ignore);
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            gather(lhs, Mode::Subject, info, m, objs, ignore);
            gather(pattern, Mode::CondPattern, info, m, objs, ignore);
        }
    }
}

/// Classify a class argument. Returns `(class_sort, is_constant)` for a class constant (an arity-0 ctor
/// ranging on a class sort) or a class-sorted variable, else `None` (which disables completion).
fn classify_class(class: &Term, info: &OoInfo, m: &BuiltModule) -> Option<(SortId, bool)> {
    match class {
        Term::Var(v) => info.class_sorts.contains(&v.sort).then_some((v.sort, false)),
        Term::Op { symbol, args } if args.is_empty() => {
            let range = m.engine.symbol_declarations(*symbol).first()?.1;
            info.class_sorts.contains(&range).then_some((range, true))
        }
        _ => None,
    }
}

/// Decompose an attribute-set term into its individual attribute terms (keyed by head operator) plus at
/// most one attribute-set variable. `None` (disabling completion) on a duplicate attribute, a second
/// set variable, or an unrecognized subterm — mirroring `analyzeAttributeSetArgument`.
fn decompose_attr_set(term: &Term, info: &OoInfo) -> Option<Occ> {
    let mut occ = Occ { attrs: Vec::new(), set_var: None };
    if walk_attr_set(term, info, &mut occ) {
        Some(occ)
    } else {
        None
    }
}

fn walk_attr_set(term: &Term, info: &OoInfo, occ: &mut Occ) -> bool {
    match term {
        // Nested `_,_` — recurse over the elements.
        Term::Op { symbol, args } if *symbol == info.attr_set_sym => {
            args.iter().all(|a| walk_attr_set(a, info, occ))
        }
        // The attribute-set identity `none` — the empty set; contributes nothing.
        Term::Op { symbol, args } if args.is_empty() && Some(*symbol) == info.none_sym => true,
        // A variable of the AttributeSet sort — the (single) set variable.
        Term::Var(v) if v.sort == info.attr_set_sort => {
            if occ.set_var.is_some() {
                return false; // two set variables — disable
            }
            occ.set_var = Some(v.clone());
            true
        }
        // Otherwise an attribute term, keyed by its head operator; a duplicate head disables completion.
        _ => match term.top_symbol() {
            Some(sym) if !occ.attrs.iter().any(|(s, _)| *s == sym) => {
                occ.attrs.push((sym, term.clone()));
                true
            }
            _ => false,
        },
    }
}

/// Maude's `checkVariables`: a set variable in the pattern must appear (identically) in every subject
/// occurrence and nowhere else; if the pattern has no set variable, no subject may have one. Returns
/// `false` to disable completion.
fn check_variables(
    objs: &[ObjInfo],
    lhs: &Term,
    rhs: Option<&Term>,
    cond: &[ConditionFragment],
) -> bool {
    // Occurrence counts per variable index, across the whole statement.
    let mut counts: HashMap<u32, usize> = HashMap::new();
    count_vars(lhs, &mut counts);
    if let Some(rhs) = rhs {
        count_vars(rhs, &mut counts);
    }
    for frag in cond {
        for t in condition_terms(frag) {
            count_vars(t, &mut counts);
        }
    }
    for obj in objs {
        let occurrences = 1 + obj.subjects.len();
        match &obj.pattern.set_var {
            None => {
                // No pattern set variable ⇒ no subject may carry one.
                if obj.subjects.iter().any(|s| s.set_var.is_some()) {
                    return false;
                }
            }
            Some(pv) => {
                // Every subject must carry the same set variable, used nowhere else.
                for s in &obj.subjects {
                    match &s.set_var {
                        Some(sv) if sv.index == pv.index => {}
                        _ => return false,
                    }
                }
                if counts.get(&pv.index).copied().unwrap_or(0) > occurrences {
                    return false;
                }
            }
        }
    }
    true
}

/// Rewrite each object occurrence in `term` under `mode` from its plan.
fn transform(term: &mut Term, mode: Mode, plans: &HashMap<Term, ObjPlan>, info: &OoInfo) {
    if let Term::Op { symbol, args } = term {
        if *symbol == info.object_ctor
            && args.len() == 3
            && let Some(plan) = plans.get(&args[0])
        {
            apply_object(args, mode, plan, info);
        }
        for a in args.iter_mut() {
            transform(a, mode, plans, info);
        }
    }
}

fn transform_condition(frag: &mut ConditionFragment, plans: &HashMap<Term, ObjPlan>, info: &OoInfo) {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            transform(lhs, Mode::Subject, plans, info);
            transform(rhs, Mode::Subject, plans, info);
        }
        ConditionFragment::SortTest { term, .. } => transform(term, Mode::Subject, plans, info),
        ConditionFragment::Matching { pattern, subject, .. } => {
            transform(pattern, Mode::CondPattern, plans, info);
            transform(subject, Mode::Subject, plans, info);
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            transform(lhs, Mode::Subject, plans, info);
            transform(pattern, Mode::CondPattern, plans, info);
        }
    }
}

/// Apply one object's plan to a `< oid : class | atts >` argument vector (`args[1]` = class, `args[2]` =
/// attribute set), rebuilding the attribute set per `mode`.
fn apply_object(args: &mut [Term], mode: Mode, plan: &ObjPlan, info: &OoInfo) {
    if let Some(vt) = &plan.class_replace {
        args[1] = vt.clone();
    }
    // The occurrence's own attributes + set variable, then the shared attribute-set variable.
    let mut own = Occ { attrs: Vec::new(), set_var: None };
    let _ = walk_attr_set(&args[2], info, &mut own);
    let atts = own.set_var.as_ref().map_or_else(|| plan.atts_var.clone(), |v| Term::Var(v.clone()));

    let mut elems: Vec<Term> = Vec::new();
    match mode {
        Mode::Pattern => {
            // Original attributes, then the added kind-variable attributes (subject-only ones).
            elems.extend(own.attrs.iter().map(|(_, t)| t.clone()));
            elems.extend(plan.added_attrs.iter().map(|(_, t)| t.clone()));
        }
        Mode::Subject | Mode::CondPattern => {
            // Pattern attributes this occurrence lacks (copied back), then its own attributes.
            for (sym, t) in &plan.pattern_attrs {
                if !own.attrs.iter().any(|(s, _)| s == sym) {
                    elems.push(t.clone());
                }
            }
            elems.extend(own.attrs.iter().map(|(_, t)| t.clone()));
        }
    }
    args[2] = if elems.is_empty() {
        atts
    } else {
        elems.push(atts);
        Term::op(info.attr_set_sym, elems)
    };
}

/// The kind (top/error sort) of an attribute operator's argument, for a fresh kind-variable attribute
/// `a(A:[K])` (Maude's `at.first->domainComponent(0)->sort(Sort::KIND)`). Attribute operators are unary
/// (`a :_ : S -> Attribute`); on the degenerate 0-ary case, fall back to the AttributeSet kind.
fn attribute_kind_sort(m: &BuiltModule, info: &OoInfo, attr_sym: SymbolId) -> SortId {
    let sorts = m.engine.sorts();
    let dom = m.engine.symbol_declarations(attr_sym).into_iter().find_map(|(d, _)| d.first().copied());
    sorts.error_sort(sorts.kind_of(dom.unwrap_or(info.attr_set_sort)))
}

/// Count occurrences of each variable index in `term`.
fn count_vars(term: &Term, counts: &mut HashMap<u32, usize>) {
    match term {
        Term::Var(v) => *counts.entry(v.index).or_insert(0) += 1,
        Term::Op { args, .. } => args.iter().for_each(|a| count_vars(a, counts)),
        Term::Na { .. } => {}
    }
}

/// The terms carried by a condition fragment (for variable counting).
fn condition_terms(frag: &ConditionFragment) -> Vec<&Term> {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => vec![lhs, rhs],
        ConditionFragment::SortTest { term, .. } => vec![term],
        ConditionFragment::Matching { pattern, subject, .. } => vec![pattern, subject],
        ConditionFragment::Rewrite { lhs, pattern, .. } => vec![lhs, pattern],
    }
}

/// Choose a variable name not already used in `vars`: the bare `base`, else `base2`, `base3`, … (Maude's
/// `chooseFreshVariableName`, whose numbering starts at 2).
fn choose_fresh(base: &str, vars: &VarIndex) -> String {
    let used = |name: &str| (0..vars.count()).any(|i| vars.name(i) == name);
    if !used(base) {
        return base.to_string();
    }
    let mut k = 2u64;
    loop {
        let name = format!("{base}{k}");
        if !used(&name) {
            return name;
        }
        k += 1;
    }
}
