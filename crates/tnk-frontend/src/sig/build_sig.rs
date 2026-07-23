//! `build_module`: drive the `tnk-core` `Engine`'s constructor API from a [`PreModule`], and record the
//! frontend's [`SymbolSyntax`] / name→id tables. Order is forced by three kernel contracts: sorts closed
//! before ops; **all** op declarations before any node is built; `special` hooks resolved to ids. So:
//! sorts → close → **pass A** declare every op (theory-dispatched) + record syntax → **pass A2** record the
//! built-in anchors (succ/zero/string/float/qid) once all names resolve → **pass B** attach
//! ctor/strat/special. Statements are left raw (parsed in B4.4, which needs the grammar).

use crate::lex::{Frag, Interner, Sym, Token, is_punct, split_mixfix};
use crate::sig::syntax::{BuiltModule, IdentitySpec, SymbolSyntax};
use crate::surface::ast::{Attrs, IdSide, PreModule, SpecialSpec};
use std::collections::HashMap;
use tnk_core::engine::Engine;
use tnk_core::ltl::TemporalHooks;
use tnk_core::smt::{SmtOp, SmtType};
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::{
    BoolHooks, CharClass, ConvOp, FltOp, MetaHooks, MetaOp, ModelCheckerHooks, NatHooks, NumOp,
    QidOp, SatSolverHooks, SpecialOp, StdStream, StrOp, SymbolId,
};

type R<T> = Result<T, String>;

#[derive(Clone, PartialEq, Eq)]
struct ConstructorAxiomProfile {
    assoc: bool,
    comm: bool,
    idem: bool,
    iter: bool,
    identity: Option<(IdSide, Vec<Sym>)>,
}

impl ConstructorAxiomProfile {
    fn from_attrs(attrs: &Attrs) -> Self {
        Self {
            assoc: attrs.assoc,
            comm: attrs.comm,
            idem: attrs.idem,
            iter: attrs.iter,
            identity: attrs.id.as_ref().map(|tokens| {
                (
                    attrs.id_side,
                    tokens.iter().map(|token| token.sym).collect(),
                )
            }),
        }
    }
}

/// The canonical mixfix name of an op (its name tokens concatenated): `[s_]`→`"s_"`, `[<_, ,, _>]`→`"<_,_>"`.
/// An operator name may be **parenthesized to quote** a name that would otherwise clash with a keyword or
/// the terminator `.` — Maude's `op (op_:_->_[_].) : …` (the META-MODULE constructor whose name starts with
/// the `op` keyword and ends in `.`). The outer parens are a quoting wrapper, not part of the name, so they
/// are stripped: the canonical name (and thus its grammar production and `sym_by_profile` key) is
/// `op_:_->_[_].`, matching the unparenthesized `op-hook` references.
pub fn canonical_name(name: &[Token], i: &Interner) -> String {
    // Two adjacent name tokens whose boundary chars are both *non-split* (not `_`/`:`/punct) were
    // space-separated in the source — two maudeIds only ever tokenize apart on whitespace — so the blank
    // between them is load-bearing: `op c d_` is the mixfix `c`, `d`, `_`, not the single literal `cd_`.
    // Keep it as a backtick (Maude's op-name spacing convention, `` c`d_ ``), which [`split_mixfix`] reads
    // back as a fragment boundary. A boundary touching a split char (`bal :_` → `bal:_`, `<_,_>`, `[]`)
    // needs no marker — split_mixfix already breaks there — so those canonical names are unchanged.
    let is_split = |c: char| c == '_' || c == ':' || is_punct(c);
    let mut out = String::new();
    let mut prev_last: Option<char> = None;
    for t in strip_outer_parens(name, i) {
        let s = i.resolve(t.sym);
        if let (Some(pl), Some(fc)) = (prev_last, s.chars().next())
            && !is_split(pl)
            && !is_split(fc)
        {
            out.push('`');
        }
        out.push_str(s);
        prev_last = s.chars().last().or(prev_last);
    }
    out
}

/// The inner tokens if `toks` is wrapped in a single balanced `( … )` pair, else `toks` unchanged. The
/// opening paren must match the *final* token (depth returns to 0 only at the end), so a name that merely
/// starts and ends with parens — `(a) b (c)` — is left intact.
fn strip_outer_parens<'a>(toks: &'a [Token], i: &Interner) -> &'a [Token] {
    if toks.len() < 2 || i.resolve(toks[0].sym) != "(" || i.resolve(toks[toks.len() - 1].sym) != ")"
    {
        return toks;
    }
    let mut depth = 0i32;
    for (k, t) in toks.iter().enumerate() {
        match i.resolve(t.sym) {
            "(" => depth += 1,
            ")" => depth -= 1,
            _ => {}
        }
        if depth == 0 && k + 1 != toks.len() {
            return toks; // closed before the end → not a single enclosing wrapper
        }
    }
    &toks[1..toks.len() - 1]
}

/// Resolve a sort name, handling the **kind** form `[S]` — the top (error) sort of S's connected
/// component, `error_sort(kind_of(S))` (`var B : [Bool]`, `op undefined : -> [Y$Elt]`). A plain name is
/// a direct lookup. The `[S]` form requires `close_sorts()` to have run (kinds exist), so it is used for
/// op domains/ranges and variable sorts (Pass A onward), never for subsorts (resolved before close).
fn resolve_sort(engine: &Engine, sorts: &HashMap<String, SortId>, name: &str) -> R<SortId> {
    if let Some(inner) = name.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
        // Single-sort `[S]` or multi-sort `[A, B]` (the kind of the component that contains A and B —
        // `kindNameDecember2022`). Every listed sort is in the same connected component, so its kind is
        // the same; resolve the first (depth-aware, so a structured sort `Map{X,Y}` is not split at its
        // inner `,`).
        let first = first_kind_component(inner);
        let inner_id = sorts
            .get(first)
            .copied()
            .ok_or_else(|| format!("unknown sort `{first}` in kind `[{inner}]`"))?;
        Ok(engine.sorts().error_sort(engine.sorts().kind_of(inner_id)))
    } else {
        sorts
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown sort `{name}`"))
    }
}

/// The first comma-separated sort of a multi-sort kind bracket's inner text, respecting `{ … }` / `[ … ]`
/// nesting so a structured sort (`Map{X,Y}`) is not split at its inner `,`. `[A,B]` → `A`; `[Map{X,Y}]`
/// → `Map{X,Y}`.
fn first_kind_component(inner: &str) -> &str {
    let mut depth = 0i32;
    for (idx, c) in inner.char_indices() {
        match c {
            '{' | '[' => depth += 1,
            '}' | ']' => depth -= 1,
            ',' if depth == 0 => return &inner[..idx],
            _ => {}
        }
    }
    inner
}

pub fn build_module(pm: &PreModule, interner: &mut Interner) -> R<BuiltModule> {
    let mut engine = Engine::new();
    let mut sorts: HashMap<String, SortId> = HashMap::new();

    // 1. Sorts + subsorts, then close.
    for name in &pm.sorts {
        let id = engine.add_sort(name.clone());
        sorts.insert(name.clone(), id);
    }
    let sort_id = |sorts: &HashMap<String, SortId>, name: &str| -> R<SortId> {
        sorts
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown sort `{name}`"))
    };
    for chain in &pm.subsorts {
        for w in chain.windows(2) {
            for sub in &w[0] {
                for sup in &w[1] {
                    engine.add_subsort(sort_id(&sorts, sub)?, sort_id(&sorts, sup)?);
                }
            }
        }
    }
    engine.close_sorts();

    let mut ops: HashMap<(String, usize), SymbolId> = HashMap::new();
    let mut name_to_sym: HashMap<String, SymbolId> = HashMap::new();
    let mut syntax: HashMap<SymbolId, SymbolSyntax> = HashMap::new();
    // Symbol identity is the **kind-profile** (name + domain/range connected components), not just
    // (name, arity): subsort overloading (same components, different sorts — `_+_ : NzNat Nat -> NzNat`
    // and `_+_ : Nat Nat -> Nat`) adds a declaration to the *same* symbol, but **ad-hoc** overloading
    // across different components (`wrap : Hue -> Box{ToColor}` and `wrap : Box{ToColor} -> Box{V}` from a
    // nested instantiation) makes **distinct** symbols, as in Maude — the argument kind, not the range,
    // selects the declaration group.
    let mut sym_by_profile: HashMap<(String, Vec<KindId>, KindId), SymbolId> = HashMap::new();
    // Each source declaration maps to its kernel symbol(s): one for an ordinary op, or — for a
    // `poly`/`Universal` op — one per kind (the per-kind expansion below). Later passes iterate it by the
    // source index, so it is pre-sized and each declaration stores at its own index (the loop below may
    // visit the entries out of source order — constants first, see next).
    let mut op_syms: Vec<Vec<SymbolId>> = vec![Vec::new(); pm.ops.len()];
    // Identity bubbles are parsed only after the per-module grammar exists.
    let mut identity_specs: Vec<IdentitySpec> = Vec::new();
    // Structural constructor axioms belong to each source overload, while the kernel executes one
    // folded Symbol theory. Retain the first profile long enough to mark disagreements before folding.
    let mut constructor_axiom_profiles: HashMap<SymbolId, ConstructorAxiomProfile> = HashMap::new();
    let mut constructor_flags: HashMap<SymbolId, bool> = HashMap::new();

    // Pass A: declare every op (theory-dispatched), record name→id + syntax. A `poly` op is expanded
    // here — necessarily after `close_sorts`, which is what creates the kinds/error sorts. Each
    // polymorphic position (the `poly` list: arguments 1-based, range `0`) becomes its kind's error
    // (top) sort, yielding one concrete declaration per kind — exactly Maude's `instantiatePolymorph`,
    // but eager over all kinds rather than lazy over used ones (reduction-identical; cf. `show module`).
    // `Universal` is never resolved as a sort: the `poly` list drives the substitution, so it can
    // never reach `sort_id` to become "unknown".
    //
    // Keep the established constants-first partition: it preserves symbol-index ordering while the
    // identity post-pass now handles every forward/compound reference.
    let mut decl_order: Vec<usize> = (0..pm.ops.len()).collect();
    decl_order.sort_by_key(|&idx| !pm.ops[idx].domain.is_empty());
    for &idx in &decl_order {
        let od = &pm.ops[idx];
        let cname = canonical_name(&od.name, interner);
        let arity = od.domain.len();

        // The (domain, range) profile(s) this declaration expands to.
        let mut profiles: Vec<(Vec<SortId>, SortId)> = match &od.attrs.poly {
            None => {
                let domain: Vec<SortId> = od
                    .domain
                    .iter()
                    .map(|s| resolve_sort(&engine, &sorts, s))
                    .collect::<R<_>>()?;
                vec![(domain, resolve_sort(&engine, &sorts, &od.range)?)]
            }
            Some(poly) => {
                let s = engine.sorts();
                let err_sorts: Vec<SortId> = s.kinds().map(|k| s.error_sort(k)).collect();
                err_sorts
                    .into_iter()
                    .map(|err| {
                        // poly position → this kind's error sort; otherwise the declared sort.
                        let domain: Vec<SortId> = od
                            .domain
                            .iter()
                            .enumerate()
                            .map(|(i, sn)| {
                                if poly.contains(&(i as u32 + 1)) {
                                    Ok(err)
                                } else {
                                    sort_id(&sorts, sn)
                                }
                            })
                            .collect::<R<_>>()?;
                        let range = if poly.contains(&0) {
                            err
                        } else {
                            sort_id(&sorts, &od.range)?
                        };
                        Ok((domain, range))
                    })
                    .collect::<R<_>>()?
            }
        };

        // A partial (`~>`) op ranges over the **kind** (error sort): an unreduced application is
        // kind-level, the built-in/equational result refining it when defined. (kind_of(range) is the
        // same component whether or not we already lifted it, so this is idempotent.)
        if od.partial {
            for (_, range) in profiles.iter_mut() {
                *range = engine.sorts().error_sort(engine.sorts().kind_of(*range));
            }
        }

        let mut decl_syms: Vec<SymbolId> = Vec::with_capacity(profiles.len());
        for (domain, range) in profiles {
            let dom_kinds: Vec<KindId> =
                domain.iter().map(|&s| engine.sorts().kind_of(s)).collect();
            let profile = (cname.clone(), dom_kinds, engine.sorts().kind_of(range));

            let sym = if let Some(&existing) = sym_by_profile.get(&profile) {
                let inherited = od.attrs.ditto;
                let ctor = if inherited {
                    constructor_flags.get(&existing).copied().unwrap_or(false)
                } else {
                    od.attrs.ctor
                };
                let incoming = ConstructorAxiomProfile::from_attrs(&od.attrs);
                if !inherited
                    && constructor_axiom_profiles
                        .get(&existing)
                        .is_some_and(|first| first != &incoming)
                {
                    engine.mark_inconsistent_constructor_axioms(existing);
                }
                engine.add_op_decl_with_ctor(existing, domain.clone(), range, ctor);
                constructor_flags.insert(existing, ctor);
                existing
            } else {
                let sym = declare_op(&mut engine, &cname, &od.attrs, &domain, range);
                constructor_axiom_profiles
                    .insert(sym, ConstructorAxiomProfile::from_attrs(&od.attrs));
                constructor_flags.insert(sym, od.attrs.ctor);
                sym_by_profile.insert(profile, sym);
                ops.entry((cname.clone(), arity)).or_insert(sym); // first symbol of this (name, arity)
                name_to_sym.entry(cname.clone()).or_insert(sym);
                let mut frags = split_mixfix(&cname, interner);
                let holes = frags.iter().filter(|f| matches!(f, Frag::Hole)).count();
                let mut prec = od.attrs.prec;
                let mut gather = od.attrs.gather.clone();
                let mut format = od.attrs.format.clone();
                if holes != 0 && holes != domain.len() {
                    // Underscore count ≠ arity: Maude warns and clears the mixfix syntax
                    // (entry.cc "number of underscores does not match number of arguments"),
                    // leaving the prefix form usable; prec/gather/format go with it. The
                    // warning text itself is deferred diagnostics (roadmap phase E).
                    frags = vec![Frag::Tok(interner.intern(&cname))];
                    prec = None;
                    gather = None;
                    format = None;
                }
                syntax.insert(
                    sym,
                    SymbolSyntax {
                        frags,
                        domain: domain.clone(),
                        range,
                        prec,
                        gather,
                        assoc: od.attrs.assoc,
                        iter: od.attrs.iter,
                        format,
                    },
                );
                sym
            };
            if let Some(tokens) = &od.attrs.id
                && !identity_specs.iter().any(|spec| spec.symbol == sym)
            {
                match od.attrs.id_side {
                    crate::surface::ast::IdSide::Both => engine.reserve_identity(sym, range),
                    crate::surface::ast::IdSide::Left => {
                        engine.reserve_one_sided_identity(
                            sym,
                            tnk_core::symbol::IdentitySide::Left,
                            range,
                        );
                    }
                    crate::surface::ast::IdSide::Right => {
                        engine.reserve_one_sided_identity(
                            sym,
                            tnk_core::symbol::IdentitySide::Right,
                            range,
                        );
                    }
                }
                identity_specs.push(IdentitySpec {
                    symbol: sym,
                    sort: range,
                    side: od.attrs.id_side,
                    tokens: tokens.clone(),
                });
            }
            decl_syms.push(sym);
        }
        op_syms[idx] = decl_syms;
    }

    // Pass A2: record the built-in anchors (now every name resolves).
    let mut nat_succ = None;
    let mut nat_zero = None;
    let mut string_sym = None;
    let mut float_sym = None;
    let mut qid_sym = None;
    let mut minus_sym = None;
    let mut division_sym = None;
    let mut true_sym = None;
    let mut false_sym = None;
    let mut succ_zero: HashMap<SymbolId, SymbolId> = HashMap::new();
    for (idx, od) in pm.ops.iter().enumerate() {
        let Some(spec) = &od.attrs.special else {
            continue;
        };
        let Some((class, data)) = &spec.id_hook else {
            continue;
        };
        let sym = op_syms[idx][0]; // anchors are concrete (non-poly) ⇒ exactly one instance
        match class.as_str() {
            "SuccSymbol" => {
                nat_succ = Some(sym);
                let proposed = term_hook_sym(spec, "zeroTerm", &name_to_sym, interner)
                    .ok_or("SuccSymbol missing its zeroTerm")?;
                let zero = engine.register_succ_zero(sym, proposed);
                nat_zero = Some(zero);
                succ_zero.insert(sym, zero);
            }
            "StringSymbol" => string_sym = Some(sym),
            "FloatSymbol" => float_sym = Some(sym),
            "QuotedIdentifierSymbol" => qid_sym = Some(sym),
            "MinusSymbol" => minus_sym = Some(sym),
            "DivisionSymbol" => division_sym = Some(sym),
            "SystemTrue" => true_sym = Some(sym),
            "SystemFalse" => false_sym = Some(sym),
            "SMT_NumberSymbol" => {
                let kind = match data.first().map(String::as_str) {
                    Some("integers") => SmtType::Integer,
                    Some("reals") => SmtType::Real,
                    _ => return Err("SMT_NumberSymbol needs `integers` or `reals`".into()),
                };
                let range = resolve_sort(&engine, &sorts, &od.range)?;
                engine.register_smt_number(sym, range, kind);
            }
            _ => {}
        }
    }

    // Pass B: attach ctor / strat / special. A `poly` op's per-kind instances share the same
    // attributes — including the special op, whose hooks resolve to the same constants for every kind
    // (this is the re-attach-per-instance Maude does in `instantiatePolymorph`) — so resolve `special`
    // once and apply to each instance.
    // A symbol can be reached by more than one declaration. Two kinds occur: (a) a later decl *upgrades*
    // an earlier one's special — NAT's `_+_` (no `minus`) and INT's `_+_` (with `minus`) share a symbol
    // (Nat/Int are one kind), and the later (INT) must win; (b) an ad-hoc re-import re-adds an *identical*
    // op — a parameter theory `protecting BOOL` and a regular `BOOL` import both contribute
    // `if_then_else_fi`. So `set_special` is last-wins (handling a), and made idempotent for a re-attached
    // `Branch` (handling b — its "no user strat" assert would otherwise trip on the seam's own strat).
    // The canonical META-LEVEL hook set: `metaReduce` carries the full `op-hook` list; every other descent
    // op declares only `op-hook shareWith (metaReduce …)`. Resolve `metaReduce`'s once (order-independent —
    // by spec shape, not declaration position) so all sharers can clone it (see the `MetaLevelOpSymbol` arm).
    let canonical_meta =
        find_canonical_meta_hooks(pm, &sym_by_profile, &sorts, engine.sorts(), interner);
    for (idx, od) in pm.ops.iter().enumerate() {
        if od.attrs.ditto {
            continue; // attributes inherited from the prior declaration (shared symbol)
        }
        let arity = od.domain.len();
        let mut special = match &od.attrs.special {
            Some(spec) => special_op(
                spec,
                arity,
                &name_to_sym,
                &succ_zero,
                &sym_by_profile,
                &sorts,
                engine.sorts(),
                &canonical_meta,
                interner,
            )?,
            None => None,
        };
        // `_.=._`'s decompose needs its own polymorph instance at each argument kind. Pass A expanded
        // the `poly` op eagerly one instance per kind *in kind order*, so `op_syms[idx]` IS the
        // kind-indexed sibling table.
        if let Some(SpecialOp::DecomposeEquality { siblings, .. }) = &mut special {
            let n = engine.sorts().num_kinds();
            *siblings = (0..n).map(|k| op_syms[idx].get(k).copied()).collect();
        }
        // META-TERM's `<Qids> : -> Sort/Kind/Constant/Variable` declarations record the quoted-identifier
        // classification sorts, so a `Qid` constant's least sort becomes text-dependent (a `'NzNat` is a
        // `Sort`, `'0.Zero` a `Constant`, …) — needed for the meta-representation to be well-sorted.
        if let Some(spec) = &od.attrs.special
            && let Some((class, data)) = &spec.id_hook
            && class == "QuotedIdentifierSymbol"
            && let Some(code) = data.first()
        {
            let range = resolve_sort(&engine, &sorts, &od.range)?;
            engine.set_qid_class(code, range);
        }
        // Marker-class builtins (id-hooks that attach no SpecialOp: `s_`, `<Floats>`/`<Strings>`/
        // `<Qids>`, `true`/`false`, the object constructor) are non-`STANDARD` in Maude's SymbolType,
        // which the `.=.` stability analysis must see (a builtin `s X .=. s Y` stays unreduced while a
        // user `[iter]` op decomposes — oracle-verified).
        let marker = matches!(
            od.attrs.special.as_ref().and_then(|s| s.id_hook.as_ref()),
            Some((class, _))
                if matches!(
                    class.as_str(),
                    "SuccSymbol" | "StringSymbol" | "FloatSymbol" | "QuotedIdentifierSymbol"
                        | "SystemTrue" | "SystemFalse" | "ObjectConstructorSymbol"
                )
        );
        for &sym in &op_syms[idx] {
            if marker {
                engine.set_symbol_class(sym, tnk_core::symbol::SymbolClass::Marker);
            }
            if let Some(strat) = &od.attrs.strat {
                engine.set_strategy(sym, strat);
            }
            if let Some(frozen) = &od.attrs.frozen {
                engine.set_frozen(sym, frozen);
            }
            // Object-system role flags (`config`/`obj`/`msg`/`portal`, Pillar 2.5). Mirror Maude's
            // `SymbolType` CONFIG/OBJECT/MESSAGE/PORTAL bits onto the kernel symbol. Inert for the
            // existing rewriting modes; the `erewrite` scheduler (Phase 2.5-B) keys on them.
            if od.attrs.config || od.attrs.object || od.attrs.message || od.attrs.portal {
                engine.set_oo_flags(
                    sym,
                    od.attrs.config,
                    od.attrs.object,
                    od.attrs.message,
                    od.attrs.portal,
                );
            }
            if let Some(op) = &special {
                engine.set_special(sym, op.clone());
                if let SpecialOp::Smt { op } = op {
                    engine.register_smt_operator(sym, *op);
                }
            }
        }
    }

    // Ad-hoc overloading flags for print disambiguation (Maude's `entry.cc`): for each symbol, whether
    // another symbol shares its name (`ADHOC`), its name + domain kinds (`DOMAIN`), or its name + range
    // kind (`RANGE`). Two symbols of the same name are necessarily in different connected components (same
    // components ⇒ one symbol with subsort-overloaded declarations), so this is the cross-kind overloading.
    let overload = compute_overload_flags(&engine, &syntax);

    // Resolve declared variables `(name, sort)` for the grammar builder + `build_term`.
    let mut vars: Vec<(String, SortId)> = Vec::new();
    for vd in &pm.vars {
        let sort = resolve_sort(&engine, &sorts, &vd.sort)?;
        for name in &vd.names {
            vars.push((name.clone(), sort));
        }
    }

    let integer_literal_kind_count = engine.integer_literal_kind_count();
    let overloaded_naturals = ops
        .keys()
        .filter_map(|(name, arity)| {
            if *arity != 0 || name.is_empty() || !name.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let canonical = name.trim_start_matches('0');
            (!canonical.is_empty()).then(|| canonical.to_string())
        })
        .collect();

    Ok(BuiltModule {
        engine,
        name: pm.name.clone(),
        sorts,
        ops,
        syntax,
        vars,
        statements: Vec::new(), // moved in by the caller (B4.4); kept out of `&PreModule`
        eq_traces: Vec::new(),  // populated by load_statements (full-trace metadata)
        mb_traces: Vec::new(),
        rl_traces: Vec::new(),
        oo_completion_diagnostics: Vec::new(),
        nat_succ,
        nat_zero,
        string_sym,
        float_sym,
        qid_sym,
        minus_sym,
        division_sym,
        true_sym,
        false_sym,
        overload,
        integer_literal_kind_count,
        overloaded_naturals,
        strat_defs: pm.strat_defs.clone(),
        identity_specs,
    })
}

/// Compute the per-symbol ad-hoc overloading flags ([`BuiltModule::overload`]) by comparing every pair of
/// symbols that share a (canonical) name: same name ⇒ `ADHOC`; same name and per-position domain kinds ⇒
/// `DOMAIN`; same name and range kind ⇒ `RANGE`. Only symbols that pick up at least one flag are recorded.
fn compute_overload_flags(
    engine: &Engine,
    syntax: &HashMap<SymbolId, SymbolSyntax>,
) -> HashMap<SymbolId, u8> {
    use crate::sig::syntax::{OVL_ADHOC, OVL_DOMAIN, OVL_RANGE};
    // Group symbols by (name, ARITY), recording each one's domain/range *kinds*: a k-argument
    // application can only be confused with other k-argument declarations of the same name, so a
    // different-arity overload (META-LEVEL's 4-arg vs 3-arg metaParse) must not force
    // disambiguation — Maude echoes `metaParse(M, none, Q, T)` with a bare `none`.
    type Profile = (SymbolId, Vec<KindId>, KindId);
    let mut by_name: HashMap<(&str, usize), Vec<Profile>> = HashMap::new();
    for (&sym, syn) in syntax {
        let dom: Vec<KindId> = syn
            .domain
            .iter()
            .map(|&s| engine.sorts().kind_of(s))
            .collect();
        let range = engine.sorts().kind_of(syn.range);
        by_name
            .entry((engine.symbol(sym).name(), dom.len()))
            .or_default()
            .push((sym, dom, range));
    }
    let mut flags: HashMap<SymbolId, u8> = HashMap::new();
    for group in by_name.values() {
        if group.len() < 2 {
            continue; // a unique name needs no disambiguation
        }
        for (sym, dom, range) in group {
            let mut f = OVL_ADHOC; // some other symbol in the group shares the name
            for (other, odom, orange) in group {
                if other == sym {
                    continue;
                }
                if odom == dom {
                    f |= OVL_DOMAIN;
                }
                if orange == range {
                    f |= OVL_RANGE;
                }
            }
            flags.insert(*sym, f);
        }
    }
    flags
}

/// Declare one operator via the kernel constructor for its theory. Identity slots are attached by the
/// caller after every declaration exists; constructors therefore receive no provisional constant.
fn declare_op(
    engine: &mut Engine,
    name: &str,
    attrs: &Attrs,
    domain: &[SortId],
    range: SortId,
) -> SymbolId {
    let symbol = if attrs.iter {
        engine.add_op_iter(name.to_string(), domain.to_vec(), range)
    } else if attrs.assoc && attrs.comm {
        engine.add_op_ac(name.to_string(), domain.to_vec(), range, None)
    } else if attrs.assoc {
        engine.add_op_au(name.to_string(), domain.to_vec(), range, None)
    } else if attrs.comm || attrs.idem || attrs.id.is_some() {
        engine.add_op_cui(
            name.to_string(),
            domain.to_vec(),
            range,
            attrs.comm,
            attrs.idem,
            None,
        )
    } else {
        engine.add_op(name.to_string(), domain.to_vec(), range)
    };
    if attrs.ctor {
        engine.set_ctor(symbol);
    }
    symbol
}

// ---- hook resolution ----

fn op_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, sig) = spec.op_hooks.iter().find(|(p, _)| p == purpose)?;
    // The operator name is the run of tokens before the `:` of `(name : domain ~> range)`. A *mixfix*
    // name can be several tokens — `<_,_,_>` lexes as `<_ , _ , _>` — so join them (canonical form), not
    // just the first (which sufficed for the single-token names `_and_`/`_/_`/`<Strings>`).
    let name: String = sig
        .iter()
        .take_while(|t| i.resolve(t.sym) != ":")
        .map(|t| i.resolve(t.sym))
        .collect();
    name_to_sym.get(&name).copied()
}

fn term_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, term) = spec.term_hooks.iter().find(|(p, _)| p == purpose)?;
    name_to_sym.get(i.resolve(term.first()?.sym)).copied()
}

fn nat_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> R<NatHooks> {
    let succ =
        op_hook_sym(spec, "succSymbol", name_to_sym, i).ok_or("missing op-hook succSymbol")?;
    let zero = succ_zero
        .get(&succ)
        .copied()
        .ok_or("succSymbol has no recorded zeroTerm")?;
    let minus = op_hook_sym(spec, "minusSymbol", name_to_sym, i);
    Ok(NatHooks { succ, zero, minus })
}

fn bool_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<BoolHooks> {
    Some(BoolHooks {
        true_: term_hook_sym(spec, "trueTerm", name_to_sym, i)?,
        false_: term_hook_sym(spec, "falseTerm", name_to_sym, i)?,
    })
}

/// Map a `special` directive to a kernel [`SpecialOp`] (or `None` for the pure NA-constant / successor
/// markers, which carry no reduction rule — their behaviour is the theory / the literal productions).
#[allow(clippy::too_many_arguments)]
fn special_op(
    spec: &SpecialSpec,
    arity: usize,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    canonical_meta: &Option<std::rc::Rc<MetaHooks>>,
    i: &Interner,
) -> R<Option<SpecialOp>> {
    let Some((class, data)) = &spec.id_hook else {
        return Ok(None);
    };
    let code = data.first().map(String::as_str);
    let op = match class.as_str() {
        // Markers (no reduction rule): the constant/successor literals, and the `true`/`false`
        // boolean anchors (`SystemTrue`/`SystemFalse` — Maude's `trueSymbol`/`falseSymbol`). A marker
        // carries no behaviour; `true`/`false` stand for themselves. They are *recorded* (Pass A2) so
        // later passes — bare boolean conditions (`if pred` ⇒ `pred = true`), sort-test predicates —
        // can reference the canonical truth constants.
        "SuccSymbol"
        | "StringSymbol"
        | "FloatSymbol"
        | "QuotedIdentifierSymbol"
        | "SystemTrue"
        | "SystemFalse"
        | "SMT_NumberSymbol" => return Ok(None),
        // `<_:_|_>` (CONFIGURATION's `ObjectConstructorSymbol`, Pillar 2.5). A marker: the object
        // constructor is an ordinary free symbol for reduction/rewriting (its third argument is the
        // ACU `AttributeSet`, matched by the existing engine). The C++ symbol adds object-pattern
        // matching optimizations (via the `attributeSetSymbol` op-hook) that the `erewrite` scheduler
        // will exploit (Phase 2.5-B); for plain rewrite/search nothing special is needed.
        "ObjectConstructorSymbol" => return Ok(None),
        "MinusSymbol" => SpecialOp::Minus {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "DivisionSymbol" => SpecialOp::Division {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "SMT_Symbol" => SpecialOp::Smt {
            op: smt_op(code.ok_or("SMT_Symbol code")?, arity)?,
        },
        // `_==_`/`_=/=_`: structural equality of the two reduced arguments (ground or not — Maude
        // decides `X == Y` as `false` for distinct variables too).
        "EqualitySymbol" => SpecialOp::Equality {
            eq: term_hook_sym(spec, "equalTerm", name_to_sym, i).ok_or("equalTerm")?,
            neq: term_hook_sym(spec, "notEqualTerm", name_to_sym, i).ok_or("notEqualTerm")?,
        },
        // The initial-equality predicate `_.=._`: decides ground/provably-unequal cases and
        // *decomposes* symbolic ones over stable constructors into `_and_`/`_or_` of smaller
        // problems. The per-kind sibling-instance table is filled by Pass B (it needs `op_syms`).
        "CommutativeDecomposeEqualitySymbol" => SpecialOp::DecomposeEquality {
            eq: term_hook_sym(spec, "equalTerm", name_to_sym, i).ok_or("equalTerm")?,
            neq: term_hook_sym(spec, "notEqualTerm", name_to_sym, i).ok_or("notEqualTerm")?,
            conj: op_hook_sym(spec, "conjunctionSymbol", name_to_sym, i),
            disj: op_hook_sym(spec, "disjunctionSymbol", name_to_sym, i),
            siblings: std::rc::Rc::from(Vec::new()),
        },
        "BranchSymbol" => {
            // term-hooks "1", "2", … are the test constants, in order.
            let mut tests = Vec::new();
            for k in 1.. {
                match term_hook_sym(spec, &k.to_string(), name_to_sym, i) {
                    Some(s) => tests.push(s),
                    None => break,
                }
            }
            SpecialOp::Branch { tests }
        }
        "ACU_NumberOpSymbol" => SpecialOp::AcuNumberOp {
            op: num_op(code.ok_or("ACU_NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "CUI_NumberOpSymbol" => SpecialOp::CuiNumberOp {
            op: num_op(code.ok_or("CUI_NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "NumberOpSymbol" => SpecialOp::NumberOp {
            op: num_op(code.ok_or("NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
            bool_: bool_hooks(spec, name_to_sym, i),
        },
        "StringOpSymbol" => match conv_op("StringOpSymbol", code.unwrap_or(""), arity) {
            Some(op) => conversion(op, spec, name_to_sym, succ_zero, i),
            None => SpecialOp::StringOp {
                op: str_op(code.ok_or("StringOpSymbol code")?)?,
                str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i)
                    .ok_or("StringOpSymbol stringSymbol")?,
                nat: nat_hooks(spec, name_to_sym, succ_zero, i).ok(),
                bool_: bool_hooks(spec, name_to_sym, i),
                not_found: term_hook_sym(spec, "notFoundTerm", name_to_sym, i),
            },
        },
        "RandomOpSymbol" => SpecialOp::Random {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "CounterSymbol" => SpecialOp::Counter {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "QuotedIdentifierOpSymbol" => match code.ok_or("QuotedIdentifierOpSymbol code")? {
            // LEXICAL needs the frontend's byte-aware token scanner, so these two quoted-identifier
            // operations use the same upper-layer descent seam as META-LEVEL rather than becoming inert
            // or teaching the kernel about source tokens.
            "tokenize" => SpecialOp::Meta {
                op: MetaOp::Tokenize,
                hooks: std::rc::Rc::new(resolve_meta_hooks(
                    spec,
                    sym_by_profile,
                    sorts,
                    sort_table,
                    i,
                )),
            },
            "printTokens" => SpecialOp::Meta {
                op: MetaOp::PrintTokens,
                hooks: std::rc::Rc::new(resolve_meta_hooks(
                    spec,
                    sym_by_profile,
                    sorts,
                    sort_table,
                    i,
                )),
            },
            code => SpecialOp::QidOp {
                op: match qid_op(code) {
                    Ok(op) => op,
                    Err(_) => return Ok(None),
                },
                qid_sym: op_hook_sym(spec, "quotedIdentifierSymbol", name_to_sym, i)
                    .ok_or("QuotedIdentifierOpSymbol quotedIdentifierSymbol")?,
                str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i)
                    .ok_or("QuotedIdentifierOpSymbol stringSymbol")?,
            },
        },
        "FloatOpSymbol" => match conv_op("FloatOpSymbol", code.unwrap_or(""), arity) {
            Some(op) => conversion(op, spec, name_to_sym, succ_zero, i),
            None => SpecialOp::FloatOp {
                op: flt_op(code.ok_or("FloatOpSymbol code")?, arity)?,
                float_sym: op_hook_sym(spec, "floatSymbol", name_to_sym, i)
                    .ok_or("FloatOpSymbol floatSymbol")?,
                bool_: bool_hooks(spec, name_to_sym, i),
            },
        },
        // META-LEVEL descent functions share metaReduce's representation hooks. A standalone
        // extension may add operation-specific structural hooks; merge those over the canonical
        // table instead of discarding them merely because META-LEVEL is imported.
        "MetaLevelOpSymbol" => {
            let code = code.ok_or("MetaLevelOpSymbol code")?;
            let mut hooks = canonical_meta.as_deref().cloned().unwrap_or_default();
            let own = resolve_meta_hooks(spec, sym_by_profile, sorts, sort_table, i);
            hooks.ops.extend(own.ops);
            hooks.terms.extend(own.terms);
            SpecialOp::Meta {
                op: meta_op(code),
                hooks: std::rc::Rc::new(hooks),
            }
        }
        "ModelCheckerSymbol" => {
            let op_hook = |purpose: &str| -> R<SymbolId> {
                let (_, signature) = spec
                    .op_hooks
                    .iter()
                    .find(|(candidate, _)| candidate == purpose)
                    .ok_or_else(|| format!("ModelCheckerSymbol missing op-hook {purpose}"))?;
                resolve_op_hook_sig(signature, sym_by_profile, sorts, sort_table, i)
                    .ok_or_else(|| format!("ModelCheckerSymbol cannot resolve op-hook {purpose}"))
            };
            SpecialOp::ModelCheck {
                hooks: std::rc::Rc::new(ModelCheckerHooks {
                    temporal: TemporalHooks {
                        true_symbol: op_hook("trueSymbol")?,
                        false_symbol: op_hook("falseSymbol")?,
                        not_symbol: op_hook("notSymbol")?,
                        next_symbol: op_hook("nextSymbol")?,
                        and_symbol: op_hook("andSymbol")?,
                        or_symbol: op_hook("orSymbol")?,
                        until_symbol: op_hook("untilSymbol")?,
                        release_symbol: op_hook("releaseSymbol")?,
                    },
                    satisfies_symbol: op_hook("satisfiesSymbol")?,
                    qid_symbol: op_hook("qidSymbol")?,
                    unlabeled_symbol: op_hook("unlabeledSymbol")?,
                    deadlock_symbol: op_hook("deadlockSymbol")?,
                    transition_symbol: op_hook("transitionSymbol")?,
                    transition_list_symbol: op_hook("transitionListSymbol")?,
                    nil_transition_list_symbol: op_hook("nilTransitionListSymbol")?,
                    counterexample_symbol: op_hook("counterexampleSymbol")?,
                    true_term: term_hook_sym(spec, "trueTerm", name_to_sym, i)
                        .ok_or("ModelCheckerSymbol cannot resolve term-hook trueTerm")?,
                }),
            }
        }
        "SatSolverSymbol" => {
            let op_hook = |purpose: &str| -> R<SymbolId> {
                let (_, signature) = spec
                    .op_hooks
                    .iter()
                    .find(|(candidate, _)| candidate == purpose)
                    .ok_or_else(|| format!("SatSolverSymbol missing op-hook {purpose}"))?;
                resolve_op_hook_sig(signature, sym_by_profile, sorts, sort_table, i)
                    .ok_or_else(|| format!("SatSolverSymbol cannot resolve op-hook {purpose}"))
            };
            SpecialOp::SatSolve {
                hooks: std::rc::Rc::new(SatSolverHooks {
                    temporal: TemporalHooks {
                        true_symbol: op_hook("trueSymbol")?,
                        false_symbol: op_hook("falseSymbol")?,
                        not_symbol: op_hook("notSymbol")?,
                        next_symbol: op_hook("nextSymbol")?,
                        and_symbol: op_hook("andSymbol")?,
                        or_symbol: op_hook("orSymbol")?,
                        until_symbol: op_hook("untilSymbol")?,
                        release_symbol: op_hook("releaseSymbol")?,
                    },
                    formula_list_symbol: op_hook("formulaListSymbol")?,
                    nil_formula_list_symbol: op_hook("nilFormulaListSymbol")?,
                    model_symbol: op_hook("modelSymbol")?,
                    false_term: term_hook_sym(spec, "falseTerm", name_to_sym, i)
                        .ok_or("SatSolverSymbol cannot resolve term-hook falseTerm")?,
                }),
            }
        }
        // `stdin`/`stdout`/`stderr` (CONFIGURATION/STD-STREAM's `StreamManagerSymbol`, Pillar 2.5-C): a
        // standard-stream external-object manager. The id-hook data selects the stream; the op-hooks name
        // the `write`/`wrote` (and `getLine`/`gotLine`) message symbols the manager consumes/produces.
        "StreamManagerSymbol" => SpecialOp::StreamManager {
            stream: match code {
                Some("stdin") => StdStream::Stdin,
                Some("stdout") => StdStream::Stdout,
                Some("stderr") => StdStream::Stderr,
                _ => return Err("StreamManagerSymbol needs a stdin/stdout/stderr id-hook".into()),
            },
            string_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i),
            write_msg: op_hook_sym(spec, "writeMsg", name_to_sym, i),
            wrote_msg: op_hook_sym(spec, "wroteMsg", name_to_sym, i),
            get_line_msg: op_hook_sym(spec, "getLineMsg", name_to_sym, i),
            got_line_msg: op_hook_sym(spec, "gotLineMsg", name_to_sym, i),
        },
        // An id-hook class this port has not implemented (MatrixOpSymbol, LoopSymbol,
        // InterpreterManagerSymbol, …): declare the operator WITHOUT a special binding — the module
        // loads and everything else in it works; the op itself is inert (never reduces). This is the
        // §2 graceful-degrade stance (stock linear.maude's DIOPHANTINE, the prelude's
        // LOOP-MODE/LEXICAL); the advisory text is phase E.
        _other => return Ok(None),
    };
    Ok(Some(op))
}

/// Map Maude's `SMT_Symbol` data attachment to the exact C++ operator enum. The `-` spelling is
/// overloaded and therefore resolved by arity.
fn smt_op(code: &str, arity: usize) -> R<SmtOp> {
    Ok(match (code, arity) {
        ("true", 0) => SmtOp::True,
        ("false", 0) => SmtOp::False,
        ("not", 1) => SmtOp::Not,
        ("and", 2) => SmtOp::And,
        ("or", 2) => SmtOp::Or,
        ("xor", 2) => SmtOp::Xor,
        ("implies", 2) => SmtOp::Implies,
        ("===", 2) => SmtOp::Equals,
        ("=/==", 2) => SmtOp::NotEquals,
        ("ite", 3) => SmtOp::Ite,
        ("-", 1) => SmtOp::UnaryMinus,
        ("-", 2) => SmtOp::Minus,
        ("+", 2) => SmtOp::Plus,
        ("*", 2) => SmtOp::Multiply,
        ("div", 2) => SmtOp::Divide,
        ("mod", 2) => SmtOp::Modulo,
        ("<", 2) => SmtOp::Less,
        ("<=", 2) => SmtOp::LessEqual,
        (">", 2) => SmtOp::Greater,
        (">=", 2) => SmtOp::GreaterEqual,
        ("divisible", 2) => SmtOp::Divisible,
        ("/", 2) => SmtOp::RealDivide,
        ("toReal", 1) => SmtOp::ToReal,
        ("toInteger", 1) => SmtOp::ToInteger,
        ("isInteger", 1) => SmtOp::IsInteger,
        _ => return Err(format!("unsupported SMT operator `{code}`/{arity}")),
    })
}

/// Map a `MetaLevelOpSymbol` code (the descent function name) to its [`MetaOp`]. Reflection, SMT,
/// and symbolic variant/narrowing functions have dedicated variants; strategy descent maps to
/// [`MetaOp::Deferred`] (declared, inert).
fn meta_op(code: &str) -> MetaOp {
    match code {
        "metaReduce" => MetaOp::Reduce,
        "metaNormalize" => MetaOp::Normalize,
        "metaRewrite" => MetaOp::Rewrite,
        "metaFrewrite" => MetaOp::Frewrite,
        "metaApply" => MetaOp::Apply,
        "metaXapply" => MetaOp::Xapply,
        "metaMatch" => MetaOp::Match,
        "metaXmatch" => MetaOp::Xmatch,
        "metaSearch" => MetaOp::Search,
        "metaSearchPath" => MetaOp::SearchPath,
        "metaCheck" => MetaOp::Check,
        "metaSmtSearch" => MetaOp::SmtSearch,
        "variantSat" => MetaOp::VariantSat {
            validity: false,
            explicit_sorts: false,
        },
        "variantSatWithSorts" => MetaOp::VariantSat {
            validity: false,
            explicit_sorts: true,
        },
        "variantValid" => MetaOp::VariantSat {
            validity: true,
            explicit_sorts: false,
        },
        "variantValidWithSorts" => MetaOp::VariantSat {
            validity: true,
            explicit_sorts: true,
        },
        "variantSatWellFormed" => MetaOp::VariantSatWellFormed,
        "metaSortLeq" => MetaOp::SortLeq,
        "metaSameKind" => MetaOp::SameKind,
        "metaLesserSorts" => MetaOp::LesserSorts,
        "metaGlbSorts" => MetaOp::GlbSorts,
        "metaLeastSort" => MetaOp::LeastSort,
        "metaCompleteName" => MetaOp::CompleteName,
        "metaGetKind" => MetaOp::GetKind,
        "metaGetKinds" => MetaOp::GetKinds,
        "metaMaximalSorts" => MetaOp::MaximalSorts,
        "metaMinimalSorts" => MetaOp::MinimalSorts,
        "metaMaximalAritySet" => MetaOp::MaximalAritySet,
        "metaParse" => MetaOp::Parse,
        "metaPrettyPrint" => MetaOp::PrettyPrint,
        "metaPrintToString" => MetaOp::PrintToString,
        "metaWellFormedModule" => MetaOp::WellFormedModule,
        "metaWellFormedTerm" => MetaOp::WellFormedTerm,
        "metaWellFormedSubstitution" => MetaOp::WellFormedSubstitution,
        "metaUpModule" => MetaOp::UpModule,
        "metaUpImports" => MetaOp::UpImports,
        "metaUpSorts" => MetaOp::UpSorts,
        "metaUpSubsortDecls" => MetaOp::UpSubsortDecls,
        "metaUpOpDecls" => MetaOp::UpOpDecls,
        "metaUpMbs" => MetaOp::UpMbs,
        "metaUpEqs" => MetaOp::UpEqs,
        "metaUpRls" => MetaOp::UpRls,
        "metaUpStratDecls" => MetaOp::UpStratDecls,
        "metaUpSds" => MetaOp::UpSds,
        "metaUpView" => MetaOp::UpView,
        "metaUpTerm" => MetaOp::UpTerm,
        "metaDownTerm" => MetaOp::DownTerm,
        // Order-sorted unification descent (S1f). Current signature (variable-family `Qid` 3rd arg) and
        // legacy signature (fresh-variable-count `Nat` 3rd arg) carry distinct id-hook codes.
        "metaUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: false,
            legacy: false,
        },
        "metaDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: false,
            legacy: false,
        },
        "metaIrredundantUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: true,
            legacy: false,
        },
        "metaIrredundantDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: true,
            legacy: false,
        },
        "legacyMetaUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: false,
            legacy: true,
        },
        "legacyMetaDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: false,
            legacy: true,
        },
        // Folding variant descent (S2), current Qid-family and legacy Nat-family signatures.
        "metaGetVariant" => MetaOp::GetVariant {
            irredundant: false,
            legacy: false,
        },
        "metaGetIrredundantVariant" => MetaOp::GetVariant {
            irredundant: true,
            legacy: false,
        },
        "legacyMetaGetVariant" => MetaOp::GetVariant {
            irredundant: false,
            legacy: true,
        },
        "legacyMetaGetIrredundantVariant" => MetaOp::GetVariant {
            irredundant: true,
            legacy: true,
        },
        "metaVariantUnify" => MetaOp::VariantUnify {
            disjoint: false,
            legacy: false,
        },
        "metaVariantDisjointUnify" => MetaOp::VariantUnify {
            disjoint: true,
            legacy: false,
        },
        "legacyMetaVariantUnify" => MetaOp::VariantUnify {
            disjoint: false,
            legacy: true,
        },
        "legacyMetaVariantDisjointUnify" => MetaOp::VariantUnify {
            disjoint: true,
            legacy: true,
        },
        "metaVariantMatch" => MetaOp::VariantMatch,
        "metaNarrow" => MetaOp::Narrow { state_only: false },
        "metaNarrow2" => MetaOp::Narrow { state_only: true },
        "metaNarrowingApply" => MetaOp::NarrowingApply,
        "metaNarrowingSearch" => MetaOp::NarrowingSearch { path: false },
        "metaNarrowingSearchPath" => MetaOp::NarrowingSearch { path: true },
        // Remaining strategy descent is declared but inert.
        _ => MetaOp::Deferred,
    }
}

/// Find and resolve the **canonical** META-LEVEL hook set: the one descent op that carries the full
/// `op-hook` list rather than a `shareWith` reference (it is `metaReduce`). All other descent ops
/// (`metaRewrite`/`metaApply`/…) declare `op-hook shareWith (metaReduce …)` and reuse this set, so the
/// down/up maps see the constructors (`qidSymbol`/`resultPairSymbol`/`assignmentSymbol`/…) regardless of
/// declaration order. `None` if the module declares no such op (a module without `metaReduce`).
fn find_canonical_meta_hooks(
    pm: &PreModule,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> Option<std::rc::Rc<MetaHooks>> {
    pm.ops.iter().find_map(|od| {
        let spec = od.attrs.special.as_ref()?;
        let (class, data) = spec.id_hook.as_ref()?;
        if class == "MetaLevelOpSymbol" && data.first().is_some_and(|code| code == "metaReduce") {
            Some(std::rc::Rc::new(resolve_meta_hooks(
                spec,
                sym_by_profile,
                sorts,
                sort_table,
                i,
            )))
        } else {
            None
        }
    })
}

/// Resolve a descent function's `op-hook`/`term-hook` list into the meta-representation symbols the
/// down/up maps need ([`MetaHooks`]), keyed by hook purpose (`qidSymbol`, `metaTermSymbol`, …). Op-hooks
/// resolve by **signature** (name + domain/range kinds), since names like `_,_` / `__` are ad-hoc
/// overloaded across kinds (a TermList `_,_` vs a RenamingSet `_,_`); a hook whose signature names a sort
/// not in this module is skipped (it is simply unavailable to descent).
fn resolve_meta_hooks(
    spec: &SpecialSpec,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> MetaHooks {
    let mut ops = HashMap::new();
    for (purpose, sig) in &spec.op_hooks {
        if let Some(sym) = resolve_op_hook_sig(sig, sym_by_profile, sorts, sort_table, i) {
            ops.insert(purpose.clone(), sym);
        }
    }
    // The descent functions carry op-hooks only (no term-hooks), so `terms` stays empty.
    MetaHooks {
        ops,
        terms: HashMap::new(),
    }
}

/// Resolve one `op-hook` signature `name : dom… ~> range` to the symbol with that profile (name + the
/// kinds of the domain/range sorts), via [`sym_by_profile`]. Returns `None` if the signature is malformed
/// or names an unknown sort.
fn resolve_op_hook_sig(
    sig: &[crate::lex::Token],
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> Option<SymbolId> {
    let texts: Vec<&str> = sig.iter().map(|t| i.resolve(t.sym)).collect();
    let colon = texts.iter().position(|&t| t == ":")?;
    let arrow = texts.iter().position(|&t| t == "~>" || t == "->")?;
    let name: String = texts[..colon].concat();
    let kind_of_sort = |s: &str| sorts.get(s).map(|&sid| sort_table.kind_of(sid));
    let dom_kinds: Vec<KindId> = texts[colon + 1..arrow]
        .iter()
        .map(|s| kind_of_sort(s))
        .collect::<Option<_>>()?;
    let range = texts.get(arrow + 1)?;
    let range_kind = kind_of_sort(range)?;
    sym_by_profile.get(&(name, dom_kinds, range_kind)).copied()
}

fn num_op(code: &str) -> R<NumOp> {
    Ok(match code {
        "+" => NumOp::Add,
        "*" => NumOp::Mul,
        "gcd" => NumOp::Gcd,
        "lcm" => NumOp::Lcm,
        "min" => NumOp::Min,
        "max" => NumOp::Max,
        "xor" => NumOp::Xor,
        "&" => NumOp::And,
        "|" => NumOp::Or,
        "sd" => NumOp::Sd,
        "-" => NumOp::Sub,
        "quo" => NumOp::Quo,
        "rem" => NumOp::Rem,
        "^" => NumOp::Pow,
        "modExp" => NumOp::ModExp,
        ">>" => NumOp::Shr,
        "<<" => NumOp::Shl,
        "abs" => NumOp::Abs,
        "~" => NumOp::BitNot,
        "<" => NumOp::Lt,
        "<=" => NumOp::Le,
        ">" => NumOp::Gt,
        ">=" => NumOp::Ge,
        "divides" => NumOp::Divides,
        other => return Err(format!("unsupported number op `{other}`")),
    })
}

/// A CONVERSION coercion code, distinguished by id-hook class + code + arity (since `float`/`rat`/
/// `string` are overloaded across argument types — e.g. `string : Rat NzNat` vs `string : Float`).
/// `None` ⇒ not a conversion (an ordinary `FloatOp`/`StringOp` arithmetic/string code).
fn conv_op(class: &str, code: &str, arity: usize) -> Option<ConvOp> {
    Some(match (class, code, arity) {
        ("FloatOpSymbol", "float", 1) => ConvOp::RatToFloat,
        ("FloatOpSymbol", "rat", 1) => ConvOp::FloatToRat,
        ("StringOpSymbol", "string", 2) => ConvOp::RatToString,
        ("StringOpSymbol", "string", 1) => ConvOp::FloatToString,
        ("StringOpSymbol", "rat", 2) => ConvOp::StringToRat,
        ("StringOpSymbol", "float", 1) => ConvOp::StringToFloat,
        ("StringOpSymbol", "decFloat", 2) => ConvOp::DecFloat,
        _ => return None,
    })
}

/// Build a [`SpecialOp::Conversion`], resolving each (optional) hook a conversion might need.
fn conversion(
    op: ConvOp,
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> SpecialOp {
    SpecialOp::Conversion {
        op,
        float_sym: op_hook_sym(spec, "floatSymbol", name_to_sym, i),
        str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i),
        nat: nat_hooks(spec, name_to_sym, succ_zero, i).ok(),
        division: op_hook_sym(spec, "divisionSymbol", name_to_sym, i),
        dec_float: op_hook_sym(spec, "decFloatSymbol", name_to_sym, i),
    }
}

fn qid_op(code: &str) -> R<QidOp> {
    Ok(match code {
        "string" => QidOp::String,
        "qid" => QidOp::Qid,
        other => return Err(format!("unsupported quoted-id op `{other}`")),
    })
}

fn str_op(code: &str) -> R<StrOp> {
    Ok(match code {
        "+" => StrOp::Concat,
        "length" => StrOp::Length,
        "substr" => StrOp::Substr,
        "ascii" => StrOp::Ascii,
        "char" => StrOp::Char,
        "find" => StrOp::Find,
        "rfind" => StrOp::Rfind,
        "upperCase" => StrOp::UpperCase,
        "lowerCase" => StrOp::LowerCase,
        "cntrl" => StrOp::IsClass(CharClass::Control),
        "print" => StrOp::IsClass(CharClass::Printable),
        "space" => StrOp::IsClass(CharClass::Space),
        "blank" => StrOp::IsClass(CharClass::Blank),
        "graph" => StrOp::IsClass(CharClass::Graphic),
        "punct" => StrOp::IsClass(CharClass::Punct),
        "alnum" => StrOp::IsClass(CharClass::Alnum),
        "alpha" => StrOp::IsClass(CharClass::Alpha),
        "isupper" => StrOp::IsClass(CharClass::Upper),
        "islower" => StrOp::IsClass(CharClass::Lower),
        "digit" => StrOp::IsClass(CharClass::Digit),
        "xdigit" => StrOp::IsClass(CharClass::XDigit),
        "startsWith" => StrOp::StartsWith,
        "endsWith" => StrOp::EndsWith,
        "ltrim" => StrOp::TrimStart,
        "rtrim" => StrOp::TrimEnd,
        "trim" => StrOp::Trim,
        "<" => StrOp::Lt,
        "<=" => StrOp::Le,
        ">" => StrOp::Gt,
        ">=" => StrOp::Ge,
        other => return Err(format!("unsupported string op `{other}`")),
    })
}

fn flt_op(code: &str, arity: usize) -> R<FltOp> {
    Ok(match (code, arity) {
        ("-", 1) => FltOp::Neg,
        ("abs", _) => FltOp::Abs,
        ("sqrt", _) => FltOp::Sqrt,
        ("floor", _) => FltOp::Floor,
        ("ceiling", _) => FltOp::Ceiling,
        ("exp", _) => FltOp::Exp,
        ("log", _) => FltOp::Log,
        ("sin", _) => FltOp::Sin,
        ("cos", _) => FltOp::Cos,
        ("tan", _) => FltOp::Tan,
        ("asin", _) => FltOp::Asin,
        ("acos", _) => FltOp::Acos,
        ("atan", 1) => FltOp::Atan,
        ("atan", _) => FltOp::Atan2, // binary `atan(y, x)`
        ("+", _) => FltOp::Add,
        ("-", _) => FltOp::Sub,
        ("*", _) => FltOp::Mul,
        ("/", _) => FltOp::Div,
        ("rem", _) => FltOp::Rem,
        ("^", _) => FltOp::Pow,
        ("min", _) => FltOp::Min,
        ("max", _) => FltOp::Max,
        ("<", _) => FltOp::Lt,
        ("<=", _) => FltOp::Le,
        (">", _) => FltOp::Gt,
        (">=", _) => FltOp::Ge,
        (other, _) => return Err(format!("unsupported float op `{other}`")),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::surface::parser::Parser;
    use tnk_core::variant_sat::{ConstructorAnalysis, EligibilityRejection, SortOverrides};

    fn build(src: &str) -> BuiltModule {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse ok");
        build_module(&s.modules[0], &mut i).expect("build ok")
    }

    /// B4.2 done-when: the parsed signature is the same one the hand-built B3.4 test constructs — proven by
    /// reducing through the attached special ops (no equations needed; arithmetic is built-in).
    #[test]
    fn nat_signature_reduces_via_special_ops() {
        let src = "\
fmod NATB is
  sorts Truth Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  ops tt ff : -> Truth [ctor] .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  op _+_ : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (+) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _+_ : Nat Nat -> Nat [ditto] .
  op gcd : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (gcd) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op gcd : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
endfm
";
        let mut m = build(src);
        let (succ, zero) = (m.nat_succ.unwrap(), m.nat_zero.unwrap());
        let num = |m: &mut BuiltModule, n: u64| {
            let z = m.engine.make_const(zero);
            m.engine.make_iter(succ, n, z)
        };
        // 2 + 3 = 5 (ACU_NumberOp), NzNat, 1 rewrite.
        let plus = m.ops[&("_+_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let sum = m.engine.make_ac(plus, vec![a, b]);
        m.engine.reset_rewrites();
        let r = m.engine.reduce(sum);
        let five = num(&mut m, 5);
        assert!(m.engine.deep_equal(r, five), "2 + 3 = 5");
        assert_eq!(m.engine.sorts().name(m.engine.sort_of(r)), "NzNat");
        assert_eq!(m.engine.rewrites(), 1);

        // gcd(12, 18) = 6.
        let gcd = m.ops[&("gcd".to_string(), 2)];
        let (a, b) = (num(&mut m, 12), num(&mut m, 18));
        let g = m.engine.make_ac(gcd, vec![a, b]);
        let r = m.engine.reduce(g);
        let six = num(&mut m, 6);
        assert!(m.engine.deep_equal(r, six), "gcd(12, 18) = 6");

        // The `_<_` NumberOp produced a Truth result: 2 < 3 = tt.
        let lt = m.ops[&("_<_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let q = m.engine.make_free(lt, vec![a, b]);
        let r = m.engine.reduce(q);
        let tt = m.ops[&("tt".to_string(), 0)];
        let tt_node = m.engine.make_const(tt);
        assert!(m.engine.deep_equal(r, tt_node), "2 < 3 = tt");
    }

    #[test]
    fn constructor_analysis_rejects_mixed_overload_axioms() {
        let mut module = build(
            "\
fmod BAD-CTOR-OVERLOAD is
  sorts A B K .
  subsorts A B < K .
  ops a : -> A [ctor] .
  ops b : -> B [ctor] .
  op _*_ : A A -> A [ctor comm] .
  op _*_ : B B -> B [ctor assoc comm] .
endfm
",
        );
        let rejection = match ConstructorAnalysis::build(
            &mut module.engine,
            &SortOverrides::default(),
            false,
        ) {
            Ok(_) => panic!("mixed constructor axiom profiles must be rejected"),
            Err(rejection) => rejection,
        };
        assert!(matches!(
            rejection,
            EligibilityRejection::InconsistentOverloadedConstructorAxioms { .. }
        ));
    }
}
