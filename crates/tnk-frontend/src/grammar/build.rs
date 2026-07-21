//! `build_grammar`: construct a module's mixfix CF [`Grammar`] from its [`BuiltModule`] — a port of
//! `MixfixModule::makeComponentProductions` + `makeSymbolProductions` (`makeGrammar.cc`).
//!
//! Emission order follows Maude: **component productions** (per kind: sort names, the `TERM` injection,
//! parentheses, flattened assoc lists) and the declared-variable productions first, then **symbol
//! productions** (per operator: constants, prefix/assoc-prefix forms, mixfix forms, the successor
//! numeral). Order is observable (it decides the first parse on ambiguity), so it is preserved.
//!
//! Iter-symbol productions cover both genuine prefix names (`g^n(t)`) and canonical mixfix names
//! (`s_^n(t)`), alongside built-in literal, sort-disambiguation, colon-variable, and structured-sort
//! productions. The redundant ordinary prefix form for a mixfix operator (`_+_(a,b)`) remains outside
//! this builder's current surface.

use super::{ANY, Action, GSym, Grammar, Nt, NtType, PREFIX_GATHER, Production, Terminal};
use crate::lex::{Frag, Interner};
use crate::sig::syntax::BuiltModule;
use tnk_core::sort::{KindId, SortId, Sorts};
use tnk_core::symbol::SymbolId;

/// The grammar terminals of a `.Sort` qualifier, with the leading dot fused to the base token as the lexer
/// produces it: `List{ToN}` → `.List`, `{`, `ToN`, `}`. Splits the dotted name on the structured-sort
/// punctuation (`{ } ,`), each run an interned token.
fn dot_sort_terminals(name: &str, interner: &mut Interner) -> Vec<GSym> {
    let dotted = format!(".{name}");
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in dotted.chars() {
        if matches!(c, '{' | '}' | ',') {
            if !cur.is_empty() {
                out.push(GSym::T(Terminal::Tok(interner.intern(&cur))));
                cur.clear();
            }
            out.push(GSym::T(Terminal::Tok(interner.intern(&c.to_string()))));
        } else {
            cur.push(c);
        }
    }
    if !cur.is_empty() {
        out.push(GSym::T(Terminal::Tok(interner.intern(&cur))));
    }
    out
}

/// Build the per-module mixfix grammar. Interns the punctuation/sort-name tokens it needs (idempotent —
/// they share the module's interner, so a grammar terminal's [`Sym`] equals the lexed input token's).
pub fn build_grammar(m: &BuiltModule, interner: &mut Interner) -> Grammar {
    let mut g = Grammar::default();
    let sorts = m.engine.sorts();

    // Punctuation terminals (interned once; equal to the lexer's tokens for the same text).
    let lp = Terminal::Tok(interner.intern("("));
    let rp = Terminal::Tok(interner.intern(")"));
    let comma = Terminal::Tok(interner.intern(","));

    // The kinds of this module, in member-declaration order (SortId is declaration order); deterministic
    // so the production emission order is reproducible.
    let mut sids: Vec<SortId> = m.sorts.values().copied().collect();
    sids.sort();
    let mut kinds: Vec<KindId> = Vec::new();
    for s in sids {
        let k = sorts.kind_of(s);
        if !kinds.contains(&k) {
            kinds.push(k);
        }
    }

    // ---- component productions (per kind) ----
    for &k in &kinds {
        let term_nt = Nt::Comp(k, NtType::Term);
        let sort_nt = Nt::Comp(k, NtType::Sort);
        let assoc_nt = Nt::Comp(k, NtType::AssocList);

        // Sort-name terminals: `<FooSort> ::= SortName`.
        for &member in &sorts.kind(k).members {
            let name = Terminal::Tok(interner.intern(sorts.name(member)));
            push(&mut g, sort_nt, vec![GSym::T(name)], 0, vec![], Action::Nop);
        }

        // `TERM ::= <FooTerm>` — lift any kind's term to the universal start symbol.
        push(
            &mut g,
            Nt::Term,
            vec![GSym::N(term_nt)],
            0,
            vec![ANY],
            Action::PassThru,
        );

        // Parentheses: `<FooTerm> ::= ( <FooTerm> )`.
        push(
            &mut g,
            term_nt,
            vec![GSym::T(lp), GSym::N(term_nt), GSym::T(rp)],
            0,
            vec![ANY],
            Action::PassThru,
        );

        // Sort disambiguation: `<FooTerm> ::= ( <FooTerm> ) .Sort` for each sort of this kind (Maude's
        // `(t).Sort` syntax — the inverse of the printer's `(t).Sort` disambiguation of an ad-hoc-overloaded
        // term). The `.Sort` qualifier selects this kind, so an overloaded constant like `nil` (one per
        // kind) round-trips. The qualifier lexes with the leading dot fused to the base token
        // (`.List{ToN}` → `.List { ToN }`); the inner term passes through unchanged.
        for &member in &sorts.kind(k).members {
            let mut rhs = vec![GSym::T(lp), GSym::N(term_nt), GSym::T(rp)];
            rhs.extend(dot_sort_terminals(sorts.name(member), interner));
            push(&mut g, term_nt, rhs, 0, vec![ANY], Action::PassThru);
        }

        // Flattened assoc arg lists: `<FooAssocList> ::= <FooTerm> , <FooTerm>`
        //                           `<FooAssocList> ::= <FooAssocList> , <FooTerm>`.
        push(
            &mut g,
            assoc_nt,
            vec![GSym::N(term_nt), GSym::T(comma), GSym::N(term_nt)],
            PREFIX_GATHER,
            vec![PREFIX_GATHER, PREFIX_GATHER],
            Action::AssocList,
        );
        push(
            &mut g,
            assoc_nt,
            vec![GSym::N(assoc_nt), GSym::T(comma), GSym::N(term_nt)],
            PREFIX_GATHER,
            vec![PREFIX_GATHER, PREFIX_GATHER],
            Action::AssocList,
        );
    }

    // Declared-variable productions: `<FooTerm> ::= varName` (from the module's `var`/`vars`).
    for (name, sort) in &m.vars {
        let nt = Nt::Comp(sorts.kind_of(*sort), NtType::Term);
        let tok = Terminal::Tok(interner.intern(name));
        push(
            &mut g,
            nt,
            vec![GSym::T(tok)],
            0,
            vec![],
            Action::MakeVariable(*sort),
        );
    }

    // On-the-fly variable productions: `<FooTerm> ::= name:Foo` for every sort (Maude's colon-variable
    // syntax) — a `name:sort` token of that sort, the whole token becoming the variable name. Iterated in
    // SortId order for a reproducible grammar.
    let mut sort_names: Vec<(&String, SortId)> = m.sorts.iter().map(|(n, &s)| (n, s)).collect();
    sort_names.sort_by_key(|&(_, s)| s);
    for (sort_name, sort_id) in sort_names {
        let nt = Nt::Comp(sorts.kind_of(sort_id), NtType::Term);
        let name_sym = interner.intern(sort_name);
        push(
            &mut g,
            nt,
            vec![GSym::T(Terminal::ColonVar(name_sym))],
            0,
            vec![],
            Action::MakeVariable(sort_id),
        );
        // The **kind** colon-variable `name:[S]` — an error-sort (kind-level) on-the-fly variable
        // (`var B : [Bool]` flattens to `B:[Bool]`; also a user-typed `X:[Foo]`). `[S]` resolves to S's
        // component's error sort, into that component's term NT. Any sort of a multi-sort kind spells the
        // same kind (`[Zero]` = `[Nat]`); the distinct tokens each get a production to the one error sort.
        let err = sorts.error_sort(sorts.kind_of(sort_id));
        let kind_sym = interner.intern(&format!("[{sort_name}]"));
        push(
            &mut g,
            nt,
            vec![GSym::T(Terminal::ColonVar(kind_sym))],
            0,
            vec![],
            Action::MakeVariable(err),
        );
    }

    // ---- symbol productions (per operator, in declaration order) ----
    let mut syms: Vec<SymbolId> = m.syntax.keys().copied().collect();
    syms.sort();
    for sym in syms {
        symbol_productions(&mut g, m, sorts, sym, (lp, rp, comma), interner);
    }

    g
}

/// The canonical glued name of a mixfix operator — its fragments concatenated, holes written `_`
/// (`[Tok(s), Hole]` → `s_`). Matches Maude's `Token::name` for the symbol; used to key the `iter`-token
/// terminal against the base name of an `f^count` input token.
fn glued_name(frags: &[Frag], interner: &Interner) -> String {
    let mut s = String::new();
    for f in frags {
        match f {
            Frag::Tok(t) => s.push_str(interner.resolve(*t)),
            Frag::Hole => s.push('_'),
        }
    }
    s
}

/// Productions for one operator (`makeSymbolProductions` body). All tokens it needs are either
/// pre-interned operator-name fragments or the punctuation passed in `(lp, rp, comma)`.
fn symbol_productions(
    g: &mut Grammar,
    m: &BuiltModule,
    sorts: &Sorts,
    sym: SymbolId,
    (lp, rp, comma): (Terminal, Terminal, Terminal),
    interner: &mut Interner,
) {
    let syn = &m.syntax[&sym];
    let nr_args = syn.domain.len();
    let range_nt = Nt::Comp(sorts.kind_of(syn.range), NtType::Term);
    let arg_nt = |k: usize| GSym::N(Nt::Comp(sorts.kind_of(syn.domain[k]), NtType::Term));
    let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));

    if has_hole {
        // Mixfix form: `<rangeTerm> ::= <items with _ → arg nonterminals>`.
        let pg = super::prec_gather::compute(
            &syn.frags,
            nr_args,
            syn.prec,
            syn.gather.as_deref(),
            syn.assoc,
        );
        let mut rhs = Vec::with_capacity(syn.frags.len());
        let mut k = 0;
        for f in &syn.frags {
            match f {
                Frag::Tok(s) => rhs.push(GSym::T(Terminal::Tok(*s))),
                Frag::Hole => {
                    rhs.push(arg_nt(k));
                    k += 1;
                }
            }
        }
        push(g, range_nt, rhs, pg.prec, pg.gather, Action::MakeTerm(sym));

        // A successor symbol additionally accepts a decimal numeral: `<rangeTerm> ::= SMALL_NAT`.
        if m.nat_succ == Some(sym) {
            push(
                g,
                range_nt,
                vec![GSym::T(Terminal::SmallNat)],
                0,
                vec![],
                Action::MakeNatural(sym),
            );
        }
        // A minus symbol additionally accepts a negative numeral: `<rangeTerm> ::= SMALL_NEG` (Maude's
        // `MAKE_INTEGER`). `-7` is one `SMALL_NEG` token; `- 7` and `5 - 7` keep `-` as the `-_`/`_-_`
        // operator token, so prefix negation and binary subtraction are unaffected.
        if m.minus_sym == Some(sym) {
            push(
                g,
                range_nt,
                vec![GSym::T(Terminal::SmallNeg)],
                0,
                vec![],
                Action::MakeInteger(sym),
            );
        }
        // A division symbol additionally accepts a glued rational literal: `<rangeTerm> ::= RATIONAL`
        // (Maude's `MAKE_RATIONAL` → `DivisionSymbol::makeRatTerm`). A negative numerator needs the
        // `MinusSymbol`; RAT always imports it (INT), but guard so the production is well-formed.
        if m.division_sym == Some(sym) {
            if let Some(minus) = m.minus_sym {
                push(
                    g,
                    range_nt,
                    vec![GSym::T(Terminal::Rational)],
                    0,
                    vec![],
                    Action::MakeRational {
                        division: sym,
                        minus,
                    },
                );
            }
        }
        // An `iter` symbol additionally accepts the `f^count(t)` iter-token form: `<rangeTerm> ::=
        // ITER_SYMBOL ( <argTerm> )` (Maude's `MAKE_ITER`). The `iter` axiom forces arity 1.
        if syn.iter && nr_args == 1 {
            let name_str = glued_name(&syn.frags, interner);
            let name = interner.intern(&name_str);
            push(
                g,
                range_nt,
                vec![
                    GSym::T(Terminal::IterSymbol(name)),
                    GSym::T(lp),
                    arg_nt(0),
                    GSym::T(rp),
                ],
                0,
                vec![PREFIX_GATHER],
                Action::MakeIter(sym),
            );
        }
        // (Deferred B4.5: the `s_(t)` prefix form.)
        return;
    }

    // No underscore: a constant (arity 0) or a genuine prefix operator. The name is the full fragment
    // sequence — usually one token (`gcd`, `0`, `tt`), but several when it lexes with punctuation
    // (`[]`, `{}` → `[ ]` / `{ }`, the empty-collection constants).
    let name_toks: Vec<GSym> = syn
        .frags
        .iter()
        .map(|f| match f {
            Frag::Tok(s) => GSym::T(Terminal::Tok(*s)),
            Frag::Hole => unreachable!("a hole-less operator has no holes"),
        })
        .collect();
    if nr_args == 0 {
        // A single-token constant may be a built-in literal terminal (the string/qid/float pseudo-ctor).
        if let Some((term, action)) = (name_toks.len() == 1)
            .then(|| literal_terminal_for(m, sym))
            .flatten()
        {
            push(g, range_nt, vec![GSym::T(term)], 0, vec![], action);
        } else {
            push(g, range_nt, name_toks, 0, vec![], Action::MakeTerm(sym));
        }
        return;
    }

    // Prefix operator. An associative operator takes its arguments as a flattened assoc list.
    if syn.assoc {
        let assoc_nt = Nt::Comp(sorts.kind_of(syn.domain[0]), NtType::AssocList);
        let mut rhs = name_toks;
        rhs.extend([GSym::T(lp), GSym::N(assoc_nt), GSym::T(rp)]);
        push(
            g,
            range_nt,
            rhs,
            0,
            vec![PREFIX_GATHER],
            Action::MakeTerm(sym),
        );
    } else {
        let mut rhs = name_toks;
        rhs.push(GSym::T(lp));
        let mut gather = Vec::with_capacity(nr_args);
        for j in 0..nr_args {
            gather.push(PREFIX_GATHER);
            rhs.push(arg_nt(j));
            rhs.push(GSym::T(if j + 1 == nr_args { rp } else { comma }));
        }
        push(g, range_nt, rhs, 0, gather, Action::MakeTerm(sym));
    }
    // A genuine prefix `iter` operator additionally accepts its compact token form:
    // `<rangeTerm> ::= f^count ( <argTerm> )`.  Mixfix iter operators get the same production in the
    // branch above; keeping this beside the ordinary `f(arg)` production preserves that spelling.
    if syn.iter && nr_args == 1 {
        let name_str = glued_name(&syn.frags, interner);
        let name = interner.intern(&name_str);
        push(
            g,
            range_nt,
            vec![
                GSym::T(Terminal::IterSymbol(name)),
                GSym::T(lp),
                arg_nt(0),
                GSym::T(rp),
            ],
            0,
            vec![PREFIX_GATHER],
            Action::MakeIter(sym),
        );
    }
}

/// The built-in literal terminal + action for a nullary string/qid/float symbol, if `sym` is one.
fn literal_terminal_for(m: &BuiltModule, sym: SymbolId) -> Option<(Terminal, Action)> {
    if m.string_sym == Some(sym) {
        Some((Terminal::Str, Action::MakeString(sym)))
    } else if m.qid_sym == Some(sym) {
        Some((Terminal::Qid, Action::MakeQid(sym)))
    } else if m.float_sym == Some(sym) {
        Some((Terminal::Float, Action::MakeFloat(sym)))
    } else {
        None
    }
}

/// `Grammar::push`, but free-function so this module can call it (the method is private to keep callers
/// honest about the gather invariant).
fn push(g: &mut Grammar, lhs: Nt, rhs: Vec<GSym>, prec: u32, gather: Vec<u32>, action: Action) {
    debug_assert_eq!(
        gather.len(),
        rhs.iter().filter(|s| s.is_nonterminal()).count(),
        "gather must have one bound per nonterminal: lhs={lhs:?} rhs={rhs:?}"
    );
    g.productions.push(Production {
        lhs,
        rhs,
        prec,
        gather,
        action,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::sig::build_sig::build_module;
    use crate::surface::parser::Parser;

    const NATB: &str = "\
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
  var X : Nat .
endfm
";

    fn build(src: &str) -> (BuiltModule, Interner, Grammar) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse ok");
        let m = build_module(&s.modules[0], &mut i).expect("build ok");
        let g = build_grammar(&m, &mut i);
        (m, i, g)
    }

    /// All productions whose action targets `sym`.
    fn prods_for(g: &Grammar, sym: SymbolId) -> Vec<&Production> {
        g.productions
            .iter()
            .filter(|p| {
                matches!(p.action,
                    Action::MakeTerm(s) | Action::MakeNatural(s) | Action::MakeInteger(s)
                    | Action::MakeIter(s) | Action::MakeFloat(s) | Action::MakeString(s)
                    | Action::MakeQid(s) if s == sym)
            })
            .collect()
    }

    #[test]
    fn plus_is_right_associating_infix() {
        let (m, _i, g) = build(NATB);
        let plus = m.ops[&("_+_".to_string(), 2)];
        let ps = prods_for(&g, plus);
        // Exactly the mixfix form (assoc-prefix and `_+_(a,b)` are deferred): prec 41, gather [40,41].
        let mix = ps
            .iter()
            .find(|p| p.prec == 41)
            .expect("mixfix _+_ production");
        assert_eq!(mix.gather, vec![40, 41], "right-associating gather (e E)");
        assert_eq!(mix.rhs.len(), 3, "<term> + <term>");
        assert!(mix.rhs[0].is_nonterminal() && mix.rhs[2].is_nonterminal());
    }

    #[test]
    fn less_than_is_plain_infix() {
        let (m, _i, g) = build(NATB);
        let lt = m.ops[&("_<_".to_string(), 2)];
        let p = prods_for(&g, lt);
        assert_eq!(p.len(), 1);
        assert_eq!(p[0].prec, 41);
        assert_eq!(
            p[0].gather,
            vec![41, 41],
            "non-assoc infix: both holes at prec"
        );
    }

    #[test]
    fn succ_has_mixfix_and_numeral_forms() {
        let (m, _i, g) = build(NATB);
        let succ = m.nat_succ.unwrap();
        let ps = prods_for(&g, succ);
        let mixfix = ps
            .iter()
            .find(|p| matches!(p.action, Action::MakeTerm(_)))
            .expect("s _ mixfix");
        assert_eq!(mixfix.prec, 15, "UNARY_PREC");
        assert_eq!(mixfix.gather, vec![15]);
        let numeral = ps
            .iter()
            .find(|p| matches!(p.action, Action::MakeNatural(_)));
        assert!(
            numeral.is_some(),
            "successor symbol accepts a decimal numeral via SMALL_NAT"
        );
        assert_eq!(numeral.unwrap().rhs, vec![GSym::T(Terminal::SmallNat)]);
    }

    #[test]
    fn gcd_uses_assoc_list_prefix_form() {
        let (m, _i, g) = build(NATB);
        let gcd = m.ops[&("gcd".to_string(), 2)];
        let p = prods_for(&g, gcd);
        assert_eq!(p.len(), 1, "the flattened assoc-list prefix form");
        // rhs = gcd ( <assocList> )
        assert_eq!(p[0].gather, vec![PREFIX_GATHER]);
        assert!(
            p[0].rhs
                .iter()
                .any(|s| matches!(s, GSym::N(Nt::Comp(_, NtType::AssocList))))
        );
    }

    #[test]
    fn constant_zero_is_a_single_token_production() {
        let (m, _i, g) = build(NATB);
        let zero = m.ops[&("0".to_string(), 0)];
        let p = prods_for(&g, zero);
        assert_eq!(p.len(), 1);
        assert!(p[0].rhs.len() == 1 && matches!(p[0].rhs[0], GSym::T(Terminal::Tok(_))));
        assert!(p[0].gather.is_empty());
    }

    #[test]
    fn has_term_injection_parens_and_assoc_lists_per_kind() {
        let (_m, _i, g) = build(NATB);
        // Two kinds (Truth; Nat-family). Each gets a `TERM ::= <kind>Term`, a parens production, and
        // two assoc-list productions.
        let term_injections = g
            .productions
            .iter()
            .filter(|p| p.lhs == Nt::Term && p.action == Action::PassThru)
            .count();
        assert_eq!(term_injections, 2, "one TERM injection per kind");
        let assoc_lists = g
            .productions
            .iter()
            .filter(|p| matches!(p.lhs, Nt::Comp(_, NtType::AssocList)))
            .count();
        assert_eq!(assoc_lists, 4, "two assoc-list productions per kind");
    }

    #[test]
    fn variable_x_produces_a_nat_term() {
        let (m, _i, g) = build(NATB);
        let x_prod = g
            .productions
            .iter()
            .find(|p| matches!(p.action, Action::MakeVariable(_)))
            .expect("a variable production for X");
        // X : Nat → produces into the Nat kind's term nonterminal.
        let nat = m.sorts["Nat"];
        assert_eq!(
            x_prod.lhs,
            Nt::Comp(m.engine.sorts().kind_of(nat), NtType::Term)
        );
    }
}
