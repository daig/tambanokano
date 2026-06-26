//! The Earley recognizer (Maude's `pass1`, DRP bypassed): build the item sets for a token stream and
//! report whether it parses to the start nonterminal. The chart it produces is walked by the forest
//! extractor (B4.4b) to build terms.

use super::compile::CompiledGrammar;
use crate::grammar::{GSym, Nt, Terminal};
use crate::lex::{Interner, TokKind, Token};
use std::collections::HashSet;

/// An Earley item: a production, the dot position within its rhs, and the token index where the item
/// started (its origin). `(prod, dot, origin)` is the full identity for chart dedup.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Item {
    pub prod: u32,
    pub dot: u16,
    pub origin: u32,
}

/// The Earley chart: one item set per token position `0..=n` (`sets[j]` = items recognized just before
/// token `j`; `sets[n]` is the final set). `present[j]` is the same content as a set, for O(1) membership
/// (the forest extractor's prefix check, B4.4b). Retained for forest extraction.
#[derive(Debug)]
pub struct Chart {
    pub sets: Vec<Vec<Item>>,
    present: Vec<HashSet<Item>>,
}

impl Chart {
    /// Whether `item` is in set `pos` (the forest extractor's prefix check).
    pub fn contains(&self, pos: usize, item: Item) -> bool {
        self.present[pos].contains(&item)
    }

    /// Whether the input parsed to `start`: some production of `start` completed spanning the whole input
    /// (origin 0, dot at end, in the final set).
    pub fn recognized(&self, g: &CompiledGrammar, start: Nt) -> bool {
        self.root_items(g, start).next().is_some()
    }

    /// The completed top-level items for `start` (origin 0, fully matched) in the final set — the roots of
    /// the parse forest. More than one ⇒ ambiguous (B4.4b).
    pub fn root_items<'a>(
        &'a self,
        g: &'a CompiledGrammar,
        start: Nt,
    ) -> impl Iterator<Item = Item> + 'a {
        let last = self.sets.len() - 1;
        self.sets[last].iter().copied().filter(move |it| {
            let p = &g.prods[it.prod as usize];
            p.lhs == start && it.dot as usize == p.rhs.len() && it.origin == 0
        })
    }
}

/// Does grammar terminal `t` match input token `tok`? A specific token matches by interned `Sym`; a
/// built-in class matches by lexical kind. `SMALL_NAT` excludes the value-zero numeral (`0`, `00`):
/// Maude splits `ZERO` from `SMALL_NAT`, and a successor symbol's numeral production accepts only
/// positives — `0` is solely the declared zero constant, so excluding it here avoids a spurious parse.
fn terminal_matches(t: Terminal, tok: &Token, i: &Interner) -> bool {
    match t {
        Terminal::Tok(s) => tok.sym == s,
        Terminal::SmallNat => {
            tok.kind == TokKind::Number && i.resolve(tok.sym).bytes().any(|b| b != b'0')
        }
        Terminal::Float => tok.kind == TokKind::Float,
        Terminal::SmallNeg => tok.kind == TokKind::NegNumber,
        Terminal::Str => tok.kind == TokKind::Str,
        Terminal::Qid => tok.kind == TokKind::Qid,
        // `name:sort` on-the-fly variable: an identifier whose part after the last `:` is this sort's
        // name, with a non-empty name before it. (`X:Nat` is one token; the spaced `X : Nat` is three.)
        Terminal::ColonVar(sort_name) => {
            tok.kind == TokKind::Ident
                && matches!(
                    i.resolve(tok.sym).rsplit_once(':'),
                    Some((name, sort)) if !name.is_empty() && sort == i.resolve(sort_name)
                )
        }
    }
}

/// Run the Earley recognizer over `tokens`, seeding the start nonterminal `start`. Returns the chart;
/// call [`Chart::recognized`] / [`Chart::root_items`] to interpret it. `i` resolves token text for the
/// built-in lexical-class terminals (`SMALL_NAT`).
pub fn parse(g: &CompiledGrammar, tokens: &[Token], start: Nt, i: &Interner) -> Chart {
    let n = tokens.len();
    let mut sets: Vec<Vec<Item>> = vec![Vec::new(); n + 1];
    let mut seen: Vec<HashSet<Item>> = vec![HashSet::new(); n + 1];

    // Seed: predict every production of the start nonterminal at position 0.
    for &p in g.productions_for(start) {
        add(&mut sets, &mut seen, 0, Item { prod: p, dot: 0, origin: 0 });
    }

    for j in 0..=n {
        // Work-list over set j; predict/complete append to set j (picked up here), scan appends to j+1.
        let mut idx = 0;
        while idx < sets[j].len() {
            let item = sets[j][idx];
            idx += 1;
            let prod = &g.prods[item.prod as usize];
            let dot = item.dot as usize;
            if dot == prod.rhs.len() {
                complete(g, &mut sets, &mut seen, j, item);
            } else {
                match prod.rhs[dot] {
                    GSym::N(nt) => {
                        // Predict: add every production of `nt`, starting here.
                        for &p in g.productions_for(nt) {
                            add(&mut sets, &mut seen, j, Item { prod: p, dot: 0, origin: j as u32 });
                        }
                    }
                    GSym::T(t) => {
                        // Scan: consume token j if it matches, advancing into set j+1.
                        if j < n && terminal_matches(t, &tokens[j], i) {
                            add(
                                &mut sets,
                                &mut seen,
                                j + 1,
                                Item { prod: item.prod, dot: item.dot + 1, origin: item.origin },
                            );
                        }
                    }
                }
            }
        }
    }

    Chart { sets, present: seen }
}

/// Completer: a finished production of nonterminal `N` (`item`, spanning `[item.origin, j)`) advances
/// every waiting item in `sets[item.origin]` whose dot sits before `N` and whose gather bound for that
/// hole is `>= N`'s precedence (Maude's `pass1.cc:164` gate).
fn complete(
    g: &CompiledGrammar,
    sets: &mut [Vec<Item>],
    seen: &mut [HashSet<Item>],
    j: usize,
    item: Item,
) {
    let finished = &g.prods[item.prod as usize];
    let (n, prec) = (finished.lhs, finished.prec);
    // No epsilon productions, so a completed item spans ≥1 token ⇒ origin < j ⇒ sets[origin] ≠ sets[j];
    // collect first to release the shared borrow before pushing.
    let origin = item.origin as usize;
    let advanced: Vec<Item> = sets[origin]
        .iter()
        .filter_map(|&it2| {
            let p2 = &g.prods[it2.prod as usize];
            let d2 = it2.dot as usize;
            match p2.rhs.get(d2) {
                Some(GSym::N(nt)) if *nt == n && p2.bound[d2].unwrap() >= prec => {
                    Some(Item { prod: it2.prod, dot: it2.dot + 1, origin: it2.origin })
                }
                _ => None,
            }
        })
        .collect();
    for a in advanced {
        add(sets, seen, j, a);
    }
}

/// Add `item` to set `pos` if not already present (chart dedup keeps the work-list finite).
fn add(sets: &mut [Vec<Item>], seen: &mut [HashSet<Item>], pos: usize, item: Item) {
    if seen[pos].insert(item) {
        sets[pos].push(item);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::build::build_grammar;
    use crate::lex::{tokenize, Interner};
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

    /// Build NATB, returning a recognizer closure `accepts(term_text) -> bool` over the shared interner.
    /// `FnMut` because lexing a term may intern fresh numerals; operator/punctuation tokens keep the ids
    /// they were interned with at grammar-build time, so the grammar's `Terminal::Tok`s still match.
    fn natb_recognizer() -> impl FnMut(&str) -> bool {
        let mut i = Interner::new();
        let toks = tokenize(NATB, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let m = build_module(&s.modules[0], &mut i).expect("build");
        let g = CompiledGrammar::compile(&build_grammar(&m, &mut i));
        move |term: &str| {
            let tokens = tokenize(term, &mut i);
            parse(&g, &tokens, Nt::Term, &i).recognized(&g, Nt::Term)
        }
    }

    #[test]
    fn accepts_well_formed_terms() {
        let mut ok = natb_recognizer();
        assert!(ok("0"), "constant");
        assert!(ok("s s 0"), "repeated unary mixfix");
        assert!(ok("2 + 3"), "infix with numerals");
        assert!(ok("2 + 3 + 4"), "right-associated infix chain");
        assert!(ok("gcd ( 12 , 18 )"), "assoc-list prefix form");
        assert!(ok("( s s 0 ) + 0"), "parenthesised subterm");
        assert!(ok("2 < 3"), "cross-kind relational");
        assert!(ok("s X"), "declared variable under a mixfix op");
    }

    #[test]
    fn rejects_malformed_terms() {
        let mut ok = natb_recognizer();
        assert!(!ok("2 +"), "missing right operand");
        assert!(!ok("+ 3"), "missing left operand");
        assert!(!ok("s s"), "successor with no base");
        assert!(!ok("gcd ( 12 )"), "assoc list needs ≥ 2 elements");
        assert!(!ok("( 2 + 3"), "unbalanced paren");
        assert!(!ok(""), "empty input");
    }
}
