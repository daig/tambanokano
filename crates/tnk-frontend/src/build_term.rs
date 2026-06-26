//! `build_term`: walk a parse [`PTree`] into a kernel [`Term`], and the end-to-end glue that takes a
//! command/term token bubble through lex-built grammar → Earley parse → forest → term → reduce.
//!
//! A port of the functional subset of Maude's `MixfixParser::makeTerm` (`mixfixParser.cc`): each
//! production carries an [`Action`] resolved at grammar-build time, and the tree-walk dispatches on it —
//! `MakeTerm` builds `symbol(args…)` from the nonterminal children (flattening a single assoc-list child,
//! Maude's `makeAssocList`); `MakeVariable` resolves a token to a statement-local variable index;
//! `MakeNatural` expands a decimal into a successor chain; `PassThru` forwards its one child. The kernel
//! then folds the uniform `Term` into the right theory node at `instantiate` time (`rebuild`).

use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::grammar::Action;
use crate::lex::{Interner, Token};
use crate::sig::syntax::BuiltModule;
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::Term;

/// Assigns each distinct variable *name* a statement-local index (Maude's `Term`s index variables, not
/// name them). Shared across a statement's lhs/rhs/condition so the same name maps to the same index.
#[derive(Debug, Default)]
pub struct VarIndex {
    entries: Vec<(String, SortId)>,
}

impl VarIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// The index for `name` (declared at `sort`), assigning a fresh one in first-seen order.
    pub fn index_of(&mut self, name: &str, sort: SortId) -> u32 {
        if let Some(p) = self.entries.iter().position(|(n, _)| n == name) {
            return p as u32;
        }
        self.entries.push((name.to_string(), sort));
        (self.entries.len() - 1) as u32
    }

    /// The number of distinct variables seen (a statement's `nr_vars`).
    pub fn count(&self) -> u32 {
        self.entries.len() as u32
    }

    /// The source name of the variable at `index` (for rendering a `match` solution's `X --> …` lines).
    pub fn name(&self, index: u32) -> &str {
        &self.entries[index as usize].0
    }

    /// The declared sort of the variable at `index` — for a `search` solution's `X:Sort --> …` lines,
    /// which (unlike `match`) annotate the variable with its sort.
    pub fn sort(&self, index: u32) -> SortId {
        self.entries[index as usize].1
    }
}

/// Build a kernel [`Term`] from a parse tree. `vars` accumulates the statement-local variable indices
/// (pass a fresh one for a ground command term).
pub fn build_term(
    tree: &PTree,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    match g.prods[tree.prod as usize].action {
        Action::PassThru => {
            let child = tree.nt_children.first().ok_or("PassThru without a child")?;
            build_term(child, g, m, tokens, i, vars)
        }
        Action::MakeTerm(sym) => {
            let args = make_args(tree, sym, g, m, tokens, i, vars)?;
            Ok(Term::op(sym, args))
        }
        Action::MakeVariable(sort) => {
            let name = tokens[tree.start].text(i);
            Ok(Term::var(vars.index_of(name, sort), sort))
        }
        Action::MakeNatural(succ) => {
            let text = tokens[tree.start].text(i);
            let n: u64 = text.parse().map_err(|_| format!("bad numeral `{text}`"))?;
            let zero = m.nat_zero.ok_or("MAKE_NATURAL without a zero symbol")?;
            Ok(numeral_term(succ, zero, n))
        }
        Action::MakeInteger(minus) => {
            let text = tokens[tree.start].text(i);
            let n: u64 = neg_magnitude(text)?;
            let succ = m.nat_succ.ok_or("MAKE_INTEGER without a successor symbol")?;
            let zero = m.nat_zero.ok_or("MAKE_INTEGER without a zero symbol")?;
            Ok(Term::op(minus, vec![numeral_term(succ, zero, n)]))
        }
        Action::AssocList => Err("assoc-list node reached build_term directly".to_string()),
        Action::Nop => Err("sort production has no term".to_string()),
        // String/qid/float literals (B4.5) and the f^n iter-token form (deferred) — not on the milestone.
        other => Err(format!("unsupported action {other:?} (B4.5)")),
    }
}

/// The argument terms for a `MakeTerm`: the nonterminal children, except that a single associative-list
/// child is flattened to the operator's full argument sequence (Maude's `makeAssocList`).
fn make_args(
    tree: &PTree,
    _sym: SymbolId,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Vec<Term>, String> {
    if tree.nt_children.len() == 1 && is_assoc_list(g, &tree.nt_children[0]) {
        flatten_assoc(&tree.nt_children[0], g, m, tokens, i, vars)
    } else {
        tree.nt_children.iter().map(|c| build_term(c, g, m, tokens, i, vars)).collect()
    }
}

/// Flatten a left-recursive assoc-list subtree into its element terms, left-to-right (Maude's
/// `makeAssocList`: collect right children walking left, then the leftmost, then reverse).
fn flatten_assoc(
    node: &PTree,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Vec<Term>, String> {
    let mut rev = Vec::new();
    let mut cur = node;
    loop {
        // An assoc-list production is binary: `<list> ::= <left> , <right>`.
        rev.push(build_term(&cur.nt_children[1], g, m, tokens, i, vars)?);
        let left = &cur.nt_children[0];
        if is_assoc_list(g, left) {
            cur = left;
        } else {
            rev.push(build_term(left, g, m, tokens, i, vars)?);
            break;
        }
    }
    rev.reverse();
    Ok(rev)
}

fn is_assoc_list(g: &CompiledGrammar, t: &PTree) -> bool {
    matches!(g.prods[t.prod as usize].action, Action::AssocList)
}

/// `s^n(zero)` as a successor-chain term; the kernel folds it into one compact `s^n(0)` iter node at
/// `instantiate` time. Adequate for milestone-sized numerals; a direct bignum iter node is the fast path
/// for large literals (B4.5).
fn numeral_term(succ: SymbolId, zero: SymbolId, n: u64) -> Term {
    let mut t = Term::constant(zero);
    for _ in 0..n {
        t = Term::op(succ, vec![t]);
    }
    t
}

/// The magnitude of a `SMALL_NEG` token `-N` (Maude builds `-(s^N(0))` via `MinusSymbol::makeIntTerm`).
/// Like [`numeral_term`]'s caller it bounds the literal to `u64` (large literals are a deferred bignum
/// path); the lexer guarantees the `-` prefix + digits.
fn neg_magnitude(text: &str) -> Result<u64, String> {
    text.strip_prefix('-')
        .unwrap_or(text)
        .parse()
        .map_err(|_| format!("bad negative integer `{text}`"))
}

/// Build a kernel `DagId` directly from a parse tree — the **ground command-term** path. Unlike
/// [`build_term`] (which yields a `Term` for statements/patterns), this constructs DAG nodes through the
/// engine, so it can build built-in **literals** (string/qid/float values a `Term` cannot carry) and a
/// compact `s^n(0)` numeral (no successor chain). Operators dispatch by theory via [`Engine::make_node`].
/// Variables are rejected — a `reduce` term is ground.
pub fn build_dag(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
) -> Result<DagId, String> {
    match g.prods[tree.prod as usize].action {
        Action::PassThru => {
            let child = tree.nt_children.first().ok_or("PassThru without a child")?;
            build_dag(child, g, engine, nat_zero, nat_succ, tokens, i)
        }
        Action::MakeTerm(sym) => {
            let args = dag_args(tree, g, engine, nat_zero, nat_succ, tokens, i)?;
            Ok(engine.make_node(sym, args))
        }
        Action::MakeNatural(succ) => {
            let text = tokens[tree.start].text(i);
            let n: u64 = text.parse().map_err(|_| format!("bad numeral `{text}`"))?;
            let zero = nat_zero.ok_or("MAKE_NATURAL without a zero symbol")?;
            let base = engine.make_const(zero);
            Ok(engine.make_iter(succ, n, base))
        }
        Action::MakeInteger(minus) => {
            let text = tokens[tree.start].text(i);
            let n: u64 = neg_magnitude(text)?;
            let zero = nat_zero.ok_or("MAKE_INTEGER without a zero symbol")?;
            let succ = nat_succ.ok_or("MAKE_INTEGER without a successor symbol")?;
            let base = engine.make_const(zero);
            let nat = engine.make_iter(succ, n, base);
            Ok(engine.make_node(minus, vec![nat]))
        }
        Action::MakeString(sym) => Ok(engine.make_string(sym, &unquote_string(tokens[tree.start].text(i)))),
        Action::MakeQid(sym) => {
            let text = tokens[tree.start].text(i);
            Ok(engine.make_qid(sym, text.strip_prefix('\'').unwrap_or(text)))
        }
        Action::MakeFloat(sym) => {
            let text = tokens[tree.start].text(i);
            let v: f64 = text.parse().map_err(|_| format!("bad float `{text}`"))?;
            Ok(engine.make_float(sym, v))
        }
        Action::MakeVariable(_) => Err("a reduce-command term must be ground (no variables)".into()),
        Action::AssocList => Err("assoc-list node reached build_dag directly".into()),
        Action::Nop => Err("a sort production has no term".into()),
        Action::MakeIter(_) => Err("the f^n iter-token form is deferred".into()),
    }
}

/// The argument DAGs for a `MakeTerm`: the nonterminal children, flattening a single assoc-list child to
/// the operator's full argument sequence (the `build_term` `make_args` analogue, on the DAG side). A
/// manual loop (not `map`) so the `&mut Engine` reborrows per child.
fn dag_args(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
) -> Result<Vec<DagId>, String> {
    if tree.nt_children.len() == 1 && is_assoc_list(g, &tree.nt_children[0]) {
        return flatten_dag_assoc(&tree.nt_children[0], g, engine, nat_zero, nat_succ, tokens, i);
    }
    let mut args = Vec::with_capacity(tree.nt_children.len());
    for c in &tree.nt_children {
        args.push(build_dag(c, g, engine, nat_zero, nat_succ, tokens, i)?);
    }
    Ok(args)
}

fn flatten_dag_assoc(
    node: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
) -> Result<Vec<DagId>, String> {
    let mut rev = Vec::new();
    let mut cur = node;
    loop {
        rev.push(build_dag(&cur.nt_children[1], g, engine, nat_zero, nat_succ, tokens, i)?);
        let left = &cur.nt_children[0];
        if is_assoc_list(g, left) {
            cur = left;
        } else {
            rev.push(build_dag(left, g, engine, nat_zero, nat_succ, tokens, i)?);
            break;
        }
    }
    rev.reverse();
    Ok(rev)
}

/// Strip a string literal's surrounding quotes and undo its escapes (the lexer keeps the quotes).
fn unquote_string(tok: &str) -> String {
    let inner = tok.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(tok);
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => out.push(other), // \" \\ and any other escaped char
                None => {}
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfparser::{earley, forest};
    use crate::grammar::{build::build_grammar, Nt};
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
  op _*_ : NzNat NzNat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (*) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _*_ : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
  op gcd : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (gcd) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op gcd : Nat Nat -> Nat [ditto] .
endfm
";

    /// A self-contained harness over NATB: parse a term, build it, reduce it, and report `(result-sort
    /// name, rewrite count, deep-equal to a reference numeral)`.
    struct Natb {
        m: BuiltModule,
        i: Interner,
        g: CompiledGrammar,
    }

    fn natb() -> Natb {
        let mut i = Interner::new();
        let toks = tokenize(NATB, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let m = build_module(&s.modules[0], &mut i).expect("build");
        let g = CompiledGrammar::compile(&build_grammar(&m, &mut i));
        Natb { m, i, g }
    }

    impl Natb {
        /// Parse + build + reduce a ground term; return `(result, rewrites)`.
        fn reduce(&mut self, term: &str) -> (tnk_core::dag::DagId, u64) {
            let tokens = tokenize(term, &mut self.i);
            let chart = earley::parse(&self.g, &tokens, Nt::Term, &self.i);
            let parse = forest::extract(&self.g, &chart, tokens.len(), Nt::Term).expect("parse");
            assert!(!parse.ambiguous, "`{term}` parsed ambiguously");
            let mut vars = VarIndex::new();
            let t = build_term(&parse.tree, &self.g, &self.m, &tokens, &self.i, &mut vars)
                .expect("build_term");
            let dag = self.m.engine.instantiate(&t, &empty_subst());
            self.m.engine.reset_rewrites();
            let r = self.m.engine.reduce(dag);
            (r, self.m.engine.rewrites())
        }

        /// A reference numeral `s^n(0)` built directly via the kernel.
        fn numeral(&mut self, n: u64) -> tnk_core::dag::DagId {
            let z = self.m.engine.make_const(self.m.nat_zero.unwrap());
            self.m.engine.make_iter(self.m.nat_succ.unwrap(), n, z)
        }

        fn sort_name(&self, d: tnk_core::dag::DagId) -> String {
            self.m.engine.sorts().name(self.m.engine.sort_of(d)).to_string()
        }
    }

    fn empty_subst() -> tnk_core::term::Subst {
        let mut s = tnk_core::term::Subst::new();
        s.reset(0);
        s
    }

    /// The B4.4b milestone for terms: parse `.maude` text → reduce → matches a kernel-built reference,
    /// with the binary's result sort and rewrite count.
    #[test]
    fn reduces_arithmetic_to_reference_numerals() {
        let mut e = natb();

        let (r, rw) = e.reduce("2 + 3");
        let five = e.numeral(5);
        assert!(e.m.engine.deep_equal(r, five), "2 + 3 = 5");
        assert_eq!(e.sort_name(r), "NzNat");
        assert_eq!(rw, 1, "one ACU_NumberOp rewrite");

        let (r, _) = e.reduce("3 * 4");
        let twelve = e.numeral(12);
        assert!(e.m.engine.deep_equal(r, twelve), "3 * 4 = 12");

        let (r, _) = e.reduce("gcd ( 12 , 18 )");
        let six = e.numeral(6);
        assert!(e.m.engine.deep_equal(r, six), "gcd(12, 18) = 6");
    }

    #[test]
    fn reduces_repeated_successor_and_parens() {
        let mut e = natb();
        // `s s 0` is a ground iter numeral (no rewrites); `(s 0) + (s s 0)` exercises parens + ACU.
        let (r, _) = e.reduce("s s 0");
        let two = e.numeral(2);
        assert!(e.m.engine.deep_equal(r, two), "s s 0 = s^2(0)");

        let (r, _) = e.reduce("( s 0 ) + ( s s 0 )");
        let three = e.numeral(3);
        assert!(e.m.engine.deep_equal(r, three), "(s 0) + (s s 0) = 3");
    }

    #[test]
    fn relational_reduces_to_truth_constant() {
        let mut e = natb();
        let (r, _) = e.reduce("2 < 3");
        assert_eq!(e.sort_name(r), "Truth", "2 < 3 : Truth");
    }
}
