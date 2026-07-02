//! Grammar-aware operator renaming for statement term-bubbles (the `op _,_ to _;_` case).
//!
//! A renaming `op _,_ to _;_` must rewrite only the *operator* occurrences of `,` in a term, never the
//! argument separators of an enclosing prefix application — a distinction only the grammar can make:
//! `delete(E, (E, S))` has an arg-separator comma and an operator comma at the *same* paren depth, and
//! `if E in S' then E, A else A fi` hides an operator comma inside a mixfix operand. So we build the
//! source module's grammar, parse each bubble, and surgically replace the literal fragment tokens at the
//! parse-identified positions of the renamed operators — leaving every other token (and the bubble's
//! exact shape) untouched. Single-token op renames (`empty to none`) ride the same path, identified by
//! parse rather than blind text match.

use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::cfparser::{earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::{Action, GSym, Nt};
use crate::lex::{split_mixfix, Frag, Interner, TokKind, Token};
use crate::sig::build_sig::build_module;
use crate::sig::syntax::BuiltModule;
use crate::surface::ast::PreModule;
use std::collections::HashMap;

/// A renamer for one import's op renamings: the source module's signature + grammar (built once from the
/// *pre-rename* declarations) plus the from-name → target-fragment map.
pub struct OpRenamer {
    built: BuiltModule,
    grammar: CompiledGrammar,
    /// from-op canonical name (`_,_`, `empty`, `f`) → the candidate renames of that name: each an optional
    /// disambiguating **arity** (`Some(2)` for `op f : A B -> C to g`; `None` renames every overload) with
    /// the target op's literal fragment texts, in order (`_;_` → `[";"]`, `none` → `["none"]`).
    targets: HashMap<String, Vec<(Option<usize>, Vec<String>)>>,
}

impl OpRenamer {
    /// Build the grammar of `pm` (a flattened, pre-rename module) for the op renames `renames`
    /// (`(from_name, arity, to_name)` — `arity` = `Some(n)` for an arity-disambiguated rename of one
    /// overload, `None` for a plain rename of every overload). Returns `None` if there is nothing to do; an
    /// `Err` only if building the source module/grammar fails.
    pub fn new(
        pm: &PreModule,
        renames: &[(String, Option<usize>, String)],
        interner: &mut Interner,
    ) -> Result<Option<Self>, String> {
        if renames.is_empty() {
            return Ok(None);
        }
        let mut targets: HashMap<String, Vec<(Option<usize>, Vec<String>)>> = HashMap::new();
        for (from, arity, to) in renames {
            targets.entry(from.clone()).or_default().push((*arity, literal_frags(to, interner)));
        }
        let built = build_module(pm, interner)?;
        let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
        Ok(Some(Self { built, grammar, targets }))
    }

    /// Rewrite one term bubble in place-ish (returns a fresh token vector). Replaces every renamed
    /// operator's literal fragment tokens with its target's. A bubble that does not parse as a term (a
    /// non-term fragment) is returned unchanged — operator identity is undefined there, so nothing is
    /// renamed (the prelude's renamed imports have no such fragments mentioning the renamed ops).
    pub fn rewrite(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        if bubble.is_empty() {
            return bubble.to_vec();
        }
        let tree = match parse_term(bubble, &self.grammar, interner) {
            Ok(t) => t,
            Err(_) => return bubble.to_vec(),
        };
        let mut edits: Vec<(usize, &str)> = Vec::new();
        self.collect(&tree, &mut edits);
        if edits.is_empty() {
            return bubble.to_vec();
        }
        let new_syms: Vec<(usize, _)> =
            edits.iter().map(|(pos, text)| (*pos, interner.intern(text))).collect();
        let mut out = bubble.to_vec();
        for (pos, sym) in new_syms {
            out[pos].sym = sym;
        }
        out
    }

    /// Walk `t`, recording `(token-position, replacement-text)` for each literal fragment of a renamed
    /// operator. At a `MakeTerm(sym)` node whose symbol is renamed, the literal fragments are the
    /// terminal positions of the production's rhs — found by tiling `[start, end)` with the child spans
    /// (Maude's `extractFirstSubparse` order): a terminal consumes one token, a nonterminal jumps to the
    /// next child's end.
    fn collect<'a>(&'a self, t: &PTree, edits: &mut Vec<(usize, &'a str)>) {
        let prod = &self.grammar.prods[t.prod as usize];
        if let Action::MakeTerm(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            // This node's arity = the number of argument nonterminals in the production. An
            // arity-disambiguated candidate matches only that arity; a plain (`None`) candidate matches any.
            let arity = prod.rhs.iter().filter(|g| matches!(g, GSym::N(_))).count();
            if let Some(target) = self.targets.get(name).and_then(|cands| {
                cands
                    .iter()
                    .find(|(a, _)| *a == Some(arity))
                    .or_else(|| cands.iter().find(|(a, _)| a.is_none()))
                    .map(|(_, frags)| frags)
            }) {
                let mut cursor = t.start;
                let mut child = 0;
                let mut frag = 0;
                for g in &prod.rhs {
                    match g {
                        GSym::T(_) => {
                            if let Some(text) = target.get(frag) {
                                edits.push((cursor, text));
                            }
                            frag += 1;
                            cursor += 1;
                        }
                        GSym::N(_) => {
                            cursor = t.nt_children[child].end;
                            child += 1;
                        }
                    }
                }
            }
        }
        for c in &t.nt_children {
            self.collect(c, edits);
        }
    }
}

/// A grammar-aware operator-map substituter for **view** op→op instantiation, where the source and target
/// operators may have *different* fixity (`op f to _+_`, `op _#_ to g`, `op _#_ to _+_`) — a distinction a
/// token substitution cannot express. Like [`OpRenamer`] it builds the source (parameterized) module's
/// grammar and parses each statement bubble, but instead of surgically swapping an operator's literal
/// fragments it **reconstructs** each mapped operator application in the *target* operator's syntax: a
/// prefix target `g` emits `g ( a , b )`, a mixfix target `_+_` emits `( ( a ) + ( b ) )`, wrapped around
/// the (recursively rewritten) argument sub-bubbles. Every non-mapped subterm is reproduced token-for-token,
/// so the bubble's shape is preserved wherever no mapped operator occurs.
///
/// The from-name is a symbol of the source (parameter-theory) signature; the to-name is spelled in the
/// target module's syntax — mirroring [`OpRenamer`], but generalized to a fixity change. Prefix→prefix and
/// constant op→term maps stay on the caller's textual path; only maps with a mixfix side come here.
/// The target of a view operator map that needs grammar-aware reconstruction: another operator (with a
/// possibly different fixity), or a **term template** for an op→term map with variable arguments.
#[derive(Clone)]
pub enum ReconTarget {
    /// op→op: the target operator's canonical name (`g`, `_+_`) — the application is re-emitted in its syntax.
    Op(String),
    /// op(A, B, …)→term: a term template. `formals` are the from-pattern's argument variable base-names in
    /// order (`lt(A, B)` ⇒ `["A", "B"]`); `template` is the target term's tokens (`A < B`). At each
    /// occurrence, every template variable whose base-name is a formal is replaced by the (rewritten,
    /// parenthesized) actual argument at that position.
    Term { formals: Vec<String>, template: Vec<Token> },
}

pub struct ViewOpSubst {
    built: BuiltModule,
    grammar: CompiledGrammar,
    /// source op canonical name (`f`, `_#_`, `lt`) → its reconstruction target.
    targets: HashMap<String, ReconTarget>,
}

impl ViewOpSubst {
    /// Build over `pm` (the source parameterized module, flattened with its parameter copies so the theory
    /// operators and its variables are in scope). `Ok(None)` if `maps` is empty; `Err` only if building the
    /// source module/grammar fails.
    pub fn new(
        pm: &PreModule,
        maps: &[(String, ReconTarget)],
        interner: &mut Interner,
    ) -> Result<Option<Self>, String> {
        if maps.is_empty() {
            return Ok(None);
        }
        let built = build_module(pm, interner)?;
        let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
        let targets = maps.iter().cloned().collect();
        Ok(Some(Self { built, grammar, targets }))
    }

    /// Rewrite one term bubble. A bubble that does not parse as a single term (e.g. a condition fragment
    /// carrying `=`) is returned unchanged — operator identity is undefined there.
    pub fn rewrite(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        if bubble.is_empty() {
            return bubble.to_vec();
        }
        match parse_term(bubble, &self.grammar, interner) {
            Ok(tree) => self.emit(&tree, bubble, interner),
            Err(_) => bubble.to_vec(),
        }
    }

    /// Re-serialize the parse tree `t`, substituting a mapped operator's application with the target
    /// operator's syntax and reproducing everything else token-for-token (the terminal positions are tiled
    /// exactly as in [`OpRenamer::collect`]: a terminal consumes one token, a nonterminal jumps to its
    /// child's end).
    fn emit(&self, t: &PTree, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        let prod = &self.grammar.prods[t.prod as usize];
        if let Action::MakeTerm(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            if let Some(target) = self.targets.get(name).cloned() {
                let args: Vec<Vec<Token>> =
                    t.nt_children.iter().map(|c| self.emit(c, bubble, interner)).collect();
                return match target {
                    ReconTarget::Op(name) => emit_application(&name, &args, bubble, interner),
                    ReconTarget::Term { formals, template } => {
                        emit_template(&formals, &template, &args, bubble, interner)
                    }
                };
            }
        }
        let mut out = Vec::new();
        let mut cursor = t.start;
        let mut child = 0;
        for g in &prod.rhs {
            match g {
                GSym::T(_) => {
                    out.push(bubble[cursor]);
                    cursor += 1;
                }
                GSym::N(_) => {
                    let c = &t.nt_children[child];
                    out.extend(self.emit(c, bubble, interner));
                    cursor = c.end;
                    child += 1;
                }
            }
        }
        out
    }
}

/// Emit an application of the operator named `target` to `args` (each an already-rewritten sub-bubble), in
/// `target`'s mixfix syntax: `g ( a , b )` for a prefix/constant name, `( ( a ) + ( b ) )` for a mixfix
/// name (redundant parentheses guard precedence when the result is re-parsed against the instance grammar).
/// `line` for synthesized tokens is borrowed from the first available argument/bubble token.
fn emit_application(
    target: &str,
    args: &[Vec<Token>],
    bubble: &[Token],
    interner: &mut Interner,
) -> Vec<Token> {
    let frags = split_mixfix(target, interner);
    let line = args.iter().flatten().next().or_else(|| bubble.first()).map(|t| t.line).unwrap_or(0);
    let lp = Token { sym: interner.intern("("), line, kind: TokKind::Punct };
    let rp = Token { sym: interner.intern(")"), line, kind: TokKind::Punct };
    let comma = Token { sym: interner.intern(","), line, kind: TokKind::Punct };
    let mut out = Vec::new();
    if frags.iter().any(|f| matches!(f, Frag::Hole)) {
        out.push(lp);
        let mut ai = 0;
        for f in &frags {
            match f {
                Frag::Tok(s) => out.push(Token { sym: *s, line, kind: TokKind::Ident }),
                Frag::Hole => {
                    out.push(lp);
                    if let Some(a) = args.get(ai) {
                        out.extend_from_slice(a);
                    }
                    out.push(rp);
                    ai += 1;
                }
            }
        }
        out.push(rp);
    } else {
        for f in &frags {
            if let Frag::Tok(s) = f {
                out.push(Token { sym: *s, line, kind: TokKind::Ident });
            }
        }
        if !args.is_empty() {
            out.push(lp);
            for (k, a) in args.iter().enumerate() {
                out.extend_from_slice(a);
                out.push(if k + 1 == args.len() { rp } else { comma });
            }
        }
    }
    out
}

/// Emit a term template for an op→term view map (`op lt(A, B) to term A < B`), substituting each formal
/// variable in `template` with the (already-rewritten) actual argument at the matching position. A template
/// token is a placeholder iff its base-name (the text before any `:sort` suffix) is one of `formals`; the
/// substituted argument is wrapped in parentheses so it re-parses at any precedence. Non-placeholder tokens
/// (operators, literals, the target term's own free variables) are reproduced verbatim.
fn emit_template(
    formals: &[String],
    template: &[Token],
    args: &[Vec<Token>],
    bubble: &[Token],
    interner: &mut Interner,
) -> Vec<Token> {
    let line = args.iter().flatten().next().or_else(|| bubble.first()).map(|t| t.line).unwrap_or(0);
    let lp = Token { sym: interner.intern("("), line, kind: TokKind::Punct };
    let rp = Token { sym: interner.intern(")"), line, kind: TokKind::Punct };
    let mut out = Vec::new();
    for t in template {
        let text = interner.resolve(t.sym);
        let base = text.split(':').next().unwrap_or(text);
        if let Some(idx) = formals.iter().position(|f| f == base)
            && let Some(arg) = args.get(idx)
        {
            out.push(lp);
            out.extend_from_slice(arg);
            out.push(rp);
        } else {
            out.push(*t);
        }
    }
    out
}

/// The literal (non-hole) fragment texts of a mixfix op name, in order (`_;_` → `[";"]`, `none` →
/// `["none"]`). Also used by the module system to rename an op *declaration*'s name tokens.
pub fn literal_frags(name: &str, interner: &mut Interner) -> Vec<String> {
    split_mixfix(name, interner)
        .into_iter()
        .filter_map(|f| match f {
            Frag::Tok(s) => Some(interner.resolve(s).to_string()),
            Frag::Hole => None,
        })
        .collect()
}

/// Parse a term token bubble to its first parse tree (the statement/pattern path, sans build).
fn parse_term(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    let chart = earley::parse(g, tokens, Nt::Term, i);
    let parsed = forest::extract(g, &chart, tokens.len(), Nt::Term)?;
    if parsed.ambiguous {
        return Err("ambiguous".into());
    }
    Ok(parsed.tree)
}
