//! The surface (recursive-descent) parser: `.maude` token stream → [`Source`] (functional modules +
//! commands). Term-carrying parts are collected as raw token **bubbles** (terminator-delimited), handed
//! to the mixfix parser later (B4.4). This replaces Maude's flex/bison `lexBubble` global handshake with
//! an explicit cursor + `collect_until` (decision: no hidden lexer↔parser state).

use crate::lex::{Interner, TokKind, Token};
use crate::surface::ast::*;

pub type PResult<T> = Result<T, String>;

pub struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    i: &'a Interner,
}

impl<'a> Parser<'a> {
    pub fn new(toks: &'a [Token], i: &'a Interner) -> Self {
        Parser { toks, pos: 0, i }
    }

    // ---- cursor primitives ----
    fn peek(&self) -> Option<Token> {
        self.toks.get(self.pos).copied()
    }
    fn peek_text(&self) -> Option<&'a str> {
        self.peek().map(|t| self.i.resolve(t.sym))
    }
    fn at(&self, kw: &str) -> bool {
        self.peek_text() == Some(kw)
    }
    fn at_dot(&self) -> bool {
        self.peek().is_some_and(|t| t.kind == TokKind::Dot)
    }
    fn advance(&mut self) -> Option<Token> {
        let t = self.peek();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, kw: &str) -> PResult<()> {
        if self.at(kw) {
            self.advance();
            Ok(())
        } else {
            Err(format!("expected `{kw}`, found {:?}", self.peek_text()))
        }
    }
    fn eat_dot(&mut self) -> PResult<()> {
        if self.at_dot() {
            self.advance();
            Ok(())
        } else {
            Err(format!("expected `.`, found {:?}", self.peek_text()))
        }
    }
    /// An identifier token's text (any non-Dot token), consumed.
    fn name(&mut self) -> PResult<String> {
        match self.advance() {
            Some(t) if t.kind != TokKind::Dot => Ok(self.i.resolve(t.sym).to_string()),
            other => Err(format!("expected a name, found {other:?}")),
        }
    }

    /// Collect a token bubble until a terminator text (or any `.`) at parenthesis depth 0; the terminator
    /// is left unconsumed. `(`/`)` track depth so a terminator inside parens does not end the bubble.
    fn collect_until(&mut self, terms: &[&str]) -> Vec<Token> {
        let mut depth = 0i32;
        let mut out = Vec::new();
        while let Some(t) = self.peek() {
            let txt = self.i.resolve(t.sym);
            if depth == 0 && (t.kind == TokKind::Dot || terms.contains(&txt)) {
                break;
            }
            match txt {
                "(" => depth += 1,
                ")" => depth -= 1,
                _ => {}
            }
            out.push(t);
            self.advance();
        }
        out
    }

    /// Collect the tokens inside a balanced `( … )` (consuming both parens).
    fn balanced(&mut self) -> PResult<Vec<Token>> {
        self.eat("(")?;
        let mut depth = 1i32;
        let mut out = Vec::new();
        while let Some(t) = self.peek() {
            match self.i.resolve(t.sym) {
                "(" => depth += 1,
                ")" => {
                    depth -= 1;
                    if depth == 0 {
                        self.advance();
                        return Ok(out);
                    }
                }
                _ => {}
            }
            out.push(t);
            self.advance();
        }
        Err("unbalanced `(`".into())
    }

    // ---- top level ----
    pub fn parse_source(&mut self) -> PResult<Source> {
        let mut src = Source::default();
        while let Some(txt) = self.peek_text() {
            // A command runs against the most recently entered module (Maude's current module).
            match txt {
                "fmod" | "mod" => src.modules.push(self.module()?),
                "reduce" | "red" => {
                    let m = src.modules.len().checked_sub(1).ok_or("command before any module")?;
                    self.advance();
                    let term = self.collect_until(&[]);
                    self.eat_dot()?;
                    src.commands.push((m, Command::Reduce { term }));
                }
                "match" | "xmatch" => {
                    let m = src.modules.len().checked_sub(1).ok_or("command before any module")?;
                    let xmatch = txt == "xmatch";
                    self.advance();
                    let pattern = self.collect_until(&["<=?"]);
                    self.eat("<=?")?;
                    let subject = self.collect_until(&[]);
                    self.eat_dot()?;
                    src.commands.push((m, Command::Match { pattern, subject, xmatch }));
                }
                _ => return Err(format!("unexpected top-level token {txt:?}")),
            }
        }
        Ok(src)
    }

    fn module(&mut self) -> PResult<PreModule> {
        self.advance(); // fmod / mod
        let name = self.name()?;
        self.eat("is")?;
        let mut m = PreModule {
            name,
            sorts: Vec::new(),
            subsorts: Vec::new(),
            ops: Vec::new(),
            vars: Vec::new(),
            statements: Vec::new(),
        };
        while !self.at("endfm") && !self.at("endm") {
            self.decl(&mut m)?;
        }
        self.advance(); // endfm
        Ok(m)
    }

    fn decl(&mut self, m: &mut PreModule) -> PResult<()> {
        let kw = self.peek_text().ok_or("unexpected end of input in module")?;
        match kw {
            "sort" | "sorts" => {
                self.advance();
                while !self.at_dot() {
                    m.sorts.push(self.name()?);
                }
                self.eat_dot()?;
            }
            "subsort" | "subsorts" => {
                self.advance();
                // groups of sort names separated by `<`, e.g. `A B < C < D`.
                let mut chain = vec![Vec::new()];
                while !self.at_dot() {
                    if self.at("<") {
                        self.advance();
                        chain.push(Vec::new());
                    } else {
                        chain.last_mut().unwrap().push(self.name()?);
                    }
                }
                self.eat_dot()?;
                m.subsorts.push(chain);
            }
            "op" | "ops" => {
                let multi = kw == "ops";
                self.advance();
                let names = self.collect_until(&[":"]);
                self.eat(":")?;
                let mut domain = Vec::new();
                while !self.at("->") {
                    domain.push(self.name()?);
                }
                self.eat("->")?;
                let range = self.name()?;
                let attrs = if self.at("[") { self.attrs()? } else { Attrs::default() };
                self.eat_dot()?;
                if multi {
                    for t in names {
                        m.ops.push(OpDecl {
                            name: vec![t],
                            domain: domain.clone(),
                            range: range.clone(),
                            attrs: attrs.clone_shallow(),
                        });
                    }
                } else {
                    m.ops.push(OpDecl { name: names, domain, range, attrs });
                }
            }
            "var" | "vars" => {
                self.advance();
                let mut names = Vec::new();
                while !self.at(":") {
                    names.push(self.name()?);
                }
                self.eat(":")?;
                let sort = self.name()?;
                self.eat_dot()?;
                m.vars.push(VarDecl { names, sort });
            }
            "eq" | "ceq" => {
                let conditional = kw == "ceq";
                self.advance();
                let lhs = self.collect_until(&["="]);
                self.eat("=")?;
                let (rhs, cond);
                if conditional {
                    rhs = self.collect_until(&["if"]);
                    self.eat("if")?;
                    cond = Some(self.collect_until(&["[owise]"]));
                } else {
                    rhs = self.collect_until(&[]);
                    cond = None;
                }
                let owise = self.opt_owise()?;
                self.eat_dot()?;
                m.statements.push(Statement::Eq { lhs, rhs, cond, owise });
            }
            "mb" | "cmb" => {
                let conditional = kw == "cmb";
                self.advance();
                let lhs = self.collect_until(&[":"]);
                self.eat(":")?;
                let sort;
                let cond;
                if conditional {
                    sort = self.collect_until(&["if"]);
                    self.eat("if")?;
                    cond = Some(self.collect_until(&[]));
                } else {
                    sort = self.collect_until(&[]);
                    cond = None;
                }
                self.eat_dot()?;
                m.statements.push(Statement::Mb { lhs, sort, cond });
            }
            other => return Err(format!("unsupported declaration `{other}`")),
        }
        Ok(())
    }

    /// A trailing `[owise]` on an equation (the only attribute statements carry in the functional subset).
    fn opt_owise(&mut self) -> PResult<bool> {
        if self.at("[") {
            self.advance();
            self.eat("owise")?;
            self.eat("]")?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    // ---- operator attributes ----
    fn attrs(&mut self) -> PResult<Attrs> {
        self.eat("[")?;
        let mut a = Attrs::default();
        while !self.at("]") {
            let kw = self.peek_text().ok_or("unexpected end in op attributes")?;
            match kw {
                "assoc" => { self.advance(); a.assoc = true; }
                "comm" => { self.advance(); a.comm = true; }
                "idem" => { self.advance(); a.idem = true; }
                "iter" => { self.advance(); a.iter = true; }
                "ctor" => { self.advance(); a.ctor = true; }
                "ditto" => { self.advance(); a.ditto = true; }
                "memo" | "frozen" | "config" | "obj" | "msg" | "portal" => { self.advance(); }
                "id:" => {
                    self.advance();
                    a.id = Some(self.collect_until(&["]"]));
                }
                "prec" => {
                    self.advance();
                    a.prec = Some(self.name()?.parse().map_err(|_| "bad prec".to_string())?);
                }
                "gather" => {
                    self.advance();
                    let g = self.balanced()?;
                    a.gather = Some(self.gather_elems(&g)?);
                }
                "strat" => {
                    self.advance();
                    let s = self.balanced()?;
                    a.strat = Some(
                        s.iter()
                            .map(|t| self.i.resolve(t.sym).parse::<u32>().map_err(|_| "bad strat".to_string()))
                            .collect::<Result<_, _>>()?,
                    );
                }
                "special" => {
                    self.advance();
                    a.special = Some(self.special()?);
                }
                "format" | "metadata" | "poly" | "latex" => {
                    // skip the keyword and its `( … )` / token argument (not modelled in the subset).
                    self.advance();
                    if self.at("(") {
                        self.balanced()?;
                    } else if !self.at("]") {
                        self.advance();
                    }
                }
                other => return Err(format!("unsupported op attribute `{other}`")),
            }
        }
        self.eat("]")?;
        Ok(a)
    }

    fn gather_elems(&self, toks: &[Token]) -> PResult<Vec<GatherElem>> {
        toks.iter()
            .map(|t| match self.i.resolve(t.sym) {
                "E" => Ok(GatherElem::Strong),
                "e" => Ok(GatherElem::Weak),
                "&" => Ok(GatherElem::Any),
                other => Err(format!("bad gather element `{other}`")),
            })
            .collect()
    }

    fn special(&mut self) -> PResult<SpecialSpec> {
        self.eat("(")?;
        let mut spec = SpecialSpec::default();
        while !self.at(")") {
            let hook = self.peek_text().ok_or("unexpected end in special()")?;
            match hook {
                "id-hook" => {
                    self.advance();
                    let class = self.name()?;
                    let data = if self.at("(") {
                        self.balanced()?.iter().map(|t| self.i.resolve(t.sym).to_string()).collect()
                    } else {
                        Vec::new()
                    };
                    spec.id_hook = Some((class, data));
                }
                "op-hook" => {
                    self.advance();
                    let purpose = self.name()?;
                    let sig = self.balanced()?;
                    spec.op_hooks.push((purpose, sig));
                }
                "term-hook" => {
                    self.advance();
                    let purpose = self.name()?;
                    let term = self.balanced()?;
                    spec.term_hooks.push((purpose, term));
                }
                other => return Err(format!("unsupported special hook `{other}`")),
            }
        }
        self.eat(")")?;
        Ok(spec)
    }
}

impl Attrs {
    /// A shallow clone for splitting `ops f g : …` into one `OpDecl` per name. The flag/prec/gather/strat
    /// fields are `Copy`-ish; `special`/`id` (token bubbles) are cloned. (`ops` with a `special` attr is
    /// unusual but supported.)
    fn clone_shallow(&self) -> Attrs {
        Attrs {
            assoc: self.assoc,
            comm: self.comm,
            idem: self.idem,
            iter: self.iter,
            ctor: self.ctor,
            id: self.id.clone(),
            prec: self.prec,
            gather: self.gather.clone(),
            strat: self.strat.clone(),
            special: self.special.clone(),
            ditto: self.ditto,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;

    fn parse(src: &str) -> Source {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        Parser::new(&toks, &i).parse_source().expect("parse ok")
    }

    #[test]
    fn parses_iter_module_and_command() {
        let src = "\
fmod ITER is
  sorts Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  eq s s 0 = 0 .
endfm
red s s s s s 0 .
";
        let s = parse(src);
        assert_eq!(s.modules.len(), 1);
        let m = &s.modules[0];
        assert_eq!(m.name, "ITER");
        assert_eq!(m.sorts, ["Zero", "NzNat", "Nat"]);
        assert_eq!(m.subsorts, vec![vec![vec!["Zero".to_string(), "NzNat".into()], vec!["Nat".into()]]]);
        assert_eq!(m.ops.len(), 2);
        assert_eq!(m.ops[0].range, "Zero");
        assert!(m.ops[0].attrs.ctor && m.ops[0].domain.is_empty());
        assert_eq!(m.ops[1].domain, ["Nat"]);
        assert!(m.ops[1].attrs.iter && m.ops[1].attrs.ctor && m.ops[1].attrs.special.is_some());
        assert_eq!(m.statements.len(), 1);
        assert_eq!(s.commands.len(), 1);
    }

    #[test]
    fn parses_nat_ops_and_attrs() {
        let src = "\
fmod NATB is
  sorts Truth Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  ops tt ff : -> Truth [ctor] .
  op _+_ : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (+) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _+_ : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
endfm
";
        let m = &parse(src).modules[0];
        // `ops tt ff` → two constants.
        assert_eq!(m.ops.iter().filter(|o| o.range == "Truth" && o.domain.is_empty()).count(), 2);
        let plus0 = &m.ops[2];
        assert!(plus0.attrs.assoc && plus0.attrs.comm && plus0.attrs.special.is_some());
        let plus1 = &m.ops[3];
        assert!(plus1.attrs.ditto);
        let lt = m.ops.last().unwrap();
        let sp = lt.attrs.special.as_ref().unwrap();
        assert_eq!(sp.id_hook.as_ref().unwrap().0, "NumberOpSymbol");
        assert_eq!(sp.id_hook.as_ref().unwrap().1, ["<"]);
        assert_eq!(sp.op_hooks.len(), 1);
        assert_eq!(sp.term_hooks.len(), 2);
    }
}
