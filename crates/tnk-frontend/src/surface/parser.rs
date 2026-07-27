//! The surface (recursive-descent) parser: `.maude` token stream → [`Source`] (functional modules +
//! commands). Term-carrying parts are collected as raw token **bubbles** (terminator-delimited), handed
//! to the mixfix parser later (B4.4). This replaces Maude's flex/bison `lexBubble` global handshake with
//! an explicit cursor + `collect_until` (decision: no hidden lexer↔parser state).

use crate::lex::{Interner, TokKind, Token};
use crate::surface::ast::*;

pub type PResult<T> = Result<T, String>;

/// The retained trailing attributes of a statement: the execution-relevant `[owise]`/`[nonexec]` flags and
/// the `[label …]` name (kept for META up-translation — `upEqs`/`upMbs` render it, matching the reference).
/// Other attributes (`metadata`, `print`, `format`, …) are parsed but not retained — see
/// [`Parser::stmt_attrs`].
#[derive(Debug, Default, Clone)]
struct StmtAttrs {
    owise: bool,
    nonexec: bool,
    variant: bool,
    narrowing: bool,
    label: Option<String>,
    /// The tokens of a `[print …]` attribute's content (the strings/variables after `print`), captured for
    /// validation: a print variable must resolve to a variable of the statement (Maude rejects an unknown
    /// token and drops the statement — fable-audit.md §3.6, C4f). Empty when there is no `print` attribute.
    print: Vec<Token>,
}

pub struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    i: &'a Interner,
}

/// The index of the first or last top-level token (depth 0 over `()`/`[]`/`{}`) whose text is `kw`.
/// Used to split a [`Parser::collect_to_dot`] statement body.
fn top_level_find(toks: &[Token], i: &Interner, kw: &str, last: bool) -> Option<usize> {
    let mut depth = 0i32;
    let mut found = None;
    for (idx, t) in toks.iter().enumerate() {
        match i.resolve(t.sym) {
            "(" | "[" | "{" => depth += 1,
            ")" | "]" | "}" => depth -= 1,
            s if depth == 0 && s == kw => {
                found = Some(idx);
                if !last {
                    break;
                }
            }
            _ => {}
        }
    }
    found
}

/// Locate the statement-level `=` in an equation bubble. It is normally the first top-level `=`;
/// choosing the last one misclassifies unparenthesized mixfix operators in the right-hand side (for
/// example `eq p = while Q = 0 do … od`). The one exceptional shape needed by Maude's built-in syntax
/// is `_=[_]_` on the left: when the first `=` opens a bracketed argument and another separator follows
/// that argument, use the latter. If no later `=` exists, the bracket starts an ordinary right-hand side.
fn equation_separator(toks: &[Token], i: &Interner) -> Option<usize> {
    let first = top_level_find(toks, i, "=", false)?;
    if toks.get(first + 1).map(|token| token.text(i)) == Some("[")
        && let Some(later) = top_level_find(&toks[first + 1..], i, "=", false)
    {
        return Some(first + 1 + later);
    }
    Some(first)
}

/// Peel a trailing top-level statement-attribute group `[ owise | nonexec | dnt | metadata … ]` off `body`,
/// returning the execution-relevant flags. A trailing `[ … ]` is attributes **only** when its first
/// inner token is a statement-attribute keyword — otherwise it is a `[_]`-list / `{_}`-set *term* (e.g.
/// the rhs of `eq reverse([E P]) = [$reverse(P, E)] .`), which is left in `body`.
fn peel_stmt_attrs(body: &mut Vec<Token>, i: &Interner) -> StmtAttrs {
    let mut sa = StmtAttrs::default();
    if body.last().map(|t| i.resolve(t.sym)) != Some("]") {
        return sa;
    }
    // The matching `[` of the trailing `]` (scan from the end).
    let mut depth = 0i32;
    let mut open = None;
    for idx in (0..body.len()).rev() {
        match i.resolve(body[idx].sym) {
            "]" | ")" | "}" => depth += 1,
            "[" | "(" | "{" => {
                depth -= 1;
                if depth == 0 {
                    open = Some(idx);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(open) = open else { return sa };
    let is_attr_kw = |s: &str| {
        matches!(
            s,
            "owise"
                | "nonexec"
                | "label"
                | "metadata"
                | "print"
                | "format"
                | "variant"
                | "narrowing"
                | "dnt"
        )
    };
    if !body
        .get(open + 1)
        .map(|t| i.resolve(t.sym))
        .is_some_and(is_attr_kw)
    {
        return sa; // a `[_]`-list / `{_}`-set term, not attributes
    }
    // `label`/`metadata` each take one following argument token; capture the label name (for META
    // up-translation), skip metadata's, and ignore everything else token-by-token. `print` captures its
    // following string/variable list (until the next attribute keyword) for later validation (C4f).
    let mut want_arg: Option<&str> = None;
    let mut in_print = false;
    for t in &body[open + 1..body.len() - 1] {
        let s = i.resolve(t.sym);
        if let Some(kw) = want_arg.take() {
            if kw == "label" {
                sa.label = Some(s.to_string());
            }
            continue;
        }
        // A string is always a print item (never an attribute keyword); a non-string keyword ends the list.
        if in_print && (t.kind == TokKind::Str || !is_attr_kw(s)) {
            sa.print.push(*t);
            continue;
        }
        in_print = false;
        match s {
            "owise" => sa.owise = true,
            "nonexec" => sa.nonexec = true,
            "variant" => sa.variant = true,
            "narrowing" => sa.narrowing = true,
            "label" | "metadata" => want_arg = Some(s),
            "print" => in_print = true,
            _ => {}
        }
    }
    body.truncate(open);
    sa
}

/// Remove a top-level `such that … irreducible` suffix from a variant-command body and return the
/// comma-separated blocker bubble. The command builder parses each blocker against the same variable
/// namespace as the principal term/problem.
fn peel_irreducible_suffix(body: &mut Vec<Token>, i: &Interner) -> PResult<Vec<Token>> {
    let Some(such) = top_level_find(body, i, "such", false) else {
        return Ok(Vec::new());
    };
    if body.get(such + 1).map(|t| i.resolve(t.sym)) != Some("that")
        || body.last().map(|t| i.resolve(t.sym)) != Some("irreducible")
    {
        return Err("expected `such that <terms> irreducible`".into());
    }
    let mut blockers = body.split_off(such + 2);
    body.truncate(such);
    blockers.pop(); // `irreducible`
    if blockers.is_empty() {
        return Err("irreducibility constraint needs at least one term".into());
    }
    Ok(blockers)
}

/// A `[print …]` attribute is well-formed iff each of its non-string items resolves to a variable of the
/// statement: an on-the-fly typed variable (a token carrying `:`, self-declaring) or a bare name that is a
/// declared `var`/`vars` of the module. Maude rejects any other token ("bad token X") and DROPS the whole
/// statement — a bare name that only appears on-the-fly in the body is *not* accepted (fable-audit.md §3.6,
/// C4f; a declared-but-unused variable IS accepted — Maude only warns, so it stays valid here).
fn print_attr_ok(print: &[Token], m: &PreModule, i: &Interner) -> bool {
    print.iter().all(|t| {
        if t.kind == TokKind::Str {
            return true; // a string literal is always a valid print item
        }
        let s = i.resolve(t.sym);
        if s.contains(':') {
            return true; // an on-the-fly typed variable `X:Sort` declares itself
        }
        m.vars.iter().any(|vd| vd.names.iter().any(|n| n == s))
    })
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
    /// An optional `in <MODULE-EXPR> :` qualifier after a command keyword (Maude's `red in NAT : t .`).
    /// The module expression runs to the `:` that precedes the term — module names / instantiations have
    /// no top-level `:` (a colon variable `X:Nat` lexes as one token, so its `:` is invisible here). The
    /// tokens are concatenated (module names contain no spaces: `NAT`, `META-LEVEL`, `LIST{Nat}`).
    fn opt_in_module(&mut self) -> PResult<Option<String>> {
        if !self.at("in") {
            return Ok(None);
        }
        self.advance(); // `in`
        let toks = self.collect_until(&[":"]);
        self.eat(":")?;
        Ok(Some(toks.iter().map(|t| self.i.resolve(t.sym)).collect()))
    }

    /// An identifier token's text (any non-Dot token), consumed.
    fn name(&mut self) -> PResult<String> {
        match self.advance() {
            Some(t) if t.kind != TokKind::Dot => Ok(self.i.resolve(t.sym).to_string()),
            other => Err(format!("expected a name, found {other:?}")),
        }
    }

    /// The two synthetic tokens for Maude's class-attribute suffix `` `:_ ``.
    /// [`tokenize`](crate::lex::tokenize) pre-interns both fragments because the surface parser holds
    /// only `&Interner`.
    fn attribute_suffix(&self, line: u32) -> [Token; 2] {
        let fragment = |text| Token {
            sym: self
                .i
                .get(text)
                .expect("attribute suffix fragment must be pre-interned by tokenize"),
            line,
            kind: TokKind::Ident,
        };
        [fragment(":"), fragment("_")]
    }

    /// Desugar `class C` into a sort `C`, a subsort `C < Cid`, and the honorary class constant
    /// `op C : -> C [ctor]` (Maude's `processClassSorts`/`processClassOps`). In a theory the class constant
    /// is implicitly a parameter constant, so a parameter copy renames it `C` → `X$C`. `ctoks` is the
    /// complete structured class name (for example `List { X }`), reused as the constant's mixfix name.
    fn desugar_class(&self, m: &mut PreModule, ctoks: Vec<Token>, cname: &str) {
        m.sorts.push(cname.to_string());
        // `C < Cid`: a two-group chain (`[[C], [Cid]]`), as the `subsort` parser builds it.
        m.subsorts
            .push(vec![vec![cname.to_string()], vec!["Cid".to_string()]]);
        m.ops.push(OpDecl {
            name: ctoks,
            domain: Vec::new(),
            range: cname.to_string(),
            partial: false,
            attrs: Attrs {
                ctor: true,
                pconst: m.is_theory,
                ..Attrs::default()
            },
        });
    }

    /// Desugar a class attribute `a : S` into `op a`:_ : S -> Attribute [ctor gather (&)]` (Maude's
    /// `processClassOps`: the `attributeSuffix` ``"`:_"``, range `Attribute`, `gather (&)`). `atok` is the
    /// attribute name's own token; the mixfix name is `[a, :, _]` (canonical `a:_`, re-split to `a :_`).
    fn desugar_attribute(&self, m: &mut PreModule, atok: Token, asort: String) {
        let mut name = vec![atok];
        name.extend(self.attribute_suffix(atok.line));
        m.ops.push(OpDecl {
            name,
            domain: vec![asort],
            range: "Attribute".to_string(),
            partial: false,
            attrs: Attrs {
                ctor: true,
                gather: Some(vec![GatherElem::Any]),
                ..Attrs::default()
            },
        });
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

    /// Consume an operator name and its signature delimiter. Literal colons are legal name
    /// fragments (`<_:Snd|buff:_>`), so the delimiter is the last top-level `:` before the
    /// signature's top-level arrow, not the first colon token.
    fn op_names_before_signature(&mut self) -> PResult<Vec<Token>> {
        let mut depth = 0i32;
        let mut delimiter = None;
        for position in self.pos..self.toks.len() {
            match self.i.resolve(self.toks[position].sym) {
                "(" => depth += 1,
                ")" => depth -= 1,
                ":" if depth == 0 => delimiter = Some(position),
                "->" | "~>" if depth == 0 => break,
                _ => {}
            }
        }
        let delimiter =
            delimiter.ok_or_else(|| "operator declaration is missing `:`".to_string())?;
        let names = self.toks[self.pos..delimiter].to_vec();
        self.pos = delimiter + 1;
        Ok(names)
    }

    /// Collect a whole statement body up to the top-level terminator `.` (left unconsumed). Besides
    /// ordinary delimiters, account for reflected module constructors: a meta-level term can contain
    /// `fmod ... sorts ... . ... endfm` at top level, and those internal dots are data, not the enclosing
    /// equation's terminator.
    fn collect_to_dot(&mut self) -> Vec<Token> {
        let mut delimiter_depth = 0i32;
        let mut reflected_module_depth = 0i32;
        let mut out = Vec::new();
        while let Some(t) = self.peek() {
            let text = self.i.resolve(t.sym);
            if delimiter_depth == 0 && reflected_module_depth == 0 && t.kind == TokKind::Dot {
                break;
            }
            match text {
                "(" | "[" | "{" => delimiter_depth += 1,
                ")" | "]" | "}" => delimiter_depth -= 1,
                "fmod" | "mod" | "fth" | "th" | "smod" | "sth" | "omod" | "oth" => {
                    reflected_module_depth += 1;
                }
                "endfm" | "endm" | "endfth" | "endth" | "endsm" | "endsth" | "endom" | "endoth"
                    if reflected_module_depth > 0 =>
                {
                    reflected_module_depth -= 1;
                }
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

    fn narrowing_prefix_options(&mut self) -> PResult<(bool, bool, bool)> {
        self.eat("{")?;
        let mut fold = false;
        let mut vfold = false;
        let mut path = false;
        loop {
            match self.peek_text() {
                Some("fold") => fold = true,
                Some("vfold") => vfold = true,
                Some("path") => path = true,
                other => {
                    return Err(format!(
                        "vu-narrow: expected `fold`, `vfold`, or `path`, found {other:?}"
                    ));
                }
            }
            self.advance();
            if self.at(",") {
                self.advance();
            } else {
                break;
            }
        }
        self.eat("}")?;
        Ok((fold, vfold, path))
    }

    fn narrowing_command(&mut self, mut fold: bool, vfold: bool, path: bool) -> PResult<Command> {
        let fvu = self.at("fvu-narrow");
        if !fvu && !self.at("vu-narrow") {
            return Err("expected `vu-narrow` or `fvu-narrow`".into());
        }
        self.advance();
        fold |= fvu;
        let mut filter = false;
        let mut delay = false;
        if self.at("{")
            && self
                .toks
                .get(self.pos + 1)
                .is_some_and(|token| matches!(self.i.resolve(token.sym), "filter" | "delay"))
        {
            self.advance();
            loop {
                match self.peek_text() {
                    Some("filter") => filter = true,
                    Some("delay") => delay = true,
                    other => {
                        return Err(format!(
                            "vu-narrow: expected `filter` or `delay`, found {other:?}"
                        ));
                    }
                }
                self.advance();
                if self.at(",") {
                    self.advance();
                } else {
                    break;
                }
            }
            self.eat("}")?;
        }
        let (max_solutions, max_depth) = self.opt_search_bound()?;
        let module = self.opt_in_module()?;
        let subject = self.collect_until(&["=>1", "=>+", "=>*", "=>!"]);
        let arrow = match self.peek_text() {
            Some("=>1") => SearchArrow::One,
            Some("=>+") => SearchArrow::Plus,
            Some("=>*") => SearchArrow::Star,
            Some("=>!") => SearchArrow::Bang,
            other => {
                return Err(format!(
                    "vu-narrow: expected `=>1`/`=>+`/`=>*`/`=>!`, found {other:?}"
                ));
            }
        };
        self.advance();
        let goal = self.collect_until(&["such"]);
        let condition = if self.at("such") {
            self.advance();
            self.eat("that")?;
            Some(self.collect_until(&[]))
        } else {
            None
        };
        self.eat_dot()?;
        Ok(Command::Narrow {
            module,
            max_solutions,
            max_depth,
            subject,
            arrow,
            goal,
            condition,
            fold,
            fvu,
            vfold,
            path,
            filter,
            delay,
        })
    }

    // ---- top level ----

    /// Parse one top-level item — a module or a (module-untagged) command — or `None` at end of input.
    /// The REPL drives this directly (a command binds to its persistent current module); `parse_source`
    /// loops over it and re-applies Maude's most-recently-entered-module tagging.
    pub fn parse_top_item(&mut self) -> PResult<Option<TopItem>> {
        let Some(txt) = self.peek_text() else {
            return Ok(None);
        };
        let item = match txt {
            "fmod" | "mod" | "fth" | "th" | "smod" | "sth" | "omod" | "oth" => {
                TopItem::Module(self.module()?)
            }
            "view" => TopItem::View(self.view()?),
            "{" => {
                let (fold, vfold, path) = self.narrowing_prefix_options()?;
                TopItem::Command(self.narrowing_command(fold, vfold, path)?)
            }
            "vu-narrow" | "fvu-narrow" => {
                TopItem::Command(self.narrowing_command(false, false, false)?)
            }
            "show" => {
                self.advance();
                let (display, state) = match self.peek_text() {
                    Some("frontier") => {
                        self.advance();
                        self.eat("states")?;
                        (NarrowDisplay::Frontier, None)
                    }
                    Some("most") => {
                        self.advance();
                        self.eat("general")?;
                        self.eat("states")?;
                        (NarrowDisplay::MostGeneral, None)
                    }
                    Some("path") => {
                        self.advance();
                        let display = if self.at("states") {
                            self.advance();
                            NarrowDisplay::PathStates
                        } else {
                            NarrowDisplay::Path
                        };
                        let state = Some(
                            self.name()?
                                .parse::<u64>()
                                .map_err(|_| "show path: expected a state number".to_string())?,
                        );
                        (display, state)
                    }
                    other => {
                        return Err(format!(
                            "show: expected `frontier states`, `most general states`, or `path`, found {other:?}"
                        ));
                    }
                };
                self.eat_dot()?;
                TopItem::Command(Command::ShowNarrowing { display, state })
            }
            "srewrite" | "srew" | "dsrewrite" | "dsrew" => {
                let depth_first = txt.starts_with('d');
                self.advance();
                let module = self.opt_in_module()?;
                let term = self.collect_until(&["using"]);
                self.eat("using")?;
                let strategy = self.strategy()?;
                self.eat_dot()?;
                TopItem::Command(Command::Srewrite {
                    module,
                    depth_first,
                    term,
                    strategy,
                })
            }
            "reduce" | "red" => {
                self.advance();
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Reduce { module, term })
            }
            "check" => {
                self.advance();
                let module = self.opt_in_module()?;
                let term = self.collect_to_dot();
                self.eat_dot()?;
                TopItem::Command(Command::Check { module, term })
            }
            "get" => {
                self.advance();
                let irredundant = if self.at("irredundant") {
                    self.advance();
                    true
                } else {
                    false
                };
                self.eat("variants")?;
                let bound = self.opt_bound()?;
                let module = self.opt_in_module()?;
                let mut term = self.collect_until(&[]);
                self.eat_dot()?;
                let blockers = peel_irreducible_suffix(&mut term, self.i)?;
                TopItem::Command(Command::GetVariants {
                    module,
                    bound,
                    irredundant,
                    term,
                    blockers,
                })
            }
            "variant" | "filtered" => {
                let filtered = txt == "filtered";
                self.advance();
                if filtered {
                    self.eat("variant")?;
                }
                match self.peek_text() {
                    Some("unify") => {
                        self.advance();
                        let bound = self.opt_bound()?;
                        let module = self.opt_in_module()?;
                        let mut body = self.collect_until(&[]);
                        self.eat_dot()?;
                        let blockers = peel_irreducible_suffix(&mut body, self.i)?;
                        TopItem::Command(Command::VariantUnify {
                            module,
                            bound,
                            filtered,
                            body,
                            blockers,
                        })
                    }
                    Some("match") if !filtered => {
                        self.advance();
                        let bound = self.opt_bound()?;
                        let module = self.opt_in_module()?;
                        let pattern = self.collect_until(&["<=?"]);
                        self.eat("<=?")?;
                        let mut subject = self.collect_until(&[]);
                        self.eat_dot()?;
                        let blockers = peel_irreducible_suffix(&mut subject, self.i)?;
                        TopItem::Command(Command::VariantMatch {
                            module,
                            bound,
                            pattern,
                            subject,
                            blockers,
                        })
                    }
                    other => {
                        return Err(format!(
                            "expected `unify` or `match` after `variant`, found {other:?}"
                        ));
                    }
                }
            }
            "match" | "xmatch" => {
                let xmatch = txt == "xmatch";
                self.advance();
                let module = self.opt_in_module()?;
                let pattern = self.collect_until(&["<=?"]);
                self.eat("<=?")?;
                let subject = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Match {
                    module,
                    pattern,
                    subject,
                    xmatch,
                })
            }
            "unify" | "irredundant" | "irred" => {
                // `[irredundant] unify [[n]] [in M :] T1 =? T2 [/\ …] .`. The body (the
                // `=?`/`/\`-separated bubble) is collected whole and split by the command builder,
                // reusing the condition machinery (`=?` and `/\` each lex as a single token).
                let irredundant = txt != "unify";
                self.advance(); // `unify` / `irredundant` / `irred`
                if irredundant {
                    self.eat("unify")?;
                }
                let bound = self.opt_bound()?;
                let module = self.opt_in_module()?;
                let body = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Unify {
                    module,
                    bound,
                    irredundant,
                    body,
                })
            }
            "rewrite" | "rew" => {
                self.advance();
                let bound = self.opt_bound()?;
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Rewrite {
                    module,
                    bound,
                    term,
                })
            }
            "frewrite" | "frew" => {
                // `frewrite [n]` (rewrite bound) or `frewrite [n, g]` (bound + gas). The two-number form
                // reuses the search-style `[n, m]` parse: `(bound, gas)` (fable-audit.md §3.4 — the gas was
                // stuck at the default 1).
                self.advance();
                let (bound, gas) = self.opt_search_bound()?;
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Frewrite {
                    module,
                    bound,
                    gas,
                    term,
                })
            }
            "erewrite" | "erew" => {
                // `erewrite [n]` (delivery bound) or `erewrite [n, g]` (bound + gas). The two-number form
                // reuses the search-style `[n, m]` parse: `(bound, gas)`.
                self.advance();
                let (bound, gas) = self.opt_search_bound()?;
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::ERewrite {
                    module,
                    bound,
                    gas,
                    term,
                })
            }
            "search" => {
                self.advance();
                let (max_solutions, max_depth) = self.opt_search_bound()?;
                let module = self.opt_in_module()?;
                // The arrows `=>1`/`=>+`/`=>*`/`=>!` lex as single tokens (runs of non-punctuation).
                let subject = self.collect_until(&["=>1", "=>+", "=>*", "=>!"]);
                let arrow = match self.peek_text() {
                    Some("=>1") => SearchArrow::One,
                    Some("=>+") => SearchArrow::Plus,
                    Some("=>*") => SearchArrow::Star,
                    Some("=>!") => SearchArrow::Bang,
                    other => {
                        return Err(format!(
                            "search: expected `=>1`/`=>+`/`=>*`/`=>!`, found {other:?}"
                        ));
                    }
                };
                self.advance(); // the arrow
                let pattern = self.collect_until(&["such"]);
                let such_that = if self.at("such") {
                    self.advance();
                    self.eat("that")?;
                    Some(self.collect_until(&[]))
                } else {
                    None
                };
                self.eat_dot()?;
                TopItem::Command(Command::Search {
                    module,
                    max_solutions,
                    max_depth,
                    subject,
                    arrow,
                    pattern,
                    such_that,
                })
            }
            "smt-search" => {
                self.advance();
                let (max_solutions, max_depth) = self.opt_search_bound()?;
                let module = self.opt_in_module()?;
                // The arrows `=>1`/`=>+`/`=>*`/`=>!` lex as single tokens (runs of non-punctuation).
                let subject = self.collect_until(&["=>1", "=>+", "=>*", "=>!"]);
                let arrow = match self.peek_text() {
                    Some("=>1") => SearchArrow::One,
                    Some("=>+") => SearchArrow::Plus,
                    Some("=>*") => SearchArrow::Star,
                    Some("=>!") => SearchArrow::Bang,
                    other => {
                        return Err(format!(
                            "smt-search: expected `=>1`/`=>+`/`=>*`/`=>!`, found {other:?}"
                        ));
                    }
                };
                self.advance(); // the arrow
                let pattern = self.collect_until(&["such"]);
                let such_that = if self.at("such") {
                    self.advance();
                    self.eat("that")?;
                    Some(self.collect_until(&[]))
                } else {
                    None
                };
                self.eat_dot()?;
                TopItem::Command(Command::SmtSearch {
                    module,
                    max_solutions,
                    max_depth,
                    subject,
                    arrow,
                    pattern,
                    such_that,
                })
            }
            "continue" | "cont" => {
                // `continue n .` takes a **bare** number (unlike `rewrite [n]`'s bracketed bound); an
                // omitted bound continues unbounded to the next normal form / solution.
                self.advance();
                let bound = if self.at_dot() {
                    None
                } else {
                    Some(
                        self.name()?
                            .parse::<u64>()
                            .map_err(|_| "expected a number after `continue`".to_string())?,
                    )
                };
                self.eat_dot()?;
                TopItem::Command(Command::Continue { bound })
            }
            "set" => {
                // An interpreter directive, e.g. `set include BOOL off .` (prelude:31). A no-op for
                // us: we never auto-import a module (every import is explicit in the source), and
                // interactive `set` (e.g. `set trace on`) is intercepted by the REPL before the
                // parser runs. Consume through the `.` and parse the next item.
                self.advance(); // `set`
                while !self.at_dot() && self.peek_text().is_some() {
                    self.advance();
                }
                self.eat_dot()?;
                return self.parse_top_item();
            }
            _ => {
                // Top-level junk: Maude warns "unexpected token" and skips it token-by-token, then
                // continues (fable-audit.md §3.4) — a run of junk (`junkalpha junkbeta …`) is consumed and
                // the next real construct (a module / command) still parses. Skip this token and retry; the
                // per-token warning is phase-E diagnostics, so the skip is silent here.
                self.advance();
                return self.parse_top_item();
            }
        };
        Ok(Some(item))
    }

    pub fn parse_source(&mut self) -> PResult<Source> {
        let mut src = Source::default();
        while let Some(item) = self.parse_top_item()? {
            match item {
                TopItem::Module(m) => src.modules.push(m),
                TopItem::View(v) => src.views.push(v),
                // A command runs against the most recently entered module (Maude's current module).
                TopItem::Command(c) => {
                    let m = src
                        .modules
                        .len()
                        .checked_sub(1)
                        .ok_or("command before any module")?;
                    src.commands.push((m, c));
                }
            }
        }
        Ok(src)
    }

    fn module(&mut self) -> PResult<PreModule> {
        // System (`mod`/`th`) allows rules; functional (`fmod`/`fth`) rejects them (in `decl`). `fth`/`th`
        // are theories (the `is_theory` axis — a view source / parameter bound, statements not executed).
        let kw = self.peek_text().unwrap_or("");
        // A strategy module/theory (`smod`/`sth`) and an object module/theory (`omod`/`oth`) are both
        // system modules (rules allowed); `smod`/`sth` additionally permit `strat`/`sd`, `omod`/`oth`
        // additionally permit `class`/`subclass`/`msg`. A `th`/`sth`/`oth` is a theory.
        let kind = if matches!(kw, "mod" | "th" | "smod" | "sth" | "omod" | "oth") {
            ModuleKind::System
        } else {
            ModuleKind::Functional
        };
        let is_theory = matches!(kw, "fth" | "th" | "sth" | "oth");
        let is_strategy = matches!(kw, "smod" | "sth");
        let is_object = matches!(kw, "omod" | "oth");
        self.advance(); // fmod / mod / fth / th / smod / sth / omod / oth
        let name = self.name()?;
        // Optional formal parameters `{X :: T, …}` (B-iii). The stored name stays the bare base.
        let params = if self.at("{") {
            self.param_list()?
        } else {
            Vec::new()
        };
        self.eat("is")?;
        let mut m = PreModule {
            name,
            kind,
            is_theory,
            is_strategy,
            is_object,
            params,
            imports: Vec::new(),
            sorts: Vec::new(),
            subsorts: Vec::new(),
            ops: Vec::new(),
            vars: Vec::new(),
            statements: Vec::new(),
            strat_decls: Vec::new(),
            strat_defs: Vec::new(),
        };
        // An object module auto-imports `CONFIGURATION` (Maude's `set oo include CONFIGURATION on`),
        // supplying the object constructor `<_:_|_>`, `Cid`/`Attribute`/`AttributeSet`, and the soup `__`.
        // Applied first (Maude adds oo-includes ahead of the user's imports); the built-in `CONFIGURATION`
        // is injected into the module DB on demand (`tnk_modules::prelude`). Modes don't affect flattening.
        if is_object {
            m.imports.push(Import {
                mode: ImportMode::Including,
                expr: ModuleExpr::Named("CONFIGURATION".to_string()),
            });
        }
        while !self.at_module_end() {
            self.decl(&mut m)?;
        }
        self.advance(); // endfm / endm / endfth / endth / endom / endoth
        Ok(m)
    }

    /// At a module/theory closing keyword (`endfm`/`endm`/`endfth`/`endth`).
    fn at_module_end(&self) -> bool {
        matches!(
            self.peek_text(),
            Some("endfm" | "endm" | "endfth" | "endth" | "endsm" | "endsth" | "endom" | "endoth")
        )
    }

    /// A formal parameter list `{X :: T, Y :: T', …}` (B-iii). `::` lexes as one token (`:` is not
    /// splitting punctuation). The theory is a plain named theory.
    fn param_list(&mut self) -> PResult<Vec<Parameter>> {
        self.eat("{")?;
        let mut params = Vec::new();
        loop {
            let name = self.name()?;
            self.eat("::")?;
            let theory = self.name()?;
            params.push(Parameter { name, theory });
            if self.at(",") {
                self.advance();
            } else {
                break;
            }
        }
        self.eat("}")?;
        Ok(params)
    }

    /// A sort name, possibly **structured** (B-iii): a base identifier optionally followed by `{ … }` of
    /// comma-separated sort-name arguments — `Pair{X}`, `Map{X,Y}`, `List{List{X}}`. Reassembled into the
    /// canonical no-space spelling Maude uses internally (`List{X}`), which then flows through `build_sig`
    /// as an ordinary sort name string. A parameter sort `X$Elt` is already one token (`$` is not splitting
    /// punctuation), so it needs no special handling. (A kind `[…]` sort is a follow-up.)
    fn sort_name(&mut self) -> PResult<String> {
        if self.at("[") {
            // A **kind** sort `[S]` — the top (error) sort of S's connected component (`var B : [Bool]`,
            // `op undefined : -> [Y$Elt]`). The multi-sort form `[A, B]` names the kind of the component
            // that contains A and B (`kindNameDecember2022`; the sorts must share one component). `build_sig`
            // resolves the canonical `[A,B]` spelling to `error_sort(kind_of(·))`. Each inner is a full sort
            // name (so `[List{Nat}]` nests; the `,` inside `{ … }` is consumed by the inner parse).
            self.advance(); // [
            let mut inners = vec![self.sort_name()?];
            while self.at(",") {
                self.advance();
                inners.push(self.sort_name()?);
            }
            self.eat("]")?;
            return Ok(format!("[{}]", inners.join(",")));
        }
        let mut name = self.name()?;
        // A `.` inside a sort name is illegal (Maude: `A.B is not a valid sort name`). The lexer glues a
        // non-terminator dot into the maudeId, so a dotted sort like `A.B` arrives as one token here; a
        // legitimate structured/kind sort never has a `.` in its base identifier (it uses `{}`/`[]`). This
        // rejects the whole declaration (bail-on-first-error), matching Maude's "module unusable" recovery
        // (fable-audit.md §3.6, C4d).
        if name.contains('.') {
            return Err(format!(
                "`{name}` is not a valid sort name (`.` not allowed)"
            ));
        }
        // A *chain* of `{ … }` groups, not just one: a nested instantiation's renaming names the inner
        // structured sort `NeList{STRICT-WEAK-ORDER}{X}` (Axis-A5), and `List{List{X}}` nests via the
        // recursive arg parse. Reassembled into Maude's canonical no-space spelling.
        while self.at("{") {
            self.advance(); // {
            let mut args = Vec::new();
            loop {
                args.push(self.sort_name()?);
                if self.at(",") {
                    self.advance();
                } else {
                    break;
                }
            }
            self.eat("}")?;
            name = format!("{name}{{{}}}", args.join(","));
        }
        Ok(name)
    }

    /// A view definition `view V [{X :: T, …}] from <expr> to <expr> is <maps> endv` (B-ii / Axis-A2). An
    /// optional parameter list after the name makes it a *parameterized* view (`view V{X :: T} … to M{X}`),
    /// only used by a nested instantiation. `from`/`to` are module expressions. Maps: `sort A to B .`,
    /// `op f to g .`, `op f : A -> B to g .`, and `op f to term t .`.
    fn view(&mut self) -> PResult<ViewDecl> {
        self.eat("view")?;
        let name = self.name()?;
        let params = if self.at("{") {
            self.param_list()?
        } else {
            Vec::new()
        };
        // `module_expr` parses an atom/`*`/`+` chain and stops at the first other token (it does not
        // consume a terminator), so it ends naturally at `to` / `is`.
        self.eat("from")?;
        let from = self.module_expr()?;
        self.eat("to")?;
        let to = self.module_expr()?;
        self.eat("is")?;

        let mut sort_maps = Vec::new();
        let mut op_maps = Vec::new();
        let mut vars = Vec::new();
        while !self.at("endv") {
            match self.peek_text().ok_or("unexpected end of input in view")? {
                "sort" => {
                    self.advance();
                    // Targets may be structured sorts in a parameterized view (`sort Elt to Box{X}`).
                    let from_s = self.sort_name()?;
                    self.eat("to")?;
                    let to_s = self.sort_name()?;
                    self.eat_dot()?;
                    sort_maps.push((from_s, to_s));
                }
                "var" | "vars" => {
                    self.advance();
                    let mut names = Vec::new();
                    while !self.at(":") {
                        names.push(self.name()?);
                    }
                    self.eat(":")?;
                    let sort = self.sort_name()?;
                    self.eat_dot()?;
                    vars.push(VarDecl { names, sort });
                }
                "op" => {
                    self.advance();
                    // A signature selector has a top-level arrow before the map's top-level `to`.
                    // Colons inside an op→term source pattern (`f(A:Elt)`) are therefore not mistaken for
                    // the selector delimiter.
                    let mut depth = 0i32;
                    let mut signature_colon = None;
                    let mut has_signature_arrow = false;
                    for position in self.pos..self.toks.len() {
                        match self.i.resolve(self.toks[position].sym) {
                            "(" => depth += 1,
                            ")" => depth -= 1,
                            "to" if depth == 0 => break,
                            ":" if depth == 0 => signature_colon = Some(position),
                            "->" | "~>" if depth == 0 => {
                                has_signature_arrow = true;
                                break;
                            }
                            _ => {}
                        }
                    }
                    let (from, dom_range) = if has_signature_arrow {
                        let delimiter =
                            signature_colon.ok_or("disambiguated view op map is missing `:`")?;
                        let from = self.toks[self.pos..delimiter].to_vec();
                        self.pos = delimiter + 1;
                        let mut domain = Vec::new();
                        while !self.at("->") && !self.at("~>") {
                            domain.push(self.sort_name()?);
                        }
                        self.advance();
                        let range = self.sort_name()?;
                        (from, Some((domain, range)))
                    } else {
                        (self.collect_until(&["to"]), None)
                    };
                    self.eat("to")?;
                    if self.at("term") {
                        self.advance();
                        let term = self.collect_until(&[]);
                        self.eat_dot()?;
                        op_maps.push(OpMap::Term {
                            from,
                            to: term,
                            dom_range,
                        });
                    } else {
                        let to = self.collect_until(&[]);
                        self.eat_dot()?;
                        op_maps.push(OpMap::Op {
                            from,
                            to,
                            dom_range,
                        });
                    }
                }
                "class" => {
                    self.advance();
                    let from_start = self.pos;
                    let from_s = self.sort_name()?;
                    let from = self.toks[from_start..self.pos].to_vec();
                    self.eat("to")?;
                    let to_start = self.pos;
                    let to_s = self.sort_name()?;
                    let to = self.toks[to_start..self.pos].to_vec();
                    self.eat_dot()?;
                    // OO class maps are the sort map plus the honorary class-constant operator map
                    // created by `desugar_class`.
                    sort_maps.push((from_s, to_s));
                    op_maps.push(OpMap::Op {
                        from,
                        to,
                        dom_range: None,
                    });
                }
                "attr" => {
                    self.advance();
                    let from_token = self.peek().ok_or("expected an attribute name")?;
                    let from_name = self.name()?;
                    if self.at_dot() {
                        self.eat_dot()?;
                        let _class = self.sort_name()?;
                    }
                    self.eat("to")?;
                    let to_token = self.peek().ok_or("expected a target attribute name")?;
                    let to_name = self.name()?;
                    self.eat_dot()?;
                    if from_name.contains('_') || to_name.contains('_') {
                        return Err("underscore not allowed in an attribute name".into());
                    }
                    let mut from = vec![from_token];
                    from.extend(self.attribute_suffix(from_token.line));
                    let mut to = vec![to_token];
                    to.extend(self.attribute_suffix(to_token.line));
                    op_maps.push(OpMap::Op {
                        from,
                        to,
                        dom_range: None,
                    });
                }
                "msg" => {
                    self.advance();
                    let body = self.collect_until(&[]);
                    self.eat_dot()?;
                    let split = body
                        .windows(2)
                        .position(|pair| {
                            self.i.resolve(pair[0].sym) == "to"
                                && self.i.resolve(pair[1].sym) == "term"
                        })
                        .ok_or("message view map must use `msg … to term …`")?;
                    let from = body[..split].to_vec();
                    let to = body[split + 2..].to_vec();
                    if from.is_empty() || to.is_empty() {
                        return Err("message view map has an empty source or target term".into());
                    }
                    op_maps.push(OpMap::Term {
                        from,
                        to,
                        dom_range: None,
                    });
                }
                other => {
                    return Err(format!(
                        "view map must be `sort … to …`, `op … to …`, `class … to …`, \
                         `attr … to …`, `msg … to term …`, or a variable declaration, found `{other}`"
                    ));
                }
            }
        }
        self.advance(); // endv
        Ok(ViewDecl {
            name,
            params,
            from,
            to,
            vars,
            sort_maps,
            op_maps,
        })
    }

    fn decl(&mut self, m: &mut PreModule) -> PResult<()> {
        let kw = self
            .peek_text()
            .ok_or("unexpected end of input in module")?;
        match kw {
            "protecting" | "pr" | "extending" | "ex" | "including" | "inc" => {
                let mode = match kw {
                    "protecting" | "pr" => ImportMode::Protecting,
                    "extending" | "ex" => ImportMode::Extending,
                    _ => ImportMode::Including,
                };
                self.advance();
                let expr = self.module_expr()?;
                self.eat_dot()?;
                m.imports.push(Import { mode, expr });
            }
            // `generated-by <module-expr> .` — a stricter `protecting` (the imported sorts are asserted to
            // be generated by the import's constructors). The mode does not affect flattening, so it is
            // treated as `protecting`; accepted silently (fable-audit.md §3.4).
            "generated-by" => {
                self.advance();
                let expr = self.module_expr()?;
                self.eat_dot()?;
                m.imports.push(Import {
                    mode: ImportMode::Protecting,
                    expr,
                });
            }
            "sort" | "sorts" => {
                self.advance();
                while !self.at_dot() {
                    m.sorts.push(self.sort_name()?);
                }
                self.eat_dot()?;
            }
            "subsort" | "subsorts" => {
                self.advance();
                // groups of sort names separated by `<`, e.g. `A B < C < D` (sorts may be structured).
                let mut chain = vec![Vec::new()];
                while !self.at_dot() {
                    if self.at("<") {
                        self.advance();
                        chain.push(Vec::new());
                    } else {
                        chain.last_mut().unwrap().push(self.sort_name()?);
                    }
                }
                self.eat_dot()?;
                m.subsorts.push(chain);
            }
            "op" | "ops" => {
                let multi = kw == "ops";
                self.advance();
                let names = self.op_names_before_signature()?;
                let mut domain = Vec::new();
                while !self.at("->") && !self.at("~>") {
                    domain.push(self.sort_name()?);
                }
                // `~>` is the partial (kind-level) arrow: all domain/range sorts are lifted to their kinds
                // by signature construction (recorded here so the compiled declaration preserves it).
                let partial = self.at("~>");
                if partial {
                    self.advance();
                } else {
                    self.eat("->")?;
                }
                let range = self.sort_name()?;
                let attrs = if self.at("[") {
                    self.attrs()?
                } else {
                    Attrs::default()
                };
                self.eat_dot()?;
                if multi {
                    for t in names {
                        m.ops.push(OpDecl {
                            name: vec![t],
                            domain: domain.clone(),
                            range: range.clone(),
                            partial,
                            attrs: attrs.clone_shallow(),
                        });
                    }
                } else {
                    m.ops.push(OpDecl {
                        name: names,
                        domain,
                        range,
                        partial,
                        attrs,
                    });
                }
            }
            "var" | "vars" => {
                self.advance();
                let mut names = Vec::new();
                while !self.at(":") {
                    names.push(self.name()?);
                }
                self.eat(":")?;
                let sort = self.sort_name()?;
                self.eat_dot()?;
                m.vars.push(VarDecl { names, sort });
            }
            // Object-module surface (`omod`, Pillar 2.5-E). `class`/`subclass`/`msg` are **desugared here**
            // into ordinary sorts/subsorts/ops (Maude's `ooProcess.cc`), so the rest of the pipeline needs
            // no object-module awareness — only the `is_object` flag (for the pattern-completion transform)
            // and the auto-imported `CONFIGURATION` (for `Cid`/`Attribute`/`AttributeSet`/`<_:_|_>`/`__`).
            "class" | "classes" => {
                if !m.is_object {
                    return Err(format!(
                        "`{kw}` is only allowed in an object module (`omod {}`)",
                        m.name
                    ));
                }
                self.advance();
                // `class C [| a1 : S1, a2 : S2] .` — a possibly structured class name, then an optional
                // `|`-separated list of `attr : sort` pairs. `C` becomes a sort `C`, a subsort `C < Cid`,
                // and an honorary class *constant* `op C : -> C [ctor]`; each attribute `a : S` becomes
                // `op a`:_ : S -> Attribute [ctor gather (&)]` (the `a :_` mixfix form).
                let class_start = self.pos;
                let cname = self.sort_name()?;
                let ctoks = self.toks[class_start..self.pos].to_vec();
                // A class name becomes a sort *and* a same-named constant operator; an underscore would
                // make that operator a mixfix form with a hole (Maude rejects it — `ooProcess.cc`).
                if cname.contains('_') {
                    return Err(format!("underscore not allowed in class name `{cname}`"));
                }
                self.desugar_class(m, ctoks, &cname);
                if self.at("|") {
                    self.advance();
                    loop {
                        let atok = self.peek().ok_or("expected an attribute name")?;
                        let aname = self.name()?;
                        // The attribute op name is `a` + `` `:_ ``; an underscore in `a` would corrupt it.
                        if aname.contains('_') {
                            return Err(format!(
                                "underscore not allowed in attribute name `{aname}`"
                            ));
                        }
                        self.eat(":")?;
                        let asort = self.sort_name()?;
                        self.desugar_attribute(m, atok, asort);
                        if self.at(",") {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                self.eat_dot()?;
            }
            "subclass" | "subclasses" => {
                if !m.is_object {
                    return Err(format!(
                        "`{kw}` is only allowed in an object module (`omod {}`)",
                        m.name
                    ));
                }
                self.advance();
                // `subclass A B < C < D .` is a subsort relation between class sorts — desugar to a subsort
                // chain, parsed exactly like `subsort`.
                let mut chain = vec![Vec::new()];
                while !self.at_dot() {
                    if self.at("<") {
                        self.advance();
                        chain.push(Vec::new());
                    } else {
                        chain.last_mut().unwrap().push(self.sort_name()?);
                    }
                }
                self.eat_dot()?;
                m.subsorts.push(chain);
            }
            "msg" | "msgs" => {
                if !m.is_object {
                    return Err(format!(
                        "`{kw}` is only allowed in an object module (`omod {}`)",
                        m.name
                    ));
                }
                let multi = kw == "msgs";
                self.advance();
                // `msg m : S1 S2 -> Msg .` desugars to `op m : S1 S2 -> Msg [ctor msg]` (Maude's `endMsg`
                // sets `MESSAGE | CTOR`); the range is whatever the user writes (`Msg` by convention).
                let names = self.op_names_before_signature()?;
                let mut domain = Vec::new();
                while !self.at("->") && !self.at("~>") {
                    domain.push(self.sort_name()?);
                }
                self.eat("->")?;
                let range = self.sort_name()?;
                let mut attrs = if self.at("[") {
                    self.attrs()?
                } else {
                    Attrs::default()
                };
                attrs.ctor = true;
                attrs.message = true;
                self.eat_dot()?;
                if multi {
                    for t in names {
                        m.ops.push(OpDecl {
                            name: vec![t],
                            domain: domain.clone(),
                            range: range.clone(),
                            partial: false,
                            attrs: attrs.clone_shallow(),
                        });
                    }
                } else {
                    m.ops.push(OpDecl {
                        name: names,
                        domain,
                        range,
                        partial: false,
                        attrs,
                    });
                }
            }
            "eq" | "ceq" => {
                let conditional = kw == "ceq";
                self.advance();
                // Optional leading `[name] :` label (Maude's labelled-equation syntax). Only a real
                // `[name] :` is peeled; a `[_]`-headed lhs (`eq [x] = y .`) leaves its `[` for the body.
                let leading = self.peel_leading_label()?;
                // Collect the whole statement body (depth-aware over `()[]{}`) and split it, rather than
                // streaming to the first `=`/`[`: a `[_]`-list term (`eq reverse([]) = [] .`) has top-level
                // brackets in the rhs. Peel a trailing `[attrs]` only when it really is attributes, then
                // let `equation_separator` distinguish the statement delimiter from `_=[_]_` on the lhs.
                let mut body = self.collect_to_dot();
                self.eat_dot()?;
                let sa = peel_stmt_attrs(&mut body, self.i);
                // A `[print …]` referencing a non-variable token is rejected by Maude, which DROPS the
                // statement and keeps the module (C4f). Drop it here (skip the push); the module survives.
                if !print_attr_ok(&sa.print, m, self.i) {
                    return Ok(());
                }
                let cond = if conditional {
                    let i = top_level_find(&body, self.i, "if", false)
                        .ok_or("`ceq` is missing its `if` condition")?;
                    let c = body.split_off(i + 1);
                    body.pop(); // the `if`
                    Some(c)
                } else {
                    None
                };
                let eq = equation_separator(&body, self.i).ok_or("equation is missing `=`")?;
                let rhs = body.split_off(eq + 1);
                body.pop(); // the `=`
                m.statements.push(Statement::Eq {
                    lhs: body,
                    rhs,
                    cond,
                    owise: sa.owise,
                    variant: sa.variant,
                    nonexec: sa.nonexec,
                    label: leading.or(sa.label),
                });
            }
            "mb" | "cmb" => {
                let conditional = kw == "cmb";
                self.advance();
                // Optional leading `[name] :` label, like `eq`/`rl` (fable-audit.md §3.4).
                let leading = self.peel_leading_label()?;
                let lhs = self.collect_until(&[":"]);
                self.eat(":")?;
                // The sort (and a condition) end at the optional trailing attribute `[ … ]` or `.` — stop
                // the bubble at `[` so a `[nonexec]`/`[label …]` is not swallowed into the sort.
                let sort;
                let cond;
                if conditional {
                    sort = self.collect_until(&["if"]);
                    self.eat("if")?;
                    cond = Some(self.collect_until(&["["]));
                } else {
                    sort = self.collect_until(&["["]);
                    cond = None;
                }
                let sa = self.stmt_attrs()?;
                self.eat_dot()?;
                if !print_attr_ok(&sa.print, m, self.i) {
                    return Ok(()); // bad `[print …]` variable: drop the statement, keep the module (C4f)
                }
                m.statements.push(Statement::Mb {
                    lhs,
                    sort,
                    cond,
                    nonexec: sa.nonexec,
                    label: leading.or(sa.label),
                });
            }
            "rl" | "crl" => {
                if m.kind == ModuleKind::Functional {
                    return Err(format!(
                        "rule `{kw}` is not allowed in a functional module (`fmod {}`); use `mod`",
                        m.name
                    ));
                }
                let conditional = kw == "crl";
                self.advance();
                // Optional leading label `[name] :` (Maude's labelled-rule syntax) — only a genuine
                // `[name] :`; a `[_]`-headed lhs (`rl [N] => [N + 1] .`) leaves its leading `[` for the
                // body (fable-audit.md §3.4).
                let label = self.peel_leading_label()?;
                // Collect the whole body depth-aware over `()[]{}` (like `eq`) so a `[_]`-headed lhs/rhs
                // (`[N + 1]`) is not truncated at its `[`, then peel a trailing `[attrs]` (real attributes
                // only, not a `[_]`-list term). Split at the **first** top-level `=>` (the rule arrow — a
                // rewrite-condition fragment's `=>` sits after `if`), then a `crl` at its top-level `if`.
                let mut body = self.collect_to_dot();
                self.eat_dot()?;
                let sa = peel_stmt_attrs(&mut body, self.i);
                if !print_attr_ok(&sa.print, m, self.i) {
                    return Ok(()); // bad `[print …]` variable: drop the statement, keep the module (C4f)
                }
                // The arrow `=>` lexes as one token (a run of non-punctuation chars); an unspaced `t=>p`
                // lexes as a single token and so will not split here — rejected exactly as Maude rejects it.
                let arrow =
                    top_level_find(&body, self.i, "=>", false).ok_or("rule is missing `=>`")?;
                let mut rest = body.split_off(arrow + 1);
                body.pop(); // the `=>`
                let lhs = body;
                let (rhs, cond);
                if conditional {
                    let ifi = top_level_find(&rest, self.i, "if", false)
                        .ok_or("`crl` is missing its `if` condition")?;
                    let c = rest.split_off(ifi + 1);
                    rest.pop(); // the `if`
                    rhs = rest;
                    cond = Some(c);
                } else {
                    rhs = rest;
                    cond = None;
                }
                // The label may be written either as the leading `[name] :` or as a trailing `[label name]`;
                // the leading form wins if both appear.
                m.statements.push(Statement::Rule {
                    label: label.or(sa.label),
                    lhs,
                    rhs,
                    cond,
                    nonexec: sa.nonexec,
                    narrowing: sa.narrowing,
                });
            }
            "strat" | "strats" => {
                if !m.is_strategy {
                    return Err(format!(
                        "strategy declaration `{kw}` is only allowed in a strategy module (`smod {}`)",
                        m.name
                    ));
                }
                self.advance();
                // `strat[s] n1 … : <domain sorts> @ Sort .`; Maude omits the colon when the
                // strategy has no call parameters (`strats n1 n2 @ Sort .`).
                let mut names = Vec::new();
                while !self.at(":") && !self.at("@") {
                    names.push(self.name()?);
                }
                let mut domain = Vec::new();
                if self.at(":") {
                    self.advance();
                    while !self.at("@") {
                        domain.push(self.sort_name()?);
                    }
                }
                self.eat("@")?;
                let subject = self.sort_name()?;
                self.eat_dot()?;
                for name in names {
                    m.strat_decls.push(StratDecl {
                        name,
                        domain: domain.clone(),
                        subject: subject.clone(),
                        origin: None,
                        source_index: None,
                        home: None,
                    });
                }
            }
            "sd" | "csd" => {
                if !m.is_strategy {
                    return Err(format!(
                        "strategy definition `{kw}` is only allowed in a strategy module (`smod {}`)",
                        m.name
                    ));
                }
                let conditional = kw == "csd";
                self.advance();
                let name = self.name()?;
                // Optional call parameters `name(p1, …)` — raw bubbles, split at top-level commas.
                let params = if self.at("(") {
                    self.paren_arg_bubbles()?
                } else {
                    Vec::new()
                };
                self.eat(":=")?;
                let body = self.strategy()?;
                let cond = if conditional {
                    self.eat("if")?;
                    Some(self.collect_until(&[]))
                } else {
                    None
                };
                self.eat_dot()?;
                m.strat_defs.push(StratDef {
                    name,
                    params,
                    body,
                    cond,
                    origin: None,
                    source_index: None,
                    home: None,
                });
            }
            other => return Err(format!("unsupported declaration `{other}`")),
        }
        Ok(())
    }

    // ---- strategy expressions (Pillar 2.4) ----

    /// Parse a strategy expression (precedence low→high: `|` < `;` < `? :` < postfix `* + !` < atom). Term-
    /// carrying parts (test/matchrew patterns + conditions, application substitutions, call arguments) are
    /// left as raw token bubbles, parsed against the module grammar at execution time.
    fn strategy(&mut self) -> PResult<StratExpr> {
        let mut e = self.strat_branch()?;
        while self.at("|") {
            self.advance();
            let rhs = self.strat_branch()?;
            e = StratExpr::Union(Box::new(e), Box::new(rhs));
        }
        Ok(e)
    }

    fn strat_branch(&mut self) -> PResult<StratExpr> {
        let e = self.strat_seq()?;
        if self.at("?") {
            self.advance();
            let success = self.strategy()?;
            self.eat(":")?;
            let failure = self.strat_branch()?;
            return Ok(StratExpr::Branch {
                test: Box::new(e),
                success: Box::new(success),
                failure: Box::new(failure),
            });
        }
        Ok(e)
    }

    fn strat_seq(&mut self) -> PResult<StratExpr> {
        let mut e = self.strat_postfix()?;
        while self.at(";") {
            self.advance();
            let rhs = self.strat_postfix()?;
            e = StratExpr::Seq(Box::new(e), Box::new(rhs));
        }
        Ok(e)
    }

    fn strat_postfix(&mut self) -> PResult<StratExpr> {
        let mut e = self.strat_atom()?;
        loop {
            e = match self.peek_text() {
                Some("*") => StratExpr::Star(Box::new(e)),
                Some("+") => StratExpr::Plus(Box::new(e)),
                Some("!") => StratExpr::Normalize(Box::new(e)),
                _ => break,
            };
            self.advance();
        }
        Ok(e)
    }

    fn strat_atom(&mut self) -> PResult<StratExpr> {
        let txt = self.peek_text().ok_or("expected a strategy")?;
        Ok(match txt {
            "idle" => {
                self.advance();
                StratExpr::Idle
            }
            "fail" => {
                self.advance();
                StratExpr::Fail
            }
            "all" => {
                self.advance();
                StratExpr::All
            }
            "(" => {
                self.advance();
                let e = self.strategy()?;
                self.eat(")")?;
                e
            }
            "top" | "one" => {
                self.advance();
                self.eat("(")?;
                let e = Box::new(self.strategy()?);
                self.eat(")")?;
                if txt == "top" {
                    StratExpr::Top(e)
                } else {
                    StratExpr::One(e)
                }
            }
            // Derived branch forms — kept in surface spelling (echo fidelity); resolution desugars.
            "try" | "not" | "test" => {
                self.advance();
                self.eat("(")?;
                let e = self.strategy()?;
                self.eat(")")?;
                let kind = match txt {
                    "not" => StratSugar::NotS,
                    "test" => StratSugar::TestS,
                    _ => StratSugar::Try,
                };
                StratExpr::Sugar {
                    kind,
                    args: vec![e],
                }
            }
            "or-else" => {
                self.advance();
                self.eat("(")?;
                let a = self.strategy()?;
                self.eat(",")?;
                let b = self.strategy()?;
                self.eat(")")?;
                StratExpr::Sugar {
                    kind: StratSugar::OrElse,
                    args: vec![a, b],
                }
            }
            "match" | "xmatch" | "amatch" => {
                self.advance();
                let kind = Self::test_kind(txt);
                let (pattern, cond) = self.strat_pattern_cond()?;
                StratExpr::Test {
                    kind,
                    pattern,
                    cond,
                }
            }
            "matchrew" | "xmatchrew" | "amatchrew" => {
                self.advance();
                let kind = match txt {
                    "xmatchrew" => TestKind::XMatch,
                    "amatchrew" => TestKind::AMatch,
                    _ => TestKind::Match,
                };
                let (pattern, cond) = self.matchrew_pattern_cond()?;
                self.eat("by")?;
                let mut subs = Vec::new();
                loop {
                    let var = self.collect_until(&["using"]);
                    self.eat("using")?;
                    let e = self.strategy()?;
                    subs.push((var, e));
                    if self.at(",") {
                        self.advance();
                    } else {
                        break;
                    }
                }
                StratExpr::MatchRew {
                    kind,
                    pattern,
                    cond,
                    subs,
                }
            }
            // A rule application `label[σ]{strats}` or a strategy call `name(args)` / bare `name`.
            _ => {
                let name = self.name()?;
                if self.at("(") {
                    StratExpr::Call {
                        name,
                        args: self.paren_arg_bubbles()?,
                    }
                } else {
                    let subst = if self.at("[") {
                        self.strat_subst()?
                    } else {
                        Vec::new()
                    };
                    let substrats = if self.at("{") {
                        self.strat_brace_strats()?
                    } else {
                        Vec::new()
                    };
                    StratExpr::Apply {
                        label: name,
                        subst,
                        substrats,
                    }
                }
            }
        })
    }

    fn test_kind(txt: &str) -> TestKind {
        match txt {
            "xmatch" => TestKind::XMatch,
            "amatch" => TestKind::AMatch,
            _ => TestKind::Match,
        }
    }

    /// A test pattern up to a strategy delimiter, plus an optional `such that <cond>`.
    fn strat_pattern_cond(&mut self) -> PResult<(Vec<Token>, Option<Vec<Token>>)> {
        self.strat_pattern_cond_until(&[])
    }

    /// A `matchrew` pattern + optional `such that <cond>`, both delimited by the explicit `by` keyword.
    /// Unlike a bare `match`/`test` pattern, strategy operators (`|`, `;`, `?`, …) are **not** stops here:
    /// a bare `|` is the user's `_|_` term operator *inside* the pattern (fable-audit.md §3.4), not
    /// strategy union — the `by` (and `such that`) delimit the pattern, so the term wins.
    fn matchrew_pattern_cond(&mut self) -> PResult<(Vec<Token>, Option<Vec<Token>>)> {
        let pattern = self.collect_until(&["such", "by"]);
        let cond = if self.at("such") {
            self.advance();
            self.eat("that")?;
            Some(self.collect_until(&["by"]))
        } else {
            None
        };
        Ok((pattern, cond))
    }

    /// As [`strat_pattern_cond`](Self::strat_pattern_cond) but `extra` adds pattern/condition stop tokens
    /// (matchrew stops the pattern/condition at `by`).
    fn strat_pattern_cond_until(
        &mut self,
        extra: &[&str],
    ) -> PResult<(Vec<Token>, Option<Vec<Token>>)> {
        let mut stops = vec!["such", ";", "|", "?", ":", ")", ",", "*", "+", "!"];
        stops.extend_from_slice(extra);
        let pattern = self.collect_until(&stops);
        let cond = if self.at("such") {
            self.advance();
            self.eat("that")?;
            let mut cstops = vec![";", "|", "?", ":", ")", ",", "*", "+", "!"];
            cstops.extend_from_slice(extra);
            Some(self.collect_until(&cstops))
        } else {
            None
        };
        Ok((pattern, cond))
    }

    /// An application's initial substitution `[x1 <- t1, …]` — raw `(var, term)` bubbles.
    fn strat_subst(&mut self) -> PResult<Vec<(Vec<Token>, Vec<Token>)>> {
        self.eat("[")?;
        let mut subst = Vec::new();
        if !self.at("]") {
            loop {
                let var = self.collect_until(&["<-"]);
                self.eat("<-")?;
                let term = self.collect_until(&[",", "]"]);
                subst.push((var, term));
                if self.at(",") {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.eat("]")?;
        Ok(subst)
    }

    /// An application's rewrite-condition substrategies `{E1, …}`.
    fn strat_brace_strats(&mut self) -> PResult<Vec<StratExpr>> {
        self.eat("{")?;
        let mut strats = Vec::new();
        if !self.at("}") {
            loop {
                strats.push(self.strategy()?);
                if self.at(",") {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.eat("}")?;
        Ok(strats)
    }

    /// A parenthesized comma-separated list of raw argument bubbles `( a1, …, an )` (call args / `sd`
    /// parameters). The `(`-depth in [`collect_until`](Self::collect_until) keeps nested calls intact.
    fn paren_arg_bubbles(&mut self) -> PResult<Vec<Vec<Token>>> {
        self.eat("(")?;
        let mut args = Vec::new();
        if !self.at(")") {
            loop {
                args.push(self.collect_until(&[",", ")"]));
                if self.at(",") {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.eat(")")?;
        Ok(args)
    }

    // ---- module expressions (B5) ----

    /// A (non-parameterized) module expression: a summation of renamings of atoms. `*` (renaming) binds
    /// tighter than `+` (summation); both are left-associative. Parses up to the terminator `.`.
    fn module_expr(&mut self) -> PResult<ModuleExpr> {
        let mut e = self.module_rename()?;
        while self.at("+") {
            self.advance();
            let rhs = self.module_rename()?;
            e = ModuleExpr::Sum(Box::new(e), Box::new(rhs));
        }
        Ok(e)
    }

    /// `atom ('*' '(' renaming ')')*`.
    fn module_rename(&mut self) -> PResult<ModuleExpr> {
        let mut e = self.module_atom()?;
        while self.at("*") {
            self.advance();
            let items = self.renaming()?;
            e = ModuleExpr::Rename(Box::new(e), items);
        }
        Ok(e)
    }

    /// `(NAME | '(' module_expr ')') ('{' arg (',' arg)* '}')*`. Each `{…}` after the base is a parameterized
    /// instantiation `M{A, …}`; a *chain* `M{A}{B}` (Axis-A5 kind 1) re-instantiates the free parameters a
    /// theory-view argument leaves behind. A **parenthesized** base is itself instantiable —
    /// `(M * (renaming)){V}` instantiates a renamed parameterized module (finding C3a; stock `linear.maude`).
    fn module_atom(&mut self) -> PResult<ModuleExpr> {
        let mut e = if self.at("(") {
            self.advance();
            let inner = self.module_expr()?;
            self.eat(")")?;
            inner
        } else {
            ModuleExpr::Named(self.name()?)
        };
        while self.at("{") {
            e = ModuleExpr::Instantiation(Box::new(e), self.instantiation_args()?);
        }
        Ok(e)
    }

    /// The argument list of an instantiation `{A1, A2, …}` (Axis-A2/A5). Each argument is a full module
    /// expression: a view name (`Nat`), a nested instantiation (`BoxV{ToColor}`, `List{Nat}`), or a bare
    /// enclosing-parameter name (`X`). `flatten` classifies each contextually.
    fn instantiation_args(&mut self) -> PResult<Vec<ModuleExpr>> {
        self.eat("{")?;
        let mut args = Vec::new();
        loop {
            args.push(self.module_expr()?);
            if self.at(",") {
                self.advance();
            } else {
                break;
            }
        }
        self.eat("}")?;
        Ok(args)
    }

    /// A renaming `( sort A to B , op f to g , label l to m , … )`. An `op f : dom -> range to g` selects
    /// one overload by signature (arity-disambiguated). OO renaming items (`class`/`attr`/`msg to`) desugar
    /// to the sort/op maps the OO desugaring produces (`class C to D` ⇒ sort *and* class-constant rename).
    fn renaming(&mut self) -> PResult<Vec<RenameItem>> {
        self.eat("(")?;
        let mut items = Vec::new();
        loop {
            match self.name()?.as_str() {
                "sort" => {
                    // Structured sorts on both sides — a nested-instantiation renaming strips the inner
                    // label: `sort NeList{STRICT-WEAK-ORDER}{X} to NeList{X}`.
                    let from = self.sort_name()?;
                    self.eat("to")?;
                    let to = self.sort_name()?;
                    items.push(RenameItem::Sort { from, to });
                }
                "op" => items.push(self.op_rename_item()?),
                // `label l to m` — rename a statement label.
                "label" => {
                    let from = self.name()?;
                    self.eat("to")?;
                    let to = self.name()?;
                    items.push(RenameItem::Label { from, to });
                }
                // OO renaming items (fable-audit.md §3.4): desugar to the sort/op maps the omod desugaring
                // produced. A class is a sort *and* a same-named constant; an attribute `a` is the mixfix op
                // `a`:_`; a message is a prefix op.
                "class" => {
                    let from = self.name()?;
                    self.eat("to")?;
                    let to = self.name()?;
                    items.push(RenameItem::Sort {
                        from: from.clone(),
                        to: to.clone(),
                    });
                    items.push(RenameItem::Op {
                        from,
                        to,
                        dom_range: None,
                        attrs: Attrs::default(),
                    });
                }
                "attr" => {
                    // `attr a [. C] to b`: the attribute op is `a`:_` (range `Attribute`); the optional
                    // `. C` class qualifier (Maude's disambiguator) is parsed and ignored (a single
                    // attribute name is unambiguous in these specs).
                    let from = self.name()?;
                    if self.at_dot() {
                        self.eat_dot()?;
                        let _class = self.name()?;
                    }
                    self.eat("to")?;
                    let to = self.name()?;
                    items.push(RenameItem::Op {
                        from: format!("{from}:_"),
                        to: format!("{to}:_"),
                        dom_range: None,
                        attrs: Attrs::default(),
                    });
                }
                "msg" => {
                    let from = self.name()?;
                    self.eat("to")?;
                    let to = self.name()?;
                    items.push(RenameItem::Op {
                        from,
                        to,
                        dom_range: None,
                        attrs: Attrs::default(),
                    });
                }
                other => {
                    return Err(format!(
                        "renaming item must start with `sort`, `op`, `label`, `class`, `attr`, or `msg`, \
                         found `{other}`"
                    ));
                }
            }
            if self.at(",") {
                self.advance();
            } else {
                break;
            }
        }
        self.eat(")")?;
        Ok(items)
    }

    /// One `op … to …` renaming item. The from-name is a full mixfix name (may contain `,`, e.g. `_,_`):
    /// collect its tokens up to the standalone `to` keyword or the disambiguating `:`. An arity-disambiguated
    /// `op f : dom -> range to g` records the signature so only the matching overload is renamed.
    fn op_rename_item(&mut self) -> PResult<RenameItem> {
        let from_toks = self.collect_until(&["to", ":"]);
        let dom_range = if self.at(":") {
            self.advance(); // :
            let mut domain = Vec::new();
            while !self.at("->") && !self.at("~>") {
                domain.push(self.sort_name()?);
            }
            // `~>` (partial arrow) disambiguates the same as `->` — the range sort follows either.
            self.advance(); // -> / ~>
            let range = self.sort_name()?;
            Some((domain, range))
        } else {
            None
        };
        self.eat("to")?;
        // The to-name runs to the next item separator `,`, the attribute `[`, or `)`. A parenthesized
        // target `(_,_)` (grouping so a mixfix target reads unambiguously) has its outer parens stripped.
        let to_toks = self.collect_until(&[",", "[", ")"]);
        let attrs = if self.at("[") {
            self.attrs()?
        } else {
            Attrs::default()
        };
        let from: String = from_toks.iter().map(|t| self.i.resolve(t.sym)).collect();
        let mut to: String = to_toks.iter().map(|t| self.i.resolve(t.sym)).collect();
        if let Some(inner) = to.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            to = inner.to_string();
        }
        Ok(RenameItem::Op {
            from,
            to,
            dom_range,
            attrs,
        })
    }

    /// An optional leading `[name] :` statement label (Maude's labelled-statement syntax, valid on
    /// `eq`/`ceq`/`mb`/`cmb`/`rl`/`crl`). It fires **only** when the bracket group is `[` <one token> `]`
    /// immediately followed by `:` — otherwise the leading `[` heads a `[_]`-term LHS
    /// (`rl [N] => [N + 1] .`, `eq [x] = y .`) and is left for the body (fable-audit.md §3.4).
    fn peel_leading_label(&mut self) -> PResult<Option<String>> {
        if !self.at("[") {
            return Ok(None);
        }
        // Scan (depth-aware) from the leading `[` to its matching `]`; the group is a label iff it is a
        // single token wide and a `:` immediately follows the close bracket.
        let mut depth = 0i32;
        let mut close = None;
        for idx in self.pos..self.toks.len() {
            match self.i.resolve(self.toks[idx].sym) {
                "[" | "(" | "{" => depth += 1,
                "]" | ")" | "}" => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(idx);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else { return Ok(None) };
        let is_label = close == self.pos + 2 // `[`, <name>, `]`
            && self.toks.get(close + 1).map(|t| self.i.resolve(t.sym)) == Some(":");
        if !is_label {
            return Ok(None);
        }
        self.advance(); // `[`
        let l = self.name()?;
        self.eat("]")?;
        self.eat(":")?;
        Ok(Some(l))
    }

    /// Optional trailing statement attributes `[ … ]` on an `eq`/`mb`/`rl`. `owise`, `nonexec`,
    /// equation `variant`, rule `narrowing`, and the `label` name are retained; `dnt`, `metadata`, and
    /// presentation-only attributes (`format`, …) are parsed but ignored. Absent `[` ⇒ defaults.
    fn stmt_attrs(&mut self) -> PResult<StmtAttrs> {
        let mut sa = StmtAttrs::default();
        if !self.at("[") {
            return Ok(sa);
        }
        self.advance(); // [
        while !self.at("]") {
            match self
                .peek_text()
                .ok_or("unterminated statement attribute `[`")?
            {
                "owise" => {
                    sa.owise = true;
                    self.advance();
                }
                "nonexec" => {
                    sa.nonexec = true;
                    self.advance();
                }
                "variant" => {
                    sa.variant = true;
                    self.advance();
                }
                "narrowing" => {
                    sa.narrowing = true;
                    self.advance();
                }
                "label" => {
                    self.advance(); // 'label'
                    if !self.at("]") {
                        sa.label = self.peek_text().map(str::to_string); // retained for META up-translation
                        self.advance();
                    }
                }
                "metadata" => {
                    self.advance(); // 'metadata'
                    if !self.at("]") {
                        self.advance(); // its string argument (not retained)
                    }
                }
                "print" => {
                    self.advance(); // 'print'
                    // Capture the print list (strings/variables) until the next attribute keyword or `]`,
                    // for validation (C4f); a string is always a print item, never a keyword.
                    while let Some(t) = self.peek() {
                        if self.at("]") {
                            break;
                        }
                        let s = self.i.resolve(t.sym);
                        let is_attr_kw = matches!(
                            s,
                            "owise"
                                | "nonexec"
                                | "label"
                                | "metadata"
                                | "print"
                                | "format"
                                | "variant"
                                | "narrowing"
                                | "dnt"
                        );
                        if t.kind != TokKind::Str && is_attr_kw {
                            break;
                        }
                        sa.print.push(t);
                        self.advance();
                    }
                }
                _ => {
                    self.advance(); // any other attribute (format, …): ignore token-by-token
                }
            }
        }
        self.eat("]")?;
        Ok(sa)
    }

    /// An optional command bound `[n]` (e.g. `rewrite [2] …`, `continue [3] .`). Returns the number, or
    /// `None` when absent. (The `[n, m]` search bound is a Pillar A-iv extension.)
    fn opt_bound(&mut self) -> PResult<Option<u64>> {
        if self.at("[") {
            self.advance();
            let n = self
                .name()?
                .parse::<u64>()
                .map_err(|_| "expected a number in command bound `[n]`".to_string())?;
            self.eat("]")?;
            Ok(Some(n))
        } else {
            Ok(None)
        }
    }

    /// An optional `search` bound `[n]` (max solutions) or `[n, m]` (max solutions, max depth). Returns
    /// `(max_solutions, max_depth)`, both `None` when absent.
    fn opt_search_bound(&mut self) -> PResult<(Option<u64>, Option<u64>)> {
        let bound_head = self
            .toks
            .get(self.pos + 1)
            .map(|token| self.i.resolve(token.sym));
        if !self.at("[")
            || !bound_head.is_some_and(|text| {
                text == "," || (!text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            })
        {
            return Ok((None, None));
        }
        self.advance();
        let n = if self.at(",") {
            None
        } else {
            Some(
                self.name()?
                    .parse::<u64>()
                    .map_err(|_| "expected a number in search bound".to_string())?,
            )
        };
        let m = if self.at(",") {
            self.advance();
            Some(
                self.name()?
                    .parse::<u64>()
                    .map_err(|_| "expected a depth in search bound".to_string())?,
            )
        } else {
            None
        };
        self.eat("]")?;
        Ok((n, m))
    }

    // ---- operator attributes ----
    fn attrs(&mut self) -> PResult<Attrs> {
        self.eat("[")?;
        let mut a = Attrs::default();
        while !self.at("]") {
            let kw = self.peek_text().ok_or("unexpected end in op attributes")?;
            match kw {
                "assoc" => {
                    self.advance();
                    a.assoc = true;
                }
                "comm" => {
                    self.advance();
                    a.comm = true;
                }
                "idem" => {
                    self.advance();
                    a.idem = true;
                }
                "iter" => {
                    self.advance();
                    a.iter = true;
                }
                "ctor" => {
                    self.advance();
                    a.ctor = true;
                }
                "ditto" => {
                    self.advance();
                    a.ditto = true;
                }
                "memo" => {
                    self.advance();
                }
                // Object-system role attributes (Pillar 2.5). `obj`≡`object`, `msg`≡`message`,
                // `config`≡`configuration` (Maude's lexer aliases). Recorded onto the symbol; they
                // drive the `erewrite` object-message scheduler but are inert for plain rewrite/search.
                "config" | "configuration" => {
                    self.advance();
                    a.config = true;
                }
                "obj" | "object" => {
                    self.advance();
                    a.object = true;
                }
                "msg" | "message" => {
                    self.advance();
                    a.message = true;
                }
                "portal" => {
                    self.advance();
                    a.portal = true;
                }
                "frozen" => {
                    self.advance();
                    // `frozen` = all args; `frozen (1 2)` = those 1-based positions.
                    let positions = if self.at("(") {
                        let toks = self.balanced()?;
                        toks.iter()
                            .map(|t| {
                                self.i
                                    .resolve(t.sym)
                                    .parse::<u32>()
                                    .map_err(|_| "bad frozen position".to_string())
                            })
                            .collect::<Result<_, _>>()?
                    } else {
                        Vec::new()
                    };
                    a.frozen = Some(positions);
                }
                "id:" => {
                    self.advance();
                    a.id = Some(self.id_term());
                }
                // One-sided identity `left id:` / `right id:` (Maude's `assoc left id: e`): the identity
                // collapses only on the declared side (fable-audit.md §3.4).
                "left" | "right" => {
                    a.id_side = if kw == "left" {
                        IdSide::Left
                    } else {
                        IdSide::Right
                    };
                    self.advance(); // left / right
                    self.eat("id:")?;
                    a.id = Some(self.id_term());
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
                            .map(|t| {
                                self.i
                                    .resolve(t.sym)
                                    .parse::<u32>()
                                    .map_err(|_| "bad strat".to_string())
                            })
                            .collect::<Result<_, _>>()?,
                    );
                }
                "special" => {
                    self.advance();
                    a.special = Some(self.special()?);
                }
                "poly" => {
                    // `poly ( <positions> )` — the polymorphic positions (args 1-based, range `0`).
                    self.advance();
                    let toks = self.balanced()?;
                    a.poly = Some(
                        toks.iter()
                            .map(|t| {
                                self.i
                                    .resolve(t.sym)
                                    .parse::<u32>()
                                    .map_err(|_| "bad poly position".to_string())
                            })
                            .collect::<Result<_, _>>()?,
                    );
                }
                "format" => {
                    // `format ( <word> … )` — one directive word per mixfix gap, each a single token
                    // (`+`/`-`/`d`/… are not splitting punctuation, so `n++i` lexes as one). Stored for
                    // the pretty-printer; the words are interpreted there.
                    self.advance();
                    let toks = self.balanced()?;
                    a.format = Some(
                        toks.iter()
                            .map(|t| self.i.resolve(t.sym).to_string())
                            .collect(),
                    );
                }
                "metadata" | "latex" => {
                    // skip the keyword and its `( … )` / token argument (not modelled in the subset).
                    self.advance();
                    if self.at("(") {
                        self.balanced()?;
                    } else if !self.at("]") {
                        self.advance();
                    }
                }
                "pconst" => {
                    // A parameter constant of a theory (`op c : -> Elt [pconst]`): referred to as `X$c`
                    // in a parameterized module, mapped through the view like a parameter sort.
                    self.advance();
                    a.pconst = true;
                }
                "rpo" => {
                    // Recursive-path-ordering weight (`[rpo 1]`) — a termination hint; accepted and
                    // ignored (Maude reads it for its termination checker, not for reduction). Consume an
                    // optional numeric argument.
                    self.advance();
                    if !self.at("]") && self.peek_text().is_some_and(|t| t.parse::<i64>().is_ok()) {
                        self.advance();
                    }
                }
                other => return Err(format!("unsupported op attribute `{other}`")),
            }
        }
        self.eat("]")?;
        Ok(a)
    }

    /// The identity term bubble of an `id:` / `left id:` / `right id:` attribute — a single term, collected
    /// up to the next attribute keyword (or `]`). NOT `collect_until(["]"])`, which would swallow following
    /// attributes (`prec`, `format`, …) into the identity bubble — leaving the op with no `prec`, so e.g.
    /// SET/MAP's `_,_ [assoc comm id: empty prec 121]` defaulted to prec 41 and mis-parsed a
    /// constructor-application argument (`a |-> a, a |-> a`).
    fn id_term(&mut self) -> Vec<Token> {
        self.collect_until(&[
            "assoc",
            "comm",
            "idem",
            "iter",
            "ctor",
            "ditto",
            "memo",
            "config",
            "configuration",
            "obj",
            "object",
            "msg",
            "message",
            "portal",
            "frozen",
            "id:",
            "left",
            "right",
            "prec",
            "gather",
            "strat",
            "special",
            "poly",
            "format",
            "metadata",
            "latex",
            "pconst",
            "rpo",
            "]",
        ])
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
                        self.balanced()?
                            .iter()
                            .map(|t| self.i.resolve(t.sym).to_string())
                            .collect()
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
            frozen: self.frozen.clone(),
            special: self.special.clone(),
            ditto: self.ditto,
            poly: self.poly.clone(),
            format: self.format.clone(),
            config: self.config,
            object: self.object,
            message: self.message,
            portal: self.portal,
            pconst: self.pconst,
            id_side: self.id_side,
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
        assert_eq!(
            m.subsorts,
            vec![vec![
                vec!["Zero".to_string(), "NzNat".into()],
                vec!["Nat".into()]
            ]]
        );
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
        assert_eq!(
            m.ops
                .iter()
                .filter(|o| o.range == "Truth" && o.domain.is_empty())
                .count(),
            2
        );
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

    /// B5: import declarations parse into `PreModule.imports` with the right mode + module expression.
    #[test]
    fn parses_imports() {
        let src = "\
fmod M is
  protecting BOOL .
  extending FOO + BAR .
  including BAZ * (sort S to T, op f to g) .
  sort X .
endfm
";
        let m = &parse(src).modules[0];
        assert_eq!(m.imports.len(), 3);
        // protecting BOOL
        assert_eq!(m.imports[0].mode, ImportMode::Protecting);
        assert!(matches!(&m.imports[0].expr, ModuleExpr::Named(n) if n == "BOOL"));
        // extending FOO + BAR
        assert_eq!(m.imports[1].mode, ImportMode::Extending);
        match &m.imports[1].expr {
            ModuleExpr::Sum(a, b) => {
                assert!(matches!(&**a, ModuleExpr::Named(n) if n == "FOO"));
                assert!(matches!(&**b, ModuleExpr::Named(n) if n == "BAR"));
            }
            other => panic!("expected Sum, got {other:?}"),
        }
        // including BAZ * (sort S to T, op f to g)
        assert_eq!(m.imports[2].mode, ImportMode::Including);
        match &m.imports[2].expr {
            ModuleExpr::Rename(base, items) => {
                assert!(matches!(&**base, ModuleExpr::Named(n) if n == "BAZ"));
                assert_eq!(items.len(), 2);
                assert!(
                    matches!(&items[0], RenameItem::Sort { from, to } if from == "S" && to == "T")
                );
                assert!(
                    matches!(&items[1], RenameItem::Op { from, to, .. } if from == "f" && to == "g")
                );
            }
            other => panic!("expected Rename, got {other:?}"),
        }
        // the rest of the module still parses.
        assert_eq!(m.sorts, ["X"]);
    }

    /// `*` (renaming) binds tighter than `+` (summation): `A + B * (R)` = `A + (B * R)`.
    #[test]
    fn renaming_binds_tighter_than_summation() {
        let src = "fmod M is protecting A + B * (sort S to T) . endfm\n";
        let m = &parse(src).modules[0];
        match &m.imports[0].expr {
            ModuleExpr::Sum(a, b) => {
                assert!(matches!(&**a, ModuleExpr::Named(n) if n == "A"));
                assert!(matches!(&**b, ModuleExpr::Rename(_, _)));
            }
            other => panic!("expected Sum(A, Rename(B,…)), got {other:?}"),
        }
    }

    /// B-i: a theory (`fth`) parses into a `PreModule` flagged `is_theory` (kind Functional), with
    /// `[nonexec]` captured on its axiom and an ordinary equation left executable.
    #[test]
    fn parses_functional_theory_with_nonexec() {
        let src = "\
fth ORD is
  sort Elt .
  op _<_ : Elt Elt -> Elt .
  vars X Y : Elt .
  eq X < X = X [nonexec label irreflexive] .
  eq X < Y = Y .
endfth
";
        let m = &parse(src).modules[0];
        assert!(m.is_theory, "fth is a theory");
        assert_eq!(m.kind, ModuleKind::Functional);
        assert_eq!(m.name, "ORD");
        assert_eq!(m.sorts, ["Elt"]);
        assert_eq!(m.statements.len(), 2);
        match &m.statements[0] {
            Statement::Eq { nonexec, owise, .. } => {
                assert!(*nonexec, "the `[nonexec]` axiom is flagged");
                assert!(!*owise);
            }
            other => panic!("expected Eq, got {other:?}"),
        }
        match &m.statements[1] {
            Statement::Eq { nonexec, .. } => {
                assert!(!*nonexec, "an ordinary equation is executable")
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    /// B-i: `th` is a *system* theory (rules allowed); a functional theory (`fth`) rejects rules exactly
    /// as `fmod` does. Closing keywords `endth`/`endfth` are matched.
    #[test]
    fn system_theory_allows_rules_functional_rejects() {
        let ok = "th T is sort S . ops a b : -> S . rl a => b . endth\n";
        let m = &parse(ok).modules[0];
        assert!(m.is_theory && m.kind == ModuleKind::System);
        assert_eq!(m.statements.len(), 1);
        assert!(matches!(&m.statements[0], Statement::Rule { .. }));

        let bad = "fth T is sort S . ops a b : -> S . rl a => b . endfth\n";
        let mut i = Interner::new();
        let toks = tokenize(bad, &mut i);
        let err = Parser::new(&toks, &i).parse_source().unwrap_err();
        assert!(
            err.contains("functional"),
            "rules rejected in a functional theory: {err}"
        );
    }

    /// B-iii: a parameterized module parses its formal parameters and structured sort names (`Ctr{X}`,
    /// `X$Elt`, the structured subsort) — the name stays the bare base.
    #[test]
    fn parses_parameterized_module() {
        let src = "\
fmod CTR{X :: TRIV} is
  sorts Ctr{X} NzCtr{X} .
  subsort NzCtr{X} < Ctr{X} .
  op put : X$Elt Ctr{X} -> NzCtr{X} [ctor] .
endfm
";
        let m = &parse(src).modules[0];
        assert_eq!(m.name, "CTR");
        assert_eq!(m.params.len(), 1);
        assert_eq!(m.params[0].name, "X");
        assert_eq!(m.params[0].theory, "TRIV");
        assert_eq!(m.sorts, ["Ctr{X}", "NzCtr{X}"]);
        assert_eq!(
            m.subsorts,
            vec![vec![
                vec!["NzCtr{X}".to_string()],
                vec!["Ctr{X}".to_string()]
            ]]
        );
        let put = &m.ops[0];
        assert_eq!(put.domain, ["X$Elt", "Ctr{X}"]);
        assert_eq!(put.range, "NzCtr{X}");
    }

    /// B-iii: multiple parameters and a multi-argument structured sort `Map{X,Y}` (canonical no-space form).
    #[test]
    fn parses_multi_param_and_structured_sort() {
        let src = "fmod MAP{X :: TRIV, Y :: TRIV} is sort Map{X,Y} . op e : -> Map{X,Y} . endfm\n";
        let m = &parse(src).modules[0];
        assert_eq!(m.params.len(), 2);
        assert_eq!(m.params[1].name, "Y");
        assert_eq!(m.sorts, ["Map{X,Y}"]);
        assert_eq!(m.ops[0].range, "Map{X,Y}");
    }

    /// B-ii: a view parses into a `ViewDecl` — from-theory, to-module, a sort map, and op→op / op→term maps.
    #[test]
    fn parses_view() {
        let src = "\
view ToNum from TRIV to NUM is
  sort Elt to N .
  op e to z .
  op 0 to term zero .
endv
";
        let s = parse(src);
        assert!(s.modules.is_empty());
        assert_eq!(s.views.len(), 1);
        let v = &s.views[0];
        assert_eq!(v.name, "ToNum");
        assert!(matches!(&v.from, ModuleExpr::Named(n) if n == "TRIV"));
        assert!(matches!(&v.to, ModuleExpr::Named(n) if n == "NUM"));
        assert_eq!(v.sort_maps, vec![("Elt".to_string(), "N".to_string())]);
        assert_eq!(v.op_maps.len(), 2);
        assert!(matches!(&v.op_maps[0], OpMap::Op { .. }), "op e to z");
        assert!(
            matches!(&v.op_maps[1], OpMap::Term { .. }),
            "op 0 to term zero"
        );
    }

    #[test]
    fn parses_disambiguated_view_op_map_without_confusing_colon_variables() {
        let source = parse(
            "view V from T to M is\n\
               op f : A -> A to g .\n\
               op h(X:A) to term X:B .\n\
             endv\n",
        );
        let view = &source.views[0];
        assert!(matches!(
            &view.op_maps[0],
            OpMap::Op {
                dom_range: Some((domain, range)),
                ..
            } if domain == &["A"] && range == "A"
        ));
        assert!(matches!(
            &view.op_maps[1],
            OpMap::Term {
                dom_range: None,
                ..
            }
        ));
    }

    /// B-ii: an empty view (`view V from T to M is endv`) parses with no maps.
    #[test]
    fn parses_empty_view() {
        let s = parse("view Id from TRIV to TRIV is endv\n");
        assert_eq!(s.views.len(), 1);
        assert!(s.views[0].sort_maps.is_empty() && s.views[0].op_maps.is_empty());
    }

    /// Axis-A2: a parameterized view name (`view V{X :: T} …`) parses into `ViewDecl.params`, and its `to`
    /// target may be a (non-`Named`) instantiation `LIST{X}`.
    #[test]
    fn parses_parameterized_view() {
        let mut i = Interner::new();
        let toks = tokenize("view V{X :: TRIV} from TRIV to LIST{X} is endv\n", &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let v = &s.views[0];
        assert_eq!(v.params.len(), 1);
        assert_eq!(
            (v.params[0].name.as_str(), v.params[0].theory.as_str()),
            ("X", "TRIV")
        );
        match &v.to {
            ModuleExpr::Instantiation(base, args) => {
                assert!(matches!(&**base, ModuleExpr::Named(n) if n == "LIST"));
                assert!(matches!(args.as_slice(), [ModuleExpr::Named(n)] if n == "X"));
            }
            other => panic!("expected Instantiation target, got {other:?}"),
        }
    }

    /// B-iv: a parameterized instantiation `LIST{Nat}` parses into `ModuleExpr::Instantiation`; a
    /// multi-argument `MAP{Nat, String}` carries one argument expression per parameter. Axis-A5: a nested
    /// instantiation `BOX{BoxV{ToColor}}` parses its argument as an inner `Instantiation`.
    #[test]
    fn parses_instantiation() {
        let m = &parse("fmod M is protecting LIST{Nat} . endfm\n").modules[0];
        match &m.imports[0].expr {
            ModuleExpr::Instantiation(base, args) => {
                assert!(matches!(&**base, ModuleExpr::Named(n) if n == "LIST"));
                assert!(matches!(args.as_slice(), [ModuleExpr::Named(n)] if n == "Nat"));
            }
            other => panic!("expected Instantiation, got {other:?}"),
        }
        let m2 = &parse("fmod M is protecting MAP{Nat, String} . endfm\n").modules[0];
        match &m2.imports[0].expr {
            ModuleExpr::Instantiation(_, args) => {
                assert!(matches!(&args[0], ModuleExpr::Named(n) if n == "Nat"));
                assert!(matches!(&args[1], ModuleExpr::Named(n) if n == "String"));
            }
            other => panic!("expected Instantiation, got {other:?}"),
        }
        let m3 = &parse("fmod M is protecting BOX{BoxV{ToColor}} . endfm\n").modules[0];
        match &m3.imports[0].expr {
            ModuleExpr::Instantiation(_, args) => match &args[0] {
                ModuleExpr::Instantiation(ibase, iargs) => {
                    assert!(matches!(&**ibase, ModuleExpr::Named(n) if n == "BoxV"));
                    assert!(matches!(iargs.as_slice(), [ModuleExpr::Named(n)] if n == "ToColor"));
                }
                other => panic!("expected nested Instantiation arg, got {other:?}"),
            },
            other => panic!("expected Instantiation, got {other:?}"),
        }
        // Axis-A5 kind 1: a *chain* `BOX{ToT2}{C2}` parses as an instantiation whose base is itself an
        // instantiation (the inner `{ToT2}` applied, then the outer `{C2}`).
        let m4 = &parse("fmod M is protecting BOX{ToT2}{C2} . endfm\n").modules[0];
        match &m4.imports[0].expr {
            ModuleExpr::Instantiation(base, args) => {
                assert!(matches!(args.as_slice(), [ModuleExpr::Named(n)] if n == "C2"));
                match &**base {
                    ModuleExpr::Instantiation(ibase, iargs) => {
                        assert!(matches!(&**ibase, ModuleExpr::Named(n) if n == "BOX"));
                        assert!(matches!(iargs.as_slice(), [ModuleExpr::Named(n)] if n == "ToT2"));
                    }
                    other => panic!("expected chained Instantiation base, got {other:?}"),
                }
            }
            other => panic!("expected Instantiation, got {other:?}"),
        }
    }
}
