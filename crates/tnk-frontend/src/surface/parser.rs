//! The surface (recursive-descent) parser: `.maude` token stream → [`Source`] (functional modules +
//! commands). Term-carrying parts are collected as raw token **bubbles** (terminator-delimited), handed
//! to the mixfix parser later (B4.4). This replaces Maude's flex/bison `lexBubble` global handshake with
//! an explicit cursor + `collect_until` (decision: no hidden lexer↔parser state).

use crate::lex::{Interner, TokKind, Token};
use crate::surface::ast::*;

pub type PResult<T> = Result<T, String>;

/// The execution-relevant trailing attributes of a statement (`[owise]`, `[nonexec]`). Other attributes
/// (`label`, `metadata`, `print`, …) are parsed but not retained — see [`Parser::stmt_attrs`].
#[derive(Debug, Default, Clone, Copy)]
struct StmtAttrs {
    owise: bool,
    nonexec: bool,
}

pub struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    i: &'a Interner,
}

/// The index of a top-level token (depth 0 over `()`/`[]`/`{}`) whose text is `kw` — the `last`
/// occurrence (the equation separator `=`, *past* the `=[` of a `_=[_]_` in the lhs) or the first (the
/// `ceq` `if`). Used to split a [`Parser::collect_to_dot`] statement body.
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

/// Peel a trailing top-level statement-attribute group `[ owise | nonexec | metadata … ]` off `body`,
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
        matches!(s, "owise" | "nonexec" | "label" | "metadata" | "print" | "format" | "variant" | "narrowing")
    };
    if !body.get(open + 1).map(|t| i.resolve(t.sym)).is_some_and(is_attr_kw) {
        return sa; // a `[_]`-list / `{_}`-set term, not attributes
    }
    for t in &body[open + 1..body.len() - 1] {
        match i.resolve(t.sym) {
            "owise" => sa.owise = true,
            "nonexec" => sa.nonexec = true,
            _ => {}
        }
    }
    body.truncate(open);
    sa
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

    /// Collect a whole statement body up to the top-level terminator `.` (left unconsumed), tracking
    /// `()`/`[]`/`{}` depth so a bracketed sub-term — a `[_]`-list rhs, a `{_}` set, a structured sort —
    /// does not look like a delimiter. The caller then splits the body (separator `=`, `if`, attributes)
    /// with [`top_level_find`] / [`peel_stmt_attrs`].
    fn collect_to_dot(&mut self) -> Vec<Token> {
        let mut depth = 0i32;
        let mut out = Vec::new();
        while let Some(t) = self.peek() {
            if depth == 0 && t.kind == TokKind::Dot {
                break;
            }
            match self.i.resolve(t.sym) {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
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

    /// Parse one top-level item — a module or a (module-untagged) command — or `None` at end of input.
    /// The REPL drives this directly (a command binds to its persistent current module); `parse_source`
    /// loops over it and re-applies Maude's most-recently-entered-module tagging.
    pub fn parse_top_item(&mut self) -> PResult<Option<TopItem>> {
        let Some(txt) = self.peek_text() else { return Ok(None) };
        let item = match txt {
            "fmod" | "mod" | "fth" | "th" | "smod" | "sth" => TopItem::Module(self.module()?),
            "view" => TopItem::View(self.view()?),
            "srewrite" | "srew" | "dsrewrite" | "dsrew" => {
                let depth_first = txt.starts_with('d');
                self.advance();
                let module = self.opt_in_module()?;
                let term = self.collect_until(&["using"]);
                self.eat("using")?;
                let strategy = self.strategy()?;
                self.eat_dot()?;
                TopItem::Command(Command::Srewrite { module, depth_first, term, strategy })
            }
            "reduce" | "red" => {
                self.advance();
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Reduce { module, term })
            }
            "match" | "xmatch" => {
                let xmatch = txt == "xmatch";
                self.advance();
                let module = self.opt_in_module()?;
                let pattern = self.collect_until(&["<=?"]);
                self.eat("<=?")?;
                let subject = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Match { module, pattern, subject, xmatch })
            }
            "rewrite" | "rew" => {
                self.advance();
                let bound = self.opt_bound()?;
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Rewrite { module, bound, term })
            }
            "frewrite" | "frew" => {
                self.advance();
                let bound = self.opt_bound()?;
                let module = self.opt_in_module()?;
                let term = self.collect_until(&[]);
                self.eat_dot()?;
                TopItem::Command(Command::Frewrite { module, bound, term })
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
                    other => return Err(format!("search: expected `=>1`/`=>+`/`=>*`/`=>!`, found {other:?}")),
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
                TopItem::Command(Command::Search { module, max_solutions, max_depth, subject, arrow, pattern, such_that })
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
            _ => return Err(format!("unexpected top-level token {txt:?}")),
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
                    let m = src.modules.len().checked_sub(1).ok_or("command before any module")?;
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
        // A strategy module/theory (`smod`/`sth`) is a system module (rules allowed) that additionally
        // permits `strat`/`sd`; a `th`/`sth` is a theory.
        let kind =
            if matches!(kw, "mod" | "th" | "smod" | "sth") { ModuleKind::System } else { ModuleKind::Functional };
        let is_theory = matches!(kw, "fth" | "th" | "sth");
        let is_strategy = matches!(kw, "smod" | "sth");
        self.advance(); // fmod / mod / fth / th / smod / sth
        let name = self.name()?;
        // Optional formal parameters `{X :: T, …}` (B-iii). The stored name stays the bare base.
        let params = if self.at("{") { self.param_list()? } else { Vec::new() };
        self.eat("is")?;
        let mut m = PreModule {
            name,
            kind,
            is_theory,
            is_strategy,
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
        while !self.at_module_end() {
            self.decl(&mut m)?;
        }
        self.advance(); // endfm / endm / endfth / endth
        Ok(m)
    }

    /// At a module/theory closing keyword (`endfm`/`endm`/`endfth`/`endth`).
    fn at_module_end(&self) -> bool {
        matches!(self.peek_text(), Some("endfm" | "endm" | "endfth" | "endth" | "endsm" | "endsth"))
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
            // `op undefined : -> [Y$Elt]`). `build_sig` resolves the canonical `[S]` spelling to
            // `error_sort(kind_of(S))`. The inner is a full sort name (so `[List{Nat}]` nests).
            self.advance(); // [
            let inner = self.sort_name()?;
            self.eat("]")?;
            return Ok(format!("[{inner}]"));
        }
        let mut name = self.name()?;
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
    /// `op f to g .`, `op f to term t .` — a disambiguated source `op f : … to …` is rejected (follow-up).
    fn view(&mut self) -> PResult<ViewDecl> {
        self.eat("view")?;
        let name = self.name()?;
        let params = if self.at("{") { self.param_list()? } else { Vec::new() };
        // `module_expr` parses an atom/`*`/`+` chain and stops at the first other token (it does not
        // consume a terminator), so it ends naturally at `to` / `is`.
        self.eat("from")?;
        let from = self.module_expr()?;
        self.eat("to")?;
        let to = self.module_expr()?;
        self.eat("is")?;

        let mut sort_maps = Vec::new();
        let mut op_maps = Vec::new();
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
                "op" => {
                    self.advance();
                    let from = self.collect_until(&["to"]);
                    if from.iter().any(|t| self.i.resolve(t.sym) == ":") {
                        return Err("disambiguated view op map `op f : … to …` is a B-ii follow-up".into());
                    }
                    self.eat("to")?;
                    if self.at("term") {
                        self.advance();
                        let term = self.collect_until(&[]);
                        self.eat_dot()?;
                        op_maps.push(OpMap::Term { from, to: term });
                    } else {
                        let to = self.collect_until(&[]);
                        self.eat_dot()?;
                        op_maps.push(OpMap::Op { from, to });
                    }
                }
                other => {
                    return Err(format!(
                        "view map must be `sort … to …` or `op … to …`, found `{other}` \
                         (strat/var/class maps are a follow-up)"
                    ));
                }
            }
        }
        self.advance(); // endv
        Ok(ViewDecl { name, params, from, to, sort_maps, op_maps })
    }

    fn decl(&mut self, m: &mut PreModule) -> PResult<()> {
        let kw = self.peek_text().ok_or("unexpected end of input in module")?;
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
                let names = self.collect_until(&[":"]);
                self.eat(":")?;
                let mut domain = Vec::new();
                while !self.at("->") && !self.at("~>") {
                    domain.push(self.sort_name()?);
                }
                // `~>` is the partial (kind-level) arrow (`op modExp : Nat Nat NzNat ~> Nat`): its range
                // is the kind, so an unreduced application sits at the kind level (recorded in `partial`).
                let partial = self.at("~>");
                if partial {
                    self.advance();
                } else {
                    self.eat("->")?;
                }
                let range = self.sort_name()?;
                let attrs = if self.at("[") { self.attrs()? } else { Attrs::default() };
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
                    m.ops.push(OpDecl { name: names, domain, range, partial, attrs });
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
            "eq" | "ceq" => {
                let conditional = kw == "ceq";
                self.advance();
                // Collect the whole statement body (depth-aware over `()[]{}`) and split it, rather than
                // streaming to the first `=`/`[`: a `[_]`-list term (`eq reverse([]) = [] .`) has top-level
                // brackets in the rhs, and the `_=[_]_` operator (`eq X =[Z] Y = … .`) puts a top-level `=`
                // in the lhs. So: peel a trailing `[attrs]` (only when it really is attributes, not a list),
                // split a `ceq` at the top-level `if`, and split lhs/rhs at the **last** top-level `=`.
                let mut body = self.collect_to_dot();
                self.eat_dot()?;
                let sa = peel_stmt_attrs(&mut body, self.i);
                let cond = if conditional {
                    let i = top_level_find(&body, self.i, "if", false)
                        .ok_or("`ceq` is missing its `if` condition")?;
                    let c = body.split_off(i + 1);
                    body.pop(); // the `if`
                    Some(c)
                } else {
                    None
                };
                let eq = top_level_find(&body, self.i, "=", true).ok_or("equation is missing `=`")?;
                let rhs = body.split_off(eq + 1);
                body.pop(); // the `=`
                m.statements.push(Statement::Eq { lhs: body, rhs, cond, owise: sa.owise, nonexec: sa.nonexec });
            }
            "mb" | "cmb" => {
                let conditional = kw == "cmb";
                self.advance();
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
                m.statements.push(Statement::Mb { lhs, sort, cond, nonexec: sa.nonexec });
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
                // Optional leading label `[name] :` (Maude's labelled-rule syntax). `[`/`]` are splitting
                // punctuation, so they lex as their own tokens.
                let label = if self.at("[") {
                    self.advance();
                    let l = self.name()?;
                    self.eat("]")?;
                    self.eat(":")?;
                    Some(l)
                } else {
                    None
                };
                // The arrow `=>` lexes as one token (a run of non-punctuation chars); an unspaced `t=>p`
                // lexes as a single token and so will not split here — rejected exactly as Maude rejects it.
                let lhs = self.collect_until(&["=>"]);
                self.eat("=>")?;
                let (rhs, cond);
                if conditional {
                    rhs = self.collect_until(&["if"]);
                    self.eat("if")?;
                    cond = Some(self.collect_until(&["["]));
                } else {
                    rhs = self.collect_until(&["["]);
                    cond = None;
                }
                // Optional trailing statement attributes (`[nonexec]`, `[label …]`, `[metadata …]`, …):
                // `nonexec` blocks execution; the rest don't affect it.
                let sa = self.stmt_attrs()?;
                self.eat_dot()?;
                m.statements.push(Statement::Rule { label, lhs, rhs, cond, nonexec: sa.nonexec });
            }
            "strat" | "strats" => {
                if !m.is_strategy {
                    return Err(format!(
                        "strategy declaration `{kw}` is only allowed in a strategy module (`smod {}`)",
                        m.name
                    ));
                }
                self.advance();
                // `strat[s] n1 … : <domain sorts> @ Sort .`
                let mut names = Vec::new();
                while !self.at(":") {
                    names.push(self.name()?);
                }
                self.eat(":")?;
                let mut domain = Vec::new();
                while !self.at("@") {
                    domain.push(self.sort_name()?);
                }
                self.eat("@")?;
                let subject = self.sort_name()?;
                self.eat_dot()?;
                for name in names {
                    m.strat_decls.push(StratDecl { name, domain: domain.clone(), subject: subject.clone() });
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
                let params = if self.at("(") { self.paren_arg_bubbles()? } else { Vec::new() };
                self.eat(":=")?;
                let body = self.strategy()?;
                let cond = if conditional {
                    self.eat("if")?;
                    Some(self.collect_until(&[]))
                } else {
                    None
                };
                self.eat_dot()?;
                m.strat_defs.push(StratDef { name, params, body, cond });
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
                if txt == "top" { StratExpr::Top(e) } else { StratExpr::One(e) }
            }
            // Derived branch forms (sugar over `? :`).
            "try" | "not" | "test" => {
                self.advance();
                self.eat("(")?;
                let e = Box::new(self.strategy()?);
                self.eat(")")?;
                let (success, failure) = match txt {
                    "not" => (StratExpr::Fail, StratExpr::Idle),
                    _ => (StratExpr::Idle, StratExpr::Fail), // try / test
                };
                StratExpr::Branch { test: e, success: Box::new(success), failure: Box::new(failure) }
            }
            "or-else" => {
                self.advance();
                self.eat("(")?;
                let a = Box::new(self.strategy()?);
                self.eat(",")?;
                let b = self.strategy()?;
                self.eat(")")?;
                StratExpr::Branch { test: a, success: Box::new(StratExpr::Idle), failure: Box::new(b) }
            }
            "match" | "xmatch" | "amatch" => {
                self.advance();
                let kind = Self::test_kind(txt);
                let (pattern, cond) = self.strat_pattern_cond()?;
                StratExpr::Test { kind, pattern, cond }
            }
            "matchrew" | "xmatchrew" | "amatchrew" => {
                self.advance();
                let kind = match txt {
                    "xmatchrew" => TestKind::XMatch,
                    "amatchrew" => TestKind::AMatch,
                    _ => TestKind::Match,
                };
                let (pattern, cond) = self.strat_pattern_cond_until(&["by"])?;
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
                StratExpr::MatchRew { kind, pattern, cond, subs }
            }
            // A rule application `label[σ]{strats}` or a strategy call `name(args)` / bare `name`.
            _ => {
                let name = self.name()?;
                if self.at("(") {
                    StratExpr::Call { name, args: self.paren_arg_bubbles()? }
                } else {
                    let subst = if self.at("[") { self.strat_subst()? } else { Vec::new() };
                    let substrats = if self.at("{") { self.strat_brace_strats()? } else { Vec::new() };
                    StratExpr::Apply { label: name, subst, substrats }
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

    /// As [`strat_pattern_cond`](Self::strat_pattern_cond) but `extra` adds pattern/condition stop tokens
    /// (matchrew stops the pattern/condition at `by`).
    fn strat_pattern_cond_until(&mut self, extra: &[&str]) -> PResult<(Vec<Token>, Option<Vec<Token>>)> {
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

    /// `NAME ('{' arg (',' arg)* '}')* | '(' module_expr ')'`. Each `{…}` after a name is a parameterized
    /// instantiation `M{A, …}`; a *chain* `M{A}{B}` (Axis-A5 kind 1) re-instantiates the free parameters a
    /// theory-view argument leaves behind.
    fn module_atom(&mut self) -> PResult<ModuleExpr> {
        if self.at("(") {
            self.advance();
            let e = self.module_expr()?;
            self.eat(")")?;
            return Ok(e);
        }
        let mut e = ModuleExpr::Named(self.name()?);
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

    /// A renaming `( sort A to B , op f to g , … )`. Disambiguated op renaming (`op f : A -> B to g`) is
    /// a B5 follow-up, rejected loudly here; mixfix op renaming is rejected when applied (in `tnk-modules`).
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
                "op" => {
                    // The from-name is a full mixfix name (may contain `,`, e.g. `_,_`): collect its
                    // tokens up to the standalone `to` keyword, joined with no spaces into the canonical
                    // name (`_` `,` `_` → `_,_`). A disambiguated `op f : dom -> range to g` is a
                    // follow-up, rejected loudly.
                    let from_toks = self.collect_until(&["to", ":"]);
                    if self.at(":") {
                        return Err("disambiguated op renaming `op f : … to g` is a B5 follow-up".into());
                    }
                    self.eat("to")?;
                    // The to-name runs to the next item separator `,`, the attribute `[`, or `)`.
                    let to_toks = self.collect_until(&[",", "[", ")"]);
                    let attrs = if self.at("[") { self.attrs()? } else { Attrs::default() };
                    let from: String = from_toks.iter().map(|t| self.i.resolve(t.sym)).collect();
                    let to: String = to_toks.iter().map(|t| self.i.resolve(t.sym)).collect();
                    items.push(RenameItem::Op { from, to, attrs });
                }
                other => {
                    return Err(format!("renaming item must start with `sort` or `op`, found `{other}`"));
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

    /// Optional trailing statement attributes `[ … ]` on an `eq`/`mb`/`rl`. Only `owise` and `nonexec`
    /// affect execution and are returned; `label`/`metadata` (and their argument) plus any other attribute
    /// (`print`, `format`, …) are parsed and ignored. Absent `[` ⇒ both `false`.
    fn stmt_attrs(&mut self) -> PResult<StmtAttrs> {
        let mut sa = StmtAttrs::default();
        if !self.at("[") {
            return Ok(sa);
        }
        self.advance(); // [
        while !self.at("]") {
            match self.peek_text().ok_or("unterminated statement attribute `[`")? {
                "owise" => {
                    sa.owise = true;
                    self.advance();
                }
                "nonexec" => {
                    sa.nonexec = true;
                    self.advance();
                }
                "label" | "metadata" => {
                    self.advance(); // the keyword
                    if !self.at("]") {
                        self.advance(); // its single argument (label name / metadata string)
                    }
                }
                _ => {
                    self.advance(); // any other attribute (print, format, …): ignore token-by-token
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
        if !self.at("[") {
            return Ok((None, None));
        }
        self.advance();
        let n = self.name()?.parse::<u64>().map_err(|_| "expected a number in search bound".to_string())?;
        let m = if self.at(",") {
            self.advance();
            Some(self.name()?.parse::<u64>().map_err(|_| "expected a depth in search bound".to_string())?)
        } else {
            None
        };
        self.eat("]")?;
        Ok((Some(n), m))
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
                "memo" | "config" | "obj" | "msg" | "portal" => { self.advance(); }
                "frozen" => {
                    self.advance();
                    // `frozen` = all args; `frozen (1 2)` = those 1-based positions.
                    let positions = if self.at("(") {
                        let toks = self.balanced()?;
                        toks.iter()
                            .map(|t| self.i.resolve(t.sym).parse::<u32>().map_err(|_| "bad frozen position".to_string()))
                            .collect::<Result<_, _>>()?
                    } else {
                        Vec::new()
                    };
                    a.frozen = Some(positions);
                }
                "id:" => {
                    self.advance();
                    // The identity is a single term; collect up to the next attribute keyword (or `]`).
                    // NOT `collect_until(["]"])`, which swallows following attributes (`prec`, `format`,
                    // …) into the identity bubble — leaving the op with no `prec`, so e.g. SET/MAP's
                    // `_,_ [assoc comm id: empty prec 121]` defaulted to prec 41 and mis-parsed a
                    // constructor-application argument (`a |-> a, a |-> a`).
                    a.id = Some(self.collect_until(&[
                        "assoc", "comm", "idem", "iter", "ctor", "ditto", "memo", "config", "obj", "msg",
                        "portal", "frozen", "id:", "prec", "gather", "strat", "special", "poly", "format",
                        "metadata", "latex", "]",
                    ]));
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
                "poly" => {
                    // `poly ( <positions> )` — the polymorphic positions (args 1-based, range `0`).
                    self.advance();
                    let toks = self.balanced()?;
                    a.poly = Some(
                        toks.iter()
                            .map(|t| self.i.resolve(t.sym).parse::<u32>().map_err(|_| "bad poly position".to_string()))
                            .collect::<Result<_, _>>()?,
                    );
                }
                "format" => {
                    // `format ( <word> … )` — one directive word per mixfix gap, each a single token
                    // (`+`/`-`/`d`/… are not splitting punctuation, so `n++i` lexes as one). Stored for
                    // the pretty-printer; the words are interpreted there.
                    self.advance();
                    let toks = self.balanced()?;
                    a.format = Some(toks.iter().map(|t| self.i.resolve(t.sym).to_string()).collect());
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
            frozen: self.frozen.clone(),
            special: self.special.clone(),
            ditto: self.ditto,
            poly: self.poly.clone(),
            format: self.format.clone(),
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
                assert!(matches!(&items[0], RenameItem::Sort { from, to } if from == "S" && to == "T"));
                assert!(matches!(&items[1], RenameItem::Op { from, to, .. } if from == "f" && to == "g"));
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
            Statement::Eq { nonexec, .. } => assert!(!*nonexec, "an ordinary equation is executable"),
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
        assert!(err.contains("functional"), "rules rejected in a functional theory: {err}");
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
        assert_eq!(m.subsorts, vec![vec![vec!["NzCtr{X}".to_string()], vec!["Ctr{X}".to_string()]]]);
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
        assert!(matches!(&v.op_maps[1], OpMap::Term { .. }), "op 0 to term zero");
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
        assert_eq!((v.params[0].name.as_str(), v.params[0].theory.as_str()), ("X", "TRIV"));
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
