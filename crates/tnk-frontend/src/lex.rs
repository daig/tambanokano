//! Lexer: Maude tokenization + operator-name splitting.
//!
//! Maude tokens are separated by whitespace and by the **special-splitting** punctuation `( ) [ ] { } ,`
//! (each its own token); everything else (letters, digits, `+ - < = : _ .` …) is part of a *maudeId*. The
//! statement/command terminator `.` is a `.` followed by whitespace/EOF/punctuation — distinguished from a
//! `.` inside a float (`1.5`) or a structured sort. Strings are `"…"`, quoted-ids start with `'`, and a
//! backquote escapes a splitting char into a maudeId. (`lexer.ll` / `token.{hh,cc}` in the reference.)
//!
//! Line comments (`***`/`---` to end of line) and **bracketed** comments (`***( … )` / `---( … )`, balanced
//! parens across newlines) are both handled. Tokens are interned ([`Interner`]) so equality is a `u32`
//! compare. This slice is the functional-fragment subset; LaTeX/file-name lexer modes and the
//! lexer↔parser bubble handshake (replaced by an explicit surface-parser API in B4.2) are follow-ups.

use std::collections::HashMap;

/// An interned token string (an index into the [`Interner`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym(u32);

/// String interner: text ↔ [`Sym`]. Token equality is `Sym` equality.
#[derive(Debug, Default)]
pub struct Interner {
    strings: Vec<String>,
    lookup: HashMap<String, Sym>,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn intern(&mut self, s: &str) -> Sym {
        if let Some(&sym) = self.lookup.get(s) {
            return sym;
        }
        let sym = Sym(u32::try_from(self.strings.len()).expect("interner exceeded u32"));
        self.strings.push(s.to_string());
        self.lookup.insert(s.to_string(), sym);
        sym
    }
    pub fn resolve(&self, sym: Sym) -> &str {
        &self.strings[sym.0 as usize]
    }
    /// The [`Sym`] for an already-interned string, or `None`. Immutable lookup (no interning) — used by
    /// the surface parser (which holds `&Interner`) to obtain the mixfix fragment chars (`:`/`_`) it
    /// splices into synthesized `omod` attribute-operator names; [`tokenize`] guarantees they are interned.
    pub fn get(&self, s: &str) -> Option<Sym> {
        self.lookup.get(s).copied()
    }
}

impl Sym {
    /// The raw intern index — assigned in first-occurrence order, exactly Maude's `Token` name code.
    /// The variable-vs-variable dag order is `id() - id()` on name codes (variableDagNode.cc), so this
    /// is the rank a command-subject pseudo-variable carries into the kernel.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Rebuild a [`Sym`] from a raw intern index previously obtained via [`index`](Self::index) —
    /// the inverse used when a name code comes back out of a kernel `Var` leaf for printing. The
    /// caller must pass an index minted by the same [`Interner`].
    pub fn from_raw(raw: u32) -> Sym {
        Sym(raw)
    }
}

/// The lexical class of a [`Token`], computed at scan time from its text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokKind {
    /// An identifier / keyword / operator-name fragment (the default).
    Ident,
    /// A splitting punctuation character `( ) [ ] { } ,` (its own token).
    Punct,
    /// The statement/command terminator `.` (a `.` followed by whitespace/EOF/punctuation).
    Dot,
    /// A natural-number literal `0 | [1-9][0-9]*`.
    Number,
    /// A string literal `"…"` — a token that is *exactly* one string (its unescaped close-quote is the
    /// last char). A string merely *glued into* a longer maudeId (`"x"y`, `foo"bar"`) is an `Ident`, not
    /// a `Str` — Maude's `Token::computeSpecialProperty` (`token.cc:478`).
    Str,
    /// A float literal — Maude's `looksLikeFloat` forms (see [`is_float_literal`]): `1.5`, `-1.5`,
    /// `5.0e-1`, and the abbreviated `1.`, `.5`, `1.e3`, `.5e2`, `1e3`, `Infinity`.
    Float,
    /// A negative-integer literal `-[0-9]+` with a nonzero magnitude (Maude's `SMALL_NEG`): a `-` glued
    /// to digits, lexed as one token. `-1.5` is a Float (checked first); a *spaced* `-` stays its own
    /// token, so `5 - 7` is subtraction and `5 -7` fails to parse (just as in Maude).
    NegNumber,
    /// A quoted identifier `'…`.
    Qid,
    /// A glued rational literal `[-]num/den` (Maude's `RATIONAL`, [`is_rational_literal`]): `1/6`,
    /// `-7/3`. A *spaced* `1 / 6` stays three tokens (the `_/_` division operator), so binary division
    /// is unaffected — only a `/`-glued numeral pair reaches `classify` as one token, as in Maude.
    Rational,
    /// An `iter`-symbol input token `f^count` (Maude's `ITER_SYMBOL`, [`is_iter_token`]): `s_^10`,
    /// `s_^18446744073709551616`. The text before the last `^` is the operator name, the trailing
    /// (leading-nonzero) digits the iteration count.
    Iter,
}

/// A lexical token: its interned text, source line, and class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub sym: Sym,
    pub line: u32,
    pub kind: TokKind,
}

impl Token {
    /// The token's text.
    pub fn text<'a>(&self, i: &'a Interner) -> &'a str {
        i.resolve(self.sym)
    }
}

/// A splitting punctuation char (its own token; not part of a maudeId).
pub(crate) fn is_punct(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',')
}

/// Whether the maudeId built so far is the prefix of a colon variable `name:base` — a non-empty variable
/// name and a non-empty sort base after the last `:`. When it is, a following `{ … }` is part of the
/// (structured) sort name, so the lexer keeps `L:List{Nat}` one token rather than splitting `L:List` off
/// from `{ Nat }`. (A plain sort `List{Nat}` has no `:`, so it still tokenizes as `List { Nat }`.)
fn colon_var_shape(text: &str) -> bool {
    matches!(text.rsplit_once(':'), Some((name, base)) if !name.is_empty() && !base.is_empty())
}

/// A line comment `***`/`---` begins at `chars[j]`.
fn is_line_comment_start(chars: &[char], j: usize) -> bool {
    matches!(chars.get(j), Some('*') | Some('-'))
        && chars.get(j + 1) == chars.get(j)
        && chars.get(j + 2) == chars.get(j)
}

/// A top-level keyword that can begin a new statement/command/declaration — so a `.` immediately before
/// one (on the same line) is a terminator. Maude's `SEEN_DOT` one-token lookahead, reduced to the
/// functional-fragment keyword set.
fn is_top_level_keyword(w: &str) -> bool {
    matches!(
        w,
        "fmod" | "mod" | "fth" | "th" | "endfm" | "endm" | "endfth" | "endth"
            | "view" | "endv"
            | "sort" | "sorts" | "subsort" | "subsorts" | "op" | "ops" | "var" | "vars"
            | "protecting" | "pr" | "extending" | "ex" | "including" | "inc"
            | "eq" | "ceq" | "mb" | "cmb" | "rl" | "crl"
            | "red" | "reduce" | "match" | "xmatch" | "rew" | "rewrite" | "search"
    )
}

/// Whether `chars[i] == '.'` is a statement/command **terminator** rather than an ordinary token (a `.`
/// inside a float `1.5`, a structured sort, or the `_._` operator).
///
/// Maude's rule (the stateful `SEEN_DOT` lexer state) is one-token lookahead: a `.` terminates iff what
/// follows it — skipping spaces/tabs — is end-of-line, EOF, a line comment, **or a top-level keyword**
/// (a new statement/command, even on the same line, as in `sort N . op 0 : …`). A `.` followed by an
/// ordinary token on the same line is the `_._` operator (`"ab" . "cd"`), not a terminator.
fn is_terminator_dot(chars: &[char], i: usize) -> bool {
    let mut j = i + 1;
    while matches!(chars.get(j), Some(' ') | Some('\t') | Some('\r')) {
        j += 1;
    }
    match chars.get(j) {
        None | Some('\n') => return true,
        _ if is_line_comment_start(chars, j) => return true,
        _ => {}
    }
    // Read the next word and check it against the top-level keywords.
    let start = j;
    while let Some(&c) = chars.get(j) {
        if c.is_whitespace() || is_punct(c) {
            break;
        }
        j += 1;
    }
    let word: String = chars[start..j].iter().collect();
    is_top_level_keyword(&word)
}

/// A token is a STRING literal iff it starts with `"` and the matching *unescaped* close-quote is its
/// LAST character — Maude's `Token::computeSpecialProperty` (`token.cc:478`). A token that merely
/// *contains* a string (`"x"y`, `foo"bar"`) is an ordinary identifier, not a string constant. (The quote
/// and backslash are ASCII, so byte-scanning is faithful even across multibyte string content.)
fn is_string_literal(text: &str) -> bool {
    let bytes = text.as_bytes();
    if bytes.first() != Some(&b'"') {
        return false;
    }
    let mut seen_backslash = false;
    for (idx, &c) in bytes.iter().enumerate().skip(1) {
        match c {
            b'\\' => seen_backslash = !seen_backslash,
            b'"' if !seen_backslash => return idx == bytes.len() - 1,
            _ => seen_backslash = false,
        }
    }
    false // unterminated
}

/// The class of a scanned maudeId text. The order mirrors Maude's `Token::computeSpecialProperty`
/// (`token.cc`): quoted-id / string, then `ITER_SYMBOL`, `FLOAT`, integer (`ZERO`/`SMALL_NEG`/
/// `SMALL_NAT`), and finally `RATIONAL` — a token that is not any of these is an ordinary identifier.
fn classify(text: &str) -> TokKind {
    if is_string_literal(text) {
        return TokKind::Str;
    }
    if text.starts_with('\'') && text.len() > 1 {
        return TokKind::Qid;
    }
    if is_iter_token(text) {
        return TokKind::Iter;
    }
    if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) {
        return TokKind::Number;
    }
    if is_float_literal(text) {
        return TokKind::Float;
    }
    if is_neg_integer(text) {
        return TokKind::NegNumber;
    }
    if is_rational_literal(text) {
        return TokKind::Rational;
    }
    TokKind::Ident
}

/// A glued rational literal — a faithful mirror of Maude's `Token::looksLikeRational` (`token.cc`): an
/// optional leading `-`, a numerator (digits; a `0` numerator only as the unsigned `0/n`, never `-0/n`
/// or `00/n`), a `/`, then a denominator that is digits with a nonzero leading digit (`den >= 1`, no
/// leading zero). Examples: `1/6`, `2/4`, `-7/3`, `0/5`. Rejected: `1/0`, `1/06`, `-0/3`, `00/3`, `1/6/7`.
fn is_rational_literal(text: &str) -> bool {
    let (neg, rest) = match text.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, text),
    };
    let Some((num, den)) = rest.split_once('/') else { return false };
    // Numerator: all digits, non-empty; a `0` numerator is allowed only unsigned and only as exactly `0`.
    if num.is_empty() || !num.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    if num.bytes().next() == Some(b'0') && (neg || num.len() != 1) {
        return false;
    }
    // Denominator: all digits, non-empty, with a nonzero leading digit (>= 1, no leading zero) and no
    // further `/`.
    !den.is_empty()
        && den.bytes().all(|b| b.is_ascii_digit())
        && den.as_bytes()[0] != b'0'
}

/// An `iter`-symbol input token `f^count` — a faithful mirror of Maude's `ITER_SYMBOL` branch of
/// `Token::computeSpecialProperty` (`token.cc`): a non-empty operator-name prefix, a `^`, then a
/// maximal run of trailing digits whose first digit is nonzero (so `f^0`/`f^01` are *not* iter tokens).
/// The prefix may itself contain `_` (`s_^10`). `k` may be a bignum (`s_^18446744073709551616`).
fn is_iter_token(text: &str) -> bool {
    let Some((prefix, digits)) = text.rsplit_once('^') else { return false };
    !prefix.is_empty()
        && !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.as_bytes()[0] != b'0'
}

/// A negative-integer literal: a `-` glued to one or more digits with a nonzero magnitude — Maude's
/// `SMALL_NEG` (`mpz_set_str(s, 10)` succeeds and is `< 0`). `-1.5` has a `.` and is classified as a Float
/// first; `-0`/`-00` (magnitude zero) is excluded — `0` is solely the declared zero constant (Maude maps
/// it to `ZERO`), and a glued `-0` is a degenerate input.
fn is_neg_integer(text: &str) -> bool {
    let Some(digits) = text.strip_prefix('-') else { return false };
    !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.bytes().any(|b| b != b'0')
}

/// A float literal — a faithful mirror of Maude's `looksLikeFloat` (`Utility/macros.cc`), so the lexer
/// accepts exactly the forms the term builder can `float(String)`: an optional sign, then either
/// `Infinity` or a mantissa/exponent that carries at least one digit AND a `.` or an `[eE]` exponent.
/// Accepted: `1.5`, `-1.5`, `5.0e-1`, `2.0E+3`, and the abbreviated forms `1.`, `.5`, `1.e3`, `.5e2`,
/// `1e3`, `Infinity`. Rejected (fall through to `Ident`, no parse — as Maude rejects them): a dangling
/// exponent `1.5e`, a lone `.`, and a bare integer numeral `5` (that is a `Number`, handled earlier in
/// [`classify`]). Tokens are whitespace-delimited, so `5.0 - 1.5` keeps `-` as its own token; only a
/// sign written *attached* to the number (`-1.5`) reaches `classify` as a single token, as in Maude.
fn is_float_literal(text: &str) -> bool {
    let t = text.strip_prefix(['+', '-']).unwrap_or(text);
    if t == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match t.split_once(['e', 'E']) {
        Some((m, e)) => (m, Some(e)),
        None => (t, None),
    };
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, Some(f)),
        None => (mantissa, None),
    };
    let all_digits = |p: &str| p.bytes().all(|b| b.is_ascii_digit());
    if !all_digits(int_part) || !frac_part.is_none_or(all_digits) {
        return false;
    }
    // At least one digit somewhere in the mantissa…
    if int_part.is_empty() && frac_part.is_none_or(str::is_empty) {
        return false;
    }
    // …and a `.` or an exponent to make it a float rather than an integer numeral. A present exponent
    // must itself carry digits (a dangling `1.5e` is not a float).
    match exponent {
        Some(e) => {
            let e = e.strip_prefix(['+', '-']).unwrap_or(e);
            !e.is_empty() && all_digits(e)
        }
        None => frac_part.is_some(),
    }
}

/// Tokenize Maude source into a [`Token`] stream (interning into `interner`). Handles whitespace, `***`/
/// `---` line comments, the splitting punctuation, string literals, the terminator `.`, and maudeIds with
/// backquote escaping.
pub fn tokenize(src: &str, interner: &mut Interner) -> Vec<Token> {
    // Guarantee the two mixfix fragment chars the `omod` class-desugaring splices into synthesized
    // attribute-operator names (`bal` + `:` + `_` → `bal :_`) are interned, so the surface parser (which
    // holds only `&Interner`) can look them up via `Interner::get`. The `:` separator is present in any
    // real module (every op/var declaration), but the `_` hole may legitimately be absent from an object
    // module's source — its objects are written `< O : C | ... >`, never a bare `_`.
    interner.intern(":");
    interner.intern("_");

    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0;
    let mut line = 1u32;
    let mut out = Vec::new();

    while i < n {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // `***` / `---` comments. If the first non-blank character after the marker is `(`, it is a
        // **bracketed** comment `***( … )` that runs until its parentheses balance — across newlines
        // (Maude's `eatComment` parenMode, `lexerAux.cc`); a backquoted paren does not count. Otherwise it
        // is a line comment to end of line. (The `***>`/`--->` echo forms have `>` as the first character,
        // so they fall through to the line-comment case — never bracketed — just as in Maude.)
        let is_comment = |k: char| {
            chars[i] == k && chars.get(i + 1) == Some(&k) && chars.get(i + 2) == Some(&k)
        };
        if is_comment('*') || is_comment('-') {
            i += 3;
            let mut j = i;
            while matches!(chars.get(j), Some(' ') | Some('\t') | Some('\r')) {
                j += 1;
            }
            if chars.get(j) == Some(&'(') {
                i = j;
                let (mut depth, mut bq) = (0u32, false);
                while i < n {
                    let ch = chars[i];
                    if ch == '\n' {
                        line += 1;
                    }
                    if !bq && ch == '(' {
                        depth += 1;
                    } else if !bq && ch == ')' {
                        depth -= 1;
                        if depth == 0 {
                            i += 1;
                            break;
                        }
                    }
                    bq = !bq && ch == '`';
                    i += 1;
                }
            } else {
                while i < n && chars[i] != '\n' {
                    i += 1;
                }
            }
            continue;
        }
        if is_punct(c) {
            let sym = interner.intern(&c.to_string());
            out.push(Token { sym, line, kind: TokKind::Punct });
            i += 1;
            continue;
        }
        if c == '.' && is_terminator_dot(&chars, i) {
            let sym = interner.intern(".");
            out.push(Token { sym, line, kind: TokKind::Dot });
            i += 1;
            continue;
        }
        // A maudeId: a run of non-whitespace, non-punctuation chars (with backquote escaping), stopping at
        // a terminator `.`. A string literal `"…"` is a `normal` char in Maude's grammar (`lexer.ll`), so
        // it is consumed *into* the maudeId — a glued `foo"bar"`/`"x"y` stays one token; classify then
        // sorts a lone-string token (`"hi"`) into `Str` and a glued one into `Ident`.
        let mut text = String::new();
        while i < n {
            let ch = chars[i];
            // A string literal is a `normal`: consume the whole `"…"` (with `\`-escapes) and keep scanning,
            // so it glues into the surrounding maudeId rather than splitting it (`a"b"c`, `"x"y` = 1 token).
            if ch == '"' {
                text.push(ch);
                i += 1;
                while i < n && chars[i] != '"' {
                    if chars[i] == '\\' && i + 1 < n {
                        text.push(chars[i]);
                        text.push(chars[i + 1]);
                        i += 2;
                    } else {
                        if chars[i] == '\n' {
                            line += 1;
                        }
                        text.push(chars[i]);
                        i += 1;
                    }
                }
                if i < n {
                    text.push(chars[i]); // closing quote
                    i += 1;
                }
                continue;
            }
            // A structured-sort colon variable keeps its braces in one token: `L:List{Nat}` (and the chained
            // `X:Box{ToT2}{C2}`) — consume the balanced `{ … }` group rather than letting `{` split it off.
            if ch == '{' && colon_var_shape(&text) {
                let mut depth = 0u32;
                while i < n {
                    let cj = chars[i];
                    if cj == '\n' {
                        line += 1;
                    }
                    text.push(cj);
                    i += 1;
                    match cj {
                        '{' => depth += 1,
                        '}' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                continue;
            }
            if ch.is_whitespace() || is_punct(ch) {
                break;
            }
            if ch == '.' && is_terminator_dot(&chars, i) {
                break;
            }
            if ch == '`' && i + 1 < n {
                let next = chars[i + 1];
                // A backquote before a *split* char (`_`/`:`/punct) escapes it: the char joins this token
                // as a literal (a `` `[ `` bracket, a `` `, `` comma), so drop the backquote — its only role
                // was to suppress the split.
                if next == '_' || next == ':' || is_punct(next) {
                    text.push(next);
                    i += 2;
                    continue;
                }
                // A backquote before a *normal* char is an inter-token blank (Maude's op-name spacing).
                // Inside a quoted identifier (`'`…) it is kept as content — `` 'c`d_ `` is one Qid — so a
                // spelled-out multi-token Qid round-trips through the meta level. In a *bare* identifier it
                // *separates* two tokens (`` hello`world `` ≡ the name `hello world`), exactly like a space:
                // end this token here and resume scanning at the next char, so a term written either way
                // (`hello world` or `` hello`world ``) tokenizes the same.
                if text.starts_with('\'') {
                    text.push('`');
                    text.push(next);
                    i += 2;
                    continue;
                }
                i += 1; // consume the separating blank
                if text.is_empty() {
                    continue; // a leading blank: nothing to emit yet, keep scanning
                }
                break; // emit the token so far; the next token starts at `next`
            }
            text.push(ch);
            i += 1;
        }
        let kind = classify(&text);
        let sym = interner.intern(&text);
        out.push(Token { sym, line, kind });
    }
    out
}

/// A fragment of an operator's mixfix syntax: a literal name fragment, or an argument hole (`_`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Frag {
    /// A literal name fragment (interned).
    Tok(Sym),
    /// An argument position (`_`).
    Hole,
}

/// Split an operator name's text into mixfix fragments at `_`: `_+_` → `[Hole, +, Hole]`; `s_` →
/// `[s, Hole]`; `if_then_else_fi` → `[if, Hole, then, Hole, else, Hole, fi]`; a bare `gcd` → `[gcd]`
/// (prefix-only). (A name whose tokens are split by punctuation — e.g. `<_,_>`, split at `,` — is
/// assembled by the surface parser from the per-token results; B4.5.)
pub fn split_mixfix(name: &str, interner: &mut Interner) -> Vec<Frag> {
    let mut frags = Vec::new();
    let mut pending = String::new();
    let mut chars = name.chars().peekable();
    while let Some(ch) = chars.next() {
        // A backquote before a *split* char (`_`/`:`/punct) escapes it — a *literal* part of the
        // surrounding token, so `` _`[_ `` is one bracket op, not a structural `[`. A backquote before a
        // *normal* char is an inter-token blank (Maude's op-name spacing, `` c`d_ ``): it ends the current
        // literal fragment, and the next char starts a fresh one — this is what recovers a multi-token name
        // like `c d_` → `c`, `d`, `_` (rather than merging to the single literal `cd_`).
        if ch == '`' {
            match chars.peek() {
                Some(&next) if next == '_' || next == ':' || is_punct(next) => {
                    chars.next();
                    pending.push(next);
                }
                _ => {
                    if !pending.is_empty() {
                        frags.push(Frag::Tok(interner.intern(&pending)));
                        pending.clear();
                    }
                }
            }
            continue;
        }
        // A hole (`_`) or a punctuation char (`( ) [ ] { } ,`) ends the pending literal and becomes its
        // own fragment. Splitting on punctuation — like the main lexer — is what makes an op name whose
        // tokens glue punctuation to text (`_=[_]_` → `= [ ]`) align with how a *term* tokenizes (`=[Z]`
        // lexes as `= [ Z ]`); without it the grammar terminal `=[` could never match.
        //
        // `:` splits too — but unlike punctuation it is *not* split by the main lexer (so `X:Nat` stays
        // one colon-variable token). The asymmetry is deliberate: an op name's `:` is a syntactic
        // separator that is always written space-delimited (`bal :_`, `<_:_|_>`), so in a *term* it is
        // its own token (`bal : n0` → `bal`, `:`, `n0` — `bal:n0` with no space would be a variable).
        // The name's tokens, however, get concatenated into the canonical string (`[bal][:_]` → `bal:_`),
        // gluing the `:` to `bal`; splitting it back out here makes the grammar terminal `:` match the
        // term's standalone `:` (object/message attribute ops `bal :_`/`turns :_`, Pillar 2.5).
        if ch == '_' || ch == ':' || is_punct(ch) {
            if !pending.is_empty() {
                frags.push(Frag::Tok(interner.intern(&pending)));
                pending.clear();
            }
            if ch == '_' {
                frags.push(Frag::Hole);
            } else if ch == ':' {
                // A maximal run of `:` is ONE maudeId token in the main lexer (`::` in `X :: Y`),
                // so it must be one fragment here too — split per-char, `_::_`'s two `:` fragments
                // could never match a term's single `::` token, and printed with an inner space.
                let mut run = String::from(":");
                while chars.peek() == Some(&':') {
                    chars.next();
                    run.push(':');
                }
                frags.push(Frag::Tok(interner.intern(&run)));
            } else {
                frags.push(Frag::Tok(interner.intern(ch.encode_utf8(&mut [0u8; 4]))));
            }
        } else {
            pending.push(ch);
        }
    }
    if !pending.is_empty() {
        frags.push(Frag::Tok(interner.intern(&pending)));
    }
    frags
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Decode a token stream to `(text, kind)` pairs for assertions.
    fn lex(src: &str) -> (Interner, Vec<(String, TokKind)>) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let decoded = toks.iter().map(|t| (t.text(&i).to_string(), t.kind)).collect();
        (i, decoded)
    }

    #[test]
    fn splits_on_whitespace_and_punctuation() {
        let (_i, t) = lex("op _+_ : Nat Nat -> Nat .");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["op", "_+_", ":", "Nat", "Nat", "->", "Nat", "."]);
        assert_eq!(t.last().unwrap().1, TokKind::Dot, "trailing . is the terminator");
    }

    /// A structured-sort colon variable keeps its braces in one token (`L:List{Nat}`, and the chained
    /// `X:Box{A}{B}`), so it matches the `ColonVar` grammar terminal — but a *plain* structured sort
    /// (`List{Nat}`, no colon) still splits on the braces. `N:Nat` (unstructured) is one token as before.
    #[test]
    fn structured_colon_variable_is_one_token() {
        let (_i, t) = lex("hd(c(N:Nat, L:List{Nat}), X:Box{A}{B}) List{Nat}");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, [
            "hd", "(", "c", "(", "N:Nat", ",", "L:List{Nat}", ")", ",", "X:Box{A}{B}", ")",
            // a plain structured sort (no colon) is unaffected — still `List { Nat }`.
            "List", "{", "Nat", "}",
        ]);
        assert_eq!(t[6].1, TokKind::Ident, "the colon-var token classifies as an identifier");
    }

    /// A bracketed comment `***( … )` / `---( … )` (the first non-blank after the marker is `(`) runs until
    /// its parentheses balance — across newlines, with backquoted parens not counting; a plain `***`/`---`
    /// comment runs to end of line. (Maude's `eatComment` parenMode.)
    #[test]
    fn bracketed_and_line_comments() {
        let texts = |s| {
            let (_i, t) = lex(s);
            t.into_iter().map(|(x, _)| x).collect::<Vec<_>>()
        };
        assert_eq!(texts("a\n***( c1\nc2 )\nb"), ["a", "b"]); // multi-line bracketed
        assert_eq!(texts("a ***(x) b"), ["a", "b"]); // `***(` with no space
        assert_eq!(texts("a *** line ( unbalanced\nb"), ["a", "b"]); // line comment: `(` ignored
        assert_eq!(texts("a ***( p `) q ) b"), ["a", "b"]); // a backquoted `)` does not close early
        assert_eq!(texts("a ---> echo ( x\nb"), ["a", "b"]); // `--->` echo form is a line comment
    }

    #[test]
    fn prefix_application_punctuation() {
        let (_i, t) = lex("gcd(12, 18)");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["gcd", "(", "12", ",", "18", ")"]);
        assert_eq!(t[2].1, TokKind::Number); // 12
    }

    #[test]
    fn classifies_literals() {
        let (_i, t) = lex(r#"0 42 1.5 "abc" 'foo s_"#);
        let kinds: Vec<TokKind> = t.iter().map(|(_, k)| *k).collect();
        use TokKind::*;
        assert_eq!(kinds, [Number, Number, Float, Str, Qid, Ident]);
        assert_eq!(t[3].0, "\"abc\"", "the string keeps its quotes");
    }

    /// Maude's grammar admits a string literal as a `normal` char (`lexer.ll`: `normal = […|{string}]`),
    /// so a string can be glued INTO a maudeId — `a"b"c`, `foo"bar"`, `"x"y` are each ONE identifier
    /// token, while a bare `"hello"`/`""` is a `Str` constant (its unescaped close-quote is the last char —
    /// `Token::computeSpecialProperty`, `token.cc:478`). Verified byte-identical to the reference binary:
    /// `op a"b"c : -> S .` ⇒ `result S: a"b"c`. Bare strings around space/paren/comma still split.
    #[test]
    fn string_glued_into_identifier() {
        use TokKind::*;
        let t = |s| lex(s).1;
        // A token that is exactly one string is `Str` (close-quote is the last char).
        assert_eq!(t(r#""hello""#), [("\"hello\"".into(), Str)]);
        assert_eq!(t(r#""""#), [("\"\"".into(), Str)], "the empty string is a Str");
        // A string glued into an identifier is ONE `Ident` token (Maude keeps the whole maudeId).
        assert_eq!(t(r#"a"b"c"#), [("a\"b\"c".into(), Ident)]);
        assert_eq!(t(r#"foo"bar""#), [("foo\"bar\"".into(), Ident)]);
        assert_eq!(t(r#""x"y"#), [("\"x\"y".into(), Ident)], "leading string + glued suffix = Ident");
        // An escaped quote inside the string does not end it; the trailing `"` does.
        assert_eq!(t(r#""a\"b""#), [("\"a\\\"b\"".into(), Str)]);
        // Bare strings separated by space/paren/comma still split (the only form real specs use).
        assert_eq!(t(r#"len("hello")"#), [
            ("len".into(), Ident),
            ("(".into(), Punct),
            ("\"hello\"".into(), Str),
            (")".into(), Punct),
        ]);
        // `"ab" . "cd"` is `_._` String concat: the middle `.` (followed by `"cd"`, not a keyword) is an
        // ordinary `Ident` operator token, not a terminator — exactly as in `red "ab" . "cd" .`.
        assert_eq!(t(r#""ab" . "cd""#), [
            ("\"ab\"".into(), Str),
            (".".into(), Ident),
            ("\"cd\"".into(), Str),
        ]);
    }

    /// Leading-zero numerals stay the broad `Number` kind. `classify` assigns `Number` to *every*
    /// all-digit run (`0`, `00`, `01`, `007`, `123`) — mirroring Maude's two-stage design: flex first
    /// lexes `00`/`01` as a single identifier (`maudeId`) token, and the term parser *then* re-classifies
    /// it by text via `Token::specialProperty` (`mpz_set_str(text, 10)` → `ZERO` / `SMALL_NAT`). The
    /// ZERO-vs-SMALL_NAT split — so `0` is the zero constant, all-zero runs `00`/`000` fail to parse, and
    /// `01`/`007` reduce to the numbers `1`/`7` with leading zeros stripped — is reproduced *downstream*
    /// at the grammar terminal (`cfparser/earley.rs`: `SmallNat` matches a `Number` token only when it has
    /// a non-zero digit). Reclassifying a leading-zero run as `Ident` *here* would regress `01`→1 / `007`→7,
    /// which the reference binary accepts. (Differentially verified vs `~/Downloads/Maude-3/maude`.)
    #[test]
    fn leading_zero_numerals_stay_number() {
        use TokKind::*;
        assert_eq!(classify("0"), Number, "the bare zero constant");
        assert_eq!(classify("00"), Number, "all-zero run: Number here; rejected at the grammar terminal");
        assert_eq!(classify("000"), Number);
        assert_eq!(classify("01"), Number, "leading-zero numeral: Number, becomes `1` (zeros stripped)");
        assert_eq!(classify("007"), Number);
        assert_eq!(classify("123"), Number);
        // A glued negative-zero is not a numeral at all — Maude excludes it (`-0` → no parse) and so do we.
        assert_eq!(classify("-0"), Ident);
    }

    #[test]
    fn dot_inside_float_is_not_a_terminator() {
        let (_i, t) = lex("red 1.5 .");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["red", "1.5", "."]);
        assert_eq!(t[1].1, TokKind::Float);
        assert_eq!(t[2].1, TokKind::Dot);
    }

    /// Signed/exponent float literals and glued negative integers (`SMALL_NEG`). A `-` glued to a numeral
    /// is part of the literal token (`-1.5` Float, `-7` NegNumber); a *spaced* `-` stays its own token, so
    /// binary subtraction (`5.0 - 1.5`, `5 - 7`) is unaffected — and `5 -7` fails to parse just as Maude
    /// rejects it. (Float gap found by the whole-conformance-suite sweep; C10 added the integer case.)
    #[test]
    fn signed_and_exponent_floats() {
        assert_eq!(classify("-1.5"), TokKind::Float);
        assert_eq!(classify("+0.25"), TokKind::Float);
        assert_eq!(classify("5.0e-1"), TokKind::Float);
        assert_eq!(classify("2.0E+3"), TokKind::Float);
        assert_eq!(classify("4.0"), TokKind::Float);
        // A dotless `-N` is a negative-integer literal (Maude's `SMALL_NEG`), not a float.
        assert_eq!(classify("-3"), TokKind::NegNumber, "`-3` is a SMALL_NEG, parsed via the `-_` op");
        assert_eq!(classify("-7"), TokKind::NegNumber);
        assert_eq!(classify("-0"), TokKind::Ident, "`-0` (magnitude zero) is not SMALL_NEG");
        // Abbreviated float forms Maude's `looksLikeFloat` ACCEPTS (verified against Maude 3.5.1:
        // `reduce in FLOAT : 1. .` → `result FiniteFloat: 1.0`, `.5` → `5.0e-1`, `1.e3`/`1e3` → `1.0e+3`,
        // `.5e2` → `5.0e+1`, `Infinity` → `result Float: Infinity`). The prior pins asserted Maude
        // rejected `1.`/`.5` — it does not (fable-audit.md §3.4, roadmap C1c).
        assert_eq!(classify("1."), TokKind::Float);
        assert_eq!(classify(".5"), TokKind::Float);
        assert_eq!(classify("1.e3"), TokKind::Float);
        assert_eq!(classify(".5e2"), TokKind::Float);
        assert_eq!(classify("1e3"), TokKind::Float);
        assert_eq!(classify("Infinity"), TokKind::Float);
        assert_eq!(classify("-Infinity"), TokKind::Float, "signed Infinity");
        // …and the forms it still REJECTS (verified: `1.5e` → `bad token 1.5e`, lone `.` → parse error).
        assert_eq!(classify("1.5e"), TokKind::Ident, "a dangling exponent is not a float");
        assert_eq!(classify("."), TokKind::Ident, "a lone dot is not a float");
        assert_eq!(classify("5"), TokKind::Number, "a bare integer numeral is a Number, not a Float");
        // `5.0 - 1.5` keeps the spaced `-` as a separate Ident token (binary minus).
        let (_i, t) = lex("5.0 - 1.5");
        let decoded: Vec<(&str, TokKind)> = t.iter().map(|(s, k)| (s.as_str(), *k)).collect();
        assert_eq!(decoded, [("5.0", TokKind::Float), ("-", TokKind::Ident), ("1.5", TokKind::Float)]);
        // A glued `-7` is one `NegNumber` token; a spaced `- 7` and `5 - 7` keep `-` separate. So `5 -7`
        // lexes as `5`, `-7` (which then fails to parse, exactly as the reference binary rejects it).
        let toks = |s| lex(s).1;
        assert_eq!(toks("-7 quo 2"), [("-7".into(), TokKind::NegNumber), ("quo".into(), TokKind::Ident), ("2".into(), TokKind::Number)]);
        assert_eq!(toks("5 -7"), [("5".into(), TokKind::Number), ("-7".into(), TokKind::NegNumber)]);
        assert_eq!(toks("5 - 7"), [("5".into(), TokKind::Number), ("-".into(), TokKind::Ident), ("7".into(), TokKind::Number)]);
    }

    #[test]
    fn comments_skipped_and_lines_tracked() {
        let mut i = Interner::new();
        let toks = tokenize("a *** comment\nb --- another\nc", &mut i);
        let texts: Vec<&str> = toks.iter().map(|t| t.text(&i)).collect();
        assert_eq!(texts, ["a", "b", "c"]);
        assert_eq!((toks[0].line, toks[1].line, toks[2].line), (1, 2, 3));
    }

    #[test]
    fn op_name_splitting() {
        let mut i = Interner::new();
        let frag = |name: &str, i: &mut Interner| {
            split_mixfix(name, i)
                .iter()
                .map(|f| match f {
                    Frag::Hole => "_".to_string(),
                    Frag::Tok(s) => i.resolve(*s).to_string(),
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(frag("_+_", &mut i), ["_", "+", "_"]);
        assert_eq!(frag("s_", &mut i), ["s", "_"]);
        assert_eq!(frag("-_", &mut i), ["-", "_"]);
        assert_eq!(frag("_<=_", &mut i), ["_", "<=", "_"]);
        assert_eq!(frag("if_then_else_fi", &mut i), ["if", "_", "then", "_", "else", "_", "fi"]);
        assert_eq!(frag("gcd", &mut i), ["gcd"], "a bare identifier is prefix-only");
    }
}
