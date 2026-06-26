//! Lexer: Maude tokenization + operator-name splitting.
//!
//! Maude tokens are separated by whitespace and by the **special-splitting** punctuation `( ) [ ] { } ,`
//! (each its own token); everything else (letters, digits, `+ - < = : _ .` …) is part of a *maudeId*. The
//! statement/command terminator `.` is a `.` followed by whitespace/EOF/punctuation — distinguished from a
//! `.` inside a float (`1.5`) or a structured sort. Strings are `"…"`, quoted-ids start with `'`, and a
//! backquote escapes a splitting char into a maudeId. (`lexer.ll` / `token.{hh,cc}` in the reference.)
//!
//! Tokens are interned ([`Interner`]) so equality is a `u32` compare. This slice is the functional-fragment
//! subset; bracketed comments (`***( … )`), LaTeX/file-name modes, and the lexer↔parser bubble handshake
//! (replaced by an explicit surface-parser API in B4.2) are follow-ups.

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
    /// A string literal `"…"`.
    Str,
    /// A float literal `[0-9]+.[0-9]+` (exponents are a follow-up).
    Float,
    /// A negative-integer literal `-[0-9]+` with a nonzero magnitude (Maude's `SMALL_NEG`): a `-` glued
    /// to digits, lexed as one token. `-1.5` is a Float (checked first); a *spaced* `-` stays its own
    /// token, so `5 - 7` is subtraction and `5 -7` fails to parse (just as in Maude).
    NegNumber,
    /// A quoted identifier `'…`.
    Qid,
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
fn is_punct(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',')
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

/// The class of a scanned maudeId text.
fn classify(text: &str) -> TokKind {
    if text.starts_with('\'') && text.len() > 1 {
        return TokKind::Qid;
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
    TokKind::Ident
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

/// A float literal: an optional leading sign, an integer part, `.`, a fraction, and an optional
/// exponent — `1.5`, `-1.5`, `5.0e-1`, `2.0E+3` (the forms Maude lexes and prints, e.g. `neg(1.5)`
/// reduces to the literal `-1.5`). Tokens are whitespace-delimited, so `5.0 - 1.5` keeps `-` as its own
/// token; only a sign written *attached* to the number (`-1.5`) reaches `classify` as a single token,
/// exactly as in Maude.
fn is_float_literal(text: &str) -> bool {
    let body = text.strip_prefix(['-', '+']).unwrap_or(text);
    let Some((int_part, rest)) = body.split_once('.') else { return false };
    let all_digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    if !all_digits(int_part) {
        return false;
    }
    // The fraction, optionally followed by an `[eE][-+]?digits` exponent.
    match rest.split_once(['e', 'E']) {
        None => all_digits(rest),
        Some((fraction, exp)) => {
            all_digits(fraction) && all_digits(exp.strip_prefix(['-', '+']).unwrap_or(exp))
        }
    }
}

/// Tokenize Maude source into a [`Token`] stream (interning into `interner`). Handles whitespace, `***`/
/// `---` line comments, the splitting punctuation, string literals, the terminator `.`, and maudeIds with
/// backquote escaping.
pub fn tokenize(src: &str, interner: &mut Interner) -> Vec<Token> {
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
        // `***` / `---` line comments → skip to end of line.
        let is_comment = |k: char| {
            chars[i] == k && chars.get(i + 1) == Some(&k) && chars.get(i + 2) == Some(&k)
        };
        if is_comment('*') || is_comment('-') {
            while i < n && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if is_punct(c) {
            let sym = interner.intern(&c.to_string());
            out.push(Token { sym, line, kind: TokKind::Punct });
            i += 1;
            continue;
        }
        if c == '"' {
            let start = i;
            i += 1;
            while i < n && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < n {
                    i += 2;
                } else {
                    if chars[i] == '\n' {
                        line += 1;
                    }
                    i += 1;
                }
            }
            i += 1; // closing quote (or EOF)
            let text: String = chars[start..i.min(n)].iter().collect();
            let sym = interner.intern(&text);
            out.push(Token { sym, line, kind: TokKind::Str });
            continue;
        }
        if c == '.' && is_terminator_dot(&chars, i) {
            let sym = interner.intern(".");
            out.push(Token { sym, line, kind: TokKind::Dot });
            i += 1;
            continue;
        }
        // A maudeId: a run of non-whitespace, non-punctuation, non-`"` chars (with backquote escaping),
        // stopping at a terminator `.`.
        let mut text = String::new();
        while i < n {
            let ch = chars[i];
            if ch.is_whitespace() || is_punct(ch) || ch == '"' {
                break;
            }
            if ch == '.' && is_terminator_dot(&chars, i) {
                break;
            }
            if ch == '`' && i + 1 < n {
                text.push(chars[i + 1]); // backquote escapes the next char into the token
                i += 2;
                continue;
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
    for ch in name.chars() {
        if ch == '_' {
            if !pending.is_empty() {
                frags.push(Frag::Tok(interner.intern(&pending)));
                pending.clear();
            }
            frags.push(Frag::Hole);
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
        assert_eq!(classify("1."), TokKind::Ident);
        assert_eq!(classify(".5"), TokKind::Ident);
        assert_eq!(classify("1.5e"), TokKind::Ident);
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
