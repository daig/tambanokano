//! A port of Maude's `AutoWrapBuffer` (`IO_Stuff/autoWrapBuffer.{hh,cc}`) — the line-wrapper Maude
//! installs on stdout. Long output is broken across lines at a column limit, with wrapped continuation
//! lines indented by [`LEFT_MARGIN`] spaces; breaks land only at "legal positions" (a space, or just
//! after a `,([{`) and never inside a `"string"` or an `ESC … m` color sequence. Maude applies it to the
//! whole output stream, so our REPL applies it once at the [`eval`](crate::Repl::eval) boundary — making
//! our printed output byte-for-byte identical to `maude file.maude` even for a very long result (C13;
//! e.g. `fib(22)`'s 17711-successor numeral wraps to ~190 lines exactly as the reference does).
//!
//! Ported faithfully, including the per-byte width accounting (so a multibyte UTF-8 char counts as
//! several columns, as in Maude) and the "token too long to ever fit" hard-dump. Breaks are only ever
//! inserted at ASCII boundaries (before a buffered run that began after a space/`,([{`), so the wrapped
//! byte stream stays valid UTF-8.

/// Maude's `DEFAULT_COLUMNS` — the wrap width when stdout is not a terminal (the case differential
/// testing exercises: `maude file.maude` piped). A wrapped line is kept to `LINE_WIDTH - RIGHT_MARGIN`
/// (79) columns.
const LINE_WIDTH: i32 = 80;
/// Indent of a wrapped continuation line (`AutoWrapBuffer::LEFT_MARGIN`).
const LEFT_MARGIN: i32 = 4;
/// Columns kept clear at the right (`AutoWrapBuffer::RIGHT_MARGIN`): a line may fill to column
/// `LINE_WIDTH - RIGHT_MARGIN`.
const RIGHT_MARGIN: i32 = 1;
/// `pending_width` sentinel: not currently buffering (no legal break position is pending).
const UNDEFINED: i32 = -1;

/// Wrap `input` exactly as Maude's stdout `AutoWrapBuffer` would. Pure: no terminal-width detection (it
/// uses Maude's non-TTY default of 80, which is what the reference binary uses when its output is piped).
pub fn auto_wrap(input: &str) -> String {
    let mut w = Wrapper::default();
    for &b in input.as_bytes() {
        w.byte(b);
    }
    w.finish()
}

/// The streambuf state machine. `pending` holds bytes seen since the last legal break position; once a
/// further legal position is reached, [`decide_on_break`](Self::decide_on_break) either dumps them in
/// place or, if dumping would overrun the right margin, inserts a newline + indent *before* them.
struct Wrapper {
    out: Vec<u8>,
    /// Column the cursor would be at if `pending` were printed.
    cursor: i32,
    pending: Vec<u8>,
    /// Printable bytes in `pending` (excludes `\t`/ESC), or [`UNDEFINED`] when not buffering.
    pending_width: i32,
    in_string: bool,
    in_escape: bool,
    seen_backquote: bool,
    seen_backslash: bool,
}

impl Default for Wrapper {
    fn default() -> Self {
        Wrapper {
            out: Vec::new(),
            cursor: 0,
            pending: Vec::new(),
            pending_width: UNDEFINED,
            in_string: false,
            in_escape: false,
            seen_backquote: false,
            seen_backslash: false,
        }
    }
}

impl Wrapper {
    /// `AutoWrapBuffer::dumpBuffer` — emit the pending bytes, keeping buffering off until restarted.
    fn dump_buffer(&mut self) {
        self.out.extend_from_slice(&self.pending);
        self.pending.clear();
    }

    /// `AutoWrapBuffer::handleEscapeSequenceChar` — a `\t`/ESC byte: buffered (if buffering) but not
    /// counted toward the width.
    fn handle_escape_char(&mut self, ch: u8) {
        if self.pending_width == UNDEFINED {
            self.out.push(ch);
        } else {
            self.pending.push(ch);
        }
    }

    /// `AutoWrapBuffer::handleChar` — a printable byte: buffered and counted, or emitted directly when not
    /// buffering. A pending run that grows past what could *ever* fit on a fresh wrapped line is dumped
    /// and buffering disabled (a hard-wrapped token Maude does not try to avoid).
    fn handle_char(&mut self, ch: u8) {
        if self.pending_width == UNDEFINED {
            self.out.push(ch);
        } else {
            self.pending.push(ch);
            self.pending_width += 1;
            if self.pending_width > LINE_WIDTH - RIGHT_MARGIN - LEFT_MARGIN {
                self.dump_buffer();
                self.pending_width = UNDEFINED;
            }
        }
    }

    /// `AutoWrapBuffer::decideOnBreak` — at a fresh legal break position, decide whether the pending run
    /// should start a new (indented) line because dumping it in place would overrun the right margin.
    fn decide_on_break(&mut self) {
        if self.pending_width == UNDEFINED {
            return;
        }
        if self.cursor > LINE_WIDTH - RIGHT_MARGIN {
            self.out.push(b'\n');
            for _ in 0..LEFT_MARGIN {
                self.out.push(b' ');
            }
            self.cursor = LEFT_MARGIN;
            if !self.pending.is_empty() {
                let t = usize::from(self.pending[0] == b' '); // skip a leading space at a wrap
                if self.pending.len() - t > 0 {
                    let first = self.pending[0];
                    self.out.extend_from_slice(&self.pending[t..]);
                    if first == b'\t' {
                        self.cursor = next_tab(self.cursor) + self.pending_width;
                    } else {
                        self.cursor += self.pending_width - t as i32;
                    }
                }
                self.pending.clear();
            }
        } else {
            self.dump_buffer();
        }
        self.pending_width = UNDEFINED;
    }

    /// `AutoWrapBuffer::legalPositionToBreak` — mark that a `\n` could be inserted here; start buffering.
    fn legal_position_to_break(&mut self) {
        self.pending_width = 0;
        self.cursor = self.cursor.rem_euclid(LINE_WIDTH);
    }

    /// `AutoWrapBuffer::overflow` — process one output byte.
    fn byte(&mut self, ch: u8) {
        if self.in_escape {
            self.handle_escape_char(ch);
            if ch == b'm' {
                self.in_escape = false;
            }
            return;
        }
        if !is_print(ch) {
            self.in_string = false;
        }
        // `normal` replays Maude's `goto normal` (handle the byte as content); the special cases that
        // break out of the switch leave it false.
        let mut normal = false;
        match ch {
            b'"' => {
                if !self.seen_backslash {
                    self.in_string = !self.in_string;
                }
                normal = true;
            }
            0x1b => {
                self.in_escape = true;
                self.handle_escape_char(ch);
            }
            b'\n' => {
                self.decide_on_break();
                self.out.push(b'\n');
                self.cursor = 0;
            }
            b'\t' => {
                self.decide_on_break();
                self.legal_position_to_break();
                self.handle_escape_char(ch);
                self.cursor = next_tab(self.cursor);
            }
            b' ' => {
                if !self.in_string {
                    self.decide_on_break();
                    self.legal_position_to_break();
                }
                normal = true;
            }
            b',' | b'(' | b'[' | b'{' => {
                if !self.in_string && !self.seen_backquote {
                    // A `\n` may follow these: emit, then open a legal break position after.
                    self.handle_char(ch);
                    self.cursor += 1;
                    self.decide_on_break();
                    self.legal_position_to_break();
                } else {
                    normal = true; // backquoted / in-string: lose the special meaning
                }
            }
            _ => normal = true,
        }
        if normal {
            self.handle_char(ch);
            self.cursor += 1;
        }
        self.seen_backquote = ch == b'`';
        self.seen_backslash = self.in_string && !self.seen_backslash && ch == b'\\';
    }

    /// Flush at end-of-stream: Maude's result line ends with a `\n` whose `decideOnBreak` flushes (and
    /// possibly wraps) the final pending run; the REPL trims that trailing newline, so we reproduce the
    /// same break decision here without emitting the newline itself.
    fn finish(mut self) -> String {
        self.decide_on_break();
        String::from_utf8(self.out).expect("wrap inserts breaks only at ASCII boundaries")
    }
}

/// `isprint` for a byte (C locale): printable ASCII `0x20..=0x7e`. High/control bytes are non-printing,
/// which (matching Maude) drops us out of `"string"` mode.
fn is_print(ch: u8) -> bool {
    (0x20..=0x7e).contains(&ch)
}

/// `AutoWrapBuffer::nextTabPosition` — round up to the next 8-column tab stop.
fn next_tab(pos: i32) -> i32 {
    (pos + 8) & !7
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A short string never wraps.
    #[test]
    fn short_text_is_unchanged() {
        assert_eq!(auto_wrap("result Nat: s s s 0"), "result Nat: s s s 0");
        assert_eq!(auto_wrap(""), "");
        assert_eq!(auto_wrap("Bye."), "Bye.");
    }

    /// Every wrapped line stays within `LINE_WIDTH - RIGHT_MARGIN` (79) columns, and continuation lines
    /// carry the 4-space indent — the structural invariant of Maude's wrapper.
    #[test]
    fn wraps_at_seventy_nine_columns_with_indent() {
        let long = format!("result Nat: {}", "s ".repeat(200));
        let long = long.trim_end();
        let wrapped = auto_wrap(long);
        let lines: Vec<&str> = wrapped.split('\n').collect();
        assert!(lines.len() > 1, "a 400-token line must wrap");
        for (i, line) in lines.iter().enumerate() {
            assert!(
                line.len() <= 79,
                "line {i} is {} cols (> 79): {line:?}",
                line.len()
            );
            if i > 0 {
                assert!(
                    line.starts_with("    "),
                    "continuation line {i} is indented: {line:?}"
                );
            }
        }
        // Every `s` survives the wrap (only spaces are absorbed at break points, never content).
        assert_eq!(
            wrapped.matches('s').count(),
            long.matches('s').count(),
            "no successor lost"
        );
    }

    /// ANSI color escapes (`ESC … m`) are not counted toward the column width, so colored output wraps at
    /// the same *visible* positions as the uncolored form — stripping the escapes from the colored wrap
    /// reproduces the plain wrap exactly.
    #[test]
    fn ansi_escapes_do_not_count_toward_width() {
        let plain = format!("result Nat: {}", "s ".repeat(100));
        let plain = plain.trim_end();
        let colored = format!("result Nat: {}", "\x1b[33ms\x1b[0m ".repeat(100));
        let colored = colored.trim_end();
        assert_eq!(
            strip_ansi(&auto_wrap(colored)),
            auto_wrap(plain),
            "colored wraps at visible columns"
        );
    }

    fn strip_ansi(s: &str) -> String {
        let mut out = String::new();
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            if c == '\x1b' {
                for d in chars.by_ref() {
                    if d == 'm' {
                        break;
                    }
                }
            } else {
                out.push(c);
            }
        }
        out
    }

    /// Wrapping never breaks inside a quoted string even when it overflows the margin.
    #[test]
    fn does_not_break_inside_a_string() {
        let s = format!("result String: \"{}\"", "x".repeat(120));
        let wrapped = auto_wrap(&s);
        // The 120-x run is one unbreakable token (no space inside), so it stays on one physical line.
        assert_eq!(
            wrapped.matches('\n').count(),
            0,
            "no break inside the string: {wrapped:?}"
        );
    }
}
