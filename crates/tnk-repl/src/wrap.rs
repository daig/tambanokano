//! Fixed-width output wrapping with four-space continuation indentation. Breaks occur only at legal ASCII
//! positions and never inside string literals or ANSI color sequences.
//!
//! Width is measured per byte, so a multibyte UTF-8 character occupies multiple columns. Oversized tokens
//! are emitted intact. Breaks occur only at ASCII boundaries, preserving valid UTF-8 output.

/// Noninteractive wrap width; content may occupy 79 columns before the right margin.
const LINE_WIDTH: i32 = 80;
/// Continuation-line indentation.
const LEFT_MARGIN: i32 = 4;
/// Columns reserved at the right edge.
const RIGHT_MARGIN: i32 = 1;
/// `pending_width` sentinel: not currently buffering (no legal break position is pending).
const UNDEFINED: i32 = -1;

/// Wrap using the fixed noninteractive width without terminal detection.
pub fn auto_wrap(input: &str) -> String {
    let mut w = Wrapper::default();
    for &b in input.as_bytes() {
        w.byte(b);
    }
    w.finish()
}

/// Wrapping state machine. `pending` holds bytes seen since the last legal break position; at the next
/// legal position, [`decide_on_break`](Self::decide_on_break) either emits them in place or inserts a
/// newline and indentation before them when they would overrun the right margin.
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
    /// Emit the pending bytes, keeping buffering off until it is restarted.
    fn dump_buffer(&mut self) {
        self.out.extend_from_slice(&self.pending);
        self.pending.clear();
    }

    /// Handle a `\t` or ESC byte: buffer it when buffering is active, but do not count it toward width.
    fn handle_escape_char(&mut self, ch: u8) {
        if self.pending_width == UNDEFINED {
            self.out.push(ch);
        } else {
            self.pending.push(ch);
        }
    }

    /// Buffer printable bytes until a legal break. Oversized indivisible tokens are emitted intact.
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

    /// At a legal break position, move the pending run to a new indented line if emitting it in place
    /// would overrun the right margin.
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

    /// Mark a legal newline position and start buffering.
    fn legal_position_to_break(&mut self) {
        self.pending_width = 0;
        self.cursor = self.cursor.rem_euclid(LINE_WIDTH);
    }

    /// Process one output byte.
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
        // `normal` means the byte is ordinary content; structural branches leave it false.
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

    /// Flush the final pending run without appending a newline.
    fn finish(mut self) -> String {
        self.decide_on_break();
        String::from_utf8(self.out).expect("wrap inserts breaks only at ASCII boundaries")
    }
}

/// Printable ASCII byte predicate. High and control bytes end string mode.
fn is_print(ch: u8) -> bool {
    (0x20..=0x7e).contains(&ch)
}

/// Round up to the next eight-column tab stop.
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

    /// Wrapped lines fit the 79-column content width and continuations carry four spaces.
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
