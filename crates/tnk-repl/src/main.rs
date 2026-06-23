//! The `tnk-repl` binary: load an optional `.maude` file from `argv`, then drive [`Repl`] interactively
//! with `rustyline`, buffering multi-line input until it is complete.

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::io::IsTerminal;
use tnk_repl::Repl;

fn main() -> rustyline::Result<()> {
    // Colorize results only when stdout is a terminal (so piped/redirected output stays plain).
    let mut repl = Repl::new(std::io::stdout().is_terminal());
    println!("tambanokano REPL — enter modules, `reduce`/`match`, `show`/`select`; `quit` to exit.");

    // Optional file argument: load it (modules + commands), as `maude file.maude` does, then go interactive.
    if let Some(path) = std::env::args().nth(1) {
        match std::fs::read_to_string(&path) {
            Ok(src) => print_nonempty(&repl.eval(&src).output),
            Err(e) => eprintln!("error reading `{path}`: {e}"),
        }
    }

    let mut rl = DefaultEditor::new()?;
    let mut buffer = String::new();
    loop {
        let prompt = if buffer.is_empty() { "tnk> " } else { "   > " };
        match rl.readline(prompt) {
            Ok(line) => {
                buffer.push_str(&line);
                buffer.push('\n');
                if repl.input_complete(&buffer) {
                    let _ = rl.add_history_entry(buffer.trim());
                    let ev = repl.eval(&buffer);
                    buffer.clear();
                    print_nonempty(&ev.output);
                    if ev.exit {
                        break;
                    }
                }
            }
            Err(ReadlineError::Interrupted) => buffer.clear(), // Ctrl-C: abandon the current input
            Err(ReadlineError::Eof) => break,                  // Ctrl-D
            Err(e) => {
                eprintln!("error: {e}");
                break;
            }
        }
    }
    Ok(())
}

fn print_nonempty(s: &str) {
    if !s.is_empty() {
        println!("{s}");
    }
}
