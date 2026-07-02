//! The `tnk-repl` binary: load an optional `.maude` file from `argv`, then drive [`Repl`] interactively
//! with `rustyline`, buffering multi-line input until it is complete.

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::io::IsTerminal;
use tnk_repl::Repl;

fn main() -> rustyline::Result<()> {
    // Flags (decision D11): `-no-prelude` skips the standing prelude, `-no-banner` the banner
    // line; the first non-flag argument is the file to load (as `maude file.maude` does).
    let mut no_prelude = false;
    let mut no_banner = false;
    let mut file: Option<String> = None;
    for a in std::env::args().skip(1) {
        match a.as_str() {
            "-no-prelude" => no_prelude = true,
            "-no-banner" => no_banner = true,
            other if file.is_none() => file = Some(other.to_string()),
            other => eprintln!("ignoring extra argument `{other}`"),
        }
    }

    // Colorize results only when stdout is a terminal (so piped/redirected output stays plain).
    let mut repl = Repl::new(std::io::stdout().is_terminal());
    if !no_banner {
        println!("tambanokano REPL — enter modules, `reduce`/`match`, `show`/`select`; `quit` to exit.");
    }

    // Standing prelude (D11): load `prelude.maude` from `$MAUDE_LIB` (colon-separated dirs) or
    // the CWD. Its own `set include BOOL on` line then enables the implicit-BOOL auto-import.
    // The engine/library layer stays prelude-free — this is REPL plumbing only.
    if !no_prelude {
        match find_prelude() {
            Some(p) => match std::fs::read_to_string(&p) {
                Ok(src) => print_nonempty(&repl.eval(&src).output),
                Err(e) => eprintln!("error reading prelude `{}`: {e}", p.display()),
            },
            None => {
                eprintln!("no prelude.maude found (set MAUDE_LIB or use -no-prelude); continuing without");
            }
        }
    }

    // Optional file argument: load it (modules + commands), then go interactive.
    if let Some(path) = file {
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

/// `prelude.maude` from `$MAUDE_LIB` (colon-separated directories) or the current directory.
fn find_prelude() -> Option<std::path::PathBuf> {
    if let Ok(lib) = std::env::var("MAUDE_LIB") {
        for dir in lib.split(':').filter(|d| !d.is_empty()) {
            let p = std::path::Path::new(dir).join("prelude.maude");
            if p.is_file() {
                return Some(p);
            }
        }
    }
    let cwd = std::path::PathBuf::from("prelude.maude");
    cwd.is_file().then_some(cwd)
}

fn print_nonempty(s: &str) {
    if !s.is_empty() {
        println!("{s}");
    }
}
