//! The `tnk-repl` binary loads the optional prelude and input file, then feeds terminal or piped stdin
//! through `rustyline`, buffering multiline submissions until complete.

use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;
use std::io::IsTerminal;
use std::process::ExitCode;
use tnk_repl::Repl;

#[derive(Debug, Default, PartialEq, Eq)]
struct Options {
    no_prelude: bool,
    no_banner: bool,
    file: Option<String>,
}

fn parse_args(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let mut options = Options::default();
    for arg in args {
        match arg.as_str() {
            "-no-prelude" => options.no_prelude = true,
            "-no-banner" => options.no_banner = true,
            other if other.starts_with('-') => {
                return Err(format!("unknown option `{other}`"));
            }
            other if options.file.is_none() => options.file = Some(other.to_string()),
            other => {
                return Err(format!(
                    "unexpected argument `{other}`; only one input file is supported"
                ));
            }
        }
    }
    Ok(options)
}

fn main() -> ExitCode {
    let options = match parse_args(std::env::args().skip(1)) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("error: {error}");
            return ExitCode::from(2);
        }
    };
    match run(options) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(options: Options) -> Result<(), String> {
    let file_source = options
        .file
        .as_ref()
        .map(|path| {
            std::fs::read_to_string(path).map_err(|error| format!("reading `{path}`: {error}"))
        })
        .transpose()?;
    let prelude_source = if options.no_prelude {
        None
    } else {
        match find_prelude() {
            Some(path) => Some(
                std::fs::read_to_string(&path)
                    .map_err(|error| format!("reading prelude `{}`: {error}", path.display()))?,
            ),
            None => {
                eprintln!(
                    "warning: prelude.maude not found (set MAUDE_LIB or use -no-prelude); continuing without"
                );
                None
            }
        }
    };

    let stdin_is_terminal = std::io::stdin().is_terminal();
    let mut repl = Repl::new(std::io::stdout().is_terminal());
    if !options.no_banner {
        println!(
            "tambanokano REPL — enter modules, `reduce`/`match`, `show`/`select`; `quit` to exit."
        );
    }
    if let Some(source) = prelude_source {
        print_nonempty(&repl.eval(&source).output);
    }
    if let Some(source) = file_source {
        print_nonempty(&repl.eval(&source).output);
    }

    let mut rl = DefaultEditor::new().map_err(|error| error.to_string())?;
    let mut buffer = String::new();
    loop {
        let prompt = if !stdin_is_terminal {
            ""
        } else if buffer.is_empty() {
            "tnk> "
        } else {
            "   > "
        };
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
            Err(ReadlineError::Interrupted) => buffer.clear(),
            Err(ReadlineError::Eof) => break,
            Err(error) => return Err(error.to_string()),
        }
    }
    Ok(())
}

/// Finds `prelude.maude` in the platform path list from `MAUDE_LIB`, then in the current directory.
fn find_prelude() -> Option<std::path::PathBuf> {
    if let Some(lib) = std::env::var_os("MAUDE_LIB") {
        for dir in std::env::split_paths(&lib) {
            let path = dir.join("prelude.maude");
            if path.is_file() {
                return Some(path);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_supported_options_and_file() {
        assert_eq!(
            parse_args([
                "-no-banner".to_string(),
                "input.maude".to_string(),
                "-no-prelude".to_string(),
            ]),
            Ok(Options {
                no_prelude: true,
                no_banner: true,
                file: Some("input.maude".to_string()),
            })
        );
    }

    #[test]
    fn rejects_unknown_options_and_extra_files() {
        assert_eq!(
            parse_args(["-no-baner".to_string()]),
            Err("unknown option `-no-baner`".to_string())
        );
        assert_eq!(
            parse_args(["one.maude".to_string(), "two.maude".to_string()]),
            Err("unexpected argument `two.maude`; only one input file is supported".to_string())
        );
    }
}
