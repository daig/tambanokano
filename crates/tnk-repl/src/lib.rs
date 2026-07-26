//! `tnk-repl` — the terminal adapter over [`tnk_session::Session`].
//!
//! Semantic state, command evaluation, loading, reflection caches, and continuations live in
//! `tnk-session`. This crate owns only terminal-facing policy: color selection and Maude-compatible
//! output wrapping. The binary adds line editing, history, prompts, banners, and CLI arguments.

mod wrap;

pub use tnk_session::Eval;
use tnk_session::Session;

/// Thin terminal policy adapter around a reusable [`Session`].
pub struct Repl {
    session: Session,
    color: bool,
}

impl Repl {
    /// Create a terminal adapter. `color` is a host-selected rendering policy; the Session itself does
    /// not inspect terminal capabilities.
    pub fn new(color: bool) -> Self {
        Self {
            session: Session::new(),
            color,
        }
    }

    /// Provide scripted/piped input for `erewrite`'s `getLine` manager.
    pub fn set_stdin(&mut self, input: impl Into<String>) {
        self.session.set_stdin(input);
    }

    /// The current module name, for prompts and host introspection.
    pub fn current(&self) -> Option<&str> {
        self.session.current()
    }

    /// Evaluate one input submission and apply Maude's terminal output wrapper exactly once.
    pub fn eval(&mut self, input: &str) -> Eval {
        let mut result = self.session.eval(input, self.color);
        result.output = wrap::auto_wrap(&result.output);
        result
    }

    /// Whether an interactive input buffer is a complete top-level submission.
    pub fn input_complete(&mut self, input: &str) -> bool {
        self.session.input_complete(input)
    }
}

#[cfg(test)]
mod tests;
