//! The surface layer: the fixed `.maude` top-level syntax (functional modules + commands) and its
//! recursive-descent parser, producing a [`Source`](ast::Source) of [`PreModule`](ast::PreModule)s whose
//! term-carrying parts are still raw token bubbles (parsed by the mixfix parser in B4.4).

pub mod ast;
pub mod parser;
