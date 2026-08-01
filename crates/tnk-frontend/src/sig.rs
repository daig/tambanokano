//! The signature layer: the frontend's **source of truth** for surface syntax + name→id resolution, and
//! the [`build_sig`](build_sig::build_module) pass that drives the `tnk-core` `Engine`'s constructor API
//! from a [`PreModule`](crate::surface::ast::PreModule). `tnk-core` stores no syntax, so the mixfix grammar
//! and pretty-printer read these tables instead of the kernel.

pub mod build_sig;
pub mod syntax;
