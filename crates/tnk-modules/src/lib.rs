//! `tnk-modules` — module/view storage, algebra, flattening, built-in module injection, and META-LEVEL
//! descent.
//!
//! [`ModuleDb`](db::ModuleDb) retains parsed modules. The flattener resolves imports, sums, renamings,
//! parameterized instantiations, and views into one [`PreModule`](tnk_frontend::surface::ast::PreModule)
//! for the frontend build pipeline. All import modes contribute the same flattened closure; their mode is
//! retained for non-flat reflection.
//! [`load::load_program`] builds a runnable program and is shared by batch loading and the session layer.

pub mod db;
pub mod flatten;
pub mod load;
pub mod meta;
pub mod prelude;
pub mod rename;
pub mod view;
