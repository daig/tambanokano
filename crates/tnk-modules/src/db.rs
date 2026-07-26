//! The module database: parsed [`PreModule`]s keyed by name, the input to [`flatten`](crate::flatten).
//!
//! For B5 this is built once from a loaded source; the REPL (next round) will hold it and insert modules
//! incrementally, re-flattening importers on demand.

use std::collections::HashMap;
use tnk_frontend::surface::ast::PreModule;

/// A name → [`PreModule`] table. Names are the surface module names (`fmod NAME is …`).
#[derive(Debug, Default, Clone)]
pub struct ModuleDb {
    modules: HashMap<String, PreModule>,
}

impl ModuleDb {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a module (overwriting any previous module of the same name, as the REPL re-entering a
    /// module would).
    pub fn insert(&mut self, pm: PreModule) {
        self.modules.insert(pm.name.clone(), pm);
    }

    pub fn get(&self, name: &str) -> Option<&PreModule> {
        self.modules.get(name)
    }

    /// Build a database from the modules of a parsed source (file order; later definitions win on a name
    /// clash).
    pub fn from_modules(modules: impl IntoIterator<Item = PreModule>) -> Self {
        let mut db = Self::new();
        for pm in modules {
            db.insert(pm);
        }
        db
    }
}
