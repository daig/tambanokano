//! Parsed modules keyed by name. Batch loading populates the table in source order; interactive sessions
//! update it incrementally and rebuild affected importers.

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

    /// Insert or replace a module by name.
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
