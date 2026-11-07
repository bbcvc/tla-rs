//! Reads a spec and its model configuration as TLC does before it checks them: the modules from
//! the spec's directory and the library directories, TLC's order of the strings and of the
//! variables, and the Java classes beside the spec that override operators.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tla_tools_parser::ModelConfig;
use tla_tools_resolve::Spec;
pub use tla_tools_resolve::{ErrorKind, ResolveError, SanyModuleOrder, is_standard_module};

/// The modules of the library directories, by name: TLC's `TLA-Library`.
#[derive(Clone, Debug, Default)]
pub struct Library {
    modules: HashMap<String, PathBuf>,
}

impl Library {
    /// The `.tla` files under `directories`, the first of a name winning. A standard module
    /// the checker knows isn't taken from a library.
    pub fn new(directories: &[PathBuf]) -> Self {
        let mut modules = HashMap::new();
        for directory in directories {
            let mut files = Vec::new();
            collect(directory, &mut files);
            for path in files {
                let name = path.file_stem().unwrap_or_default().to_string_lossy().into_owned();
                if !tla_tools_resolve::is_standard_module(&name) {
                    modules.entry(name).or_insert(path);
                }
            }
        }
        Self { modules }
    }

    pub fn get(&self, name: &str) -> Option<&Path> {
        self.modules.get(name).map(PathBuf::as_path)
    }
}

fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(path)
            .into_iter()
            .flatten()
            .flatten()
            .map(|entry| entry.path())
            .collect();
        entries.sort();
        for entry in entries {
            collect(&entry, files);
        }
    } else if path.extension().is_some_and(|found| found == "tla") {
        files.push(path.to_path_buf());
    }
}

/// Why a model couldn't be read, with TLC's wording.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// The configuration can't be read or parsed.
    Config(String),
    /// A module can't be read, parsed, or resolved.
    Parse(ParseFailure),
}

/// Why SANY rejects a spec, with what it read before.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseFailure {
    pub message: String,
    /// The error the resolver reports, if it reports one.
    pub error: Option<ResolveError>,
    pub modules: Modules,
}

impl LoadError {
    pub fn message(&self) -> &str {
        match self {
            LoadError::Config(message) => message,
            LoadError::Parse(failure) => &failure.message,
        }
    }
}

/// The modules of a spec as SANY reads them: the orders it parses and analyzes them in, and the
/// file each module that isn't a standard module was read from.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Modules {
    pub order: SanyModuleOrder,
    /// The files the modules were read from, by module name, in the order they were first read.
    pub files: Vec<(String, PathBuf)>,
}

/// A spec and its model configuration, read.
pub struct Loaded {
    pub spec: Spec,
    pub config: ModelConfig,
    /// The Java class files beside the spec, by the name of the module they override.
    pub classes: HashMap<String, Vec<u8>>,
    /// TLC's order of the variables.
    pub variable_order: Option<Vec<String>>,
    pub modules: Modules,
}

/// Reads the spec at `spec_path` and the configuration at `config_path`, finding the modules
/// the spec uses beside it or in `library`.
///
/// TLC orders strings by when it reads them, which every sorted set and record built from here
/// on depends on. That order is the process's ([`tla_tools_eval::value::set_order`]), so a process
/// loads one model.
pub fn load(spec_path: &Path, config_path: &Path, library: &Library) -> Result<Loaded, LoadError> {
    let config = std::fs::read_to_string(config_path)
        .map_err(|error| LoadError::Config(format!("{}: {error}", config_path.display())))?;
    // TLC reads the configuration first, which orders its strings and model values.
    let config = tla_tools_parser::parse_config(&config)
        .map_err(|error| LoadError::Config(error.message))?;
    let source = std::fs::read_to_string(spec_path).map_err(|error| {
        let message = format!("{}: {error}", spec_path.display());
        LoadError::Parse(ParseFailure { message, error: None, modules: Modules::default() })
    })?;
    let directory = spec_path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
    let mut files: Vec<(String, PathBuf)> = vec![(stem(spec_path), spec_path.to_path_buf())];
    let mut loader = |name: &str| {
        let beside = directory.join(format!("{name}.tla"));
        let (path, text) = match std::fs::read_to_string(&beside) {
            Ok(text) => (beside, text),
            Err(_) => {
                let path = library.get(name)?;
                (path.to_path_buf(), std::fs::read_to_string(path).ok()?)
            }
        };
        if !files.iter().any(|(known, _)| known == name) {
            files.push((name.to_owned(), path));
        }
        Some(text)
    };
    if let Ok(order) = tla_tools_resolve::tlc_string_order(&source, &config, &mut loader) {
        tla_tools_eval::value::set_order(order.iter().map(String::as_str));
    }
    let variable_order = tla_tools_resolve::tlc_variable_order(&source, &mut loader).ok();
    let order = tla_tools_resolve::sany_module_order(&source, &mut loader);
    let resolved = tla_tools_resolve::resolve(&source, &mut loader);
    let modules = Modules { order, files };
    let spec = match resolved {
        Ok(spec) => spec,
        Err(error) => {
            let message = error.to_string();
            return Err(LoadError::Parse(ParseFailure { message, error: Some(error), modules }));
        }
    };
    // TLC requires the root module to be named after its file.
    let stem = stem(spec_path);
    if spec.modules[0].name.as_str() != stem {
        let message = format!(
            "File name '{stem}' does not match the name '{}' of the top level module it contains.",
            spec.modules[0].name
        );
        return Err(LoadError::Parse(ParseFailure { message, error: None, modules }));
    }
    // TLC loads a class named after each module from beside the spec.
    let classes = spec
        .modules
        .iter()
        .filter_map(|module| {
            let class = std::fs::read(directory.join(format!("{}.class", module.name))).ok()?;
            Some((module.name.as_str().to_owned(), class))
        })
        .collect();
    Ok(Loaded { spec, config, classes, variable_order, modules })
}

fn stem(path: &Path) -> String {
    path.file_stem().unwrap_or_default().to_string_lossy().into_owned()
}
