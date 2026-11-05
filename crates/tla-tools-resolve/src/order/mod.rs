//! TLC's order of strings, ported from tla-ts `tlc/order.ts`.
//!
//! TLC orders strings and model values by when it first interned their text. Before it checks a
//! spec, it interns, in order: the values of the model configuration, its startup strings, the
//! tokens of each module in the order SANY parses the modules, the contents of string literals in
//! the order SANY analyzes the modules, and the names it uses for `TLCGet`.
//! [`tlc_string_order`] lists those texts, for `tla_tools_intern::set_order`.

mod context;
mod lexer;
mod strings;

pub use context::tlc_variable_order;

use std::collections::{HashMap, HashSet};

use lexer::{Kind, Token, tokenize};
use tla_tools_parser::{ConfigValue, ModelConfig};

use crate::ModuleLoader;

/// The standard modules a spec may ship its own file of, which SANY reads in place of its own.
const USER_STANDARD_MODULES: &[&str] = &["Bags", "Json", "Randomization", "TLCExt"];

/// What SANY interns as its semantic analysis starts.
const SEMANTIC_PRELUDE: &[&str] =
    &["LAMBDA", "$$InAssume", "nullODN", "nullOpArg", "nullLabelNode"];

/// Every text TLC interns before it checks the spec whose root module is `source`, in order.
/// It fails where SANY would fail to read a module.
pub fn tlc_string_order(
    source: &str,
    config: &ModelConfig,
    loader: &mut dyn ModuleLoader,
) -> Result<Vec<String>, String> {
    let mut order = Order::default();
    for constant in &config.constants {
        constant.args.iter().for_each(|value| order.config_value(value));
        order.config_value(&constant.value);
    }
    strings::TLC_STARTUP_STRINGS.iter().for_each(|text| order.intern(text));
    let mut modules = Modules::new(source, loader)?;
    Parse::default().run(&mut modules, &mut order)?;
    strings::TLC_RUNTIME_STRINGS.iter().for_each(|text| order.intern(text));
    Ok(order.texts)
}

/// Texts in the order they were first interned.
#[derive(Default)]
struct Order {
    texts: Vec<String>,
    seen: HashSet<String>,
}

impl Order {
    fn intern(&mut self, text: &str) {
        if self.seen.insert(text.to_owned()) {
            self.texts.push(text.to_owned());
        }
    }

    fn config_value(&mut self, value: &ConfigValue) {
        match value {
            ConfigValue::ModelValue(name) | ConfigValue::Str(name) => self.intern(name.as_str()),
            ConfigValue::Set(elements) => {
                elements.iter().for_each(|value| self.config_value(value))
            }
            ConfigValue::Int(_) | ConfigValue::Bool(_) => {}
        }
    }
}

/// A module's tokens: the tokens of its file from `start` up to `end`.
#[derive(Clone)]
struct Unit {
    file: usize,
    start: usize,
    end: usize,
}

/// The modules TLC reads: the root module, TLC's standard modules, the files the loader returns,
/// the modules that follow the root module in its file, and the modules nested in any of these.
/// A module without a source has no tokens.
struct Modules<'a> {
    source: &'a str,
    loader: &'a mut dyn ModuleLoader,
    files: Vec<Vec<Token>>,
    /// The text of each file.
    texts: Vec<Option<String>>,
    units: HashMap<Option<String>, Unit>,
    nested: HashMap<String, Unit>,
}

/// Where each module of a file starts and ends, by name, the first of each name.
fn ranges(tokens: &[Token]) -> Vec<(String, usize, usize)> {
    let mut ranges: Vec<(String, usize, usize)> = Vec::new();
    let mut open: Vec<(String, usize)> = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if token.kind == Kind::Separator
            && tokens.get(index + 1).is_some_and(|next| next.text == "MODULE")
            && let Some(name) = tokens.get(index + 2)
        {
            open.push((name.text.clone(), index));
        }
        if token.kind == Kind::ModuleEnd
            && let Some((name, start)) = open.pop()
            && !ranges.iter().any(|(known, _, _)| *known == name)
        {
            ranges.push((name, start, index + 1));
        }
    }
    ranges
}

/// The lines of `source` from a header of module `name` to the next line starting with `====`.
fn extract_module(source: &str, name: &str) -> Option<String> {
    let lines: Vec<&str> =
        source.split('\n').map(|line| line.strip_suffix('\r').unwrap_or(line)).collect();
    let is_header = |line: &str| {
        let line = line.trim_end();
        let rest = line.trim_start_matches('-');
        if line.len() - rest.len() < 4 {
            return false;
        }
        let Some(rest) = rest.trim_start().strip_prefix("MODULE") else { return false };
        let Some(rest) = rest.trim_start().strip_prefix(name) else { return false };
        let rest = rest.trim_start();
        rest.len() >= 3 && rest.chars().all(|char| char == '-')
    };
    let start = lines.iter().position(|line| is_header(line))?;
    let end = lines
        .iter()
        .enumerate()
        .skip(start + 1)
        .find(|(_, line)| line.starts_with("===="))
        .map(|(index, _)| index);
    let end = end.map_or(lines.len(), |end| end + 1);
    Some(format!("{}\n", lines[start..end].join("\n")))
}

impl<'a> Modules<'a> {
    fn new(source: &'a str, loader: &'a mut dyn ModuleLoader) -> Result<Self, String> {
        let mut modules = Self {
            source,
            loader,
            files: Vec::new(),
            texts: Vec::new(),
            units: HashMap::new(),
            nested: HashMap::new(),
        };
        modules.file(None)?;
        Ok(modules)
    }

    fn file(&mut self, name: Option<&str>) -> Result<Unit, String> {
        let key = name.map(str::to_owned);
        if let Some(unit) = self.units.get(&key) {
            return Ok(unit.clone());
        }
        let text = match name {
            None => Some(self.source.to_owned()),
            Some(name) => {
                let shipped =
                    USER_STANDARD_MODULES.contains(&name).then(|| self.loader.load(name)).flatten();
                shipped
                    .or_else(|| crate::stdlib::standard_module(name).map(str::to_owned))
                    .or_else(|| self.loader.load(name))
                    .or_else(|| extract_module(self.source, name))
            }
        };
        let tokens = match &text {
            Some(text) => tokenize(text)?,
            None => Vec::new(),
        };
        self.texts.push(text);
        let ranges = ranges(&tokens);
        let module_name = tokens.get(2).map(|token| token.text.clone());
        let (start, end) = ranges
            .iter()
            .find(|(range_name, _, _)| Some(range_name) == module_name.as_ref())
            .map_or((0, 0), |(_, start, end)| (*start, *end));
        let file = self.files.len();
        self.files.push(tokens);
        let unit = Unit { file, start, end };
        self.units.insert(key, unit.clone());
        for (nested_name, nested_start, nested_end) in ranges {
            if nested_start != start && !self.nested.contains_key(&nested_name) {
                self.nested
                    .insert(nested_name, Unit { file, start: nested_start, end: nested_end });
            }
        }
        Ok(unit)
    }

    fn unit(&mut self, name: Option<&str>) -> Result<Unit, String> {
        if let Some(unit) = name.and_then(|name| self.nested.get(name)) {
            return Ok(unit.clone());
        }
        self.file(name)
    }

    /// Whether the file of a module has any token: SANY found a source for it.
    fn is_found(&mut self, name: Option<&str>) -> Result<bool, String> {
        let unit = self.unit(name)?;
        Ok(!self.files[unit.file].is_empty())
    }

    fn tokens(&mut self, name: Option<&str>) -> Result<Vec<Token>, String> {
        let unit = self.unit(name)?;
        Ok(self.files[unit.file][unit.start..unit.end].to_vec())
    }
}

/// The names a list of declarations such as `EXTENDS A, B` gives, and where the list ends.
fn declarations(tokens: &[Token], mut index: usize) -> Vec<String> {
    let mut names = Vec::new();
    while let Some(first) = tokens.get(index) {
        let second = tokens.get(index + 1);
        let (name, end) =
            if first.text == "_" && second.is_some_and(|token| token.kind == Kind::Operator) {
                let second = second.expect("checked above");
                let is_infix = tokens.get(index + 2).is_some_and(|token| token.text == "_");
                (second.text.clone(), if is_infix { index + 3 } else { index + 2 })
            } else if first.kind == Kind::Operator {
                (if first.text == "-" { "-.".to_owned() } else { first.text.clone() }, index + 2)
            } else if second.is_some_and(|token| token.text == "(") {
                let close = (index + 1..tokens.len()).find(|&at| tokens[at].text == ")");
                (first.text.clone(), close.map_or(tokens.len(), |close| close + 1))
            } else {
                (first.text.clone(), index + 1)
            };
        names.push(name);
        if tokens.get(end).is_none_or(|token| token.text != ",") {
            break;
        }
        index = end + 1;
    }
    names
}

/// The modules a module extends and instantiates, with its inner modules, as SANY's `SpecObj`
/// walks them to decide which module to parse next.
struct References {
    key: String,
    unit: Option<String>,
    extends: Vec<String>,
    instances: Vec<String>,
    inner: Vec<usize>,
    /// The modules this module and the modules nested in it extend, by index into
    /// [`Parse::extends`].
    all_extends: usize,
}

fn is_adjacent(left: &Token, right: Option<&Token>) -> bool {
    right.is_some_and(|right| {
        right.line == left.line && right.column == left.column + left.text.chars().count()
    })
}

/// A string literal as SANY interns it while it parses: as written, quotes included.
fn written_string(text: &str) -> String {
    let mut written = String::from("\"");
    for char in text.chars() {
        match char {
            '\\' => written.push_str("\\\\"),
            '"' => written.push_str("\\\""),
            '\n' => written.push_str("\\n"),
            '\t' => written.push_str("\\t"),
            '\r' => written.push_str("\\r"),
            '\u{c}' => written.push_str("\\f"),
            _ => written.push(char),
        }
    }
    written.push('"');
    written
}

/// The texts SANY interns while it parses a module, in order. It reads a proof step label such
/// as `<1>2` and a module header such as `---- MODULE` as one token.
fn parsed_texts(tokens: &[Token]) -> Vec<String> {
    let mut texts = Vec::new();
    let mut index = 0;
    while index < tokens.len() {
        let token = &tokens[index];
        let next = tokens.get(index + 1);
        let is_step_label = token.text == "<"
            && is_adjacent(token, next)
            && next.is_some_and(|next| {
                next.text == "*"
                    || next.text == "+"
                    || next.text.chars().all(|char| char.is_ascii_digit()) && !next.text.is_empty()
            })
            && tokens.get(index + 2).is_some_and(|close| close.text == ">")
            && is_adjacent(&tokens[index + 1], tokens.get(index + 2));
        if is_step_label {
            index += if is_adjacent(&tokens[index + 2], tokens.get(index + 3)) { 4 } else { 3 };
            continue;
        }
        let is_header =
            token.text == "MODULE" && index > 0 && tokens[index - 1].kind == Kind::Separator;
        if !is_header {
            texts.push(if token.kind == Kind::String {
                written_string(&token.text)
            } else {
                token.text.clone()
            });
        }
        index += 1;
    }
    texts
}

/// SANY's order of parsing and analyzing the modules of a spec.
#[derive(Default)]
struct Parse {
    references: Vec<References>,
    /// The references of each module unit, by name, `None` for the root module.
    by_unit: HashMap<Option<String>, usize>,
    /// The references of each module nested in another, by name.
    inner_modules: HashMap<String, usize>,
    extends: Vec<HashSet<String>>,
    /// The modules each module was found to depend on, as `key>name`.
    relations: HashSet<String>,
}

impl Parse {
    fn read(
        &mut self,
        tokens: &[Token],
        start: usize,
        key: String,
        unit: &Option<String>,
        all_extends: usize,
    ) -> (usize, usize) {
        let id = self.references.len();
        self.references.push(References {
            key: key.clone(),
            unit: unit.clone(),
            extends: Vec::new(),
            instances: Vec::new(),
            inner: Vec::new(),
            all_extends,
        });
        let mut index = start + 1;
        while index < tokens.len() {
            let token = &tokens[index];
            if token.kind == Kind::ModuleEnd {
                return (id, index);
            }
            if token.kind == Kind::Separator
                && tokens.get(index + 1).is_some_and(|next| next.text == "MODULE")
            {
                let name =
                    tokens.get(index + 2).map_or_else(String::new, |token| token.text.clone());
                let (inner, end) =
                    self.read(tokens, index, format!("{key}/{name}"), unit, all_extends);
                self.inner_modules.insert(name, inner);
                self.references[id].inner.push(inner);
                index = end;
            } else if index > 0 && tokens[index - 1].text == "." {
                // A record field named EXTENDS or INSTANCE, as in r.EXTENDS.
            } else if token.text == "EXTENDS" {
                let names = declarations(tokens, index + 1);
                self.extends[all_extends].extend(names.iter().cloned());
                self.references[id].extends.extend(names);
            } else if token.text == "INSTANCE"
                && tokens.get(index + 1).is_some_and(|next| next.kind == Kind::Identifier)
            {
                let name = tokens[index + 1].text.clone();
                self.references[id].instances.push(name);
            }
            index += 1;
        }
        (id, tokens.len())
    }

    fn unit_references(
        &mut self,
        modules: &mut Modules<'_>,
        name: Option<&str>,
    ) -> Result<usize, String> {
        let key = name.map(str::to_owned);
        if let Some(&id) = self.by_unit.get(&key) {
            return Ok(id);
        }
        let tokens = modules.tokens(name)?;
        let all_extends = self.extends.len();
        self.extends.push(HashSet::new());
        let (id, _) = self.read(&tokens, 0, key.clone().unwrap_or_default(), &key, all_extends);
        self.by_unit.insert(key, id);
        Ok(id)
    }

    fn referenced(&mut self, modules: &mut Modules<'_>, name: &str) -> Result<usize, String> {
        match self.inner_modules.get(name) {
            Some(&id) => Ok(id),
            None => self.unit_references(modules, Some(name)),
        }
    }

    fn is_resolved(&self, module: usize, name: &str) -> bool {
        self.inner_modules.contains_key(name)
            || self.relations.contains(&format!("{}>{name}", self.references[module].key))
    }

    /// The first module, depth first, with a module of `names(module)` not yet resolved, and that
    /// name.
    fn search(
        &mut self,
        modules: &mut Modules<'_>,
        module: usize,
        visited: &mut HashSet<String>,
        is_instance: bool,
    ) -> Result<Option<(usize, String)>, String> {
        if !visited.insert(self.references[module].key.clone()) {
            return Ok(None);
        }
        let names = if is_instance {
            &self.references[module].instances
        } else {
            &self.references[module].extends
        };
        if let Some(name) = names.iter().find(|name| !self.is_resolved(module, name)) {
            return Ok(Some((module, name.clone())));
        }
        let mut nested = Vec::new();
        for name in self.references[module].extends.clone() {
            nested.push(self.referenced(modules, &name)?);
        }
        for name in self.references[module].instances.clone() {
            if self.is_resolved(module, &name) {
                nested.push(self.referenced(modules, &name)?);
            }
        }
        nested.extend(self.references[module].inner.clone());
        for item in nested {
            if let Some(found) = self.search(modules, item, visited, is_instance)? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    fn run(mut self, modules: &mut Modules<'_>, order: &mut Order) -> Result<(), String> {
        let root_tokens = modules.tokens(None)?;
        for (index, text) in parsed_texts(&root_tokens).iter().enumerate() {
            if index == 3 {
                strings::SANY_NODE_NAMES.iter().for_each(|name| order.intern(name));
            }
            order.intern(text);
        }
        let root = self.unit_references(modules, None)?;
        let mut parsed: HashSet<Option<String>> = HashSet::from([None]);
        let mut dependencies: HashMap<Option<String>, Vec<String>> = HashMap::new();
        loop {
            let found = match self.search(modules, root, &mut HashSet::new(), false)? {
                Some(found) => Some(found),
                None => self.search(modules, root, &mut HashSet::new(), true)?,
            };
            let Some((module, name)) = found else { break };
            let key = format!("{}>{name}", self.references[module].key);
            self.relations.insert(key);
            let unit = self.references[module].unit.clone();
            dependencies.entry(unit.clone()).or_default().push(name.clone());
            if !parsed.insert(Some(name.clone())) {
                continue;
            }
            if !modules.is_found(Some(&name))? {
                let importer = unit.unwrap_or_else(|| {
                    root_tokens.get(2).map_or_else(String::new, |token| token.text.clone())
                });
                return Err(format!(
                    "Cannot find source file for module {name} imported in module {importer}."
                ));
            }
            let tokens = modules.tokens(Some(&name))?;
            parsed_texts(&tokens).iter().for_each(|text| order.intern(text));
        }
        SEMANTIC_PRELUDE.iter().for_each(|text| order.intern(text));
        self.analyze(modules, None, &dependencies, &mut HashSet::new(), order)
    }

    /// Interns the contents of the string literals of a module after those of the modules it
    /// depends on, extended modules first, as SANY's semantic analysis does.
    fn analyze(
        &mut self,
        modules: &mut Modules<'_>,
        name: Option<String>,
        dependencies: &HashMap<Option<String>, Vec<String>>,
        analyzed: &mut HashSet<Option<String>>,
        order: &mut Order,
    ) -> Result<(), String> {
        if !analyzed.insert(name.clone()) {
            return Ok(());
        }
        let unit_dependencies = dependencies.get(&name).cloned().unwrap_or_default();
        let references = self.unit_references(modules, name.as_deref())?;
        let extendees = self.extends[self.references[references].all_extends].clone();
        let (extended, instantiated): (Vec<_>, Vec<_>) =
            unit_dependencies.into_iter().partition(|item| extendees.contains(item));
        for dependency in extended.into_iter().chain(instantiated) {
            self.analyze(modules, Some(dependency), dependencies, analyzed, order)?;
        }
        for token in modules.tokens(name.as_deref())? {
            if token.kind == Kind::String {
                order.intern(&token.text);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
