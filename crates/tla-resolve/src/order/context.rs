//! TLC's order of the variables of a spec, ported from tla-ts `tlc/order.ts`
//! (`createContexts`, `getTlcDeclarationOrder`).
//!
//! TLC keeps a state's variables in the order `ModuleNode.getVariableDecls` returns them: the
//! reverse of the enumeration of the root module's SANY `Context`, a `java.util.Hashtable` of
//! every name the module sees. The order depends on the hash of each name and on how many names
//! the table holds, so this rebuilds the table as SANY fills it: SANY's built-in operators, the
//! names of the modules the module extends, then the module's own, in the order it declares
//! them.

use std::collections::{HashMap, HashSet};

use tla_ast::{Module, Unit};

use super::Modules;
use crate::ModuleLoader;

/// The operators SANY's `Context` starts with, in the order SANY adds them, reversed.
const SANY_BUILTINS: &[&str] = &[
    "STRING",
    "FALSE",
    "TRUE",
    "BOOLEAN",
    "=",
    "/=",
    ".",
    "'",
    "\\lnot",
    "\\neg",
    "\\land",
    "\\lor",
    "\\equiv",
    "=>",
    "SUBSET",
    "UNION",
    "DOMAIN",
    "\\subseteq",
    "\\in",
    "\\notin",
    "\\",
    "\\intersect",
    "\\union",
    "\\times",
    "~>",
    "[]",
    "<>",
    "ENABLED",
    "UNCHANGED",
    "\\cdot",
    "-+->",
    "$AngleAct",
    "$BoundedChoose",
    "$BoundedExists",
    "$BoundedForall",
    "$CartesianProd",
    "$Case",
    "$ConjList",
    "$DisjList",
    "$Except",
    "$FcnApply",
    "$FcnConstructor",
    "$IfThenElse",
    "$NonRecursiveFcnSpec",
    "$Pair",
    "$RcdConstructor",
    "$RcdSelect",
    "$RecursiveFcnSpec",
    "$Seq",
    "$SetEnumerate",
    "$SetOfAll",
    "$SetOfFcns",
    "$SetOfRcds",
    "$SF",
    "$SquareAct",
    "$SubsetOf",
    "$TemporalExists",
    "$TemporalForall",
    "$TemporalWhile",
    "$Tuple",
    "$UnboundedChoose",
    "$UnboundedExists",
    "$UnboundedForall",
    "$WF",
    "$Nop",
    "$Qed",
    "$Pfcase",
    "$Have",
    "$Take",
    "$Pick",
    "$Witness",
    "$Suffices",
];

/// The spellings of each operator, the one SANY names it by first.
const OPERATOR_SYNONYMS: &[&[&str]] = &[
    &["\\lnot", "~", "\\neg", "¬"],
    &["[]", "□"],
    &["<>", "◇"],
    &["\\land", "/\\", "∧"],
    &["\\lor", "\\/", "∨"],
    &["\\equiv", "<=>", "≡", "⇔"],
    &["/=", "#", "≠"],
    &["\\leq", "<=", "=<", "≤"],
    &["\\geq", ">=", "≥"],
    &["\\times", "\\X", "×"],
    &["\\intersect", "\\cap", "∩"],
    &["\\union", "\\cup", "∪"],
    &["\\o", "\\circ", "∘"],
    &["\\oplus", "(+)", "⊕"],
    &["\\ominus", "(-)", "⊖"],
    &["\\odot", "(.)", "⊙"],
    &["\\oslash", "(/)", "⊘"],
    &["\\otimes", "(\\X)", "⊗"],
    &["\\approx", "≈"],
    &[":=", "≔"],
    &["\\asymp", "≍"],
    &["\\bigcirc", "◯"],
    &["::=", "⩴"],
    &["\\bullet", "●"],
    &["\\cdot", "⋅"],
    &["\\cong", "≅"],
    &["\\div", "÷"],
    &["\\doteq", "≐"],
    &["..", "‥"],
    &["...", "…"],
    &["!!", "‼"],
    &["\\gg", "≫"],
    &["=>", "⇒"],
    &["\\in", "∈"],
    &["=|", "⫤"],
    &["~>", "↝"],
    &["\\ll", "≪"],
    &["-|", "⊣"],
    &["\\notin", "∉"],
    &["-+->", "⇸"],
    &["\\prec", "≺"],
    &["\\preceq", "⪯"],
    &["\\propto", "∝"],
    &["??", "⁇"],
    &["|=", "⊨"],
    &["|-", "⊢"],
    &["\\sim", "∼"],
    &["\\simeq", "≃"],
    &["\\sqcap", "⊓"],
    &["\\sqcup", "⊔"],
    &["\\sqsubset", "⊏"],
    &["\\sqsubseteq", "⊑"],
    &["\\sqsupset", "⊐"],
    &["\\sqsupseteq", "⊒"],
    &["\\star", "⋆"],
    &["\\subset", "⊂"],
    &["\\subseteq", "⊆"],
    &["\\succ", "≻"],
    &["\\succeq", "⪰"],
    &["\\supset", "⊃"],
    &["\\supseteq", "⊇"],
    &["\\uplus", "⊎"],
    &["||", "‖"],
    &["\\wr", "≀"],
    &["^+", "⁺"],
];

fn canonical(name: &str) -> String {
    OPERATOR_SYNONYMS
        .iter()
        .find(|synonyms| synonyms.contains(&name))
        .map_or_else(|| name.to_owned(), |synonyms| synonyms[0].to_owned())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Builtin,
    Constant,
    Variable,
    Definition,
    Theorem,
    Module,
}

#[derive(Clone, Debug)]
struct Entry {
    name: String,
    kind: Kind,
    is_local: bool,
}

impl Entry {
    fn key(&self) -> String {
        match self.kind {
            Kind::Module => format!("module {}", self.name),
            _ => self.name.clone(),
        }
    }
}

/// `String.hashCode` of Java.
fn java_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| hash.wrapping_mul(31).wrapping_add(i32::from(unit)))
}

/// `java.util.Hashtable` as SANY's `Context` uses it: capacity 11, load factor 0.75, new
/// entries at the head of their bucket, and enumeration from the last bucket to the first.
#[derive(Clone)]
struct Table {
    buckets: Vec<Vec<Entry>>,
    threshold: usize,
    keys: HashSet<String>,
    inserted: Vec<Entry>,
}

impl Table {
    fn new() -> Self {
        Self {
            buckets: vec![Vec::new(); 11],
            threshold: 8,
            keys: HashSet::new(),
            inserted: Vec::new(),
        }
    }

    fn bucket(name: &str, capacity: usize) -> usize {
        (java_hash(name) & 0x7fff_ffff) as usize % capacity
    }

    fn put(&mut self, entry: Entry) {
        if !self.keys.insert(entry.key()) {
            return;
        }
        if self.inserted.len() >= self.threshold {
            let capacity = self.buckets.len() * 2 + 1;
            let mut buckets: Vec<Vec<Entry>> = vec![Vec::new(); capacity];
            for bucket in self.buckets.iter().rev() {
                for entry in bucket {
                    buckets[Self::bucket(&entry.name, capacity)].insert(0, entry.clone());
                }
            }
            self.buckets = buckets;
            self.threshold = capacity * 3 / 4;
        }
        let capacity = self.buckets.len();
        self.buckets[Self::bucket(&entry.name, capacity)].insert(0, entry.clone());
        self.inserted.push(entry);
    }

    fn enumerate(&self) -> impl Iterator<Item = &Entry> {
        self.buckets.iter().rev().flatten()
    }
}

/// The variables of the root module of a spec in the order TLC keeps them in a state.
pub fn tlc_variable_order(
    source: &str,
    loader: &mut dyn ModuleLoader,
) -> Result<Vec<String>, String> {
    let mut contexts = Contexts { modules: Modules::new(source, loader)?, tables: HashMap::new() };
    let root = contexts.context(None)?;
    let mut variables: Vec<String> = root
        .enumerate()
        .filter(|entry| entry.kind == Kind::Variable)
        .map(|entry| entry.name.clone())
        .collect();
    variables.reverse();
    Ok(variables)
}

struct Contexts<'a> {
    modules: Modules<'a>,
    tables: HashMap<Option<String>, Table>,
}

impl Contexts<'_> {
    /// The module named `name`, `None` for the root module.
    fn module(&mut self, name: Option<&str>) -> Result<Module, String> {
        let unit = self.modules.unit(name)?;
        let tokens = &self.modules.files[unit.file];
        if tokens.is_empty() {
            return Err(format!("Cannot find source file for module {}.", name.unwrap_or("")));
        }
        let text = self.modules.texts[unit.file].clone().unwrap_or_default();
        let parsed = tla_parser::parse_modules(&text).map_err(|error| error.to_string())?;
        let Some(name) = name else {
            return parsed.into_iter().next().ok_or_else(|| "The spec has no module.".into());
        };
        find(&parsed, name).ok_or_else(|| format!("Cannot find module {name}."))
    }

    fn context(&mut self, name: Option<&str>) -> Result<Table, String> {
        let key = name.map(str::to_owned);
        if let Some(table) = self.tables.get(&key) {
            return Ok(table.clone());
        }
        let module = self.module(name)?;
        let mut table = Table::new();
        for builtin in SANY_BUILTINS.iter().rev() {
            table.put(Entry { name: (*builtin).to_owned(), kind: Kind::Builtin, is_local: false });
        }
        // A module that extends itself, directly or not, is an error SANY reports elsewhere.
        self.tables.insert(key.clone(), table.clone());
        for extended in &module.extends {
            for entry in self.context(Some(extended.symbol.as_str()))?.inserted {
                if !entry.is_local {
                    table.put(entry);
                }
            }
        }
        let defined: HashSet<&str> = module
            .units
            .iter()
            .filter_map(|unit| match unit {
                Unit::Operator(definition) => Some(definition.name.symbol.as_str()),
                Unit::Function(definition) => Some(definition.name.symbol.as_str()),
                _ => None,
            })
            .collect();
        let mut statements: HashSet<String> = HashSet::new();
        for unit in &module.units {
            let mut put = |name: &str, kind: Kind, is_local: bool| {
                table.put(Entry { name: name.to_owned(), kind, is_local });
            };
            match unit {
                Unit::Constants(declarations) => declarations
                    .iter()
                    .for_each(|declaration| put(&declared(declaration), Kind::Constant, false)),
                Unit::Variables(names) => {
                    names.iter().for_each(|name| put(name.symbol.as_str(), Kind::Variable, false))
                }
                Unit::Recursive(declarations) => {
                    let names: Vec<String> = declarations.iter().map(declared).collect();
                    if names.iter().all(|name| defined.contains(name.as_str())) {
                        names.iter().for_each(|name| put(name, Kind::Definition, false));
                    }
                }
                Unit::Operator(definition) => {
                    let name = canonical(definition.name.symbol.as_str());
                    if !statements.contains(&name) {
                        put(&name, Kind::Definition, definition.is_local);
                    }
                }
                Unit::Function(definition) => {
                    put(definition.name.symbol.as_str(), Kind::Definition, definition.is_local)
                }
                Unit::Assume(assume) => {
                    if let Some(name) = assume.name {
                        statements.insert(name.symbol.to_string());
                        put(name.symbol.as_str(), Kind::Theorem, false);
                    }
                }
                Unit::Theorem(theorem) => {
                    if let Some(name) = theorem.name {
                        statements.insert(name.symbol.to_string());
                        put(name.symbol.as_str(), Kind::Theorem, false);
                    }
                }
                Unit::Module(inner) => put(inner.name.symbol.as_str(), Kind::Module, false),
                Unit::Instance(instance) => {
                    let instancee = self.context(Some(instance.module.symbol.as_str()))?;
                    instantiate(&mut table, &instancee, "", instance.is_local);
                }
                Unit::ModuleDef(definition) => {
                    let module = definition.instance.module.symbol.as_str();
                    let instancee = self.context(Some(module))?;
                    let prefix = format!("{}!", definition.name.symbol);
                    instantiate(&mut table, &instancee, &prefix, definition.is_local);
                    table.put(Entry {
                        name: definition.name.symbol.to_string(),
                        kind: Kind::Definition,
                        is_local: definition.is_local,
                    });
                }
                Unit::Hide(_) => {}
            }
        }
        self.tables.insert(key, table.clone());
        Ok(table)
    }
}

/// The name a declaration such as `F(_)`, `_ ++ _`, or `-. _` gives, as SANY names it.
fn declared(declaration: &tla_ast::OpDecl) -> String {
    canonical(declaration.name.symbol.as_str())
}

/// Adds the definitions and theorems an `INSTANCE` brings, with `prefix`, to `table`.
fn instantiate(table: &mut Table, instancee: &Table, prefix: &str, is_local: bool) {
    let entries: Vec<&Entry> = instancee.enumerate().collect();
    let definitions = entries.iter().filter(|entry| entry.kind == Kind::Definition);
    let theorems = entries.iter().filter(|entry| entry.kind == Kind::Theorem);
    for entry in definitions.chain(theorems) {
        if entry.is_local {
            continue;
        }
        table.put(Entry { name: format!("{prefix}{}", entry.name), kind: entry.kind, is_local });
    }
}

/// The module named `name` among `modules` and the modules nested in them.
fn find(modules: &[Module], name: &str) -> Option<Module> {
    for module in modules {
        if module.name.symbol.as_str() == name {
            return Some(module.clone());
        }
        let nested: Vec<Module> = module
            .units
            .iter()
            .filter_map(|unit| match unit {
                Unit::Module(inner) => Some(inner.clone()),
                _ => None,
            })
            .collect();
        if let Some(found) = find(&nested, name) {
            return Some(found);
        }
    }
    None
}
