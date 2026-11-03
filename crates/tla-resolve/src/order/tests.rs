use tla_parser::parse_config;

use super::lexer::tokenize;
use super::{parsed_texts, tlc_string_order};

fn order(source: &str, config: &str, modules: &[(&str, &str)]) -> Vec<String> {
    let config = parse_config(config).unwrap();
    let mut loader = |name: &str| {
        modules.iter().find(|(module, _)| *module == name).map(|(_, source)| source.to_string())
    };
    tlc_string_order(source, &config, &mut loader).unwrap()
}

fn position(order: &[String], text: &str) -> usize {
    order.iter().position(|known| known == text).unwrap_or_else(|| panic!("{text} is not ranked"))
}

#[test]
fn ranks_configuration_values_then_startup_strings_then_tokens() {
    let source = "---- MODULE M ----\nEXTENDS Helper\nVARIABLE x\nInit == x = \"init\" /\\ y = \"c\"\n====\n";
    let helper = "---- MODULE Helper ----\nH == \"helper\"\n====\n";
    let order = order(source, "CONSTANT N = {b, a}\nINIT Init", &[("Helper", helper)]);
    assert_eq!(&order[..2], ["b", "a"]);
    assert_eq!(order[2], "STRING");
    // The root module's tokens, with SANY's node names after its first three.
    assert!(position(&order, "M") < position(&order, "Not a node"));
    assert!(position(&order, "Not a node") < position(&order, "EXTENDS"));
    // The root module's tokens, then those of the module it extends; literals as written while
    // parsing, then their contents during semantic analysis, those of an extended module first.
    assert!(position(&order, "Helper") < position(&order, "\"init\""));
    assert!(position(&order, "\"init\"") < position(&order, "H"));
    assert!(position(&order, "H") < position(&order, "LAMBDA"));
    assert!(position(&order, "LAMBDA") < position(&order, "helper"));
    assert!(position(&order, "helper") < position(&order, "init"));
    assert!(position(&order, "init") < position(&order, "c"));
    assert_eq!(order.last().map(String::as_str), Some("bfs"));
    assert!(!order.iter().any(|text| text == "MODULE"));
}

#[test]
fn reads_operators_by_their_canonical_spelling() {
    let source = "---- MODULE M ----\nA == 1 =< 2 /\\ {} \\union {} /\\ <1>2 \"a\\\"b\"\n====\n";
    let tokens = tokenize(source).unwrap();
    let texts: Vec<&str> = tokens.iter().map(|token| token.text.as_str()).collect();
    assert_eq!(
        texts,
        [
            "----", "MODULE", "M", "----", "A", "==", "1", "<=", "2", "/\\", "{", "}", "\\cup",
            "{", "}", "/\\", "<1>2", "a\"b", "===="
        ]
    );
    assert_eq!(parsed_texts(&tokens)[16], "\"a\\\"b\"");
}

#[test]
fn reads_the_modules_after_the_root_module_in_its_file() {
    let source =
        "---- MODULE M ----\nEXTENDS Inner\n====\n---- MODULE Inner ----\nI == \"inner\"\n====\n";
    let order = order(source, "", &[]);
    assert!(position(&order, "I") < position(&order, "inner"));
}

#[test]
fn fails_for_a_module_it_cant_find() {
    let config = parse_config("").unwrap();
    let source = "---- MODULE M ----\nEXTENDS Missing\n====\n";
    let error = tlc_string_order(source, &config, &mut |_: &str| None).unwrap_err();
    assert_eq!(error, "Cannot find source file for module Missing imported in module M.");
}
