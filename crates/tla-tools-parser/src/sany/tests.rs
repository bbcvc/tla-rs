//! tla-ts's `tests/unit/sany-parse-error.test.ts`. The modules come from the conformance
//! corpora unless they test one of the checks SANY's parser makes as it builds the syntax tree,
//! and the expected reports are what SANY's parser prints for them.

use super::parse_error;

fn report(lines: &[&str]) -> Option<String> {
    Some(format!(
        "***Parse Error***\n{}",
        lines.iter().map(|line| format!("{line}\n")).collect::<String>()
    ))
}

#[test]
fn reports_where_a_record_constructor_has_an_expression_for_a_field_name() {
    let source = r"---- MODULE definition_parse_error ----
EXTENDS Integers
CONSTANT Limit
VARIABLE x
Bad == [a/b |-> 1]
Derived == Bad.a
Init == x = 0
Next == x < Limit /\ x' = x + 1
Small == x <= Limit
====
";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Encountered "|->" at line 5, column 13 and token "b" "#,
            "",
            "Residual stack trace follows:",
            "Some [] Form starting at line 5, column 8.",
            "ExtendableExpr starting at line 5, column 8.",
            "Expression starting at line 5, column 8.",
            "Definition starting at line 5, column 1.",
            "Module body starting at line 3, column 1.",
        ])
    );
}

#[test]
fn reports_a_lambda_outside_an_operator_argument_with_what_the_parser_expected() {
    let source = r"---- MODULE lambda ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

double == LAMBDA n : n * 2

Next == x' = double[x] /\ x < 5

Inv == x <= 10 /\ x >= 0

====
";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Was expecting "Expression or Instance""#,
            r#"Encountered "LAMBDA" at line 8, column 11 and token "==" "#,
            "",
            "Residual stack trace follows:",
            "Definition starting at line 8, column 1.",
            "Module body starting at line 4, column 1.",
            "Module definition starting at line 1, column 1.",
        ])
    );
}

#[test]
fn reports_an_unbounded_declaration_in_a_function_constructor() {
    let source = r"-------------------- MODULE FunctionConstructorOnlyBoundeds --------------------
(* Test that function constructors allow only bounded declarations. *)
f == [x \in TRUE, y |-> TRUE]
================================================================================
";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Encountered "|->" at line 3, column 21 and token "y" "#,
            "",
            "Residual stack trace follows:",
            "Quant Bound starting at line 3, column 19.",
            "Some [] Form starting at line 3, column 6.",
            "ExtendableExpr starting at line 3, column 6.",
            "Expression starting at line 3, column 6.",
            "Definition starting at line 3, column 1.",
        ])
    );
}

#[test]
fn reports_an_operator_as_a_by_def_item_in_the_productions_of_a_proof() {
    let source = "--------------- MODULE Operators_test -------------
z - y == z
z + y == z
THEOREM (z - y) = z
BY DEF - , +
=============================================================================
";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Encountered "," at line 5, column 10 and token "-" "#,
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 5, column 10.",
            "Expression starting at line 5, column 8.",
            "UseOrHideOrBy starting at line 5, column 1.",
            "Proof starting at line 5, column 1.",
            "Theorem starting at line 4, column 1.",
        ])
    );
}

#[test]
fn shows_the_tokens_a_failed_two_token_lookahead_read() {
    let source = "---- MODULE Github1417Local ----\nLOCAL hidden hidden == 42\n====\n";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Was expecting "LOCAL, INSTANCE, PROOF, ASSUMPTION, THEOREM, RECURSIVE, declaration, or definition""#,
            r#"Encountered "LOCAL hidden" at line 2, column 1 and token "----" "#,
            "",
            "Residual stack trace follows:",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ])
    );
}

#[test]
fn skips_text_before_the_module_header() {
    let source = "CAUSES the translator to throw an exception

last modified on Sun 11 Dec 2005 at  0:30:16 UT by lamport

---------------------------- MODULE bug-05-12-10 ----------------------------
EXTENDS Naturals, Sequences, FiniteSets , TLC
";
    assert_eq!(
        parse_error(source),
        report(&[
            r#"Was expecting "----""#,
            r#"Encountered "-" at line 5, column 40 and token "bug" "#,
            "",
            "Residual stack trace follows:",
            "Begin module starting at line 5, column 1.",
            "Module definition starting at line 5, column 1.",
        ])
    );
}

#[test]
fn reports_a_file_without_a_module_header_at_its_last_character() {
    assert_eq!(
        parse_error("CAUSES the translator to throw an exception\n"),
        report(&[
            r#"Was expecting "---- MODULE (beginning of module)""#,
            r#"Encountered "<EOF>" at line 1, column 44 and token "" "#,
            "",
            "Residual stack trace follows:",
            "Begin module starting at line 1, column 44.",
            "Module definition starting at line 1, column 44.",
        ])
    );
}

/// The checks SANY's parser makes as it builds the syntax tree, each for a unit of a module
/// `Test`.
const CHECKS: &[(&str, &str, &[&str])] = &[
    (
        "a precedence conflict",
        "F == a = b = c",
        &[
            "",
            "  Precedence conflict between ops = in block line 2, col 8 to line 2, col 8 of module Test and =.",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 10.",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
        ],
    ),
    (
        "a precedence conflict with a prefix minus",
        "F == x ^ -y",
        &[
            "",
            "  Precedence conflict between ops ^ in block line 2, col 8 to line 2, col 8 of module Test and -..",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a precedence conflict with a postfix operator",
        "F == ENABLED x'",
        &[
            "Precedence conflict between ops ENABLED in block line 2, col 15 to line 2, col 15 of module Test and '.",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 14.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "expressions without an operator between them",
        r"F == f[x \in S |-> 1]",
        &[
            "Expression at location line 2, col 6 to line 2, col 6 of module Test and expression at location line 2, col 7 to line 2, col 21 of module Test follow each other without any intervening operator.",
            "",
            "Residual stack trace follows:",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "an expression after a postfix operator",
        "F == a' [b -> c]",
        &[
            "",
            " Error following expression at  line 2, col 7 to line 2, col 7 of module Test, missing operator or separator.",
            "",
            "Residual stack trace follows:",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a = that may be a mistyped ==",
        "F == a'\n  [b -> c] = 1",
        &[
            "",
            "  *** Hint *** You may have mistyped ==",
            "  Illegal combination of operators ' in block line 2, col 7 to line 2, col 7 of module Test and =.",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a junction item that is not indented",
        "F == /\\ x = [a |-> 1,\nb |-> 2]\n     /\\ y",
        &[
            "Item at line 3, col 1 to line 3, col 7 of module Test is not properly indented inside conjunction or  disjunction list item at line 2, col 6 to line 3, col 8 of module Test",
            "",
            "Residual stack trace follows:",
            "AND-OR Junction starting at line 2, column 6.",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
        ],
    ),
    (
        "a :: after something other than a label",
        "F == x' :: y",
        &[
            "`::' at line 2, col 9 to line 2, col 10 of module Test does not follow a label.",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a label whose removal would change the parse",
        "F == a * l(u, v) :: b + c",
        &[
            "Removing label at line 2, col 10 to line 2, col 16 of module Test would change expression parsing.",
            "",
            "Residual stack trace follows:",
            "ExtendableExpr starting at line 2, column 10.",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
        ],
    ),
    (
        "a declared operator with a domain",
        r"THEOREM ASSUME NEW F(_, _) \in S PROVE TRUE",
        &[
            r"declared symbol with arguments before \in at line 2, col 20 to line 2, col 26 of module Test",
            "",
            "Residual stack trace follows:",
            "NEW symbol declaration starting at line 2, column 16.",
            "Assume-Prove starting at line 2, column 9.",
            "Theorem starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a proof of a step that takes none",
        "THEOREM TRUE\n<1>1. HAVE TRUE\n  OBVIOUS\n<1>2. QED",
        &[
            "line 3, col 7 to line 3, col 15 of module Test: proof of step that does not take a proof.",
            "",
            "Residual stack trace follows:",
            "Step starting at line 3, column 1.",
            "Proof starting at line 3, column 1.",
            "Theorem starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ],
    ),
    (
        "a decimal number as a structural term",
        "F == y!1.5",
        &[
            "Illegal structural term at line 2, col 8 to line 2, col 10 of module Test",
            "",
            "Residual stack trace follows:",
            "Bang Extension starting at line 2, column 7.",
            "Primitive expression starting at line 2, column 6.",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
        ],
    ),
    (
        "a set of all whose expression is a membership",
        r"S == {1 \in x : x \in T}",
        &[
            r"Form {a \in b : c \in d }, at line 2, is not allowed",
            "",
            "Residual stack trace follows:",
            "Some { } form starting at line 2, column 6.",
            "ExtendableExpr starting at line 2, column 6.",
            "Expression starting at line 2, column 6.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
        ],
    ),
];

#[test]
fn reports_the_checks_the_parser_makes_as_it_builds_the_syntax_tree() {
    for (check, body, expected) in CHECKS {
        let source = format!("---- MODULE Test ----\n{body}\n====\n");
        assert_eq!(parse_error(&source), report(expected), "{check}");
    }
}

#[test]
fn reports_lexical_errors() {
    // The modules and messages come from SANY.
    for (case, body, message) in [
        (
            "a character no token starts with",
            "x == 1 ; 2\n====\n",
            r#"Lexical error at line 2, column 8.  Encountered: ";" (59), after : """#,
        ),
        (
            "a token prefix",
            "x == \"a\" ?\n====\n",
            r#"Lexical error at line 2, column 11.  Encountered: "\n" (10), after : "?""#,
        ),
        (
            "an invalid escape",
            "x == \"a\\qb\"\n====\n",
            r#"Lexical error at line 2, column 9.  Encountered: "q" (113), after : "\"a\\""#,
        ),
        (
            "a string at the end of the file",
            "x == \"abc",
            r#"Lexical error at line 2, column 10.  Encountered: <EOF> after : "\"abc""#,
        ),
        (
            "a comment that ends the last line",
            "(* abc\n",
            r#"Lexical error at line 3, column 0.  Encountered: <EOF> after : """#,
        ),
        (
            "an end-of-line comment at the end of the file",
            "x == 1 \\* abc",
            r#"Lexical error at line 2, column 14.  Encountered: <EOF> after : """#,
        ),
        (
            "a comment open over lines",
            "(* abc\n\n",
            "Lexical {error: EOF reached, possibly open comment starting around line 2",
        ),
        (
            "a comment open after a nested comment",
            "(* \n(* \n *) abc\n\n",
            "Lexical {error: EOF reached, possibly open comment starting around line 4",
        ),
    ] {
        let source = format!("---- MODULE M ----\n{body}");
        assert_eq!(parse_error(&source).as_deref(), Some(message), "{case}");
    }
}

#[test]
fn reports_a_parse_error_for_a_comment_that_ends_the_file_with_a_bracket() {
    let error = parse_error("---- MODULE M ----\nx == 1\n(* abc (* d *)").unwrap();
    assert!(error.starts_with("***Parse Error***\n"), "{error}");
}

#[test]
fn reports_the_parse_error_before_a_lexical_error_in_a_token_the_parser_never_reads() {
    assert_eq!(
        parse_error("---- MODULE M ----\nOp == LET a == 1\n====\n\\* abc"),
        report(&[
            r#"Encountered "====" at line 3, column 1 and token "1" "#,
            "",
            "Residual stack trace follows:",
            "Case Other Arm starting at line 2, column 7.",
            "Expression starting at line 2, column 7.",
            "Definition starting at line 2, column 1.",
            "Module body starting at line 2, column 1.",
            "Module definition starting at line 1, column 1.",
        ])
    );
}

#[test]
fn reports_nothing_for_a_module_whose_error_sany_finds_after_parsing() {
    assert_eq!(parse_error("---- MODULE Infix ----\nVARIABLE x\nOp == x @@ x\n====\n"), None);
}

#[test]
fn reports_the_statechart_skill_s_parse_error() {
    let source = "---- MODULE Broken ----\nVARIABLE x\nInit == x = = 0\nNext == x' = x\n====\n";
    let error = parse_error(source).unwrap();
    assert!(error.contains("\nEncountered \"0\" at line 3, column 15"), "{error}");
}
