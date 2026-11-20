//! The productions of `javacc/tla+.jj` for a module and its declarations and definitions.

use std::collections::HashMap;

use super::State;
use super::expressions::{
    infix_operator, nonexp_prefix_operator, postfix_operator, set_field_name_expecting,
};
use super::grammar::{
    Exit, Production, Unit, action, choice, expect, lookahead_amount, lookahead_expansion,
    lookahead_semantic, optional, seq, zero_or_more,
};
use super::kinds::kind;
use super::semantics::belch_def;

fn definition(expecting: &'static str, mut parts: Vec<Unit>) -> Unit {
    let body = parts.pop().expect("a definition has a body");
    parts.extend([
        expect("=="),
        Unit::from("<DEF>"),
        action(move |state| {
            belch_def(state);
            state.expecting = expecting;
            None
        }),
        body,
    ]);
    Unit::sequence(parts)
}

pub(super) fn add_production(
    productions: &mut HashMap<&'static str, Production>,
    name: &'static str,
    message: Option<&'static str>,
    body: Unit,
    exit: Option<Exit>,
) {
    productions.insert(name, Production { message, body, exit });
}
pub(super) fn add(productions: &mut HashMap<&'static str, Production>) {
    let mut add = |name, message, body| add_production(productions, name, message, body, None);
    add(
        "CompilationUnit",
        None,
        seq![
            action(|state| {
                belch_def(state);
                None
            }),
            optional!("Prelude"),
            "Module",
        ],
    );
    add(
        "Prelude",
        None,
        seq!["<BEGIN_PRAGMA>", zero_or_more!(choice!("<NUMBER>", "<IDENTIFIER>"))],
    );
    add(
        "Module",
        Some("Module definition"),
        seq![
            expect("---- MODULE"),
            "BeginModule",
            expect("EXTENDS clause or module body"),
            "Extends",
            expect("Module body"),
            "Body",
            expect("==== or more Module body"),
            "EndModule",
        ],
    );
    add(
        "BeginModule",
        Some("Begin module"),
        seq![
            expect("---- MODULE (beginning of module)"),
            choice!("<_BM0>", "<_BM1>", "<_BM2>"),
            set_field_name_expecting("Identifier"),
            "Identifier",
            action(|state: &mut State| {
                if state.module_name.is_none() {
                    state.module_name = Some(state.token(state.token).image.clone());
                }
                state.expecting = "----";
                None
            }),
            "<SEPARATOR>",
        ],
    );
    add("EndModule", None, seq!["<END_MODULE>"]);
    add(
        "Extends",
        Some("Extends"),
        seq![optional!(
            "<EXTENDS>",
            set_field_name_expecting("Identifier"),
            "Identifier",
            expect("comma or module body"),
            zero_or_more!("<COMMA>", set_field_name_expecting("Identifier"), "Identifier"),
        )],
    );
    add(
        "Body",
        Some("Module body"),
        seq![
            expect(
                "LOCAL, INSTANCE, PROOF, ASSUMPTION, THEOREM, RECURSIVE, declaration, or definition"
            ),
            zero_or_more!(choice!(
                "<SEPARATOR>",
                "VariableDeclaration",
                "ParamDeclaration",
                seq![lookahead_amount(2), "OperatorOrFunctionDefinition"],
                "Recursive",
                seq![lookahead_amount(2), "Instance"],
                seq![lookahead_amount(2), "Assumption"],
                seq![lookahead_amount(2), "Theorem"],
                seq![
                    lookahead_amount(1),
                    "Module",
                    action(|state| {
                        belch_def(state);
                        None
                    }),
                ],
                seq![
                    lookahead_semantic(|state| {
                        if state.next_kind_is(&["USE"]) {
                            let second = state.get_token(2);
                            if state.kind_of(second) != kind("ONLY") {
                                return true;
                            }
                        }
                        state.next_kind_is(&["HIDE"])
                    }),
                    "UseOrHideOrBy",
                ],
            )),
        ],
    );
    add(
        "VariableDeclaration",
        Some("variable declaration"),
        seq![
            "<VARIABLE>",
            expect("Identifier"),
            "Identifier",
            expect("comma or module body"),
            zero_or_more!("<COMMA>", expect("Identifier"), "Identifier"),
        ],
    );
    add(
        "ParamDeclaration",
        Some("Parameter declaration"),
        seq![
            expect("CONSTANT"),
            "ParamSubDecl",
            expect("Identifier, operator or _"),
            "ConstantDeclarationItems",
            expect(","),
            zero_or_more!(
                "<COMMA>",
                expect("Identifier, operator or _"),
                "ConstantDeclarationItems"
            ),
        ],
    );
    add("ParamSubDecl", Some("Parameter declaration item"), seq!["<CONSTANT>"]);
    add(
        "Recursive",
        Some("Recursive"),
        seq![
            expect("RECURSIVE"),
            "<RECURSIVE>",
            expect("Identifier, operator or _"),
            "ConstantDeclarationItems",
            expect(","),
            zero_or_more!(
                "<COMMA>",
                expect("Identifier, operator or _"),
                "ConstantDeclarationItems",
                expect("`,' or `)'"),
            ),
        ],
    );
    add(
        "ConstantDeclarationItems",
        Some("Constant declaration items"),
        seq![
            expect("Identifier, _ or prefix op"),
            choice!(
                seq![
                    "Identifier",
                    expect("(, comma, or Module Body"),
                    optional!(
                        lookahead_amount(2),
                        "<LBR>",
                        expect("_"),
                        "<US>",
                        expect("comma or )"),
                        zero_or_more!("<COMMA>", expect("_"), "<US>", expect("comma or )")),
                        "<RBR>",
                    ),
                ],
                seq!["NonExpPrefixOp", expect("_"), "<US>"],
                seq![
                    "<US>",
                    expect("prefix or postfix operator"),
                    choice!(seq!["InfixOp", expect("_"), "<US>"], "PostfixOp"),
                ],
            ),
        ],
    );
    add(
        "OperatorOrFunctionDefinition",
        Some("Definition"),
        seq![
            expect("LOCAL, Identifier or Operator Symbol"),
            optional!("<LOCAL>"),
            "<DEFBREAK>",
            expect("LOCAL, Identifier or Operator Symbol"),
            choice!(
                definition(
                    "Expression",
                    vec![
                        lookahead_expansion(seq!["<IDENTIFIER>", "<LSB>"]),
                        "Identifier".into(),
                        expect("["),
                        "<LSB>".into(),
                        expect("Identifier"),
                        "QuantBound".into(),
                        expect("COMMA or ]"),
                        zero_or_more!("<COMMA>", expect("Identifier"), "QuantBound"),
                        "<RSB>".into(),
                        "Expression".into(),
                    ],
                ),
                definition(
                    "Expression",
                    vec![
                        lookahead_expansion(seq!["<IDENTIFIER>", postfix_operator()]),
                        "PostfixLHS".into(),
                        "Expression".into(),
                    ],
                ),
                definition(
                    "Expression",
                    vec![
                        lookahead_expansion(seq!["<IDENTIFIER>", infix_operator()]),
                        "InfixLHS".into(),
                        "Expression".into(),
                    ],
                ),
                definition(
                    "Expression or Instance",
                    vec![
                        lookahead_expansion(seq!["<IDENTIFIER>", choice!("<LBR>", "<DEF>")]),
                        "IdentLHS".into(),
                        choice!("Expression", "Instantiation"),
                    ],
                ),
                definition("Expression", vec!["PrefixLHS".into(), "Expression".into()]),
            ),
        ],
    );
    add(
        "IdentifierTuple",
        Some("Identifier tuple"),
        seq![
            "<LAB>",
            expect("Identifier or >>"),
            optional!(
                "Identifier",
                expect("COMMA or >>"),
                zero_or_more!(
                    "<COMMA>",
                    expect("COMMA or >>"),
                    "Identifier",
                    expect("COMMA or >>")
                ),
            ),
            "<RAB>",
        ],
    );
    add(
        "IdentLHS",
        Some("Identifier LHS"),
        seq![
            "Identifier",
            expect("( or =="),
            optional!(
                "<LBR>",
                expect("Identifier Declaration, prefix op, _ or )"),
                choice!("IdentDecl", "SomeFixDecl"),
                expect("COMMA or )"),
                zero_or_more!(
                    "<COMMA>",
                    expect("Identifier Declaration, prefix op or _"),
                    choice!("IdentDecl", "SomeFixDecl"),
                    expect("COMMA or )"),
                ),
                "<RBR>",
            ),
        ],
    );
    add(
        "PrefixLHS",
        Some("Prefix LHS"),
        seq![nonexp_prefix_operator(), expect("Identifier"), "Identifier"],
    );
    add("InfixLHS", Some("Infix LHS"), seq!["Identifier", infix_operator(), "Identifier"]);
    add("PostfixLHS", Some("Postfix LHS"), seq!["Identifier", postfix_operator()]);
    add(
        "IdentDecl",
        Some("Identifier Declation"),
        seq![
            "Identifier",
            expect("( or ..."),
            optional!(
                "<LBR>",
                expect("_"),
                "<US>",
                expect("COMMA or )"),
                zero_or_more!("<COMMA>", expect("_"), "<US>", expect("COMMA or )")),
                "<RBR>",
            ),
        ],
    );
    add(
        "SomeFixDecl",
        Some("Op. Symbol Declaration"),
        seq![choice!(
            seq!["NonExpPrefixOp", expect("_"), "<US>"],
            seq![
                "<US>",
                expect("infix or postfix operator"),
                choice!(seq!["InfixOp", expect("_"), "<US>"], "PostfixOp"),
            ],
        )],
    );
    add(
        "Instance",
        Some("Instance"),
        seq![
            expect("LOCAL or instance"),
            optional!("<LOCAL>"),
            "Instantiation",
            expect("COMMA or Module Body")
        ],
    );
    add(
        "Instantiation",
        Some("NonLocalInstance"),
        seq![
            "<INSTANCE>",
            set_field_name_expecting("Module identifier"),
            "Identifier",
            expect("WITH or another definition."),
            optional!(
                "<WITH>",
                expect(""),
                "Substitution",
                expect(""),
                zero_or_more!(
                    lookahead_amount(3),
                    "<COMMA>",
                    expect(""),
                    "Substitution",
                    expect("")
                ),
            ),
        ],
    );
    add(
        "Substitution",
        Some("Substitution"),
        seq![
            choice!("Identifier", "NonExpPrefixOp", "InfixOp", "PostfixOp"),
            expect("<-"),
            "<SUBSTITUTE>",
            expect("Expression or Op. Symbol"),
            "OpOrExpr",
        ],
    );
    add("Identifier", None, seq!["<IDENTIFIER>"]);
}
