//! The productions of `javacc/tla+.jj` for expressions and operators.

use std::collections::HashMap;

use super::grammar::{
    Production, Unit, UnitKind, action, choice, expect, lookahead, lookahead_amount,
    lookahead_both, lookahead_expansion, lookahead_semantic, one_or_more, optional, seq, tokens,
    zero_or_more,
};
use super::kinds::kind;
use super::operators::{function_operator, set_last_operator};
use super::productions::add_production;
use super::semantics::{
    INFIX_KINDS, POSTFIX_KINDS, is_above_current, is_case_separator, is_new_bullet,
    match_fcn_const, misindented, set_field_name,
};
use super::{Junction, Node, State};

fn prefix_operator_kinds() -> Vec<u16> {
    [
        "op_26", "op_29", "op_58", "CASESEP", "op_61", "op_112", "op_113", "op_114", "op_115",
        "op_116",
    ]
    .map(kind)
    .to_vec()
}

pub(super) fn prefix_operator() -> Unit {
    tokens(prefix_operator_kinds())
}

pub(super) fn nonexp_prefix_operator() -> Unit {
    tokens(prefix_operator_kinds().into_iter().chain([kind("op_76")]))
}

pub(super) fn infix_operator() -> Unit {
    Unit::new(UnitKind::Tokens(*INFIX_KINDS))
}

pub(super) fn postfix_operator() -> Unit {
    Unit::new(UnitKind::Tokens(*POSTFIX_KINDS))
}

pub(super) fn set_field_name_expecting(expecting: &'static str) -> Unit {
    action(move |state| {
        state.expecting = expecting;
        set_field_name(state);
        None
    })
}

/// A junction list whose bullets are `bullet`.
fn junctions_of(bullet: &'static str) -> Unit {
    seq![
        lookahead_expansion(seq![bullet]),
        "JuncItem",
        zero_or_more!(lookahead_semantic(is_new_bullet), "JuncItem"),
    ]
}

/// The node a production returns: the first of what it matched.
fn first_heir(frame: &mut super::Frame, _: &mut State) -> Option<String> {
    frame.node = Some(frame.heirs[0].clone());
    None
}

pub(super) fn add(productions: &mut HashMap<&'static str, Production>) {
    let mut add = |name, message, body, exit: Option<super::grammar::Exit>| {
        add_production(productions, name, message, body, exit);
    };
    add("PrefixOp", None, seq![prefix_operator(), set_last_operator()], None);
    add("NonExpPrefixOp", None, seq![nonexp_prefix_operator(), set_last_operator()], None);
    add("InfixOp", Some("Infix Op"), seq![infix_operator(), set_last_operator()], None);
    add("PostfixOp", None, seq![postfix_operator(), set_last_operator()], None);
    add(
        "ParenthesesExpression",
        None,
        seq![choice!("ParenExpr", "BraceCases", "SBracketCases", "TupleOrAction", "FairnessExpr")],
        None,
    );
    add(
        "OpenExpression",
        None,
        seq![choice!(
            "SomeQuant",
            "SomeTQuant",
            "IfThenElse",
            "Case",
            "LetIn",
            "UnboundOrBoundChoose"
        )],
        None,
    );
    add("String", Some("String"), seq!["<STRING_LITERAL>"], None);
    add(
        "Number",
        None,
        seq!["<NUMBER_LITERAL>", optional!(lookahead_amount(2), "<DOT>", "<NUMBER_LITERAL>")],
        None,
    );
    add(
        "OpArgs",
        Some("Optional Arguments"),
        seq!["<LBR>", "OpOrExpr", zero_or_more!("<COMMA>", "OpOrExpr"), "<RBR>"],
        None,
    );
    let after_operator = [
        "COMMA",
        "RBR",
        "DEFBREAK",
        "LOCAL",
        "INSTANCE",
        "THEOREM",
        "ASSUME",
        "END_MODULE",
        "SEPARATOR",
        "_BM0",
        "ASSUMPTION",
        "CONSTANT",
        "VARIABLE",
        "RECURSIVE",
    ];
    add(
        "OpOrExpr",
        None,
        seq![choice!(
            seq![
                lookahead(
                    2,
                    Some(seq![
                        choice!(nonexp_prefix_operator(), infix_operator(), postfix_operator()),
                        tokens(after_operator.map(kind)),
                    ]),
                    Some(Box::new(is_above_current)),
                ),
                choice!(
                    "NonExpPrefixOp",
                    seq![
                        "InfixOp",
                        action(|state| {
                            let token = state.token;
                            matches!(state.token(token).image.as_str(), "\\X" | "\\times").then(
                                || {
                                    format!(
                                        "{}: \\X may not be used as an infix operator.",
                                        state.location(token, token)
                                    )
                                },
                            )
                        }),
                    ],
                    "PostfixOp",
                ),
            ],
            seq![lookahead_both(seq!["<LAMBDA>"], is_above_current), "Lambda"],
            "Expression",
        )],
        Some(Box::new(first_heir)),
    );
    add("ParenExpr", None, seq!["<LBR>", "Expression", "<RBR>"], None);
    add(
        "SomeQuant",
        Some("Quantified form"),
        seq![
            choice!("<EXISTS>", "<FORALL>"),
            choice!(
                seq![
                    lookahead_expansion(seq![
                        "<IDENTIFIER>",
                        zero_or_more!("<COMMA>", "<IDENTIFIER>"),
                        "<COLON>"
                    ]),
                    "Identifier",
                    zero_or_more!("<COMMA>", "Identifier"),
                ],
                seq!["QuantBound", zero_or_more!("<COMMA>", "QuantBound")],
            ),
            "<COLON>",
            "Expression",
        ],
        None,
    );
    add(
        "SomeTQuant",
        Some("Bound Quantified Expression"),
        seq![
            choice!("<T_EXISTS>", "<T_FORALL>"),
            "Identifier",
            zero_or_more!("<COMMA>", "Identifier"),
            "<COLON>",
            "Expression"
        ],
        None,
    );
    add(
        "QuantBound",
        Some("Quant Bound"),
        seq![
            choice!(
                "IdentifierTuple",
                seq!["Identifier", zero_or_more!("<COMMA>", "Identifier", expect(", or \\in"))],
            ),
            "<IN>",
            "Expression",
        ],
        None,
    );
    add(
        "BraceCases",
        Some("Some { } form"),
        seq![
            "<LBC>",
            optional!(choice!(
                seq![
                    lookahead_semantic(match_fcn_const),
                    choice!("IdentifierTuple", "Identifier"),
                    expect("\\in"),
                    "<IN>",
                    "Expression",
                    expect("':', ',' or '}'"),
                    optional!(choice!(
                        seq!["<COLON>", "Expression"],
                        one_or_more!("<COMMA>", "Expression")
                    )),
                ],
                seq![
                    lookahead_expansion(seq![
                        choice!("IdentifierTuple", "<IDENTIFIER>"),
                        "<COMMA>"
                    ]),
                    "Expression",
                    zero_or_more!("<COMMA>", "Expression"),
                ],
                seq![
                    lookahead_expansion(seq![
                        choice!("IdentifierTuple", "<IDENTIFIER>"),
                        "<COLON>"
                    ]),
                    "Expression",
                    "<COLON>",
                    "QuantBound",
                    zero_or_more!("<COMMA>", "QuantBound"),
                ],
                seq![
                    "Expression",
                    optional!(choice!(
                        seq![
                            "<COLON>",
                            action(|state| {
                                let expression = state.heir(2);
                                let is_membership = expression.kind == "InfixExpr"
                                    && state.token(expression.heirs[1].first).image == "\\in";
                                is_membership.then(|| {
                                    format!(
                                        "Form {{a \\in b : c \\in d }}, at line {}, is not allowed",
                                        state.token(state.token).line
                                    )
                                })
                            }),
                            "QuantBound",
                            zero_or_more!("<COMMA>", "QuantBound"),
                        ],
                        one_or_more!("<COMMA>", "Expression"),
                    )),
                ],
            )),
            "<RBC>",
        ],
        None,
    );
    add(
        "SBracketCases",
        Some("Some [] Form"),
        seq![
            "<LSB>",
            choice!(
                seq![
                    lookahead_semantic(match_fcn_const),
                    "QuantBound",
                    zero_or_more!("<COMMA>", "QuantBound"),
                    "<MAPTO>",
                    "Expression",
                    "<RSB>",
                ],
                seq![
                    lookahead_expansion(seq!["<IDENTIFIER>", "<MAPTO>"]),
                    "FieldVal",
                    zero_or_more!("<COMMA>", "FieldVal"),
                    "<RSB>",
                ],
                seq![
                    lookahead_semantic(|state| {
                        let (first, second) = (state.get_token(1), state.get_token(2));
                        state.kind_of(second) == kind("MAPTO")
                            && super::semantics::FIELD_NAME_KINDS.contains(state.kind_of(first))
                    }),
                    action(|state| {
                        let token = state.get_token(1);
                        state.tokens[token].kind = kind("IDENTIFIER");
                        None
                    }),
                    "FieldVal",
                    zero_or_more!("<COMMA>", "FieldVal"),
                    "<RSB>",
                ],
                seq![
                    lookahead_expansion(seq!["<IDENTIFIER>", "<COLON>"]),
                    "FieldSet",
                    zero_or_more!("<COMMA>", "FieldSet"),
                    "<RSB>",
                ],
                seq![
                    "Expression",
                    choice!(
                        seq![
                            zero_or_more!("<COMMA>", "Expression"),
                            "<RSB>",
                            action(|state| {
                                let frame =
                                    state.frames.last_mut().expect("SBracketCases is parsed");
                                frame.node = Some(Node::new("FcnAppl", frame.heirs.clone()));
                                state.last_operator = Some(function_operator());
                                None
                            }),
                        ],
                        seq!["<ARROW>", "Expression", "<RSB>"],
                        seq![
                            "<EXCEPT>",
                            "ExceptSpec",
                            zero_or_more!("<COMMA>", "ExceptSpec"),
                            "<RSB>"
                        ],
                        seq!["<ARSB>", "ReducedExpression"],
                    ),
                ],
            ),
        ],
        None,
    );
    add("FieldVal", Some("Field Value"), seq!["Identifier", "<MAPTO>", "Expression"], None);
    add("FieldSet", Some("Field Set"), seq!["Identifier", "<COLON>", "Expression"], None);
    add(
        "ExceptSpec",
        Some("Except Spec"),
        seq!["<BANG>", one_or_more!("ExceptComponent", expect("= or ,")), "<EQUALS>", "Expression"],
        None,
    );
    add(
        "ExceptComponent",
        Some("Except Component"),
        seq![choice!(
            seq![
                "<DOT>",
                action(|state| {
                    set_field_name(state);
                    None
                }),
                "Identifier",
            ],
            seq!["<LSB>", "Expression", zero_or_more!("<COMMA>", "Expression"), "<RSB>"],
        )],
        None,
    );
    add(
        "TupleOrAction",
        Some("Some << -- >> or >>_ Form"),
        seq![
            "<LAB>",
            optional!("Expression", zero_or_more!("<COMMA>", "Expression")),
            choice!("<RAB>", seq!["<ARAB>", "ReducedExpression"]),
        ],
        None,
    );
    // The innermost NoOpExtension sets FairnessHook to its arguments, which end with `)`.
    add(
        "NoOpExtension",
        None,
        seq![
            "Identifier",
            optional!(lookahead_amount(2), "OpArgs"),
            choice!(
                seq!["<BANG>", "NoOpExtension"],
                action(|state| {
                    state.is_fairness_hooked = state.kind_of(state.token) == kind("RBR");
                    None
                }),
            ),
        ],
        None,
    );
    add(
        "ReducedExpression",
        Some("restricted form of expression"),
        seq![choice!("NoOpExtension", "ParenExpr", "BraceCases", "SBracketCases", "TupleOrAction")],
        None,
    );
    add(
        "FairnessExpr",
        Some("Fairness Expression"),
        seq![
            action(|state| {
                state.is_fairness_hooked = false;
                state.is_fairness_parenthesized.push(false);
                None
            }),
            choice!("<WF>", "<SF>"),
            "ReducedExpression",
            optional!(
                lookahead_amount(2),
                "<LBR>",
                "Expression",
                "<RBR>",
                action(|state| {
                    if let Some(last) = state.is_fairness_parenthesized.last_mut() {
                        *last = true;
                    }
                    None
                }),
            ),
        ],
        Some(Box::new(|frame, state| {
            let is_parenthesized = state.is_fairness_parenthesized.pop().unwrap_or(false);
            if is_parenthesized || state.is_fairness_hooked {
                return None;
            }
            let first = state.token(frame.heirs[0].first);
            Some(format!(
                "Ill-structured fairness expression at line {}, column {}",
                first.line, first.column
            ))
        })),
    );
    add(
        "IfThenElse",
        Some("IF THEN ELSE"),
        seq!["<IF>", "Expression", "<THEN>", "Expression", "<ELSE>", "Expression"],
        None,
    );
    add(
        "Case",
        Some("CASE Expression"),
        seq![
            "<CASE>",
            "CaseArm",
            zero_or_more!(
                lookahead_semantic(|state| {
                    if !is_case_separator(state) {
                        return false;
                    }
                    let second = state.get_token(2);
                    state.kind_of(second) != kind("OTHER")
                }),
                "<CASESEP>",
                "CaseArm",
            ),
            optional!(lookahead_semantic(is_case_separator), "<CASESEP>", "OtherArm"),
        ],
        None,
    );
    add("CaseArm", Some("Case Arm"), seq!["Expression", "<ARROW>", "Expression"], None);
    add("OtherArm", Some("Case Other Arm"), seq!["<OTHER>", "<ARROW>", "Expression"], None);
    add(
        "LetIn",
        Some("Case Other Arm"),
        seq!["<LET>", "LetDefinitions", "<LETIN>", "Expression"],
        None,
    );
    add(
        "LetDefinitions",
        Some("Let Definitions"),
        seq![one_or_more!(choice!("OperatorOrFunctionDefinition", "Recursive"))],
        None,
    );
    add(
        "Junctions",
        Some("AND-OR Junction"),
        seq![
            action(|state| {
                let token = state.get_token(1);
                let token = state.token(token);
                let junction = Junction { kind: token.kind, column: token.column };
                state.junctions.push(junction);
                None
            }),
            choice!(junctions_of("<OR>"), junctions_of("<AND>"),),
            action(|state| {
                state.junctions.pop();
                None
            }),
        ],
        None,
    );
    // TLAplusParser.checkIndentation.
    add(
        "JuncItem",
        Some("Junction Item"),
        seq![choice!("<OR>", "<AND>"), "Expression"],
        Some(Box::new(|frame, state| {
            let item = misindented(state, &frame.heirs[1])?;
            Some(format!(
                "Item at {} is not properly indented inside conjunction or  disjunction list item at {}",
                state.node_location(item),
                state.location(frame.heirs[0].first, frame.heirs[1].last)
            ))
        })),
    );
    add(
        "UnboundOrBoundChoose",
        Some("(Un)Bounded Choose"),
        seq![
            "<CHOOSE>",
            choice!("Identifier", "IdentifierTuple"),
            "MaybeBound",
            "<COLON>",
            "Expression"
        ],
        None,
    );
    add(
        "Lambda",
        Some("Lambda"),
        seq![
            "<LAMBDA>",
            expect("Identifier"),
            "Identifier",
            expect("`,' or `:'"),
            zero_or_more!("<COMMA>", expect("Identifier"), "Identifier", expect("`,' or `:'")),
            "<COLON>",
            expect("Expression"),
            "Expression",
        ],
        None,
    );
}
