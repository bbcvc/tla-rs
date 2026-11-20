//! The productions of `javacc/tla+.jj` that build an expression from its operators and
//! operands as `OperatorStack` orders them: Expression, ExtendableExpr, and the primitive
//! expressions.

use std::collections::HashMap;

use super::expressions::prefix_operator;
use super::grammar::{
    Production, Unit, action, choice, expect, lookahead_amount, lookahead_both,
    lookahead_expansion, lookahead_semantic, optional, seq, zero_or_more,
};
use super::operators::{
    Fix, StackElement, VOID_OPERATOR, is_looser, push_on_stack, push_operand, push_operator,
    reduce_postfix, reduce_stack,
};
use super::productions::add_production;
use super::semantics::{arguments, is_above_current, is_label, proof_level, set_field_name};
use super::{Node, State};

/// The prefix operators that Expression and ExtendableExpr share. Each use is a separate
/// lookahead site, as in the generated parser.
fn prefix_operators() -> Unit {
    zero_or_more!(
        lookahead_both(choice!(prefix_operator(), "<op_77>"), is_above_current),
        choice!("PrefixOp", "InfixOp"),
        push_operator(),
    )
}

/// The operand that Expression and ExtendableExpr share.
fn operand() -> Unit {
    choice!(
        seq![lookahead_both(seq!["OpenStart"], is_above_current), "OpenExpression", push_operand()],
        seq![lookahead_semantic(is_above_current), "ExtendableExpr"],
    )
}

pub(super) fn add(productions: &mut HashMap<&'static str, Production>) {
    let mut add = |name, message, body, exit: Option<super::grammar::Exit>| {
        add_production(productions, name, message, body, exit);
    };
    // OperatorStack.finalReduce, which pushes an operator that binds looser than any other,
    // whose node, null in Java, is never printed.
    add(
        "Expression",
        Some("Expression"),
        seq![
            action(|state| {
                state.operator_stacks.push(Vec::new());
                None
            }),
            prefix_operators(),
            operand(),
        ],
        Some(Box::new(|frame, state| {
            let node = frame.heirs[0].clone();
            state.operator_stack().push(StackElement { node, operator: Some(&VOID_OPERATOR) });
            let message = reduce_stack(state);
            frame.node = Some(state.operator_stack()[0].node.clone());
            state.operator_stacks.pop();
            message
        })),
    );
    add("ExtendableExpr", Some("ExtendableExpr"), extendable_expression(), None);
    add(
        "PrimitiveExp",
        Some("Primitive expression"),
        seq![choice!(
            seq![lookahead_both(seq!["String"], is_above_current), "String"],
            seq![lookahead_both(seq!["<NUMBER_LITERAL>"], is_above_current), "Number"],
            seq![
                choice!(
                    "Identifier",
                    seq![
                        choice!("<ProofStepLexeme>", "<ProofImplicitStepLexeme>"),
                        action(|state| {
                            let token = state.token;
                            if proof_level(state) < 0 && state.proof_levels.len() <= 1 {
                                let location = state.location(token, token);
                                return Some(format!(
                                    "{location}: Step number used outside proof."
                                ));
                            }
                            let image = &state.token(token).image;
                            (image.chars().nth(1) == Some('+')).then(|| {
                                let location = state.location(token, token);
                                format!("{location}: <+> step number used in an expression.")
                            })
                        }),
                    ],
                    "InfixOp",
                    "PostfixOp",
                    seq![lookahead_expansion(seq!["<op_76>"]), "NonExpPrefixOp"],
                ),
                optional!(lookahead_amount(2), "OpArgs"),
                zero_or_more!("BangExt"),
            ],
        )],
        Some(Box::new(|frame, _| {
            let head = &frame.heirs[0];
            frame.node = if matches!(head.kind, "String" | "Number") {
                Some(head.clone())
            } else if arguments(&frame.heirs).is_some() {
                Some(Node::new("OpApplication", frame.heirs.clone()))
            } else if frame.heirs.len() == 1 {
                Some(Node::new("GeneralId", frame.heirs.clone()))
            } else {
                None
            };
            None
        })),
    );
    add(
        "BangExt",
        Some("Bang Extension"),
        seq![
            "<BANG>",
            choice!(
                seq![
                    choice!(
                        seq![
                            lookahead_both(seq!["Identifier"], |state: &mut State| {
                                let token = state.get_token(1);
                                state.token(token).image != "@"
                            }),
                            "Identifier",
                        ],
                        "NonExpPrefixOp",
                        "InfixOp",
                        "PostfixOp",
                    ),
                    optional!(lookahead_amount(2), "OpArgs"),
                ],
                "OpArgs",
                "StructOp",
            ),
        ],
        None,
    );
    add(
        "StructOp",
        Some("StructOp"),
        seq![
            expect("`<<' , `>>' , `:' , `@' , or number"),
            choice!(
                "<LAB>",
                "<RAB>",
                "<COLON>",
                "Number",
                seq![
                    lookahead_semantic(|state| {
                        let token = state.get_token(1);
                        state.token(token).image == "@"
                    }),
                    "<IDENTIFIER>",
                ],
            ),
        ],
        Some(Box::new(|frame, state| {
            let number = &frame.heirs[0];
            (number.kind == "Number" && number.heirs.len() > 1)
                .then(|| format!("Illegal structural term at {}", state.node_location(number)))
        })),
    );
    add(
        "OpenStart",
        None,
        seq![choice!(
            "<CASE>",
            "<CHOOSE>",
            "<EXISTS>",
            "<FORALL>",
            "<IF>",
            "<LET>",
            "<T_EXISTS>",
            "<T_FORALL>"
        )],
        None,
    );
}

fn extendable_expression() -> Unit {
    seq![
        choice!(
            seq![
                lookahead_both(choice!("<AND>", "<OR>"), |state: &mut State| {
                    // OperatorStack.preInEmptyTop.
                    let top = state.operator_stacks.last().and_then(|stack| stack.last());
                    top.is_none_or(|top| {
                        top.operator.is_some_and(|operator| operator.fix != Fix::Postfix)
                    })
                }),
                "Junctions",
            ],
            "ParenthesesExpression",
            "PrimitiveExp",
        ),
        push_operand(),
        zero_or_more!(choice!(
            seq![lookahead_both(seq!["PostfixOp"], is_above_current), "PostfixOp", push_operator()],
            seq![
                lookahead_both(seq!["<DOT>"], is_above_current),
                "<DOT>",
                action(|state| {
                    set_field_name(state);
                    None
                }),
                lookahead_semantic(is_above_current),
                "Identifier",
                // OperatorStack.reduceRecord, which first applies a postfix operator on top.
                action(|state| {
                    let (field, dot) = (state.heir(1), state.heir(2));
                    let stack = state.operator_stack();
                    if stack[stack.len() - 1].operator.is_some() {
                        let top = stack.len();
                        reduce_postfix(stack, top);
                    }
                    let last = stack.len() - 1;
                    let node =
                        Node::new("RecordComponent", vec![stack[last].node.clone(), dot, field]);
                    stack[last] = StackElement { node, operator: None };
                    None
                }),
            ],
            seq![
                lookahead_both(seq!["<LSB>"], is_above_current),
                expect("function argument"),
                "SBracketCases",
                // TLAplusParser.isGenOp, which holds of a function application.
                push_on_stack(|node| node.kind == "FcnAppl"),
            ],
        )),
        optional!(choice!(
            seq![
                lookahead_both(seq!["InfixOp"], is_above_current),
                "InfixOp",
                push_operator(),
                prefix_operators(),
                operand(),
            ],
            seq![
                lookahead_both(seq!["<COLONCOLON>"], is_above_current),
                "<COLONCOLON>",
                action(|state| {
                    let stack = state.operator_stack();
                    if !is_label(&stack[stack.len() - 1].node) {
                        let token = state.token;
                        return Some(format!(
                            "`::' at {} does not follow a label.",
                            state.location(token, token)
                        ));
                    }
                    stack.pop();
                    None
                }),
                "Expression",
                // TLAplusParser.labelDoesNotChangeParse, given the operator parsed last.
                action(|state| {
                    let labeled = state.heir(1);
                    let operator = state.operator_stack().last().and_then(|top| top.operator);
                    let is_reordered = matches!(labeled.kind, "InfixExpr" | "PostfixExpr")
                        && operator.is_some_and(|operator| {
                            state.last_operator.is_some_and(|last| !is_looser(operator, last))
                        });
                    if is_reordered {
                        let label = state.heir(3);
                        return Some(format!(
                            "Removing label at {} would change expression parsing.",
                            state.node_location(&label)
                        ));
                    }
                    let node = Node::new("Label", vec![state.heir(3), state.heir(2), labeled]);
                    state.operator_stack().push(StackElement { node, operator: None });
                    None
                }),
            ],
        )),
    ]
}
