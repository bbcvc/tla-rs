//! The productions of `javacc/tla+.jj` for assumptions, theorems, and proofs.

use std::collections::HashMap;

use super::grammar::{
    Production, Unit, action, choice, expect, lookahead_amount, lookahead_expansion,
    lookahead_semantic, one_or_more, optional, seq, tokens, zero_or_more,
};
use super::kinds::kind;
use super::productions::add_production;
use super::semantics::{begins_proof, belch_def, check_step_level};

fn use_item() -> Unit {
    choice!(seq!["<MODULE>", expect("identifier"), "Identifier"], "Expression")
}

fn assume_prove_item() -> Unit {
    choice!(
        seq![
            lookahead_semantic(|state| {
                if state.next_kind_is(&["ASSUME", "BOXASSUME"]) {
                    return true;
                }
                let (second, third) = (state.get_token(2), state.get_token(3));
                state.kind_of(second) == kind("COLONCOLON")
                    && [kind("ASSUME"), kind("BOXASSUME")].contains(&state.kind_of(third))
            }),
            "AssumeProve",
        ],
        "NewSymb",
        "Expression",
    )
}

fn set_terminal_proof(is_terminal_proof: bool) -> Unit {
    action(move |state| {
        state.is_terminal_proof = is_terminal_proof;
        None
    })
}

/// An alternative of OperatorOrFunctionDefinition: a left-hand side, then `==`, then a body.

fn step_start() -> Unit {
    tokens(
        [
            "ProofStepLexeme",
            "ProofImplicitStepLexeme",
            "ProofStepDotLexeme",
            "BareLevelLexeme",
            "UnnumberedStepLexeme",
        ]
        .map(kind),
    )
}

pub(super) fn add(productions: &mut HashMap<&'static str, Production>) {
    let mut add = |name, message, body| add_production(productions, name, message, body, None);
    add(
        "Assumption",
        Some("Assumption"),
        seq![
            expect("ASSUM..."),
            choice!("<ASSUMPTION>", "<ASSUME>"),
            optional!(
                lookahead_amount(2),
                optional!("<DEFBREAK>"),
                "Identifier",
                expect("=="),
                "<DEF>"
            ),
            action(|state| {
                belch_def(state);
                state.expecting = "Expression";
                None
            }),
            "Expression",
        ],
    );
    // A label returns from AssumeProve after the labeled AssumeProve, which a choice expresses.
    add(
        "AssumeProve",
        Some("Assume-Prove"),
        seq![choice!(
            seq!["Identifier", "<COLONCOLON>", "AssumeProve"],
            seq![
                choice!("<ASSUME>", "<BOXASSUME>"),
                expect("Expression, Declaration, or AssumeProve"),
                assume_prove_item(),
                expect("PROVE or `,'"),
                zero_or_more!(
                    "<COMMA>",
                    expect("Expression, Declaration, or AssumeProve"),
                    assume_prove_item(),
                    expect("PROVE or `,'"),
                ),
                choice!("<PROVE>", "<BOXPROVE>"),
                expect("Expression"),
                "Expression",
            ],
        )],
    );
    add(
        "NewSymb",
        Some("NEW symbol declaration"),
        seq![
            expect("NEW, CONSTANT, VARIABLE, STATE, ACTION, or TEMPORAL"),
            choice!(
                seq![
                    lookahead_amount(2),
                    choice!(
                        seq![lookahead_amount(2), "<NEW>", "<CONSTANT>"],
                        "<NEW>",
                        "<CONSTANT>"
                    ),
                    expect("Constant declaration"),
                    choice!(
                        seq![
                            lookahead_amount(2),
                            "IdentDecl",
                            optional!(
                                "<IN>",
                                action(|state| {
                                    let declaration = state.heir(2);
                                    (declaration.heirs.len() > 1).then(|| {
                                        format!(
                                            "declared symbol with arguments before \\in at {}",
                                            state.node_location(&declaration)
                                        )
                                    })
                                }),
                                expect("Expression"),
                                "Expression",
                            ),
                        ],
                        "SomeFixDecl",
                    ),
                ],
                seq![
                    lookahead_amount(2),
                    optional!("<NEW>"),
                    "<VARIABLE>",
                    expect("Identifier"),
                    "Identifier"
                ],
                seq![
                    lookahead_amount(2),
                    optional!("<NEW>"),
                    choice!("<STATE>", "<ACTION>", "<TEMPORAL>"),
                    expect("Declaration"),
                    choice!("IdentDecl", "SomeFixDecl"),
                ],
            ),
        ],
    );
    add(
        "MaybeBound",
        Some("Domain binding"),
        seq![optional!("<IN>", expect("Expression"), "Expression")],
    );
    add(
        "Theorem",
        Some("Theorem"),
        seq![
            expect("THEOREM, PROPOSITION"),
            choice!("<THEOREM>", "<PROPOSITION>"),
            expect("Identifier, Assume-Prove or Expression"),
            optional!(lookahead_amount(2), "Identifier", expect("=="), "<DEF>"),
            action(|state| {
                belch_def(state);
                None
            }),
            choice!(
                seq![
                    lookahead_amount(3),
                    lookahead_semantic(|state| state.next_kind_is(&["ASSUME", "BOXASSUME"])),
                    "AssumeProve",
                ],
                "Expression",
            ),
            optional!(lookahead_semantic(begins_proof), "Proof"),
        ],
    );
    add(
        "Proof",
        Some("Proof"),
        seq![
            action(|state| {
                state.proof_levels.push(-1);
                None
            }),
            choice!(
                seq![
                    lookahead_semantic(|state| {
                        if state.next_kind_is(&["BY"]) {
                            return true;
                        }
                        let second = state.get_token(2);
                        state.kind_of(second) == kind("BY")
                    }),
                    "UseOrHideOrBy",
                ],
                seq![lookahead_amount(2), optional!("<PROOF>"), choice!("<OBVIOUS>", "<OMITTED>")],
                seq![
                    optional!(lookahead_amount(2), "<PROOF>"),
                    zero_or_more!(
                        lookahead_semantic(|state| {
                            let second = state.get_token(2);
                            state.kind_of(second) != kind("QED")
                        }),
                        "Step",
                        expect("a proof step"),
                    ),
                    "QEDStep",
                ],
            ),
            action(|state| {
                state.proof_levels.pop();
                None
            }),
        ],
    );
    add(
        "UseOrHideOrBy",
        Some("UseOrHideOrBy"),
        seq![
            choice!(
                seq![optional!("<PROOF>"), "<BY>", set_terminal_proof(true), optional!("<ONLY>")],
                seq!["<USE>", set_terminal_proof(false), optional!("<ONLY>")],
                seq!["<HIDE>", set_terminal_proof(false)],
            ),
            expect("an expression, `MODULE' or `DEF'"),
            optional!(
                use_item(),
                zero_or_more!(
                    "<COMMA>",
                    expect("MODULE or expression"),
                    use_item(),
                    action(|state| {
                        state.expecting = match state.is_terminal_proof {
                            true => "comma, DEF, or [.]",
                            false => "comma, DEF, or proof step",
                        };
                        None
                    }),
                ),
            ),
            optional!(
                "<DF>",
                expect("MODULE or expression"),
                use_item(),
                zero_or_more!(
                    "<COMMA>",
                    expect("MODULE or expression"),
                    use_item(),
                    action(|state| {
                        state.expecting = match state.is_terminal_proof {
                            true => "comma or [.]",
                            false => "comma or proof step",
                        };
                        None
                    }),
                ),
            ),
            action(|state| {
                if state.is_terminal_proof {
                    state.expecting = "[.]";
                }
                None
            }),
        ],
    );
    add(
        "QEDStep",
        Some("QED step"),
        seq![
            expect("Step number"),
            step_start(),
            check_step_level("QED step's number has bad level."),
            expect("QED"),
            "<QED>",
            optional!(lookahead_semantic(begins_proof), "Proof"),
        ],
    );
    add(
        "Step",
        Some("Step"),
        seq![
            expect("Step number"),
            step_start(),
            check_step_level("step's number has bad level."),
            expect("proof step"),
            choice!(
                seq![
                    lookahead_semantic(|state| state.next_kind_is(&["USE", "HIDE"])),
                    "UseOrHideOrBy"
                ],
                seq![
                    lookahead_semantic(|state| state.next_kind_is(&["INSTANCE"])),
                    "Instantiation"
                ],
                seq![
                    lookahead_semantic(|state| state.next_kind_is(&["DEFBREAK", "DEFINE"])),
                    "DefStep"
                ],
                "HaveStep",
                "TakeStep",
                "WitnessStep",
                "PickStep",
                "CaseStep",
                "AssertStep",
            ),
            optional!(
                lookahead_semantic(begins_proof),
                action(|state| {
                    let step = state.heir(1);
                    match matches!(step.kind, "PickStep" | "CaseStep" | "AssertStep") {
                        true => None,
                        false => Some(format!(
                            "{}: proof of step that does not take a proof.",
                            state.node_location(&step)
                        )),
                    }
                }),
                "Proof",
            ),
        ],
    );
    add(
        "DefStep",
        Some("DefStep"),
        seq![
            optional!("<DEFINE>"),
            one_or_more!(lookahead_amount(2), "OperatorOrFunctionDefinition")
        ],
    );
    add("HaveStep", Some("HaveStep"), seq!["<HAVE>", expect("expression"), "Expression"]);
    add(
        "TakeStep",
        Some("TakeStep"),
        seq![
            "<TAKE>",
            expect("identifier"),
            choice!(
                seq![
                    lookahead_expansion(choice!(
                        seq!["<IDENTIFIER>", zero_or_more!("<COMMA>", "<IDENTIFIER>"), "<IN>"],
                        "<LAB>",
                    )),
                    "QuantBound",
                    expect("comma or step"),
                    zero_or_more!(
                        "<COMMA>",
                        expect("identifier or tuple of identifiers"),
                        "QuantBound",
                        expect("comma or proof step"),
                    ),
                ],
                seq![
                    "Identifier",
                    expect("comma or proof step"),
                    zero_or_more!(
                        "<COMMA>",
                        expect("identifier"),
                        "Identifier",
                        expect("comma or proof step")
                    ),
                ],
            ),
        ],
    );
    add(
        "WitnessStep",
        Some("WitnessStep"),
        seq![
            "<WITNESS>",
            expect("expression"),
            "Expression",
            zero_or_more!("<COMMA>", expect("expression"), "Expression", expect("comma or colon")),
        ],
    );
    add(
        "PickStep",
        Some("PickStep"),
        seq![
            "<PICK>",
            expect("identifier"),
            choice!(
                seq![
                    lookahead_expansion(seq![
                        "<IDENTIFIER>",
                        zero_or_more!("<COMMA>", "<IDENTIFIER>"),
                        "<COLON>"
                    ]),
                    "Identifier",
                    expect("comma, or colon"),
                    zero_or_more!(
                        "<COMMA>",
                        expect("identifier"),
                        "Identifier",
                        expect("comma or colon")
                    ),
                ],
                seq![
                    "QuantBound",
                    expect("comma or colon"),
                    zero_or_more!(
                        "<COMMA>",
                        expect("identifier or tuple of identifiers"),
                        "QuantBound",
                        expect("comma or colon"),
                    ),
                ],
            ),
            "<COLON>",
            expect("expression"),
            "Expression",
        ],
    );
    add("CaseStep", Some("CaseStep"), seq!["<CASE>", expect("expression"), "Expression"]);
    add(
        "AssertStep",
        Some("AssertStep"),
        seq![
            optional!("<SUFFICES>", expect("expression or ASSUME/PROVE")),
            choice!(
                "Expression",
                seq![
                    lookahead_semantic(|state| state.next_kind_is(&["ASSUME", "BOXASSUME"])),
                    "AssumeProve"
                ],
            ),
        ],
    );
}
