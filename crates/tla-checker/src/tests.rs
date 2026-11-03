use crate::Status;
use crate::testing::{System, run};

const SPEC: &str = "CONSTANT C\nInit == x = 0\nNext == x' = C\nSpec == Init /\\ [][Next]_x\n\
    Foo == x\nTwo == 2\nLevel == TLCGet(\"level\")\nDiameter == TLCGet(\"diameter\")";

fn check(config: &str) -> crate::Outcome {
    let config = format!("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n{config}");
    run(SPEC, &config, System { init: vec![0], next: |_| vec![0] })
}

#[test]
fn rejects_substitutes_for_constants_that_need_a_state() {
    let outcome = check("CONSTANT C <- Foo");
    assert_eq!(
        (outcome.status, outcome.message.as_deref()),
        (Status::Error, Some("The configuration file substitutes constant C with non-constant Foo"))
    );
    // TLC reads the statistics only once it creates its model checker.
    assert_eq!(check("CONSTANT C <- Diameter").status, Status::Error);
    // A substitute that evaluates without a state is fine, whatever its level.
    assert_eq!(check("CONSTANT C <- Level").status, Status::Success);
    assert_eq!(check("CONSTANT C <- Two").status, Status::Success);
}
