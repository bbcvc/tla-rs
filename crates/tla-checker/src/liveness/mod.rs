//! Liveness checking, as TLC does it with `-lncheck final`: the temporal properties are
//! negated and conjoined with the fairness of the spec, the formula's tableau is paired with the
//! states the search finds into a behavior graph, and once the search is done, a strongly
//! connected component of the graph that satisfies a way of violating the properties gives a
//! counterexample. Ported from tla-ts `liveness.ts`, `tableau.ts`, and `liveness-checker.ts`.

pub mod checker;
pub mod convert;
pub mod graph;
pub mod lasso;
pub mod live;
pub mod tableau;

#[cfg(test)]
pub(crate) mod tests {
    use std::sync::Arc;

    use tla_eval::{Evaluator, Frames};
    use tla_resolve::DefId;

    use crate::Status;
    use crate::testing::{System, run};

    /// Frames for atoms that tests never evaluate.
    pub(crate) fn frames() -> Frames {
        let evaluator = Evaluator::new(Arc::new(crate::testing::spec("")), Vec::new());
        evaluator.module_frames(DefId(0))
    }

    const SPEC: &str = "Init == x = 0\nNext == x < 3 /\\ x' = x + 1\n\
        Spec == Init /\\ [][Next]_x\nFair == Spec /\\ WF_x(Next)\n\
        Reach == <>(x = 3)\nOften == []<>(x = 0)\nStays == <>[](x = 3)";

    fn counter(x: i32) -> Vec<i32> {
        if x < 3 { vec![x + 1] } else { Vec::new() }
    }

    fn check(config: &str) -> crate::Outcome {
        let config = format!("{config}\nCHECK_DEADLOCK FALSE");
        run(SPEC, &config, System { init: vec![0], next: counter })
    }

    // The outcomes tla-ts gives, as TLC.
    #[test]
    fn finds_behaviors_that_violate_temporal_properties() {
        // Without fairness, the behavior may stop short of 3. The search finds it stuttering in
        // 2, which TLC prints with the stuttering step.
        let outcome = check("SPECIFICATION Spec\nPROPERTY Reach");
        assert_eq!((outcome.status, outcome.trace_length), (Status::LivenessViolation, Some(4)));
        // Weak fairness makes it count to 3, where it stays.
        assert_eq!(check("SPECIFICATION Fair\nPROPERTY Reach").status, Status::Success);
        assert_eq!(check("SPECIFICATION Fair\nPROPERTY Stays").status, Status::Success);
        let outcome = check("SPECIFICATION Fair\nPROPERTY Often");
        assert_eq!((outcome.status, outcome.trace_length), (Status::LivenessViolation, Some(5)));
        // The counts are those of the search.
        let outcome = check("SPECIFICATION Fair\nPROPERTY Reach Stays");
        assert_eq!((outcome.generated, outcome.distinct), (Some(4), Some(4)));
    }

    #[test]
    fn rejects_tautologies() {
        let body = format!("{SPEC}\nTaut == <>(x = 1) \\/ TRUE");
        let config = "SPECIFICATION Spec\nPROPERTY Taut\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!(outcome.status, Status::Error);
    }
}
