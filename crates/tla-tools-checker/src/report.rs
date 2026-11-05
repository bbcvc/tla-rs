//! What TLC prints about the end of a check, beyond its verdict: the behavior that leads to a
//! violation, step by step with the action of each step, and the counts of the search.

use tla_tools_eval::Value;

use crate::progress::Counts;

/// One state of a behavior, with the action that leads to it.
#[derive(Clone, Debug)]
pub struct Step {
    /// Where TLC says the action that leads to the state is, as in
    /// `Next line 4, col 7 to line 4, col 12 of module M`, or `None` for an initial state.
    pub action: Option<String>,
    /// The variables and their values, in TLC's order of the variables.
    pub variables: Vec<(String, Value)>,
}

/// The behavior that leads to a violation.
#[derive(Clone, Debug, Default)]
pub struct Trace {
    pub steps: Vec<Step>,
    /// For a behavior that violates a liveness property, the index of the step the last one
    /// loops back to. The behavior stutters when it is the last step.
    pub loop_start: Option<usize>,
    /// The action of the step from the last state back to the one at `loop_start`.
    pub loop_action: Option<String>,
}

/// An assumption that doesn't hold.
#[derive(Clone, Debug)]
pub struct Assumption {
    /// Where its expression is, as TLC names an assumption.
    pub location: String,
    /// Why it failed to evaluate, when it isn't simply false.
    pub error: Option<String>,
}

/// What a front end prints about a check, as TLC does.
#[derive(Clone, Debug, Default)]
pub struct Report {
    /// The behavior that leads to the violation, or to the state an error happened on.
    pub trace: Option<Trace>,
    /// The counts of the search as it ended, which TLC prints after the verdict.
    pub counts: Option<Counts>,
    /// How many expanded states had each number of new successors, the last bucket counting 31
    /// and up, for TLC's summary of the outdegree of a complete search.
    pub out_degrees: Option<Vec<u64>>,
    /// The violated assumption.
    pub assumption: Option<Assumption>,
    /// The names of the temporal properties a liveness counterexample violates.
    pub temporal_properties: Vec<String>,
}

/// TLC's buckets of the outdegree.
pub(crate) const OUT_DEGREE_BUCKETS: usize = 32;
