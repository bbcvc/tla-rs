//! Liveness checking, as TLC does it with `-lncheck final`: the temporal properties are
//! negated and conjoined with the fairness of the spec, the formula's tableau is paired with the
//! states the search finds into a behavior graph, and once the search is done, a strongly
//! connected component of the graph that satisfies a way of violating the properties gives a
//! counterexample. Ported from tla-ts `liveness.ts`, `tableau.ts`, and `liveness-checker.ts`.

pub mod live;
pub mod tableau;
pub mod template;
