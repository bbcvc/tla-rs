//! What the model checker reports as it runs, for a front end that prints TLC's messages as TLC
//! prints them: when it computes the initial states, how far the search got, and when it starts
//! checking the temporal properties.

use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// TLC's counts of a search.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// The states generated, repeats and initial states included.
    pub generated: u64,
    pub distinct: u64,
    /// The states found that are still to be expanded.
    pub queue: u64,
    /// The length of the longest behavior found, one for the initial states.
    pub depth: u64,
}

/// Something the model checker did, in the order TLC reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    /// The liveness checker translated the temporal properties into this many solutions, which
    /// TLC calls branches.
    TemporalBranches(usize),
    /// The search starts computing the initial states.
    InitialStatesStarted,
    /// The search computed the initial states.
    InitialStatesComputed { generated: u64, distinct: u64 },
    /// How far the search got, which TLC reports every minute.
    Progress(Counts),
    /// The search is done and the liveness checker starts checking the temporal properties on
    /// the behavior graph of each branch, with this many states.
    LivenessStarted { counts: Counts, branches: usize, states: u64 },
}

type Reporter = dyn Fn(&Event) + Send + Sync;

/// Where the model checker reports [`Event`]s. The default reports none.
#[derive(Clone, Default)]
pub struct Progress(Option<Arc<Reporter>>);

impl Progress {
    pub fn new(report: impl Fn(&Event) + Send + Sync + 'static) -> Self {
        Self(Some(Arc::new(report)))
    }

    pub(crate) fn report(&self, event: Event) {
        if let Some(report) = &self.0 {
            report(&event);
        }
    }

    pub(crate) fn is_reported(&self) -> bool {
        self.0.is_some()
    }
}

impl fmt::Debug for Progress {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(if self.0.is_some() { "Progress(..)" } else { "Progress(None)" })
    }
}

/// How often TLC reports the progress of a search.
const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);

/// When the search last reported its progress.
pub(crate) struct Ticker {
    last: Instant,
}

impl Ticker {
    pub(crate) fn new() -> Self {
        Self { last: Instant::now() }
    }

    /// Whether a minute has passed since the last report, which starts the next one.
    pub(crate) fn is_due(&mut self) -> bool {
        let now = Instant::now();
        let is_due = now.duration_since(self.last) >= PROGRESS_INTERVAL;
        if is_due {
            self.last = now;
        }
        is_due
    }
}
