//! How long the checker takes on each model against how long TLC took, on the models where
//! they agree. Both times are wall times of a whole run: TLC's include starting the JVM, and
//! ours starting a child process.

/// A model's times, in milliseconds.
pub struct Timing<'a> {
    pub id: &'a str,
    pub ours: u64,
    pub tlc: u64,
}

impl Timing<'_> {
    /// How many times as long as TLC the checker took.
    fn ratio(&self) -> f64 {
        self.ours.max(1) as f64 / self.tlc.max(1) as f64
    }
}

/// The median ratio, the share of models where the checker is faster, the totals, and the
/// `slowest` models by ratio.
pub fn summary(timings: &[Timing], slowest: usize) -> String {
    if timings.is_empty() {
        return "no matched models with TLC's time".into();
    }
    let mut ratios: Vec<f64> = timings.iter().map(Timing::ratio).collect();
    ratios.sort_by(f64::total_cmp);
    let middle = ratios.len() / 2;
    let median = match ratios.len() % 2 {
        0 => (ratios[middle - 1] + ratios[middle]) / 2.0,
        _ => ratios[middle],
    };
    let faster = timings.iter().filter(|timing| timing.ours < timing.tlc).count();
    let ours: u64 = timings.iter().map(|timing| timing.ours).sum();
    let tlc: u64 = timings.iter().map(|timing| timing.tlc).sum();
    let mut lines = vec![format!(
        "time against TLC on {} matched models: median ratio {median:.3}, faster on {faster}, \
         total {:.1} s against {:.1} s",
        timings.len(),
        ours as f64 / 1000.0,
        tlc as f64 / 1000.0,
    )];
    let mut by_ratio: Vec<&Timing> = timings.iter().collect();
    by_ratio.sort_by(|left, right| right.ratio().total_cmp(&left.ratio()));
    for timing in by_ratio.into_iter().take(slowest) {
        lines.push(format!(
            "  {:>8.3}x  {:>8} ms  TLC {:>8} ms  {}",
            timing.ratio(),
            timing.ours,
            timing.tlc,
            timing.id
        ));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn summarizes_ratios_to_tlc() {
        let timings = [
            Timing { id: "a", ours: 100, tlc: 400 },
            Timing { id: "b", ours: 900, tlc: 300 },
            Timing { id: "c", ours: 200, tlc: 400 },
        ];
        let summary = summary(&timings, 1);
        let lines: Vec<&str> = summary.lines().collect();
        assert!(lines[0].contains("3 matched models: median ratio 0.500, faster on 2"), "{summary}");
        assert!(lines[0].contains("total 1.2 s against 1.1 s"), "{summary}");
        assert_eq!(lines.len(), 2);
        assert!(lines[1].contains("3.000x") && lines[1].ends_with(" b"), "{summary}");
    }
}
