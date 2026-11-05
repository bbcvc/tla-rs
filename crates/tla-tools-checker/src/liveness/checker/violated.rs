//! Which properties a counterexample violates, as TLC names them in its report: those whose
//! negation holds of the lasso, tla-ts `evaluateOnLasso`.

use tla_tools_eval::State;

use super::{Cache, Checker, Live, eval};

impl Checker<'_> {
    /// The names of the properties the behavior `path`, which loops back to the state at
    /// `cycle_start` after its last state, violates.
    pub fn violated_properties(&self, path: &[State], cycle_start: usize) -> Vec<String> {
        let mut names: Vec<String> = Vec::new();
        if cycle_start >= path.len() {
            return names;
        }
        for (name, negation) in &self.negations {
            let lasso = Lasso { checker: self, path, cycle_start };
            if lasso.holds(negation, 0).unwrap_or(false) && !names.contains(name) {
                names.push(name.clone());
            }
        }
        names
    }
}

struct Lasso<'c, 'e> {
    checker: &'c Checker<'e>,
    path: &'c [State],
    cycle_start: usize,
}

impl Lasso<'_, '_> {
    fn next(&self, position: usize) -> usize {
        if position + 1 < self.path.len() { position + 1 } else { self.cycle_start }
    }

    /// The positions from `position` on, which on a lasso are those of the cycle too.
    fn future(&self, position: usize) -> std::ops::Range<usize> {
        position.min(self.cycle_start)..self.path.len()
    }

    fn holds(&self, live: &Live, position: usize) -> Result<bool, String> {
        Ok(match live {
            Live::Not(body) => !self.holds(body, position)?,
            Live::And(operands) => {
                for operand in operands.iter() {
                    if !self.holds(operand, position)? {
                        return Ok(false);
                    }
                }
                true
            }
            Live::Or(operands) => {
                for operand in operands.iter() {
                    if self.holds(operand, position)? {
                        return Ok(true);
                    }
                }
                false
            }
            Live::Next(body) => self.holds(body, self.next(position))?,
            Live::Always(body) => {
                for index in self.future(position) {
                    if !self.holds(body, index)? {
                        return Ok(false);
                    }
                }
                true
            }
            Live::Eventually(body) => {
                for index in self.future(position) {
                    if self.holds(body, index)? {
                        return Ok(true);
                    }
                }
                false
            }
            Live::Bool(_) | Live::Atom(_) => {
                let (checker, mut cache) = (self.checker, Cache::default());
                let (state, next) = (&self.path[position], &self.path[self.next(position)]);
                eval(checker.evaluator, &checker.exprs, &mut cache, live, state, Some(next))?
            }
        })
    }
}
