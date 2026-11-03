//! A function applied in action position, as `Actions[p]`: TLC walks the body of a function it
//! keeps lazy at the arguments, and evaluates the application of any other function.

use std::sync::Arc;

use tla_resolve::{Expr, Pattern};
use tla_value::{LazySet, Value};

use super::run::{Computation, Run, env};
use super::{Action, Rest, Site};
use crate::eval::At;
use crate::eval::bound::tuple_items;
use crate::eval::describe;
use crate::eval::function::{Lambda, bind_argument};
use crate::{EvalError, Evaluator, Result};

impl Evaluator {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn act_application(
        &self,
        func: &Expr,
        args: &[Expr],
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        let function = {
            let mut env = env(site, run);
            // TLC keeps the function lazy to walk its body, except as it computes the initial
            // states, which it evaluates eagerly.
            env.keep_lazy = run.computation != Computation::Init;
            self.eval(func, &mut env)?
        };
        if let Value::LazyFunc(lazy) = &function
            && let Some(lambda) =
                lazy.source.clone().and_then(|source| source.downcast::<Lambda>().ok())
            && Arc::ptr_eq(lambda.body.spec(), &self.spec)
        {
            let argument = {
                let mut env = env(site, run);
                match args {
                    [arg] => self.eval(arg, &mut env)?,
                    _ => Value::tuple(
                        args.iter().map(|arg| self.eval(arg, &mut env)).collect::<Result<_>>()?,
                    ),
                }
            };
            self.check_argument(&lambda, &lazy.domain, &function, &argument, func, site, run)?;
            let mut frame = lambda.captured.frame.clone();
            bind_argument(lambda.bounds.get(), &argument, &mut frame).at(
                self,
                &env(site, run),
                expr,
            )?;
            let callee = Site { frame, ..Site::of(&lambda.captured) };
            return self.act(lambda.body.get(), &callee, run, action, rest);
        }
        let mut env = env(site, run);
        let range = self.range(&env, expr);
        if !function.is_function() {
            let message = format!(
                "In computing {}, a non-function ({}) was applied as a function.\n{range}",
                run.computation.name(),
                describe(&function)
            );
            return Err(self.error(&env, expr, message));
        }
        match self.eval(expr, &mut env)? {
            Value::Bool(true) => {
                drop(env);
                self.resume(run, action, rest)
            }
            Value::Bool(false) => Ok(()),
            _ => {
                let message = format!(
                    "In computing {}, TLC expected a boolean expression,\nbut didn't find one.\n{range}",
                    run.computation.name()
                );
                Err(self.error(&env, expr, message))
            }
        }
    }

    /// Fails as TLC's `Tool.getFcnContext` does on an argument outside the domain of the function
    /// whose body the walk enters.
    #[allow(clippy::too_many_arguments)]
    fn check_argument(
        &self,
        lambda: &Lambda,
        domain: &Value,
        function: &Value,
        argument: &Value,
        func: &Expr,
        site: &Site,
        run: &Run<'_>,
    ) -> Result<()> {
        let env = env(site, run);
        let fail = |ordinal: &str, element: &Value, problem: &str| -> EvalError {
            let message = format!(
                "In applying the function\n{function},\nthe {ordinal} is:\n{element}{problem}.\n{}",
                self.range(&env, func)
            );
            self.error(&env, func, message)
        };
        let patterns: Vec<&Pattern> = lambda
            .bounds
            .get()
            .iter()
            .flat_map(|bound| {
                let count = match &bound.pattern {
                    Pattern::Names(slots) => slots.len(),
                    Pattern::Tuple(_) => 1,
                };
                std::iter::repeat_n(&bound.pattern, count)
            })
            .collect();
        if patterns.len() == 1 {
            if !domain.contains(argument).at(self, &env, func)? {
                return Err(fail("first argument", argument, "which is not in its domain"));
            }
            return Ok(());
        }
        let factors = match domain {
            Value::Lazy(set) => match &**set {
                LazySet::Product(factors) => factors.to_vec(),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let Some(items) = tuple_items(argument).filter(|items| items.len() >= patterns.len())
        else {
            let message = format!(
                "Attempted to apply a function to an argument not in its domain.\n{}",
                self.range(&env, func)
            );
            return Err(self.error(&env, func, message));
        };
        for (index, pattern) in patterns.iter().enumerate() {
            let (item, ordinal) = (&items[index], format!("argument number {}", index + 1));
            let is_member = match factors.get(index) {
                Some(factor) => factor.contains(item).at(self, &env, func)?,
                None => false,
            };
            if !is_member {
                let separator = if matches!(pattern, Pattern::Names(_)) { "" } else { "\n" };
                let problem = format!("{separator}which is not in its domain");
                return Err(fail(&ordinal, item, &problem));
            }
            if let Pattern::Tuple(slots) = pattern
                && tuple_items(item).is_none_or(|parts| parts.len() != slots.len())
            {
                return Err(fail(&ordinal, item, "which does not match its formal parameter"));
            }
        }
        Ok(())
    }
}
