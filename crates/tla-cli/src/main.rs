//! `tla-rs`: checks a TLA+ spec with its model configuration as `java tlc2.TLC` does, printing
//! TLC's messages and exiting with TLC's exit status.

mod args;
mod exit;
mod printer;
mod result;
mod run;

use std::io::Write;

use args::Args;

/// The stack of the thread that checks the spec, which evaluates deeply nested expressions.
const STACK_SIZE: usize = 1 << 30;

fn main() {
    let args = match Args::parse_tlc(std::env::args()) {
        Ok(args) => args,
        Err(error) => {
            let code = match error.use_stderr() {
                true => exit::USAGE_ERROR,
                false => exit::SUCCESS,
            };
            let _ = error.print();
            std::process::exit(code);
        }
    };
    let checked = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || run::run(&args))
        .expect("the checking thread starts")
        .join();
    let code = checked.unwrap_or_else(|panic| {
        let message = panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|text| text.to_string()))
            .unwrap_or_default();
        println!("Error: tla-rs failed unexpectedly: {message}");
        exit::ERROR
    });
    let _ = std::io::stdout().flush();
    std::process::exit(code);
}
