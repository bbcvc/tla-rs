//! What TLC's operators with effects use: printed output and `TLCGet`/`TLCSet` registers.

use std::sync::Mutex;

use tla_value::Value;

#[derive(Default)]
pub struct Runtime {
    /// Lines printed by `Print` and `PrintT`, in order.
    pub output: Mutex<Vec<String>>,
    /// The registers of `TLCSet(i, v)` and `TLCGet(i)`.
    pub registers: Mutex<Vec<Value>>,
}

impl Runtime {
    pub fn print(&self, line: String) {
        self.output.lock().unwrap().push(line);
    }
}
