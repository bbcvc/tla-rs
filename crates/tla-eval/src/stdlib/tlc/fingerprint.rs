//! TLC's 64-bit fingerprints of values, ported from tla-ts `tlc/fingerprint.ts`: FP64 with TLC's
//! first irreducible polynomial, which `-fp 0` selects. TLC reseeds its random choices with the
//! fingerprint of each state it expands, and `TLCExt!TLCFP` returns part of one.
//!
//! TLC extends a fingerprint by a model value's token number, its rank in TLC's intern order,
//! which this crate's interner doesn't expose. A model value counts as token 0 here.

use tla_value::{Result, Value};

/// FP64.Polys[0].
const IRREDUCIBLE_POLYNOMIAL: u64 = 0x9114_98ae_0e66_bad6;

/// What extending a fingerprint by each byte XORs into it.
const BYTE_MOD_TABLE: [u64; 256] = byte_mod_table();

const fn byte_mod_table() -> [u64; 256] {
    let mut powers = [0u64; 72];
    let mut power = 1u64 << 63;
    let mut index = 0;
    while index < 72 {
        powers[index] = power;
        power = (power >> 1) ^ if power & 1 == 0 { 0 } else { IRREDUCIBLE_POLYNOMIAL };
        index += 1;
    }
    let mut table = [0u64; 256];
    let mut byte = 0;
    while byte < 256 {
        let mut entry = 0;
        let mut bit = 0;
        while bit < 8 {
            if (byte >> bit) & 1 == 1 {
                entry ^= powers[71 - bit];
            }
            bit += 1;
        }
        table[byte] = entry;
        byte += 1;
    }
    table
}

// The tag each of TLC's value classes extends a fingerprint by.
const BOOL_VALUE: u8 = 0;
const INT_VALUE: u8 = 1;
const STRING_VALUE: u8 = 3;
const SET_ENUM_VALUE: u8 = 5;
const FCN_RCD_VALUE: u8 = 9;
const MODEL_VALUE: u8 = 21;

struct Fingerprint(u64);

impl Fingerprint {
    fn byte(&mut self, byte: u8) {
        self.0 = (self.0 >> 8) ^ BYTE_MOD_TABLE[usize::from(byte ^ self.0 as u8)];
    }

    fn int(&mut self, value: i32) {
        for byte in value.to_le_bytes() {
            self.byte(byte);
        }
    }

    /// Value#fingerPrint of the value's TLC class.
    fn value(&mut self, value: &Value) -> Result<()> {
        match value {
            Value::Bool(value) => {
                self.byte(BOOL_VALUE);
                self.byte(if *value { b't' } else { b'f' });
            }
            Value::Int(value) => {
                self.byte(INT_VALUE);
                self.int(*value);
            }
            Value::Str(text) => {
                let units: Vec<u16> = text.as_str().encode_utf16().collect();
                self.byte(STRING_VALUE);
                self.int(units.len() as i32);
                for unit in units {
                    self.byte(unit as u8);
                }
            }
            Value::Model(_) => {
                self.byte(MODEL_VALUE);
                self.int(0);
            }
            Value::Tuple(items) => {
                self.byte(FCN_RCD_VALUE);
                self.int(items.len() as i32);
                for (index, item) in items.iter().enumerate() {
                    self.value(&Value::Int(index as i32 + 1))?;
                    self.value(item)?;
                }
            }
            Value::Func(func) => {
                self.byte(FCN_RCD_VALUE);
                self.int(func.keys.len() as i32);
                for (key, value) in func.keys.iter().zip(func.values.iter()) {
                    self.value(key)?;
                    self.value(value)?;
                }
            }
            Value::LazyFunc(_) => self.value(&value.materialize()?)?,
            _ => {
                let elements = value.elements()?;
                self.byte(SET_ENUM_VALUE);
                self.int(elements.len() as i32);
                for element in elements.iter() {
                    self.value(element)?;
                }
            }
        }
        Ok(())
    }
}

/// TLCStateMut#fingerPrint of `values`, in order.
pub(crate) fn tlc_fingerprint(values: &[Value]) -> Result<u64> {
    let mut fingerprint = Fingerprint(IRREDUCIBLE_POLYNOMIAL);
    for value in values {
        fingerprint.value(value)?;
    }
    Ok(fingerprint.0)
}

#[cfg(test)]
mod tests {
    use tla_value::{Symbol, Value};

    use super::tlc_fingerprint;
    use crate::stdlib::testing::{ints, string, tuple};

    #[test]
    fn matches_tla_ts() {
        // The values tla-ts's getTlcFingerprint gives.
        let record = Value::record(vec![(Symbol::intern("a"), Value::Int(1))]);
        let cases = [
            (vec![], 0x9114_98ae_0e66_bad6),
            (vec![Value::Int(0)], 0xd0ba_3e88_0dcd_d983),
            (vec![Value::Int(-7), Value::TRUE], 0xcb9b_9edd_15ee_15b6),
            (vec![string("abc")], 0x7212_9dcd_5334_cbd6),
            (vec![tuple(&[1, 2]), ints(&[3, 4])], 0x23d8_1127_bac9_0319),
            (vec![record], 0x43d4_7117_2a35_59df),
            (vec![Value::FALSE, string("\u{e9}\u{4e2d}")], 0xf58c_d606_e527_1b83),
        ];
        for (values, expected) in cases {
            assert_eq!(tlc_fingerprint(&values).unwrap(), expected, "{values:?}");
        }
    }
}
