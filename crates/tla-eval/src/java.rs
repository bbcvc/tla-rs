//! The Java classes TLC loads beside a spec to override the operators of a module, ported from
//! tla-ts `java-overrides.ts`: TLC replaces each operator of the module the root module sees with
//! the public static method of the class named after the module that has the operator's name and
//! arity. This reads the class file and runs the bytecode of an override that returns a constant
//! value, such as `BoolValue.ValTrue`, `IntValue.gen(3)`, or `new StringValue("a")`.

use tla_resolve::{DefBody, DefId, ModuleId, Spec};
use tla_value::Value;

use crate::ConstBinding;

/// Why a class can't override a module's operators.
#[derive(Debug)]
pub enum JavaOverrideError {
    /// The file isn't a class file TLC could load.
    Invalid(String),
    /// An override computes its value, which needs a JVM to run.
    Unsupported(String),
}

/// The constant pool tags of the JVM specification, section 4.4.
mod tag {
    pub const UTF8: u8 = 1;
    pub const INTEGER: u8 = 3;
    pub const FLOAT: u8 = 4;
    pub const LONG: u8 = 5;
    pub const DOUBLE: u8 = 6;
    pub const CLASS: u8 = 7;
    pub const STRING: u8 = 8;
    pub const METHOD_HANDLE: u8 = 15;
    pub const METHOD_TYPE: u8 = 16;
    pub const MODULE: u8 = 19;
    pub const PACKAGE: u8 = 20;
}

/// The JVM opcodes an override returning a constant value uses.
mod opcode {
    pub const ICONST_M1: u8 = 0x02;
    pub const ICONST_0: u8 = 0x03;
    pub const ICONST_5: u8 = 0x08;
    pub const BIPUSH: u8 = 0x10;
    pub const SIPUSH: u8 = 0x11;
    pub const LDC: u8 = 0x12;
    pub const LDC_W: u8 = 0x13;
    pub const DUP: u8 = 0x59;
    pub const ARETURN: u8 = 0xb0;
    pub const GETSTATIC: u8 = 0xb2;
    pub const INVOKESPECIAL: u8 = 0xb7;
    pub const INVOKESTATIC: u8 = 0xb8;
    pub const NEW: u8 = 0xbb;
}

const CLASS_MAGIC: u32 = 0xcafe_babe;
const ACCESS_PUBLIC: u16 = 0x0001;
const ACCESS_STATIC: u16 = 0x0008;
const VALUE_PACKAGE: &str = "tlc2/value/impl/";

#[derive(Clone, Default)]
struct PoolEntry {
    tag: u8,
    text: String,
    value: i32,
    first: u16,
    second: u16,
}

struct Method {
    name: String,
    arity: usize,
    code: Option<Vec<u8>>,
}

struct ClassFile {
    pool: Vec<PoolEntry>,
    methods: Vec<Method>,
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn bytes(&mut self, length: usize) -> Result<&'a [u8], JavaOverrideError> {
        let end = self.offset.checked_add(length).filter(|&end| end <= self.bytes.len());
        let end = end.ok_or_else(|| invalid("A module override is a truncated class file"))?;
        let bytes = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(bytes)
    }

    fn u8(&mut self) -> Result<u8, JavaOverrideError> {
        Ok(self.bytes(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, JavaOverrideError> {
        Ok(u16::from_be_bytes(self.bytes(2)?.try_into().expect("two bytes")))
    }

    fn u32(&mut self) -> Result<u32, JavaOverrideError> {
        Ok(u32::from_be_bytes(self.bytes(4)?.try_into().expect("four bytes")))
    }
}

fn invalid(message: &str) -> JavaOverrideError {
    JavaOverrideError::Invalid(message.to_owned())
}

/// The number of parameters a method descriptor such as `(Ltlc2/value/impl/Value;I)V` gives.
fn parameter_count(descriptor: &str) -> usize {
    let parameters = descriptor.split(')').next().unwrap_or_default().trim_start_matches('(');
    let mut chars = parameters.chars();
    let mut count = 0;
    while let Some(char) = chars.next() {
        match char {
            '[' => continue,
            'L' => {
                chars.by_ref().find(|&char| char == ';');
                count += 1;
            }
            _ => count += 1,
        }
    }
    count
}

impl ClassFile {
    /// The public static methods of a class file and their bytecode, in the order of the file.
    fn read(bytes: &[u8]) -> Result<Self, JavaOverrideError> {
        let mut reader = Reader { bytes, offset: 0 };
        if reader.u32()? != CLASS_MAGIC {
            return Err(invalid("A module override is not a class file"));
        }
        reader.bytes(4)?;
        let pool_size = usize::from(reader.u16()?);
        let mut pool = vec![PoolEntry::default(); pool_size.max(1)];
        let mut index = 1;
        while index < pool_size {
            let tag = reader.u8()?;
            let entry = &mut pool[index];
            entry.tag = tag;
            match tag {
                tag::UTF8 => {
                    let length = usize::from(reader.u16()?);
                    entry.text = String::from_utf8_lossy(reader.bytes(length)?).into_owned();
                }
                tag::INTEGER => entry.value = reader.u32()? as i32,
                tag::FLOAT => {
                    reader.u32()?;
                }
                tag::LONG | tag::DOUBLE => {
                    reader.bytes(8)?;
                    index += 1;
                }
                tag::CLASS | tag::STRING | tag::METHOD_TYPE | tag::MODULE | tag::PACKAGE => {
                    entry.first = reader.u16()?;
                }
                tag::METHOD_HANDLE => {
                    reader.u8()?;
                    entry.first = reader.u16()?;
                }
                _ => {
                    entry.first = reader.u16()?;
                    entry.second = reader.u16()?;
                }
            }
            index += 1;
        }
        // The access flags, this class, the superclass, and the interfaces.
        reader.bytes(6)?;
        let interfaces = usize::from(reader.u16()?);
        reader.bytes(interfaces * 2)?;
        for _ in 0..reader.u16()? {
            reader.bytes(6)?;
            for _ in 0..reader.u16()? {
                reader.u16()?;
                let length = reader.u32()? as usize;
                reader.bytes(length)?;
            }
        }
        let text = |pool: &[PoolEntry], index: u16| {
            pool.get(usize::from(index)).map(|entry| entry.text.clone()).unwrap_or_default()
        };
        let mut methods = Vec::new();
        for _ in 0..reader.u16()? {
            let access = reader.u16()?;
            let name = text(&pool, reader.u16()?);
            let descriptor = text(&pool, reader.u16()?);
            let mut code = None;
            for _ in 0..reader.u16()? {
                let attribute = text(&pool, reader.u16()?);
                let length = reader.u32()? as usize;
                let mut body = Reader { bytes: reader.bytes(length)?, offset: 0 };
                if attribute == "Code" {
                    // max_stack and max_locals come before the length of the bytecode.
                    body.bytes(4)?;
                    let length = body.u32()? as usize;
                    code = Some(body.bytes(length)?.to_vec());
                }
            }
            if access & ACCESS_PUBLIC != 0 && access & ACCESS_STATIC != 0 {
                methods.push(Method { name, arity: parameter_count(&descriptor), code });
            }
        }
        Ok(Self { pool, methods })
    }

    fn entry(&self, index: u16) -> &PoolEntry {
        static EMPTY: PoolEntry =
            PoolEntry { tag: 0, text: String::new(), value: 0, first: 0, second: 0 };
        self.pool.get(usize::from(index)).unwrap_or(&EMPTY)
    }

    fn class_name(&self, index: u16) -> &str {
        &self.entry(self.entry(index).first).text
    }

    /// The class and the name of the field or method at `index`.
    fn member(&self, index: u16) -> (&str, &str) {
        let reference = self.entry(index);
        let name_and_type = self.entry(reference.second);
        (self.class_name(reference.first), &self.entry(name_and_type.first).text)
    }
}

/// What the bytecode of an override pushes on its stack.
enum Item {
    Int(i32),
    Text(String),
    Value(Value),
    /// An object `new` made, with the value its constructor gave it.
    Object(Option<Value>),
}

/// Runs the bytecode of an override that returns a constant TLC value, and returns that value.
fn returned_value(
    class: &ClassFile,
    method: &Method,
    module: &str,
) -> Result<Value, JavaOverrideError> {
    let unsupported = || {
        JavaOverrideError::Unsupported(format!(
            "The Java override {module}.{} computes its value, which tla-rs cannot run",
            method.name
        ))
    };
    let code = method.code.as_deref().ok_or_else(unsupported)?;
    let mut stack: Vec<Item> = Vec::new();
    let constant = |index: u16| {
        let entry = class.entry(index);
        match entry.tag {
            tag::INTEGER => Ok(Item::Int(entry.value)),
            tag::STRING => Ok(Item::Text(class.entry(entry.first).text.clone())),
            _ => Err(unsupported()),
        }
    };
    let mut offset = 0;
    while let Some(&op) = code.get(offset) {
        let byte = |at: usize| code.get(offset + at).copied().ok_or_else(unsupported);
        let index = || Ok::<u16, JavaOverrideError>(u16::from_be_bytes([byte(1)?, byte(2)?]));
        match op {
            opcode::ICONST_M1..=opcode::ICONST_5 => {
                stack.push(Item::Int(i32::from(op) - i32::from(opcode::ICONST_0)));
                offset += 1;
            }
            opcode::BIPUSH => {
                stack.push(Item::Int(i32::from(byte(1)? as i8)));
                offset += 2;
            }
            opcode::SIPUSH => {
                stack.push(Item::Int(i32::from(index()? as i16)));
                offset += 3;
            }
            opcode::LDC => {
                stack.push(constant(u16::from(byte(1)?))?);
                offset += 2;
            }
            opcode::LDC_W => {
                stack.push(constant(index()?)?);
                offset += 3;
            }
            opcode::DUP => {
                let top = match stack.last().ok_or_else(unsupported)? {
                    Item::Int(value) => Item::Int(*value),
                    Item::Text(text) => Item::Text(text.clone()),
                    Item::Value(value) => Item::Value(value.clone()),
                    // Both copies are the one object, which the constructor fills in.
                    Item::Object(_) => Item::Int(0),
                };
                stack.push(top);
                offset += 1;
            }
            opcode::GETSTATIC => {
                let (field_class, field) = class.member(index()?);
                let value = match (field_class.strip_prefix(VALUE_PACKAGE), field) {
                    (Some("BoolValue"), "ValTrue") => Value::TRUE,
                    (Some("BoolValue"), "ValFalse") => Value::FALSE,
                    _ => return Err(unsupported()),
                };
                stack.push(Item::Value(value));
                offset += 3;
            }
            opcode::INVOKESTATIC => {
                let (callee_class, callee) = class.member(index()?);
                let (Some("IntValue"), "gen", Some(Item::Int(value))) =
                    (callee_class.strip_prefix(VALUE_PACKAGE), callee, stack.pop())
                else {
                    return Err(unsupported());
                };
                stack.push(Item::Value(Value::Int(value)));
                offset += 3;
            }
            opcode::NEW => {
                index()?;
                stack.push(Item::Object(None));
                offset += 3;
            }
            opcode::INVOKESPECIAL => {
                let (constructor_class, constructor) = class.member(index()?);
                let is_string_value = constructor_class.strip_prefix(VALUE_PACKAGE)
                    == Some("StringValue")
                    && constructor == "<init>";
                // The text, then the copy `dup` made of the object, under the object itself.
                let (Some(Item::Text(text)), Some(_)) = (stack.pop(), stack.pop()) else {
                    return Err(unsupported());
                };
                match stack.last_mut() {
                    Some(Item::Object(value)) if is_string_value => {
                        *value = Some(Value::str(&text));
                    }
                    _ => return Err(unsupported()),
                }
                offset += 3;
            }
            opcode::ARETURN => {
                return match stack.pop() {
                    Some(Item::Value(value) | Item::Object(Some(value))) => Ok(value),
                    _ => Err(unsupported()),
                };
            }
            _ => return Err(unsupported()),
        }
    }
    Err(unsupported())
}

/// The overrides of the operators of `module` that the class file `class` gives, as TLC loads
/// the class named after the module.
pub fn java_overrides(
    spec: &Spec,
    module: ModuleId,
    class: &[u8],
) -> Result<Vec<(DefId, ConstBinding)>, JavaOverrideError> {
    let class_file = ClassFile::read(class)?;
    let module_name = spec.modules[module.index()].name.as_str();
    let mut overrides = Vec::new();
    for (index, def) in spec.defs.iter().enumerate() {
        if def.module != module || def.depth > 0 || !matches!(def.body, DefBody::Expr(_)) {
            continue;
        }
        let matched = class_file
            .methods
            .iter()
            .find(|method| method.name == def.name.as_str() && method.arity == def.params.len());
        if let Some(method) = matched {
            let value = returned_value(&class_file, method, module_name)?;
            overrides.push((DefId(index as u32), ConstBinding::Value(value)));
        }
    }
    Ok(overrides)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A class file with a constant pool built as entries are asked for, and public static
    /// methods with the given bytecode.
    #[derive(Default)]
    struct Builder {
        pool: Vec<Vec<u8>>,
        methods: Vec<(u16, u16, u16, Vec<u8>)>,
    }

    impl Builder {
        fn entry(&mut self, bytes: Vec<u8>) -> u16 {
            if let Some(index) = self.pool.iter().position(|entry| *entry == bytes) {
                return index as u16 + 1;
            }
            self.pool.push(bytes);
            self.pool.len() as u16
        }

        fn utf8(&mut self, text: &str) -> u16 {
            let mut bytes = vec![tag::UTF8];
            bytes.extend((text.len() as u16).to_be_bytes());
            bytes.extend(text.as_bytes());
            self.entry(bytes)
        }

        fn indexed(&mut self, tag: u8, indexes: &[u16]) -> u16 {
            let mut bytes = vec![tag];
            indexes.iter().for_each(|index| bytes.extend(index.to_be_bytes()));
            self.entry(bytes)
        }

        fn class(&mut self, name: &str) -> u16 {
            let name = self.utf8(name);
            self.indexed(tag::CLASS, &[name])
        }

        /// A field (tag 9) or method (tag 10) reference.
        fn member(&mut self, tag: u8, class: &str, name: &str, descriptor: &str) -> u16 {
            let class = self.class(class);
            let (name, descriptor) = (self.utf8(name), self.utf8(descriptor));
            let name_and_type = self.indexed(12, &[name, descriptor]);
            self.indexed(tag, &[class, name_and_type])
        }

        fn method(&mut self, name: &str, descriptor: &str, code: Vec<u8>) {
            let (name, descriptor, code_name) =
                (self.utf8(name), self.utf8(descriptor), self.utf8("Code"));
            self.methods.push((name, descriptor, code_name, code));
        }

        fn build(mut self) -> Vec<u8> {
            let (this, object) = (self.class("M"), self.class("java/lang/Object"));
            let mut bytes = CLASS_MAGIC.to_be_bytes().to_vec();
            bytes.extend([0, 0, 0, 52]);
            bytes.extend((self.pool.len() as u16 + 1).to_be_bytes());
            self.pool.iter().for_each(|entry| bytes.extend(entry));
            bytes.extend([0, 0x21]);
            bytes.extend(this.to_be_bytes());
            bytes.extend(object.to_be_bytes());
            bytes.extend([0, 0, 0, 0]);
            bytes.extend((self.methods.len() as u16).to_be_bytes());
            for (name, descriptor, code_name, code) in &self.methods {
                bytes.extend((ACCESS_PUBLIC | ACCESS_STATIC).to_be_bytes());
                bytes.extend(name.to_be_bytes());
                bytes.extend(descriptor.to_be_bytes());
                bytes.extend([0, 1]);
                bytes.extend(code_name.to_be_bytes());
                bytes.extend((code.len() as u32 + 12).to_be_bytes());
                bytes.extend([0, 2, 0, 1]);
                bytes.extend((code.len() as u32).to_be_bytes());
                bytes.extend(code);
                bytes.extend([0, 0, 0, 0]);
            }
            bytes.extend([0, 0]);
            bytes
        }
    }

    fn spec(body: &str) -> Spec {
        let source = format!("---- MODULE M ----\n{body}\n====\n");
        tla_resolve::resolve(&source, &mut |_: &str| None).unwrap()
    }

    fn overridden(spec: &Spec, class: &[u8]) -> Result<Vec<(String, String)>, JavaOverrideError> {
        let overrides = java_overrides(spec, ModuleId(0), class)?;
        Ok(overrides
            .into_iter()
            .map(|(def, binding)| match binding {
                ConstBinding::Value(value) => {
                    (spec.def(def).name.as_str().to_owned(), value.to_string())
                }
                _ => unreachable!("an override is a value"),
            })
            .collect())
    }

    const VALUE: &str = "()Ltlc2/value/impl/Value;";

    #[test]
    fn overrides_operators_with_the_constants_their_methods_return() {
        let mut class = Builder::default();
        let truth =
            class.member(9, "tlc2/value/impl/BoolValue", "ValTrue", "Ltlc2/value/impl/BoolValue;");
        class.method("Get", VALUE, vec![opcode::GETSTATIC, 0, truth as u8, opcode::ARETURN]);
        let generate =
            class.member(10, "tlc2/value/impl/IntValue", "gen", "(I)Ltlc2/value/impl/IntValue;");
        let code =
            vec![opcode::BIPUSH, 0xf9, opcode::INVOKESTATIC, 0, generate as u8, opcode::ARETURN];
        class.method("Seven", "(Ltlc2/value/impl/Value;)Ltlc2/value/impl/Value;", code);
        let string_class = class.class("tlc2/value/impl/StringValue");
        let text = class.utf8("a");
        let string = class.indexed(tag::STRING, &[text]);
        let init =
            class.member(10, "tlc2/value/impl/StringValue", "<init>", "(Ljava/lang/String;)V");
        let code = vec![
            opcode::NEW,
            0,
            string_class as u8,
            opcode::DUP,
            opcode::LDC,
            string as u8,
            opcode::INVOKESPECIAL,
            0,
            init as u8,
            opcode::ARETURN,
        ];
        class.method("Text", VALUE, code);
        class.method("Unused", VALUE, vec![opcode::ICONST_0, opcode::ARETURN]);
        let spec = spec("Get == FALSE\nSeven(x) == 7\nText == \"b\"\nUnused(x) == 1\nOther == 2");
        assert_eq!(
            overridden(&spec, &class.build()).unwrap(),
            [
                ("Get".into(), "TRUE".into()),
                ("Seven".into(), "-7".into()),
                ("Text".into(), "\"a\"".into())
            ]
        );
    }

    #[test]
    fn refuses_an_override_that_computes_its_value() {
        let mut class = Builder::default();
        class.method("Get", VALUE, vec![opcode::ICONST_0, opcode::ARETURN]);
        let error = overridden(&spec("Get == 1"), &class.build()).unwrap_err();
        assert!(
            matches!(error, JavaOverrideError::Unsupported(message) if message.contains("M.Get"))
        );
        assert!(matches!(
            overridden(&spec("Get == 1"), b"not a class"),
            Err(JavaOverrideError::Invalid(_))
        ));
    }
}
