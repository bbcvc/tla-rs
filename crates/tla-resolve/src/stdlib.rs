//! TLC's standard modules, bundled verbatim from `tlaplus/tlaplus` at commit `2ef2af8c` (MIT, see
//! `stdlib/LICENSE`). Most of their definitions are placeholders that TLC replaces with Java
//! implementations, and the evaluator replaces them the same way.

const MODULES: &[(&str, &str)] = &[
    ("Bags", include_str!("../stdlib/Bags.tla")),
    ("FiniteSets", include_str!("../stdlib/FiniteSets.tla")),
    ("Integers", include_str!("../stdlib/Integers.tla")),
    ("Json", include_str!("../stdlib/Json.tla")),
    ("Naturals", include_str!("../stdlib/Naturals.tla")),
    ("Randomization", include_str!("../stdlib/Randomization.tla")),
    ("RealTime", include_str!("../stdlib/RealTime.tla")),
    ("Reals", include_str!("../stdlib/Reals.tla")),
    ("Sequences", include_str!("../stdlib/Sequences.tla")),
    ("TLC", include_str!("../stdlib/TLC.tla")),
    ("TLCExt", include_str!("../stdlib/TLCExt.tla")),
    ("Toolbox", include_str!("../stdlib/Toolbox.tla")),
    ("_Possible", include_str!("../stdlib/_Possible.tla")),
];

pub(crate) fn standard_module(name: &str) -> Option<&'static str> {
    MODULES.iter().find(|(module, _)| *module == name).map(|(_, source)| *source)
}

#[cfg(test)]
mod tests {
    #[test]
    fn every_standard_module_parses() {
        for (name, source) in super::MODULES {
            let module =
                tla_parser::parse_module(source).unwrap_or_else(|error| panic!("{name}: {error}"));
            assert_eq!(module.name.symbol.as_str(), *name);
        }
    }
}
