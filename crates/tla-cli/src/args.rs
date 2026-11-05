//! TLC's command line: `tla-rs Spec.tla [-config Spec.cfg] [-workers N] ...`, with TLC's
//! single-dash options.

use std::path::PathBuf;

use clap::Parser;

/// Checks a TLA+ spec as TLC does: `java tlc2.TLC Spec.tla`.
#[derive(Debug, Parser)]
#[command(name = "tla-rs", version)]
pub struct Args {
    /// The spec: `Spec.tla`, `Spec`, or its configuration `Spec.cfg`.
    pub spec: PathBuf,
    /// The model configuration. Defaults to the spec's with `.cfg` for `.tla`.
    #[arg(long, value_name = "FILE")]
    pub config: Option<PathBuf>,
    /// The number of workers, or `auto` for one per core. tla-rs checks with one for now.
    #[arg(long, value_name = "COUNT", default_value = "1")]
    pub workers: Workers,
    /// Don't check for deadlock.
    #[arg(long)]
    pub deadlock: bool,
    /// The seed of TLC's random choices.
    #[arg(long, default_value_t = 0, allow_negative_numbers = true)]
    pub seed: i64,
    /// TLC's index of the fingerprint polynomial. tla-rs fingerprints as TLC does with 0.
    #[arg(long, value_name = "NUM")]
    pub fp: Option<i64>,
    /// Don't print warnings.
    #[arg(long)]
    pub nowarning: bool,
    /// When to check the temporal properties. tla-rs checks them once the search is done, as
    /// TLC does with `final`.
    #[arg(long, value_name = "final|default|seqfinal|off")]
    pub lncheck: Option<String>,
    /// The directory of TLC's states (ignored: tla-rs keeps them in memory).
    #[arg(long, value_name = "DIR")]
    pub metadir: Option<PathBuf>,
    /// Don't generate the trace exploration spec (tla-rs generates none).
    #[arg(long = "noGenerateSpecTE")]
    pub no_generate_spec_te: bool,
    /// A directory of modules the spec uses, as TLC's `-DTLA-Library`. May be repeated.
    #[arg(long, value_name = "DIR")]
    pub library: Vec<PathBuf>,
}

/// How many workers `-workers` asks for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Workers {
    Count(usize),
    Auto,
}

impl std::str::FromStr for Workers {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, String> {
        match text {
            "auto" => Ok(Workers::Auto),
            _ => match text.parse::<usize>() {
                Ok(count) if count > 0 => Ok(Workers::Count(count)),
                _ => Err(format!("expected a positive number of workers or auto, not {text}")),
            },
        }
    }
}

/// The options that take TLC's single dash.
const LONG_OPTIONS: &[&str] = &[
    "config",
    "workers",
    "deadlock",
    "seed",
    "fp",
    "nowarning",
    "lncheck",
    "metadir",
    "noGenerateSpecTE",
    "library",
    "help",
    "version",
];

const LIBRARY_PROPERTY: &str = "-DTLA-Library=";

/// The arguments with TLC's `-option` spelled `--option`, and Java's `-DTLA-Library=a:b` as
/// `--library` options.
pub fn normalize(args: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut normalized = Vec::new();
    for arg in args {
        if let Some(directories) = arg.strip_prefix(LIBRARY_PROPERTY) {
            for directory in std::env::split_paths(directories) {
                normalized.push("--library".into());
                normalized.push(directory.to_string_lossy().into_owned());
            }
            continue;
        }
        let name = arg.strip_prefix('-').filter(|rest| !rest.starts_with('-'));
        let name = name.map(|rest| rest.split_once('=').map_or(rest, |(name, _)| name));
        match name {
            Some(name) if LONG_OPTIONS.contains(&name) => normalized.push(format!("-{arg}")),
            _ => normalized.push(arg),
        }
    }
    normalized
}

impl Args {
    /// The arguments of the process, with TLC's spelling.
    pub fn parse_tlc(args: impl IntoIterator<Item = String>) -> Result<Self, clap::Error> {
        Args::try_parse_from(normalize(args))
    }

    /// The spec's `.tla` file: `Spec` and `Spec.cfg` name `Spec.tla`.
    pub fn spec_path(&self) -> PathBuf {
        match self.spec.extension().and_then(|extension| extension.to_str()) {
            Some("tla") => self.spec.clone(),
            Some("cfg") => self.spec.with_extension("tla"),
            _ => {
                let mut path = self.spec.clone().into_os_string();
                path.push(".tla");
                PathBuf::from(path)
            }
        }
    }

    /// The configuration: the one `-config` names, or the spec's with `.cfg` for `.tla`.
    pub fn config_path(&self) -> PathBuf {
        self.config.clone().unwrap_or_else(|| self.spec_path().with_extension("cfg"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Args {
        let args = std::iter::once("tla-rs").chain(args.iter().copied()).map(String::from);
        Args::parse_tlc(args).unwrap()
    }

    #[test]
    fn reads_tlc_single_dash_options() {
        let args = parse(&[
            "-config",
            "Other.cfg",
            "-workers",
            "auto",
            "-deadlock",
            "-seed",
            "-4",
            "-fp",
            "0",
            "-nowarning",
            "-lncheck",
            "final",
            "-metadir",
            "states",
            "-noGenerateSpecTE",
            "Spec.tla",
        ]);
        assert_eq!(args.config, Some(PathBuf::from("Other.cfg")));
        assert_eq!(args.workers, Workers::Auto);
        assert!(args.deadlock && args.nowarning && args.no_generate_spec_te);
        assert_eq!(args.seed, -4);
        assert_eq!(args.fp, Some(0));
        assert_eq!(args.lncheck.as_deref(), Some("final"));
        assert_eq!(args.spec_path(), PathBuf::from("Spec.tla"));
        assert_eq!(args.config_path(), PathBuf::from("Other.cfg"));
    }

    #[test]
    fn defaults_the_configuration_to_the_spec_s() {
        let args = parse(&["dir/Spec"]);
        assert_eq!(args.spec_path(), PathBuf::from("dir/Spec.tla"));
        assert_eq!(args.config_path(), PathBuf::from("dir/Spec.cfg"));
        assert_eq!(parse(&["Spec.cfg"]).spec_path(), PathBuf::from("Spec.tla"));
        assert_eq!(parse(&["Spec.tla"]).workers, Workers::Count(1));
    }

    #[test]
    fn reads_library_directories() {
        let args = parse(&["-DTLA-Library=a:b", "--library", "c", "-library", "d", "Spec.tla"]);
        let expected: Vec<PathBuf> = ["a", "b", "c", "d"].iter().map(PathBuf::from).collect();
        assert_eq!(args.library, expected);
    }

    #[test]
    fn rejects_a_bad_worker_count() {
        let args = ["tla-rs", "-workers", "none", "Spec.tla"].map(String::from);
        assert!(Args::parse_tlc(args).is_err());
    }
}
