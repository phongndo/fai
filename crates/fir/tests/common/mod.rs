//! What the tests share: the `.fir` files under `tests/`, and the Lean reference tool.
//!
//! The reference is `spec/.lake/build/bin/fir-ref` (build it with `lake build` in `spec/`), or
//! the path in `FIR_REF`. `FIR_REF=none` skips the comparisons, leaving only the checks that
//! need no reference.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

pub fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

/// Every `.fir` file under `tests/`, sorted.
pub fn fir_files() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let mut entries: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|e| e == "fir") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(&repo().join("tests"), &mut out);
    assert!(!out.is_empty());
    out
}

/// The file's path relative to the repository, for messages.
pub fn display_name(file: &Path) -> String {
    file.strip_prefix(repo()).unwrap().display().to_string()
}

/// The errors a test file expects (`// error: TEXT`).
pub fn expected_errors(text: &str) -> Vec<&str> {
    text.lines()
        .filter_map(|l| l.trim().strip_prefix("// error:"))
        .map(str::trim)
        .collect()
}

pub fn reference() -> Option<PathBuf> {
    match std::env::var("FIR_REF") {
        Ok(s) if s == "none" => None,
        Ok(s) => Some(PathBuf::from(s)),
        Err(_) => {
            let p = repo().join("spec/.lake/build/bin/fir-ref");
            assert!(
                p.exists(),
                "the Lean reference tool is missing: run `lake build` in spec/, or set FIR_REF=none to skip"
            );
            Some(p)
        }
    }
}

/// Run `TOOL CMD FILE ARGS...`.
pub fn run(tool: &Path, cmd: &str, file: &Path, args: &[&str]) -> Output {
    Command::new(tool)
        .arg(cmd)
        .arg(file)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", tool.display()))
}

/// A run's stdout, or the message it fails with (stderr without the `FILE: ` prefix).
pub fn outcome(out: &Output, file: &Path) -> Result<String, String> {
    if out.status.success() {
        Ok(String::from_utf8(out.stdout.clone()).unwrap())
    } else {
        let err = String::from_utf8(out.stderr.clone()).unwrap();
        let prefix = format!("{}: ", file.display());
        Err(err
            .trim_end()
            .strip_prefix(&prefix)
            .unwrap_or(err.trim_end())
            .to_owned())
    }
}
