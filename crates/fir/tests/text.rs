//! The text format, checked on every `.fir` file under `tests/` against the Lean reference tool's
//! parser and printer (`fir-ref fmt --unverified`, which parses without verifying).
//!
//! * Where the reference parses a file, this crate must print it exactly the same (with and
//!   without locations) and print it the same again after reparsing, or reject it with the
//!   file's expected error (`// error: TEXT`). Only name errors qualify: this parser resolves
//!   names, which in Lean is the verifier's job.
//! * Where the reference fails to parse a file, this crate must fail with the same message.
//! * A file with no expected error must also pass the reference's verifier.
//!
//! The reference is `spec/.lake/build/bin/fir-ref` (build it with `lake build` in `spec/`), or
//! the path in `FIR_REF`. `FIR_REF=none` skips the comparison, leaving only the checks that
//! need no reference.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn fir_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            fir_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "fir") {
            out.push(p);
        }
    }
}

fn reference() -> Option<PathBuf> {
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

/// The reference's output for `fir-ref fmt FILE ARGS...`: its stdout, or the message it fails with.
fn reference_fmt(tool: &Path, file: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new(tool)
        .arg("fmt")
        .arg(file)
        .args(args)
        .output()
        .expect("running fir-ref");
    if out.status.success() {
        Ok(String::from_utf8(out.stdout).unwrap())
    } else {
        let err = String::from_utf8(out.stderr).unwrap();
        let prefix = format!("{}: ", file.display());
        Err(err
            .trim_end()
            .strip_prefix(&prefix)
            .unwrap_or(err.trim_end())
            .to_owned())
    }
}

/// Printing is stable: what this crate prints, it reads back and prints the same.
fn check_stable(name: &str, m: &fir::Module, fails: &mut Vec<String>) {
    for show_locs in [true, false] {
        let printed = m.render(show_locs);
        match fir::parse_module(&printed) {
            Ok(m2) if m2.render(show_locs) == printed => {}
            Ok(_) => fails.push(format!("{name}: printing is not stable after reparsing")),
            Err(e) => fails.push(format!("{name}: printed text does not parse: {e}")),
        }
    }
}

#[test]
fn text_matches_reference() {
    let mut files = Vec::new();
    fir_files(&repo().join("tests"), &mut files);
    assert!(!files.is_empty());
    let tool = reference();
    let mut fails = Vec::new();
    let (mut matched, mut rejected_alike, mut name_errors) = (0, 0, 0);
    for file in &files {
        let name = file.strip_prefix(repo()).unwrap().display().to_string();
        let text = std::fs::read_to_string(file).unwrap();
        let expected: Vec<&str> = text
            .lines()
            .filter_map(|l| l.trim().strip_prefix("// error:"))
            .map(str::trim)
            .collect();
        let expects = |e: &str| expected.iter().any(|t| e.contains(t));
        let parsed = fir::parse_module(&text);
        if let Ok(m) = &parsed {
            check_stable(&name, m, &mut fails);
        }
        let Some(tool) = &tool else {
            match &parsed {
                Err(e) if !expects(e) => fails.push(format!("{name}: unexpected error '{e}'")),
                _ => {}
            }
            continue;
        };
        if expected.is_empty()
            && let Err(e) = reference_fmt(tool, file, &[])
        {
            fails.push(format!(
                "{name}: fir-ref rejects a file with no expected error: {e}"
            ));
        }
        match (reference_fmt(tool, file, &["--unverified"]), &parsed) {
            (Ok(_), Ok(m)) => {
                for (show_locs, args) in [
                    (true, &["--unverified"][..]),
                    (false, &["--unverified", "--no-locs"]),
                ] {
                    let printed = m.render(show_locs);
                    match reference_fmt(tool, file, args) {
                        Ok(want) if want == printed => {}
                        Ok(want) => fails.push(format!(
                            "{name} (show_locs={show_locs}): differs from fir-ref\n--- fir-ref\n{want}--- fir\n{printed}"
                        )),
                        Err(e) => fails.push(format!("{name}: fir-ref fails only without locations: {e}")),
                    }
                }
                matched += 1;
            }
            (Ok(_), Err(e)) if expects(e) => name_errors += 1,
            (Ok(_), Err(e)) => {
                fails.push(format!("{name}: fir-ref parses this, but fir fails: {e}"))
            }
            (Err(want), Err(e)) if *e == want => rejected_alike += 1,
            (Err(want), Err(e)) => fails.push(format!(
                "{name}: parse errors differ\n  fir-ref: {want}\n  fir:     {e}"
            )),
            (Err(want), Ok(_)) => fails.push(format!(
                "{name}: fir-ref fails to parse ({want}), but fir accepts"
            )),
        }
    }
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
    eprintln!(
        "{matched} files print like fir-ref, {rejected_alike} fail to parse alike, {name_errors} fail on names as expected"
    );
}
