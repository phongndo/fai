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
//! See `common` for where the reference comes from; `FIR_REF=none` leaves only the checks that
//! need no reference.

mod common;

use std::path::Path;

use common::{display_name, expected_errors, fir_files, outcome, reference, run};

/// The reference's output for `fir-ref fmt FILE ARGS...`: its stdout, or the message it fails with.
fn reference_fmt(tool: &Path, file: &Path, args: &[&str]) -> Result<String, String> {
    outcome(&run(tool, "fmt", file, args), file)
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
    let files = fir_files();
    let tool = reference();
    let mut fails = Vec::new();
    let (mut matched, mut rejected_alike, mut name_errors) = (0, 0, 0);
    for file in &files {
        let name = display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let expected = expected_errors(&text);
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
