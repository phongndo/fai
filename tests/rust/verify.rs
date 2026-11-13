//! The verifier, checked on every `.fir` file under `tests/` against the Lean reference tool's
//! (`fir-ref check`), through the command-line tool: `fir check FILE` must print exactly what
//! `fir-ref check FILE` prints (`ok`, the holes, or the error), on the same stream with the same
//! exit code.
//!
//! The one allowed difference is the file's expected error (`// error: TEXT`) when this crate's
//! parser reports it: the parser resolves names, which in Lean is the verifier's job, so it
//! reports undefined and repeated values with a different position, and before any verifier
//! error. The reference must then fail with the expected error too.
//!
//! See `common` for where the reference comes from. With `FIR_REF=none`, a file must pass
//! `fir check` exactly when it expects no error, and otherwise fail with its expected error.

mod common;

use std::path::Path;
use std::process::Output;

use common::{display_name, expected_errors, fir_files, outcome, reference, run};

fn show(out: &Output) -> String {
    format!(
        "exit {}, stdout {:?}, stderr {:?}",
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn check_matches_reference() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let tool = reference();
    let mut fails = Vec::new();
    let (mut matched, mut name_errors) = (0, 0);
    for file in &fir_files() {
        let name = display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let expected = expected_errors(&text);
        let expects = |e: &str| expected.iter().any(|t| e.contains(t));
        let ours = run(fir, "check", file, &[]);
        let Some(tool) = &tool else {
            match outcome(&ours, file) {
                Ok(_) if !expected.is_empty() => {
                    fails.push(format!("{name}: expected an error, but fir check passes"))
                }
                Err(e) if !expects(&e) => fails.push(format!("{name}: unexpected error '{e}'")),
                _ => {}
            }
            continue;
        };
        let theirs = run(tool, "check", file, &[]);
        if (ours.status.code(), &ours.stdout, &ours.stderr)
            == (theirs.status.code(), &theirs.stdout, &theirs.stderr)
        {
            matched += 1;
            continue;
        }
        // The one allowed difference: both reject on a name, and `fir` reports it from the
        // parser, with the parser's message and otherwise the same behavior.
        let name_error = match (
            fir::parse_module(&text),
            outcome(&ours, file),
            outcome(&theirs, file),
        ) {
            (Err(e), Err(cli), Err(want)) => {
                cli == e
                    && expects(&e)
                    && expects(&want)
                    && ours.status.code() == theirs.status.code()
                    && ours.stdout.is_empty()
                    && theirs.stdout.is_empty()
            }
            _ => false,
        };
        if name_error {
            name_errors += 1;
        } else {
            fails.push(format!(
                "{name}: check differs from fir-ref\n  fir-ref: {}\n  fir:     {}",
                show(&theirs),
                show(&ours)
            ));
        }
    }
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
    eprintln!("{matched} files check like fir-ref, {name_errors} fail on names as expected");
}
