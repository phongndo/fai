//! The interpreter, checked on every `// run: @f(ARGS) -> OUTCOME` line of the `.fir` files under
//! `tests/` against the Lean reference tool: `fir run FILE @f ARGS...` must print exactly what
//! `fir-ref run` prints (same stdout, stderr, and exit code), and that must be the outcome the
//! file expects.
//!
//! See `common` for where the reference comes from. With `FIR_REF=none`, only the expectations
//! are checked.

// This test uses only part of the shared helpers.
#[allow(dead_code)]
mod common;

use std::path::Path;
use std::process::{Command, Output};

use common::{display_name, fir_files, reference};

/// A `// run:` line: the function, its arguments, and the expected outcome (Lean's
/// `expectations` and `parseCall`).
fn run_lines(text: &str) -> Vec<(String, Vec<String>, String)> {
    let mut out = Vec::new();
    for line in text.lines() {
        let Some(body) = line.trim().strip_prefix("// run:") else {
            continue;
        };
        // The outcome may contain ` -> ` itself (a function type), so split at the first.
        let Some((call, want)) = body.split_once(" -> ") else {
            panic!("bad run line: {line}");
        };
        let call = call.trim();
        let (name, rest) = call
            .strip_prefix('@')
            .and_then(|c| c.split_once('('))
            .unwrap_or_else(|| panic!("bad run line: {line}"));
        let inner = rest
            .strip_suffix(')')
            .unwrap_or_else(|| panic!("bad run line: {line}"));
        let args = if inner.trim().is_empty() {
            Vec::new()
        } else {
            inner.split(',').map(|a| a.trim().to_owned()).collect()
        };
        out.push((name.to_owned(), args, want.trim().to_owned()));
    }
    out
}

fn run(tool: &Path, file: &Path, name: &str, args: &[String]) -> Output {
    Command::new(tool)
        .arg("run")
        .arg(file)
        .arg(format!("@{name}"))
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", tool.display()))
}

fn show(out: &Output) -> String {
    format!(
        "exit {}, stdout {:?}, stderr {:?}",
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn run_matches_reference() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let tool = reference();
    let ev = common::evidence::Evidence::new("run_fixtures");
    let mut fails = Vec::new();
    let mut checked = 0;
    for file in &fir_files() {
        let name = display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let lines = run_lines(&text);
        let module = fir::parse_module(&text)
            .and_then(|m| fir::verify_module(&m).map(|_| m))
            .ok();
        for (func, args, want) in lines {
            checked += 1;
            let call = format!("{name}: @{func}({})", args.join(", "));
            let got = run(fir, file, &func, &args);
            let stdout = String::from_utf8_lossy(&got.stdout);
            if !got.status.success() || stdout.trim_end() != want {
                fails.push(format!("{call}: expected '{want}' but got {}", show(&got)));
            }
            if let Some(tool) = &tool {
                ev.count("runs compared with fir-ref run", 1);
                let reference = run(tool, file, &func, &args);
                if (&got.stdout, &got.stderr, got.status.code())
                    != (
                        &reference.stdout,
                        &reference.stderr,
                        reference.status.code(),
                    )
                {
                    fails.push(format!(
                        "{call}: reference {}, fir {}",
                        show(&reference),
                        show(&got)
                    ));
                } else if got.status.success()
                    && stdout.trim_end() == want
                    && let Some(m) = &module
                {
                    // Compare this profiled run too, so coverage is about the same function,
                    // arguments, fuel and result as the successful CLI/reference comparison.
                    let args: Vec<&str> = args.iter().map(String::as_str).collect();
                    let r =
                        fir::interp::run_detail(m, &func, &args, fir::interp::DEFAULT_FUEL, false)
                            .unwrap();
                    assert_eq!(
                        format!("{}\n", r.line).as_bytes(),
                        got.stdout,
                        "{call}: profiled run differs"
                    );
                    ev.executed(&r.profile);
                }
            }
        }
    }
    assert!(checked > 0);
    ev.count("run lines", checked);
    ev.count("failures", fails.len() as u64);
    ev.write();
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

/// Command-line handling the fixtures don't cover: argument syntax, `--fuel`, and errors.
#[test]
fn command_line_matches_reference() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let Some(tool) = reference() else { return };
    let file = common::repo().join("tests/fir0/sum.fir");
    let cases: &[&[&str]] = &[
        &["@sum", "5"],
        &["@sum", "-5"],
        &["@sum", "1_000"],
        &["@sum", "-1_0"],
        &["@sum", "+5"],
        &["@sum", "_1"],
        &["@sum", "1_"],
        &["@sum", "1__0"],
        &["@sum", ""],
        &["@sum", "0x10"],
        &["@sum", "poison"],
        &["@sum", "null"],
        &["@sum", "99999999999999999999"],
        &["@sum", "100", "--fuel", "50"],
        &["@sum", "100", "--fuel", "abc"],
        &["@sum", "100", "--fuel", "0"],
        &["@sum", "3", "--fuel", "10", "--fuel", "20"],
        &["@sum", "--fuel", "20"],
        &["@sum"],
        &["@sum", "1", "2"],
        &["@nope"],
        &["sum", "3"],
        &[],
    ];
    let mut fails = Vec::new();
    for args in cases {
        let mut ours = Command::new(fir);
        let mut theirs = Command::new(&tool);
        for c in [&mut ours, &mut theirs] {
            c.arg("run").arg(&file).args(*args);
        }
        let (a, b) = (ours.output().unwrap(), theirs.output().unwrap());
        if (&a.stdout, &a.stderr, a.status.code()) != (&b.stdout, &b.stderr, b.status.code()) {
            fails.push(format!(
                "{args:?}: reference {}, fir {}",
                show(&b),
                show(&a)
            ));
        }
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
