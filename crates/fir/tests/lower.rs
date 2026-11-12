//! The lowering from HFIR to MFIR (`fir lower`, `src/lower.rs`), checked on every HFIR `.fir`
//! file under `tests/`: it must print exactly what `fir-ref lower` prints (same stdout, stderr,
//! and exit code), and every `// run:` line must give the same outcome on the lowering as on the
//! HFIR program, unless the HFIR run ends in UB (or gets stuck), where the lowering must perform
//! the same events first and may then do anything (`RunOutput::lowers_to`). The reference tool
//! checks the same rule on its own lowering (`fir-ref test`). A `// lower-error: TEXT` line
//! expects lowering to fail with a message containing TEXT.

#[allow(dead_code)]
mod common;

use std::path::Path;

use common::{display_name, fir_files, reference};

#[test]
fn lowering_matches_reference_and_refines() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let tool = reference();
    let mut fails = Vec::new();
    let mut lowered = 0;
    let mut runs = 0;
    for file in &fir_files() {
        let name = display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() {
            continue;
        }
        if let Some(tool) = &tool {
            let (a, b) = (
                common::run(fir, "lower", file, &[]),
                common::run(tool, "lower", file, &[]),
            );
            if (&a.stdout, &a.stderr, a.status.code()) != (&b.stdout, &b.stderr, b.status.code()) {
                fails.push(format!(
                    "{name}: fir lower printed {:?} {:?}, fir-ref lower {:?} {:?}",
                    String::from_utf8_lossy(&a.stdout),
                    String::from_utf8_lossy(&a.stderr),
                    String::from_utf8_lossy(&b.stdout),
                    String::from_utf8_lossy(&b.stderr)
                ));
            }
        }
        if m.layer != fir::Layer::Hfir {
            continue;
        }
        let expected: Vec<&str> = text
            .lines()
            .filter_map(|l| l.trim().strip_prefix("// lower-error:"))
            .map(str::trim)
            .collect();
        let l = match fir::lower_checked(&m) {
            Ok(l) => {
                if let Some(t) = expected.first() {
                    fails.push(format!("{name}: expected lowering to fail with '{t}'"));
                }
                l
            }
            Err(e) => {
                if expected.is_empty() {
                    fails.push(format!("{name}: {e}"));
                }
                for t in &expected {
                    if !e.contains(t) {
                        fails.push(format!(
                            "{name}: lowering error '{e}' does not contain '{t}'"
                        ));
                    }
                }
                continue;
            }
        };
        lowered += 1;
        for line in text.lines() {
            let Some(body) = line.trim().strip_prefix("// run:") else {
                continue;
            };
            let call = body.split_once(" -> ").unwrap().0.trim();
            let (func, rest) = call.strip_prefix('@').unwrap().split_once('(').unwrap();
            let inner = rest.strip_suffix(')').unwrap();
            let args: Vec<&str> = if inner.trim().is_empty() {
                Vec::new()
            } else {
                inner.split(',').map(str::trim).collect()
            };
            let fuel = fir::interp::DEFAULT_FUEL;
            let (Ok(src), Ok(tgt)) = (
                fir::interp::run_detail(&m, func, &args, fuel, true),
                fir::interp::run_detail(&l, func, &args, 16 * fuel, false),
            ) else {
                continue;
            };
            runs += 1;
            if !src.lowers_to(&tgt) {
                fails.push(format!(
                    "{name}: @{func}({}): HFIR '{}', lowered '{}'",
                    args.join(", "),
                    src.line,
                    tgt.line
                ));
            }
        }
    }
    assert!(lowered > 0 && runs > 0);
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
