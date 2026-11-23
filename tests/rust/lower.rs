//! The lowering from HFIR to MFIR (`fir lower`, `src/lower.rs`), checked on every HFIR `.fir`
//! file under `tests/`: it must print exactly what `fir-ref lower` prints (same stdout, stderr,
//! and exit code), and every `// run:` line must give the same outcome on the lowering as on the
//! HFIR program, unless the HFIR run ends in UB (or gets stuck), where the lowering must perform
//! the same events first and may then do anything (`RunOutput::lowers_to`). The reference tool
//! checks the same rule on its own lowering (`fir-ref test`). A `// lower-error: TEXT` line
//! expects lowering to fail with a message containing TEXT.
//!
//! A `// run:` line gives scalar arguments only, so a function that takes a struct, an array, a
//! union, or a slice is run by those lines only through its callers. Each such function is
//! also run on generated values, and its lowering on the same values encoded as the lowered
//! signature takes them (`fir::interp::run_lowering_pair`): the lowered signature itself,
//! checked against the encoding the refinement statement uses.

#[allow(dead_code)]
mod common;

use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};

use common::{display_name, fir_files, reference};

/// How many sets of generated arguments each function with a composite parameter runs on.
const PAIR_SEEDS: u64 = 8;

#[test]
fn lowering_matches_reference_and_refines() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let tool = reference();
    // One file per step, on every core: each file is lowered and run by itself.
    let fails = Mutex::new(Vec::new());
    let (lowered, runs) = (AtomicU64::new(0), AtomicU64::new(0));
    let (pair_funcs, pair_runs, pair_skipped) =
        (AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0));
    let pair_returns = AtomicU64::new(0);
    let files = fir_files();
    let next = AtomicUsize::new(0);
    let one = |file: &Path| {
        let name = display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            return;
        };
        if fir::verify_module(&m).is_err() {
            return;
        }
        if let Some(tool) = &tool {
            let (a, b) = (
                common::run(fir, "lower", file, &[]),
                common::run(tool, "lower", file, &[]),
            );
            if (&a.stdout, &a.stderr, a.status.code()) != (&b.stdout, &b.stderr, b.status.code()) {
                fails.lock().unwrap().push(format!(
                    "{name}: fir lower printed {:?} {:?}, fir-ref lower {:?} {:?}",
                    String::from_utf8_lossy(&a.stdout),
                    String::from_utf8_lossy(&a.stderr),
                    String::from_utf8_lossy(&b.stdout),
                    String::from_utf8_lossy(&b.stderr)
                ));
            }
        }
        if m.layer != fir::Layer::Hfir {
            return;
        }
        let expected: Vec<&str> = text
            .lines()
            .filter_map(|l| l.trim().strip_prefix("// lower-error:"))
            .map(str::trim)
            .collect();
        let l = match fir::lower_checked(&m) {
            Ok(l) => {
                if let Some(t) = expected.first() {
                    fails
                        .lock()
                        .unwrap()
                        .push(format!("{name}: expected lowering to fail with '{t}'"));
                }
                l
            }
            Err(e) => {
                if expected.is_empty() {
                    fails.lock().unwrap().push(format!("{name}: {e}"));
                }
                for t in &expected {
                    if !e.contains(t) {
                        fails.lock().unwrap().push(format!(
                            "{name}: lowering error '{e}' does not contain '{t}'"
                        ));
                    }
                }
                return;
            }
        };
        lowered.fetch_add(1, Relaxed);
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
            runs.fetch_add(1, Relaxed);
            if !src.lowers_to(&tgt) {
                fails.lock().unwrap().push(format!(
                    "{name}: @{func}({}): HFIR '{}', lowered '{}'",
                    args.join(", "),
                    src.line,
                    tgt.line
                ));
            }
        }
        // The functions a `// run:` line can't call: those taking a struct, an array, a union,
        // or a slice. Each runs on generated values, and its lowering on the same values as
        // the lowered signature takes them (`fir::interp::run_lowering_pair`).
        for f in &m.funcs {
            let body = &f.body;
            if body.params(body.entry()).all(|p| body.ty(p).is_value()) {
                continue;
            }
            let mut compared = false;
            for seed in 0..PAIR_SEEDS {
                let fuel = fir::interp::DEFAULT_FUEL;
                match fir::interp::run_lowering_pair(&m, &l, &f.name, seed, fuel) {
                    Ok(Some((src, tgt))) => {
                        compared = true;
                        pair_runs.fetch_add(1, Relaxed);
                        // A run that returns compares the whole result; one that ends in UB
                        // lets the lowering do anything after the same events.
                        if src.line.starts_with("returned") {
                            pair_returns.fetch_add(1, Relaxed);
                        }
                        if !src.lowers_to(&tgt) {
                            fails.lock().unwrap().push(format!(
                                "{name}: @{} on generated arguments (seed {seed}): HFIR '{}', lowered '{}'",
                                f.name, src.line, tgt.line
                            ));
                        }
                    }
                    Ok(None) => break,
                    Err(e) => {
                        fails.lock().unwrap().push(format!("{name}: {e}"));
                        break;
                    }
                }
            }
            if compared {
                pair_funcs.fetch_add(1, Relaxed);
            } else {
                pair_skipped.fetch_add(1, Relaxed);
            }
        }
    };
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let Some(file) = files.get(next.fetch_add(1, Relaxed)) else {
                        return;
                    };
                    one(file);
                }
            });
        }
    });
    let mut fails = fails.into_inner().unwrap();
    fails.sort();
    let (lowered, runs) = (lowered.into_inner(), runs.into_inner());
    let ev = common::evidence::Evidence::new("lower_fixtures");
    ev.count("modules lowered", lowered);
    ev.count("runs compared (HFIR against its lowering)", runs);
    ev.count(
        "lowering compared with fir-ref lower",
        if tool.is_some() { lowered } else { 0 },
    );
    ev.count(
        "functions with composite parameters compared on generated arguments",
        pair_funcs.into_inner(),
    );
    ev.count("generated runs compared", pair_runs.into_inner());
    ev.count(
        "generated runs compared where the source returned",
        pair_returns.into_inner(),
    );
    ev.count(
        "functions with composite parameters not compared (a type that isn't generated)",
        pair_skipped.into_inner(),
    );
    ev.count("failures", fails.len() as u64);
    ev.write();
    assert!(lowered > 0 && runs > 0);
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
