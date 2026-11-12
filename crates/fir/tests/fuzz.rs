//! Differential fuzzing of the interpreter: random well-typed programs (see `progs`) are run by
//! this crate's interpreter and by `fir-ref run`, with random arguments and fuel limits, and the
//! outcomes must be identical, events included.
//!
//! By default 200 programs run. `FIR_FUZZ=N` runs N, and `FIR_FUZZ_SEED=S` picks another seed;
//! program `k` of seed `S` is always the same, so a failure names the program to replay. Failing
//! programs are written to `target/tmp/fuzz/`. `FIR_FUZZ_SHOW=PREFIX` also prints the runs whose
//! outcome starts with `PREFIX` (say `ambiguous`) and keeps their programs there. With
//! `FIR_REF=none` nothing runs.

#[allow(dead_code)]
mod common;
mod progs;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).map_or(default, |s| s.parse().expect(name))
}

/// What a run prints: stdout, stderr, and the exit code.
type Printed = (String, String, i32);

fn ours(m: &fir::Module, args: &[String], fuel: u64) -> Printed {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match fir::interp::run(m, "f0", &args, fuel) {
        Ok(s) => (format!("{s}\n"), String::new(), 0),
        Err(e) => (String::new(), format!("{e}\n"), 1),
    }
}

fn theirs(tool: &Path, file: &Path, args: &[String], fuel: u64) -> Printed {
    let out = Command::new(tool)
        .arg("run")
        .arg(file)
        .arg("@f0")
        .args(args)
        .arg("--fuel")
        .arg(fuel.to_string())
        .output()
        .unwrap();
    (
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
        out.status.code().unwrap_or(-1),
    )
}

/// The number of events a run printed before its outcome.
fn events(p: &Printed) -> usize {
    p.0.split("; ").take_while(|s| s.starts_with('@')).count()
}

/// The kind of outcome, after any events, for the statistics: `returned`, `ub noalias`, `out of
/// fuel`, ...
fn kind(p: &Printed) -> String {
    let line = if p.2 == 0 {
        p.0.split("; ").find(|s| !s.starts_with('@')).unwrap_or("")
    } else {
        "error"
    };
    let words: Vec<&str> = line.split_whitespace().collect();
    match words.as_slice() {
        ["returned", ..] => "returned".to_owned(),
        ["out", "of", "fuel", ..] => "out of fuel".to_owned(),
        [k @ ("ub" | "trap"), what, ..] => format!("{k} {what}"),
        [k, ..] => k.trim_end_matches(':').to_owned(),
        [] => "empty".to_owned(),
    }
}

#[test]
fn interpreter_matches_reference_on_random_programs() {
    let Some(tool) = common::reference() else {
        return;
    };
    let count = env_u64("FIR_FUZZ", 200);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("fuzz");
    std::fs::create_dir_all(&dir).unwrap();
    let stats = Mutex::new(BTreeMap::<String, u64>::new());
    let fails = Mutex::new(Vec::<String>::new());
    let next = Mutex::new(0u64);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let k = {
                        let mut n = next.lock().unwrap();
                        *n += 1;
                        *n - 1
                    };
                    if k >= count {
                        return;
                    }
                    let mut rng = progs::Rng::new(seed.wrapping_mul(0x1_0000_0001) ^ k);
                    let prog = progs::program(&mut rng);
                    let file = dir.join(format!("s{seed}-p{k}.fir"));
                    std::fs::write(&file, &prog.text).unwrap();
                    let m = fir::parse_module(&prog.text)
                        .and_then(|m| fir::verify_module(&m).map(|_| m))
                        .unwrap_or_else(|e| {
                            panic!("generated program {} is invalid: {e}", file.display())
                        });
                    let show = std::env::var("FIR_FUZZ_SHOW").ok();
                    let mut keep = false;
                    for (args, fuel) in &prog.runs {
                        let (a, b) = (ours(&m, args, *fuel), theirs(&tool, &file, args, *fuel));
                        let mut st = stats.lock().unwrap();
                        *st.entry(kind(&b)).or_default() += 1;
                        let n = events(&b) as u64;
                        if n > 0 {
                            *st.entry("(runs with events)".to_owned()).or_default() += 1;
                            *st.entry("(events)".to_owned()).or_default() += n;
                        }
                        drop(st);
                        if show.as_ref().is_some_and(|k| b.0.starts_with(k)) {
                            keep = true;
                            eprintln!(
                                "{} @f0 {}: {}",
                                file.display(),
                                args.join(" "),
                                b.0.trim_end()
                            );
                        }
                        if a != b {
                            keep = true;
                            fails.lock().unwrap().push(format!(
                                "{} @f0 {} --fuel {fuel}\n  reference: {:?}\n  fir:       {:?}",
                                file.display(),
                                args.join(" "),
                                b,
                                a
                            ));
                        }
                    }
                    if !keep {
                        std::fs::remove_file(&file).unwrap();
                    }
                }
            });
        }
    });
    let stats = stats.into_inner().unwrap();
    let runs: u64 = stats
        .iter()
        .filter(|(k, _)| !k.starts_with('('))
        .map(|(_, n)| n)
        .sum();
    eprintln!("{count} programs, {runs} runs (seed {seed}); outcomes:");
    for (k, n) in &stats {
        eprintln!("  {n:6}  {k}");
    }
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} of {runs} runs differ:\n{}",
        fails.len(),
        fails.join("\n")
    );
}
