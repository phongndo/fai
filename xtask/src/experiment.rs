//! `cargo xtask experiment`: propose a compiler change, test it, and measure it, without touching
//! anything but `target/experiments/NAME/`.
//!
//! ```text
//! cargo xtask experiment NAME [--passes P,... [--experimental] | --none]
//!                             [--baseline-passes P,... | --baseline-none] [--baseline-rev REV]
//!                             [--gate quick|none] [--fuzz N] [--seed S] [--jobs N]
//! ```
//!
//! An experiment compares a **candidate** with a **baseline**. The candidate is this working tree
//! (committed or not) with the candidate pipeline (`--passes`, `-O` by default); the baseline is
//! this tree, or the tree at `--baseline-rev REV` (checked out in a temporary git worktree and
//! built in its own target directory), with the baseline pipeline (`-O` by default). So a new
//! pipeline is `--passes …`, and a change to the compiler's code is `--baseline-rev main`.
//!
//! 1. **Measure** (`fir measure`, see `tools/fir/measure.rs`) every `.fir` module under `tests/`
//!    (not the `errors/` corpora) with both: ops in the prepared MFIR, ops the interpreter
//!    executed on the module's `// run:` lines (in all, memory ops, calls), and the instructions
//!    the AArch64 and x86-64 backends emit. All are deterministic: the same on every host and
//!    every run, so a difference is the change's and not noise. Every candidate run must refine
//!    its source run and print what the file expects; a module the baseline prepares and the
//!    candidate can't is a failure too.
//! 2. **Gate** (`--gate quick`, the default): the differential suites with the candidate pipeline
//!    (`FIR_PASSES`): `opt` (every fixture and `--fuzz` random programs, 200 by default, each run
//!    of the optimized module refining the original's), `aarch64` and `x86_64` (fixtures and
//!    random programs compiled with the pipeline, run natively or under qemu, compared with the
//!    interpreter), in release, with `FIR_REQUIRE_FULL=1` and the evidence checked: each suite
//!    reported, tested the candidate's pipeline, skipped nothing, failed nothing, and ran the
//!    configured number of programs. A suite the host can't run is accepted only if
//!    `HOST_GAPS` declares it for this host, and is reported as unverified. `--gate none` only
//!    measures; its verdict says it is ungated.
//! 3. **Report**: `target/experiments/NAME/report.json` and `report.md`, and a summary on stderr:
//!    the identity of both sides (revision, whether the tree was dirty, and a hash of the diff),
//!    each metric's totals, change, files better and worse, and geometric mean ratio, the
//!    largest changes, the correctness problems, the gate's checks, what the host couldn't run,
//!    and what backs each pass of the candidate.
//!
//! The verdict is `REJECTED` (a correctness problem, a failing gate, or a harness error: exit 1),
//! or, for a candidate that passed, `IMPROVED`, `REGRESSED`, `MIXED`, or `NO CHANGE` by the
//! executed ops (the primary metric) and the others (exit 0). Passing is evidence on this corpus
//! and these random programs, not a proof: a candidate with an unproved pass is reported as not
//! eligible for the default pipeline, whatever it measures. `verify full` (which clears
//! `FIR_PASSES`) remains the required check for anything that lands.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use serde_json::{Value, json};

use crate::{CLEARED, filtered_out, host, host_gap_reason, load_evidence};

/// What the experiment measures, primary first; lower is better for every one.
const METRICS: &[&str] = &[
    "ops.executed",
    "mem.executed",
    "calls.executed",
    "ops.static",
    "aarch64.insns",
    "x86_64.insns",
];

/// Metrics that count the runs, so they compare only where both sides measured the same runs.
fn dynamic(metric: &str) -> bool {
    metric.ends_with(".executed")
}

#[derive(Clone, Debug, PartialEq)]
enum Pipe {
    Default,
    None,
    Passes { spec: String, experimental: bool },
}

impl Pipe {
    fn measure_args(&self) -> Vec<String> {
        match self {
            Pipe::Default => vec!["-O".into()],
            Pipe::None => vec!["--none".into()],
            Pipe::Passes { spec, experimental } => {
                let mut a = vec!["--passes".into(), spec.clone()];
                if *experimental {
                    a.push("--experimental".into());
                }
                a
            }
        }
    }

    fn show(&self) -> String {
        match self {
            Pipe::Default => "-O".into(),
            Pipe::None => "none".into(),
            Pipe::Passes { spec, .. } => spec.clone(),
        }
    }
}

struct Opts {
    name: String,
    cand: Pipe,
    base: Pipe,
    base_rev: Option<String>,
    gate: bool,
    fuzz: u64,
    seed: u64,
    jobs: usize,
}

const USAGE: &str = "usage: cargo xtask experiment NAME [--passes P,... [--experimental] | --none]\n                              [--baseline-passes P,... | --baseline-none] [--baseline-rev REV]\n                              [--gate quick|none] [--fuzz N] [--seed S] [--jobs N]";

fn parse(args: &[String]) -> Result<Opts, String> {
    let mut it = args.iter();
    let name = it.next().ok_or("an experiment needs a NAME")?.clone();
    if name.is_empty()
        || name.starts_with(['-', '.'])
        || !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_.".contains(c))
    {
        return Err(format!(
            "bad experiment name {name:?}: letters, digits, '-', '_', '.'"
        ));
    }
    let mut o = Opts {
        name,
        cand: Pipe::Default,
        base: Pipe::Default,
        base_rev: None,
        gate: true,
        fuzz: 200,
        seed: 1,
        jobs: std::thread::available_parallelism().map_or(4, |n| n.get()),
    };
    let mut experimental = false;
    let value = |it: &mut std::slice::Iter<'_, String>, flag: &str| {
        it.next()
            .cloned()
            .ok_or_else(|| format!("{flag} needs a value"))
    };
    while let Some(a) = it.next() {
        match a.as_str() {
            "--passes" => {
                o.cand = Pipe::Passes {
                    spec: value(&mut it, a)?,
                    experimental: false,
                }
            }
            "--experimental" => experimental = true,
            "--none" => o.cand = Pipe::None,
            "--baseline-passes" => {
                o.base = Pipe::Passes {
                    spec: value(&mut it, a)?,
                    experimental: true,
                }
            }
            "--baseline-none" => o.base = Pipe::None,
            "--baseline-rev" => o.base_rev = Some(value(&mut it, a)?),
            "--gate" => match value(&mut it, a)?.as_str() {
                "quick" => o.gate = true,
                "none" => o.gate = false,
                g => return Err(format!("unknown gate {g:?}: quick or none")),
            },
            "--fuzz" => {
                o.fuzz = value(&mut it, a)?
                    .parse()
                    .map_err(|e| format!("--fuzz: {e}"))?
            }
            "--seed" => {
                o.seed = value(&mut it, a)?
                    .parse()
                    .map_err(|e| format!("--seed: {e}"))?
            }
            "--jobs" => {
                o.jobs = value(&mut it, a)?
                    .parse()
                    .map_err(|e| format!("--jobs: {e}"))?
            }
            _ => return Err(format!("unknown option {a}")),
        }
    }
    if let Pipe::Passes {
        experimental: e, ..
    } = &mut o.cand
    {
        *e = experimental;
    } else if experimental {
        return Err("--experimental goes with --passes".into());
    }
    // The suites take a pipeline as `FIR_PASSES` (empty means `-O`): no passes can't be gated.
    if o.gate && o.cand == Pipe::None {
        return Err(
            "--none can only be measured (--gate none): the gate's suites need passes".into(),
        );
    }
    if o.fuzz == 0 || o.jobs == 0 {
        return Err("--fuzz and --jobs must be positive".into());
    }
    Ok(o)
}

/// A command with the weakening variables cleared, as `verify` runs its children.
fn clean(prog: &str, dir: &Path) -> Command {
    let mut c = Command::new(prog);
    c.current_dir(dir).stdin(Stdio::null());
    for v in CLEARED {
        c.env_remove(v);
    }
    for (k, _) in std::env::vars() {
        if k.starts_with("CARGO_TARGET_") && k.ends_with("_RUNNER") {
            c.env_remove(k);
        }
    }
    c
}

/// Run `c`, logging its output to `log`; its success and the log's tail.
fn logged(mut c: Command, log: &Path) -> (bool, String) {
    let out = c.output();
    let (ok, text) = match out {
        Ok(o) => (
            o.status.success(),
            format!(
                "{}\n--- stderr ---\n{}",
                String::from_utf8_lossy(&o.stdout),
                String::from_utf8_lossy(&o.stderr)
            ),
        ),
        Err(e) => (false, format!("can't run: {e}")),
    };
    std::fs::write(log, &text).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    (ok, lines[lines.len().saturating_sub(25)..].join("\n"))
}

fn git(root: &Path, args: &[&str]) -> String {
    Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .unwrap_or_default()
}

/// The revision, whether the tree is dirty, and a hash of its diff against that revision.
fn identity(root: &Path) -> Value {
    let dirty = !git(root, &["status", "--porcelain"]).is_empty();
    let mut diff = Command::new("git")
        .args(["diff", "HEAD", "--binary"])
        .current_dir(root)
        .output()
        .map(|o| o.stdout)
        .unwrap_or_default();
    // Untracked files can be build inputs (a new pass): their names and contents count too.
    for f in git(root, &["ls-files", "--others", "--exclude-standard"]).lines() {
        diff.extend_from_slice(format!("\0untracked {f}\0").as_bytes());
        diff.extend(std::fs::read(root.join(f)).unwrap_or_default());
    }
    let hash = Command::new("git")
        .args(["hash-object", "--stdin"])
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .and_then(|mut ch| {
            use std::io::Write as _;
            ch.stdin.take().unwrap().write_all(&diff)?;
            ch.wait_with_output()
        })
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .unwrap_or_default();
    json!({
        "revision": git(root, &["rev-parse", "HEAD"]),
        "branch": git(root, &["rev-parse", "--abbrev-ref", "HEAD"]),
        "dirty": dirty,
        // Of `git diff HEAD` and every untracked file's name and contents.
        "diff hash": if dirty { hash } else { String::new() },
        "untracked files": git(root, &["ls-files", "--others", "--exclude-standard"]).lines().count(),
    })
}

/// The modules measured: every `.fir` file under `tests/` outside an `errors/` directory.
fn corpus(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
            .into_iter()
            .flatten()
            .flatten()
            .map(|e| e.path())
            .collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                if p.file_name().is_some_and(|n| n != "errors") {
                    walk(&p, out);
                }
            } else if p.extension().is_some_and(|e| e == "fir") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(&root.join("tests"), &mut out);
    out
}

/// One side's measurement of one module: the JSON `fir measure` printed, or why there is none.
type Measured = Result<Value, String>;

fn measure_all(
    fir: &Path,
    root: &Path,
    files: &[PathBuf],
    pipe: &Pipe,
    jobs: usize,
) -> Vec<Measured> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: Vec<std::sync::Mutex<Option<Measured>>> =
        files.iter().map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|s| {
        for _ in 0..jobs.min(files.len()).max(1) {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(file) = files.get(i) else { break };
                    let rel = file.strip_prefix(root).unwrap_or(file);
                    let out = clean(&fir.display().to_string(), root)
                        .arg("measure")
                        .arg(rel)
                        .args(pipe.measure_args())
                        .output();
                    let r = match out {
                        Err(e) => Err(format!("can't run {}: {e}", fir.display())),
                        // `fir measure` exits 0 or 1 with its JSON; anything else (a panic, a
                        // crash, bad usage) is a harness failure, whatever it printed.
                        Ok(o) => match serde_json::from_slice::<Value>(&o.stdout) {
                            Ok(v) if matches!(o.status.code(), Some(0 | 1)) => Ok(v),
                            _ => Err(format!(
                                "fir measure exited with {}: {}",
                                o.status,
                                String::from_utf8_lossy(&o.stderr).trim()
                            )),
                        },
                    };
                    *results[i].lock().unwrap() = Some(r);
                }
            });
        }
    });
    results
        .into_iter()
        .map(|m| m.into_inner().unwrap().unwrap())
        .collect()
}

/// Build `fir` in release from the tree at `dir`, into `target` (with the tree's own lock file),
/// and copy the binary to `keep`, so another build into `target` (another experiment) can't
/// replace it while this one measures; the copy.
fn build_fir(dir: &Path, target: &Path, log: &Path, keep: &Path) -> Result<PathBuf, String> {
    let mut c = clean("cargo", dir);
    c.args(["build", "--release", "--locked", "--bin", "fir"])
        .env("CARGO_TARGET_DIR", target);
    let (ok, tail) = logged(c, log);
    if !ok {
        return Err(format!("building fir in {} failed:\n{tail}", dir.display()));
    }
    std::fs::copy(target.join("release/fir"), keep)
        .map_err(|e| format!("copying fir to {}: {e}", keep.display()))?;
    Ok(keep.to_owned())
}

/// The worktree a baseline revision is checked out in, removed when dropped.
struct Worktree<'a> {
    root: &'a Path,
    path: PathBuf,
}

impl Drop for Worktree<'_> {
    fn drop(&mut self) {
        let removed = Command::new("git")
            .args(["worktree", "remove", "--force"])
            .arg(&self.path)
            .current_dir(self.root)
            .output();
        if !removed.is_ok_and(|o| o.status.success()) {
            eprintln!(
                "warning: couldn't remove the baseline worktree {}: remove it with `git worktree remove --force` (the next experiment prunes it)",
                self.path.display()
            );
        }
    }
}

fn metric(v: &Value, k: &str) -> Option<u64> {
    v["metrics"][k].as_u64()
}

/// Per-metric comparison over the modules both sides measured.
fn compare(
    files: &[String],
    base: &[Measured],
    cand: &[Measured],
) -> (serde_json::Map<String, Value>, Vec<String>) {
    let mut table = serde_json::Map::new();
    let mut refusals = Vec::new();
    for (i, f) in files.iter().enumerate() {
        if let (Ok(b), Ok(c)) = (&base[i], &cand[i]) {
            for t in ["aarch64", "x86_64"] {
                let key = format!("{t}.refused");
                if b[&key].is_null() && !c[&key].is_null() {
                    refusals.push(format!("{f}: {t} now refuses it: {}", c[&key]));
                }
            }
        }
    }
    for &m in METRICS {
        let (mut bt, mut ct) = (0u64, 0u64);
        let (mut better, mut worse, mut same) = (0u64, 0u64, 0u64);
        let (mut log_sum, mut logs) = (0f64, 0u64);
        let mut changes: Vec<(f64, String, u64, u64)> = Vec::new();
        for (i, f) in files.iter().enumerate() {
            let (Ok(b), Ok(c)) = (&base[i], &cand[i]) else {
                continue;
            };
            if dynamic(m)
                && (metric(b, "runs measured") != metric(c, "runs measured")
                    || metric(b, "runs measured") == Some(0))
            {
                continue;
            }
            let (Some(bv), Some(cv)) = (metric(b, m), metric(c, m)) else {
                continue;
            };
            bt += bv;
            ct += cv;
            match cv.cmp(&bv) {
                std::cmp::Ordering::Less => better += 1,
                std::cmp::Ordering::Greater => worse += 1,
                std::cmp::Ordering::Equal => same += 1,
            }
            if bv > 0 && cv > 0 {
                log_sum += (cv as f64 / bv as f64).ln();
                logs += 1;
            }
            if bv != cv {
                let rel = if bv == 0 {
                    f64::INFINITY
                } else {
                    cv as f64 / bv as f64 - 1.0
                };
                changes.push((rel, f.clone(), bv, cv));
            }
        }
        changes.sort_by(|a, b| a.0.total_cmp(&b.0));
        let show = |v: &[(f64, String, u64, u64)]| -> Vec<Value> {
            v.iter()
                .map(|(r, f, b, c)| json!({"file": f, "baseline": b, "candidate": c, "change": format!("{:+.1}%", r * 100.0)}))
                .collect()
        };
        let improvements: Vec<_> = changes
            .iter()
            .filter(|c| c.0 < 0.0)
            .take(5)
            .cloned()
            .collect();
        let regressions: Vec<_> = changes
            .iter()
            .rev()
            .filter(|c| c.0 > 0.0)
            .take(5)
            .cloned()
            .collect();
        table.insert(
            m.to_owned(),
            json!({
                "baseline": bt,
                "candidate": ct,
                "change": if bt == 0 { "n/a".to_owned() } else { format!("{:+.2}%", (ct as f64 / bt as f64 - 1.0) * 100.0) },
                "modules better": better,
                "modules worse": worse,
                "modules same": same,
                "geomean ratio": if logs == 0 { Value::Null } else { json!(format!("{:.4}", (log_sum / logs as f64).exp())) },
                "largest improvements": show(&improvements),
                "largest regressions": show(&regressions),
            }),
        );
    }
    (table, refusals)
}

/// Correctness problems in the candidate's measurements, and the modules neither side prepares.
fn problems(files: &[String], base: &[Measured], cand: &[Measured]) -> (Vec<String>, Vec<String>) {
    let mut bad = Vec::new();
    let mut unmeasured = Vec::new();
    for (i, f) in files.iter().enumerate() {
        let berr = match &base[i] {
            Ok(b) => b["error"].as_str().map(str::to_owned),
            // The baseline couldn't be measured at all (not a refusal to prepare): the module
            // would silently drop out of the comparison.
            Err(e) => {
                bad.push(format!("{f}: the baseline's measurement failed: {e}"));
                continue;
            }
        };
        match &cand[i] {
            Err(e) => bad.push(format!("{f}: the candidate's measurement failed: {e}")),
            Ok(c) => {
                if let Some(e) = c["error"].as_str() {
                    match &berr {
                        Some(be) => unmeasured.push(format!("{f}: {be}")),
                        None => bad.push(format!(
                            "{f}: the baseline prepares it, the candidate doesn't: {e}"
                        )),
                    }
                    continue;
                }
                for r in c["runs"].as_array().into_iter().flatten() {
                    let call = r["call"].as_str().unwrap_or("?");
                    if r["refines"] != json!(true) {
                        bad.push(format!(
                            "{f} {call}: the candidate's run doesn't refine the source's: {} (source {}, candidate {})",
                            r["how"], r["source"], r["target"]
                        ));
                    }
                    if r["matches expectation"] != json!(true) {
                        bad.push(format!(
                            "{f} {call}: the source run doesn't print what the file expects ({} vs {}): the interpreter changed",
                            r["source"], r["expected"]
                        ));
                    }
                }
            }
        }
    }
    (bad, unmeasured)
}

/// The suites a gate test binary writes evidence for, and the key counting its random programs.
const GATE: &[(&str, &[(&str, &str)])] = &[
    ("opt", &[("opt_fixtures", ""), ("opt_fuzz", "programs")]),
    (
        "aarch64",
        &[("aarch64_fixtures", ""), ("aarch64_fuzz", "(programs)")],
    ),
    (
        "x86_64",
        &[("x86_64_fixtures", ""), ("x86_64_fuzz", "(programs)")],
    ),
];

struct Gate {
    checks: Vec<Value>,
    failed: bool,
    host_gaps: Vec<Value>,
}

impl Gate {
    fn check(&mut self, name: &str, ok: bool, seconds: f64, details: Vec<String>) {
        eprintln!(
            "[{}] gate: {name} ({seconds:.1}s)",
            if ok { "ok  " } else { "FAIL" }
        );
        if !ok {
            self.failed = true;
            for d in &details {
                eprintln!("       {d}");
            }
        }
        self.checks
            .push(json!({"name": name, "passed": ok, "seconds": seconds, "details": details}));
    }
}

fn gate(root: &Path, out: &Path, o: &Opts, run_id: &str) -> Gate {
    let mut g = Gate {
        checks: Vec::new(),
        failed: false,
        host_gaps: Vec::new(),
    };
    let logs = out.join("gate");
    std::fs::create_dir_all(&logs).unwrap();
    // The suites compare with the Lean reference, `spec/.lake/build/bin/fir-ref`.
    let start = Instant::now();
    let mut c = clean("lake", &root.join("spec"));
    c.arg("build");
    let (ok, tail) = logged(c, &logs.join("lake-build.log"));
    g.check(
        "lean: build (for fir-ref)",
        ok,
        start.elapsed().as_secs_f64(),
        if ok {
            vec![]
        } else {
            tail.lines().map(str::to_owned).collect()
        },
    );
    if !ok {
        return g;
    }
    let evidence = logs.join("evidence");
    let _ = std::fs::remove_dir_all(&evidence);
    let start = Instant::now();
    let mut c = clean("cargo", root);
    c.args([
        "test",
        "--release",
        "--locked",
        "--no-fail-fast",
        "-p",
        "fir",
    ]);
    for (t, _) in GATE {
        c.args(["--test", t]);
    }
    c.env("FIR_EVIDENCE", &evidence)
        .env("FIR_EVIDENCE_RUN", run_id)
        .env("FIR_REQUIRE_FULL", "1")
        .env("FIR_FUZZ", o.fuzz.to_string())
        .env("FIR_FUZZ_SEED", o.seed.to_string());
    let want_pipeline = match &o.cand {
        Pipe::Passes { spec, .. } => {
            c.env("FIR_PASSES", spec);
            spec.clone()
        }
        _ => "-O".to_owned(),
    };
    let log = logs.join("cargo-test.log");
    let (ok, tail) = logged(c, &log);
    let text = std::fs::read_to_string(&log).unwrap_or_default();
    let filtered: Vec<String> = text
        .lines()
        .filter(|l| l.starts_with("test result:") && filtered_out(l) > 0)
        .map(str::to_owned)
        .collect();
    let mut details: Vec<String> = if ok {
        vec![]
    } else {
        tail.lines().map(str::to_owned).collect()
    };
    details.extend(filtered.iter().map(|l| format!("filtered: {l}")));
    details.push(format!("log: {}", log.display()));
    g.check(
        &format!(
            "differential suites ({}) with the candidate pipeline",
            GATE.iter().map(|(t, _)| *t).collect::<Vec<_>>().join(", ")
        ),
        ok && filtered.is_empty(),
        start.elapsed().as_secs_f64(),
        details,
    );
    // What the suites say they did.
    let evs = load_evidence(&evidence);
    let mut bad = Vec::new();
    for (_, suites) in GATE {
        for (s, programs) in *suites {
            let Some(ev) = evs.get(*s) else {
                if let Some(why) = host_gap_reason(s) {
                    g.host_gaps.push(json!({"suite": s, "why": why}));
                } else {
                    bad.push(format!("{s}: no evidence"));
                }
                continue;
            };
            if ev["run"].as_str() != Some(run_id) {
                bad.push(format!("{s}: evidence from another run"));
            }
            if let Some(gap) = ev["facts"]["host gap"].as_str() {
                match host_gap_reason(s) {
                    Some(why) => g
                        .host_gaps
                        .push(json!({"suite": s, "why": why, "test says": gap})),
                    None => bad.push(format!(
                        "{s}: reports a host gap ({gap}) not declared for {}",
                        host()
                    )),
                }
                continue;
            }
            for sk in ev["skipped"].as_array().into_iter().flatten() {
                bad.push(format!("{s}: skipped {sk}"));
            }
            if ev["counts"]["failures"].as_u64().unwrap_or(0) > 0 {
                bad.push(format!("{s}: {} failures", ev["counts"]["failures"]));
            }
            let got = ev["facts"]["pipeline"].as_str().unwrap_or("(not recorded)");
            if got != want_pipeline {
                bad.push(format!(
                    "{s}: tested the pipeline {got:?}, not the candidate's {want_pipeline:?}"
                ));
            }
            if !programs.is_empty() {
                let n = ev["counts"][*programs].as_u64().unwrap_or(0);
                if n != o.fuzz {
                    bad.push(format!("{s}: {programs} is {n}, expected {}", o.fuzz));
                }
            }
        }
    }
    let n = evs.len();
    g.check(
        "evidence: every suite tested the candidate, fully",
        bad.is_empty(),
        0.0,
        if bad.is_empty() {
            vec![format!("{n} suites reported")]
        } else {
            bad
        },
    );
    g
}

pub fn main(root: &Path, args: &[String]) -> i32 {
    let o = match parse(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{e}\n{USAGE}");
            return 2;
        }
    };
    let start = Instant::now();
    let out = root.join("target/experiments").join(&o.name);
    let _ = std::fs::remove_dir_all(&out);
    std::fs::create_dir_all(&out).unwrap();
    let run_id = format!(
        "experiment-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos())
    );
    eprintln!(
        "cargo xtask experiment {}: candidate {} vs baseline {}{}",
        o.name,
        o.cand.show(),
        o.base.show(),
        o.base_rev
            .as_deref()
            .map(|r| format!(" at {r}"))
            .unwrap_or_default()
    );
    let mut errors: Vec<String> = Vec::new();
    let cand_id = identity(root);

    // The two `fir`s.
    // The candidate builds where cargo would put it (`cargo xtask mutate` sets its own).
    let cand_target = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("target"));
    let cand_fir = match build_fir(
        root,
        &cand_target,
        &out.join("build-candidate.log"),
        &out.join("fir-candidate"),
    ) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e}");
            return 1;
        }
    };
    let mut _worktree = None;
    let (base_fir, base_id) = match &o.base_rev {
        None => (cand_fir.clone(), cand_id.clone()),
        Some(rev) => {
            let path = out.join("baseline-tree");
            // A run that was killed leaves its worktree registered; its directory went with
            // `out` above, so pruning unregisters it.
            let _ = Command::new("git")
                .args(["worktree", "prune"])
                .current_dir(root)
                .output();
            let added = Command::new("git")
                .args(["worktree", "add", "--detach", "--quiet"])
                .arg(&path)
                .arg(rev)
                .current_dir(root)
                .output();
            match added {
                Ok(a) if a.status.success() => {}
                Ok(a) => {
                    eprintln!(
                        "can't check out {rev}: {}",
                        String::from_utf8_lossy(&a.stderr).trim()
                    );
                    return 1;
                }
                Err(e) => {
                    eprintln!("can't run git: {e}");
                    return 1;
                }
            }
            _worktree = Some(Worktree {
                root,
                path: path.clone(),
            });
            // A target directory of its own, kept between experiments so the next one is fast.
            let target = root.join("target/experiments/.baseline-target");
            match build_fir(
                &path,
                &target,
                &out.join("build-baseline.log"),
                &out.join("fir-baseline"),
            ) {
                Ok(p) => (p, identity(&path)),
                Err(e) => {
                    eprintln!("{e}");
                    return 1;
                }
            }
        }
    };

    // Measure.
    let files = corpus(root);
    let names: Vec<String> = files
        .iter()
        .map(|f| f.strip_prefix(root).unwrap_or(f).display().to_string())
        .collect();
    let t = Instant::now();
    let base = measure_all(&base_fir, root, &files, &o.base, o.jobs);
    let cand = measure_all(&cand_fir, root, &files, &o.cand, o.jobs);
    eprintln!(
        "measured {} modules with both in {:.1}s",
        files.len(),
        t.elapsed().as_secs_f64()
    );
    if base
        .iter()
        .all(|b| b.as_ref().is_err_and(|e| e.contains("usage")))
    {
        errors.push(format!(
            "the baseline's fir has no `measure` command: {} predates it",
            o.base_rev.as_deref().unwrap_or("the baseline")
        ));
    }
    drop(_worktree);
    for (dir, side) in [("baseline", &base), ("candidate", &cand)] {
        let d = out.join(dir);
        std::fs::create_dir_all(&d).unwrap();
        for (n, m) in names.iter().zip(side.iter()) {
            let text = match m {
                Ok(v) => serde_json::to_string_pretty(v).unwrap(),
                Err(e) => serde_json::to_string_pretty(&json!({"harness error": e})).unwrap(),
            };
            std::fs::write(d.join(format!("{}.json", n.replace('/', "__"))), text).unwrap();
        }
    }
    let (bad, unmeasured) = problems(&names, &base, &cand);
    let (metrics, refusals) = compare(&names, &base, &cand);
    for b in &bad {
        eprintln!("problem: {b}");
    }

    // Gate.
    let gate = if o.gate && errors.is_empty() {
        Some(gate(root, &out, &o, &run_id))
    } else {
        None
    };

    // What backs the candidate's passes.
    let passes: Vec<Value> = cand
        .iter()
        .find_map(|c| c.as_ref().ok())
        .map(|c| {
            c["pipeline"]["passes"]
                .as_array()
                .cloned()
                .unwrap_or_default()
        })
        .unwrap_or_default();
    let unproved: Vec<String> = passes
        .iter()
        .filter(|p| p["proved"] != json!(true))
        .filter_map(|p| p["name"].as_str().map(str::to_owned))
        .collect();

    // Verdict.
    let gate_failed = gate.as_ref().is_some_and(|g| g.failed);
    let total = |m: &str, k: &str| metrics[m][k].as_u64().unwrap_or(0);
    let worse: Vec<&str> = METRICS
        .iter()
        .copied()
        .filter(|m| total(m, "candidate") > total(m, "baseline"))
        .collect();
    let better: Vec<&str> = METRICS
        .iter()
        .copied()
        .filter(|m| total(m, "candidate") < total(m, "baseline"))
        .collect();
    let primary = METRICS[0];
    let verdict = if !errors.is_empty() || !bad.is_empty() || gate_failed {
        "REJECTED"
    } else if worse.is_empty() && better.is_empty() && refusals.is_empty() {
        "NO CHANGE"
    } else if worse.is_empty() && refusals.is_empty() {
        "IMPROVED"
    } else if better.is_empty() || total(primary, "candidate") > total(primary, "baseline") {
        "REGRESSED"
    } else {
        "MIXED"
    };
    let verdict = if gate.is_none() && verdict != "REJECTED" {
        format!("UNGATED {verdict} (measured only: --gate none)")
    } else {
        verdict.to_owned()
    };
    let eligibility = if unproved.is_empty() {
        "every pass in the candidate pipeline has a Lean refinement proof of its rewrite relation (the Rust code is tested, not proved)".to_owned()
    } else {
        format!(
            "not eligible for the default pipeline: {} unproved (experimental); this experiment is evidence, not proof",
            unproved.join(", ")
        )
    };
    let host_gaps: Vec<Value> = gate
        .as_ref()
        .map(|g| g.host_gaps.clone())
        .unwrap_or_default();
    let report = json!({
        "experiment": o.name,
        "verdict": verdict,
        "host": host(),
        "seconds": start.elapsed().as_secs_f64(),
        "candidate": {"pipeline": o.cand.show(), "tree": cand_id, "passes": passes},
        "baseline": {"pipeline": o.base.show(), "revision requested": o.base_rev, "tree": base_id},
        "eligibility": eligibility,
        "modules": names.len(),
        "unmeasured (neither side prepares)": unmeasured,
        "correctness problems": bad,
        "harness errors": errors,
        "new backend refusals": refusals,
        "metrics": metrics,
        "gate": gate.as_ref().map(|g| json!({"fuzz": o.fuzz, "seed": o.seed, "checks": g.checks})),
        "unverified on this host": host_gaps,
        "what this shows": "Deterministic counts on the tests/ corpus (interpreter-executed ops are a proxy for run time, not a timing), each candidate run checked against its source run in the interpreter, and, when gated, the differential suites with the candidate pipeline. Not a proof of the candidate; not a timing. `cargo xtask verify full` remains the required check.",
    });
    std::fs::write(
        out.join("report.json"),
        serde_json::to_string_pretty(&report).unwrap(),
    )
    .unwrap();
    std::fs::write(out.join("report.md"), markdown(&report)).unwrap();

    eprintln!("\n{}", summary(&report));
    eprintln!("report: {}", out.join("report.md").display());
    if verdict == "REJECTED" { 1 } else { 0 }
}

fn summary(r: &Value) -> String {
    let mut s = format!(
        "{}: {}\n",
        r["experiment"].as_str().unwrap_or(""),
        r["verdict"].as_str().unwrap_or("")
    );
    for &m in METRICS {
        let x = &r["metrics"][m];
        writeln!(
            s,
            "  {m:<15} {:>10} -> {:>10} ({}, {} better, {} worse, geomean {})",
            x["baseline"],
            x["candidate"],
            x["change"].as_str().unwrap_or(""),
            x["modules better"],
            x["modules worse"],
            x["geomean ratio"].as_str().unwrap_or("n/a")
        )
        .unwrap();
    }
    for k in [
        "correctness problems",
        "harness errors",
        "new backend refusals",
    ] {
        let v = r[k].as_array().map_or(0, Vec::len);
        if v > 0 {
            writeln!(s, "  {k}: {v}").unwrap();
        }
    }
    for g in r["unverified on this host"]
        .as_array()
        .into_iter()
        .flatten()
    {
        writeln!(
            s,
            "  unverified on this host: {} ({})",
            g["suite"].as_str().unwrap_or(""),
            g["why"].as_str().unwrap_or("")
        )
        .unwrap();
    }
    writeln!(s, "  {}", r["eligibility"].as_str().unwrap_or("")).unwrap();
    s
}

fn markdown(r: &Value) -> String {
    let mut md = format!(
        "# Experiment `{}`\n\n**{}** ({:.0} s on {})\n\n",
        r["experiment"].as_str().unwrap_or(""),
        r["verdict"].as_str().unwrap_or(""),
        r["seconds"].as_f64().unwrap_or(0.0),
        r["host"].as_str().unwrap_or("")
    );
    for side in ["candidate", "baseline"] {
        let t = &r[side]["tree"];
        writeln!(
            md,
            "- **{side}**: pipeline `{}`, revision `{}`{}",
            r[side]["pipeline"].as_str().unwrap_or(""),
            t["revision"].as_str().unwrap_or(""),
            if t["dirty"] == json!(true) {
                format!(
                    " plus uncommitted changes (diff hash `{}`)",
                    t["diff hash"].as_str().unwrap_or("")
                )
            } else {
                String::new()
            }
        )
        .unwrap();
    }
    writeln!(
        md,
        "- **eligibility**: {}\n",
        r["eligibility"].as_str().unwrap_or("")
    )
    .unwrap();
    md += "| Metric (lower is better) | Baseline | Candidate | Change | Better | Worse | Geomean ratio |\n|---|---:|---:|---:|---:|---:|---:|\n";
    for &m in METRICS {
        let x = &r["metrics"][m];
        writeln!(
            md,
            "| `{m}` | {} | {} | {} | {} | {} | {} |",
            x["baseline"],
            x["candidate"],
            x["change"].as_str().unwrap_or(""),
            x["modules better"],
            x["modules worse"],
            x["geomean ratio"].as_str().unwrap_or("n/a")
        )
        .unwrap();
    }
    let list = |md: &mut String, title: &str, v: &Value| {
        let items = v.as_array().cloned().unwrap_or_default();
        if !items.is_empty() {
            writeln!(md, "\n## {title}\n").unwrap();
            for i in items {
                writeln!(
                    md,
                    "- {}",
                    i.as_str().map_or_else(|| i.to_string(), str::to_owned)
                )
                .unwrap();
            }
        }
    };
    list(&mut md, "Correctness problems", &r["correctness problems"]);
    list(&mut md, "Harness errors", &r["harness errors"]);
    list(&mut md, "New backend refusals", &r["new backend refusals"]);
    md += "\n## Largest changes\n\n";
    for &m in METRICS {
        for k in ["largest regressions", "largest improvements"] {
            for c in r["metrics"][m][k].as_array().into_iter().flatten() {
                writeln!(
                    md,
                    "- `{m}` {}: `{}` {} -> {} ({})",
                    if k.contains("regress") {
                        "worse"
                    } else {
                        "better"
                    },
                    c["file"].as_str().unwrap_or(""),
                    c["baseline"],
                    c["candidate"],
                    c["change"].as_str().unwrap_or("")
                )
                .unwrap();
            }
        }
    }
    if let Some(checks) = r["gate"]["checks"].as_array() {
        writeln!(
            md,
            "\n## Gate ({} random programs, seed {})\n",
            r["gate"]["fuzz"], r["gate"]["seed"]
        )
        .unwrap();
        for c in checks {
            writeln!(
                md,
                "- {} {} ({:.1} s)",
                if c["passed"] == json!(true) {
                    "passed:"
                } else {
                    "**FAILED**:"
                },
                c["name"].as_str().unwrap_or(""),
                c["seconds"].as_f64().unwrap_or(0.0)
            )
            .unwrap();
            if c["passed"] != json!(true) {
                for d in c["details"].as_array().into_iter().flatten() {
                    writeln!(md, "  - `{}`", d.as_str().unwrap_or("").replace('`', "'")).unwrap();
                }
            }
        }
    } else {
        md += "\n## Gate\n\nNot run (`--gate none`): this experiment is measured only.\n";
    }
    list(
        &mut md,
        "Unverified on this host",
        &Value::Array(
            r["unverified on this host"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|g| {
                    json!(format!(
                        "{}: {}",
                        g["suite"].as_str().unwrap_or(""),
                        g["why"].as_str().unwrap_or("")
                    ))
                })
                .collect(),
        ),
    );
    list(
        &mut md,
        "Modules neither side prepares (not measured)",
        &r["unmeasured (neither side prepares)"],
    );
    writeln!(
        md,
        "\n## What this shows\n\n{}",
        r["what this shows"].as_str().unwrap_or("")
    )
    .unwrap();
    md
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(executed: u64, runs: u64, a64: u64) -> Measured {
        Ok(
            json!({"metrics": {"ops.executed": executed, "mem.executed": 0, "calls.executed": 0,
            "ops.static": 10, "runs measured": runs, "aarch64.insns": a64, "x86_64.insns": 5},
            "aarch64.refused": null, "x86_64.refused": null, "runs": []}),
        )
    }

    #[test]
    fn compares_only_like_runs_and_counts_both_ways() {
        let files = vec!["a".to_owned(), "b".to_owned(), "c".to_owned()];
        let base = vec![m(100, 1, 20), m(50, 2, 10), m(7, 1, 3)];
        // `c` measured a different number of runs: its dynamic counts don't compare.
        let cand = vec![m(80, 1, 22), m(50, 2, 10), m(1, 0, 3)];
        let (t, refusals) = compare(&files, &base, &cand);
        assert!(refusals.is_empty());
        assert_eq!(t["ops.executed"]["baseline"], json!(150));
        assert_eq!(t["ops.executed"]["candidate"], json!(130));
        assert_eq!(t["ops.executed"]["modules better"], json!(1));
        assert_eq!(t["aarch64.insns"]["modules worse"], json!(1));
        assert_eq!(
            t["aarch64.insns"]["largest regressions"][0]["file"],
            json!("a")
        );
    }

    #[test]
    fn a_run_that_does_not_refine_is_a_problem() {
        let files = vec!["a".to_owned(), "b".to_owned(), "c".to_owned()];
        let ok = m(1, 1, 1);
        let wrong = Ok(
            json!({"runs": [{"call": "@f()", "refines": false, "matches expectation": true,
            "how": "the ending", "source": "returned i32 1", "target": "returned i32 2"}], "metrics": {}}),
        );
        let refused = Ok(json!({"error": "preparing: nope"}));
        let base = vec![ok.clone(), ok.clone(), refused.clone()];
        let cand = vec![wrong, refused.clone(), refused];
        let (bad, unmeasured) = problems(&files, &base, &cand);
        assert_eq!(bad.len(), 2, "{bad:?}");
        assert!(bad[0].contains("doesn't refine"));
        assert!(bad[1].contains("the baseline prepares it"));
        assert_eq!(unmeasured.len(), 1);
        // A baseline that couldn't be measured at all is a problem, not a missing module.
        let base: Vec<Measured> = vec![Err("fir measure exited with 101".into())];
        let (bad, _) = problems(&files[..1], &base, &[m(1, 1, 1)]);
        assert!(
            bad[0].contains("the baseline's measurement failed"),
            "{bad:?}"
        );
    }

    #[test]
    fn options() {
        let a = |s: &str| s.split_whitespace().map(str::to_owned).collect::<Vec<_>>();
        let o = parse(&a("x --passes mem2reg,dce --experimental --gate none")).unwrap();
        assert_eq!(
            o.cand,
            Pipe::Passes {
                spec: "mem2reg,dce".into(),
                experimental: true
            }
        );
        assert!(!o.gate);
        assert!(parse(&a("../x")).is_err());
        assert!(parse(&a("x --experimental")).is_err());
        assert!(parse(&a("x --none")).is_err(), "no passes can't be gated");
        assert!(parse(&a("x --none --gate none")).is_ok());
    }
}
