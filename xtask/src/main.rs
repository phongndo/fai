//! `cargo xtask verify [fast|full]`: the repository's one required verification command.
//!
//! **full** builds the Lean development from the current sources, checks every generated file,
//! audits the proofs (`fir-audit` against the reviewed lock), checks formatting and lints, runs
//! every Rust test suite in debug and release with the Lean reference and the native AArch64
//! runner required (`FIR_REQUIRE_FULL=1`), runs the C API tests under AddressSanitizer, and then
//! reads what the tests recorded (`FIR_EVIDENCE`) to check that the work actually happened:
//! every required suite reported, none skipped anything, the counts are what was asked for, and
//! every op the components claim to support was exercised by a differential comparison. It
//! succeeds only if every check ran and passed; a missing tool, `FIR_REF=none`, an unavailable
//! emulator, or a suite that ran fewer comparisons than configured is a failure, not a skip.
//!
//! **fast** runs the same static checks and the debug tests with whatever is available, and
//! reports what it skipped. It never reports full verification.
//!
//! Both write `target/verify/report.json` and `target/verify/report.md` (revision, toolchains,
//! each check with its status, time, and counts, coverage, and the exclusions), and print a
//! summary. `--no-lean-clean` keeps Lean's build directory (by default `full` rebuilds it from
//! scratch); `--report-dir DIR` writes elsewhere.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use serde_json::{Value, json};

mod mutate;

/// How many random programs each fuzzing suite runs in a full verification (the suites'
/// defaults): set explicitly, so an inherited `FIR_FUZZ=1` can't shrink the run.
const FUZZ: &[(&str, &str)] = &[
    ("FIR_FUZZ", "200"),
    ("FIR_FUZZ_SEED", "1"),
    ("FIR_FUZZ_LEAN", "100"),
];

/// Variables that would weaken or redirect the checks; cleared for every child.
const CLEARED: &[&str] = &[
    "FIR_REF",
    "FIR_GEN_RUST",
    "FIR_GEN_BUILDER",
    "FIR_CC",
    "FIR_CAPI_SANITIZE",
    "FIR_FUZZ",
    "FIR_FUZZ_SEED",
    "FIR_FUZZ_LEAN",
    "FIR_PASSES",
    "FIR_ABI",
    "FIR_ABI_SEED",
    "FIR_SHOW_ADDRESS_DIFFS",
    "CBINDGEN",
];

/// Tools a full verification needs on `PATH`.
const TOOLS: &[&str] = &["cargo", "rustc", "lake", "clang", "cbindgen"];

/// Suites whose evidence a full verification needs, per test profile.
const SUITES: &[&str] = &[
    "generated_rust",
    "contracts",
    "dce_check",
    "dce_adversarial",
    "regcheck_adversarial",
    "aarch64_fixtures",
    "aarch64_fuzz",
    "aarch64_lfir",
    "run_fixtures",
    "interp_fuzz",
    "lower_fixtures",
    "opt_fixtures",
    "opt_fuzz",
    "text_fixtures",
    "capi_programs",
    "capi_e2e",
    "abi_torture",
];

/// Op constructors no differential test can exercise, and why. Every other constructor that a
/// component claims to support must appear in that component's comparisons.
const COVERAGE_EXCLUSIONS: &[(&str, &str, &str)] = &[];

#[derive(Clone, Debug)]
enum Status {
    Passed,
    Failed(String),
    Skipped(String),
}

struct Check {
    name: String,
    status: Status,
    seconds: f64,
    details: Vec<String>,
}

struct Verify {
    /// Stamped into every evidence file this run's tests write (`FIR_EVIDENCE_RUN`).
    run_id: String,
    root: PathBuf,
    full: bool,
    out_dir: PathBuf,
    checks: Vec<Check>,
    identity: BTreeMap<String, String>,
    coverage: Value,
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The first line a command prints, or `None` if it can't run.
fn version(cmd: &str, args: &[&str], dir: &Path) -> Option<String> {
    let out = Command::new(cmd)
        .args(args)
        .current_dir(dir)
        .output()
        .ok()?;
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    text.lines()
        .find(|l| !l.trim().is_empty())
        .map(|l| l.trim().to_owned())
}

fn tail(s: &str, n: usize) -> Vec<String> {
    let lines: Vec<&str> = s.lines().collect();
    lines[lines.len().saturating_sub(n)..]
        .iter()
        .map(|l| l.to_string())
        .collect()
}

impl Verify {
    fn record(&mut self, name: &str, start: Instant, status: Status, details: Vec<String>) {
        let mark = match &status {
            Status::Passed => "ok  ",
            Status::Failed(_) => "FAIL",
            Status::Skipped(_) => "skip",
        };
        let secs = start.elapsed().as_secs_f64();
        match &status {
            Status::Passed => eprintln!("[{mark}] {name} ({secs:.1}s)"),
            Status::Failed(m) | Status::Skipped(m) => {
                eprintln!("[{mark}] {name} ({secs:.1}s): {m}")
            }
        }
        self.checks.push(Check {
            name: name.to_owned(),
            status,
            seconds: secs,
            details,
        });
    }

    /// Run a command as a check: its output goes to `logs/NAME.log`, its tail into the report on
    /// failure. Returns its stdout when it succeeded.
    fn command(
        &mut self,
        name: &str,
        dir: &Path,
        cmd: &str,
        args: &[&str],
        env: &[(&str, String)],
    ) -> Option<String> {
        let start = Instant::now();
        let mut c = Command::new(cmd);
        c.args(args).current_dir(dir).stdin(Stdio::null());
        for v in CLEARED {
            c.env_remove(v);
        }
        // A test runner wrapper can pass `--skip` to the test binaries: none is inherited.
        for (k, _) in std::env::vars() {
            if k.starts_with("CARGO_TARGET_") && k.ends_with("_RUNNER") {
                c.env_remove(k);
            }
        }
        for (k, v) in env {
            c.env(k, v);
        }
        let out = match c.output() {
            Ok(o) => o,
            Err(e) => {
                self.record(
                    name,
                    start,
                    Status::Failed(format!("can't run {cmd}: {e}")),
                    vec![],
                );
                return None;
            }
        };
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        let logs = self.out_dir.join("logs");
        std::fs::create_dir_all(&logs).unwrap();
        let log = logs.join(format!("{}.log", name.replace([' ', '/'], "_")));
        std::fs::write(
            &log,
            format!(
                "$ {cmd} {}\n{stdout}\n--- stderr ---\n{stderr}",
                args.join(" ")
            ),
        )
        .unwrap();
        if out.status.success() {
            self.record(
                name,
                start,
                Status::Passed,
                vec![format!("log: {}", log.display())],
            );
            Some(stdout)
        } else {
            let mut details = tail(&stderr, 30);
            details.extend(tail(&stdout, 10));
            details.push(format!("log: {}", log.display()));
            self.record(
                name,
                start,
                Status::Failed(format!("{cmd} exited with {}", out.status)),
                details,
            );
            None
        }
    }

    fn skip(&mut self, name: &str, why: &str) {
        self.record(
            name,
            Instant::now(),
            Status::Skipped(why.to_owned()),
            vec![],
        );
    }

    fn fail(&mut self, name: &str, why: String, details: Vec<String>) {
        self.record(name, Instant::now(), Status::Failed(why), details);
    }

    fn pass(&mut self, name: &str, details: Vec<String>) {
        self.record(name, Instant::now(), Status::Passed, details);
    }

    fn identity(&mut self) {
        let root = self.root.clone();
        let spec = root.join("spec");
        let git = |args: &[&str]| version("git", args, &root).unwrap_or_default();
        let dirty = Command::new("git")
            .args(["status", "--porcelain"])
            .current_dir(&root)
            .output()
            .map(|o| !o.stdout.is_empty())
            .unwrap_or(true);
        let id = &mut self.identity;
        id.insert("revision".into(), git(&["rev-parse", "HEAD"]));
        id.insert("branch".into(), git(&["rev-parse", "--abbrev-ref", "HEAD"]));
        id.insert("dirty".into(), dirty.to_string());
        for (k, cmd, args, dir) in [
            ("rustc", "rustc", &["--version"][..], &root),
            ("cargo", "cargo", &["--version"][..], &root),
            ("clippy", "cargo", &["clippy", "--version"][..], &root),
            ("rustfmt", "rustfmt", &["--version"][..], &root),
            ("lean", "lake", &["env", "lean", "--version"][..], &spec),
            ("lake", "lake", &["--version"][..], &spec),
            ("clang", "clang", &["--version"][..], &root),
            ("cbindgen", "cbindgen", &["--version"][..], &root),
            ("qemu-aarch64", "qemu-aarch64", &["--version"][..], &root),
            (
                "aarch64-cc",
                "aarch64-unknown-linux-gnu-cc",
                &["--version"][..],
                &root,
            ),
        ] {
            id.insert(
                k.into(),
                version(cmd, args, dir).unwrap_or_else(|| "missing".into()),
            );
        }
        id.insert(
            "lean-toolchain".into(),
            std::fs::read_to_string(spec.join("lean-toolchain"))
                .unwrap_or_default()
                .trim()
                .to_owned(),
        );
        id.insert(
            "host".into(),
            format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
        );
        id.insert(
            "in-nix-shell".into(),
            std::env::var("IN_NIX_SHELL").unwrap_or_else(|_| "no".into()),
        );
    }

    fn tools(&mut self) -> bool {
        let mut missing: Vec<&str> = TOOLS.iter().copied().filter(|t| !on_path(t)).collect();
        let native = cfg!(target_arch = "aarch64");
        if !native {
            for t in ["aarch64-unknown-linux-gnu-cc", "qemu-aarch64"] {
                if !on_path(t) {
                    missing.push(t);
                }
            }
        }
        if missing.is_empty() {
            self.pass("required tools", vec![format!("native AArch64: {native}")]);
            true
        } else if self.full {
            self.fail(
                "required tools",
                format!("missing: {} (run inside `nix develop`)", missing.join(", ")),
                vec![],
            );
            false
        } else {
            self.skip(
                "required tools",
                &format!("missing: {}", missing.join(", ")),
            );
            false
        }
    }

    fn env_guard(&mut self) {
        let set: Vec<String> = CLEARED
            .iter()
            .filter_map(|v| std::env::var(v).ok().map(|x| format!("{v}={x}")))
            .collect();
        if set.is_empty() {
            self.pass("environment", vec![]);
        } else if self.full && set.iter().any(|s| s == "FIR_REF=none") {
            self.fail(
                "environment",
                "FIR_REF=none would disable the Lean reference comparisons; full verification refuses it".into(),
                set,
            );
        } else {
            self.pass(
                "environment",
                vec![format!("cleared for the checks: {}", set.join(" "))],
            );
        }
    }

    fn lean(&mut self, clean: bool) -> bool {
        let spec = self.root.join("spec");
        if clean {
            let _ = std::fs::remove_dir_all(spec.join(".lake/build"));
        }
        let name = if clean {
            "lean: build from scratch"
        } else {
            "lean: build"
        };
        self.command(name, &spec, "lake", &["build"], &[]).is_some()
    }

    fn generated(&mut self) {
        let spec = self.root.join("spec");
        let bin = spec.join(".lake/build/bin");
        let files: &[(&str, &[&str], &str)] = &[
            ("gen-rust", &[], "crates/fir/src/generated/ops.rs"),
            (
                "gen-rust",
                &["contracts"],
                "crates/fir/src/generated/contracts.rs",
            ),
            (
                "gen-rust",
                &["manifest"],
                "docs/assurance/op-contracts.json",
            ),
            (
                "gen-builder",
                &["rust"],
                "crates/fir/src/generated/builder.rs",
            ),
            (
                "gen-builder",
                &["capi"],
                "crates/fir-capi/src/generated/ops.rs",
            ),
        ];
        let start = Instant::now();
        let mut stale = Vec::new();
        let mut checked = Vec::new();
        for (tool, args, file) in files {
            let out = Command::new(bin.join(tool)).args(*args).output();
            match out {
                Ok(o) if o.status.success() => {
                    let have = std::fs::read(self.root.join(file)).unwrap_or_default();
                    if have != o.stdout {
                        stale.push(format!("{file}: stale; regenerate with `cd spec && lake exe {tool} {} > ../{file}`", args.join(" ")));
                    } else {
                        checked.push(format!("{file}: fresh"));
                    }
                }
                Ok(o) => stale.push(format!(
                    "{tool} {}: {}",
                    args.join(" "),
                    String::from_utf8_lossy(&o.stderr).trim()
                )),
                Err(e) => stale.push(format!("{tool}: {e}")),
            }
        }
        let header = Command::new("cbindgen")
            .args([
                "--config",
                "crates/fir-capi/cbindgen.toml",
                "--crate",
                "fir-capi",
                "--quiet",
            ])
            .current_dir(&self.root)
            .output();
        match header {
            Ok(o) if o.status.success() => {
                let have = std::fs::read(self.root.join("crates/fir-capi/include/fir.h"))
                    .unwrap_or_default();
                if have != o.stdout {
                    stale.push(
                        "crates/fir-capi/include/fir.h: stale; regenerate with cbindgen".into(),
                    );
                } else {
                    checked.push("crates/fir-capi/include/fir.h: fresh".into());
                }
            }
            Ok(o) => stale.push(format!(
                "cbindgen: {}",
                String::from_utf8_lossy(&o.stderr).trim()
            )),
            Err(e) => stale.push(format!("cbindgen: {e}")),
        }
        if stale.is_empty() {
            self.record("generated files", start, Status::Passed, checked);
        } else {
            self.record(
                "generated files",
                start,
                Status::Failed(format!("{} stale or failing", stale.len())),
                stale,
            );
        }
    }

    fn audit(&mut self) -> Value {
        let spec = self.root.join("spec");
        let report = self.out_dir.join("proofs.md");
        let start = Instant::now();
        // Through `lake exe`, which puts the compiled `Fir` modules on the search path.
        let out = Command::new("lake")
            .args(["exe", "fir-audit"])
            .args([
                "--json",
                "--lock",
                "../docs/assurance/proofs.lock.json",
                "--report",
            ])
            .arg(&report)
            .current_dir(&spec)
            .output();
        let out = match out {
            Ok(o) => o,
            Err(e) => {
                self.record(
                    "proof audit",
                    start,
                    Status::Failed(format!("can't run fir-audit: {e}")),
                    vec![],
                );
                return Value::Null;
            }
        };
        let j: Value = serde_json::from_slice(&out.stdout).unwrap_or(Value::Null);
        let errors: Vec<String> = j["errors"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|e| e.as_str().map(str::to_owned))
            .collect();
        let review: Vec<String> = j["review"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|e| e.as_str().map(str::to_owned))
            .collect();
        let claims = j["claims"].as_array().map_or(0, Vec::len);
        let mut details = vec![format!("{claims} claims; report: {}", report.display())];
        details.extend(errors.iter().map(|e| format!("error: {e}")));
        details.extend(review.iter().map(|r| format!("needs review: {r}")));
        // The committed report must be the one the audit writes now.
        let committed =
            std::fs::read(self.root.join("docs/assurance/proofs.md")).unwrap_or_default();
        let fresh = std::fs::read(&report).is_ok_and(|r| r == committed);
        if !fresh {
            details.push(
                "docs/assurance/proofs.md is stale: cd spec && lake exe fir-audit --update --report ../docs/assurance/proofs.md"
                    .into(),
            );
        }
        if out.status.success() && j["ok"] == json!(true) && claims > 0 && fresh {
            self.record("proof audit", start, Status::Passed, details);
        } else {
            let why = if j.is_null() {
                format!(
                    "fir-audit failed: {}",
                    String::from_utf8_lossy(&out.stderr).trim()
                )
            } else {
                format!(
                    "{} errors, {} changes needing review (after review: lake exe fir-audit --update)",
                    errors.len(),
                    review.len()
                )
            };
            self.record("proof audit", start, Status::Failed(why), details);
        }
        j
    }

    fn tests(&mut self, profile: &str, evidence: &Path) -> bool {
        let _ = std::fs::remove_dir_all(evidence);
        let mut env: Vec<(&str, String)> = vec![
            ("FIR_EVIDENCE", evidence.display().to_string()),
            ("FIR_EVIDENCE_RUN", self.run_id.clone()),
        ];
        if self.full {
            env.push(("FIR_REQUIRE_FULL", "1".into()));
            env.extend(FUZZ.iter().map(|(k, v)| (*k, (*v).to_owned())));
        }
        let mut args = vec!["test", "--workspace", "--no-fail-fast"];
        if profile == "release" {
            args.push("--release");
        }
        let root = self.root.clone();
        let name = format!("rust tests ({profile})");
        let out = self.command(&name, &root, "cargo", &args, &env);
        self.none_filtered(&name, out.as_deref())
    }

    /// A test run that filtered tests out ran less than it says: fail it.
    fn none_filtered(&mut self, name: &str, stdout: Option<&str>) -> bool {
        let Some(stdout) = stdout else { return false };
        let filtered: Vec<&str> = stdout
            .lines()
            .filter(|l| l.starts_with("test result:") && filtered_out(l) > 0)
            .collect();
        if filtered.is_empty() {
            return true;
        }
        self.fail(
            &format!("{name}: nothing filtered out"),
            format!(
                "{} test binaries ran with tests filtered out",
                filtered.len()
            ),
            filtered.iter().map(|l| l.to_string()).collect(),
        );
        false
    }

    fn asan(&mut self, evidence: &Path) -> bool {
        let _ = std::fs::remove_dir_all(evidence);
        let env = vec![
            ("FIR_EVIDENCE", evidence.display().to_string()),
            ("FIR_EVIDENCE_RUN", self.run_id.clone()),
            ("FIR_REQUIRE_FULL", "1".to_owned()),
            ("FIR_CAPI_SANITIZE", "address".to_owned()),
        ];
        let root = self.root.clone();
        let name = "C API under AddressSanitizer";
        let args = ["test", "-p", "fir-capi", "--test", "c"];
        let out = self.command(name, &root, "cargo", &args, &env);
        self.none_filtered(name, out.as_deref())
    }
}

/// How many tests a `test result:` line says were filtered out.
fn filtered_out(line: &str) -> u64 {
    line.split(';')
        .find_map(|part| part.trim().strip_suffix(" filtered out"))
        .and_then(|n| n.trim().parse().ok())
        .unwrap_or(0)
}

fn load_evidence(dir: &Path) -> BTreeMap<String, Value> {
    let mut out = BTreeMap::new();
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "json")
                && let Ok(text) = std::fs::read_to_string(&p)
                && let Ok(v) = serde_json::from_str::<Value>(&text)
            {
                out.insert(p.file_stem().unwrap().to_string_lossy().to_string(), v);
            }
        }
    }
    out
}

fn count(ev: &Value, key: &str) -> u64 {
    ev["counts"][key].as_u64().unwrap_or(0)
}

fn executed_ops(evs: &[&Value]) -> BTreeMap<String, u64> {
    let mut out = BTreeMap::new();
    for ev in evs {
        if let Some(m) = ev["executed ops"].as_object() {
            for (k, v) in m {
                if let Some(n) = v.as_u64().filter(|n| *n > 0) {
                    *out.entry(k.clone()).or_default() += n;
                }
            }
        }
    }
    out
}

/// Check one profile's evidence: every suite reported, nothing skipped, the counts are what was
/// configured, and claimed support was exercised. Returns the problems and the coverage table.
fn check_evidence(
    root: &Path,
    evs: &BTreeMap<String, Value>,
    sanitized: Option<&BTreeMap<String, Value>>,
    run: Option<&str>,
) -> (Vec<String>, Value) {
    let mut bad = Vec::new();
    // Evidence must come from this run: a file another run left can't stand in for a suite.
    if let Some(run) = run {
        for (name, ev) in evs.iter().chain(sanitized.into_iter().flatten()) {
            if ev["run"].as_str() != Some(run) {
                bad.push(format!("{name}: evidence from another run ({})", ev["run"]));
            }
        }
    }
    for s in SUITES {
        match evs.get(*s) {
            None => bad.push(format!(
                "{s}: no evidence (the suite didn't run, or didn't finish)"
            )),
            Some(ev) => {
                for sk in ev["skipped"].as_array().into_iter().flatten() {
                    bad.push(format!("{s}: skipped {sk}"));
                }
                if count(ev, "failures") > 0 {
                    bad.push(format!("{s}: {} failures", count(ev, "failures")));
                }
            }
        }
    }
    let get = |s: &str| evs.get(s).cloned().unwrap_or(Value::Null);
    let fuzz: u64 = FUZZ[0].1.parse().unwrap();
    // Counts that must be what was configured, or not zero.
    let need = |bad: &mut Vec<String>, suite: &str, key: &str, want: Option<u64>| {
        let n = count(&get(suite), key);
        match want {
            Some(w) if n != w => bad.push(format!("{suite}: {key} is {n}, expected {w}")),
            None if n == 0 => bad.push(format!("{suite}: {key} is 0")),
            _ => {}
        }
    };
    need(
        &mut bad,
        "generated_rust",
        "fresh: crates/fir/src/generated/contracts.rs",
        Some(1),
    );
    need(&mut bad, "contracts", "kinds", None);
    // The C ABI against the C compiler: the default number of random signatures, all agreeing,
    // with each register class exhausted, scalars after a composite on the stack, reordered
    // HFAs, non-C composites through `...` as twins, split pointers refused, and the interpreter
    // runs of MFIR and LFIR agreeing.
    need(&mut bad, "abi_torture", "signatures", Some(240));
    for key in [
        "gp_exhausted",
        "fp_exhausted",
        "scalar_after_stack_composite",
        "reordered_hfa",
        "variadic_twins",
        "refused_split_pointer",
        "interpreter_runs",
    ] {
        need(&mut bad, "abi_torture", key, None);
    }
    need(
        &mut bad,
        "dce_check",
        "functions accepted by Fir.Dce.checkFunc",
        None,
    );
    need(
        &mut bad,
        "dce_check",
        "modules with deletions accepted",
        None,
    );
    need(&mut bad, "dce_check", "random programs", Some(fuzz));
    need(
        &mut bad,
        "dce_check",
        "-O dce steps accepted by Fir.Dce.checkFunc",
        None,
    );
    need(
        &mut bad,
        "dce_adversarial",
        "refused by Fir.Dce.checkFunc",
        None,
    );
    need(
        &mut bad,
        "dce_adversarial",
        "refused by the Rust checker",
        None,
    );
    need(
        &mut bad,
        "regcheck_adversarial",
        "corruptions refused",
        None,
    );
    need(&mut bad, "aarch64_fixtures", "native matches", None);
    need(&mut bad, "aarch64_fixtures", "native -O matches", None);
    need(
        &mut bad,
        "aarch64_fixtures",
        "LFIR: fir-ref run agrees",
        None,
    );
    need(&mut bad, "aarch64_fuzz", "(programs)", Some(fuzz));
    need(&mut bad, "aarch64_fuzz", "native matches", None);
    need(
        &mut bad,
        "run_fixtures",
        "runs compared with fir-ref run",
        Some(count(&get("run_fixtures"), "run lines")),
    );
    need(&mut bad, "interp_fuzz", "programs", Some(fuzz));
    need(
        &mut bad,
        "interp_fuzz",
        "runs compared with fir-ref run",
        None,
    );
    need(
        &mut bad,
        "lower_fixtures",
        "lowering compared with fir-ref lower",
        Some(count(&get("lower_fixtures"), "modules lowered")),
    );
    need(&mut bad, "opt_fuzz", "programs", Some(fuzz));
    need(
        &mut bad,
        "capi_e2e",
        "native runs matching fir run",
        Some(14),
    );
    need(&mut bad, "capi_programs", "C programs passed", None);
    for pass in ["dse", "fwd", "copyprop", "dce"] {
        need(&mut bad, "opt_fuzz", &format!("pass {pass}: changes"), None);
    }
    if let Some(san) = sanitized {
        for s in ["capi_programs_address", "capi_e2e_address"] {
            match san.get(s) {
                None => bad.push(format!("{s}: no evidence from the AddressSanitizer run")),
                Some(ev) if ev["facts"]["sanitize"] != json!("address") => {
                    bad.push(format!("{s}: not built with -fsanitize=address"))
                }
                Some(_) => {}
            }
        }
        if count(
            san.get("capi_e2e_address").unwrap_or(&Value::Null),
            "native runs matching fir run",
        ) != 14
        {
            bad.push("capi_e2e_address: the native runs didn't all happen".into());
        }
    }
    if !get("aarch64_fixtures")["facts"]["native"].is_string() {
        bad.push("aarch64_fixtures: no native runner recorded".into());
    }
    // Coverage: every op constructor a component claims was exercised by its comparisons.
    let manifest: Value = std::fs::read_to_string(root.join("docs/assurance/op-contracts.json"))
        .ok()
        .and_then(|t| serde_json::from_str(&t).ok())
        .unwrap_or(Value::Null);
    let mut ctor_of = BTreeMap::new();
    for op in manifest["ops"].as_array().into_iter().flatten() {
        ctor_of.insert(
            op["name"].as_str().unwrap_or("").to_owned(),
            op["ctor"].as_str().unwrap_or("").to_owned(),
        );
    }
    if ctor_of.is_empty() {
        bad.push("docs/assurance/op-contracts.json: missing or empty".into());
    }
    let facts = get("contracts")["facts"].clone();
    let claimed = |comp: &str| -> BTreeSet<String> {
        facts
            .as_object()
            .into_iter()
            .flatten()
            .filter_map(|(k, _)| {
                k.strip_prefix(&format!("support {comp} "))
                    .map(str::to_owned)
            })
            .collect()
    };
    let native_ops = executed_ops(&[&get("aarch64_fixtures"), &get("aarch64_fuzz")]);
    let interp_ops = executed_ops(&[
        &get("run_fixtures"),
        &get("interp_fuzz"),
        &get("aarch64_lfir"),
        &get("aarch64_lfir_fuzz"),
    ]);
    let mut table = serde_json::Map::new();
    for (comp, exercised) in [("isel.aarch64", &native_ops), ("interp", &interp_ops)] {
        let kinds = claimed(comp);
        let ctors: BTreeSet<&str> = kinds
            .iter()
            .filter_map(|k| ctor_of.get(k).map(String::as_str))
            .collect();
        let seen_ctors: BTreeSet<&str> = exercised
            .keys()
            .filter_map(|k| ctor_of.get(k).map(String::as_str))
            .collect();
        let excluded: BTreeSet<&str> = COVERAGE_EXCLUSIONS
            .iter()
            .filter(|(c, _, _)| *c == comp)
            .map(|(_, k, _)| *k)
            .collect();
        let missing: Vec<&str> = ctors
            .iter()
            .copied()
            .filter(|c| !seen_ctors.contains(c) && !excluded.contains(c))
            .collect();
        let kinds_seen = kinds.iter().filter(|k| exercised.contains_key(*k)).count();
        for m in &missing {
            bad.push(format!("coverage: {comp} claims support for op {m}, but no differential comparison exercised it"));
        }
        table.insert(
            comp.to_owned(),
            json!({
                "constructors claimed": ctors.len(),
                "constructors exercised": ctors.intersection(&seen_ctors).count(),
                "constructors excluded": excluded.iter().collect::<Vec<_>>(),
                "kinds claimed (with modifiers)": kinds.len(),
                "kinds exercised (with modifiers)": kinds_seen,
                "missing": missing,
            }),
        );
    }
    (bad, Value::Object(table))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage: cargo xtask verify [fast|full] [--no-lean-clean] [--report-dir DIR]\n       cargo xtask mutate [NAME...]\n       cargo xtask evidence DIR";
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .unwrap();
    match args.first().map(String::as_str) {
        Some("verify") => {}
        Some("mutate") => std::process::exit(mutate::main(&root, &args[1..])),
        Some("evidence") if args.len() == 2 => {
            // Check one evidence directory as a full verification would (without the sanitizer
            // runs): used by `mutate` to show the check refuses incomplete evidence.
            let (bad, _) = check_evidence(&root, &load_evidence(Path::new(&args[1])), None, None);
            for b in &bad {
                eprintln!("{b}");
            }
            std::process::exit(if bad.is_empty() { 0 } else { 1 });
        }
        _ => {
            eprintln!("{usage}");
            std::process::exit(2);
        }
    }
    let full = match args.get(1).map(String::as_str) {
        Some("full") => true,
        Some("fast") | None => false,
        Some(m) if m.starts_with("--") => false,
        Some(m) => {
            eprintln!("unknown mode {m}\n{usage}");
            std::process::exit(2);
        }
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .unwrap();
    let out_dir = match args.iter().position(|a| a == "--report-dir") {
        Some(i) => PathBuf::from(&args[i + 1]),
        None => root.join("target/verify"),
    };
    std::fs::create_dir_all(&out_dir).unwrap();
    // Children run from different directories (spec/ and individual crates).
    let out_dir = out_dir.canonicalize().unwrap();
    let clean = full && !args.iter().any(|a| a == "--no-lean-clean");
    let mut v = Verify {
        run_id: format!(
            "{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos())
        ),
        root: root.clone(),
        full,
        out_dir: out_dir.clone(),
        checks: Vec::new(),
        identity: BTreeMap::new(),
        coverage: Value::Null,
    };
    let start = Instant::now();
    eprintln!("cargo xtask verify {}", if full { "full" } else { "fast" });
    v.identity();
    let tools = v.tools();
    v.env_guard();
    let lean = (tools || on_path("lake")) && v.lean(clean);
    if lean {
        v.generated();
    } else {
        v.skip("generated files", "the Lean build didn't complete");
    }
    let audit = if lean {
        v.audit()
    } else {
        v.skip("proof audit", "the Lean build didn't complete");
        Value::Null
    };
    v.command("rustfmt", &root, "cargo", &["fmt", "--all", "--check"], &[]);
    v.command(
        "clippy",
        &root,
        "cargo",
        &[
            "clippy",
            "--workspace",
            "--all-targets",
            "--",
            "-D",
            "warnings",
        ],
        &[],
    );
    let ev_debug = out_dir.join("evidence/debug");
    v.tests("debug", &ev_debug);
    let ev_release = out_dir.join("evidence/release");
    let ev_asan = out_dir.join("evidence/asan");
    if full {
        v.tests("release", &ev_release);
        v.asan(&ev_asan);
        let asan = load_evidence(&ev_asan);
        let mut coverage = serde_json::Map::new();
        for (profile, dir) in [("debug", &ev_debug), ("release", &ev_release)] {
            let evs = load_evidence(dir);
            let (bad, table) = check_evidence(
                &root,
                &evs,
                (profile == "debug").then_some(&asan),
                Some(&v.run_id),
            );
            coverage.insert(profile.to_owned(), table);
            let name = format!("evidence ({profile})");
            if bad.is_empty() {
                let n = evs.len();
                v.pass(
                    &name,
                    vec![format!(
                        "{n} suites reported; counts and coverage as required"
                    )],
                );
            } else {
                v.fail(&name, format!("{} problems", bad.len()), bad);
            }
        }
        v.coverage = Value::Object(coverage);
    } else {
        v.skip("rust tests (release)", "fast mode");
        v.skip("C API under AddressSanitizer", "fast mode");
        v.skip("evidence", "fast mode doesn't require complete evidence");
        let evs = load_evidence(&ev_debug);
        let (bad, table) = check_evidence(&root, &evs, None, Some(&v.run_id));
        v.coverage = json!({"debug (informational)": table, "problems (informational)": bad});
    }
    let failed = v
        .checks
        .iter()
        .filter(|c| matches!(c.status, Status::Failed(_)))
        .count();
    let skipped = v
        .checks
        .iter()
        .filter(|c| matches!(c.status, Status::Skipped(_)))
        .count();
    let verified = full && failed == 0 && skipped == 0;
    let verdict = if verified {
        "FULL VERIFICATION PASSED"
    } else if full {
        "FULL VERIFICATION FAILED"
    } else if failed == 0 {
        "PARTIAL (fast mode): not a full verification"
    } else {
        "PARTIAL (fast mode) FAILED"
    };
    // The report.
    let checks: Vec<Value> = v
        .checks
        .iter()
        .map(|c| {
            let (status, why) = match &c.status {
                Status::Passed => ("passed", String::new()),
                Status::Failed(m) => ("failed", m.clone()),
                Status::Skipped(m) => ("skipped", m.clone()),
            };
            json!({"name": c.name, "status": status, "why": why, "seconds": c.seconds, "details": c.details})
        })
        .collect();
    let report = json!({
        "mode": if full { "full" } else { "fast" },
        "verdict": verdict,
        "full_verification": verified,
        "seconds": start.elapsed().as_secs_f64(),
        "identity": v.identity,
        "checks": checks,
        "coverage": v.coverage,
        "coverage_exclusions": COVERAGE_EXCLUSIONS.iter().map(|(c, k, w)| json!({"component": c, "op": k, "why": w})).collect::<Vec<_>>(),
        "proof_audit": audit,
        "evidence": {
            "debug": load_evidence(&ev_debug),
            "release": load_evidence(&ev_release),
            "asan": load_evidence(&ev_asan),
        },
    });
    std::fs::write(
        out_dir.join("report.json"),
        serde_json::to_string_pretty(&report).unwrap(),
    )
    .unwrap();
    let mut md = format!(
        "# Verification report\n\n**{verdict}** ({:.0} s)\n\n",
        start.elapsed().as_secs_f64()
    );
    md += "| | |\n|---|---|\n";
    for (k, val) in &v.identity {
        writeln!(md, "| {k} | `{}` |", val.replace('|', "/")).unwrap();
    }
    md += "\n| Check | Status | Time | Notes |\n|---|---|---|---|\n";
    for c in &v.checks {
        let (s, why) = match &c.status {
            Status::Passed => ("passed", String::new()),
            Status::Failed(m) => ("**failed**", m.clone()),
            Status::Skipped(m) => ("skipped", m.clone()),
        };
        writeln!(
            md,
            "| {} | {s} | {:.1} s | {} |",
            c.name,
            c.seconds,
            why.replace('|', "/")
        )
        .unwrap();
    }
    md += "\n## Details\n\n";
    for c in &v.checks {
        if !c.details.is_empty() {
            writeln!(md, "### {}\n\n```\n{}\n```\n", c.name, c.details.join("\n")).unwrap();
        }
    }
    writeln!(
        md,
        "## Coverage\n\n```json\n{}\n```",
        serde_json::to_string_pretty(&v.coverage).unwrap()
    )
    .unwrap();
    std::fs::write(out_dir.join("report.md"), md).unwrap();
    eprintln!(
        "\n{verdict}: {} checks, {failed} failed, {skipped} skipped; report: {}",
        v.checks.len(),
        out_dir.join("report.md").display()
    );
    std::process::exit(if failed == 0 && (verified || !full) {
        0
    } else {
        1
    });
}

#[cfg(test)]
mod evidence_tests {
    use super::*;

    #[test]
    fn static_presence_and_zero_counts_do_not_satisfy_execution_coverage() {
        let static_only = json!({"ops": {"int.add.wrap": 100}});
        let no_dispatch = json!({"executed ops": {"int.add.wrap": 0}});
        assert!(executed_ops(&[&static_only, &no_dispatch]).is_empty());
        let evs = BTreeMap::from([
            (
                "contracts".to_owned(),
                json!({"facts": {"support interp int.add.wrap": "yes"}}),
            ),
            ("run_fixtures".to_owned(), static_only),
        ]);
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let (bad, _) = check_evidence(&root, &evs, None, None);
        assert!(
            bad.iter()
                .any(|e| e.starts_with("coverage: interp claims support for op "))
        );
        assert_eq!(
            executed_ops(&[&json!({"executed ops": {"int.add.wrap": 3}})])["int.add.wrap"],
            3
        );
    }

    /// Found in review: evidence a previous run left behind satisfied the check when the suite
    /// didn't run. Evidence from another run is refused, and so is a run with filtered tests.
    #[test]
    fn evidence_from_another_run_and_filtered_tests_are_refused() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let evs = BTreeMap::from([("capi_e2e".to_owned(), json!({"run": "old-run"}))]);
        let (bad, _) = check_evidence(&root, &evs, None, Some("this-run"));
        assert!(
            bad.iter()
                .any(|b| b.starts_with("capi_e2e: evidence from another run")),
            "{bad:?}"
        );
        assert_eq!(
            filtered_out(
                "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out; finished in 0.8s"
            ),
            2
        );
        assert_eq!(
            filtered_out(
                "test result: ok. 3 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.1s"
            ),
            0
        );
    }
}
