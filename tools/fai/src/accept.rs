//! `fai accept` and `fai status`: one verdict for a change, and which verdicts hold for the tree
//! as it is now.
//!
//! # `fai accept [--base REV]`
//!
//! The one command that says whether a change can land. It runs `fai verify full` and
//! `fai gate`, looks at which judging files the change touches (`judging.rs`), and, when the
//! change edits or removes test files that existed at the base, runs **the tests as they were
//! at the base against the changed code**, in a copy of the tree. Its last line and exit code:
//!
//! | Last line | Exit | Means |
//! |---|---:|---|
//! | `accept: PASS` | 0 | verified, no worse on Lua and SQLite, and it moved nothing that judges it |
//! | `accept: FAIL` | 1 | verification or the gate failed; the reasons are above |
//! | `accept: NOT JUDGED` | 2 | a part could not run (no baseline, no base to compare with) |
//! | `accept: PASS, JUDGING FILES CHANGED` | 3 | it passes, and it changed what judges it: the files are named, and merging is the owner's yes |
//!
//! A change moves what judges it when it edits a baseline or a checker, or when it fails the
//! tests as they were. Editing a test file is not that by itself: half of this repository's
//! commits do (`judging.rs`), mostly to add cases. A change that still passes the old tests
//! didn't need to move them; one that fails them did, and the failing tests are named.
//!
//! On a host with declared gaps (`HOST_GAPS`; the gate needs a host that isn't AArch64) the
//! best verdict is `accept: HOST PASS ON host`, exit 0, which is not a pass.
//!
//! # `fai status`
//!
//! `verify`, `gate`, `mutate`, and `accept` each leave a report under `target/`, and a report
//! says nothing about the tree once the tree has changed. Each therefore records the tree it
//! judged ([`crate::judging::tree_hash`]: every tracked and untracked file that isn't ignored,
//! so a tree with uncommitted edits has an identity too), at its start and at its end.
//! `fai status` compares that with the tree now and prints, per verdict, whether it is of this
//! tree, of another (`STALE`), or of none it can name.
//!
//! Exit codes: 0 when the last `verify full` and the last `gate` are both of this tree and both
//! passed; 1 otherwise. `mutate` is shown and doesn't decide: it checks the checkers, and a
//! change to the compiler alone doesn't make its last run wrong.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{Value, json};

use crate::judging::{self, Change, Judging, Kind};

/// Whether a report is about the tree as it is now.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Fresh {
    ThisTree,
    /// It judged another tree (its hash), or the tree changed while it ran.
    Stale(String),
    /// The report names no tree (it predates this check, or wasn't run through `fai`).
    Unbound,
    /// There is no report.
    Missing,
}

/// What a report's two tree hashes say about the tree `now`.
pub(crate) fn fresh(now: &str, at_start: Option<&str>, at_end: Option<&str>) -> Fresh {
    match (at_start, at_end) {
        (Some(a), Some(b)) if a == now && b == now => Fresh::ThisTree,
        (Some(a), Some(b)) if a != b => Fresh::Stale(format!(
            "the tree changed while it ran ({} to {})",
            short(a),
            short(b)
        )),
        (Some(a), _) if a != now => Fresh::Stale(format!("it judged tree {}", short(a))),
        // A start without an end: the run was cut short.
        (Some(_), None) => Fresh::Stale("the run didn't finish".to_owned()),
        _ => Fresh::Unbound,
    }
}

fn short(h: &str) -> &str {
    &h[..h.len().min(9)]
}

/// One verdict as `status` shows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Part {
    pub name: &'static str,
    pub verdict: String,
    pub passed: bool,
    pub fresh: Fresh,
}

impl Part {
    /// Passed, and of this tree.
    pub(crate) fn holds(&self) -> bool {
        self.passed && self.fresh == Fresh::ThisTree
    }

    fn line(&self) -> String {
        let fresh = match &self.fresh {
            Fresh::ThisTree => "of this tree".to_owned(),
            Fresh::Stale(why) => format!("STALE: {why}"),
            Fresh::Unbound => "STALE: the report names no tree".to_owned(),
            Fresh::Missing => "not run".to_owned(),
        };
        format!("{:<7} {:<44} {fresh}", self.name, self.verdict)
    }
}

fn read(path: &Path) -> Option<Value> {
    serde_json::from_slice(&std::fs::read(path).ok()?).ok()
}

fn missing(name: &'static str) -> Part {
    Part {
        name,
        verdict: "no report".to_owned(),
        passed: false,
        fresh: Fresh::Missing,
    }
}

/// The last `fai verify`: it passes here only as a full (or, on a host with declared gaps, a
/// host) verification.
pub(crate) fn verify_part(report: Option<&Value>, now: &str) -> Part {
    let Some(r) = report else {
        return missing("verify");
    };
    let id = &r["identity"];
    Part {
        name: "verify",
        verdict: r["verdict"]
            .as_str()
            .unwrap_or("?")
            .split(':')
            .next()
            .unwrap_or("?")
            .to_owned(),
        passed: r["host_verification"] == Value::Bool(true),
        fresh: fresh(now, id["tree"].as_str(), id["tree_at_end"].as_str()),
    }
}

/// The last `fai gate` into the default directory: only `PASS` passes (`PARTIAL` doesn't).
pub(crate) fn gate_part(report: Option<&Value>, now: &str) -> Part {
    let Some(r) = report else {
        return missing("gate");
    };
    let verdict = r["verdict"].as_str().unwrap_or("?");
    let configs = r["configs"].as_object().map_or(String::new(), |c| {
        c.keys().cloned().collect::<Vec<_>>().join(", ")
    });
    Part {
        name: "gate",
        verdict: format!("{verdict} ({configs})"),
        passed: verdict == "PASS",
        fresh: fresh(now, r["tree"].as_str(), r["tree_at_end"].as_str()),
    }
}

/// The last `fai mutate`: it passes when it ran every planted defect and caught each.
pub(crate) fn mutate_part(report: Option<&Value>, now: &str) -> Part {
    let Some(r) = report else {
        return missing("mutate");
    };
    let all = r["mutations"].as_array().map_or(0, Vec::len);
    let caught = r["mutations"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|m| m["passed"] == Value::Bool(true))
        .count();
    let subset = r["subset"] == Value::Bool(true);
    Part {
        name: "mutate",
        verdict: format!(
            "{caught} of {all} caught{}",
            if subset { " (a subset was run)" } else { "" }
        ),
        passed: !subset && all > 0 && caught == all,
        fresh: fresh(now, r["tree"].as_str(), r["tree"].as_str()),
    }
}

/// The three verdicts on disk, against the tree `now`.
pub(crate) fn parts(root: &Path, now: &str) -> [Part; 4] {
    [
        verify_part(read(&root.join("target/verify/report.json")).as_ref(), now),
        gate_part(
            read(&root.join("target/projbench/gate-report.json")).as_ref(),
            now,
        ),
        mutate_part(read(&root.join("target/mutate/report.json")).as_ref(), now),
        accept_part(read(&root.join("target/accept/report.json")).as_ref(), now),
    ]
}

/// `fai status`.
pub(crate) fn status(root: &Path) -> i32 {
    let now = match judging::tree_hash(root) {
        Ok(h) => h,
        Err(e) => {
            println!("status: UNKNOWN: this tree has no identity ({e})");
            return 1;
        }
    };
    let head = judging::git(root, &["rev-parse", "--short=9", "HEAD"]).unwrap_or_default();
    let dirty = judging::git(root, &["status", "--porcelain"]).is_ok_and(|s| !s.is_empty());
    println!(
        "tree    {} (HEAD {head}{})",
        short(&now),
        if dirty {
            ", with uncommitted changes"
        } else {
            ""
        }
    );
    let parts = parts(root, &now);
    for p in &parts {
        println!("{}", p.line());
    }
    println!("{}", judging::judging(root, None, None).line());
    let [verify, gate, _, _] = &parts;
    // The gate counts instructions under qemu, which an AArch64 host doesn't use.
    let gate_needed = !crate::host().starts_with("aarch64");
    let wrong: Vec<&str> = [(verify, true), (gate, gate_needed)]
        .iter()
        .filter(|(p, needed)| *needed && !p.holds())
        .map(|(p, _)| p.name)
        .collect();
    if wrong.is_empty() {
        println!("status: CURRENT: verify and the gate passed on this tree");
        0
    } else {
        let stale = [verify, gate]
            .iter()
            .any(|p| p.passed && p.fresh != Fresh::ThisTree);
        println!(
            "status: {}: {}",
            if stale { "STALE" } else { "NOT VERIFIED" },
            wrong.join(", ")
        );
        1
    }
}

/// How `fai verify full` ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verified {
    Full,
    /// Everything this host can run passed, and it has declared gaps.
    Host,
    Failed,
}

/// How `fai gate` ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Gated {
    Pass,
    Fail,
    /// It could not judge the tree (no baseline).
    NotRun,
    /// This host can't run it (it counts instructions under qemu, off AArch64).
    HostGap,
}

/// What running the base's tests against the changed code found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OldTests {
    /// The change edits or removes no test file that existed at the base.
    NotNeeded,
    /// The tests as they were still pass: these edited files didn't need to change.
    Passed(Vec<String>),
    /// The change fails the tests as they were: the files, and what failed.
    Failed {
        files: Vec<String>,
        failures: Vec<String>,
    },
    /// They could not be run, and why.
    NotRun(String),
}

/// The test files a change edited or removed that existed at the base.
pub(crate) fn moved_tests(changes: &[Change]) -> Vec<String> {
    changes
        .iter()
        .filter(|c| c.kind == Kind::Test && c.status != 'A')
        .map(|c| c.path.clone())
        .collect()
}

/// The `cargo test` arguments that run the tests in `files`: the suites by name when every
/// file is one of `fir`'s integration tests (`tests/rust/NAME.rs`), and the whole workspace
/// otherwise (a fixture or a shared helper is read by many suites).
pub(crate) fn old_test_commands(files: &[String]) -> Vec<Vec<String>> {
    let suites: Option<Vec<&str>> = files
        .iter()
        .map(|f| {
            f.strip_prefix("tests/rust/")
                .and_then(|n| n.strip_suffix(".rs"))
                .filter(|n| !n.contains('/'))
        })
        .collect();
    let args = |a: &[&str]| a.iter().map(|x| (*x).to_owned()).collect::<Vec<_>>();
    match suites {
        Some(names) if !names.is_empty() => names
            .iter()
            .map(|n| args(&["test", "-p", "fir", "--test", n, "--no-fail-fast"]))
            .collect(),
        _ => vec![args(&["test", "--workspace", "--no-fail-fast"])],
    }
}

/// What failed in `cargo test`'s output: the tests, and the first lines of a build error.
pub(crate) fn test_failures(output: &str) -> Vec<String> {
    let mut out: Vec<String> = output
        .lines()
        .filter_map(|l| l.strip_prefix("test ")?.strip_suffix(" ... FAILED"))
        .map(|t| format!("test {t} failed"))
        .collect();
    // The compiler's errors, not cargo's summary that a test target failed.
    let errors: Vec<&str> = output
        .lines()
        .filter(|l| l.starts_with("error[") || l.starts_with("error: could not compile"))
        .take(3)
        .collect();
    out.extend(errors.iter().map(|e| format!("it doesn't build: {e}")));
    out.sort();
    out.dedup();
    out
}

/// The verdict: its exit code, its last line, and the lines above it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Decision {
    pub code: i32,
    pub line: String,
    pub notes: Vec<String>,
}

/// One verdict from the parts. A failure outranks a part that could not run, which outranks
/// judging files that moved, which outranks a pass.
pub(crate) fn decide(
    verified: Verified,
    gated: Gated,
    judging: &Judging,
    old: &OldTests,
    host: &str,
) -> Decision {
    let mut notes = Vec::new();
    let mut failed = Vec::new();
    if verified == Verified::Failed {
        failed.push("verify full failed");
    }
    if gated == Gated::Fail {
        failed.push("the gate failed");
    }
    if !failed.is_empty() {
        return Decision {
            code: 1,
            line: format!("accept: FAIL: {}", failed.join(", and ")),
            notes,
        };
    }
    let mut unjudged = Vec::new();
    if gated == Gated::NotRun {
        unjudged.push("the gate could not run".to_owned());
    }
    if let Judging::NoBase(why) = judging {
        unjudged.push(format!(
            "there is no base to compare the judging files with ({why})"
        ));
    }
    if let OldTests::NotRun(why) = old {
        unjudged.push(format!("the tests as they were could not be run ({why})"));
    }
    if !unjudged.is_empty() {
        return Decision {
            code: 2,
            line: format!("accept: NOT JUDGED: {}", unjudged.join("; ")),
            notes,
        };
    }
    // What the change moved of what judges it.
    let mut moved: BTreeSet<String> = judging
        .changes()
        .iter()
        .filter(|c| c.kind != Kind::Test)
        .map(|c| c.path.clone())
        .collect();
    match old {
        OldTests::Failed { files, failures } => {
            notes.push(format!(
                "the change fails the tests as they were at the base ({}):",
                files.join(", ")
            ));
            notes.extend(failures.iter().map(|f| format!("  {f}")));
            moved.extend(files.iter().cloned());
        }
        OldTests::Passed(files) => notes.push(format!(
            "{} test files were edited, and the tests as they were still pass: {}",
            files.len(),
            files.join(", ")
        )),
        _ => {}
    }
    let pass = if verified == Verified::Host || gated == Gated::HostGap {
        format!("HOST PASS ON {host}")
    } else {
        "PASS".to_owned()
    };
    if !moved.is_empty() {
        let files: Vec<String> = moved.into_iter().collect();
        return Decision {
            code: 3,
            line: format!(
                "accept: {pass}, JUDGING FILES CHANGED ({}): {}",
                files.len(),
                files.join(", ")
            ),
            notes,
        };
    }
    Decision {
        code: 0,
        line: if pass == "PASS" {
            "accept: PASS".to_owned()
        } else {
            format!("accept: {pass}: every check this host can run passed, which is not a pass")
        },
        notes,
    }
}

/// Make `tree` the files of `root` as they are now (tracked, and untracked ones that aren't
/// ignored), writing only what differs so that a later build there rebuilds only what changed.
fn sync_copy(root: &Path, tree: &Path) -> Result<(), String> {
    let list = Command::new("git")
        .args([
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ])
        .current_dir(root)
        .output()
        .map_err(|e| format!("can't run git: {e}"))?;
    if !list.status.success() {
        return Err("git ls-files failed".to_owned());
    }
    let mut keep: BTreeSet<PathBuf> = BTreeSet::new();
    for f in list.stdout.split(|&b| b == 0).filter(|f| !f.is_empty()) {
        let rel = PathBuf::from(String::from_utf8_lossy(f).into_owned());
        let src = root.join(&rel);
        if !src.is_file() {
            continue;
        }
        let dst = tree.join(&rel);
        let new = std::fs::read(&src).map_err(|e| format!("{}: {e}", src.display()))?;
        if std::fs::read(&dst).ok().as_deref() != Some(&new[..]) {
            std::fs::create_dir_all(dst.parent().unwrap()).map_err(|e| e.to_string())?;
            std::fs::copy(&src, &dst).map_err(|e| format!("{}: {e}", dst.display()))?;
        }
        keep.insert(rel);
    }
    // Files the copy has and the tree no longer does.
    let mut dirs = vec![tree.to_path_buf()];
    while let Some(d) = dirs.pop() {
        for e in std::fs::read_dir(&d).map_err(|e| e.to_string())?.flatten() {
            let p = e.path();
            let Ok(kind) = e.file_type() else { continue };
            if kind.is_dir() {
                dirs.push(p);
            } else if kind.is_file()
                && let Ok(rel) = p.strip_prefix(tree)
                && !keep.contains(rel)
            {
                let _ = std::fs::remove_file(&p);
            }
        }
    }
    // The Lean reference the tests compare with is the working tree's build.
    let lake = tree.join("spec/.lake");
    if std::fs::symlink_metadata(&lake).is_err() {
        std::os::unix::fs::symlink(root.join("spec/.lake"), &lake).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Run the tests of `files` as they were at `base` against the tree as it is now: in a copy
/// (`target/accept/tree`, with its own Cargo target directory), put the base's version of each
/// file back, and run the suites that read them.
pub(crate) fn run_old_tests(root: &Path, base: &str, files: &[String]) -> OldTests {
    if files.is_empty() {
        return OldTests::NotNeeded;
    }
    let dir = root.join("target/accept");
    let tree = dir.join("tree");
    if let Err(e) = std::fs::create_dir_all(&tree).map_err(|e| e.to_string()) {
        return OldTests::NotRun(e);
    }
    if let Err(e) = sync_copy(root, &tree) {
        return OldTests::NotRun(e);
    }
    for f in files {
        let old = Command::new("git")
            .args(["show", &format!("{base}:{f}")])
            .current_dir(root)
            .output();
        match old {
            Ok(o) if o.status.success() => {
                let dst = tree.join(f);
                let _ = std::fs::create_dir_all(dst.parent().unwrap());
                if let Err(e) = std::fs::write(&dst, &o.stdout) {
                    return OldTests::NotRun(format!("{}: {e}", dst.display()));
                }
            }
            _ => return OldTests::NotRun(format!("git can't show {base}:{f}")),
        }
    }
    let mut failures = Vec::new();
    for args in old_test_commands(files) {
        eprintln!("accept: the tests as they were: cargo {}", args.join(" "));
        let mut c = Command::new("cargo");
        c.args(&args)
            .current_dir(&tree)
            .env("CARGO_TARGET_DIR", dir.join("target"))
            .stdin(Stdio::null());
        for v in crate::CLEARED {
            c.env_remove(v);
        }
        for v in ["FIR_REQUIRE_FULL", "FIR_EVIDENCE", "FIR_EVIDENCE_RUN"] {
            c.env_remove(v);
        }
        // The old tests look for what the change broke, not for coverage.
        c.env("FIR_FUZZ", "40");
        let out = match c.output() {
            Ok(o) => o,
            Err(e) => return OldTests::NotRun(format!("can't run cargo: {e}")),
        };
        if !out.status.success() {
            let text = format!(
                "{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            let found = test_failures(&text);
            if found.is_empty() {
                failures.push(format!("cargo {} failed", args.join(" ")));
            }
            failures.extend(found);
        }
    }
    if failures.is_empty() {
        OldTests::Passed(files.to_vec())
    } else {
        OldTests::Failed {
            files: files.to_vec(),
            failures,
        }
    }
}

/// Run this binary's `fai ARGS` and give its exit code.
fn fai(root: &Path, args: &[&str]) -> i32 {
    let exe = std::env::current_exe().unwrap_or_else(|_| PathBuf::from("fai"));
    Command::new(exe)
        .args(args)
        .current_dir(root)
        .status()
        .ok()
        .and_then(|s| s.code())
        .unwrap_or(1)
}

/// `fai accept [--base REV] [--no-lean-clean]`.
pub(crate) fn accept(root: &Path, rest: &[String]) -> i32 {
    let (mut base, mut lean_clean) = (None, true);
    let mut it = rest.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--base" => base = it.next().map(String::as_str),
            "--no-lean-clean" => lean_clean = false,
            _ => {
                eprintln!("usage: fai accept [--base REV] [--no-lean-clean]");
                return 2;
            }
        }
    }
    let tree = judging::tree_hash(root).unwrap_or_default();
    let host = crate::host();
    eprintln!("accept: fai verify full");
    let mut verify_args = vec!["verify", "full"];
    if !lean_clean {
        verify_args.push("--no-lean-clean");
    }
    let verify_code = fai(root, &verify_args);
    let report = read(&root.join("target/verify/report.json"));
    let ours = report
        .as_ref()
        .is_some_and(|r| r["identity"]["tree"] == json!(tree));
    let flag = |k: &str| report.as_ref().is_some_and(|r| r[k] == json!(true));
    let verified = if verify_code == 0 && ours && flag("full_verification") {
        Verified::Full
    } else if verify_code == 0 && ours && flag("host_verification") {
        Verified::Host
    } else {
        Verified::Failed
    };
    let gated = if host.starts_with("aarch64") {
        eprintln!("accept: the gate can't run on {host} (it counts instructions under qemu)");
        Gated::HostGap
    } else {
        eprintln!("accept: fai gate");
        match fai(root, &["gate"]) {
            0 => Gated::Pass,
            2 => Gated::NotRun,
            _ => Gated::Fail,
        }
    };
    let judging = judging::judging(root, base, None);
    let old = match &judging {
        Judging::Against { base, changes, .. } => run_old_tests(root, base, &moved_tests(changes)),
        Judging::NoBase(_) => OldTests::NotNeeded,
    };
    let d = decide(verified, gated, &judging, &old, &host);
    let tree_at_end = judging::tree_hash(root).unwrap_or_default();
    let dir = root.join("target/accept");
    let _ = std::fs::create_dir_all(&dir);
    let report = json!({
        "tree": tree,
        "tree_at_end": tree_at_end,
        "exit_code": d.code,
        "verdict": d.line,
        "notes": d.notes,
        "verify": format!("{verified:?}"),
        "gate": format!("{gated:?}"),
        "old_tests": format!("{old:?}"),
        "judging": judging.json(),
        "host": host,
    });
    let _ = std::fs::write(
        dir.join("report.json"),
        serde_json::to_string_pretty(&report).unwrap(),
    );
    println!("{}", judging.listing());
    for n in &d.notes {
        println!("{n}");
    }
    if tree_at_end != tree {
        println!("accept: the tree changed while this ran: the verdict is of no tree");
    }
    println!("{}", d.line);
    d.code
}

/// The last `fai accept`.
pub(crate) fn accept_part(report: Option<&Value>, now: &str) -> Part {
    let Some(r) = report else {
        return missing("accept");
    };
    Part {
        name: "accept",
        verdict: r["verdict"]
            .as_str()
            .unwrap_or("?")
            .trim_start_matches("accept: ")
            .chars()
            .take(40)
            .collect(),
        passed: r["exit_code"] == json!(0) || r["exit_code"] == json!(3),
        fresh: fresh(now, r["tree"].as_str(), r["tree_at_end"].as_str()),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn a_report_is_of_this_tree_only_when_both_hashes_are_the_trees() {
        assert_eq!(fresh("aa", Some("aa"), Some("aa")), Fresh::ThisTree);
        assert!(matches!(
            fresh("bb", Some("aa"), Some("aa")),
            Fresh::Stale(_)
        ));
        // The tree changed during the run, even if it is back where the run began.
        assert!(matches!(
            fresh("aa", Some("aa"), Some("bb")),
            Fresh::Stale(_)
        ));
        assert!(matches!(fresh("aa", Some("aa"), None), Fresh::Stale(_)));
        assert_eq!(fresh("aa", None, None), Fresh::Unbound);
        assert_eq!(fresh("aa", None, Some("aa")), Fresh::Unbound);
    }

    #[test]
    fn only_a_full_verification_and_a_whole_gate_pass() {
        let v = |verdict: &str, host: bool| {
            json!({"verdict": verdict, "host_verification": host,
                   "identity": {"tree": "aa", "tree_at_end": "aa"}})
        };
        assert!(verify_part(Some(&v("FULL VERIFICATION PASSED", true)), "aa").holds());
        // Fast mode never verifies, whatever it found.
        assert!(
            !verify_part(
                Some(&v("PARTIAL (fast mode): not a full verification", false)),
                "aa"
            )
            .holds()
        );
        // A pass of another tree doesn't hold.
        assert!(!verify_part(Some(&v("FULL VERIFICATION PASSED", true)), "bb").holds());
        assert!(!verify_part(None, "aa").holds());
        let g = |verdict: &str| json!({"verdict": verdict, "configs": {"fcc-O": {}}, "tree": "aa", "tree_at_end": "aa"});
        assert!(gate_part(Some(&g("PASS")), "aa").holds());
        assert!(!gate_part(Some(&g("PARTIAL")), "aa").holds());
        assert!(!gate_part(Some(&g("FAIL")), "aa").holds());
        // A report written before reports named their tree (or not through `fai`).
        let old = json!({"verdict": "PASS", "configs": {}});
        assert_eq!(gate_part(Some(&old), "aa").fresh, Fresh::Unbound);
        assert!(!gate_part(Some(&old), "aa").holds());
    }

    fn against(changes: &[(char, &str)]) -> Judging {
        Judging::Against {
            base: "base".into(),
            changes: changes
                .iter()
                .map(|(status, path)| Change {
                    status: *status,
                    path: (*path).into(),
                    kind: judging::classify(path).unwrap(),
                    lines: None,
                })
                .collect(),
            added_tests: 0,
        }
    }

    #[test]
    fn the_four_verdicts_and_their_order() {
        let none = against(&[]);
        let host = "x86_64-linux";
        let d = |v, g, j: &Judging, o: &OldTests| decide(v, g, j, o, host);
        // 0: verified, gated, and nothing that judges was moved.
        let pass = d(Verified::Full, Gated::Pass, &none, &OldTests::NotNeeded);
        assert_eq!((pass.code, pass.line.as_str()), (0, "accept: PASS"));
        // 1: either part failing fails, whatever else is true.
        for (v, g) in [
            (Verified::Failed, Gated::Pass),
            (Verified::Full, Gated::Fail),
            (Verified::Failed, Gated::NotRun),
        ] {
            let f = d(
                v,
                g,
                &Judging::NoBase("no git".into()),
                &OldTests::NotNeeded,
            );
            assert_eq!(f.code, 1, "{v:?} {g:?}");
            assert!(f.line.starts_with("accept: FAIL"), "{}", f.line);
        }
        // 2: a part that could not run is not a pass.
        let no_baseline = d(Verified::Full, Gated::NotRun, &none, &OldTests::NotNeeded);
        assert_eq!(no_baseline.code, 2);
        assert!(no_baseline.line.starts_with("accept: NOT JUDGED"));
        let no_base = d(
            Verified::Full,
            Gated::Pass,
            &Judging::NoBase("no git".into()),
            &OldTests::NotNeeded,
        );
        assert_eq!(no_base.code, 2);
        let unrun = OldTests::NotRun("no cargo".into());
        assert_eq!(d(Verified::Full, Gated::Pass, &none, &unrun).code, 2);
        // 3: a baseline or a checker changed.
        let baseline = against(&[('M', "benchmarks/projects/gate.json")]);
        let moved = d(Verified::Full, Gated::Pass, &baseline, &OldTests::NotNeeded);
        assert_eq!(moved.code, 3);
        assert_eq!(
            moved.line,
            "accept: PASS, JUDGING FILES CHANGED (1): benchmarks/projects/gate.json"
        );
        // And a moved judge doesn't hide a failure or a part that didn't run.
        assert_eq!(
            d(Verified::Full, Gated::Fail, &baseline, &OldTests::NotNeeded).code,
            1
        );
        assert_eq!(
            d(
                Verified::Full,
                Gated::NotRun,
                &baseline,
                &OldTests::NotNeeded
            )
            .code,
            2
        );
    }

    #[test]
    fn an_edited_test_counts_only_when_the_old_tests_fail() {
        let edited = against(&[('M', "tests/rust/regcheck.rs")]);
        let files = vec!["tests/rust/regcheck.rs".to_owned()];
        assert_eq!(
            moved_tests(against(&[('A', "tests/rust/new.rs")]).changes()),
            Vec::<String>::new()
        );
        assert_eq!(moved_tests(edited.changes()), files);
        let host = "x86_64-linux";
        // The old tests still pass: the edit is noted, and the verdict is a plain pass.
        let ok = decide(
            Verified::Full,
            Gated::Pass,
            &edited,
            &OldTests::Passed(files.clone()),
            host,
        );
        assert_eq!((ok.code, ok.line.as_str()), (0, "accept: PASS"));
        assert!(ok.notes[0].contains("still pass"));
        // The change fails them: named, with what failed.
        let failed = OldTests::Failed {
            files: files.clone(),
            failures: vec!["test honest_allocation_is_accepted failed".into()],
        };
        let moved = decide(Verified::Full, Gated::Pass, &edited, &failed, host);
        assert_eq!(moved.code, 3);
        assert_eq!(
            moved.line,
            "accept: PASS, JUDGING FILES CHANGED (1): tests/rust/regcheck.rs"
        );
        assert!(
            moved
                .notes
                .iter()
                .any(|n| n.contains("honest_allocation_is_accepted"))
        );
    }

    #[test]
    fn a_host_with_gaps_never_passes() {
        let none = against(&[]);
        for (v, g) in [
            (Verified::Host, Gated::HostGap),
            (Verified::Full, Gated::HostGap),
        ] {
            let d = decide(v, g, &none, &OldTests::NotNeeded, "aarch64-macos");
            assert_eq!(d.code, 0);
            assert!(
                d.line.starts_with("accept: HOST PASS ON aarch64-macos"),
                "{}",
                d.line
            );
            assert_ne!(d.line, "accept: PASS");
        }
    }

    #[test]
    fn old_tests_run_by_suite_or_all_together() {
        let s = |v: &[&str]| v.iter().map(|x| (*x).to_owned()).collect::<Vec<_>>();
        assert_eq!(
            old_test_commands(&s(&["tests/rust/regcheck.rs", "tests/rust/debug_lines.rs"])),
            vec![
                s(&["test", "-p", "fir", "--test", "regcheck", "--no-fail-fast"]),
                s(&[
                    "test",
                    "-p",
                    "fir",
                    "--test",
                    "debug_lines",
                    "--no-fail-fast"
                ]),
            ]
        );
        // A fixture, or a helper every suite uses, is read by many suites.
        for f in [
            "tests/fir0/holes.fir",
            "tests/rust/common/mod.rs",
            "sdk/c/tests/fcc.rs",
        ] {
            assert_eq!(
                old_test_commands(&s(&["tests/rust/regcheck.rs", f])),
                vec![s(&["test", "--workspace", "--no-fail-fast"])],
                "{f}"
            );
        }
        let out = "test a::b ... ok\ntest honest ... FAILED\nerror[E0425]: cannot find value\n\
                   error: test failed, to rerun pass `-p fir --test regcheck`\nerror: 1 target failed:\n";
        assert_eq!(
            test_failures(out),
            [
                "it doesn't build: error[E0425]: cannot find value",
                "test honest failed"
            ]
        );
    }

    #[test]
    fn mutate_passes_only_when_everything_ran_and_was_caught() {
        let m = |passed: &[bool], subset: bool| {
            json!({"tree": "aa", "subset": subset,
                   "mutations": passed.iter().map(|p| json!({"passed": p})).collect::<Vec<_>>()})
        };
        assert!(mutate_part(Some(&m(&[true, true], false)), "aa").holds());
        assert!(!mutate_part(Some(&m(&[true, false], false)), "aa").holds());
        assert!(!mutate_part(Some(&m(&[true], true)), "aa").holds());
        assert!(!mutate_part(Some(&m(&[], false)), "aa").holds());
    }
}
