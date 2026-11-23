//! `fai judging [--base REV] [--head REV] [--json]`: the judging files a change touches, and
//! the identity of a tree.
//!
//! A **judging file** decides whether other changes pass: a test with its fixtures and expected
//! outputs, a baseline or a lock, or a checker. A change that edits one has moved what judges
//! it. That can be right (a test that relied on an accident of the old code), and it is never
//! the change's own call: the verdict names every such file, and merging is the owner's yes.
//!
//! The list comes from `git diff` against the merge base with `origin/main` (or `--base`), never
//! from a file a change can write. Without `--head` it is the working tree that is compared,
//! untracked files included: an uncommitted edit to a fixture is the case this exists for. Only
//! a *new* file under a test directory is exempt, since it can't weaken a test that exists; new
//! lines in an existing test file can (an early `return`), so they are not.
//!
//! The line is information, and on this repository's history it is frequent: 113 of main's 228
//! commits touch a judging file, 91 of them an existing test file, and 102 still do when only
//! removed or changed lines count. So it can't be the alarm by itself. The alarm is `fai accept`
//! running the tests *as they were at the base* against the changed code (`accept.rs`): a change
//! that passes its old tests didn't need to move them.
//!
//! Exit codes of `fai judging`: 0 when no judging file changed, 3 when some did, 2 when there
//! is nothing to compare with (no git, or no base). `verify`, `gate`, and `accept` print the
//! same line and put it in their reports; there it changes no exit code but `accept`'s.
//!
//! The path list below is itself a judging file (it is under `tools/fai/src`), and
//! `fai mutate` checks that dropping the tests from it is caught.

use std::path::Path;
use std::process::Command;

use serde_json::{Value, json};

/// What a judging file is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// A test, a fixture, or an expected output.
    Test,
    /// What was accepted: the gate's baseline, the proof lock, the registered claims.
    Baseline,
    /// A program that gives a verdict, or part of one.
    Checker,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Test => "test",
            Kind::Baseline => "baseline",
            Kind::Checker => "checker",
        }
    }
}

/// The judging files that aren't tests: a path, or a directory when it ends in `/`.
const JUDGING: &[(&str, Kind)] = &[
    ("benchmarks/projects/gate.json", Kind::Baseline),
    ("docs/assurance/proofs.lock.json", Kind::Baseline),
    ("spec/Audit/Claims.lean", Kind::Baseline),
    // `fai` itself: verify, the evidence it requires, the host gaps, mutate's planted defects,
    // and this list.
    ("tools/fai/src/", Kind::Checker),
    // The gate, the harness it imports, and the plugin that counts instructions.
    ("benchmarks/projects/projbench.py", Kind::Checker),
    ("benchmarks/c/cbench.py", Kind::Checker),
    ("benchmarks/c/insn_count.c", Kind::Checker),
    (".github/workflows/", Kind::Checker),
    // The proof audit.
    ("spec/Audit.lean", Kind::Checker),
    ("spec/Audit/", Kind::Checker),
    // The verifiers and the checkers that run inside the compiler.
    ("spec/Fir/Verify.lean", Kind::Checker),
    ("spec/Fir/DceCheck.lean", Kind::Checker),
    ("spec/Fir/DceCheckLinear.lean", Kind::Checker),
    ("compiler/ir/src/verify.rs", Kind::Checker),
    ("targets/aarch64/src/regcheck.rs", Kind::Checker),
    ("targets/aarch64/src/regcheck/", Kind::Checker),
];

/// Whether `path` (relative to the repository's root, with `/`) is a judging file, and which
/// kind. A file under any directory named `tests` is a test.
pub(crate) fn classify(path: &str) -> Option<Kind> {
    for (p, k) in JUDGING {
        if path == *p || (p.ends_with('/') && path.starts_with(p)) {
            return Some(*k);
        }
    }
    let dirs = path.rsplit_once('/').map_or("", |(d, _)| d);
    dirs.split('/').any(|c| c == "tests").then_some(Kind::Test)
}

/// One judging file a change touches: `A`dded, `M`odified, or `D`eleted, and the lines it adds
/// and removes when git counted them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Change {
    pub status: char,
    pub path: String,
    pub kind: Kind,
    pub lines: Option<(u64, u64)>,
}

/// The judging files among `git diff --name-status` lines (`M\tpath`), and how many new test
/// files were left out as exempt.
pub(crate) fn judged(name_status: &str) -> (Vec<Change>, usize) {
    let mut out = Vec::new();
    let mut added_tests = 0;
    for line in name_status.lines() {
        let Some((status, path)) = line.split_once('\t') else {
            continue;
        };
        let Some(status) = status.chars().next() else {
            continue;
        };
        let Some(kind) = classify(path) else { continue };
        if status == 'A' && kind == Kind::Test {
            added_tests += 1;
            continue;
        }
        out.push(Change {
            status,
            path: path.to_owned(),
            kind,
            lines: None,
        });
    }
    out.sort_by(|a, b| a.path.cmp(&b.path));
    out.dedup();
    (out, added_tests)
}

/// Fill in each change's line counts from `git diff --numstat` lines (`added\tremoved\tpath`).
fn count_lines(changes: &mut [Change], numstat: &str) {
    for line in numstat.lines() {
        let mut f = line.splitn(3, '\t');
        let (Some(a), Some(d), Some(path)) = (f.next(), f.next(), f.next()) else {
            continue;
        };
        let (Ok(a), Ok(d)) = (a.parse(), d.parse()) else {
            continue;
        };
        if let Some(c) = changes.iter_mut().find(|c| c.path == path) {
            c.lines = Some((a, d));
        }
    }
}

/// What the judging line says.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Judging {
    /// Nothing to compare with, and why.
    NoBase(String),
    /// Compared with `base` (a revision): the judging files changed, and the new test files
    /// exempted.
    Against {
        base: String,
        changes: Vec<Change>,
        added_tests: usize,
    },
}

impl Judging {
    /// The judging files changed (none when there was no base).
    pub(crate) fn changes(&self) -> &[Change] {
        match self {
            Judging::Against { changes, .. } => changes,
            Judging::NoBase(_) => &[],
        }
    }

    pub(crate) fn changed(&self) -> bool {
        matches!(self, Judging::Against { changes, .. } if !changes.is_empty())
    }

    /// The exit code of `fai judging`.
    pub(crate) fn exit_code(&self) -> i32 {
        match self {
            Judging::NoBase(_) => 2,
            j if j.changed() => 3,
            _ => 0,
        }
    }

    /// The one line every verdict carries.
    pub(crate) fn line(&self) -> String {
        match self {
            Judging::NoBase(why) => format!("judging files: no base ({why})"),
            Judging::Against { base, changes, .. } if changes.is_empty() => {
                format!("judging files: unchanged against {}", short(base))
            }
            Judging::Against { base, changes, .. } => format!(
                "judging files: CHANGED against {} ({}): {}",
                short(base),
                changes.len(),
                changes
                    .iter()
                    .map(|c| c.path.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    /// The line, then each file with what happened to it and what it is.
    pub(crate) fn listing(&self) -> String {
        let mut s = self.line();
        if let Judging::Against {
            changes,
            added_tests,
            ..
        } = self
        {
            for c in changes {
                let lines = c
                    .lines
                    .map_or(String::new(), |(a, d)| format!(", +{a} -{d}"));
                s += &format!("\n  {} {}  ({}{lines})", c.status, c.path, c.kind.name());
            }
            if *added_tests > 0 {
                s += &format!("\n  ({added_tests} new test files, which are exempt)");
            }
        }
        s
    }

    pub(crate) fn json(&self) -> Value {
        match self {
            Judging::NoBase(why) => json!({"state": "no base", "why": why}),
            Judging::Against {
                base,
                changes,
                added_tests,
            } => json!({
                "state": if changes.is_empty() { "unchanged" } else { "changed" },
                "base": base,
                "added_tests": added_tests,
                "files": changes
                    .iter()
                    .map(|c| json!({
                        "status": c.status.to_string(),
                        "path": c.path,
                        "kind": c.kind.name(),
                        "added": c.lines.map(|l| l.0),
                        "removed": c.lines.map(|l| l.1),
                    }))
                    .collect::<Vec<_>>(),
            }),
        }
    }
}

fn short(rev: &str) -> &str {
    if rev.len() == 40 && rev.bytes().all(|b| b.is_ascii_hexdigit()) {
        &rev[..9]
    } else {
        rev
    }
}

/// `git ARGS` in `root`: its standard output, trimmed, when it succeeded.
pub(crate) fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|e| format!("can't run git: {e}"))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).trim_end().to_owned())
    } else {
        Err(String::from_utf8_lossy(&out.stderr)
            .lines()
            .next()
            .unwrap_or("git failed")
            .to_owned())
    }
}

/// The judging files that differ between the merge base of `base` (default: `origin/main`, then
/// `main`) and `head`, or the working tree when `head` is `None`.
pub(crate) fn judging(root: &Path, base: Option<&str>, head: Option<&str>) -> Judging {
    let tip = head.unwrap_or("HEAD");
    let merge_base = |rev: &str| git(root, &["merge-base", rev, tip]);
    let base = match base {
        Some(b) => merge_base(b),
        None => merge_base("origin/main").or_else(|_| merge_base("main")),
    };
    let base = match base {
        Ok(b) => b,
        Err(e) => return Judging::NoBase(e),
    };
    let mut args = vec!["diff", "--name-status", "--no-renames", base.as_str()];
    if let Some(h) = head {
        args.push(h);
    }
    let mut lines = match git(root, &args) {
        Ok(l) => l,
        Err(e) => return Judging::NoBase(e),
    };
    if head.is_none() {
        // Files git doesn't track yet are part of the change too.
        match git(root, &["ls-files", "--others", "--exclude-standard"]) {
            Ok(new) => {
                for f in new.lines() {
                    lines += &format!("\nA\t{f}");
                }
            }
            Err(e) => return Judging::NoBase(e),
        }
    }
    let (mut changes, added_tests) = judged(&lines);
    args[1] = "--numstat";
    if let Ok(numstat) = git(root, &args) {
        count_lines(&mut changes, &numstat);
    }
    Judging::Against {
        base,
        changes,
        added_tests,
    }
}

/// The identity of the tree as it is now: git's hash of every tracked and untracked file that
/// isn't ignored, so a tree with uncommitted edits has one too. It is made on a copy of the
/// index under `target/`, and never touches the real index or the stash.
pub(crate) fn tree_hash(root: &Path) -> Result<String, String> {
    let index = git(root, &["rev-parse", "--git-path", "index"])?;
    let dir = root.join("target/fai");
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let tmp = dir.join(format!("index.{}", std::process::id()));
    // The real index's cached stats make `add` read only what changed.
    let _ = std::fs::copy(root.join(&index), &tmp);
    let run = |args: &[&str]| -> Result<String, String> {
        let out = Command::new("git")
            .args(args)
            .current_dir(root)
            .env("GIT_INDEX_FILE", &tmp)
            .output()
            .map_err(|e| format!("can't run git: {e}"))?;
        if out.status.success() {
            Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned())
        } else {
            Err(String::from_utf8_lossy(&out.stderr).trim().to_owned())
        }
    };
    let hash = run(&["add", "-A"]).and_then(|_| run(&["write-tree"]));
    let _ = std::fs::remove_file(&tmp);
    hash
}

/// `fai judging [--base REV] [--head REV] [--json]`.
pub(crate) fn main(root: &Path, rest: &[String]) -> i32 {
    let (mut base, mut head, mut as_json) = (None, None, false);
    let mut it = rest.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--base" => base = it.next().map(String::as_str),
            "--head" => head = it.next().map(String::as_str),
            "--json" => as_json = true,
            _ => {
                eprintln!("usage: fai judging [--base REV] [--head REV] [--json]");
                return 2;
            }
        }
    }
    let j = judging(root, base, head);
    if as_json {
        println!("{}", serde_json::to_string_pretty(&j.json()).unwrap());
    } else {
        println!("{}", j.listing());
    }
    j.exit_code()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tests_baselines_and_checkers_are_judging_files() {
        for (path, kind) in [
            ("tests/rust/regcheck.rs", Kind::Test),
            ("tests/fir0/holes.fir", Kind::Test),
            ("sdk/c/tests/fcc.rs", Kind::Test),
            ("frontends/c/tests/c23/x.c", Kind::Test),
            ("benchmarks/projects/gate.json", Kind::Baseline),
            ("docs/assurance/proofs.lock.json", Kind::Baseline),
            ("spec/Audit/Claims.lean", Kind::Baseline),
            ("tools/fai/src/mutate.rs", Kind::Checker),
            ("tools/fai/src/judging.rs", Kind::Checker),
            ("benchmarks/projects/projbench.py", Kind::Checker),
            (".github/workflows/verify.yml", Kind::Checker),
            ("spec/Audit/Lock.lean", Kind::Checker),
            ("spec/Fir/Verify.lean", Kind::Checker),
            ("compiler/ir/src/verify.rs", Kind::Checker),
            ("targets/aarch64/src/regcheck/state.rs", Kind::Checker),
        ] {
            assert_eq!(classify(path), Some(kind), "{path}");
        }
        for path in [
            "targets/aarch64/src/isel.rs",
            "spec/Fir/Slot.lean",
            "docs/design/07-plan.md",
            "README.md",
            // A file named like a test directory isn't in one.
            "docs/tests",
            "compiler/ir/src/contests/x.rs",
        ] {
            assert_eq!(classify(path), None, "{path}");
        }
    }

    #[test]
    fn an_edited_or_removed_test_is_named_and_a_new_test_file_is_not() {
        let diff = "M\ttests/rust/debug_lines.rs\nA\ttests/rust/new.rs\nD\ttests/fir0/holes.fir\n\
                    M\ttargets/aarch64/src/isel.rs\nA\tbenchmarks/projects/gate.json";
        let (changes, added) = judged(diff);
        let paths: Vec<&str> = changes.iter().map(|c| c.path.as_str()).collect();
        assert_eq!(
            paths,
            [
                "benchmarks/projects/gate.json",
                "tests/fir0/holes.fir",
                "tests/rust/debug_lines.rs"
            ]
        );
        assert_eq!(added, 1);
        let j = Judging::Against {
            base: "0123456789abcdef0123456789abcdef01234567".into(),
            changes,
            added_tests: added,
        };
        assert_eq!(j.exit_code(), 3);
        assert!(
            j.line()
                .starts_with("judging files: CHANGED against 012345678 (3): ")
        );
    }

    #[test]
    fn a_change_to_no_judging_file_is_unchanged() {
        let (changes, added) =
            judged("M\ttargets/aarch64/src/isel.rs\nA\ttests/rust/new.rs\nA\tdocs/x.md");
        let j = Judging::Against {
            base: "main".into(),
            changes,
            added_tests: added,
        };
        assert_eq!(j.exit_code(), 0);
        assert_eq!(j.line(), "judging files: unchanged against main");
        assert_eq!(Judging::NoBase("no git".into()).exit_code(), 2);
    }
}
