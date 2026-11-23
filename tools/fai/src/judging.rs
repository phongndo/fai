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
//! untracked files included: an uncommitted edit to a fixture is the case this exists for.
//!
//! A *new* fixture or test program under a test directory is exempt, since it can't weaken a
//! test that exists. Nothing else new there is: a new header or helper can be picked up by
//! tests that exist (a header found first on an include path), and new lines in an existing
//! test file can weaken it (an early `return`).
//!
//! The line is information, and on this repository's history it is frequent: 113 of main's 228
//! commits touch a judging file, 91 of them an existing test file, and 102 still do when only
//! removed or changed lines count. So it can't be the alarm by itself. The alarm is `fai accept`
//! running the tests *as they were at the base* against the changed code (`accept.rs`): a change
//! that passes its old tests didn't need to move them.
//!
//! Exit codes of `fai judging`: 0 when no judging file changed, 3 when some did, 2 when there
//! is nothing to compare with (no git, not the root of a checkout, or no base). `verify`,
//! `gate`, and `accept` print the same line and put it in their reports; there it changes no
//! exit code but `accept`'s.
//!
//! The path list below is itself a judging file (it is under `tools/fai/src`), and
//! `fai mutate` checks that dropping the tests from it is caught.
//!
//! # The identity of a tree
//!
//! [`tree_hash`] is git's hash of every file in the checkout that git doesn't ignore, tracked
//! or not, read from disk into an index of its own (so `assume-unchanged` and `skip-worktree`
//! marks, which live in the real index, hide nothing). What it doesn't see: files git ignores
//! (the build outputs, and the sources the gate fetches, which the gate checks itself), the
//! contents of a nested checkout, an executable bit where `core.filemode` is off, and a tree
//! that changed and changed back between two readings.

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
    // The gate, the harness it imports, the plugin that counts instructions, and its workloads.
    ("benchmarks/projects/projbench.py", Kind::Checker),
    ("benchmarks/c/cbench.py", Kind::Checker),
    ("benchmarks/c/insn_count.c", Kind::Checker),
    ("benchmarks/projects/lua/", Kind::Checker),
    // The workflow of the required checks (not the manual experiment's).
    (".github/workflows/verify.yml", Kind::Checker),
    // The proof audit, and the reference tool the tests compare with.
    ("spec/Audit.lean", Kind::Checker),
    ("spec/Audit/", Kind::Checker),
    ("spec/Main.lean", Kind::Checker),
    // The verifiers and the checkers that run inside the compiler. Two of them share a file
    // with what they check (the x86-64 allocator, the DCE pass).
    ("spec/Fir/Verify.lean", Kind::Checker),
    ("spec/Fir/DceCheck.lean", Kind::Checker),
    ("spec/Fir/DceCheckLinear.lean", Kind::Checker),
    ("compiler/ir/src/verify.rs", Kind::Checker),
    ("compiler/transforms/src/dce.rs", Kind::Checker),
    ("compiler/transforms/src/reference.rs", Kind::Checker),
    ("targets/aarch64/src/regcheck.rs", Kind::Checker),
    ("targets/aarch64/src/regcheck/", Kind::Checker),
    ("targets/x86_64/src/regalloc.rs", Kind::Checker),
    // What decides which tests exist, how they build, and with which tools.
    ("Cargo.lock", Kind::Checker),
    (".cargo/", Kind::Checker),
    ("flake.nix", Kind::Checker),
    ("flake.lock", Kind::Checker),
    ("nix/", Kind::Checker),
    ("pyproject.toml", Kind::Checker),
    ("uv.lock", Kind::Checker),
    ("spec/lakefile.toml", Kind::Checker),
    ("spec/lakefile.lean", Kind::Checker),
    ("spec/lake-manifest.json", Kind::Checker),
    ("spec/lean-toolchain", Kind::Checker),
];

/// Directories of helpers that tests share: a new file in one can change tests that exist.
const SHARED_BY_TESTS: &[&str] = &["common", "runtime", "native", "progs", "taint", "extern"];

/// Whether `path` (relative to the repository's root, with `/`) is a judging file, and which
/// kind. A file under any directory named `tests` is a test; a Cargo manifest, which says
/// which tests exist, is a checker.
pub(crate) fn classify(path: &str) -> Option<Kind> {
    for (p, k) in JUDGING {
        if path == *p || (p.ends_with('/') && path.starts_with(p)) {
            return Some(*k);
        }
    }
    if path == "Cargo.toml" || path.ends_with("/Cargo.toml") {
        return Some(Kind::Checker);
    }
    let dirs = path.rsplit_once('/').map_or("", |(d, _)| d);
    dirs.split('/').any(|c| c == "tests").then_some(Kind::Test)
}

/// Whether a new file at `path`, under a test directory, can't change a test that exists: a
/// fixture or a test program (`.fir`, `.c`, `.rs`) outside the directories tests share.
pub(crate) fn new_test_is_exempt(path: &str) -> bool {
    let (dirs, file) = path.rsplit_once('/').unwrap_or(("", path));
    let alone = !dirs.split('/').any(|c| SHARED_BY_TESTS.contains(&c));
    let kind = file.rsplit_once('.').map_or("", |(_, e)| e);
    alone && matches!(kind, "fir" | "c" | "rs")
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

/// The judging files among a diff's `(status, path)` pairs, and how many new test files were
/// left out as exempt ([`new_test_is_exempt`]).
pub(crate) fn judged(changed: &[(char, String)]) -> (Vec<Change>, usize) {
    let mut out = Vec::new();
    let mut added_tests = 0;
    for (status, path) in changed {
        let Some(kind) = classify(path) else { continue };
        if *status == 'A' && kind == Kind::Test && new_test_is_exempt(path) {
            added_tests += 1;
            continue;
        }
        out.push(Change {
            status: *status,
            path: path.clone(),
            kind,
            lines: None,
        });
    }
    out.sort_by(|a, b| a.path.cmp(&b.path));
    out.dedup();
    (out, added_tests)
}

/// `git diff --name-status -z` output as `(status, path)` pairs. With `-z` git separates the
/// fields with NUL and writes a path as it is: without it, a path with a byte outside ASCII
/// arrives quoted and escaped (`"tests/caf\303\251.fir"`), and would match nothing.
/// A path that isn't UTF-8 can't be named or replayed faithfully, so it makes the whole list
/// an error (`NOT JUDGED`), not a path that names no file.
pub(crate) fn name_status(z: &[u8]) -> Result<Vec<(char, String)>, String> {
    let mut fields = z.split(|&b| b == 0).filter(|f| !f.is_empty());
    let mut out = Vec::new();
    while let (Some(status), Some(path)) = (fields.next(), fields.next()) {
        let path = String::from_utf8(path.to_vec()).map_err(|_| {
            format!(
                "a changed path isn't UTF-8 ({})",
                String::from_utf8_lossy(path)
            )
        })?;
        if let Some(&c) = status.first() {
            out.push((c as char, path));
        }
    }
    Ok(out)
}

/// Fill in each change's line counts from `git diff --numstat -z` output
/// (`added\tremoved\tpath`, NUL after each).
fn count_lines(changes: &mut [Change], numstat: &[u8]) {
    for entry in numstat.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let entry = String::from_utf8_lossy(entry);
        let mut f = entry.splitn(3, '\t');
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

/// `git ARGS` in `root`: its standard output as bytes, when it succeeded.
fn git_bytes(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|e| format!("can't run git: {e}"))?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(String::from_utf8_lossy(&out.stderr)
            .lines()
            .next()
            .unwrap_or("git failed")
            .to_owned())
    }
}

/// `git ARGS` in `root`: its standard output, trimmed, when it succeeded.
pub(crate) fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    git_bytes(root, args).map(|o| String::from_utf8_lossy(&o).trim_end().to_owned())
}

/// `root` must be the top of a git checkout. In a directory inside one (a copy of the tree
/// under an ignored `target/`), git would answer for the checkout around it, and a report
/// written there would name a tree it didn't judge.
fn checkout_root(root: &Path) -> Result<(), String> {
    let top = git(root, &["rev-parse", "--show-toplevel"])?;
    let same = match (Path::new(&top).canonicalize(), root.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    };
    if same {
        Ok(())
    } else {
        Err(format!(
            "{} is not the root of a git checkout",
            root.display()
        ))
    }
}

/// The judging files that differ between the merge base of `base` (default: `origin/main`, then
/// `main`) and `head`, or the working tree when `head` is `None`.
pub(crate) fn judging(root: &Path, base: Option<&str>, head: Option<&str>) -> Judging {
    if let Err(e) = checkout_root(root) {
        return Judging::NoBase(e);
    }
    let tip = head.unwrap_or("HEAD");
    let merge_base = |rev: &str| git(root, &["merge-base", rev, tip]);
    // The working tree is compared as `tree_hash` reads it: every file from disk, untracked
    // ones included, and no index mark (`assume-unchanged`, `skip-worktree`) hiding an edit.
    let now;
    let head = match head {
        Some(h) => Some(h),
        None => match tree_hash(root) {
            Ok(t) => {
                now = t;
                Some(now.as_str())
            }
            Err(e) => return Judging::NoBase(e),
        },
    };
    let base = match base {
        Some(b) => merge_base(b),
        None => merge_base("origin/main").or_else(|_| merge_base("main")),
    };
    let base = match base {
        Ok(b) => b,
        Err(e) => return Judging::NoBase(e),
    };
    let mut args = vec!["diff", "--name-status", "-z", "--no-renames", base.as_str()];
    if let Some(h) = head {
        args.push(h);
    }
    let changed = match git_bytes(root, &args).and_then(|z| name_status(&z)) {
        Ok(c) => c,
        Err(e) => return Judging::NoBase(e),
    };
    let (mut changes, added_tests) = judged(&changed);
    args[1] = "--numstat";
    if let Ok(numstat) = git_bytes(root, &args) {
        count_lines(&mut changes, &numstat);
    }
    Judging::Against {
        base,
        changes,
        added_tests,
    }
}

/// The identity of the tree as it is now: git's hash of every file in the checkout that git
/// doesn't ignore, tracked or not, so a tree with uncommitted edits has one too. The files are
/// read from disk into a new index under `target/`: the real index and the stash are never
/// touched, and marks in the real index (`assume-unchanged`, `skip-worktree`) hide nothing.
/// (It leaves the files' blobs in the object store, which changes nothing a checkout sees.)
pub(crate) fn tree_hash(root: &Path) -> Result<String, String> {
    checkout_root(root)?;
    let dir = root.join("target/fai");
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let tmp = dir.join(format!("index.{}.{nanos}", std::process::id()));
    let _ = std::fs::remove_file(&tmp);
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
    // From HEAD's files (with no cached stats, so every file is read again, and none of the
    // real index's marks), then every change on disk: a tracked file stays tracked even if an
    // exclude rule matches it, and only untracked files are left to the ignore rules.
    let hash = run(&["read-tree", "HEAD"])
        .and_then(|_| run(&["add", "-A"]))
        .and_then(|_| run(&["write-tree"]));
    let _ = std::fs::remove_file(&tmp);
    match hash {
        Ok(h) if h.len() >= 40 => Ok(h),
        Ok(h) => Err(format!("git write-tree printed {h:?}")),
        Err(e) => Err(e),
    }
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

    fn pairs(v: &[(char, &str)]) -> Vec<(char, String)> {
        v.iter().map(|(s, p)| (*s, (*p).to_owned())).collect()
    }

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
            ("benchmarks/projects/lua/trees.lua", Kind::Checker),
            (".github/workflows/verify.yml", Kind::Checker),
            ("spec/Audit/Lock.lean", Kind::Checker),
            ("spec/Main.lean", Kind::Checker),
            ("spec/Fir/Verify.lean", Kind::Checker),
            ("compiler/ir/src/verify.rs", Kind::Checker),
            ("compiler/transforms/src/dce.rs", Kind::Checker),
            ("targets/aarch64/src/regcheck/state.rs", Kind::Checker),
            // What decides which tests exist and how they are built.
            ("Cargo.toml", Kind::Checker),
            ("sdk/rust/Cargo.toml", Kind::Checker),
            (".cargo/config.toml", Kind::Checker),
            ("flake.lock", Kind::Checker),
            ("nix/devshell.nix", Kind::Checker),
            ("spec/lakefile.toml", Kind::Checker),
        ] {
            assert_eq!(classify(path), Some(kind), "{path}");
        }
        for path in [
            "targets/aarch64/src/isel.rs",
            "spec/Fir/Slot.lean",
            "docs/design/07-plan.md",
            "README.md",
            // The manual experiment's workflow is no part of the required checks.
            ".github/workflows/experiment.yml",
            // A file named like a test directory isn't in one.
            "docs/tests",
            "compiler/ir/src/contests/x.rs",
        ] {
            assert_eq!(classify(path), None, "{path}");
        }
    }

    #[test]
    fn an_edited_or_removed_test_is_named_and_a_new_test_file_is_not() {
        let diff = pairs(&[
            ('M', "tests/rust/debug_lines.rs"),
            ('A', "tests/rust/new.rs"),
            ('D', "tests/fir0/holes.fir"),
            ('M', "targets/aarch64/src/isel.rs"),
            ('A', "benchmarks/projects/gate.json"),
        ]);
        let (changes, added) = judged(&diff);
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
    fn only_a_new_fixture_or_test_program_is_exempt() {
        for path in [
            "tests/fir0/new.fir",
            "tests/rust/new.rs",
            "frontends/c/tests/c23/new.c",
        ] {
            assert!(new_test_is_exempt(path), "{path}");
        }
        // A new header can shadow one that existing tests include, and a new file among the
        // helpers tests share can change them.
        for path in [
            "frontends/c/tests/fai_test.h",
            "frontends/c/tests/runtime/extra.c",
            "tests/rust/common/extra.rs",
            "tests/rust/native/extra.rs",
            "tests/notes.txt",
        ] {
            assert!(!new_test_is_exempt(path), "{path}");
        }
        let (changes, added) = judged(&pairs(&[
            ('A', "frontends/c/tests/fai_test.h"),
            ('A', "tests/fir0/new.fir"),
        ]));
        assert_eq!(added, 1);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].path, "frontends/c/tests/fai_test.h");
    }

    #[test]
    fn paths_come_whole_from_git_whatever_bytes_they_have() {
        // What `git diff --name-status -z` prints: no quotes, NUL between the fields.
        let z = "M\0tests/fir0/caf\u{e9}.fir\0D\0tests/a b\tc.fir\0A\0docs/x.md\0";
        let got = name_status(z.as_bytes()).unwrap();
        assert_eq!(
            got,
            pairs(&[
                ('M', "tests/fir0/caf\u{e9}.fir"),
                ('D', "tests/a b\tc.fir"),
                ('A', "docs/x.md")
            ])
        );
        let (mut changes, _) = judged(&got);
        assert_eq!(changes.len(), 2);
        count_lines(
            &mut changes,
            "3\t1\ttests/fir0/caf\u{e9}.fir\0-\t-\ttests/a b\tc.fir\0".as_bytes(),
        );
        let caf = changes
            .iter()
            .find(|c| c.path.ends_with(".fir") && c.status == 'M');
        assert_eq!(caf.unwrap().lines, Some((3, 1)));
    }

    #[test]
    fn a_path_that_is_not_utf8_is_not_judged() {
        let mut z = b"M\0tests/fir0/".to_vec();
        z.push(0xff);
        z.extend_from_slice(b".fir\0");
        assert!(name_status(&z).is_err());
    }

    #[test]
    fn a_change_to_no_judging_file_is_unchanged() {
        let (changes, added) = judged(&pairs(&[
            ('M', "targets/aarch64/src/isel.rs"),
            ('A', "tests/rust/new.rs"),
            ('A', "docs/x.md"),
        ]));
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
