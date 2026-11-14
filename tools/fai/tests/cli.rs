//! The `fai` command line, run as a user runs it: every command dispatches, says how to use it,
//! and exits 0 (success), 1 (a failed check), or 2 (bad usage), as callers and CI rely on. None
//! of these runs a verification, a mutation, or a build: each stops at its argument check or
//! does only the cheap work its command is for.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fai(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fai"))
        .args(args)
        .output()
        .expect("running fai")
}

fn code(o: &Output) -> i32 {
    o.status.code().expect("fai exited with a signal")
}

fn text(o: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    )
}

fn scratch(name: &str) -> PathBuf {
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("fai-cli-{name}"));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

const COMMANDS: &[&str] = &[
    "fai verify",
    "fai mutate",
    "fai evidence",
    "fai experiment",
    "fai matrix",
];

#[test]
fn help_lists_every_command_and_succeeds() {
    for h in ["help", "--help", "-h"] {
        let o = fai(&[h]);
        assert_eq!(code(&o), 0, "{h}: {}", text(&o));
        let out = String::from_utf8_lossy(&o.stdout);
        for c in COMMANDS {
            assert!(out.contains(c), "{h} doesn't list {c}:\n{out}");
        }
    }
}

#[test]
fn bad_usage_exits_2_with_the_usage() {
    for args in [
        &[][..],
        &["frobnicate"],
        &["evidence"],
        &["evidence", "a", "b"],
        &["matrix"],
        &["verify", "bogus"],
        &["verify", "fast", "--report-dir"],
    ] {
        let o = fai(args);
        assert_eq!(code(&o), 2, "{args:?}: {}", text(&o));
        assert!(
            text(&o).contains("usage: fai verify"),
            "{args:?}: {}",
            text(&o)
        );
    }
}

#[test]
fn experiment_checks_its_arguments_before_building_anything() {
    for args in [
        &["experiment"][..],
        &["experiment", "../escape"],
        &["experiment", "x", "--none"],
        &["experiment", "x", "--experimental"],
        &["experiment", "x", "--gate", "maybe"],
    ] {
        let o = fai(args);
        assert_eq!(code(&o), 2, "{args:?}: {}", text(&o));
        assert!(
            text(&o).contains("usage: fai experiment"),
            "{args:?}: {}",
            text(&o)
        );
    }
}

#[test]
fn mutate_refuses_an_unknown_mutation_and_lists_them() {
    let o = fai(&["mutate", "no-such-mutation"]);
    assert_eq!(code(&o), 2, "{}", text(&o));
    assert!(
        text(&o).contains("experiment-rejects-a-miscompile"),
        "{}",
        text(&o)
    );
}

#[test]
fn evidence_fails_on_missing_evidence() {
    let o = fai(&["evidence", scratch("evidence").to_str().unwrap()]);
    assert_eq!(code(&o), 1, "{}", text(&o));
    assert!(text(&o).contains("no evidence"), "{}", text(&o));
}

#[test]
fn matrix_tabulates_reports_and_fails_on_a_bad_one() {
    let d = scratch("matrix");
    let report = d.join("report.json");
    std::fs::write(
        &report,
        r#"{"verdict": "FULL VERIFICATION PASSED", "host": "x86_64-linux",
            "identity": {"revision": "abc"}, "checks": [{"name": "clippy", "status": "passed"}],
            "execution": {"x86_64_fixtures": "natively on x86_64-linux"},
            "unverified_on_this_host": []}"#,
    )
    .unwrap();
    let o = fai(&["matrix", report.to_str().unwrap()]);
    assert_eq!(code(&o), 0, "{}", text(&o));
    let out = String::from_utf8_lossy(&o.stdout);
    assert!(
        out.contains("# Verification across hosts") && out.contains("x86_64-linux"),
        "{out}"
    );
    assert!(out.contains("| clippy | passed |"), "{out}");
    let bad = d.join("bad.json");
    std::fs::write(&bad, "not json").unwrap();
    assert_eq!(code(&fai(&["matrix", bad.to_str().unwrap()])), 1);
}

/// `cargo fai` is how a checkout runs it, and `cargo xtask`, the old name, must stay the same
/// command for existing scripts and branches; CI uses the new name.
#[test]
fn cargo_aliases_and_ci_name_the_fai_command() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let config = std::fs::read_to_string(root.join(".cargo/config.toml")).unwrap();
    let alias = |name: &str| {
        config
            .lines()
            .find_map(|l| l.strip_prefix(&format!("{name} = ")))
            .unwrap_or_else(|| panic!("no `{name}` alias"))
            .to_owned()
    };
    assert_eq!(
        alias("fai"),
        r#""run --quiet --package fai-tools --bin fai --""#
    );
    assert_eq!(alias("xtask"), alias("fai"));
    for wf in ["verify.yml", "experiment.yml"] {
        let text = std::fs::read_to_string(root.join(".github/workflows").join(wf)).unwrap();
        assert!(!text.contains("xtask"), "{wf} still says xtask");
        assert!(text.contains(" fai "), "{wf} doesn't run fai");
    }
}
