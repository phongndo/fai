//! The C test programs under `tests/capi/`, compiled against `include/fir.h` and the static
//! library and run: each prints `ok` and exits 0 when its checks pass. Together they must call
//! every function the header declares.
//!
//! The compiler is `$CC`, or `clang` (the dev shell's). `FIR_CAPI_SANITIZE=address` (or another
//! `-fsanitize=` value) builds the programs with that sanitizer.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

/// `libfir_capi.a`, built from the current sources. `cargo test` doesn't build a crate's static
/// library, and one left over from an earlier build may be stale, so build it here: with the
/// test's profile, in a target directory of its own (the outer cargo holds the main one's lock).
/// Cargo makes this a no-op when nothing changed.
fn static_lib() -> PathBuf {
    let release = !cfg!(debug_assertions);
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("capi-target");
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let mut cmd = Command::new(cargo);
    cmd.current_dir(repo())
        .args(["build", "--quiet", "-p", "fir-capi", "--target-dir"])
        .arg(&target);
    if release {
        cmd.arg("--release");
    }
    let status = cmd.status().expect("running cargo");
    assert!(status.success(), "building the static library failed");
    let lib = target
        .join(if release { "release" } else { "debug" })
        .join("libfir_capi.a");
    assert!(lib.exists(), "{} is missing", lib.display());
    lib
}

fn c_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(repo().join("tests/capi"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "c"))
        .collect();
    files.sort();
    assert!(!files.is_empty());
    files
}

#[test]
fn c_programs_pass() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "clang".into());
    let out_dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("capi");
    std::fs::create_dir_all(&out_dir).unwrap();
    let include = repo().join("crates/fir-capi/include");
    for file in c_files() {
        let exe = out_dir.join(file.file_stem().unwrap());
        let mut cmd = Command::new(&cc);
        cmd.args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-g"])
            .arg("-I")
            .arg(&include)
            .arg(&file)
            .arg(static_lib())
            .arg("-o")
            .arg(&exe);
        if let Ok(s) = std::env::var("FIR_CAPI_SANITIZE") {
            cmd.arg(format!("-fsanitize={s}"));
        }
        if cfg!(target_os = "linux") {
            cmd.args(["-lpthread", "-ldl", "-lm"]);
        }
        let built = cmd
            .output()
            .unwrap_or_else(|e| panic!("running {cc} (set CC to a C compiler): {e}"));
        assert!(
            built.status.success(),
            "compiling {} failed:\n{}",
            file.display(),
            String::from_utf8_lossy(&built.stderr)
        );
        let ran = Command::new(&exe).output().unwrap();
        let stdout = String::from_utf8_lossy(&ran.stdout);
        assert!(
            ran.status.success() && stdout.trim_end().ends_with("ok"),
            "{} failed:\n{stdout}\n{}",
            file.display(),
            String::from_utf8_lossy(&ran.stderr)
        );
    }
}

/// Every function in the header is called by some C test.
#[test]
fn c_programs_call_every_function() {
    let header = std::fs::read_to_string(repo().join("crates/fir-capi/include/fir.h")).unwrap();
    let mut sources = String::new();
    for file in c_files() {
        sources += &std::fs::read_to_string(file).unwrap();
    }
    let mut missing = Vec::new();
    for line in header.lines() {
        if line.starts_with("//") || line.starts_with('#') {
            continue;
        }
        let Some(start) = line.find("fir_") else {
            continue;
        };
        let name: String = line[start..]
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if line[start + name.len()..].starts_with('(') && !sources.contains(&format!("{name}(")) {
            missing.push(name);
        }
    }
    assert!(missing.is_empty(), "not called by tests/capi: {missing:?}");
}
