//! The C test programs under `tests/capi/`, compiled against `include/fir.h` and the static
//! library and run: each prints `ok` and exits 0 when its checks pass. Together they must call
//! every function the header declares.
//!
//! `tests/capi/e2e.c` is the round's end-to-end test (`end_to_end_through_the_c_api`): it builds
//! a program through the C API, runs it in the interpreter, compiles it to AArch64, and runs the
//! binary (under `qemu-aarch64` off AArch64) against the interpreter's lines. It gets the AArch64
//! toolchain found here (as `tests/aarch64.rs` finds it: `$FIR_CC`, `cc` on AArch64, else
//! `aarch64-unknown-linux-gnu-cc`, and `qemu-aarch64`); without one, its native half is skipped
//! with a note.
//!
//! The compiler is `$CC`, or `clang` (the dev shell's). `FIR_CAPI_SANITIZE=address` (or another
//! `-fsanitize=` value) builds the programs with that sanitizer.

#[path = "../../../tests/rust/common/evidence.rs"]
mod evidence;

use std::path::{Path, PathBuf};
use std::process::Command;

/// The evidence name for a test, by sanitizer, so ASan and plain runs record separately.
fn evidence_name(test: &str) -> String {
    match std::env::var("FIR_CAPI_SANITIZE") {
        Ok(s) => format!("capi_{test}_{s}"),
        Err(_) => format!("capi_{test}"),
    }
}

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

/// Compile a C test program against the header and the static library.
fn build_c(file: &Path, exe: &Path) {
    let cc = std::env::var("CC").unwrap_or_else(|_| "clang".into());
    let include = repo().join("sdk/c/include");
    let mut cmd = Command::new(&cc);
    cmd.args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-g"])
        .arg("-I")
        .arg(&include)
        .arg(file)
        .arg(static_lib())
        .arg("-o")
        .arg(exe);
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
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The AArch64 C compiler and the emulator to run its binaries with (empty: natively), if any.
fn aarch64_toolchain() -> Option<(String, String)> {
    let native = cfg!(target_arch = "aarch64");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("aarch64-unknown-linux-gnu-cc") => {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => return None,
    };
    let runner = if native {
        String::new()
    } else if on_path("qemu-aarch64") {
        "qemu-aarch64".to_owned()
    } else {
        return None;
    };
    Some((cc, runner))
}

#[test]
fn c_programs_pass() {
    let ev = evidence::Evidence::new(&evidence_name("programs"));
    ev.fact(
        "sanitize",
        std::env::var("FIR_CAPI_SANITIZE").unwrap_or_default(),
    );
    let out_dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("capi");
    std::fs::create_dir_all(&out_dir).unwrap();
    for file in c_files() {
        if file.file_stem().is_some_and(|s| s == "e2e") {
            continue;
        }
        let exe = out_dir.join(file.file_stem().unwrap());
        build_c(&file, &exe);
        let ran = Command::new(&exe).output().unwrap();
        let stdout = String::from_utf8_lossy(&ran.stdout);
        assert!(
            ran.status.success() && stdout.trim_end().ends_with("ok"),
            "{} failed:\n{stdout}\n{}",
            file.display(),
            String::from_utf8_lossy(&ran.stderr)
        );
        ev.count("C programs passed", 1);
    }
    ev.write();
}

/// The round's end-to-end test (see the module docs and `tests/capi/e2e.c`). Its output, printed
/// with `--nocapture`, lists each run's outcome in the interpreter and natively.
#[test]
fn end_to_end_through_the_c_api() {
    let ev = evidence::Evidence::new(&evidence_name("e2e"));
    ev.fact(
        "sanitize",
        std::env::var("FIR_CAPI_SANITIZE").unwrap_or_default(),
    );
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("e2e");
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("e2e-host");
    build_c(&repo().join("tests/capi/e2e.c"), &exe);
    let mut cmd = Command::new(&exe);
    let tc = aarch64_toolchain();
    match &tc {
        Some((cc, runner)) => {
            cmd.env("FIR_E2E_CC", cc)
                .env("FIR_E2E_RUN", runner)
                .env("FIR_E2E_DIR", &dir);
        }
        None => {
            evidence::require("e2e: no AArch64 toolchain or emulator for the native half");
            ev.skip("native half: no AArch64 toolchain or emulator");
        }
    }
    let ran = cmd.output().unwrap();
    let stdout = String::from_utf8_lossy(&ran.stdout);
    eprintln!("{stdout}");
    assert!(
        ran.status.success() && stdout.trim_end().ends_with("ok"),
        "e2e failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    ev.count("e2e passed", 1);
    if tc.is_some() {
        assert!(
            stdout.contains("native: 14 of 14 runs match fir run"),
            "the native runs didn't all happen:\n{stdout}"
        );
        ev.count("native runs matching fir run", 14);
    }
    ev.write();
}

/// Every function in the header is called by some C test.
#[test]
fn c_programs_call_every_function() {
    let header = std::fs::read_to_string(repo().join("sdk/c/include/fir.h")).unwrap();
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
