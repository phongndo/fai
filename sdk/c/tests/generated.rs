//! The C API's generated files are current:
//!
//! * `src/generated/ops.rs` is what `lake exe gen-builder capi` prints from the op declarations
//!   (regenerate with `cd spec && lake exe gen-builder capi > ../sdk/c/src/generated/ops.rs`).
//!   The generator is `spec/.lake/build/bin/gen-builder` (built by `lake build` in `spec/`), or
//!   the path in `FIR_GEN_BUILDER`; `FIR_REF=none` skips this check.
//! * `include/fir.h` is what cbindgen makes of this crate (regenerate with the command in its
//!   first lines). cbindgen is the dev shell's, or the path in `CBINDGEN`.

#[path = "../../../tests/rust/common/evidence.rs"]
mod evidence;

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn output(cmd: &mut Command, what: &str) -> String {
    let out = cmd
        .output()
        .unwrap_or_else(|e| panic!("running {what}: {e}"));
    assert!(
        out.status.success(),
        "{what} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn generated_ops_are_up_to_date() {
    if std::env::var("FIR_REF").is_ok_and(|s| s == "none") {
        evidence::require("FIR_REF=none skips the generated C API check");
        return;
    }
    let tool = match std::env::var("FIR_GEN_BUILDER") {
        Ok(s) => PathBuf::from(s),
        Err(_) => repo().join("spec/.lake/build/bin/gen-builder"),
    };
    assert!(
        tool.exists(),
        "the builder generator is missing: run `lake build` in spec/, or set FIR_REF=none to skip"
    );
    let want = output(Command::new(&tool).arg("capi"), "gen-builder capi");
    let have = std::fs::read_to_string(repo().join("sdk/c/src/generated/ops.rs")).unwrap();
    assert!(
        have == want,
        "sdk/c/src/generated/ops.rs is stale: run `cd spec && lake exe gen-builder capi > ../sdk/c/src/generated/ops.rs`"
    );
}

#[test]
fn header_is_up_to_date() {
    let cbindgen = std::env::var("CBINDGEN").unwrap_or_else(|_| "cbindgen".into());
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fir.h");
    let crate_dir = repo().join("sdk/c");
    output(
        Command::new(&cbindgen)
            .current_dir(repo())
            .arg("--quiet")
            .arg("--config")
            .arg(crate_dir.join("cbindgen.toml"))
            .arg("--output")
            .arg(&tmp)
            .arg(&crate_dir),
        "cbindgen (from the dev shell, or set CBINDGEN)",
    );
    let want = std::fs::read_to_string(&tmp).unwrap();
    let have = std::fs::read_to_string(crate_dir.join("include/fir.h")).unwrap();
    assert!(
        have == want,
        "sdk/c/include/fir.h is stale: run `cbindgen --config sdk/c/cbindgen.toml --crate fir-capi --output sdk/c/include/fir.h`"
    );
}

/// The constants the header spells out agree with the crate's.
#[test]
fn constants_agree() {
    assert_eq!(fir_capi::FIR_DEFAULT_FUEL, fir::interp::DEFAULT_FUEL);
}
