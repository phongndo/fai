//! `src/generated/ops.rs` is what `lake exe gen-rust` prints from the op declarations in
//! `spec/Fir/Syntax.lean`. Regenerate it with
//! `cd spec && lake exe gen-rust > ../crates/fir/src/generated/ops.rs`.
//!
//! The generator is `spec/.lake/build/bin/gen-rust` (built by `lake build` in `spec/`), or the
//! path in `FIR_GEN_RUST`. `FIR_REF=none` skips this test with the other Lean comparisons.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn generated_ops_are_up_to_date() {
    if std::env::var("FIR_REF").is_ok_and(|s| s == "none") {
        return;
    }
    let tool = match std::env::var("FIR_GEN_RUST") {
        Ok(s) => PathBuf::from(s),
        Err(_) => repo().join("spec/.lake/build/bin/gen-rust"),
    };
    assert!(
        tool.exists(),
        "the Rust generator is missing: run `lake build` in spec/, or set FIR_REF=none to skip"
    );
    let out = Command::new(&tool)
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", tool.display()));
    assert!(
        out.status.success(),
        "gen-rust failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let want = String::from_utf8(out.stdout).unwrap();
    let have = std::fs::read_to_string(repo().join("crates/fir/src/generated/ops.rs")).unwrap();
    assert!(
        have == want,
        "crates/fir/src/generated/ops.rs is stale: run `cd spec && lake exe gen-rust > ../crates/fir/src/generated/ops.rs`"
    );
}
