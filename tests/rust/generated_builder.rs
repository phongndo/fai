//! `src/generated/builder.rs` is what `lake exe gen-builder rust` prints from the op declarations
//! in `spec/Fir/Syntax.lean`. Regenerate it with
//! `cd spec && lake exe gen-builder rust > ../compiler/ir/src/generated/builder.rs`.
//!
//! The generator is `spec/.lake/build/bin/gen-builder` (built by `lake build` in `spec/`), or the
//! path in `FIR_GEN_BUILDER`. `FIR_REF=none` skips this test with the other Lean comparisons.

#[path = "common/evidence.rs"]
mod evidence;

use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn generated_builder_is_up_to_date() {
    if std::env::var("FIR_REF").is_ok_and(|s| s == "none") {
        evidence::require("FIR_REF=none skips the generated builder check");
        return;
    }
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let tool = match std::env::var("FIR_GEN_BUILDER") {
        Ok(s) => PathBuf::from(s),
        Err(_) => repo.join("spec/.lake/build/bin/gen-builder"),
    };
    assert!(
        tool.exists(),
        "the builder generator is missing: run `lake build` in spec/, or set FIR_REF=none to skip"
    );
    let out = Command::new(&tool)
        .arg("rust")
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", tool.display()));
    assert!(
        out.status.success(),
        "gen-builder failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let want = String::from_utf8(out.stdout).unwrap();
    let have = std::fs::read_to_string(repo.join("compiler/ir/src/generated/builder.rs")).unwrap();
    assert!(
        have == want,
        "compiler/ir/src/generated/builder.rs is stale: run `cd spec && lake exe gen-builder rust > ../compiler/ir/src/generated/builder.rs`"
    );
}
