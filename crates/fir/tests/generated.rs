//! The files `lake exe gen-rust` writes from the Lean op declarations and classifications must
//! be what it prints now:
//!
//! * `src/generated/ops.rs`: `lake exe gen-rust`;
//! * `src/generated/contracts.rs`: `lake exe gen-rust contracts`;
//! * `docs/assurance/op-contracts.json`: `lake exe gen-rust manifest`.
//!
//! The generator is `spec/.lake/build/bin/gen-rust` (built by `lake build` in `spec/`), or the
//! path in `FIR_GEN_RUST`. `FIR_REF=none` skips this test with the other Lean comparisons, unless
//! `FIR_REQUIRE_FULL=1`.

#[allow(dead_code)]
mod common;

use std::path::PathBuf;
use std::process::Command;

use common::evidence::{Evidence, require};
use common::repo;

fn generated(mode: &str, file: &str, ev: &Evidence) {
    let tool = match std::env::var("FIR_GEN_RUST") {
        Ok(s) => PathBuf::from(s),
        Err(_) => repo().join("spec/.lake/build/bin/gen-rust"),
    };
    assert!(
        tool.exists(),
        "the Rust generator is missing: run `lake build` in spec/, or set FIR_REF=none to skip"
    );
    let out = Command::new(&tool)
        .arg(mode)
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", tool.display()));
    assert!(
        out.status.success(),
        "gen-rust {mode} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let want = String::from_utf8(out.stdout).unwrap();
    let have = std::fs::read_to_string(repo().join(file)).unwrap_or_default();
    assert!(
        have == want,
        "{file} is stale: run `cd spec && lake exe gen-rust {mode} > ../{file}`"
    );
    ev.count(format!("fresh: {file}"), 1);
}

#[test]
fn generated_files_are_up_to_date() {
    let ev = Evidence::new("generated_rust");
    if std::env::var("FIR_REF").is_ok_and(|s| s == "none") {
        require("FIR_REF=none skips the generated-file checks");
        ev.skip("FIR_REF=none");
        ev.write();
        return;
    }
    generated("ops", "compiler/ir/src/generated/ops.rs", &ev);
    generated("contracts", "compiler/ir/src/generated/contracts.rs", &ev);
    generated("manifest", "docs/assurance/op-contracts.json", &ev);
    ev.write();
}
