//! Running the proved Lean DCE checker on the real pipeline's output.
//!
//! [`CheckDce`] is a pipeline [`Observer`]: before each run of `dce` it snapshots the module, and
//! after it writes both snapshots out and runs `fir-ref check-dce SRC TGT`, which runs
//! `Fir.Dce.checkFunc` on every pair of functions. `Fir.Dce.checkFunc_sound` says that an
//! accepted target function refines its source function *in the source module*, provided the
//! source is `Func.Decided` there (no run reaches a choice the reference semantics leaves
//! open, such as an address that may belong to two allocations). Nothing checks `Decided`.
//!
//! The checker's receipt (`ok N`, then both modules as Lean parsed and printed them) must match
//! the snapshots byte for byte, so an acceptance can't be about other text: the Rust printer and
//! the Lean parser are in the trusted base, and the match checks that they agree on these
//! modules. This is what `tests/dce_check.rs` does in the tests, here available for any input
//! (`fir opt --check-dce`; `fir opt FILE -O --check-dce FIR-REF | fir compile -` checks what
//! is compiled). It validates each DCE step of this
//! run; it says nothing about the other passes, about composing per-function refinements
//! across a module's calls, or about steps of other runs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use super::{Observer, Pass};
use crate::ir::Module;

/// Validates every `dce` step of a pipeline run with `fir-ref check-dce`.
pub struct CheckDce {
    tool: PathBuf,
    dir: PathBuf,
    before: Option<Module>,
    /// Steps checked (runs of `dce` that changed the module).
    pub steps: u64,
    /// Runs of `dce` that left the module unchanged (by its printed text, not the pass's count),
    /// so had nothing to check.
    pub unchanged: u64,
    /// Function pairs the checker accepted, over all steps.
    pub functions: u64,
    /// Ops deleted in the checked steps.
    pub deletions: u64,
    /// Time spent writing the snapshots, running the checker, and matching its receipt.
    pub time: Duration,
}

impl CheckDce {
    /// Check with the `fir-ref` at `tool`, writing snapshots into `dir` (created if needed; each
    /// pair is removed once accepted, kept for inspection when refused).
    pub fn new(tool: impl Into<PathBuf>, dir: impl Into<PathBuf>) -> CheckDce {
        CheckDce {
            tool: tool.into(),
            dir: dir.into(),
            before: None,
            steps: 0,
            unchanged: 0,
            functions: 0,
            deletions: 0,
            time: Duration::ZERO,
        }
    }

    /// One line for `--stats`.
    pub fn summary(&self) -> String {
        format!(
            "check-dce: {} steps accepted by Fir.Dce.checkFunc ({} function pairs, {} deletions; {} \
             steps deleted nothing), {:.3} ms",
            self.steps,
            self.functions,
            self.deletions,
            self.unchanged,
            self.time.as_secs_f64() * 1e3
        )
    }
}

/// What `fir-ref check-dce` prints when it accepts `src` → `tgt`.
pub fn receipt(src: &Module, tgt: &Module) -> String {
    format!(
        "ok {}\nsource:\n{}target:\n{}",
        src.funcs.len(),
        src.render(true),
        tgt.render(true)
    )
}

/// Run `fir-ref check-dce` on `src` → `tgt`; the number of functions accepted, or why not.
pub fn check_dce(
    tool: &Path,
    dir: &Path,
    name: &str,
    src: &Module,
    tgt: &Module,
) -> Result<u64, String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let (s, t) = (
        dir.join(format!("{name}.src.fir")),
        dir.join(format!("{name}.tgt.fir")),
    );
    let (src_text, tgt_text) = (src.render(true), tgt.render(true));
    std::fs::write(&s, &src_text).map_err(|e| format!("{}: {e}", s.display()))?;
    std::fs::write(&t, &tgt_text).map_err(|e| format!("{}: {e}", t.display()))?;
    let out = Command::new(tool)
        .arg("check-dce")
        .arg(&s)
        .arg(&t)
        .output()
        .map_err(|e| format!("running {}: {e}", tool.display()))?;
    if !out.status.success() {
        return Err(format!(
            "the proved checker (fir-ref check-dce) refused it: {} (snapshots kept: {}, {})",
            String::from_utf8_lossy(&out.stderr).trim(),
            s.display(),
            t.display()
        ));
    }
    if out.stdout != receipt(src, tgt).as_bytes() {
        return Err(format!(
            "fir-ref check-dce accepted, but its receipt doesn't match the modules submitted \
             (snapshots kept: {}, {})",
            s.display(),
            t.display()
        ));
    }
    let _ = std::fs::remove_file(&s);
    let _ = std::fs::remove_file(&t);
    Ok(src.funcs.len() as u64)
}

impl Observer for CheckDce {
    fn before(&mut self, pass: &Pass, _round: u32, m: &Module) {
        if pass.name == "dce" {
            self.before = Some(m.clone());
        }
    }

    fn after(&mut self, pass: &Pass, round: u32, changes: u32, m: &Module) -> Result<(), String> {
        if pass.name != "dce" {
            return Ok(());
        }
        let src = self
            .before
            .take()
            .ok_or("check-dce: no snapshot before dce")?;
        let start = Instant::now();
        // A pass's own count isn't trusted: "nothing deleted" must mean the module is unchanged,
        // compared as the text the checker would have been given.
        if changes == 0 && src.render(true) == m.render(true) {
            self.unchanged += 1;
            self.time += start.elapsed();
            return Ok(());
        }
        let name = format!("dce-{}-r{round}-s{}", std::process::id(), self.steps);
        let r = check_dce(&self.tool, &self.dir, &name, &src, m);
        self.time += start.elapsed();
        self.functions += r?;
        self.steps += 1;
        self.deletions += u64::from(changes);
        Ok(())
    }
}
