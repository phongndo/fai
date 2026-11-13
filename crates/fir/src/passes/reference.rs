//! Running the proved Lean DCE checker on the real pipeline's output.
//!
//! [`CheckDce`] is a pipeline [`Observer`]: before each run of `dce` it snapshots the module, and
//! after it writes both snapshots out and runs `fir-ref check-dce SRC TGT`, which accepts only
//! if `Fir.Dce.checkModule` does. `Fir.Dce.checkModule_sound` says that, on acceptance, the two modules
//! have functions by the same names, and each target function refines the source function of
//! its name *in the source module*, provided the source function is `Func.Decided` there (no run
//! reaches a choice the reference semantics leaves open, such as an address that may belong to
//! two allocations). Nothing checks `Decided`. The per-function checker is `Fir.Dce.checkFuncL`,
//! linear in a function's size times its nesting depth and proved equal to `Fir.Dce.checkFunc` (`checkFuncL_eq`).
//!
//! The checker's receipt (`ok N`, then both modules as Lean parsed and printed them) must match
//! the snapshots byte for byte, so an acceptance can't be about other text: the Rust printer and
//! the Lean parser are in the trusted base, and the match checks that they agree on these
//! modules. This is what `tests/dce_check.rs` does in the tests, here available for any input:
//! `fir opt --check-dce FIR-REF`, `fir compile -O --check-dce FIR-REF`, `fai-cc -O --check-dce
//! FIR-REF`, and any optimized compilation through [`crate::backend::optimize`] (the C API
//! included) when [`ENV`] names a `fir-ref`. It validates each DCE step of this run; it says
//! nothing about the other passes, about composing per-function refinements across a module's
//! calls, or about steps of other runs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use super::{Observer, Pass};
use crate::ir::Module;

/// The environment variable that turns the checker on for every optimized compilation
/// ([`crate::backend::optimize`]): the path of the `fir-ref` to run.
pub const ENV: &str = "FIR_CHECK_DCE";

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

    /// Check with the `fir-ref` at `tool`, writing snapshots into a directory this creates, new
    /// and (on Unix) private to the user, in the system's temporary directory;
    /// [`CheckDce::finish`] removes it if every step was accepted. An error if `tool` is not an
    /// executable file, so a mistyped path fails even when no step deletes anything (whether it
    /// is a working `fir-ref` shows only when a step is sent to it).
    pub fn in_temp_dir(tool: impl Into<PathBuf>) -> Result<CheckDce, String> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let tool = tool.into();
        if !is_executable(&tool) {
            return Err(format!(
                "the proved DCE checker: no executable fir-ref at {}",
                tool.display()
            ));
        }
        // Created, not reused: a directory someone else made at the same name is never
        // written into.
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos());
        for _ in 0..100 {
            let dir = std::env::temp_dir().join(format!(
                "fir-check-dce-{}-{}-{nanos:08x}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut b = std::fs::DirBuilder::new();
            #[cfg(unix)]
            std::os::unix::fs::DirBuilderExt::mode(&mut b, 0o700);
            match b.create(&dir) {
                Ok(()) => return Ok(CheckDce::new(tool, dir)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(format!("{}: {e}", dir.display())),
            }
        }
        Err("the proved DCE checker: no fresh snapshot directory".to_owned())
    }

    /// The checker [`ENV`] asks for, if it is set (and not empty).
    pub fn from_env() -> Result<Option<CheckDce>, String> {
        match std::env::var_os(ENV).filter(|t| !t.is_empty()) {
            None => Ok(None),
            Some(t) => CheckDce::in_temp_dir(t)
                .map(Some)
                .map_err(|e| format!("{ENV}: {e}")),
        }
    }

    /// Remove the snapshot directory if it is empty (a refused step's snapshots stay).
    pub fn finish(&self) {
        let _ = std::fs::remove_dir(&self.dir);
    }

    /// One line for `--stats`.
    pub fn summary(&self) -> String {
        format!(
            "check-dce: {} steps accepted by Fir.Dce.checkModule ({} function pairs, {} deletions; {} \
             steps deleted nothing), {:.3} ms",
            self.steps,
            self.functions,
            self.deletions,
            self.unchanged,
            self.time.as_secs_f64() * 1e3
        )
    }
}

fn is_executable(p: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::metadata(p).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        p.is_file()
    }
}

/// Write `text` to a new file at `p`: whatever was there (a file, or a symlink, which is removed
/// rather than followed) is replaced, and the file is created exclusively, so the write can't land
/// anywhere but `p`.
fn write_new(p: &Path, text: &str) -> Result<(), String> {
    use std::io::Write as _;
    match std::fs::remove_file(p) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
            return Err(format!("{}: {e}", p.display()));
        }
        _ => {}
    }
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(p)
        .and_then(|mut f| f.write_all(text.as_bytes()))
        .map_err(|e| format!("{}: {e}", p.display()))
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
    write_new(&s, &src_text)?;
    write_new(&t, &tgt_text)?;
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
