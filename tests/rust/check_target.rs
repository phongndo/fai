//! `fir check FILE --target T` says whether `fir compile` for the target accepts the module.
//!
//! A layer's verifier doesn't promise that the next stage takes what it accepts: MFIR's allows
//! any integer width, and the AArch64 backend refuses most above 64 bits. So the check for a
//! target is not a second rule kept in step with the backend. It is the backend's own lowering,
//! selection, and allocation, short of writing the assembly (`aarch64::check`). This test holds
//! it to that on every `.fir` file under `tests/` that verifies, for both targets: the two
//! commands succeed together or fail together, and a refusal is in the same words.

#[allow(dead_code)]
mod common;

use std::path::Path;
use std::process::{Command, Output};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};

use common::{display_name, fir_files};

/// The command's first line on stderr, without the file's name.
fn refusal(out: &Output, file: &Path) -> String {
    let err = String::from_utf8_lossy(&out.stderr);
    let line = err.lines().next().unwrap_or("");
    line.strip_prefix(&format!("{}: ", file.display()))
        .unwrap_or(line)
        .to_owned()
}

#[test]
fn check_for_a_target_says_what_compile_says() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let files = fir_files();
    let fails = Mutex::new(Vec::new());
    let (accepted, refused) = (AtomicU64::new(0), AtomicU64::new(0));
    let next = AtomicUsize::new(0);
    let one = |file: &Path| {
        let name = display_name(file);
        let Ok(text) = std::fs::read_to_string(file) else {
            return;
        };
        // Only modules that verify: for the others both commands report the same error first.
        let Ok(m) = fir::parse_module(&text) else {
            return;
        };
        if fir::verify_module(&m).is_err() {
            return;
        }
        for target in ["aarch64", "x86_64"] {
            let run = |args: &[&str]| {
                Command::new(fir)
                    .arg(args[0])
                    .arg(file)
                    .args(&args[1..])
                    .output()
                    .expect("running fir")
            };
            let check = run(&["check", "--target", target]);
            let compile = run(&[
                "compile",
                "--target",
                target,
                "--emit",
                "asm",
                "-o",
                "/dev/null",
            ]);
            if check.status.success() != compile.status.success() {
                fails.lock().unwrap().push(format!(
                    "{name} for {target}: fir check {} it, and fir compile {} it\n  check: {}\n  compile: {}",
                    if check.status.success() { "accepts" } else { "refuses" },
                    if compile.status.success() { "accepts" } else { "refuses" },
                    refusal(&check, file),
                    refusal(&compile, file),
                ));
            } else if check.status.success() {
                accepted.fetch_add(1, Relaxed);
            } else {
                if refusal(&check, file) != refusal(&compile, file) {
                    fails.lock().unwrap().push(format!(
                        "{name} for {target}: refused in other words\n  check: {}\n  compile: {}",
                        refusal(&check, file),
                        refusal(&compile, file),
                    ));
                }
                refused.fetch_add(1, Relaxed);
            }
        }
    };
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let Some(file) = files.get(next.fetch_add(1, Relaxed)) else {
                        return;
                    };
                    one(file);
                }
            });
        }
    });
    let mut fails = fails.into_inner().unwrap();
    fails.sort();
    let (accepted, refused) = (accepted.into_inner(), refused.into_inner());
    let ev = common::evidence::Evidence::new("check_target");
    ev.count("modules the check and the compile both accept", accepted);
    ev.count("modules the check and the compile both refuse", refused);
    ev.count("failures", fails.len() as u64);
    ev.write();
    // Both answers must have come up, or the comparison says nothing.
    assert!(
        accepted > 0 && refused > 0,
        "{accepted} accepted, {refused} refused"
    );
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

/// The case the layer audit found: checked addition on `i64` verifies, lowers to `i65`
/// arithmetic, and no backend takes that. The check for a target refuses it, and a note names
/// the op the source wrote, which the refusal (about `i65`) can't.
#[test]
fn a_wide_integer_from_lowering_is_refused_at_the_check_with_the_op_named() {
    let fir = Path::new(env!("CARGO_BIN_EXE_fir"));
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("check-target");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("overflow64.fir");
    std::fs::write(
        &file,
        "func @f(%a: i64, %b: i64) -> (i64, i1) {\n  \
           %s: i64, %o: i1 = int.add.overflow.s %a, %b @2:3\n  func.ret %s, %o\n}\n",
    )
    .unwrap();
    let run = |args: &[&str]| {
        Command::new(fir)
            .arg("check")
            .arg(&file)
            .args(args)
            .output()
            .unwrap()
    };
    // It is a good HFIR module.
    let plain = run(&[]);
    assert!(plain.status.success(), "{plain:?}");
    for (target, backend) in [("aarch64", "AArch64"), ("x86_64", "x86-64")] {
        let out = run(&["--target", target]);
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(!out.status.success(), "{target}: {err}");
        assert!(
            err.contains(&format!(
                "i65 is wider than 64 bits, which the {backend} backend doesn't support yet"
            )),
            "{target}: {err}"
        );
        assert!(
            err.contains(
                "note: @f: @2:3: int.add.overflow.s on i64 is lowered to arithmetic on i65"
            ),
            "{target}: {err}"
        );
    }
}
