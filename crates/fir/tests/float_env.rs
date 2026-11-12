//! The interpreter's floats don't depend on the calling thread's floating-point environment: a
//! C caller of the C API may have set another rounding mode (`fesetround`) or flushing of
//! subnormals (x86-64's MXCSR FTZ and DAZ, AArch64's FPCR FZ). Every `// run:` line of
//! `tests/float/` must still give its expected outcome when the library parses, verifies, and runs
//! it with rounding toward +∞ and subnormals flushed to zero, as must the two cases where host
//! arithmetic went wrong.
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

// This test uses only part of the shared helpers.
#[allow(dead_code)]
mod common;

use std::hint::black_box;

use common::{display_name, fir_files};

#[cfg(target_arch = "x86_64")]
mod env {
    use std::arch::asm;

    pub type Word = u32;

    pub fn get() -> Word {
        let mut x: Word = 0;
        unsafe { asm!("stmxcsr [{}]", in(reg) &mut x, options(nostack)) };
        x
    }

    pub fn set(x: Word) {
        unsafe { asm!("ldmxcsr [{}]", in(reg) &x, options(nostack)) };
    }

    /// MXCSR: rounding control toward +∞ (bits 14:13 = 10), FTZ (bit 15), and DAZ (bit 6).
    pub fn hostile(x: Word) -> Word {
        (x & !(3 << 13)) | (2 << 13) | (1 << 15) | (1 << 6)
    }
}

#[cfg(target_arch = "aarch64")]
mod env {
    use std::arch::asm;

    pub type Word = u64;

    pub fn get() -> Word {
        let x: Word;
        unsafe { asm!("mrs {}, fpcr", out(reg) x, options(nostack)) };
        x
    }

    pub fn set(x: Word) {
        unsafe { asm!("msr fpcr, {}", in(reg) x, options(nostack)) };
    }

    /// FPCR: RMode toward +∞ (bits 23:22 = 01) and FZ (bit 24), which flushes subnormal inputs
    /// and results.
    pub fn hostile(x: Word) -> Word {
        (x & !(3 << 22)) | (1 << 22) | (1 << 24)
    }
}

/// Run `f` with rounding toward +∞ and subnormals flushed, restoring the environment afterwards
/// (also on a panic).
fn hostile<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(env::Word);
    impl Drop for Restore {
        fn drop(&mut self) {
            env::set(self.0);
        }
    }
    let saved = env::get();
    let _restore = Restore(saved);
    env::set(env::hostile(saved));
    f()
}

/// The host's `1 + 2^-24` (a tie, so 1 when rounding to nearest) and the sum of two smallest
/// subnormals (2 units), in whatever environment is current.
#[inline(never)]
fn host_sums() -> (u32, u32) {
    let tie = black_box(1.0f32) + black_box(f32::from_bits(0x3380_0000)); // 2^-24
    let tiny = black_box(f32::from_bits(1)) + black_box(f32::from_bits(1));
    black_box((tie.to_bits(), tiny.to_bits()))
}

/// The `// run: @f(ARGS) -> OUTCOME` lines of a file.
fn run_lines(text: &str) -> Vec<(String, Vec<String>, String)> {
    text.lines()
        .filter_map(|l| l.trim().strip_prefix("// run:"))
        .map(|body| {
            let (call, want) = body.split_once(" -> ").unwrap();
            let (name, rest) = call.trim()[1..].split_once('(').unwrap();
            let inner = rest.strip_suffix(')').unwrap();
            let args = inner
                .split(',')
                .map(|a| a.trim().to_owned())
                .filter(|a| !a.is_empty())
                .collect();
            (name.to_owned(), args, want.trim().to_owned())
        })
        .collect()
}

fn run(text: &str, name: &str, args: &[String]) -> String {
    let m = fir::parse_module(text).unwrap();
    fir::verify_module(&m).unwrap();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    fir::interp::run(&m, name, &args, fir::interp::DEFAULT_FUEL).unwrap_or_else(|e| e)
}

const REPORTED: &str = "
func @add32(%a: f32, %b: f32) -> f32 {
  %r: f32 = float.add %a, %b
  func.ret %r
}
";

#[test]
fn floats_ignore_the_host_environment() {
    // The environment really is changed: the host's own sums come out differently.
    assert_eq!(host_sums(), (0x3f80_0000, 2));
    assert_eq!(hostile(host_sums), (0x3f80_0001, 0));
    assert_eq!(
        host_sums(),
        (0x3f80_0000, 2),
        "the environment was restored"
    );

    let reported = hostile(|| {
        [
            run(
                REPORTED,
                "add32",
                &["1.0".into(), "5.960464477539063e-8".into()],
            ),
            run(REPORTED, "add32", &["1e-45".into(), "1e-45".into()]),
        ]
    });
    assert_eq!(
        reported,
        ["returned f32 1.0", "returned f32 3e-45"],
        "1 + 2^-24 is a tie down to 1; two smallest subnormals make two units"
    );

    let mut checked = 0;
    let mut fails = Vec::new();
    for file in fir_files() {
        if !file.components().any(|c| c.as_os_str() == "float") {
            continue;
        }
        let text = std::fs::read_to_string(&file).unwrap();
        let lines = run_lines(&text);
        let got: Vec<String> = hostile(|| {
            lines
                .iter()
                .map(|(name, args, _)| run(&text, name, args))
                .collect()
        });
        for ((name, args, want), got) in lines.iter().zip(got) {
            checked += 1;
            if got != *want {
                fails.push(format!(
                    "{}: @{name}({}): got {got}, want {want}",
                    display_name(&file),
                    args.join(", ")
                ));
            }
        }
    }
    assert!(checked > 100, "only {checked} run lines under tests/float");
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
