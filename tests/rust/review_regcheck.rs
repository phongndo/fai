//! Allocation-validator counterexamples found in review (at 326b0d4), kept as regressions: each
//! plants code the validator once accepted, shows natively or in the interpreter that the code is
//! wrong (where that takes the AArch64 toolchain, only when it is available; required under
//! `FIR_REQUIRE_FULL=1`), and requires the validator to refuse it. One is a valid frame it once
//! refused.

#[allow(dead_code)]
mod common;

use fir::backend::aarch64::{self as a64, mir::Inst, mir::MFunc};
use fir::{AluImmOp, AluOp, MemSize, MovOp, Reg, Sf};

fn fixture(src: &str) -> (fir::Module, MFunc, MFunc, Vec<a64::abi::CallShape>) {
    let m = fir::parse_module(src).unwrap();
    fir::verify_module(&m).unwrap();
    let mut mm = a64::select(&m).unwrap();
    let input = mm.funcs[0].clone();
    let shapes = a64::shapes(&m);
    a64::allocate(&m, &mut mm).unwrap();
    (m, input, mm.funcs.remove(0), shapes)
}

fn insert(f: &mut MFunc, at: usize, insts: &[Inst]) {
    f.insts.splice(at..at, insts.iter().copied());
    f.locs.splice(at..at, vec![None; insts.len()]);
    for b in f.blocks.iter_mut().skip(1) {
        if *b as usize > at {
            *b += insts.len() as u32;
        }
    }
}

fn sub_sp(imm: i64) -> Inst {
    Inst::AluImm {
        op: AluImmOp::Sub,
        sf: Sf::X,
        d: Reg::SP,
        n: Reg::SP,
        imm,
    }
}

/// The native run's status is `want`, when there was a native run.
macro_rules! assert_native {
    ($got:expr, $want:expr $(, $msg:expr)? $(,)?) => {
        if let Some(got) = $got {
            assert_eq!(got, $want $(, "{}", $msg)?);
        }
    };
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The exit status of `f` linked with `harness` and run on AArch64 (under qemu off AArch64), or
/// `None` without a toolchain (a failure when a full run is required).
fn native_status(m: &fir::Module, f: MFunc, harness: &str, name: &str) -> Option<i32> {
    use std::process::Command;
    let native = cfg!(target_arch = "aarch64");
    let (cc, runner) = if native {
        ("cc", None)
    } else {
        ("aarch64-unknown-linux-gnu-cc", Some("qemu-aarch64"))
    };
    if !on_path(cc) || runner.is_some_and(|r| !on_path(r)) {
        common::evidence::require("the review regressions' native runs need the AArch64 toolchain");
        return None;
    }
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    let asm = a64::emit::emit(
        m,
        &a64::mir::MModule {
            funcs: vec![f],
            ..Default::default()
        },
        &a64::Options::default(),
    );
    let source = dir.join("test.s");
    let bin = dir.join("test");
    std::fs::write(&source, asm + harness).unwrap();
    let built = Command::new(cc)
        .arg(&source)
        .arg("-o")
        .arg(&bin)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ran = match runner {
        Some(r) => Command::new(r).arg(&bin).output().unwrap(),
        None => Command::new(&bin).output().unwrap(),
    };
    let status = ran.status.code().unwrap_or(-1);
    std::fs::remove_dir_all(dir).unwrap();
    Some(status)
}

#[test]
fn review_reject_overlapping_save_slots() {
    let (m, mut input, mut out, shapes) = fixture("func @f(%x: i64) -> i64 { func.ret %x }");
    let harness = "\n.text\n.global main\nmain:\n stp x29, x30, [sp, #-32]!\n stp x19, x20, [sp, #16]\n mov x19, #0x1122\n mov x20, #0x3344\n mov x0, #7\n bl f\n mov x1, #0x1122\n cmp x19, x1\n cset w0, ne\n ldp x19, x20, [sp, #16]\n ldp x29, x30, [sp], #32\n ret\n";
    assert_native!(
        native_status(&m, out.clone(), harness, "review-save-control"),
        0,
    );
    // Save slots -8 and -9 overlap in seven bytes, but the validator treats them as independent.
    let at = input.frame.alloc_at as usize;
    insert(
        &mut out,
        at,
        &[
            sub_sp(32),
            Inst::Str {
                size: MemSize::X,
                s: Reg::x(19),
                base: Reg::FP,
                off: -8,
            },
            Inst::Str {
                size: MemSize::X,
                s: Reg::x(20),
                base: Reg::FP,
                off: -9,
            },
        ],
    );
    let at = out
        .insts
        .iter()
        .position(|i| {
            *i == Inst::Mov {
                sf: Sf::X,
                d: Reg::SP,
                n: Reg::FP,
            }
        })
        .unwrap();
    insert(
        &mut out,
        at,
        &[
            Inst::Ldr {
                size: MemSize::X,
                d: Reg::x(19),
                base: Reg::FP,
                off: -8,
            },
            Inst::Ldr {
                size: MemSize::X,
                d: Reg::x(20),
                base: Reg::FP,
                off: -9,
            },
        ],
    );
    assert_native!(
        native_status(&m, out.clone(), harness, "review-save-corruption"),
        1,
        "x19 must actually be corrupted",
    );
    let e = a64::regcheck::validate(&mut input, out, &shapes, &shapes[0]).unwrap_err();
    assert!(e.contains("isn't an aligned 8-byte slot"), "{e}");
}

#[test]
fn review_reject_realign_without_sp_snapshot() {
    let (m, mut input, mut out, shapes) = fixture(
        "func @f(%x: i64) -> i64 { %p: ptr = mem.stack 8, align 8\n mem.store i64 %x, %p, align 8\n %y: i64 = mem.load %p, align 8\n func.ret %y }",
    );
    let at = input.frame.alloc_at as usize;
    insert(
        &mut out,
        at,
        &[
            sub_sp(16),
            // x16 was never set to sp, so this can move sp anywhere.
            Inst::AluImm {
                op: AluImmOp::And,
                sf: Sf::X,
                d: Reg::SP,
                n: Reg::x(16),
                imm: -16,
            },
        ],
    );
    let mm = a64::mir::MModule {
        funcs: vec![out.clone()],
        ..Default::default()
    };
    let lm = a64::lfir::to_module(&m, &mm);
    let got = fir::interp::run(&lm, "f", &["7"], 1000).unwrap();
    eprintln!("invalid frame run: {got}");
    assert_ne!(got, "returned i64 7");
    let e = a64::regcheck::validate(&mut input, out, &shapes, &shapes[0]).unwrap_err();
    assert!(e.contains("x16 that isn't a snapshot of sp"), "{e}");
}

#[test]
fn review_accept_large_valid_frame() {
    let m = fir::parse_module("func @f() { %p: ptr = mem.stack 16777216, align 16\n func.ret }")
        .unwrap();
    fir::verify_module(&m).unwrap();
    let mut mm = a64::select(&m).unwrap();
    a64::allocate(&m, &mut mm).expect("a valid 16 MiB frame should allocate");
}

#[test]
fn review_reject_stale_x16_after_exception_pseudo() {
    let (m, mut input, mut out, shapes) = fixture("func @f(%p: ptr) { exn.throw %p }");
    let harness = "\n.text\n.global main\nmain:\n stp x29, x30, [sp, #-16]!\n mov x0, #0\n bl f\n adrp x1, __fir_exn\n ldr x0, [x1, :lo12:__fir_exn]\n cmp x0, #0\n cset w0, eq\n ldp x29, x30, [sp], #16\n ret\n";
    assert_native!(
        native_status(&m, out.clone(), harness, "review-exn-control"),
        0,
    );
    let at = input.frame.alloc_at as usize;
    insert(
        &mut out,
        at,
        &[
            sub_sp(16),
            Inst::Str {
                size: MemSize::X,
                s: Reg::x(0),
                base: Reg::SP,
                off: 0,
            },
            Inst::MovWide {
                op: MovOp::Movz,
                sf: Sf::X,
                d: Reg::x(16),
                imm: 0,
                hw: 0,
            },
            Inst::Alu {
                op: AluOp::Add,
                sf: Sf::X,
                d: Reg::x(16),
                n: Reg::SP,
                m: Reg::x(16),
            },
        ],
    );
    let at = out
        .insts
        .iter()
        .position(|i| matches!(i, Inst::ExnSet { .. }))
        .unwrap()
        + 1;
    // The emitter implements ExnSet by replacing x16 with &__fir_exn. Reusing the old
    // stack address now overwrites the exception flag instead of a spill slot.
    insert(
        &mut out,
        at,
        &[Inst::Str {
            size: MemSize::X,
            s: Reg::x(0),
            base: Reg::x(16),
            off: 0,
        }],
    );
    assert_native!(
        native_status(&m, out.clone(), harness, "review-exn-corruption"),
        1,
    );
    let e = a64::regcheck::validate(&mut input, out, &shapes, &shapes[0]).unwrap_err();
    // With x16 clobbered by `aarch64.exn.set`, the store through it is no spill store.
    assert!(
        e.contains("Str { size: X, s: Reg(0), base: Reg(16), off: 0 }"),
        "{e}"
    );
}
