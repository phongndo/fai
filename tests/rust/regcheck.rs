//! The register allocation validator (`fir::backend::aarch64::regcheck::validate`), against
//! corrupted allocations and corrupted output code: each must be refused, for the reason the
//! corruption introduces. The honest allocation of the same functions is accepted.
//!
//! The function under test keeps 32 values live across a call and a join, so it spills, uses
//! callee-saved registers (whose saves and restores the frame lowering adds), and has a far
//! frame. Integration tests through every fixture and random program are in `tests/aarch64.rs`
//! (every allocation there is validated, in every build).

#[allow(dead_code)]
mod common;

use a64::mir::{Inst, MFunc};
use a64::regalloc::{Assignment, Home};
use fir::Reg;
use fir::backend::aarch64 as a64;

use common::evidence::Evidence;

/// 32 values live across a call and a `cf.if`, then summed.
fn source() -> String {
    let mut s = String::from(
        "extern func @g(i64) -> i64 effects[] assume\n\nfunc @f(%x: i64, %c: i1) -> i64 {\n",
    );
    for k in 0..32 {
        s += &format!(
            "  %k{k}: i64 = int.const {}\n  %a{k}: i64 = int.add.wrap %x, %k{k}\n",
            k + 1
        );
    }
    s += "  %r: i64 = func.call @g(%x)\n";
    s += "  %y: i64 = cf.if %c {\n    %t: i64 = int.add.wrap %a0, %r\n    cf.yield %t\n  } else {\n    cf.yield %a1\n  }\n";
    s += "  %s0: i64 = int.add.wrap %y, %a2\n";
    for k in 3..32 {
        s += &format!("  %s{}: i64 = int.add.wrap %s{}, %a{k}\n", k - 2, k - 3);
    }
    s += "  func.ret %s29\n}\n";
    s
}

struct Fixture {
    m: fir::Module,
    input: MFunc,
    shapes: Vec<a64::abi::CallShape>,
}

fn fixture() -> Fixture {
    let m = fir::parse_module(&source()).unwrap();
    fir::verify_module(&m).unwrap();
    let mm = a64::select(&m).unwrap();
    Fixture {
        shapes: a64::shapes(&m),
        input: mm.funcs[0].clone(),
        m,
    }
}

impl Fixture {
    fn honest(&self) -> (Assignment, MFunc) {
        let a = a64::regalloc::assignment(&self.input, &self.shapes, &self.shapes[0]);
        let mut out = self.input.clone();
        a64::regalloc::apply_assignment(&mut out, &self.shapes, &self.shapes[0], &a).unwrap();
        (a, out)
    }

    fn validate(&self, out: &MFunc) -> Result<(), String> {
        a64::regcheck::validate(
            &mut self.input.clone(),
            out.clone(),
            &self.shapes,
            &self.shapes[0],
        )
        .map(|_| ())
    }

    fn with_assignment(&self, a: &Assignment) -> Result<(), String> {
        let mut out = self.input.clone();
        a64::regalloc::apply_assignment(&mut out, &self.shapes, &self.shapes[0], a)
    }
}

/// The first output instruction matching `p`.
fn find(out: &MFunc, p: impl Fn(&Inst) -> bool) -> usize {
    out.insts.iter().position(p).expect("no such instruction")
}

fn refused(r: Result<(), String>, why: &str, ev: &Evidence, what: &str) {
    let e = r.expect_err(what);
    assert!(
        e.contains(why),
        "{what}: refused, but not because {why:?}: {e}"
    );
    ev.count("corruptions refused", 1);
    ev.count(format!("refused: {what}"), 1);
}

#[test]
fn honest_allocation_is_accepted() {
    let f = fixture();
    let (a, out) = f.honest();
    assert!(a.slots > 0, "the fixture should spill");
    assert!(
        out.frame.saved != 0,
        "the fixture should use callee-saved registers"
    );
    assert!(f.validate(&out).is_ok());
    // And it runs as the source does.
    let mut mm = a64::select(&f.m).unwrap();
    a64::allocate(&f.m, &mut mm).unwrap();
    let lm = a64::lfir::to_module(&f.m, &mm);
    for c in ["0", "1"] {
        let want = fir::interp::run(&f.m, "f", &["5", c], 100_000).unwrap();
        assert_eq!(
            fir::interp::run(&lm, "f", &["5", c], 10_000_000).unwrap(),
            want
        );
    }
}

#[test]
fn unused_virtual_registers_need_no_assignment() {
    let f = fixture();
    let mut input = f.input;
    // Selection may reserve virtual registers that no emitted instruction names.
    input.nvregs += 1;
    let a = a64::regalloc::assignment(&input, &f.shapes, &f.shapes[0]);
    assert_eq!(a.homes.last(), Some(&Home::Slot(u32::MAX)));
    a64::regalloc::apply_assignment(&mut input, &f.shapes, &f.shapes[0], &a).unwrap();
}

#[test]
fn elided_moves_may_have_different_source_locations() {
    let m = fir::parse_module(
        "func @f(%a: i8, %b: i32) -> (i32, i8) {
  %x: i8 = copy %a @1:1
  %y: i32 = copy %b @2:2
  func.ret %y, %x @3:3
}",
    )
    .unwrap();
    fir::verify_module(&m).unwrap();
    let mut mm = a64::select(&m).unwrap();
    a64::allocate(&m, &mut mm).unwrap();
}

#[test]
fn validation_keeps_function_identity_and_call_context() {
    let f = fixture();
    let (_, out) = f.honest();
    let mut wrong_function = out.clone();
    wrong_function.index += 1;
    assert!(
        f.validate(&wrong_function)
            .unwrap_err()
            .contains("different function index")
    );
    let mut wrong_signature = out.clone();
    wrong_signature.sigs.push((vec![fir::Ty::Int(64)], vec![]));
    assert!(
        f.validate(&wrong_signature)
            .unwrap_err()
            .contains("indirect-call signatures changed")
    );
    let mut wrong_frame = out.clone();
    wrong_frame.frame.locals += 16;
    assert!(
        f.validate(&wrong_frame)
            .unwrap_err()
            .contains("frame layout")
    );
    let mut wrong_loc = out.clone();
    let i = find(&wrong_loc, |i| matches!(i, Inst::Bl { .. }));
    wrong_loc.locs[i] = Some(fir::Loc { line: 900, col: 1 });
    assert!(
        f.validate(&wrong_loc)
            .unwrap_err()
            .contains("source location changed")
    );

    let mut input = f.input.clone();
    let before = format!("{input:?}");
    // Cancelled approvals and rejected proposals both leave the original code intact.
    drop(a64::regcheck::validate(&mut input, out, &f.shapes, &f.shapes[0]).unwrap());
    assert_eq!(format!("{input:?}"), before);
    let mut a = a64::regalloc::assignment(&input, &f.shapes, &f.shapes[0]);
    a.homes.pop();
    assert!(
        a64::regalloc::apply_assignment(&mut input, &f.shapes, &f.shapes[0], &a)
            .unwrap_err()
            .contains("homes for")
    );
    assert_eq!(format!("{input:?}"), before);
    let honest = a64::regalloc::assignment(&input, &f.shapes, &f.shapes[0]);
    for (home, why) in [
        (Home::Reg(Reg::x(29)), "which it may not have"),
        (Home::Slot(honest.slots), "but there are"),
        (Home::Slot(u32::MAX), "but there are"),
    ] {
        let mut bad = honest.clone();
        bad.homes[0] = home;
        assert!(
            a64::regalloc::apply_assignment(&mut input, &f.shapes, &f.shapes[0], &bad)
                .unwrap_err()
                .contains(why)
        );
        assert_eq!(format!("{input:?}"), before);
    }
    let mut huge = honest;
    huge.slots = u32::MAX;
    assert!(
        a64::regalloc::apply_assignment(&mut input, &f.shapes, &f.shapes[0], &huge)
            .unwrap_err()
            .contains("slots for")
    );
    assert_eq!(format!("{input:?}"), before);
}

#[test]
fn corrupted_allocations_are_refused() {
    let ev = Evidence::new("regcheck_adversarial");
    let f = fixture();
    let (a, out) = f.honest();
    let regs: Vec<(usize, Reg)> = a
        .homes
        .iter()
        .enumerate()
        .filter_map(|(v, h)| match h {
            Home::Reg(r) => Some((v, *r)),
            Home::Slot(_) => None,
        })
        .collect();

    // Two values in the same register at once: the later write clobbers the earlier value.
    let mut bad = a.clone();
    let (v0, r0) = regs[0];
    let (v1, _) = *regs.iter().find(|(_, r)| *r != r0).unwrap();
    bad.homes[v1] = Home::Reg(r0);
    let _ = v0;
    refused(
        f.with_assignment(&bad),
        "reads",
        &ev,
        "two live values share a register",
    );

    // A value live across the call in a caller-saved register.
    let mut bad = a.clone();
    let cross = regs
        .iter()
        .find(|(_, r)| (19..=28).contains(&r.0))
        .expect("a callee-saved home")
        .0;
    bad.homes[cross] = Home::Reg(Reg::x(9));
    refused(
        f.with_assignment(&bad),
        "reads",
        &ev,
        "a value across a call in x9",
    );

    // A callee-saved register without its save: drop the frame's saves from the output.
    let mut o = out.clone();
    let save = find(
        &o,
        |i| matches!(i, Inst::Str { base, off, .. } if *base == Reg::FP && *off < 0),
    );
    o.insts.remove(save);
    o.locs.remove(save);
    for b in o.blocks.iter_mut().skip(1) {
        *b -= 1;
    }
    refused(
        f.validate(&o),
        "its value at entry",
        &ev,
        "a callee-saved register not saved",
    );

    // A spill store dropped: the reload finds nothing.
    let mut o = out.clone();
    // Spill code goes through the scratch registers x15 and x17.
    let scratch = |r: &Reg| *r == Reg::x(15) || *r == Reg::x(17);
    let st = find(
        &o,
        |i| matches!(i, Inst::Str { s, base, .. } if *base == Reg::SP && scratch(s)),
    );
    o.insts.remove(st);
    o.locs.remove(st);
    for b in o.blocks.iter_mut() {
        if *b as usize > st {
            *b -= 1;
        }
    }
    refused(f.validate(&o), "reads", &ev, "a spill store left out");

    // A reload from the wrong slot.
    let mut o = out.clone();
    let ld = find(
        &o,
        |i| matches!(i, Inst::Ldr { d, base, .. } if *base == Reg::SP && scratch(d)),
    );
    if let Inst::Ldr { off, .. } = &mut o.insts[ld] {
        *off += 8;
    }
    refused(f.validate(&o), "reads", &ev, "a reload from the wrong slot");

    // An operand renamed to a register that holds something else.
    let mut o = out.clone();
    let add = find(&o, |i| matches!(i, Inst::Alu { .. }));
    if let Inst::Alu { m, n, .. } = &mut o.insts[add] {
        *m = if *m == Reg::x(3) {
            Reg::x(4)
        } else {
            Reg::x(3)
        };
        let _ = n;
    }
    refused(
        f.validate(&o),
        "reads",
        &ev,
        "an operand from the wrong register",
    );

    // Bad output code: an opcode or an immediate changed.
    let mut o = out.clone();
    if let Inst::Alu { op, .. } = &mut o.insts[add] {
        *op = fir::AluOp::Sub;
    }
    refused(
        f.validate(&o),
        "has no counterpart",
        &ev,
        "an add became a sub",
    );
    let mut o = out.clone();
    let k = find(&o, |i| matches!(i, Inst::MovWide { d, .. } if d.0 != 16));
    if let Inst::MovWide { imm, .. } = &mut o.insts[k] {
        *imm ^= 1;
    }
    refused(
        f.validate(&o),
        "has no counterpart",
        &ev,
        "a constant changed",
    );

    // A frame too small for the spill slots.
    let mut o = out.clone();
    let sub = find(
        &o,
        |i| matches!(i, Inst::AluImm { op: fir::AluImmOp::Sub, d, n, imm, .. } if *d == Reg::SP && *n == Reg::SP && *imm > 16),
    );
    if let Inst::AluImm { imm, .. } = &mut o.insts[sub] {
        *imm -= 16;
    }
    refused(f.validate(&o), "the frame is", &ev, "a frame too small");

    // An instruction the input doesn't have.
    let mut o = out.clone();
    let at = find(&o, |i| matches!(i, Inst::Ret));
    o.insts.insert(
        at,
        Inst::Mov {
            sf: fir::Sf::X,
            d: Reg::x(0),
            n: Reg::x(1),
        },
    );
    o.locs.insert(at, None);
    refused(f.validate(&o), "", &ev, "an extra instruction");

    // A branch retargeted.
    let mut o = out.clone();
    let br = find(&o, |i| matches!(i, Inst::BCond { .. }));
    if let Inst::BCond { t, f: e, .. } = &mut o.insts[br] {
        std::mem::swap(t, e);
    }
    refused(
        f.validate(&o),
        "BCond { c: Ne, t: 1, f: 2 }) has no counterpart",
        &ev,
        "a branch retargeted",
    );
    ev.write();
}
