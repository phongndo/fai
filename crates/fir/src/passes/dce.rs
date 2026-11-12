//! Dead code elimination: `Fir.Dce.refines`.
//!
//! ```text
//! %y: T = copy %x                   // deleted: nothing reads %y
//! %z: T = int.add.wrap %a, %y       // deleted: nothing reads %z, so then nothing reads %y
//! ```
//!
//! The rewrite is `Dce.L`: a *pure* op (`Dce.Pure`) whose results no later op of its region
//! reads, at any depth, is deleted. In a verified function a value is read only after its
//! definition, where it is visible, so "no later op reads it" is "it has no uses". Deleted ops
//! don't count as readers (the theorem's "later" is in the target), so a chain of dead ops goes
//! in one run: deleting an op may leave its operands' definitions unread, and those are deleted
//! next, from a worklist.
//!
//! `Pure` asks for no regions, no call, no stack allocation, not a terminator, operands that are
//! all variables (no holes), and a computation that only reads the core and fails only by UB or
//! getting stuck (`ReadOnly`) for any operand values. `Dce.copy_pure`, `const_pure`, and
//! `poison_pure` prove it for copies, constants, and `poison`, and `Dce.float_pure` for the float
//! ops that can't trap: `float.const`, `float.add`/`sub`/`mul`/`div`/`copysign`,
//! `float.neg`/`abs`/`sqrt`, `float.fma`, `float.cmp`, `float.ext`, `float.trunc`,
//! `int.to_float`, `float.from_bits`, `float.to_bits`, and `float.to_int` unless it traps
//! (`.trap`; `.ub` is UB, which a deletion may remove). A NaN result reads the oracle's next
//! answer without using it up, so these only read the core. For the other ops below it is read
//! off Lean's `evalSimple` (no `choose`, no allocation, no address taken, no memory or scope
//! touched, no trap), not proved:
//!
//! * integer ops: `select`, `int.and`/`or`/`xor`, comparisons, `zext`/`sext`/`trunc`, and
//!   `int.add`/`sub`/`mul`, divisions, and shifts unless a modifier traps (`.trap`, a `.trap`
//!   edge);
//! * `ptr.null`, `ptr.offset`, `ptr.field`, `ptr.index` (`offsetBy` only reads the allocation);
//! * `ty.size`, `ty.align`, `ty.offset`, and `mem.global`;
//! * HFIR's building blocks that only build or take apart values: `agg.make`, `agg.extract`,
//!   `agg.insert`, `int.add`/`sub`/`mul.overflow.s`/`.u` (both results; `poison` in, `poison` out,
//!   never a trap), `union.make`, `union.tag`, `union.get.ub` (a wrong variant is UB, which a
//!   deletion may remove), `slice.make`, `slice.ptr`, and `slice.len`.
//!
//! Not pure: `freeze`, `ptr.cmp`, `ptr.addr`, `ptr.with_addr`, `ptr.from_exposed` (they ask the
//! oracle or give an allocation its address), `ptr.expose`, `func.addr` (it may create the
//! function object), loads (they record reads in `noalias` scopes and may expose pointers:
//! decision Pointer bytes as integers), and every op with an effect on memory or control. Of the
//! building blocks: `union.get.trap` (a wrong variant traps), `slice.get.ub`/`.trap` (a load,
//! and the `.trap` form traps out of bounds), `slice.set.*` (a store), and `cf.check.*` (a trap).

use crate::body::{Body, OpId, OperandKind, ValueDef};
use crate::ir::{CvtEdge, Edge, OpKind, Ovf, ShiftEdge};

use super::{Remarks, at, walk};

/// Whether ops of this kind compute their results from their operands and the core without
/// changing the core or trapping (Lean's `ReadOnly (evalSimple …)`), with no call, stack
/// allocation, or terminator.
pub fn pure_kind(k: OpKind) -> bool {
    match k {
        OpKind::Const(_)
        | OpKind::Poison
        | OpKind::Copy
        | OpKind::Select
        | OpKind::Bit(_)
        | OpKind::Cmp(_)
        | OpKind::Zext
        | OpKind::Sext
        | OpKind::Trunc(_)
        | OpKind::PtrNull
        | OpKind::PtrOffset { .. }
        | OpKind::PtrField { .. }
        | OpKind::PtrIndex { .. }
        | OpKind::TySize(_)
        | OpKind::TyAlign(_)
        | OpKind::TyOffset { .. }
        | OpKind::MemGlobal { .. }
        | OpKind::AggMake
        | OpKind::AggExtract { .. }
        | OpKind::AggInsert { .. }
        | OpKind::Overflow { .. }
        | OpKind::UnionMake { .. }
        | OpKind::UnionTag
        | OpKind::SliceMake
        | OpKind::SlicePtr
        | OpKind::SliceLen
        | OpKind::FloatConst { .. }
        | OpKind::FloatBin(_)
        | OpKind::FloatUn(_)
        | OpKind::FloatFma
        | OpKind::FloatCmp(_)
        | OpKind::FloatExt
        | OpKind::FloatTrunc
        | OpKind::IntToFloat { .. }
        | OpKind::FloatFromBits
        | OpKind::FloatToBits => true,
        OpKind::FloatToInt { edge, .. } => edge != CvtEdge::Trap,
        OpKind::UnionGet { trap, .. } => !trap,
        OpKind::Arith(_, ovf) => !matches!(ovf, Ovf::Trap(_)),
        OpKind::Div(_, zero, ovf) => zero != Edge::Trap && ovf != Edge::Trap,
        OpKind::Shift(_, edge) => edge != ShiftEdge::Trap,
        _ => false,
    }
}

/// Lean's `Dce.Pure`, for an op in a body.
pub fn is_pure(body: &Body, op: OpId) -> bool {
    pure_kind(body.kind(op))
        && body.regions(op).is_empty()
        && body
            .operands(op)
            .iter()
            .all(|o| matches!(o.get(), OperandKind::Value(_)))
}

/// Delete every pure op whose results nothing reads, and then those that only the deleted ops
/// read. Returns how many were deleted.
///
/// Uses are counted in one walk (use lists aren't needed); deleting an op takes one from each
/// of its operands' counts, and an op whose counts reach zero is deleted next. The ops are
/// erased together at the end.
pub fn run(body: &mut Body, remarks: &mut Remarks) -> u32 {
    let mut ops = Vec::new();
    walk(body, &mut ops);
    let mut uses = vec![0u32; body.num_values()];
    for &op in &ops {
        for o in body.operands(op) {
            if let OperandKind::Value(v) = o.get() {
                uses[v.index()] += 1;
            }
        }
    }
    let unread = |body: &Body, uses: &[u32], op: OpId| {
        is_pure(body, op) && body.results(op).all(|v| uses[v.index()] == 0)
    };
    // Popped from the end, so reversed to delete in program order.
    let mut work: Vec<OpId> = ops
        .iter()
        .rev()
        .copied()
        .filter(|&op| unread(body, &uses, op))
        .collect();
    let mut dead = vec![false; body.num_ops()];
    let mut erased = Vec::new();
    while let Some(op) = work.pop() {
        if std::mem::replace(&mut dead[op.index()], true) {
            continue;
        }
        erased.push(op);
        let l = body.loc(op);
        let k = body.kind(op);
        remarks.add("dce", (op, l), None, || {
            format!("deleted unused {} {}", k.mnemonic(), at(l))
        });
        for o in body.operands(op).iter().rev() {
            let OperandKind::Value(v) = o.get() else {
                continue;
            };
            uses[v.index()] -= 1;
            if let ValueDef::Result { op: d, .. } = body.def(v)
                && uses[v.index()] == 0
                && !dead[d.index()]
                && unread(body, &uses, d)
            {
                work.push(d);
            }
        }
    }
    body.erase_many(&erased);
    erased.len() as u32
}

#[cfg(test)]
mod tests {
    use super::super::test_util::{apply, canon};
    use super::*;

    #[test]
    fn deletes_chains_of_dead_pure_ops() {
        let src = "func @f(%x: i32, %p: ptr, %n: i64) -> i32 {
  %y: i32 = copy %x @1:3
  %one: i32 = int.const 1 @2:3
  %z: i32 = int.add.wrap %y, %one @3:3
  %q: ptr = ptr.offset.inbounds %p, %n @4:3
  %k: i1 = int.cmp.eq %z, %x @5:3
  func.ret %x @6:3
}
";
        let (n, out, remarks) = apply(src, run);
        assert_eq!(n, 5);
        assert_eq!(
            out,
            canon(
                "func @f(%x: i32, %p: ptr, %n: i64) -> i32 {
  func.ret %x
}
"
            )
        );
        assert_eq!(
            remarks,
            [
                "dce: deleted unused ptr.offset.inbounds @4:3",
                "dce: deleted unused int.cmp.eq @5:3",
                "dce: deleted unused int.add.wrap @3:3",
                "dce: deleted unused copy @1:3",
                "dce: deleted unused int.const @2:3"
            ]
        );
    }

    /// Ops that aren't pure stay even when unread: they trap, ask the oracle, touch memory, or
    /// read a hole.
    #[test]
    fn keeps_impure_ops() {
        let src = "func @f(%x: i32, %p: ptr) {
  %a: i32 = int.add.s.trap %x, %x
  %b: i32 = int.div.s.trap %x, %x
  %c: i32 = int.shl.trap %x, %x
  %d: i32 = freeze %x
  %e: i32 = mem.load %p, align 4
  %f: i1 = ptr.cmp.eq %p, %p
  %g: i64 = ptr.addr %p
  %h: i32 = copy ?h: i32
  %s: ptr = mem.stack 4, align 4
  %u: i32 = cf.if %f {
    %v: i32 = int.const 0
    cf.yield %v
  } else {
    cf.yield %x
  }
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }

    /// HFIR's value building blocks are pure; the accesses and checks that can trap or touch
    /// memory are not.
    #[test]
    fn building_blocks() {
        let src = "func @f(%x: i32, %p: ptr, %n: i64, %ok: i1) {
  %s: struct<C>{i32, i32} = agg.make %x, %x
  %y: i32 = agg.extract %s, 1
  %t: struct<C>{i32, i32} = agg.insert %s, %y, 0
  %r: i32, %o: i1 = int.mul.overflow.s %x, %x
  %u: union<i32, ptr> = union.make %x, 0
  %g: i32 = union.tag %u
  %h: i32 = union.get.ub %u, 0
  %sl: slice = slice.make %p, %n
  %sp: ptr = slice.ptr %sl
  %sn: i64 = slice.len %sl
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 10);
        assert!(!out.contains(" = "), "{out}");
        let src = "func @f(%x: i32, %p: ptr, %n: i64, %ok: i1) {
  %u: union<i32, ptr> = union.make %x, 0
  %h: i32 = union.get.trap %u, 0
  %sl: slice = slice.make %p, %n
  %v: i32 = slice.get.ub %sl, %n, align 4
  %w: i32 = slice.get.trap %sl, %n, align 4
  slice.set.ub i32 %x, %sl, %n, align 4
  cf.check.bounds %ok
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }

    #[test]
    fn deletes_in_regions_and_ub_ops() {
        let src = "func @f(%x: i32, %c: i1) {
  cf.if %c {
    %a: i32 = int.div.s.ub %x, %x
    %b: i32 = int.add.nsw %a, %a
    cf.yield
  }
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 2);
        assert!(!out.contains("int."));
    }
}
