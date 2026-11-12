//! Store-to-load forwarding: `Fir.Fwd.refines`.
//!
//! ```text
//! mem.store T %v, %p, align A1
//! %y: T = mem.load %p, align A2        // becomes  %y: T = copy %v
//! ```
//!
//! The pattern is `Fwd.Pat` exactly: the load is the op right after the store in the same
//! region (at any depth), it loads through the same pointer operand, its result has the stored
//! type `T`, and `T` is `Exact`: a scalar type whose values come back from memory unchanged (an
//! integer type of whole bytes, `ptr`, or a byte type). Struct, array, and slice types (HFIR) are
//! not: their loads and stores access only the leaves (decision: Aggregate values), which
//! `Fwd.Exact` leaves out. The copy keeps the load's result, facts included, and its location, as `Pat`'s `c`
//! does. Pointers taking at least one byte, the theorem's other condition, is what the verifier
//! checks of every memory space.
//!
//! The copy stays for copy propagation and dead code elimination to remove (decision: Copies).
//!
//! Skipped: a pointer operand that is a hole (Lean compares holes by name; holes here are
//! separate operands, and a program with holes can't be compiled anyway).

use crate::body::{Body, OperandKind};
use crate::ir::{OpKind, Ty};

use super::{Remarks, at, walk};

/// Lean's `Fwd.Exact`: a scalar type whose values come back unchanged from memory.
pub fn exact(t: Ty) -> bool {
    match t {
        Ty::Int(w) => w % 8 == 0 && w > 0,
        Ty::Ptr | Ty::Byte(_) => true,
        Ty::Agg(_) | Ty::Slice => false,
    }
}

/// Turn every load right after a store of its type through the same pointer into a copy of the
/// stored value. Returns how many were forwarded.
pub fn run(body: &mut Body, remarks: &mut Remarks) -> u32 {
    let mut ops = Vec::new();
    walk(body, &mut ops);
    let mut edits = Vec::new();
    for &s in &ops {
        let OpKind::Store { ty, .. } = body.kind(s) else {
            continue;
        };
        let Some(l) = body.next(s) else { continue };
        let OpKind::Load { .. } = body.kind(l) else {
            continue;
        };
        let (&[v, p], &[lp]) = (body.operands(s), body.operands(l)) else {
            continue;
        };
        let mut results = body.results(l);
        let (Some(r), None) = (results.next(), results.next()) else {
            continue;
        };
        if !matches!(p.get(), OperandKind::Value(_)) || lp != p || body.ty(r) != ty || !exact(ty) {
            continue;
        }
        let (ls, ll) = (body.loc(s), body.loc(l));
        remarks.add("fwd", (l, ll), Some((s, ls)), || {
            format!(
                "load {} forwarded from store {} (now a copy)",
                at(ll),
                at(ls)
            )
        });
        body.set_kind(l, OpKind::Copy);
        edits.push((l, 0, v));
    }
    // Together, so that many loads through one pointer stay cheap with use lists built.
    body.set_operands(&edits);
    edits.len() as u32
}

#[cfg(test)]
mod tests {
    use super::super::test_util::{apply, canon};
    use super::*;

    #[test]
    fn forwards_the_stored_value() {
        let src = "func @f(%x: i32, %c: i1, %a: ptr) -> i32 {
  %p: ptr = mem.stack 8, align 8 @1:3
  mem.store i32 %x, %p, align 4 @2:3
  %y: i32 [range.s(0, 9) check] = mem.load %p, align 1 @3:3
  cf.if %c {
    mem.store ptr %a, %p, align 8 @5:5
    %b: ptr = mem.load %p, align 8 @6:5
    cf.yield
  }
  func.ret %y
}
";
        let (n, out, remarks) = apply(src, run);
        assert_eq!(n, 2);
        assert_eq!(
            out,
            canon(
                "func @f(%x: i32, %c: i1, %a: ptr) -> i32 {
  %p: ptr = mem.stack 8, align 8
  mem.store i32 %x, %p, align 4
  %y: i32 [range.s(0, 9) check] = copy %x
  cf.if %c {
    mem.store ptr %a, %p, align 8
    %b: ptr = copy %a
    cf.yield
  }
  func.ret %y
}
"
            )
        );
        assert_eq!(
            remarks,
            [
                "fwd: load @3:3 forwarded from store @2:3 (now a copy)",
                "fwd: load @6:5 forwarded from store @5:5 (now a copy)"
            ]
        );
    }

    /// The look-alikes: another type of the same size, another pointer, an op in between.
    #[test]
    fn keeps_what_the_theorem_does_not_cover() {
        let src = "func @f(%x: i32, %q: ptr) -> i32 {
  %p: ptr = mem.stack 8, align 8
  mem.store i32 %x, %p, align 4
  %b: b32 = mem.load %p, align 4
  mem.store i32 %x, %p, align 4
  %y: i32 = mem.load %q, align 4
  mem.store i32 %x, %p, align 4
  %z: i32 = int.const 1
  %w: i32 = mem.load %p, align 4
  func.ret %w
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }

    #[test]
    fn exact_types() {
        assert!(exact(Ty::Int(8)) && exact(Ty::Ptr) && exact(Ty::Byte(32)));
        assert!(!exact(Ty::Int(12)) && !exact(Ty::Int(1)) && !exact(Ty::Slice));
    }

    /// Aggregate loads read only the leaves, so the theorem is for scalar types only.
    #[test]
    fn keeps_aggregate_loads() {
        let src =
            "func @f(%s: struct<C>{i8, i32}, %t: slice, %p: ptr) -> (struct<C>{i8, i32}, slice) {
  mem.store struct<C>{i8, i32} %s, %p, align 4
  %a: struct<C>{i8, i32} = mem.load %p, align 4
  mem.store slice %t, %p, align 8
  %b: slice = mem.load %p, align 8
  func.ret %a, %b
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }
}
