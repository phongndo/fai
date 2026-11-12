//! Dead store elimination: `Fir.Dse.refines`.
//!
//! ```text
//! mem.store T1 %x, %p, align A1        // deleted
//! mem.store T2 %v, %p, align A2
//! ```
//!
//! The pattern is `Dse.Pat` exactly: the second store is the op right after the first in the
//! same region (at any depth), both store through the same pointer *variable* `%p`, the first
//! stores a variable `%x` (the second may store a hole), both types are scalars (`iN`, `ptr`, or
//! `bN`: `Ty.isValue`), and they have the same size in *every* data layout
//! (`∀ cfg, T1.size cfg = T2.size cfg`). With Lean's `Ty.size`, that holds when the types are
//! equal, or both are `iN`/`bN` with the same `N / 8`. A `ptr` and an `i64` have the same size in
//! the default layout but not in every layout, so they don't match.
//!
//! A run of stores through the same pointer leaves only the last: each deletion is one instance
//! of the theorem on the program the previous one left.
//!
//! Not covered by the theorem, so skipped: stores of struct, array, or slice types (HFIR). They
//! write only their leaves and leave padding as it was, so a later aggregate store doesn't hide
//! all of an earlier store's bytes (decision: Aggregate values).

use crate::body::{Body, OperandKind};
use crate::ir::{OpKind, Ty};

use super::{Remarks, at, walk};

/// Whether two scalar types take the same number of bytes in every data layout (Lean's
/// `Ty.size`: `iN` and `bN` take `N / 8`, a pointer its layout's size). False if either isn't a
/// scalar (`Dse.Pat` asks for `Ty.isValue` of both).
pub fn same_size(a: Ty, b: Ty) -> bool {
    match (a, b) {
        (Ty::Int(m) | Ty::Byte(m), Ty::Int(n) | Ty::Byte(n)) => m / 8 == n / 8,
        (Ty::Ptr, Ty::Ptr) => true,
        _ => false,
    }
}

/// Delete every store that the next op overwrites. Returns how many were deleted.
pub fn run(body: &mut Body, remarks: &mut Remarks) -> u32 {
    let mut ops = Vec::new();
    walk(body, &mut ops);
    let mut dead = Vec::new();
    for &s1 in &ops {
        let OpKind::Store { ty: t1, .. } = body.kind(s1) else {
            continue;
        };
        let Some(s2) = body.next(s1) else { continue };
        let OpKind::Store { ty: t2, .. } = body.kind(s2) else {
            continue;
        };
        let (&[x, p1], &[_, p2]) = (body.operands(s1), body.operands(s2)) else {
            continue;
        };
        let (OperandKind::Value(_), OperandKind::Value(_)) = (x.get(), p1.get()) else {
            continue;
        };
        if p1 != p2 || !same_size(t1, t2) {
            continue;
        }
        let (l1, l2) = (body.loc(s1), body.loc(s2));
        remarks.add("dse", (s1, l1), Some((s2, l2)), || {
            format!("deleted store {} (overwritten by {})", at(l1), at(l2))
        });
        dead.push(s1);
    }
    // Deciding first and erasing after is the same as erasing one by one: a store's next op
    // doesn't change when an earlier store goes. Erasing them together keeps use lists cheap.
    body.erase_many(&dead);
    dead.len() as u32
}

#[cfg(test)]
mod tests {
    use super::super::test_util::{apply, canon};
    use super::*;

    #[test]
    fn deletes_overwritten_stores() {
        let src = "func @f(%x: i32, %y: i32, %z: b32) -> i32 {
  %p: ptr = mem.stack 4, align 4 @1:3
  mem.store i32 %x, %p, align 4 @2:3
  mem.store i32 %y, %p, align 1 @3:3
  mem.store b32 %z, %p, align 4 @4:3
  %r: i32 = mem.load %p, align 4 @5:3
  func.ret %r @6:3
}
";
        let (n, out, remarks) = apply(src, run);
        assert_eq!(n, 2);
        assert_eq!(
            out,
            canon(
                "func @f(%x: i32, %y: i32, %z: b32) -> i32 {
  %p: ptr = mem.stack 4, align 4
  mem.store b32 %z, %p, align 4
  %r: i32 = mem.load %p, align 4
  func.ret %r
}
"
            )
        );
        assert_eq!(
            remarks,
            [
                "dse: deleted store @2:3 (overwritten by @3:3)",
                "dse: deleted store @3:3 (overwritten by @4:3)"
            ]
        );
    }

    #[test]
    fn inside_regions() {
        let src = "func @f(%c: i1, %x: i8, %p: ptr) {
  cf.if %c {
    mem.store i8 %x, %p, align 1
    mem.store i8 %x, %p, align 1
    cf.yield
  }
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 1);
        assert_eq!(out.matches("mem.store").count(), 1);
    }

    /// The look-alikes: a shorter second store, another pointer, an op in between, a pointer
    /// and an integer of the same size in this layout only, and a hole stored first.
    #[test]
    fn keeps_what_the_theorem_does_not_cover() {
        let src = "func @f(%x: i32, %y: i16, %q: ptr, %i: i64, %a: ptr) {
  %p: ptr = mem.stack 8, align 8
  mem.store i32 %x, %p, align 4
  mem.store i16 %y, %p, align 2
  mem.store i32 %x, %p, align 4
  mem.store i32 %x, %q, align 4
  mem.store i32 %x, %p, align 4
  %r: i32 = mem.load %p, align 4
  mem.store i32 %x, %p, align 4
  mem.store ptr %a, %p, align 8
  mem.store i64 %i, %p, align 8
  mem.store i32 ?h: i32, %p, align 4
  mem.store i32 %x, %p, align 4
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }

    #[test]
    fn sizes() {
        assert!(same_size(Ty::Int(32), Ty::Byte(32)));
        assert!(same_size(Ty::Int(64), Ty::Int(64)));
        assert!(same_size(Ty::Ptr, Ty::Ptr));
        assert!(!same_size(Ty::Ptr, Ty::Int(64)));
        assert!(!same_size(Ty::Int(16), Ty::Int(32)));
        assert!(!same_size(Ty::Slice, Ty::Slice));
    }

    /// Aggregate stores leave padding unchanged, so the theorem is for scalar stores only.
    #[test]
    fn keeps_aggregate_stores() {
        let src = "func @f(%s: struct<C>{i8, i32}, %t: slice, %p: ptr) {
  mem.store struct<C>{i8, i32} %s, %p, align 4
  mem.store struct<C>{i8, i32} %s, %p, align 4
  mem.store slice %t, %p, align 8
  mem.store slice %t, %p, align 8
  func.ret
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }
}
