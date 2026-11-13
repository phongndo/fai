//! Deleting unused stack allocations. EXPERIMENTAL: no Lean theorem backs it.
//!
//! ```text
//! %s: ptr = mem.stack.of i64, align 8      // deleted: nothing uses %s
//! ```
//!
//! A `mem.stack` or `mem.stack.of` whose pointer nothing uses is deleted. Promotion
//! ([`super::mem2reg`]) leaves such slots behind; the backend would still give each a place in
//! the frame and compute its address.
//!
//! **What correctness assumes.** In FIR's semantics an allocation is never observed unless its
//! pointer is, so the deleted one changes no value, address, or memory. But allocations are
//! numbered in the order they are made, and events and endings print pointers by that number
//! (`ptr #3`), so deleting one renumbers every later allocation: the run of the output is the
//! run of the input up to a renaming of allocations, not the same run. The pass is correct only
//! if those numbers are not observable, which holds on hardware (a pointer is an address) and
//! is what the differential tests compare (`tests/opt.rs`, which renames allocations in order of
//! appearance when this pass is in the pipeline). Making it a theorem needs refinement up to a
//! bijection of allocation ids. Stack allocation can't fail in the semantics, so no failure is
//! lost; if it could (stack overflow), deleting one would only remove a behavior.

use fai_ir::body::Body;
use fai_ir::ir::OpKind;

use super::{Remarks, at, walk};

/// Delete every stack allocation whose pointer has no uses. Returns how many were deleted.
pub fn run(body: &mut Body, remarks: &mut Remarks) -> u32 {
    body.build_uses();
    let mut ops = Vec::new();
    walk(body, &mut ops);
    let mut n = 0;
    for op in ops {
        if !matches!(
            body.kind(op),
            OpKind::MemStack { .. } | OpKind::MemStackOf { .. }
        ) {
            continue;
        }
        let p = body.results(op).next().expect("verified");
        if body.has_uses(p) {
            continue;
        }
        let loc = body.loc(op);
        remarks.add("stackdce", (op, loc), None, || {
            format!(
                "deleted unused stack allocation %{} {}",
                body.name(p),
                at(loc)
            )
        });
        body.erase(op);
        n += 1;
    }
    n
}
