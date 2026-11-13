//! Copy propagation: `Fir.CopyProp.refines`.
//!
//! ```text
//! %y: T = copy %x
//! %z: T = int.add.wrap %y, %y       // becomes  int.add.wrap %x, %x
//! func.ret %y                       // becomes  func.ret %x
//! ```
//!
//! The pattern is `CopyProp.L` with the longest run of ops it allows: after `%y = copy %x` (the
//! operand a variable), every op that follows in the same region up to (not including) the
//! first op with regions or a call (`func.invoke` included), terminators included (`exn.throw`
//! too), reads `%x` where it reads `%y`. The
//! theorem's other condition, that no op in the run binds `%x` or `%y`, always holds in a
//! verified function, where every name is defined once. Uses of `%y` in nested regions, and
//! after a call or an op with regions, keep reading `%y` (the theorem doesn't cover them yet:
//! open item 0).
//!
//! Copies are taken in program order, so a chain `%y = copy %x; %z = copy %y` ends with both
//! read as `%x`: the second copy's operand is rewritten before its own uses are. Each copy's
//! rewrite is one instance of the theorem on the program the previous ones left. The copies
//! stay; dead code elimination deletes them once nothing reads them.
//!
//! Each copy costs its result's uses, found through the use lists: ops get a segment number
//! (the region, cut at each op with regions or a call) in one walk, and a use is rewritten when
//! its op is in the copy's segment.

use fai_ir::body::{Body, OpId, OperandKind, Ops};
use fai_ir::ir::OpKind;

use super::{Remarks, at};

/// Whether copy propagation stops at the op: it has regions, or calls a function, with or
/// without a handler (Lean's `Flat` fails: `callee?` is `some`, which the generated contract
/// records as `calls`).
fn stops(body: &Body, op: OpId) -> bool {
    !body.regions(op).is_empty() || body.kind(op).contract().calls
}

/// Make the ops after each copy read its operand. Returns how many operands were rewritten.
pub fn run(body: &mut Body, remarks: &mut Remarks) -> u32 {
    body.build_uses();
    // Segments: ops of the same region with no op that stops propagation between them, the
    // later of them included. Each region starts a new one.
    let mut seg = vec![0u32; body.num_ops()];
    let mut copies = Vec::new();
    let mut next = 0u32;
    {
        let mut stack: Vec<(Ops<'_>, u32)> = vec![(body.ops(body.entry()), 0)];
        while let Some((it, s)) = stack.last_mut() {
            let Some(op) = it.next() else {
                stack.pop();
                continue;
            };
            if stops(body, op) {
                next += 1;
                *s = next;
            }
            seg[op.index()] = *s;
            if body.kind(op) == OpKind::Copy {
                copies.push(op);
            }
            for &r in body.regions(op).iter().rev() {
                next += 1;
                stack.push((body.ops(r), next));
            }
        }
    }
    let mut n = 0;
    for c in copies {
        let (&[x], Some(y)) = (body.operands(c), body.results(c).next()) else {
            continue;
        };
        let OperandKind::Value(xv) = x.get() else {
            continue;
        };
        let s = seg[c.index()];
        if remarks.enabled() {
            let mut locs: Vec<_> = body
                .uses(y)
                .map(|u| body.user(u).0)
                .filter(|op| seg[op.index()] == s)
                .map(|op| body.loc(op))
                .collect();
            if locs.is_empty() {
                continue;
            }
            locs.sort_by_key(|l| l.map(|l| (l.line, l.col)));
            locs.dedup();
            let locs: Vec<String> = locs.into_iter().map(at).collect();
            let (ny, nx) = (body.name(y).to_owned(), body.name(xv).to_owned());
            let cl = body.loc(c);
            remarks.add("copyprop", (c, cl), Some((c, cl)), || {
                format!(
                    "%{ny} read as %{nx} at {} (copy {})",
                    locs.join(", "),
                    at(cl)
                )
            });
        }
        n += body.replace_uses_where(y, xv, |b, u| seg[b.user(u).0.index()] == s);
    }
    n
}

#[cfg(test)]
mod tests {
    use super::super::test_util::{apply, canon};
    use super::*;

    #[test]
    fn propagates_up_to_a_call_or_region() {
        let src = "func @g(%a: i32) -> i32 {
  func.ret %a
}

func @f(%x: i32, %c: i1) -> i32 {
  %y: i32 = copy %x @1:3
  %z: i32 = copy %y @2:3
  %s: i32 = int.add.wrap %y, %z @3:3
  %t: i32 = func.call @g(%y) @4:3
  %u: i32 = int.add.wrap %y, %z @5:3
  %v: i32 = cf.if %c {
    %w: i32 = int.add.wrap %y, %t
    cf.yield %w
  } else {
    cf.yield %z
  }
  func.ret %v
}
";
        let mut m = fai_ir::parse_module(src).unwrap();
        fai_ir::verify_module(&m).unwrap();
        let mut remarks = Remarks::new(true);
        let n = run(&mut m.funcs[1].body, &mut remarks);
        fai_ir::verify_module(&m).unwrap();
        m.funcs[1].body.check_invariants().unwrap();
        assert_eq!(n, 3);
        let want = canon(
            "func @g(%a: i32) -> i32 {
  func.ret %a
}

func @f(%x: i32, %c: i1) -> i32 {
  %y: i32 = copy %x
  %z: i32 = copy %x
  %s: i32 = int.add.wrap %x, %x
  %t: i32 = func.call @g(%y)
  %u: i32 = int.add.wrap %y, %z
  %v: i32 = cf.if %c {
    %w: i32 = int.add.wrap %y, %t
    cf.yield %w
  } else {
    cf.yield %z
  }
  func.ret %v
}
",
        );
        assert_eq!(m.render(false), want);
        let remarks: Vec<String> = remarks.list().iter().map(|r| r.to_string()).collect();
        assert_eq!(
            remarks,
            [
                "copyprop: %y read as %x at @2:3, @3:3 (copy @1:3)",
                "copyprop: %z read as %x at @3:3 (copy @2:3)"
            ]
        );
    }

    /// Inside a region, after the op with regions, and up to and including a terminator.
    #[test]
    fn in_nested_regions_and_terminators() {
        let src = "func @f(%x: i32, %c: i1) -> i32 {
  %v: i32 = cf.if %c {
    %y: i32 = copy %x
    cf.yield %y
  } else {
    cf.yield %x
  }
  %y2: i32 = copy %v
  func.ret %y2
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 2);
        assert!(out.contains("cf.yield %x\n  } else"));
        assert!(out.contains("func.ret %v"));
    }

    #[test]
    fn copies_of_holes_stay() {
        let src = "func @f() -> i32 {
  %y: i32 = copy ?h: i32
  func.ret %y
}
";
        let (n, out, _) = apply(src, run);
        assert_eq!(n, 0);
        assert_eq!(out, canon(src));
    }
}
