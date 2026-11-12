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
//! getting stuck (`ReadOnly`) for any operand values. Which kinds qualify is not decided here: the
//! pass asks the generated contract ([`crate::contract`]), whose permissions come from Lean's
//! `Fir.Dce.dcePerm`, and `Fir.Dce.dcePerm_sound` proves every kind it lets go pure (an op of such
//! a kind with no regions and variable operands is `Pure` by `Fir.Dce.Pure.of_kind`). The kinds:
//! constants, `poison`, `copy`, `select`, bitwise ops, comparisons, extensions and truncations,
//! `int.add`/`sub`/`mul`, divisions, and shifts unless a modifier traps, `ptr.null`,
//! `ptr.offset`, `ptr.field`, `ptr.index`, `ty.size`/`align`/`offset`, `mem.global`, and the
//! value building blocks (`agg.*`, `int.*.overflow.*`, `union.make`/`tag`, `union.get.ub`,
//! `slice.make`/`ptr`/`len`), and the float ops that can't trap (all but `float.to_int.*.trap`;
//! their NaN results are the oracle's choice from the op and its operands, so they only read the
//! core: `Fir.Dce.float_pure`). Everything else stays: ops that may trap, consult the oracle
//! (`freeze`, `ptr.cmp`; `Fir.Dce.freeze_changes_core`), give an allocation its address, touch
//! memory or scopes, allocate, call, or end a block.
//!
//! **Plan, check, apply.** The pass never edits the body directly. [`plan`] reads it and proposes
//! the ops to delete (a [`Candidate`]); [`check`], an independent checker, accepts the
//! candidate only if every op in it is present once, of a kind the contract permits under the
//! policy, without regions or holes, and if no op left in the body reads its results; and only
//! an [`Accepted`] candidate, which only [`check`] makes, can be applied ([`apply`]). It holds
//! the body's exclusive borrow: approval cannot be transferred to another body or survive an
//! intervening edit. The
//! checker states the conditions of Lean's `Fir.Dce.checkFunc` for the edit (it is stricter: no
//! remaining op anywhere may read a deleted result), and the tests run the proved checker itself,
//! `fir-ref check-dce`, on the pass's output (`tests/dce_check.rs`): `Fir.Dce.checkFunc_sound` says
//! that its acceptance implies the output refines the input. The Rust checker is not proved.

use crate::body::{Body, OpId, OperandKind, ValueDef};
use crate::contract::Policy;
use crate::ir::OpKind;

use super::{Remarks, at, walk};

/// Whether dead code elimination may delete ops of this kind under `policy`: the generated
/// contract's permission ([`crate::contract`], from Lean's `Fir.Dce.dcePerm`), which
/// `Fir.Dce.dcePerm_sound` proves pure when its evidence is `Proved`.
pub fn pure_kind(k: OpKind, policy: Policy) -> bool {
    k.contract().dce.allows(policy)
}

/// Lean's `Dce.Pure`, for an op in a body.
pub fn is_pure(body: &Body, op: OpId, policy: Policy) -> bool {
    pure_kind(body.kind(op), policy)
        && body.regions(op).is_empty()
        && body
            .operands(op)
            .iter()
            .all(|o| matches!(o.get(), OperandKind::Value(_)))
}

/// The ops the pass proposes to delete, in the order it found them dead.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Candidate {
    pub erase: Vec<OpId>,
}

/// A checked deletion together with the only body it may change. Dropping it cancels the edit.
/// The exclusive borrow prevents edits between checking and applying; consuming it prevents
/// replay. There is no body argument to [`apply`] with which to substitute different code.
///
/// This compiles:
/// ```
/// use fir::{Body, contract::Policy, passes::{dce, Remarks}};
/// let (mut a, mut b) = (Body::new(), Body::new());
/// let accepted = dce::check(&mut a, dce::Candidate::default(), Policy::VerifiedOnly).unwrap();
/// dce::apply(accepted, &mut Remarks::new(false));
/// let _ = &mut b;
/// ```
/// Each of the following differs from it in one line, and doesn't compile (stable `rustdoc`
/// doesn't check the error codes, so the compiling twin is what shows the line is the reason).
/// An approval can't be applied to another body:
/// ```compile_fail,E0061
/// use fir::{Body, contract::Policy, passes::{dce, Remarks}};
/// let (mut a, mut b) = (Body::new(), Body::new());
/// let accepted = dce::check(&mut a, dce::Candidate::default(), Policy::VerifiedOnly).unwrap();
/// dce::apply(&mut b, accepted, &mut Remarks::new(false));
/// let _ = &mut b;
/// ```
/// The checked body can't change before applying:
/// ```compile_fail,E0499
/// use fir::{Body, contract::Policy, passes::{dce, Remarks}};
/// let (mut a, mut b) = (Body::new(), Body::new());
/// let accepted = dce::check(&mut a, dce::Candidate::default(), Policy::VerifiedOnly).unwrap();
/// a.erase_many(&[]); dce::apply(accepted, &mut Remarks::new(false));
/// let _ = &mut b;
/// ```
/// An approval is used at most once:
/// ```compile_fail,E0382
/// use fir::{Body, contract::Policy, passes::{dce, Remarks}};
/// let (mut a, mut b) = (Body::new(), Body::new());
/// let accepted = dce::check(&mut a, dce::Candidate::default(), Policy::VerifiedOnly).unwrap();
/// dce::apply(accepted, &mut Remarks::new(false)); dce::apply(accepted, &mut Remarks::new(false));
/// let _ = &mut b;
/// ```
#[derive(Debug)]
#[must_use = "apply the checked deletion, or drop it to leave the body unchanged"]
pub struct Accepted<'a> {
    body: &'a mut Body,
    erase: Vec<OpId>,
}

/// Delete every pure op whose results nothing reads, and then those that only the deleted ops
/// read, if the checker accepts the deletion. Returns how many were deleted, or the checker's
/// objection (the body is then unchanged).
pub fn run(body: &mut Body, remarks: &mut Remarks, policy: Policy) -> Result<u32, String> {
    let candidate = plan(body, policy);
    let accepted = check(body, candidate, policy)?;
    Ok(apply(accepted, remarks))
}

/// Find the ops to delete, without changing anything.
///
/// Uses are counted in one walk (use lists aren't needed); deleting an op takes one from each
/// of its operands' counts, and an op whose counts reach zero is deleted next.
pub fn plan(body: &Body, policy: Policy) -> Candidate {
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
    let unread = |uses: &[u32], op: OpId| {
        is_pure(body, op, policy) && body.results(op).all(|v| uses[v.index()] == 0)
    };
    // Popped from the end, so reversed to delete in program order.
    let mut work: Vec<OpId> = ops
        .iter()
        .rev()
        .copied()
        .filter(|&op| unread(&uses, op))
        .collect();
    let mut dead = vec![false; body.num_ops()];
    let mut erase = Vec::new();
    while let Some(op) = work.pop() {
        if std::mem::replace(&mut dead[op.index()], true) {
            continue;
        }
        erase.push(op);
        for o in body.operands(op).iter().rev() {
            let OperandKind::Value(v) = o.get() else {
                continue;
            };
            uses[v.index()] -= 1;
            if let ValueDef::Result { op: d, .. } = body.def(v)
                && uses[v.index()] == 0
                && !dead[d.index()]
                && unread(&uses, d)
            {
                work.push(d);
            }
        }
    }
    Candidate { erase }
}

/// Accept `c` for `body` if deleting its ops is a dead code elimination the contract permits
/// under `policy`; otherwise say why not. Independent of [`plan`]: it recounts reads from
/// scratch over the ops that remain.
pub fn check(body: &mut Body, c: Candidate, policy: Policy) -> Result<Accepted<'_>, String> {
    let mut ops = Vec::new();
    walk(body, &mut ops);
    let mut present = vec![false; body.num_ops()];
    for &op in &ops {
        present[op.index()] = true;
    }
    let mut dead = vec![false; body.num_ops()];
    for &op in &c.erase {
        if !present.get(op.index()).copied().unwrap_or(false) {
            return Err(format!("op {} is not in the body", op.index()));
        }
        if std::mem::replace(&mut dead[op.index()], true) {
            return Err(format!("op {} is deleted twice", op.index()));
        }
        let k = body.kind(op);
        if !k.contract().dce.allows(policy) {
            return Err(format!(
                "{} {}: the contract doesn't let dead code elimination delete it ({:?}, policy {policy:?})",
                k.mnemonic(),
                at(body.loc(op)),
                k.contract().dce
            ));
        }
        if !body.regions(op).is_empty() {
            return Err(format!(
                "{} {}: it has regions",
                k.mnemonic(),
                at(body.loc(op))
            ));
        }
        if body
            .operands(op)
            .iter()
            .any(|o| !matches!(o.get(), OperandKind::Value(_)))
        {
            return Err(format!(
                "{} {}: it reads a hole",
                k.mnemonic(),
                at(body.loc(op))
            ));
        }
    }
    for &op in ops.iter().filter(|op| !dead[op.index()]) {
        for o in body.operands(op) {
            if let OperandKind::Value(v) = o.get()
                && let ValueDef::Result { op: d, .. } = body.def(v)
                && dead[d.index()]
            {
                return Err(format!(
                    "{} {} reads a result of {} {}, which is deleted",
                    body.kind(op).mnemonic(),
                    at(body.loc(op)),
                    body.kind(d).mnemonic(),
                    at(body.loc(d))
                ));
            }
        }
    }
    Ok(Accepted {
        body,
        erase: c.erase,
    })
}

/// Delete the accepted ops. Returns how many.
pub fn apply(a: Accepted<'_>, remarks: &mut Remarks) -> u32 {
    let body = a.body;
    for &op in &a.erase {
        let l = body.loc(op);
        let k = body.kind(op);
        remarks.add("dce", (op, l), None, || {
            format!("deleted unused {} {}", k.mnemonic(), at(l))
        });
    }
    body.erase_many(&a.erase);
    a.erase.len() as u32
}

#[cfg(test)]
mod tests {
    use super::super::test_util::{apply as apply_pass, canon};
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
        let (n, out, remarks) = apply_pass(src, |b, r| run(b, r, Policy::VerifiedOnly).unwrap());
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
        let (n, out, _) = apply_pass(src, |b, r| run(b, r, Policy::VerifiedOnly).unwrap());
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
        let (n, out, _) = apply_pass(src, |b, r| run(b, r, Policy::VerifiedOnly).unwrap());
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
        let (n, out, _) = apply_pass(src, |b, r| run(b, r, Policy::VerifiedOnly).unwrap());
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
        let (n, out, _) = apply_pass(src, |b, r| run(b, r, Policy::VerifiedOnly).unwrap());
        assert_eq!(n, 2);
        assert!(!out.contains("int."));
    }
}
