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
//! pass asks the generated contract ([`fai_ir::contract`]), whose permissions come from Lean's
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
//!
//! **Output check.** [`check`] judges the candidate; [`apply`] and [`Body::erase_many`] then edit
//! the body, and nothing above looks at what they produced. [`check_output`] does, on every run
//! that deletes anything ([`run`]): it takes the body before and after, and decides what Lean's
//! `Fir.Dce.checkFuncL` decides (proved equal to `Fir.Dce.checkFunc`, whose acceptance
//! `Fir.Dce.checkFunc_sound` proves implies refinement): the target's ops are the source's, in
//! order and region by region, with ops of permitted kinds left out whose results no target op
//! left after them in their region reads. It is a transcription, not the proved code: that it
//! accepts exactly what `fir-ref check-dce` accepts is tested, not proved
//! (`tests/rust/dce_check.rs`: the pass's outputs, and the targets of random candidates and of
//! edits that aren't deletions, go to both).
//! It runs in every compilation, with or without `--check-dce`, in time linear in the body's size
//! times its nesting depth.

use fai_ir::body::{Body, OpId, OperandKind, RegionId, ValueDef};
use fai_ir::contract::Policy;
use fai_ir::ir::OpKind;

use super::{Remarks, at, walk};

/// Whether dead code elimination may delete ops of this kind under `policy`: the generated
/// contract's permission ([`fai_ir::contract`], from Lean's `Fir.Dce.dcePerm`), which
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
///
/// The output is then checked against the body as it was ([`check_output`]): a run that deletes
/// anything keeps a copy of the body first, and if the result isn't that copy with deletable ops
/// left out, the copy is put back (and the remarks about the deletions dropped) and the run
/// fails. A run with nothing to delete doesn't touch the body.
pub fn run(body: &mut Body, remarks: &mut Remarks, policy: Policy) -> Result<u32, String> {
    let candidate = plan(body, policy);
    if candidate.erase.is_empty() {
        return Ok(0);
    }
    let before = body.clone();
    let accepted = check(body, candidate, policy)?;
    let marks = remarks.list().len();
    let n = apply(accepted, remarks);
    if let Err(e) = check_output(&before, body, policy) {
        // The deletions are undone, so are their remarks.
        *body = before;
        remarks.truncate(marks);
        return Err(format!("its output failed the output check: {e}"));
    }
    Ok(n)
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

/// Accept `tgt` as `src` after dead code elimination: what Lean's `Fir.Dce.checkFuncL` decides
/// for the two function bodies, transcribed. Both must be versions of one body (`tgt` is `src`
/// edited; [`Body::same_tables`]), so ops are compared id by id: an op of `tgt` matches one of
/// `src` when their kinds, results, operands, and locations are equal and their regions are
/// related in the same way. Going through each region in order, the next source op either
/// matches the next target op, or is left out, which needs its kind to be one the contract lets
/// dead code elimination delete under `policy` (under [`Policy::VerifiedOnly`], exactly Lean's
/// `dcePerm`), no regions, only values as operands, and results whose names no target op not
/// yet matched in that region reads, at any depth. Reads are counted by name, as Lean counts
/// them. Returns how many source ops were left out, at any depth.
///
/// Matching is greedy, as in Lean. Comparing ids is stricter than comparing what they mean
/// (Lean compares names and printed fields), so this accepts only pairs Lean's checker would
/// (given that the printer writes the same text for equal ops, which [`Body::same_tables`]
/// makes so).
pub fn check_output(src: &Body, tgt: &Body, policy: Policy) -> Result<u64, String> {
    if !src.same_tables(tgt) {
        return Err(
            "the target isn't a version of the source body (their value, string, \
                    constant, or type tables differ)"
                .to_owned(),
        );
    }
    // A class per name: the first value with it. Reads are counted per class.
    let mut first: rustc_hash::FxHashMap<&str, u32> = rustc_hash::FxHashMap::default();
    first.reserve(src.num_values());
    let class: Vec<u32> = (0..src.num_values() as u32)
        .map(|i| {
            let v = fai_ir::body::ValueId::from_raw(i);
            *first.entry(src.name(v)).or_insert(i)
        })
        .collect();
    let mut c = OutputCheck {
        src,
        tgt,
        policy,
        class,
        pool: Vec::new(),
        left_out: 0,
    };
    c.region(tgt.entry(), src.entry())?;
    Ok(c.left_out)
}

struct OutputCheck<'a> {
    src: &'a Body,
    tgt: &'a Body,
    policy: Policy,
    class: Vec<u32>,
    /// Count arrays (by name class) for the regions being checked, innermost last, reused:
    /// each is all zeros again when its region is accepted.
    pool: Vec<Vec<i32>>,
    left_out: u64,
}

impl OutputCheck<'_> {
    /// Lean's `opTick`: add `d` to the count of every name `op` reads, at any depth.
    fn tick(&self, counts: &mut [i32], op: OpId, d: i32) {
        let b = self.tgt;
        let mut work = vec![op];
        while let Some(o) = work.pop() {
            for x in b.operands(o) {
                if let OperandKind::Value(v) = x.get() {
                    counts[self.class[v.index()] as usize] += d;
                }
            }
            for &r in b.regions(o) {
                work.extend(b.ops(r));
            }
        }
    }

    /// Lean's `checkRegionsL` for one pair of regions: the same parameters and label, and
    /// `checkOpsL` on their ops, starting from the counts of every read in the target's.
    fn region(&mut self, tr: RegionId, sr: RegionId) -> Result<(), String> {
        let (src, tgt) = (self.src, self.tgt);
        if !tgt.params(tr).eq(src.params(sr)) || tgt.label(tr) != src.label(sr) {
            return Err("a region's parameters or label differ".to_owned());
        }
        let t: Vec<OpId> = tgt.ops(tr).collect();
        let mut counts = self.pool.pop().unwrap_or_else(|| vec![0; self.class.len()]);
        for &o in &t {
            self.tick(&mut counts, o, 1);
        }
        let r = self.region_ops(&t, sr, &mut counts);
        if r.is_ok() {
            // Every target op was matched and its reads taken off by the same walk that added
            // them, so the array is all zeros again. (Not asserted: a scan of the whole array per
            // region would make debug builds quadratic in a function with many regions.)
            self.pool.push(counts);
        }
        r
    }

    /// Lean's `checkOpsL` for the target ops `t` of a region and the source region `sr`, from
    /// the counts of `t`'s reads.
    fn region_ops(&mut self, t: &[OpId], sr: RegionId, counts: &mut [i32]) -> Result<(), String> {
        let (src, tgt) = (self.src, self.tgt);
        let mut i = 0;
        for s in src.ops(sr) {
            if i < t.len() && self.same_op(t[i], s)? {
                self.tick(counts, t[i], -1);
                i += 1;
                continue;
            }
            if let Err(why) = self.deletable(counts, s) {
                let next = match t.get(i) {
                    Some(&o) => format!(
                        "the target has {} {} there",
                        tgt.kind(o).mnemonic(),
                        at(tgt.loc(o))
                    ),
                    None => "the target's region has ended".to_owned(),
                };
                return Err(format!(
                    "{} {} is missing from the target, and may not be deleted: {why} ({next})",
                    src.kind(s).mnemonic(),
                    at(src.loc(s))
                ));
            }
            self.left_out += 1;
        }
        if let Some(&o) = t.get(i) {
            return Err(format!(
                "{} {} in the target matches no op of the source",
                tgt.kind(o).mnemonic(),
                at(tgt.loc(o))
            ));
        }
        Ok(())
    }

    /// Lean's `checkOpL`: the same op, up to related regions. When everything but the regions'
    /// contents matches and those don't, this is the error from inside them: the source op has
    /// regions, so it can't be left out either, and Lean's checker refuses the pair too.
    fn same_op(&mut self, t: OpId, s: OpId) -> Result<bool, String> {
        let (src, tgt) = (self.src, self.tgt);
        if tgt.kind(t) != src.kind(s)
            || !tgt.results(t).eq(src.results(s))
            || tgt
                .operands(t)
                .iter()
                .map(|o| o.raw())
                .ne(src.operands(s).iter().map(|o| o.raw()))
            || tgt.loc(t) != src.loc(s)
            || tgt.regions(t).len() != src.regions(s).len()
        {
            return Ok(false);
        }
        for (&a, &b) in tgt.regions(t).iter().zip(src.regions(s)) {
            self.region(a, b)?;
        }
        Ok(true)
    }

    /// Lean's `deletableC`: a permitted kind, no regions, only values as operands, and results
    /// whose names the target ops not yet matched don't read.
    fn deletable(&self, counts: &[i32], s: OpId) -> Result<(), String> {
        let b = self.src;
        let k = b.kind(s);
        if !pure_kind(k, self.policy) {
            return Err(format!(
                "the contract keeps it ({:?}, policy {:?})",
                k.contract().dce,
                self.policy
            ));
        }
        if !b.regions(s).is_empty() {
            return Err("it has regions".to_owned());
        }
        if !b
            .operands(s)
            .iter()
            .all(|o| matches!(o.get(), OperandKind::Value(_)))
        {
            return Err("it reads a hole".to_owned());
        }
        for v in b.results(s) {
            if counts[self.class[v.index()] as usize] != 0 {
                return Err(format!("the target still reads %{}", b.name(v)));
            }
        }
        Ok(())
    }
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

    const OUT: &str = "func @f(%x: i32, %p: ptr, %c: i1) -> i32 {
  %y: i32 = copy %x @1:3
  %z: i32 = int.add.wrap %y, %x @2:3
  mem.store i32 %x, %p, align 4 @3:3
  %w: i32 = int.mul.wrap %x, %x @4:3
  cf.if %c @5:3 {
    %a: i32 = int.add.wrap %x, %x @6:5
    cf.yield
  }
  func.ret %w @8:3
}
";

    fn body(text: &str) -> Body {
        let m = fai_ir::parse_module(text).unwrap();
        fai_ir::verify_module(&m).unwrap();
        m.funcs.into_iter().next().unwrap().body
    }

    fn op_at(b: &Body, line: u32) -> OpId {
        let mut ops = Vec::new();
        walk(b, &mut ops);
        ops.into_iter()
            .find(|&o| b.loc(o).is_some_and(|l| l.line == line))
            .unwrap()
    }

    /// What the pass produces is accepted, at any depth, and counted.
    #[test]
    fn the_output_check_accepts_the_pass_output() {
        let src = body(OUT);
        let mut tgt = src.clone();
        let n = run(&mut tgt, &mut Remarks::new(false), Policy::VerifiedOnly).unwrap();
        assert_eq!(n, 3);
        assert_eq!(check_output(&src, &tgt, Policy::VerifiedOnly), Ok(3));
        assert_eq!(check_output(&src, &src, Policy::VerifiedOnly), Ok(0));
    }

    /// Outputs that aren't a dead code elimination of the input are refused, each for its reason,
    /// whatever produced them.
    #[test]
    fn the_output_check_refuses_other_edits() {
        let src = body(OUT);
        let refuse = |edit: &dyn Fn(&mut Body), why: &str| {
            let mut tgt = src.clone();
            edit(&mut tgt);
            let e = check_output(&src, &tgt, Policy::VerifiedOnly).unwrap_err();
            assert!(e.contains(why), "{e}");
        };
        // A store nothing reads is still kept.
        refuse(
            &|b| b.erase(op_at(b, 3)),
            "mem.store @3:3 is missing from the target, and may not be deleted: the contract keeps it",
        );
        // A pure op whose result is read.
        refuse(
            &|b| b.erase(op_at(b, 4)),
            "int.mul.wrap @4:3 is missing from the target, and may not be deleted: the target still reads %w",
        );
        // An op changed rather than deleted (inside a region too).
        refuse(
            &|b| {
                let o = op_at(b, 4);
                let k = b.kind(op_at(b, 2));
                b.set_kind(o, k);
            },
            "int.mul.wrap @4:3 is missing from the target",
        );
        refuse(
            &|b| {
                let o = op_at(b, 6);
                let k = b.kind(op_at(b, 4));
                b.set_kind(o, k);
            },
            // Greedy matching, as in Lean: the source's add is left out (nothing reads it), and
            // then the target's changed op matches nothing.
            "cf.yield @? is missing from the target, and may not be deleted: the contract keeps it (Keep, policy VerifiedOnly) (the target has int.mul.wrap @6:5 there)",
        );
        refuse(
            &|b| {
                let o = op_at(b, 4);
                let y = b.operands(op_at(b, 2))[0];
                b.set_operand(o, 1, y);
            },
            "int.mul.wrap @4:3 is missing from the target",
        );
        // A region op can't be left out, nor can the terminator.
        refuse(
            &|b| b.erase(op_at(b, 5)),
            "cf.if @5:3 is missing from the target, and may not be deleted",
        );
        refuse(
            &|b| b.erase(op_at(b, 8)),
            "func.ret @8:3 is missing from the target",
        );
        // A body that isn't a version of this one.
        refuse(
            &|b| {
                b.add_str("other");
            },
            "isn't a version of the source body",
        );
    }

    /// A deleted op read only from inside a later op's region: the read counts reach into
    /// regions, at any depth. (A target like this doesn't verify, so the differential tests
    /// never give it to the proved checker; this is where it is covered.)
    #[test]
    fn the_output_check_sees_reads_inside_regions() {
        let src = body(
            "func @f(%x: i32, %p: ptr, %c: i1) {
  %v: i32 = copy %x @1:3
  cf.if %c @2:3 {
    cf.if %c @3:5 {
      mem.store i32 %v, %p, align 4 @4:7
      cf.yield
    }
    cf.yield
  }
  func.ret @7:3
}
",
        );
        let mut tgt = src.clone();
        tgt.erase(op_at(&tgt, 1));
        let e = check_output(&src, &tgt, Policy::VerifiedOnly).unwrap_err();
        assert!(
            e.contains("copy @1:3 is missing from the target, and may not be deleted: the target still reads %v"),
            "{e}"
        );
    }

    /// The policy decides which kinds may go, as in the pass.
    #[test]
    fn the_output_check_follows_the_contract() {
        let src = body("func @f(%x: i32) {\n  %a: i32 = freeze %x @1:3\n  func.ret @2:3\n}\n");
        let mut tgt = src.clone();
        tgt.erase(op_at(&tgt, 1));
        let e = check_output(&src, &tgt, Policy::VerifiedOnly).unwrap_err();
        assert!(e.contains("freeze @1:3"), "{e}");
    }
}
