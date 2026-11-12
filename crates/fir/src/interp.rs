//! The reference interpreter, mirroring `spec/Fir/Interp.lean` step for step, for the oracle that
//! always answers `0` (the one `fir-ref run` uses): `freeze` of `poison` gives `0`, allocations
//! succeed, allocation ids and tags count up from 1, addresses are assigned first-fit from
//! `0x1000`, and comparing a one-past-the-end pointer with a pointer into another allocation
//! gives "not equal". [`run`] prints the same one-line outcome as `fir-ref run`.
//!
//! The machine follows the crate's data-oriented rules (see [`crate::Body`]):
//!
//! * **Values** are small `Copy` enums (`Value`). Integers up to 64 bits are inline; wider ones,
//!   pointers, and byte strings are ids into append-only tables (`wides`, `ptrs`, `byte_vals`).
//!   Pointer candidate lists are runs in one pool.
//! * **Environments** are one slot stack: a call gets a run of slots, one per value of its
//!   function, indexed by [`ValueId`]. Lean keeps a name-to-value map per call; since a verified
//!   function defines each name once, slots by id are the same thing.
//! * **Frames** are a `Vec` of `Copy` frames. Stack allocations and `noalias` scopes are LIFO, so
//!   each is one shared stack, and a frame records where its part starts.
//! * **Allocations** are columns indexed by allocation id (size, alignment, kind, liveness,
//!   address, exposed tags, sites, bytes). Ids start at 1; index 0 is unused.
//!
//! Addresses are 64-bit here: modules whose address size is above 64 bits are rejected. Pointer
//! offsets, which Lean leaves unbounded, are 128-bit, which a run can't overflow without more
//! than `2^63` steps.

use std::fmt::Write;

use num_bigint::{BigInt, BigUint};
use rustc_hash::FxHashMap;

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, ValueId};
use crate::ir::*;
use crate::sem::{self, Bits, Out};
pub use crate::sem::{TrapReason, UbKind};

/// The fuel `fir-ref run` uses when `--fuel` isn't given.
pub const DEFAULT_FUEL: u64 = 1_000_000;

const NONE: u32 = u32::MAX;

/// A runtime value (Lean's `RVal`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Value {
    /// A defined `iN` with `N ≤ 64`: its bits.
    Int {
        w: u32,
        bits: u64,
    },
    /// A defined `iN` with `N > 64`: an index into `wides`.
    Wide {
        w: u32,
        id: u32,
    },
    /// An `iN` that is `poison`.
    Poison {
        w: u32,
    },
    /// A pointer: an index into `ptrs`.
    Ptr(u32),
    PtrPoison,
    /// A `bN` value: a run in `byte_vals`.
    Bytes {
        start: u32,
        len: u32,
    },
    /// A slot with no value yet.
    Unset,
}

/// A byte in memory (Lean's `Byte`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Byte {
    Bits(u8),
    Poison,
    /// Byte `i` of pointer `ptr` (an index into `ptrs`).
    Frag {
        ptr: u32,
        i: u32,
    },
}

/// A run of entries in a pool.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Span {
    start: u32,
    len: u32,
}

impl Span {
    fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

/// A pointer (Lean's `Ptr`).
#[derive(Clone, Copy, Debug)]
enum Ptr {
    /// Into allocation `alloc`, through tag `tag`, at byte offset `off`.
    Rel { alloc: u32, tag: u32, off: i128 },
    /// A bare address, with the exposed `(allocation, tag)` pairs it may belong to (a run in
    /// `cands`).
    Abs { addr: u64, cands: Span },
}

/// The null pointer's index in `ptrs`.
const NULL: u32 = 0;

/// A stack frame (Lean's `Frame`). The top of the stack is always a `Block`.
#[derive(Clone, Copy, Debug)]
enum Frame {
    /// The rest of a region: the next op to run, and where this block's stack allocations start
    /// in `stack_allocs`.
    Block { next: Option<OpId>, allocs: u32 },
    /// A `cf.if` waiting for its region to `cf.yield`.
    IfJoin { op: OpId },
    /// A running `cf.loop`; `allocs` is where the allocations of its body's blocks start.
    Loop {
        op: OpId,
        progress: bool,
        allocs: u32,
    },
    /// A call: the call op (`None` for the call from outside), the caller's function and slots,
    /// and where the callee's scopes and allocations start.
    Call {
        op: Option<OpId>,
        func: u32,
        base: u32,
        scopes: u32,
        allocs: u32,
    },
}

/// An active `noalias` or `readonly` scope: one pointer parameter during one call.
struct Scope {
    alloc: u32,
    tag: u32,
    noalias: bool,
    readonly: bool,
}

/// A scope's marks per byte: accessed through a derived pointer, through another one, written.
const MARK_DERIVED: u8 = 1;
const MARK_OTHER: u8 = 2;
const MARK_WRITTEN: u8 = 4;
const MARK_BAD: u8 = 7;

/// How an access touches memory.
#[derive(Clone, Copy, PartialEq, Eq)]
enum How {
    Read,
    Write,
    /// `mem.free`: a write of the whole allocation that ends it.
    Free,
}

/// Allocations no larger than this keep their bytes in an array; larger ones in a map.
const DENSE_LIMIT: u64 = 1 << 16;

/// An allocation's bytes. Unwritten bytes are `poison`.
enum Mem {
    /// Bytes from offset 0, as far as the last one written.
    Dense(Vec<Byte>),
    Sparse(FxHashMap<u64, Byte>),
}

impl Mem {
    fn get(&self, off: u64) -> Byte {
        match self {
            Mem::Dense(v) => v.get(off as usize).copied().unwrap_or(Byte::Poison),
            Mem::Sparse(m) => m.get(&off).copied().unwrap_or(Byte::Poison),
        }
    }

    fn set(&mut self, off: u64, b: Byte) {
        match self {
            Mem::Dense(v) => {
                let i = off as usize;
                if v.len() <= i {
                    v.resize(i + 1, Byte::Poison);
                }
                v[i] = b;
            }
            Mem::Sparse(m) => {
                m.insert(off, b);
            }
        }
    }
}

/// What an allocation is: stack memory, or heap memory of an allocator family.
const STACK: u32 = u32::MAX;

/// Allocations, as columns by allocation id.
#[derive(Default)]
struct Allocs {
    size: Vec<u64>,
    align: Vec<u32>,
    /// `STACK`, or the heap family's index in `Machine::families`.
    kind: Vec<u32>,
    live: Vec<bool>,
    /// The address, or 0 before one is observed (addresses are positive).
    base: Vec<u64>,
    /// The head of the list of exposed tags in `Machine::exposures`, newest first.
    exposed: Vec<u32>,
    /// Where it was allocated and where it was freed: only notes read these.
    sites: Vec<(Option<Loc>, Option<Loc>)>,
    bytes: Vec<Mem>,
}

/// How a run ends (Lean's `Behavior`, with the returned values already rendered).
#[derive(Debug)]
enum Behavior {
    Ret(String),
    Trap(TrapReason),
    Ub(UbKind),
    Hole(String),
    Stuck(String),
    Ambiguous,
}

/// A halted run (Lean's `Halt`).
#[derive(Debug)]
struct Halt {
    behavior: Behavior,
    loc: Option<Loc>,
    note: String,
    leaks: Vec<String>,
}

impl Halt {
    /// One line describing how the run ended (Lean's `renderHalt`).
    fn render(&self) -> String {
        let l = match self.loc {
            Some(l) => format!(" @{}:{}", l.line, l.col),
            None => String::new(),
        };
        let mut out = match &self.behavior {
            Behavior::Ret(vs) if vs.is_empty() => "returned".to_owned(),
            Behavior::Ret(vs) => format!("returned {vs}"),
            Behavior::Trap(r) => format!("trap {}{l}", r.name()),
            Behavior::Ub(k) => format!("ub {}{l}", k.name()),
            Behavior::Hole(n) => format!("hole ?{n}{l}"),
            Behavior::Stuck(msg) => format!("stuck{l}: {msg}"),
            Behavior::Ambiguous => format!("ambiguous{l}"),
        };
        if !self.note.is_empty() {
            write!(out, " ({})", self.note).unwrap();
        }
        for leak in &self.leaks {
            out.push_str("; ");
            out.push_str(leak);
        }
        out
    }
}

type R<T> = Result<T, Box<Halt>>;

fn halt<T>(behavior: Behavior, loc: Option<Loc>, note: impl Into<String>) -> R<T> {
    Err(Box::new(Halt {
        behavior,
        loc,
        note: note.into(),
        leaks: Vec::new(),
    }))
}

fn ub<T>(k: UbKind, loc: Option<Loc>, note: impl Into<String>) -> R<T> {
    halt(Behavior::Ub(k), loc, note)
}

fn stuck<T>(loc: Option<Loc>, msg: impl Into<String>) -> R<T> {
    halt(Behavior::Stuck(msg.into()), loc, "")
}

/// `@line:col`, or `@?` (Lean's `renderLoc`).
fn render_loc(loc: Option<Loc>) -> String {
    match loc {
        Some(l) => format!("@{}:{}", l.line, l.col),
        None => "@?".to_owned(),
    }
}

fn align_up(x: u128, a: u128) -> u128 {
    if a <= 1 { x } else { x.div_ceil(a) * a }
}

fn cmp_int(p: Pred, x: i128, y: i128) -> bool {
    match p {
        Pred::Eq => x == y,
        Pred::Ne => x != y,
        Pred::Ult | Pred::Slt => x < y,
        Pred::Ule | Pred::Sle => x <= y,
        Pred::Ugt | Pred::Sgt => x > y,
        Pred::Uge | Pred::Sge => x >= y,
    }
}

/// Lean's `String.toNat?`: decimal digits, optionally separated by single underscores.
pub fn parse_nat(s: &str) -> Option<BigUint> {
    let b = s.as_bytes();
    let ok = !b.is_empty()
        && b.iter().all(|c| c.is_ascii_digit() || *c == b'_')
        && b[0] != b'_'
        && b[b.len() - 1] != b'_'
        && !s.contains("__");
    ok.then(|| {
        let digits: String = s.chars().filter(|c| *c != '_').collect();
        digits.parse().unwrap()
    })
}

/// Lean's `String.toInt?`: a natural number, optionally preceded by `-`.
pub fn parse_int(s: &str) -> Option<BigInt> {
    match s.strip_prefix('-') {
        Some(rest) => parse_nat(rest).map(|n| -BigInt::from(n)),
        None => parse_nat(s).map(BigInt::from),
    }
}

/// Run `@name` in `m` with arguments written as text (integers, `null`, `poison`) for at most
/// `fuel` steps, and describe the outcome in one line, exactly as `fir-ref run` does. Errors are
/// what `fir-ref run` prints on stderr: no such function, a wrong argument count, or a bad
/// argument. `m` must be verified.
pub fn run(m: &Module, name: &str, args: &[&str], fuel: u64) -> Result<String, String> {
    if m.space.addr_bits > 64 {
        return Err(format!(
            "the interpreter supports address sizes up to 64 bits, not {}",
            m.space.addr_bits
        ));
    }
    let Some(fi) = m.funcs.iter().position(|f| f.name == name) else {
        return Err(format!("no function @{name}"));
    };
    let f = &m.funcs[fi];
    let params: Vec<ValueId> = f.body.params(f.body.entry()).collect();
    if args.len() != params.len() {
        return Err(format!(
            "@{name} takes {} arguments but got {}",
            params.len(),
            args.len()
        ));
    }
    let mut mach = Machine::new(m);
    let mut vals = Vec::with_capacity(args.len());
    for (&p, &a) in params.iter().zip(args) {
        vals.push(mach.parse_arg(f.body.ty(p), a)?);
    }
    Ok(match mach.init(fi as u32, &vals) {
        Err(h) => h.render(),
        Ok(()) => mach.drive(fuel),
    })
}

struct Machine<'m> {
    module: &'m Module,
    funcs: FxHashMap<&'m str, u32>,
    space: SpaceCfg,
    // Values
    slots: Vec<Value>,
    wides: Vec<BigUint>,
    byte_vals: Vec<Byte>,
    ptrs: Vec<Ptr>,
    cands: Vec<(u32, u32)>,
    // Memory
    allocs: Allocs,
    /// Exposed-tag lists: `(tag, next)`, linked from `Allocs::exposed`.
    exposures: Vec<(u32, u32)>,
    /// Live allocations that have an address.
    placed: Vec<u32>,
    /// Each tag's parent (`NONE` for an allocation's first tag), by tag id.
    tags: Vec<u32>,
    scopes: Vec<Scope>,
    /// Each scope's marks, by byte offset.
    marks: Vec<FxHashMap<u64, u8>>,
    families: Vec<&'m str>,
    // Control
    stack_allocs: Vec<u32>,
    frames: Vec<Frame>,
    /// The running function and where its slots start.
    func: u32,
    base: u32,
    /// Reused buffers.
    scratch: Vec<Value>,
    bytes_buf: Vec<Byte>,
}

impl<'m> Machine<'m> {
    fn new(module: &'m Module) -> Machine<'m> {
        let mut funcs = FxHashMap::default();
        for (i, f) in module.funcs.iter().enumerate() {
            funcs.insert(f.name.as_str(), i as u32);
        }
        let mut allocs = Allocs::default();
        allocs.size.push(0);
        allocs.align.push(1);
        allocs.kind.push(STACK);
        allocs.live.push(false);
        allocs.base.push(0);
        allocs.exposed.push(NONE);
        allocs.sites.push((None, None));
        allocs.bytes.push(Mem::Dense(Vec::new()));
        Machine {
            module,
            funcs,
            space: module.space,
            slots: Vec::new(),
            wides: Vec::new(),
            byte_vals: Vec::new(),
            ptrs: vec![Ptr::Abs {
                addr: 0,
                cands: Span { start: 0, len: 0 },
            }],
            cands: Vec::new(),
            allocs,
            exposures: Vec::new(),
            placed: Vec::new(),
            tags: vec![NONE],
            scopes: Vec::new(),
            marks: Vec::new(),
            families: Vec::new(),
            stack_allocs: Vec::new(),
            frames: Vec::new(),
            func: 0,
            base: 0,
            scratch: Vec::new(),
            bytes_buf: Vec::new(),
        }
    }

    fn body(&self) -> &'m Body {
        &self.module.funcs[self.func as usize].body
    }

    // Values

    fn int_value(&mut self, w: u32, v: Option<Bits>) -> Value {
        match v {
            None => Value::Poison { w },
            Some(Bits::Small(bits)) => Value::Int { w, bits },
            Some(Bits::Big(n)) => {
                self.wides.push(n);
                Value::Wide {
                    w,
                    id: (self.wides.len() - 1) as u32,
                }
            }
        }
    }

    /// An integer value's bits (`None` for `poison`).
    fn bits(&self, loc: Option<Loc>, v: Value) -> R<Option<Bits>> {
        match v {
            Value::Int { bits, .. } => Ok(Some(Bits::Small(bits))),
            Value::Wide { id, .. } => Ok(Some(Bits::Big(self.wides[id as usize].clone()))),
            Value::Poison { .. } => Ok(None),
            _ => stuck(loc, "expected an integer"),
        }
    }

    fn width(v: Value) -> u32 {
        match v {
            Value::Int { w, .. } | Value::Wide { w, .. } | Value::Poison { w } => w,
            _ => 0,
        }
    }

    fn new_ptr(&mut self, p: Ptr) -> u32 {
        self.ptrs.push(p);
        (self.ptrs.len() - 1) as u32
    }

    fn ptr_of(&self, loc: Option<Loc>, v: Value) -> R<Option<u32>> {
        match v {
            Value::Ptr(p) => Ok(Some(p)),
            Value::PtrPoison => Ok(None),
            _ => stuck(loc, "expected a ptr"),
        }
    }

    fn cands(&self, s: Span) -> &[(u32, u32)] {
        &self.cands[s.range()]
    }

    /// Structural equality of pointers, as Lean compares them.
    fn ptr_eq(&self, p: u32, q: u32) -> bool {
        if p == q {
            return true;
        }
        match (self.ptrs[p as usize], self.ptrs[q as usize]) {
            (
                Ptr::Rel { alloc, tag, off },
                Ptr::Rel {
                    alloc: a2,
                    tag: t2,
                    off: o2,
                },
            ) => alloc == a2 && tag == t2 && off == o2,
            (
                Ptr::Abs { addr, cands },
                Ptr::Abs {
                    addr: a2,
                    cands: c2,
                },
            ) => addr == a2 && self.cands(cands) == self.cands(c2),
            _ => false,
        }
    }

    fn has_ty(&self, v: Value, t: Ty) -> bool {
        match (v, t) {
            (Value::Int { w, .. } | Value::Wide { w, .. } | Value::Poison { w }, Ty::Int(w2)) => {
                w == w2
            }
            (Value::Ptr(_) | Value::PtrPoison, Ty::Ptr) => true,
            (Value::Bytes { len, .. }, Ty::Byte(w)) => u64::from(len) * 8 == u64::from(w),
            _ => false,
        }
    }

    fn render_ptr(&self, p: u32, out: &mut String) {
        match self.ptrs[p as usize] {
            Ptr::Rel { alloc, off, .. } => {
                if off == 0 {
                    write!(out, "#{alloc}")
                } else if off > 0 {
                    write!(out, "#{alloc}+{off}")
                } else {
                    write!(out, "#{alloc}{off}")
                }
            }
            .unwrap(),
            Ptr::Abs { addr: 0, cands } if cands.len == 0 => out.push_str("null"),
            Ptr::Abs { addr, .. } => write!(out, "{addr:#x}").unwrap(),
        }
    }

    /// Lean's `RVal.render`.
    fn render_value(&self, v: Value, out: &mut String) {
        match v {
            Value::Int { w: 1, bits } => write!(out, "i1 {bits}").unwrap(),
            Value::Int { w, bits } => write!(out, "i{w} {}", sem::sext64(w, bits)).unwrap(),
            Value::Wide { w, id } => {
                let n = Bits::Big(self.wides[id as usize].clone()).to_int(w);
                write!(out, "i{w} {n}").unwrap();
            }
            Value::Poison { w } => write!(out, "i{w} poison").unwrap(),
            Value::Ptr(p) => {
                out.push_str("ptr ");
                self.render_ptr(p, out);
            }
            Value::PtrPoison => out.push_str("ptr poison"),
            Value::Bytes { start, len } => {
                write!(out, "b{} (", u64::from(len) * 8).unwrap();
                let span = Span { start, len };
                for (i, b) in self.byte_vals[span.range()].iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    match *b {
                        Byte::Bits(x) => write!(out, "{x:#x}").unwrap(),
                        Byte::Poison => out.push_str("poison"),
                        Byte::Frag { ptr, i } => {
                            self.render_ptr(ptr, out);
                            write!(out, "[{i}]").unwrap();
                        }
                    }
                }
                out.push(')');
            }
            Value::Unset => out.push('?'),
        }
    }

    /// Lean's `parseArg`.
    fn parse_arg(&mut self, t: Ty, s: &str) -> Result<Value, String> {
        match (t, s) {
            (Ty::Int(w), "poison") => Ok(Value::Poison { w }),
            (Ty::Int(w), _) => match parse_int(s) {
                Some(n) => Ok(self.int_value(w, Some(sem::konst(w, &n)))),
                None => Err(format!("bad argument '{s}': expected an integer or poison")),
            },
            (Ty::Ptr, "null") => Ok(Value::Ptr(NULL)),
            (Ty::Ptr, "poison") => Ok(Value::PtrPoison),
            _ => Err(format!("bad argument '{s}' for {t}")),
        }
    }

    // Environment

    fn slot(&self, v: ValueId) -> usize {
        self.base as usize + v.index()
    }

    fn operand(&self, loc: Option<Loc>, o: Operand) -> R<Value> {
        match o.get() {
            OperandKind::Value(v) => match self.slots[self.slot(v)] {
                Value::Unset => stuck(loc, format!("%{} is not defined", self.body().name(v))),
                x => Ok(x),
            },
            OperandKind::Hole(h) => {
                halt(Behavior::Hole(self.body().hole_name(h).to_owned()), loc, "")
            }
        }
    }

    /// Evaluate an op's operands into `vs`.
    fn operands(&self, op: OpId, loc: Option<Loc>, vs: &mut Vec<Value>) -> R<()> {
        vs.clear();
        for &o in self.body().operands(op) {
            vs.push(self.operand(loc, o)?);
        }
        Ok(())
    }

    /// Bind values, then check their facts: a violated fact is UB (Lean's `bindResults`).
    fn bind(
        &mut self,
        loc: Option<Loc>,
        rs: impl ExactSizeIterator<Item = ValueId> + Clone,
        vs: &[Value],
    ) -> R<()> {
        let body = self.body();
        if rs.len() != vs.len() {
            return stuck(loc, "wrong number of values");
        }
        for (r, &v) in rs.clone().zip(vs) {
            let t = body.ty(r);
            if !self.has_ty(v, t) {
                return stuck(
                    loc,
                    format!("%{} has type {t} but got another type", body.name(r)),
                );
            }
            let s = self.slot(r);
            self.slots[s] = v;
        }
        for (r, &v) in rs.zip(vs) {
            for f in body.facts(r) {
                if !self.fact_holds(f.fact, v)? {
                    return ub(
                        UbKind::Fact,
                        loc,
                        format!("%{} breaks a fact", body.name(r)),
                    );
                }
            }
        }
        Ok(())
    }

    fn fact_holds(&self, f: Fact, v: Value) -> R<bool> {
        let body = self.body();
        Ok(match (f, v) {
            (
                Fact::RangeS(lo, hi) | Fact::RangeU(lo, hi),
                Value::Int { .. } | Value::Wide { .. },
            ) => {
                let w = Self::width(v);
                let b = self.bits(None, v)?.unwrap();
                let signed = matches!(f, Fact::RangeS(..));
                match (body.int(lo), body.int(hi), &b) {
                    (Int::Small(lo), Int::Small(hi), Bits::Small(x)) => {
                        let x = if signed {
                            i128::from(sem::sext64(w, *x))
                        } else {
                            i128::from(*x)
                        };
                        i128::from(lo) <= x && x <= i128::from(hi)
                    }
                    (lo, hi, _) => {
                        let x = if signed {
                            b.to_int(w)
                        } else {
                            BigInt::from(b.to_nat())
                        };
                        lo.to_bigint() <= x && x <= hi.to_bigint()
                    }
                }
            }
            (Fact::NonNull, Value::Ptr(p)) => {
                !matches!(self.ptrs[p as usize], Ptr::Abs { addr: 0, .. })
            }
            (Fact::Align(n), Value::Ptr(p)) => match self.ptrs[p as usize] {
                Ptr::Rel { alloc, off, .. } => self.aligned_at(alloc, off, n),
                Ptr::Abs { addr, .. } => addr % n == 0,
            },
            _ => true,
        })
    }

    // Allocations

    /// Lean's `Alloc.alignedAt`.
    fn aligned_at(&self, a: u32, off: i128, n: u64) -> bool {
        let n = i128::from(n);
        let a = a as usize;
        (off.rem_euclid(n) == 0 && i128::from(self.allocs.align[a]) >= n)
            || (self.allocs.base[a] != 0
                && (i128::from(self.allocs.base[a]) + off).rem_euclid(n) == 0)
    }

    fn family(&mut self, name: &'m str) -> u32 {
        match self.families.iter().position(|f| *f == name) {
            Some(i) => i as u32,
            None => {
                self.families.push(name);
                (self.families.len() - 1) as u32
            }
        }
    }

    fn fresh_tag(&mut self, parent: u32) -> u32 {
        self.tags.push(parent);
        (self.tags.len() - 1) as u32
    }

    /// Lean's `newAlloc`: a fresh allocation and its first tag.
    fn new_alloc(&mut self, loc: Option<Loc>, size: u64, align: u32, kind: u32) -> u32 {
        let a = &mut self.allocs;
        let id = a.size.len() as u32;
        a.size.push(size);
        a.align.push(align);
        a.kind.push(kind);
        a.live.push(true);
        a.base.push(0);
        a.exposed.push(NONE);
        a.sites.push((loc, None));
        a.bytes.push(if size <= DENSE_LIMIT {
            Mem::Dense(Vec::new())
        } else {
            Mem::Sparse(FxHashMap::default())
        });
        let tag = self.fresh_tag(NONE);
        self.new_ptr(Ptr::Rel {
            alloc: id,
            tag,
            off: 0,
        })
    }

    fn kill(&mut self, a: u32) {
        self.allocs.live[a as usize] = false;
        if self.allocs.base[a as usize] != 0
            && let Some(i) = self.placed.iter().position(|&x| x == a)
        {
            self.placed.swap_remove(i);
        }
    }

    /// End the stack allocations made since `mark` (Lean's `releaseIds`).
    fn release_from(&mut self, mark: u32) {
        while self.stack_allocs.len() > mark as usize {
            let a = self.stack_allocs.pop().unwrap();
            self.kill(a);
        }
    }

    fn dead_note(&self, a: u32) -> String {
        let (site, freed) = self.allocs.sites[a as usize];
        if self.allocs.kind[a as usize] == STACK {
            format!(
                "stack memory from {}, whose region has ended",
                render_loc(site)
            )
        } else {
            format!(
                "allocated at {}, freed at {}",
                render_loc(site),
                render_loc(freed)
            )
        }
    }

    // Addresses

    fn limit(&self) -> u128 {
        1u128 << self.space.addr_bits
    }

    /// Give an allocation its address if it has none: the lowest free one from `0x1000`
    /// (Lean's `realize`).
    fn realize(&mut self, loc: Option<Loc>, a: u32) -> R<u64> {
        let ai = a as usize;
        if self.allocs.base[ai] != 0 {
            return Ok(self.allocs.base[ai]);
        }
        let size = self.allocs.size[ai];
        let span = u128::from(size.max(1));
        let align = u128::from(self.allocs.align[ai]);
        let limit = self.limit();
        let taken: Vec<(u128, u128)> = self
            .placed
            .iter()
            .map(|&x| {
                let b = u128::from(self.allocs.base[x as usize]);
                (b, b + u128::from(self.allocs.size[x as usize].max(1)))
            })
            .collect();
        let fits = |b: u128| {
            b > 0
                && b.is_multiple_of(align)
                && b + span <= limit
                && taken.iter().all(|&(lo, hi)| b + span <= lo || hi <= b)
        };
        let best = std::iter::once(align_up(0x1000, align))
            .chain(taken.iter().map(|&(_, hi)| align_up(hi, align)))
            .filter(|&b| fits(b))
            .min();
        let Some(b) = best else {
            return ub(
                UbKind::AddressSpace,
                loc,
                format!("no room for {size} bytes"),
            );
        };
        self.allocs.base[ai] = b as u64;
        if self.allocs.live[ai] {
            self.placed.push(a);
        }
        Ok(b as u64)
    }

    fn addr_mod(&self, x: i128) -> u64 {
        x.rem_euclid(self.limit() as i128) as u64
    }

    /// A pointer's address, without exposing it (Lean's `ptrAddr`).
    fn ptr_addr(&mut self, loc: Option<Loc>, p: u32) -> R<u64> {
        match self.ptrs[p as usize] {
            Ptr::Rel { alloc, off, .. } => {
                let b = self.realize(loc, alloc)?;
                Ok(self.addr_mod(i128::from(b) + off))
            }
            Ptr::Abs { addr, .. } => Ok(addr),
        }
    }

    /// A pointer's address, exposing its allocation and tag (Lean's `ptrExpose`).
    fn ptr_expose(&mut self, loc: Option<Loc>, p: u32) -> R<u64> {
        let addr = self.ptr_addr(loc, p)?;
        if let Ptr::Rel { alloc, tag, .. } = self.ptrs[p as usize] {
            let mut cur = self.allocs.exposed[alloc as usize];
            while cur != NONE {
                let (t, next) = self.exposures[cur as usize];
                if t == tag {
                    return Ok(addr);
                }
                cur = next;
            }
            self.exposures
                .push((tag, self.allocs.exposed[alloc as usize]));
            self.allocs.exposed[alloc as usize] = (self.exposures.len() - 1) as u32;
        }
        Ok(addr)
    }

    /// A pointer from an address: every exposed `(allocation, tag)` whose allocation is live and
    /// contains the address or ends at it (Lean's `fromExposed`).
    fn exposed_ptr(&mut self, n: u64) -> u32 {
        let mut hits: Vec<u32> = self
            .placed
            .iter()
            .copied()
            .filter(|&a| {
                let b = self.allocs.base[a as usize];
                b <= n && u128::from(n) <= u128::from(b) + u128::from(self.allocs.size[a as usize])
            })
            .collect();
        hits.sort_unstable();
        let start = self.cands.len();
        for a in hits {
            let mut cur = self.allocs.exposed[a as usize];
            while cur != NONE {
                let (t, next) = self.exposures[cur as usize];
                self.cands.push((a, t));
                cur = next;
            }
        }
        let cands = Span {
            start: start as u32,
            len: (self.cands.len() - start) as u32,
        };
        self.new_ptr(Ptr::Abs { addr: n, cands })
    }

    // Accesses

    /// Whether tag `t` is `anc` or derived from it.
    fn is_derived(&self, anc: u32, mut t: u32) -> bool {
        loop {
            if t == anc {
                return true;
            }
            t = self.tags[t as usize];
            if t == NONE {
                return false;
            }
        }
    }

    /// The allocation, tag, and offset a pointer accesses (Lean's `resolveIn`).
    fn resolve(&self, loc: Option<Loc>, p: u32, size: u64) -> R<(u32, u32, i128)> {
        let (addr, cands) = match self.ptrs[p as usize] {
            Ptr::Rel { alloc, tag, off } => return Ok((alloc, tag, off)),
            Ptr::Abs { addr, cands } => (addr, cands),
        };
        let fits = |&(a, _): &(u32, u32)| {
            let a = a as usize;
            let b = self.allocs.base[a];
            self.allocs.live[a]
                && b != 0
                && b <= addr
                && u128::from(addr) + u128::from(size)
                    <= u128::from(b) + u128::from(self.allocs.size[a])
        };
        let all = self.cands(cands);
        let mut fit = all.iter().filter(|c| fits(c));
        let Some(&(a, t)) = fit.next() else {
            return if all.is_empty() {
                ub(
                    UbKind::NoProvenance,
                    loc,
                    format!("address {addr} belongs to no exposed allocation"),
                )
            } else {
                ub(
                    UbKind::OutOfBounds,
                    loc,
                    format!("address {addr} is outside every allocation it may belong to"),
                )
            };
        };
        let rest: Vec<(u32, u32)> = fit.copied().collect();
        if let Some(&(a2, _)) = rest.iter().find(|x| x.0 != a) {
            return halt(
                Behavior::Ambiguous,
                loc,
                format!("address {addr} may belong to #{a} or #{a2}"),
            );
        }
        let tell_apart = |t2: u32| {
            self.scopes
                .iter()
                .any(|s| s.alloc == a && self.is_derived(s.tag, t) != self.is_derived(s.tag, t2))
        };
        if let Some(&(_, t2)) = rest.iter().find(|x| tell_apart(x.1)) {
            return halt(
                Behavior::Ambiguous,
                loc,
                format!(
                    "address {addr} may carry tag {t} or {t2} of #{a}, and an active noalias or readonly scope tells them apart"
                ),
            );
        }
        let b = self.allocs.base[a as usize];
        Ok((a, t, i128::from(addr) - i128::from(b)))
    }

    /// Where an access goes, after checking lifetime, bounds, and alignment (Lean's
    /// `checkAccess`).
    fn check_access(&self, loc: Option<Loc>, p: u32, size: u64, align: u32) -> R<(u32, u32, u64)> {
        let (a, t, off) = self.resolve(loc, p, size)?;
        let ai = a as usize;
        if !self.allocs.live[ai] {
            return ub(UbKind::UseAfterFree, loc, self.dead_note(a));
        }
        let asize = self.allocs.size[ai];
        if !(0 <= off && off + i128::from(size) <= i128::from(asize)) {
            return ub(
                UbKind::OutOfBounds,
                loc,
                format!("offset {off}, {size} bytes, allocation size {asize}"),
            );
        }
        if !self.aligned_at(a, off, u64::from(align)) {
            let b = self.allocs.base[ai];
            let note = if b != 0 {
                format!(
                    "address {} is not a multiple of {align}",
                    i128::from(b) + off
                )
            } else {
                format!(
                    "offset {off} in an allocation aligned to {} with no address yet, access needs {align}",
                    self.allocs.align[ai]
                )
            };
            return ub(UbKind::Misaligned, loc, note);
        }
        Ok((a, t, off as u64))
    }

    /// Record an access to `size` bytes of allocation `a` from `off`, through tag `t`, in each
    /// active scope (Lean's `markAll`). For `free`, which writes the whole allocation and ends
    /// it, only the bytes already marked can go bad, and the new marks are never read again, so
    /// they aren't recorded.
    fn mark_all(
        &mut self,
        loc: Option<Loc>,
        a: u32,
        t: u32,
        off: u64,
        size: u64,
        how: How,
    ) -> R<()> {
        let write = how != How::Read;
        let free = how == How::Free;
        for i in 0..self.scopes.len() {
            let s = &self.scopes[i];
            if s.alloc != a {
                continue;
            }
            let derived = self.is_derived(s.tag, t);
            if s.readonly && write && derived {
                return ub(
                    UbKind::ReadOnly,
                    loc,
                    "write through a pointer derived from a readonly parameter",
                );
            }
            if !s.noalias {
                continue;
            }
            let add = if derived { MARK_DERIVED } else { MARK_OTHER }
                | if write { MARK_WRITTEN } else { 0 };
            let marks = &mut self.marks[i];
            let bad = if free {
                marks
                    .iter()
                    .filter(|&(&o, &mk)| o >= off && o - off < size && mk | add == MARK_BAD)
                    .map(|(&o, _)| o)
                    .min()
            } else {
                (off..off + size).find(|o| marks.get(o).copied().unwrap_or(0) | add == MARK_BAD)
            };
            if let Some(o) = bad {
                return ub(
                    UbKind::NoAlias,
                    loc,
                    format!(
                        "byte {o} of #{a} is accessed both through a noalias parameter and another pointer, and written"
                    ),
                );
            }
            if !free {
                for o in off..off + size {
                    *marks.entry(o).or_insert(0) |= add;
                }
            }
        }
        Ok(())
    }

    /// Check an access and record it in the active scopes (Lean's `access`).
    fn access(
        &mut self,
        loc: Option<Loc>,
        p: u32,
        size: u64,
        align: u32,
        write: bool,
    ) -> R<(u32, u64)> {
        let (a, t, off) = self.check_access(loc, p, size, align)?;
        self.mark_all(
            loc,
            a,
            t,
            off,
            size,
            if write { How::Write } else { How::Read },
        )?;
        Ok((a, off))
    }

    /// Turn a pointer fragment into an address byte, exposing its pointer (Lean's
    /// `fragToBits`).
    fn frag_to_bits(&mut self, loc: Option<Loc>, b: Byte) -> R<Byte> {
        match b {
            Byte::Frag { ptr, i } => {
                let addr = self.ptr_expose(loc, ptr)?;
                let digit = if i < self.space.addr_bits / 8 {
                    (addr >> (8 * i)) as u8
                } else {
                    0
                };
                Ok(Byte::Bits(digit))
            }
            b => Ok(b),
        }
    }

    /// Bytes as a value of type `ty` (Lean's `decodeAs`). `bytes_buf` holds the bytes.
    fn decode(&mut self, loc: Option<Loc>, ty: Ty) -> R<Value> {
        let mut bs = std::mem::take(&mut self.bytes_buf);
        let v = match ty {
            Ty::Byte(_) => {
                let start = self.byte_vals.len() as u32;
                self.byte_vals.extend_from_slice(&bs);
                Value::Bytes {
                    start,
                    len: bs.len() as u32,
                }
            }
            Ty::Int(w) => {
                for b in bs.iter_mut() {
                    *b = self.frag_to_bits(loc, *b)?;
                }
                let v = self.decode_int(w, &bs);
                self.int_value(w, v)
            }
            Ty::Ptr => {
                if bs.contains(&Byte::Poison) {
                    Value::PtrPoison
                } else if let Some(p) = self.ptr_of_frags(&bs) {
                    Value::Ptr(p)
                } else {
                    for b in bs.iter_mut() {
                        *b = self.frag_to_bits(loc, *b)?;
                    }
                    // The address is the low address-size bits of the pointer-size integer.
                    let n = (self.space.addr_bits / 8) as usize;
                    let addr = bs
                        .iter()
                        .take(n)
                        .enumerate()
                        .fold(0u64, |acc, (i, b)| match b {
                            Byte::Bits(x) => acc | u64::from(*x) << (8 * i),
                            _ => acc,
                        });
                    Value::Ptr(self.exposed_ptr(addr))
                }
            }
        };
        self.bytes_buf = bs;
        Ok(v)
    }

    /// Bytes without fragments as an integer; any `poison` byte makes it `poison`.
    fn decode_int(&self, w: u32, bs: &[Byte]) -> Option<Bits> {
        let mut raw = Vec::with_capacity(bs.len());
        for b in bs {
            match b {
                Byte::Bits(x) => raw.push(*x),
                _ => return None,
            }
        }
        Some(sem::from_le_bytes(w, &raw))
    }

    /// The pointer whose fragments these bytes are, in order (Lean's `ptrOfFrags?`).
    fn ptr_of_frags(&self, bs: &[Byte]) -> Option<u32> {
        let Some(&Byte::Frag { ptr, i: 0 }) = bs.first() else {
            return None;
        };
        bs.iter()
            .enumerate()
            .all(|(k, b)| matches!(*b, Byte::Frag { ptr: q, i } if i as usize == k && self.ptr_eq(ptr, q)))
            .then_some(ptr)
    }

    fn ty_size(&self, t: Ty) -> u64 {
        match t {
            Ty::Int(w) | Ty::Byte(w) => u64::from(w / 8),
            Ty::Ptr => u64::from(self.space.ptr_bits / 8),
        }
    }

    fn load(&mut self, loc: Option<Loc>, ty: Ty, align: u32, p: Option<u32>) -> R<Value> {
        let Some(p) = p else {
            return ub(UbKind::Poison, loc, "load through a poison pointer");
        };
        let size = self.ty_size(ty);
        let (a, off) = self.access(loc, p, size, align, false)?;
        let mem = &self.allocs.bytes[a as usize];
        self.bytes_buf.clear();
        self.bytes_buf.extend((0..size).map(|i| mem.get(off + i)));
        self.decode(loc, ty)
    }

    /// A value's bytes (Lean's `RVal.encode`), into `bytes_buf`.
    fn encode(&mut self, v: Value) {
        let mut bs = std::mem::take(&mut self.bytes_buf);
        bs.clear();
        let pb = self.space.ptr_bits / 8;
        match v {
            Value::Int { w, bits } => {
                let mut raw = Vec::new();
                sem::to_le_bytes(w, &Bits::Small(bits), &mut raw);
                bs.extend(raw.into_iter().map(Byte::Bits));
            }
            Value::Wide { w, id } => {
                let mut raw = Vec::new();
                sem::to_le_bytes(w, &Bits::Big(self.wides[id as usize].clone()), &mut raw);
                bs.extend(raw.into_iter().map(Byte::Bits));
            }
            Value::Poison { w } => bs.extend((0..w / 8).map(|_| Byte::Poison)),
            Value::Ptr(p) => bs.extend((0..pb).map(|i| Byte::Frag { ptr: p, i })),
            Value::PtrPoison => bs.extend((0..pb).map(|_| Byte::Poison)),
            Value::Bytes { start, len } => {
                bs.extend_from_slice(&self.byte_vals[Span { start, len }.range()])
            }
            Value::Unset => {}
        }
        self.bytes_buf = bs;
    }

    fn store(&mut self, loc: Option<Loc>, ty: Ty, align: u32, v: Value, p: Option<u32>) -> R<()> {
        let Some(p) = p else {
            return ub(UbKind::Poison, loc, "store through a poison pointer");
        };
        if !self.has_ty(v, ty) {
            return stuck(loc, format!("the stored value isn't a {ty}"));
        }
        self.encode(v);
        let n = self.bytes_buf.len() as u64;
        let (a, off) = self.access(loc, p, n, align, true)?;
        let mem = &mut self.allocs.bytes[a as usize];
        for (i, b) in self.bytes_buf.iter().enumerate() {
            mem.set(off + i as u64, *b);
        }
        Ok(())
    }

    /// Lean's `freePtr`.
    fn free(&mut self, loc: Option<Loc>, family: &'m str, p: Option<u32>) -> R<()> {
        let Some(p) = p else {
            return ub(UbKind::Poison, loc, "");
        };
        if let Ptr::Abs { addr: 0, .. } = self.ptrs[p as usize] {
            return Ok(());
        }
        let (a, t, off) = self.resolve(loc, p, 0)?;
        let ai = a as usize;
        let kind = self.allocs.kind[ai];
        if !self.allocs.live[ai] {
            let k = if kind == STACK {
                UbKind::BadFree
            } else {
                UbKind::DoubleFree
            };
            return ub(k, loc, self.dead_note(a));
        }
        let fam = self.family(family);
        if kind != fam {
            let by = if kind == STACK {
                "mem.stack"
            } else {
                self.families[kind as usize]
            };
            return ub(
                UbKind::BadFree,
                loc,
                format!(
                    "allocated at {} by {by}",
                    render_loc(self.allocs.sites[ai].0)
                ),
            );
        }
        if off != 0 {
            return ub(
                UbKind::BadFree,
                loc,
                format!("offset {off} is not the start of the allocation"),
            );
        }
        self.mark_all(loc, a, t, 0, self.allocs.size[ai], How::Free)?;
        self.kill(a);
        self.allocs.sites[ai].1 = loc;
        Ok(())
    }

    // Pointer comparison

    /// The allocation and offset a pointer points into, if any (Lean's `ptrView`).
    fn ptr_view(&self, p: u32) -> Option<(u32, i128)> {
        match self.ptrs[p as usize] {
            Ptr::Rel { alloc, off, .. } => Some((alloc, off)),
            Ptr::Abs { addr, cands } => {
                let in_range = |strict: bool| {
                    self.cands(cands).iter().find_map(|&(a, _)| {
                        let ai = a as usize;
                        let b = self.allocs.base[ai];
                        let end = u128::from(b) + u128::from(self.allocs.size[ai]);
                        let x = u128::from(addr);
                        (self.allocs.live[ai]
                            && b != 0
                            && b <= addr
                            && (x < end || (!strict && x == end)))
                            .then_some((a, i128::from(addr) - i128::from(b)))
                    })
                };
                in_range(true).or_else(|| in_range(false))
            }
        }
    }

    fn cmp_ptrs(&mut self, loc: Option<Loc>, pred: Pred, p: u32, q: u32) -> R<bool> {
        let is_eq = matches!(pred, Pred::Eq | Pred::Ne);
        match (self.ptr_view(p), self.ptr_view(q)) {
            (Some((a, o)), Some((b, o2))) => {
                if a == b {
                    return Ok(cmp_int(pred, o, o2));
                }
                if !is_eq {
                    return ub(
                        UbKind::PtrCompare,
                        loc,
                        "ordered comparison of pointers into different allocations",
                    );
                }
                // Pointers into different allocations are never equal; with one past the end
                // the oracle decides, and its `0` says "not equal" too.
                Ok(pred != Pred::Eq)
            }
            _ => {
                if !is_eq {
                    return ub(
                        UbKind::PtrCompare,
                        loc,
                        "ordered comparison of pointers outside allocations",
                    );
                }
                let x = self.ptr_addr(loc, p)?;
                let y = self.ptr_addr(loc, q)?;
                Ok(cmp_int(pred, i128::from(x), i128::from(y)))
            }
        }
    }

    // Ops

    fn int_out(&mut self, loc: Option<Loc>, w: u32, o: Out) -> R<Value> {
        match o {
            Out::Val(v) => Ok(self.int_value(w, v)),
            Out::Trap(r) => halt(Behavior::Trap(r), loc, ""),
            Out::Ub(k) => ub(k, loc, ""),
        }
    }

    fn addr_value(&self, n: u64) -> Value {
        Value::Int {
            w: self.space.addr_bits,
            bits: n,
        }
    }

    /// The address-size integer operand `v`, or `None` for `poison`.
    fn addr_operand(&self, loc: Option<Loc>, v: Value) -> R<Option<u64>> {
        Ok(self.bits(loc, v)?.map(|b| b.to_u64().unwrap()))
    }

    /// Evaluate an op without regions that doesn't touch the stack (Lean's `evalSimple`).
    /// `rty` is the type of its result, if it has one.
    fn simple(
        &mut self,
        loc: Option<Loc>,
        k: OpKind,
        rty: Option<Ty>,
        vs: &[Value],
    ) -> R<Option<Value>> {
        let body = self.body();
        let rw = match rty {
            Some(Ty::Int(w)) => w,
            _ => 0,
        };
        let aw = self.space.addr_bits;
        let v = match (k, vs) {
            (OpKind::Const(n), []) => {
                let b = match body.int(n) {
                    Int::Small(n) => Bits::of_i128(rw, i128::from(n)),
                    Int::Big(n) => sem::konst(rw, n),
                };
                self.int_value(rw, Some(b))
            }
            (OpKind::Poison, []) => Value::Poison { w: rw },
            (OpKind::Freeze, &[Value::Poison { w }]) => self.int_value(w, Some(Bits::zero(w))),
            (OpKind::Freeze | OpKind::Copy, &[v]) => v,
            (OpKind::Select, &[c, a, b]) => {
                let c = self.bits(loc, c)?;
                self.bits(loc, a)?;
                self.bits(loc, b)?;
                match c {
                    None => Value::Poison { w: rw },
                    Some(c) if !c.is_zero() => a,
                    Some(_) => b,
                }
            }
            (OpKind::Arith(op, ovf), &[a, b]) => {
                let (a, b) = (self.bits(loc, a)?, self.bits(loc, b)?);
                let o = sem::arith(op, ovf, rw, a.as_ref(), b.as_ref());
                self.int_out(loc, rw, o)?
            }
            (OpKind::Bit(op), &[a, b]) => {
                let (a, b) = (self.bits(loc, a)?, self.bits(loc, b)?);
                let v = sem::bit(op, a.as_ref(), b.as_ref());
                self.int_value(rw, v)
            }
            (OpKind::Div(op, zero, ovf), &[a, b]) => {
                let (a, b) = (self.bits(loc, a)?, self.bits(loc, b)?);
                let o = sem::div(op, zero, ovf, rw, a.as_ref(), b.as_ref());
                self.int_out(loc, rw, o)?
            }
            (OpKind::Shift(op, edge), &[a, b]) => {
                let (a, b) = (self.bits(loc, a)?, self.bits(loc, b)?);
                let o = sem::shift(op, edge, rw, a.as_ref(), b.as_ref());
                self.int_out(loc, rw, o)?
            }
            (OpKind::Cmp(p), &[a, b]) => {
                let w = Self::width(a);
                let (a, b) = (self.bits(loc, a)?, self.bits(loc, b)?);
                match (a, b) {
                    (Some(a), Some(b)) => Value::Int {
                        w: 1,
                        bits: u64::from(sem::cmp_bits(p, w, &a, &b)),
                    },
                    _ => Value::Poison { w: 1 },
                }
            }
            (OpKind::Zext | OpKind::Sext | OpKind::Trunc(_), &[a]) => {
                let w = Self::width(a);
                let r = self.bits(loc, a)?.and_then(|x| match k {
                    OpKind::Zext => Some(sem::zext(rw, &x)),
                    OpKind::Sext => Some(sem::sext(w, rw, &x)),
                    OpKind::Trunc(mode) => sem::trunc(mode, w, rw, &x),
                    _ => unreachable!(),
                });
                self.int_value(rw, r)
            }
            (OpKind::MemAlloc { family, align, .. }, &[n]) => {
                let Some(size) = self.addr_operand(loc, n)? else {
                    return ub(UbKind::Poison, loc, "allocation size is poison");
                };
                let fam = self.family(body.str(family));
                Value::Ptr(self.new_alloc(loc, size, align, fam))
            }
            (OpKind::MemFree { family }, &[p]) => {
                let p = self.ptr_of(loc, p)?;
                self.free(loc, body.str(family), p)?;
                return Ok(None);
            }
            (OpKind::Load { align }, &[p]) => {
                let p = self.ptr_of(loc, p)?;
                self.load(loc, rty.unwrap(), align, p)?
            }
            (OpKind::Store { ty, align }, &[v, p]) => {
                let p = self.ptr_of(loc, p)?;
                self.store(loc, ty, align, v, p)?;
                return Ok(None);
            }
            (OpKind::PtrNull, []) => Value::Ptr(NULL),
            (OpKind::PtrOffset { inbounds }, &[p, n]) => {
                let Some(p) = self.ptr_of(loc, p)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let Some(n) = self.addr_operand(loc, n)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let n = i128::from(sem::sext64(aw, n));
                if n == 0 {
                    return Ok(Some(Value::Ptr(p)));
                }
                match self.ptrs[p as usize] {
                    Ptr::Rel { alloc, tag, off } => {
                        let ai = alloc as usize;
                        let size = i128::from(self.allocs.size[ai]);
                        let ok = self.allocs.live[ai]
                            && 0 <= off
                            && off <= size
                            && 0 <= off + n
                            && off + n <= size;
                        if inbounds && !ok {
                            Value::PtrPoison
                        } else {
                            Value::Ptr(self.new_ptr(Ptr::Rel {
                                alloc,
                                tag,
                                off: off + n,
                            }))
                        }
                    }
                    Ptr::Abs { addr, cands } => {
                        let addr2 = self.addr_mod(i128::from(addr) + n);
                        if !inbounds {
                            return Ok(Some(Value::Ptr(
                                self.new_ptr(Ptr::Abs { addr: addr2, cands }),
                            )));
                        }
                        let start = self.cands.len();
                        for i in cands.range() {
                            let (a, t) = self.cands[i];
                            let ai = a as usize;
                            let b = i128::from(self.allocs.base[ai]);
                            let end = b + i128::from(self.allocs.size[ai]);
                            let x = i128::from(addr);
                            if self.allocs.live[ai]
                                && b != 0
                                && b <= x
                                && x <= end
                                && b <= x + n
                                && x + n <= end
                            {
                                self.cands.push((a, t));
                            }
                        }
                        let keep = Span {
                            start: start as u32,
                            len: (self.cands.len() - start) as u32,
                        };
                        if keep.len == 0 {
                            Value::PtrPoison
                        } else {
                            Value::Ptr(self.new_ptr(Ptr::Abs {
                                addr: addr2,
                                cands: keep,
                            }))
                        }
                    }
                }
            }
            (OpKind::PtrAddr | OpKind::PtrExpose, &[p]) => {
                let Some(p) = self.ptr_of(loc, p)? else {
                    return Ok(Some(Value::Poison { w: aw }));
                };
                let addr = if k == OpKind::PtrAddr {
                    self.ptr_addr(loc, p)?
                } else {
                    self.ptr_expose(loc, p)?
                };
                self.addr_value(addr)
            }
            (OpKind::PtrFromExposed, &[n]) => match self.addr_operand(loc, n)? {
                None => Value::PtrPoison,
                Some(n) => Value::Ptr(self.exposed_ptr(n)),
            },
            (OpKind::PtrWithAddr, &[p, n]) => {
                let Some(p) = self.ptr_of(loc, p)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let Some(n) = self.addr_operand(loc, n)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let q = match self.ptrs[p as usize] {
                    Ptr::Rel { alloc, tag, .. } => {
                        let b = self.realize(loc, alloc)?;
                        Ptr::Rel {
                            alloc,
                            tag,
                            off: i128::from(n) - i128::from(b),
                        }
                    }
                    Ptr::Abs { cands, .. } => Ptr::Abs { addr: n, cands },
                };
                Value::Ptr(self.new_ptr(q))
            }
            (OpKind::PtrCmp(pred), &[p, q]) => {
                let (p, q) = (self.ptr_of(loc, p)?, self.ptr_of(loc, q)?);
                let (Some(p), Some(q)) = (p, q) else {
                    return Ok(Some(Value::Poison { w: 1 }));
                };
                Value::Int {
                    w: 1,
                    bits: u64::from(self.cmp_ptrs(loc, pred, p, q)?),
                }
            }
            _ => return stuck(loc, "malformed op"),
        };
        Ok(Some(v))
    }

    /// Bind a callee's parameters and open its `noalias` and `readonly` scopes; the callee's
    /// slots are current (Lean's `enterCall`).
    fn enter_call(&mut self, loc: Option<Loc>, vs: &[Value]) -> R<()> {
        let body = self.body();
        let params = body.params(body.entry());
        self.bind(loc, params.clone(), vs)?;
        for (r, &v) in params.zip(vs) {
            let facts = body.facts(r);
            let noalias = facts.iter().any(|f| f.fact == Fact::NoAlias);
            let readonly = facts.iter().any(|f| f.fact == Fact::ReadOnly);
            if !(noalias || readonly) {
                continue;
            }
            let Value::Ptr(p) = v else { continue };
            // A pointer that can't access memory opens no scope; an ambiguous one halts.
            let (a, t, off) = match self.resolve(loc, p, 0) {
                Ok(x) => x,
                Err(h) if matches!(h.behavior, Behavior::Ub(_)) => continue,
                Err(h) => return Err(h),
            };
            let t2 = self.fresh_tag(t);
            let q = self.new_ptr(Ptr::Rel {
                alloc: a,
                tag: t2,
                off,
            });
            let s = self.slot(r);
            self.slots[s] = Value::Ptr(q);
            self.scopes.push(Scope {
                alloc: a,
                tag: t2,
                noalias,
                readonly,
            });
            self.marks.push(FxHashMap::default());
        }
        Ok(())
    }

    /// The heap allocations still live, for the leak report.
    fn leaks(&self) -> Vec<String> {
        (1..self.allocs.size.len())
            .filter(|&a| self.allocs.live[a] && self.allocs.kind[a] != STACK)
            .map(|a| {
                format!(
                    "leak: {} bytes from {} at {}",
                    self.allocs.size[a],
                    self.families[self.allocs.kind[a] as usize],
                    render_loc(self.allocs.sites[a].0)
                )
            })
            .collect()
    }

    // Control flow

    fn first_op(&self, r: RegionId) -> Option<OpId> {
        self.body().ops(r).next()
    }

    fn push_block(&mut self, r: RegionId) {
        let next = self.first_op(r);
        self.frames.push(Frame::Block {
            next,
            allocs: self.stack_allocs.len() as u32,
        });
    }

    /// Bind the loop state and push the body (Lean's `enterBody`).
    fn enter_body(&mut self, loc: Option<Loc>, body: RegionId, vs: &[Value]) -> R<()> {
        self.bind(loc, self.body().params(body), vs)?;
        self.push_block(body);
        Ok(())
    }

    /// The nearest frame `pick` accepts, not looking past a call frame unless `pick` accepts it.
    fn find_frame(&self, pick: impl Fn(&Frame) -> bool) -> Option<usize> {
        for i in (0..self.frames.len()).rev() {
            let f = &self.frames[i];
            if pick(f) {
                return Some(i);
            }
            if matches!(f, Frame::Call { .. }) {
                return None;
            }
        }
        None
    }

    /// Run a terminator; the current block has already been popped (Lean's `terminate`).
    fn terminate(&mut self, loc: Option<Loc>, k: OpKind, vs: &[Value]) -> R<()> {
        let body = self.body();
        match k {
            OpKind::Yield => match self.frames.last() {
                Some(&Frame::IfJoin { op }) => {
                    self.frames.pop();
                    self.bind(body.loc(op), body.results(op), vs)
                }
                Some(Frame::Loop { .. }) => {
                    stuck(loc, "a loop body must end with cf.break or cf.continue")
                }
                _ => stuck(loc, "the function ended without func.ret"),
            },
            OpKind::Break | OpKind::Continue => {
                let Some(i) = self.find_frame(|f| matches!(f, Frame::Loop { .. })) else {
                    let what = if k == OpKind::Break {
                        "cf.break"
                    } else {
                        "cf.continue"
                    };
                    return stuck(loc, format!("{what} outside a loop"));
                };
                let Frame::Loop { op, allocs, .. } = self.frames[i] else {
                    unreachable!()
                };
                self.release_from(allocs);
                if k == OpKind::Break {
                    self.frames.truncate(i);
                    self.bind(body.loc(op), body.results(op), vs)
                } else {
                    self.frames.truncate(i + 1);
                    self.enter_body(loc, body.regions(op)[0], vs)
                }
            }
            OpKind::Ret => {
                let Some(i) = self.find_frame(|f| matches!(f, Frame::Call { .. })) else {
                    return stuck(loc, "func.ret outside a function");
                };
                let Frame::Call {
                    op,
                    func,
                    base,
                    scopes,
                    allocs,
                } = self.frames[i]
                else {
                    unreachable!()
                };
                let rets = &self.module.funcs[self.func as usize].rets;
                if vs.len() != rets.len() || !vs.iter().zip(rets).all(|(&v, &t)| self.has_ty(v, t))
                {
                    return stuck(
                        loc,
                        "func.ret values don't match the function's return types",
                    );
                }
                self.release_from(allocs);
                self.scopes.truncate(scopes as usize);
                self.marks.truncate(scopes as usize);
                let Some(op) = op else {
                    let mut out = String::new();
                    for (j, &v) in vs.iter().enumerate() {
                        if j > 0 {
                            out.push_str(", ");
                        }
                        self.render_value(v, &mut out);
                    }
                    return Err(Box::new(Halt {
                        behavior: Behavior::Ret(out),
                        loc,
                        note: String::new(),
                        leaks: self.leaks(),
                    }));
                };
                self.slots.truncate(self.base as usize);
                self.func = func;
                self.base = base;
                self.frames.truncate(i);
                let body = self.body();
                self.bind(body.loc(op), body.results(op), vs)
            }
            _ => stuck(loc, "not a terminator"),
        }
    }

    /// Run one op; the current block has already moved past it (Lean's `execOp`).
    fn exec_op(&mut self, op: OpId) -> R<()> {
        let body = self.body();
        let loc = body.loc(op);
        let kind = body.kind(op);
        let mut vs = std::mem::take(&mut self.scratch);
        match kind {
            OpKind::If => {
                self.operands(op, loc, &mut vs)?;
                let c = match vs.first() {
                    Some(&v) => self.bits(loc, v)?,
                    None => None,
                };
                let Some(c) = c else {
                    return ub(UbKind::Poison, loc, "branch on poison");
                };
                let regions = body.regions(op);
                let r = if c.is_zero() { regions[1] } else { regions[0] };
                self.frames.push(Frame::IfJoin { op });
                self.push_block(r);
            }
            OpKind::Loop { progress } => {
                self.operands(op, loc, &mut vs)?;
                self.frames.push(Frame::Loop {
                    op,
                    progress,
                    allocs: self.stack_allocs.len() as u32,
                });
                self.enter_body(loc, body.regions(op)[0], &vs)?;
            }
            OpKind::Call { callee } => {
                self.operands(op, loc, &mut vs)?;
                let name = body.str(callee);
                let Some(&f) = self.funcs.get(name) else {
                    return stuck(loc, format!("no function @{name}"));
                };
                let (caller, caller_base) = (self.func, self.base);
                let scopes = self.scopes.len() as u32;
                self.func = f;
                self.base = self.slots.len() as u32;
                let n = self.body().num_values();
                self.slots.resize(self.slots.len() + n, Value::Unset);
                self.enter_call(loc, &vs)?;
                self.frames.push(Frame::Call {
                    op: Some(op),
                    func: caller,
                    base: caller_base,
                    scopes,
                    allocs: self.stack_allocs.len() as u32,
                });
                let entry = self.body().entry();
                self.push_block(entry);
            }
            OpKind::MemStack { size, align } => {
                let p = self.new_alloc(loc, size, align, STACK);
                self.bind(loc, body.results(op), &[Value::Ptr(p)])?;
                let Ptr::Rel { alloc, .. } = self.ptrs[p as usize] else {
                    unreachable!()
                };
                self.stack_allocs.push(alloc);
            }
            OpKind::Yield | OpKind::Break | OpKind::Continue | OpKind::Ret => {
                self.operands(op, loc, &mut vs)?;
                if let Some(&Frame::Block { allocs, .. }) = self.frames.last() {
                    self.frames.pop();
                    self.release_from(allocs);
                }
                self.terminate(loc, kind, &vs)?;
            }
            _ => {
                if !body.regions(op).is_empty() {
                    return stuck(loc, "malformed op");
                }
                self.operands(op, loc, &mut vs)?;
                let results = body.results(op);
                let rty = results.clone().next().map(|r| body.ty(r));
                match self.simple(loc, kind, rty, &vs)? {
                    Some(v) => self.bind(loc, results, &[v])?,
                    None => self.bind(loc, results, &[])?,
                }
            }
        }
        self.scratch = vs;
        Ok(())
    }

    /// One step of the machine (Lean's `step`).
    fn step(&mut self) -> R<()> {
        let Some(&Frame::Block { next, allocs }) = self.frames.last() else {
            return stuck(None, "no block to run");
        };
        match next {
            None => {
                // Falling off the end of a region is an implicit `cf.yield` with no values.
                self.frames.pop();
                self.release_from(allocs);
                self.terminate(None, OpKind::Yield, &[])
            }
            Some(op) => {
                let after = self.body().next(op);
                if let Some(Frame::Block { next, .. }) = self.frames.last_mut() {
                    *next = after;
                }
                self.exec_op(op)
            }
        }
    }

    /// The machine at the start of a call from outside (Lean's `Machine.init`).
    fn init(&mut self, f: u32, args: &[Value]) -> R<()> {
        self.func = f;
        self.base = 0;
        self.slots = vec![Value::Unset; self.body().num_values()];
        self.enter_call(None, args)?;
        self.frames.push(Frame::Call {
            op: None,
            func: f,
            base: 0,
            scopes: 0,
            allocs: 0,
        });
        let entry = self.body().entry();
        self.push_block(entry);
        Ok(())
    }

    /// Run at most `fuel` steps and describe the outcome (`fir-ref run`'s `drive`).
    fn drive(&mut self, fuel: u64) -> String {
        let mut steps = 0;
        loop {
            if steps >= fuel {
                let progress = self
                    .frames
                    .iter()
                    .any(|f| matches!(f, Frame::Loop { progress: true, .. }));
                let tail = if progress { " in a progress loop" } else { "" };
                return format!("out of fuel after {fuel} steps{tail}");
            }
            if let Err(h) = self.step() {
                return h.render();
            }
            steps += 1;
        }
    }
}
