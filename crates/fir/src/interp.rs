//! The reference interpreter, mirroring `spec/Fir/Interp.lean` step for step, for the oracle that
//! always answers `0` (the one `fir-ref run` uses): `freeze` of `poison` gives `0`, allocations
//! succeed, allocation ids and tags count up from 1, addresses are assigned first-fit from
//! `0x1000`, and comparing a one-past-the-end pointer with a pointer into another allocation
//! gives "not equal"; and for the world that answers every external call with zeros and changes
//! nothing (Lean's `World.zero`). [`run`] prints the same one-line outcome as `fir-ref run`: the
//! run's events (external calls), then how it ended. An external call exposes what the callee can
//! reach, as in Lean, and returns its results one step later (`Frame::ExternRet`, Lean's
//! synthesized `func.ret`), so the caller checks them as it checks any callee's. An exception
//! unwinds in one step, as Lean's `throwExn` does (`Machine::throw_exn`), and one that leaves the
//! outermost call ends the run with `threw`.
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
//!   address, exposed tags, sites, bytes). Ids start at 1; index 0 is unused. The globals are
//!   allocations `1..=G`, made before the call; a function gets a size-0 allocation when its
//!   address is first needed (functions that initializers name, right after the globals). A
//!   `const` global's whole-run `readonly` scope in Lean is a check of the allocation's kind
//!   here, done before the other scopes, as Lean's scope comes first.
//!
//! Addresses are 64-bit here: modules whose address size is above 64 bits are rejected. Pointer
//! offsets, which Lean leaves unbounded, are 128-bit, which a run can't overflow without more
//! than `2^63` steps.

use std::fmt::Write;

use num_bigint::{BigInt, BigUint};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, Succ, ValueId};
use crate::ir::*;
use crate::sem::{self, Bits, Out};
pub use crate::sem::{TrapReason, UbKind};
use crate::types::Shape;

// The machine that runs LFIR modules for AArch64; a child module, so it shares the memory model.
#[path = "backend/aarch64/machine.rs"]
mod lfir;

/// The alignment a leaf at offset `off` of an access aligned to `align` keeps (Lean's
/// `Nat.gcd align off`).
fn leaf_align(align: u32, off: u128) -> u32 {
    let (mut a, mut b) = (u128::from(align), off);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a as u32
}

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
    /// A float of type `f`: its bits.
    Float {
        f: FloatTy,
        bits: u64,
    },
    /// A float that is `poison`.
    FloatPoison(FloatTy),
    /// A `bN` value: a run in `byte_vals`.
    Bytes {
        start: u32,
        len: u32,
    },
    /// An HFIR aggregate (Lean's `RVal.agg`): a run of parts in `agg_vals`. A union is its tag
    /// (an `i32`) and its payload; a slice its pointer and length.
    Agg {
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
    /// A running `cf.blocks`; `allocs` is where the allocations of its current block start.
    Blocks {
        op: OpId,
        progress: bool,
        allocs: u32,
    },
    /// A `cf.try` whose first region runs above it; `allocs` is where that region's allocations
    /// start. An exception thrown above it runs its handler region in its place.
    Try { op: OpId, allocs: u32 },
    /// An external call that has returned, about to bind its results: Lean's synthesized
    /// `func.ret` block and the call frame under it. `ext` is the external function's index.
    ExternRet { op: OpId, ext: u32 },
    /// A call: the call op (`None` for the call from outside; a `func.invoke` names where the
    /// callee's exceptions go), the caller's function and slots, and where the callee's scopes
    /// and allocations start.
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

/// What an allocation is (Lean's `AllocKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Stack,
    /// Heap memory of an allocator family: its index in `Machine::families`.
    Heap(u32),
    /// A global, by index in the module.
    Global(u32),
    /// A function: its index in the module's functions, or, from the number of functions on, in
    /// its external functions.
    Func(u32),
}

/// Allocations, as columns by allocation id.
#[derive(Default)]
struct Allocs {
    size: Vec<u64>,
    align: Vec<u32>,
    kind: Vec<Kind>,
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
    /// An exception left the outermost call: the value, rendered.
    Threw(String),
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
            Behavior::Threw(v) => format!("threw {v}"),
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

/// `k` modulo `2^w`, in `0..2^w`.
fn key_mod(k: Int<'_>, w: u32) -> BigInt {
    let m = BigInt::from(1) << w;
    let r = k.to_bigint() % &m;
    if r.sign() == num_bigint::Sign::Minus {
        r + m
    } else {
        r
    }
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
    run_detail(m, name, args, fuel, false).map(|r| r.line)
}

/// How a run went (Lean's `RunResult` in `spec/Main.lean`): the outcome line, the events part of
/// it, and whether the run ended in UB or got stuck, or ran out of fuel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunOutput {
    pub line: String,
    /// The events, each followed by `; `.
    pub events: String,
    pub absorbing: bool,
    pub out_of_fuel: bool,
}

impl RunOutput {
    /// Whether a run of the lowering, `tgt`, agrees with this HFIR run (Lean's
    /// `RunResult.lowersTo`): the same line, unless this run ends in UB or gets stuck, where
    /// `tgt` must have its events first. A run that ran out of fuel is not compared.
    pub fn lowers_to(&self, tgt: &RunOutput) -> bool {
        self.out_of_fuel
            || self.line == tgt.line
            || (self.absorbing && tgt.events.starts_with(&self.events))
    }
}

/// [`run`], with the outcome's parts. With `lower_rets`, returned values are shown as the
/// scalars the lowering returns instead (Lean's `Lower.lowerValue`).
pub fn run_detail(
    m: &Module,
    name: &str,
    args: &[&str],
    fuel: u64,
    lower_rets: bool,
) -> Result<RunOutput, String> {
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
    if let crate::Layer::Lfir(_) = m.layer {
        return Ok(RunOutput {
            line: lfir::run(mach, fi as u32, &vals, fuel),
            events: String::new(),
            absorbing: false,
            out_of_fuel: false,
        });
    }
    mach.lower_rets = lower_rets;
    Ok(match mach.init(fi as u32, &vals) {
        Err(h) => RunOutput {
            line: h.render(),
            events: String::new(),
            absorbing: matches!(h.behavior, Behavior::Ub(_) | Behavior::Stuck(_)),
            out_of_fuel: false,
        },
        Ok(()) => mach.drive(fuel),
    })
}

struct Machine<'m> {
    module: &'m Module,
    /// Functions, then external functions, by name: an index like `Kind::Func`'s.
    funcs: FxHashMap<&'m str, u32>,
    /// How many functions the module has (external functions are numbered after them).
    nfuncs: u32,
    /// The events so far, each followed by `; `, as the outcome line shows them.
    trace: String,
    space: &'m SpaceCfg,
    /// Pointers (indices into `ptrs`) to the globals, by name.
    globals: FxHashMap<&'m str, u32>,
    /// A pointer to each function whose address has been taken (`NONE` until then).
    fn_ptrs: Vec<u32>,
    // Values
    slots: Vec<Value>,
    wides: Vec<BigUint>,
    byte_vals: Vec<Byte>,
    agg_vals: Vec<Value>,
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
    /// Show returned values as the lowering returns them (`run_detail`).
    lower_rets: bool,
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
        let nfuncs = module.funcs.len() as u32;
        for (i, x) in module.externs.iter().enumerate() {
            funcs.insert(x.name.as_str(), nfuncs + i as u32);
        }
        let mut allocs = Allocs::default();
        allocs.size.push(0);
        allocs.align.push(1);
        allocs.kind.push(Kind::Stack);
        allocs.live.push(false);
        allocs.base.push(0);
        allocs.exposed.push(NONE);
        allocs.sites.push((None, None));
        allocs.bytes.push(Mem::Dense(Vec::new()));
        let mut m = Machine {
            module,
            funcs,
            nfuncs,
            trace: String::new(),
            space: &module.space,
            globals: FxHashMap::default(),
            fn_ptrs: vec![NONE; module.funcs.len() + module.externs.len()],
            slots: Vec::new(),
            wides: Vec::new(),
            byte_vals: Vec::new(),
            agg_vals: Vec::new(),
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
            lower_rets: false,
            scratch: Vec::new(),
            bytes_buf: Vec::new(),
        };
        m.init_globals();
        m
    }

    /// Allocate the globals, `1, 2, …` in order, then the functions their initializers take
    /// the address of, in the order they are first named, and write the initial bytes (Lean's
    /// `Core.initial`).
    fn init_globals(&mut self) {
        let module: &'m Module = self.module;
        let gs = &module.globals;
        let sp: &'m SpaceCfg = self.space;
        for g in 0..gs.len() {
            let t = gs.ty(g);
            let size = gs.types.size(sp, t) as u64;
            let align = gs.types.align(sp, t).max(u64::from(gs.align(g))) as u32;
            let p = self.new_alloc(None, size, align, Kind::Global(g as u32));
            self.globals.insert(gs.name(g), p);
        }
        let mut syms = Vec::new();
        for g in 0..gs.len() {
            gs.syms(gs.init(g), &mut syms);
        }
        for name in syms {
            if self.globals.contains_key(name) {
                continue;
            }
            if let Some(&f) = self.funcs.get(name)
                && self.fn_ptrs[f as usize] == NONE
            {
                self.fn_ptrs[f as usize] = self.new_alloc(None, 0, 1, Kind::Func(f));
            }
        }
        let mut bytes = Vec::new();
        for g in 0..gs.len() {
            bytes.clear();
            self.init_bytes(gs.ty(g), gs.init(g), &mut bytes);
            let a = g + 1;
            for (i, &b) in bytes.iter().enumerate() {
                self.allocs.bytes[a].set(i as u64, b);
            }
        }
    }

    /// The pointer `@name` denotes in an initializer.
    fn sym_ptr(&self, name: &str) -> Option<u32> {
        match self.globals.get(name) {
            Some(&p) => Some(p),
            None => {
                let f = *self.funcs.get(name)?;
                Some(self.fn_ptrs[f as usize]).filter(|&p| p != NONE)
            }
        }
    }

    /// The bytes an object of type `t` starts with (Lean's `initBytes`), appended to `out`.
    fn init_bytes(&mut self, t: Ty, init: Init, out: &mut Vec<Byte>) {
        let module: &'m Module = self.module;
        let gs = &module.globals;
        let sp: &'m SpaceCfg = self.space;
        let size = gs.types.size(sp, t) as usize;
        let start = out.len();
        match (init, t) {
            (Init::Zero, _) => out.resize(start + size, Byte::Bits(0)),
            (Init::Int(i), Ty::Int(w) | Ty::Byte(w)) => {
                let mut raw = Vec::new();
                sem::to_le_bytes(w, &sem::konst(w, gs.int(i)), &mut raw);
                out.extend(raw.into_iter().map(Byte::Bits));
            }
            (Init::Float(f, i), Ty::Float(g)) if f == g => {
                let b = gs.float(i);
                out.extend((0..f.width() / 8).map(|k| Byte::Bits((b >> (8 * k)) as u8)));
            }
            (Init::Null, Ty::Ptr) => self.push_ptr_bytes(Some(NULL), out),
            (Init::Sym(r), Ty::Ptr) => {
                let p = self.sym_ptr(gs.text(r));
                self.push_ptr_bytes(p, out);
            }
            (Init::Bytes(r), _) => out.extend(gs.bytes(r).iter().map(|&b| Byte::Bits(b))),
            (Init::List(r), Ty::Agg(id)) => {
                let items = gs.items(r);
                out.resize(start + size, Byte::Bits(0));
                let mut part = Vec::new();
                let mut put = |m: &mut Self, off: u128, ty: Ty, item: Init, out: &mut Vec<Byte>| {
                    part.clear();
                    m.init_bytes(ty, item, &mut part);
                    let off = start + off as usize;
                    // As Lean's `overlay`: what runs past the end is dropped.
                    let n = part.len().min(out.len().saturating_sub(off));
                    out[off..off + n].copy_from_slice(&part[..n]);
                };
                match gs.types.shape(id) {
                    Shape::Struct(p, fs) => {
                        let (offs, _, _) = gs.types.place(sp, p, fs);
                        for ((&f, &item), off) in fs.iter().zip(items).zip(offs) {
                            put(self, off, f, item, out);
                        }
                    }
                    Shape::Array(n, e) => {
                        let stride = gs.types.stride(sp, e);
                        for (i, &item) in items.iter().take(n as usize).enumerate() {
                            put(self, i as u128 * stride, e, item, out);
                        }
                    }
                    Shape::Func(..) | Shape::Union(_) => {}
                }
            }
            _ => out.resize(start + size, Byte::Poison),
        }
    }

    fn push_ptr_bytes(&self, p: Option<u32>, out: &mut Vec<Byte>) {
        let pb = self.space.ptr_bits / 8;
        match p {
            Some(ptr) => out.extend((0..pb).map(|i| Byte::Frag { ptr, i })),
            None => out.extend((0..pb).map(|_| Byte::Poison)),
        }
    }

    fn body(&self) -> &'m Body {
        &self.module.funcs[self.func as usize].body
    }

    /// The name of function `f` (an index like `Kind::Func`'s).
    fn fn_name(&self, f: u32) -> &'m str {
        let module: &'m Module = self.module;
        match module.funcs.get(f as usize) {
            Some(func) => &func.name,
            None => &module.externs[(f - self.nfuncs) as usize].name,
        }
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

    /// A float value's bits (`None` for `poison`), Lean's `asFloat`.
    fn float_of(&self, loc: Option<Loc>, f: FloatTy, v: Value) -> R<Option<u64>> {
        match v {
            Value::Float { f: g, bits } if g == f => Ok(Some(bits)),
            Value::FloatPoison(g) if g == f => Ok(None),
            Value::Float { f: g, .. } | Value::FloatPoison(g) => stuck(
                loc,
                format!("expected an {} but got an {}", f.name(), g.name()),
            ),
            _ => stuck(loc, format!("expected an {}", f.name())),
        }
    }

    fn float_value(f: FloatTy, v: Option<u64>) -> Value {
        match v {
            Some(bits) => Value::Float { f, bits },
            None => Value::FloatPoison(f),
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

    /// Whether a value has a type of the running function's table (Lean's `RVal.hasTy`).
    fn has_ty(&self, v: Value, t: Ty) -> bool {
        self.has_ty_in(self.body().types(), v, t)
    }

    fn has_ty_in(&self, types: &Types, v: Value, t: Ty) -> bool {
        match (v, t) {
            (Value::Int { w, .. } | Value::Wide { w, .. } | Value::Poison { w }, Ty::Int(w2)) => {
                w == w2
            }
            (Value::Ptr(_) | Value::PtrPoison, Ty::Ptr) => true,
            (Value::Bytes { len, .. }, Ty::Byte(w)) => u64::from(len) * 8 == u64::from(w),
            (Value::Float { f, .. } | Value::FloatPoison(f), Ty::Float(g)) => f == g,
            (Value::Agg { start, len }, Ty::Slice) => {
                let ps = &self.agg_vals[Span { start, len }.range()];
                matches!(
                    ps,
                    [
                        Value::Ptr(_) | Value::PtrPoison,
                        Value::Int { .. } | Value::Wide { .. } | Value::Poison { .. }
                    ]
                )
            }
            (Value::Agg { start, len }, Ty::Agg(id)) => {
                let ps = &self.agg_vals[Span { start, len }.range()];
                match types.shape(id) {
                    Shape::Struct(_, fs) => {
                        ps.len() == fs.len()
                            && ps
                                .iter()
                                .zip(fs)
                                .all(|(&p, &f)| self.has_ty_in(types, p, f))
                    }
                    Shape::Array(n, e) => {
                        ps.len() as u64 == n && ps.iter().all(|&p| self.has_ty_in(types, p, e))
                    }
                    Shape::Union(vs) => match ps {
                        [Value::Int { w: 32, bits }, x] => match vs.get(*bits as usize) {
                            Some(&u) => self.has_ty_in(types, *x, u),
                            None => false,
                        },
                        _ => false,
                    },
                    Shape::Func(..) => false,
                }
            }
            _ => false,
        }
    }

    /// The parts of an aggregate value.
    fn parts(&self, v: Value) -> Option<&[Value]> {
        match v {
            Value::Agg { start, len } => Some(&self.agg_vals[Span { start, len }.range()]),
            _ => None,
        }
    }

    fn new_agg(&mut self, parts: &[Value]) -> Value {
        let start = self.agg_vals.len() as u32;
        self.agg_vals.extend_from_slice(parts);
        Value::Agg {
            start,
            len: parts.len() as u32,
        }
    }

    /// An aggregate's scalars, depth first (Lean's `RVal.leaves`), appended to `out`.
    fn leaf_values(&self, v: Value, out: &mut Vec<Value>) {
        match self.parts(v) {
            Some(ps) => ps.iter().for_each(|&p| self.leaf_values(p, out)),
            None => out.push(v),
        }
    }

    /// A value of type `t` from the front of its scalars `vs` (Lean's `Ty.build`), with the
    /// position after them.
    fn build(&mut self, types: &Types, t: Ty, vs: &[Value], at: usize) -> Option<(Value, usize)> {
        match t {
            Ty::Slice => {
                let ps = vs.get(at..at + 2)?;
                let ps = [ps[0], ps[1]];
                Some((self.new_agg(&ps), at + 2))
            }
            Ty::Agg(id) => match types.shape(id) {
                Shape::Struct(_, fs) => {
                    let mut parts = Vec::with_capacity(fs.len());
                    let mut at = at;
                    for &f in fs {
                        let (x, next) = self.build(types, f, vs, at)?;
                        parts.push(x);
                        at = next;
                    }
                    Some((self.new_agg(&parts), at))
                }
                Shape::Array(n, e) => {
                    let mut parts = Vec::with_capacity(n as usize);
                    let mut at = at;
                    for _ in 0..n {
                        let (x, next) = self.build(types, e, vs, at)?;
                        parts.push(x);
                        at = next;
                    }
                    Some((self.new_agg(&parts), at))
                }
                _ => Some((*vs.get(at)?, at + 1)),
            },
            _ => Some((*vs.get(at)?, at + 1)),
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
            Value::Float { f, bits } => {
                write!(out, "{} {}", f.name(), crate::float::render(f, bits)).unwrap()
            }
            Value::FloatPoison(f) => write!(out, "{} poison", f.name()).unwrap(),
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
            Value::Agg { start, len } => {
                out.push('{');
                for (i, &p) in self.agg_vals[Span { start, len }.range()]
                    .iter()
                    .enumerate()
                {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.render_value(p, out);
                }
                out.push('}');
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
            (Ty::Float(f), "poison") => Ok(Value::FloatPoison(f)),
            (Ty::Float(f), _) => match crate::float::parse_lit(s).and_then(|l| l.to_bits(f)) {
                Some(bits) => Ok(Value::Float { f, bits }),
                None => Err(format!(
                    "bad argument '{s}': expected a float like 1.5, inf, nan, or poison"
                )),
            },
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
    fn new_alloc(&mut self, loc: Option<Loc>, size: u64, align: u32, kind: Kind) -> u32 {
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
        if self.allocs.kind[a as usize] == Kind::Stack {
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
            self.add_exposure(alloc, tag);
        }
        Ok(addr)
    }

    /// Record that allocation `a`'s tag `tag` is exposed, if it isn't yet.
    fn add_exposure(&mut self, a: u32, tag: u32) {
        let mut cur = self.allocs.exposed[a as usize];
        while cur != NONE {
            let (t, next) = self.exposures[cur as usize];
            if t == tag {
                return;
            }
            cur = next;
        }
        self.exposures.push((tag, self.allocs.exposed[a as usize]));
        self.allocs.exposed[a as usize] = (self.exposures.len() - 1) as u32;
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
        if let Kind::Func(f) = self.allocs.kind[ai] {
            let f = self.fn_name(f);
            return ub(UbKind::FuncAccess, loc, format!("@{f} is a function"));
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
        // A `const` global's whole-run `readonly` scope comes before every other scope.
        if write
            && let Kind::Global(g) = self.allocs.kind[a as usize]
            && self.module.globals.is_const(g as usize)
        {
            return ub(UbKind::ConstWrite, loc, "write to a const global");
        }
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
            // A float's bits, read as an integer's (decision: Pointer bytes as integers).
            Ty::Float(f) => {
                for b in bs.iter_mut() {
                    *b = self.frag_to_bits(loc, *b)?;
                }
                let v = self.decode_int(f.width(), &bs);
                Self::float_value(f, v.and_then(|b| b.to_u64()))
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
            Ty::Agg(_) | Ty::Slice => {
                self.bytes_buf = bs;
                let t = self.body().types().show(ty);
                return stuck(loc, format!("{t} is not a value type"));
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
            Ty::Float(f) => u64::from(f.width() / 8),
            Ty::Ptr => u64::from(self.space.ptr_bits / 8),
            Ty::Agg(_) | Ty::Slice => self.body().types().size(self.space, t) as u64,
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
            Value::Float { f, bits } => {
                let mut raw = Vec::new();
                sem::to_le_bytes(f.width(), &Bits::Small(bits), &mut raw);
                bs.extend(raw.into_iter().map(Byte::Bits));
            }
            Value::FloatPoison(f) => bs.extend((0..f.width() / 8).map(|_| Byte::Poison)),
            Value::Ptr(p) => bs.extend((0..pb).map(|i| Byte::Frag { ptr: p, i })),
            Value::PtrPoison => bs.extend((0..pb).map(|_| Byte::Poison)),
            Value::Bytes { start, len } => {
                bs.extend_from_slice(&self.byte_vals[Span { start, len }.range()])
            }
            Value::Agg { .. } | Value::Unset => {}
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

    /// `mem.copy` of `n` bytes: Lean loads them as a `bN` and stores that, so this checks and
    /// marks the source as a load would, then the destination as a store would.
    fn copy(&mut self, loc: Option<Loc>, n: u64, align: u32, d: Value, s: Value) -> R<()> {
        let Some(s) = self.ptr_of(loc, s)? else {
            return ub(UbKind::Poison, loc, "load through a poison pointer");
        };
        let (a, off) = self.access(loc, s, n, align, false)?;
        let mut bs = std::mem::take(&mut self.bytes_buf);
        bs.clear();
        let mem = &self.allocs.bytes[a as usize];
        bs.extend((0..n).map(|i| mem.get(off + i)));
        let r = self.copy_to(loc, n, align, d, &bs);
        self.bytes_buf = bs;
        r
    }

    fn copy_to(&mut self, loc: Option<Loc>, n: u64, align: u32, d: Value, bs: &[Byte]) -> R<()> {
        let Some(d) = self.ptr_of(loc, d)? else {
            return ub(UbKind::Poison, loc, "store through a poison pointer");
        };
        let (a, off) = self.access(loc, d, n, align, true)?;
        let mem = &mut self.allocs.bytes[a as usize];
        for (i, b) in bs.iter().enumerate() {
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
            let k = if kind == Kind::Stack {
                UbKind::BadFree
            } else {
                UbKind::DoubleFree
            };
            return ub(k, loc, self.dead_note(a));
        }
        let fam = self.family(family);
        if kind != Kind::Heap(fam) {
            let site = render_loc(self.allocs.sites[ai].0);
            let note = match kind {
                Kind::Stack => format!("allocated at {site} by mem.stack"),
                Kind::Heap(f) => format!("allocated at {site} by {}", self.families[f as usize]),
                Kind::Global(g) => {
                    format!("@{} is a global", self.module.globals.name(g as usize))
                }
                Kind::Func(f) => format!("@{} is a function", self.fn_name(f)),
            };
            return ub(UbKind::BadFree, loc, note);
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

    /// `n` modulo the address size, as an address-size integer.
    fn addr_masked(&self, n: u128) -> Value {
        self.addr_value((n % self.limit()) as u64)
    }

    /// `p` moved by `n` bytes (Lean's `offsetBy`). In bounds, it is `poison` when `p` or the
    /// result is outside `[0, size]` of a live allocation; an offset of 0 always gives `p`.
    fn offset_by(&mut self, inbounds: bool, p: u32, n: i128) -> R<Option<Value>> {
        if n == 0 {
            return Ok(Some(Value::Ptr(p)));
        }
        Ok(Some(match self.ptrs[p as usize] {
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
        }))
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
            (OpKind::Poison, []) => match rty {
                Some(Ty::Ptr) => Value::PtrPoison,
                Some(Ty::Byte(w)) => {
                    let start = self.byte_vals.len() as u32;
                    self.byte_vals
                        .extend(std::iter::repeat_n(Byte::Poison, (w / 8) as usize));
                    Value::Bytes { start, len: w / 8 }
                }
                Some(Ty::Float(f)) => Value::FloatPoison(f),
                _ => Value::Poison { w: rw },
            },
            (OpKind::Freeze, &[Value::Poison { w }]) => self.int_value(w, Some(Bits::zero(w))),
            (OpKind::Freeze, &[Value::FloatPoison(f)]) => Value::Float { f, bits: 0 },
            (OpKind::Freeze | OpKind::Copy, &[v]) => v,
            (OpKind::Select, &[c, a, b]) if matches!(rty, Some(Ty::Float(_))) => {
                let Some(Ty::Float(f)) = rty else {
                    unreachable!()
                };
                let c = self.bits(loc, c)?;
                self.float_of(loc, f, a)?;
                self.float_of(loc, f, b)?;
                match c {
                    None => Value::FloatPoison(f),
                    Some(c) if !c.is_zero() => a,
                    Some(_) => b,
                }
            }
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
            // Floats (Lean's `evalFloat`), for the oracle that answers 0: NaN results are canonical.
            (OpKind::FloatConst { value }, []) => match rty {
                Some(Ty::Float(f)) => Value::Float { f, bits: value },
                _ => return stuck(loc, "float.const of a non-float"),
            },
            (OpKind::FloatBin(op), &[a @ (Value::Float { f, .. } | Value::FloatPoison(f)), b]) => {
                let a = self.float_of(loc, f, a)?;
                let b = self.float_of(loc, f, b)?;
                Self::float_value(f, a.zip(b).map(|(a, b)| crate::float::bin(f, op, a, b)))
            }
            (OpKind::FloatUn(op), &[a @ (Value::Float { f, .. } | Value::FloatPoison(f))]) => {
                let a = self.float_of(loc, f, a)?;
                Self::float_value(f, a.map(|a| crate::float::un(f, op, a)))
            }
            (OpKind::FloatFma, &[a @ (Value::Float { f, .. } | Value::FloatPoison(f)), b, c]) => {
                let a = self.float_of(loc, f, a)?;
                let b = self.float_of(loc, f, b)?;
                let c = self.float_of(loc, f, c)?;
                Self::float_value(
                    f,
                    a.zip(b)
                        .zip(c)
                        .map(|((a, b), c)| crate::float::fma(f, a, b, c)),
                )
            }
            (OpKind::FloatCmp(p), &[a @ (Value::Float { f, .. } | Value::FloatPoison(f)), b]) => {
                let a = self.float_of(loc, f, a)?;
                let b = self.float_of(loc, f, b)?;
                match a.zip(b) {
                    Some((a, b)) => Value::Int {
                        w: 1,
                        bits: u64::from(crate::float::cmp(f, p, a, b)),
                    },
                    None => Value::Poison { w: 1 },
                }
            }
            (
                OpKind::FloatExt | OpKind::FloatTrunc,
                &[Value::Float { f, .. } | Value::FloatPoison(f)],
            ) => {
                let Some(Ty::Float(g)) = rty else {
                    return stuck(loc, "expected a float result");
                };
                let a = self.float_of(loc, f, vs[0])?;
                Self::float_value(g, a.map(|a| crate::float::cvt(f, g, a)))
            }
            (
                OpKind::FloatToInt { signed, edge },
                &[a @ (Value::Float { f, .. } | Value::FloatPoison(f))],
            ) => {
                let o = match self.float_of(loc, f, a)? {
                    Some(a) => crate::float::to_int(f, signed, edge, rw, a),
                    None if edge == CvtEdge::Sat => Out::Val(None),
                    None => Out::Ub(UbKind::Poison),
                };
                self.int_out(loc, rw, o)?
            }
            (OpKind::IntToFloat { signed }, &[a]) => {
                let Some(Ty::Float(g)) = rty else {
                    return stuck(loc, "expected a float result");
                };
                let w = Self::width(a);
                let a = self.bits(loc, a)?;
                Self::float_value(g, a.map(|a| crate::float::from_int(g, signed, w, &a)))
            }
            (OpKind::FloatFromBits, &[a]) => {
                let Some(Ty::Float(g)) = rty else {
                    return stuck(loc, "expected a float result");
                };
                if Self::width(a) != g.width() {
                    return stuck(
                        loc,
                        format!("float.from_bits of an i{} to {}", Self::width(a), g.name()),
                    );
                }
                let a = self.bits(loc, a)?;
                Self::float_value(g, a.and_then(|a| a.to_u64()))
            }
            (OpKind::FloatToBits, &[a @ (Value::Float { f, .. } | Value::FloatPoison(f))]) => {
                let a = self.float_of(loc, f, a)?;
                self.int_value(f.width(), a.map(Bits::Small))
            }
            (OpKind::MemAlloc { family, align, .. }, &[n]) => {
                let Some(size) = self.addr_operand(loc, n)? else {
                    return ub(UbKind::Poison, loc, "allocation size is poison");
                };
                let fam = self.family(body.str(family));
                Value::Ptr(self.new_alloc(loc, size, align, Kind::Heap(fam)))
            }
            (OpKind::MemFree { family }, &[p]) => {
                let p = self.ptr_of(loc, p)?;
                self.free(loc, body.str(family), p)?;
                return Ok(None);
            }
            (OpKind::Load { align }, &[p]) => {
                let p = self.ptr_of(loc, p)?;
                self.load_any(loc, rty.unwrap(), align, p)?
            }
            (OpKind::Store { ty, align }, &[v, p]) => {
                let p = self.ptr_of(loc, p)?;
                self.store_any(loc, ty, align, v, p)?;
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
                return self.offset_by(inbounds, p, i128::from(sem::sext64(aw, n)));
            }
            // Layout
            (OpKind::TySize(ty), []) => {
                let n = body.types().size(self.space, ty);
                self.addr_masked(n)
            }
            (OpKind::TyAlign(ty), []) => {
                let n = body.types().align(self.space, ty);
                self.addr_masked(n.into())
            }
            (OpKind::TyOffset { ty, index }, []) => {
                let n = body
                    .types()
                    .field_offset(self.space, ty, index)
                    .unwrap_or(0);
                self.addr_masked(n)
            }
            (
                OpKind::PtrField {
                    inbounds,
                    ty,
                    index,
                },
                &[p],
            ) => {
                let Some(p) = self.ptr_of(loc, p)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let off = body
                    .types()
                    .field_offset(self.space, ty, index)
                    .unwrap_or(0);
                return self.offset_by(inbounds, p, off as i128);
            }
            (OpKind::PtrIndex { inbounds, ty }, &[p, i]) => {
                let i = self.addr_operand(loc, i)?;
                let Some(p) = self.ptr_of(loc, p)? else {
                    return Ok(Some(Value::PtrPoison));
                };
                let Some(i) = i else {
                    return Ok(Some(Value::PtrPoison));
                };
                let stride = body.types().stride(self.space, ty);
                // `|i| < 2^63` and the stride is below the address-space size, so this fits.
                let n = i128::from(sem::sext64(aw, i)) * stride as i128;
                let wrapped = sem::wrap_signed(aw, n);
                if inbounds && wrapped != n {
                    return Ok(Some(Value::PtrPoison));
                }
                return self.offset_by(inbounds, p, wrapped);
            }
            (OpKind::MemCopy { ty, align }, &[d, s]) => {
                let n = body.types().size(self.space, ty) as u64;
                self.copy(loc, n, align, d, s)?;
                return Ok(None);
            }
            // Globals and functions
            (OpKind::MemGlobal { global }, []) => {
                let name = body.str(global);
                match self.globals.get(name) {
                    Some(&p) => Value::Ptr(p),
                    None => return stuck(loc, format!("no global @{name}")),
                }
            }
            (OpKind::FuncAddr { callee }, []) => {
                let name = body.str(callee);
                if let Some(&p) = self.globals.get(name) {
                    return Ok(Some(Value::Ptr(p)));
                }
                let Some(&f) = self.funcs.get(name) else {
                    return stuck(loc, format!("no function @{name}"));
                };
                if self.fn_ptrs[f as usize] == NONE {
                    self.fn_ptrs[f as usize] = self.new_alloc(loc, 0, 1, Kind::Func(f));
                }
                Value::Ptr(self.fn_ptrs[f as usize])
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
            // Building blocks
            (OpKind::AggMake, _) => self.new_agg(vs),
            (OpKind::AggExtract { index }, &[a]) => match self.parts(a) {
                Some(ps) => match ps.get(index as usize) {
                    Some(&x) => x,
                    None => return stuck(loc, format!("no part {index}")),
                },
                None => return stuck(loc, "malformed op"),
            },
            (OpKind::AggInsert { index }, &[a, x]) => match self.parts(a) {
                Some(ps) if (index as usize) < ps.len() => {
                    let mut ps = ps.to_vec();
                    ps[index as usize] = x;
                    self.new_agg(&ps)
                }
                Some(_) => return stuck(loc, format!("no part {index}")),
                None => return stuck(loc, "malformed op"),
            },
            (OpKind::UnionMake { index }, &[x]) => {
                let tag = Value::Int {
                    w: 32,
                    bits: u64::from(index) & sem::mask(32),
                };
                self.new_agg(&[tag, x])
            }
            (OpKind::UnionTag, &[u]) => match self.parts(u) {
                Some(&[t @ (Value::Int { w: 32, .. } | Value::Poison { w: 32 }), _]) => t,
                _ => return stuck(loc, "malformed op"),
            },
            (OpKind::UnionGet { trap, index }, &[u]) => match self.parts(u) {
                Some(&[Value::Int { w: 32, bits }, x]) => {
                    if bits == u64::from(index) {
                        x
                    } else if trap {
                        return halt(Behavior::Trap(TrapReason::Tag), loc, "");
                    } else {
                        return ub(UbKind::Tag, loc, format!("the union holds variant {bits}"));
                    }
                }
                _ => return stuck(loc, "malformed op"),
            },
            (OpKind::SliceMake, &[p, n]) => {
                self.ptr_of(loc, p)?;
                self.bits(loc, n)?;
                self.new_agg(&[p, n])
            }
            (OpKind::SlicePtr, &[sv]) => match self.parts(sv) {
                Some(&[p @ (Value::Ptr(_) | Value::PtrPoison), _]) => p,
                _ => return stuck(loc, "malformed op"),
            },
            (OpKind::SliceLen, &[sv]) => match self.parts(sv) {
                Some(
                    &[
                        _,
                        n @ (Value::Int { .. } | Value::Wide { .. } | Value::Poison { .. }),
                    ],
                ) => n,
                _ => return stuck(loc, "malformed op"),
            },
            (OpKind::SliceGet { trap, align }, &[sv, i]) => {
                let t = rty.unwrap();
                let q = self.slice_elem(loc, trap, t, sv, i)?;
                self.load_any(loc, t, align, q)?
            }
            (OpKind::SliceSet { trap, ty, align }, &[v, sv, i]) => {
                let q = self.slice_elem(loc, trap, ty, sv, i)?;
                self.store_any(loc, ty, align, v, q)?;
                return Ok(None);
            }
            (OpKind::Check(reason), &[c]) => match self.bits(loc, c)? {
                None => return ub(UbKind::Poison, loc, "check of poison"),
                Some(b) if b.to_u64() == Some(1) => return Ok(None),
                Some(_) => return halt(Behavior::Trap(reason), loc, ""),
            },
            _ => return stuck(loc, "malformed op"),
        };
        Ok(Some(v))
    }

    /// Where the leaf at offset `off` of an aggregate at `p` is: `ptr.offset.wrap` by `off`
    /// (Lean's `leafPtr`).
    fn leaf_ptr(&mut self, p: Option<u32>, off: u128) -> R<Option<u32>> {
        let Some(p) = p else { return Ok(None) };
        let n = sem::wrap_signed(self.space.addr_bits, off as i128);
        Ok(match self.offset_by(false, p, n)? {
            Some(Value::Ptr(q)) => Some(q),
            _ => None,
        })
    }

    /// Load a scalar, or an aggregate leaf by leaf (Lean's `loadAny`).
    fn load_any(&mut self, loc: Option<Loc>, ty: Ty, align: u32, p: Option<u32>) -> R<Value> {
        if ty.is_value() {
            return self.load(loc, ty, align, p);
        }
        let types: &'m Types = self.body().types();
        let mut leaves = Vec::new();
        types.leaves(self.space, ty, 0, &mut leaves);
        let mut vals = Vec::with_capacity(leaves.len());
        for &(off, t) in &leaves {
            let q = self.leaf_ptr(p, off)?;
            vals.push(self.load(loc, t, leaf_align(align, off), q)?);
        }
        match self.build(types, ty, &vals, 0) {
            Some((v, n)) if n == vals.len() => Ok(v),
            _ => stuck(loc, format!("{} is not a value type", types.show(ty))),
        }
    }

    /// Store a scalar, or an aggregate leaf by leaf (Lean's `storeAny`).
    fn store_any(
        &mut self,
        loc: Option<Loc>,
        ty: Ty,
        align: u32,
        v: Value,
        p: Option<u32>,
    ) -> R<()> {
        if ty.is_value() {
            return self.store(loc, ty, align, v, p);
        }
        let types: &'m Types = self.body().types();
        if !self.has_ty(v, ty) {
            return stuck(loc, format!("the stored value isn't a {}", types.show(ty)));
        }
        let mut leaves = Vec::new();
        types.leaves(self.space, ty, 0, &mut leaves);
        let mut vals = Vec::with_capacity(leaves.len());
        self.leaf_values(v, &mut vals);
        for (&(off, t), &w) in leaves.iter().zip(&vals) {
            let q = self.leaf_ptr(p, off)?;
            self.store(loc, t, leaf_align(align, off), w, q)?;
        }
        Ok(())
    }

    /// Where element `i` of slice `sv` of `ty`s is, after checking `i` against the length
    /// (Lean's `sliceElem`).
    fn slice_elem(
        &mut self,
        loc: Option<Loc>,
        trap: bool,
        ty: Ty,
        sv: Value,
        i: Value,
    ) -> R<Option<u32>> {
        let Some(&[pv, nv]) = self.parts(sv) else {
            return stuck(loc, "expected a slice");
        };
        let p = self.ptr_of(loc, pv)?;
        let n = self.bits(loc, nv)?;
        let i = self.bits(loc, i)?;
        let (Some(x), Some(m)) = (i, n) else {
            return ub(UbKind::Poison, loc, "slice index or length is poison");
        };
        let (x, m) = (x.to_u64().unwrap_or(0), m.to_u64().unwrap_or(0));
        if x >= m {
            if trap {
                return halt(Behavior::Trap(TrapReason::Bounds), loc, "");
            }
            return ub(UbKind::Bounds, loc, format!("index {x}, length {m}"));
        }
        let Some(p) = p else { return Ok(None) };
        let aw = self.space.addr_bits;
        let stride = self.body().types().stride(self.space, ty);
        let off = u128::from(x).wrapping_mul(stride) as u64 & sem::mask(aw);
        Ok(
            match self.offset_by(true, p, i128::from(sem::sext64(aw, off)))? {
                Some(Value::Ptr(q)) => Some(q),
                _ => None,
            },
        )
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

    /// The function an indirect call runs: the one its pointer, `vs[0]`, points at the start of,
    /// which must have the call's signature (Lean's `callTarget`).
    fn call_target(&mut self, loc: Option<Loc>, sig: Ty, vs: &[Value]) -> R<u32> {
        let Some(&v) = vs.first() else {
            return stuck(loc, "malformed op");
        };
        let Some(p) = self.ptr_of(loc, v)? else {
            return ub(UbKind::Poison, loc, "call through a poison pointer");
        };
        let (a, _, off) = self.resolve(loc, p, 0)?;
        let Kind::Func(f) = self.allocs.kind[a as usize] else {
            return ub(UbKind::BadCall, loc, format!("#{a} is not a function"));
        };
        let name = self.fn_name(f);
        if off != 0 {
            return ub(
                UbKind::BadCall,
                loc,
                format!("offset {off} is not the start of @{name}"),
            );
        }
        // Parameter and result types, in the callee's table.
        let module: &'m Module = self.module;
        let mut params = Vec::new();
        let (rets, ctypes): (&[Ty], &Types) = match module.funcs.get(f as usize) {
            Some(callee) => {
                let cb = &callee.body;
                params.extend(cb.params(cb.entry()).map(|v| cb.ty(v)));
                (&callee.rets, cb.types())
            }
            None => {
                let x = &module.externs[(f - self.nfuncs) as usize];
                params.extend_from_slice(&x.params);
                (&x.rets, &module.globals.types)
            }
        };
        let types = self.body().types();
        let same = |xs: &[Ty], ys: &[Ty]| {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(&x, &y)| ctypes.same(x, types, y))
        };
        let ok = match types.shape_of(sig) {
            Some(Shape::Func(ps, rs)) => same(&params, ps) && same(rets, rs),
            _ => false,
        };
        if !ok {
            let mut t = String::from("func<(");
            for (i, &p) in params.iter().enumerate() {
                if i > 0 {
                    t.push_str(", ");
                }
                ctypes.write(&mut t, p);
            }
            t.push(')');
            crate::types::write_rets(&mut t, rets, |out, &r| ctypes.write(out, r));
            t.push('>');
            return ub(UbKind::BadCall, loc, format!("@{name} has type {t}"));
        }
        Ok(f)
    }

    // External calls

    /// The zero value of a value type (Lean's `Ty.zero`).
    fn zero(&mut self, t: Ty) -> Value {
        match t {
            Ty::Int(w) if w <= 64 => Value::Int { w, bits: 0 },
            Ty::Int(w) => {
                self.wides.push(BigUint::default());
                Value::Wide {
                    w,
                    id: (self.wides.len() - 1) as u32,
                }
            }
            Ty::Ptr => Value::Ptr(NULL),
            Ty::Float(f) => Value::Float { f, bits: 0 },
            Ty::Byte(w) => {
                let start = self.byte_vals.len() as u32;
                let n = w / 8;
                self.byte_vals
                    .extend(std::iter::repeat_n(Byte::Bits(0), n as usize));
                Value::Bytes { start, len: n }
            }
            Ty::Agg(_) | Ty::Slice => Value::Bytes { start: 0, len: 0 },
        }
    }

    /// The `(allocation, tag)` pairs pointer `p` may access memory through (Lean's
    /// `Ptr.pairs`).
    fn push_pairs(&self, p: u32, out: &mut Vec<(u32, u32)>) {
        match self.ptrs[p as usize] {
            Ptr::Rel { alloc, tag, .. } => out.push((alloc, tag)),
            Ptr::Abs { cands, .. } => out.extend_from_slice(self.cands(cands)),
        }
    }

    /// Whether an external function may access allocation `a` for `how` (Lean's `mayAccess`).
    fn may_access(
        &self,
        x: &Extern,
        how: fn(MemClass) -> ExtEffect,
        arg_allocs: &[u32],
        reach: &FxHashSet<u32>,
        a: u32,
    ) -> bool {
        let ai = a as usize;
        let kind = self.allocs.kind[ai];
        let global = matches!(kind, Kind::Global(_));
        let constant = matches!(kind, Kind::Global(g) if self.module.globals.is_const(g as usize));
        self.allocs.live[ai]
            && !matches!(kind, Kind::Func(_))
            && !(how(MemClass::Args) == ExtEffect::Write(MemClass::Args) && constant)
            && ((x.has(how(MemClass::Args)) && arg_allocs.contains(&a))
                || (x.has(how(MemClass::Globals)) && global)
                || (x.has(how(MemClass::Exposed)) && reach.contains(&a)))
    }

    /// What an external call can reach (Lean's `externReach`): its roots, then the pointers
    /// stored in memory it may read, until nothing new turns up.
    fn extern_reach(&self, x: &Extern, vs: &[Value]) -> Vec<(u32, u32)> {
        let names = |m| x.has(ExtEffect::Read(m)) || x.has(ExtEffect::Write(m));
        let mut found = Vec::new();
        for &v in vs {
            if let Value::Ptr(p) = v {
                self.push_pairs(p, &mut found);
            }
        }
        let arg_allocs: Vec<u32> = found.iter().map(|&(a, _)| a).collect();
        if names(MemClass::Globals) {
            found.extend((1..=self.module.globals.len() as u32).map(|a| (a, a)));
        }
        if names(MemClass::Exposed) {
            for a in 1..self.allocs.size.len() {
                if self.allocs.live[a] {
                    let mut cur = self.allocs.exposed[a];
                    while cur != NONE {
                        let (t, next) = self.exposures[cur as usize];
                        found.push((a as u32, t));
                        cur = next;
                    }
                }
            }
        }
        let mut reach = Vec::new();
        let mut seen = FxHashSet::default();
        for pair in found.drain(..) {
            if seen.insert(pair) {
                reach.push(pair);
            }
        }
        loop {
            let allocs: FxHashSet<u32> = reach.iter().map(|&(a, _)| a).collect();
            let mut done = FxHashSet::default();
            for &(a, _) in &reach {
                if !done.insert(a) || !self.may_access(x, ExtEffect::Read, &arg_allocs, &allocs, a)
                {
                    continue;
                }
                let size = self.allocs.size[a as usize];
                let frag = |b: Byte, found: &mut Vec<(u32, u32)>| {
                    if let Byte::Frag { ptr, .. } = b {
                        self.push_pairs(ptr, found);
                    }
                };
                match &self.allocs.bytes[a as usize] {
                    Mem::Dense(v) => {
                        for &b in v.iter().take(size as usize) {
                            frag(b, &mut found);
                        }
                    }
                    Mem::Sparse(m) => {
                        let mut offs: Vec<u64> = m.keys().copied().filter(|&o| o < size).collect();
                        offs.sort_unstable();
                        for o in offs {
                            frag(m[&o], &mut found);
                        }
                    }
                }
            }
            let before = reach.len();
            for pair in found.drain(..) {
                if seen.insert(pair) {
                    reach.push(pair);
                }
            }
            if reach.len() == before {
                return reach;
            }
        }
    }

    /// Call external function `x` (Lean's `callExtern`, in the world that answers zeros and
    /// changes nothing): check the arguments, expose everything the callee can reach, record the
    /// event, and return the results through an `ExternRet` frame, one step later.
    fn call_extern(&mut self, op: OpId, loc: Option<Loc>, x: u32, vs: &[Value]) -> R<()> {
        let module: &'m Module = self.module;
        let ext = &module.externs[x as usize];
        if vs.len() != ext.params.len()
            || !vs.iter().zip(&ext.params).all(|(&v, &t)| self.has_ty(v, t))
        {
            return stuck(loc, format!("wrong arguments for @{}", ext.name));
        }
        for (a, t) in self.extern_reach(ext, vs) {
            if self.allocs.live[a as usize] {
                self.realize(loc, a)?;
                self.add_exposure(a, t);
            }
        }
        let mut trace = std::mem::take(&mut self.trace);
        trace.push('@');
        trace.push_str(&ext.name);
        trace.push('(');
        for (i, &v) in vs.iter().enumerate() {
            if i > 0 {
                trace.push_str(", ");
            }
            self.render_value(v, &mut trace);
        }
        trace.push_str(") -> ");
        if ext.rets.is_empty() {
            trace.push_str("()");
        }
        for (i, &t) in ext.rets.iter().enumerate() {
            if i > 0 {
                trace.push_str(", ");
            }
            let v = self.zero(t);
            self.render_value(v, &mut trace);
        }
        trace.push_str("; ");
        self.trace = trace;
        self.frames.push(Frame::ExternRet { op, ext: x });
        Ok(())
    }

    /// The heap allocations still live, for the leak report.
    fn leaks(&self) -> Vec<String> {
        (1..self.allocs.size.len())
            .filter_map(|a| match self.allocs.kind[a] {
                Kind::Heap(f) if self.allocs.live[a] => Some(format!(
                    "leak: {} bytes from {} at {}",
                    self.allocs.size[a],
                    self.families[f as usize],
                    render_loc(self.allocs.sites[a].0)
                )),
                _ => None,
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

    /// Jump to block `s` of the nearest `cf.blocks` with arguments `vs`: pop the frames above
    /// it, ending their stack memory, and start the block (Lean's `jump`).
    fn jump(&mut self, loc: Option<Loc>, s: Succ, vs: &[Value]) -> R<()> {
        let body = self.body();
        let Some(i) = self.find_frame(|f| matches!(f, Frame::Blocks { .. })) else {
            return stuck(loc, "a jump outside cf.blocks");
        };
        let Frame::Blocks { op, allocs, .. } = self.frames[i] else {
            unreachable!()
        };
        let label = body.str(s.label);
        let Some(&r) = body
            .regions(op)
            .iter()
            .find(|&&r| body.label(r).is_some_and(|l| body.str(l) == label))
        else {
            return stuck(loc, format!("no block ^{label}"));
        };
        self.release_from(allocs);
        self.frames.truncate(i + 1);
        self.enter_body(loc, r, vs)
    }

    /// Whether `cf.switch`'s key `k` is the `w`-bit value `v`, modulo `2^w`.
    fn key_matches(&self, k: Int<'_>, w: u32, v: Value) -> bool {
        match (k, v) {
            (Int::Small(k), Value::Int { bits, .. }) => {
                i128::from(k).rem_euclid(1i128 << w) as u64 == bits
            }
            (k, Value::Int { bits, .. }) => key_mod(k, w) == BigInt::from(bits),
            (k, Value::Wide { id, .. }) => {
                key_mod(k, w) == BigInt::from(self.wides[id as usize].clone())
            }
            _ => false,
        }
    }

    /// Run a terminator; the current block has already been popped (Lean's `terminate`).
    fn terminate(&mut self, loc: Option<Loc>, k: OpKind, vs: &[Value]) -> R<()> {
        let body = self.body();
        match k {
            OpKind::Yield => match self.frames.last() {
                Some(
                    &Frame::IfJoin { op } | &Frame::Blocks { op, .. } | &Frame::Try { op, .. },
                ) => {
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
                    let mut lowered = Vec::new();
                    let vs = if self.lower_rets {
                        let types = self.body().types();
                        for (&v, &t) in vs.iter().zip(rets) {
                            self.lower_value(types, t, v, &mut lowered);
                        }
                        &lowered[..]
                    } else {
                        vs
                    };
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
            OpKind::Br { dest } => self.jump(loc, body.succ(dest), vs),
            OpKind::CondBr { t, f } => {
                let c = match vs.first() {
                    Some(&v) => self.bits(loc, v)?,
                    None => None,
                };
                let Some(c) = c else {
                    return ub(UbKind::Poison, loc, "branch on poison");
                };
                let t = body.succ(t);
                let rest = vs.get(1..).unwrap_or_default();
                let n = (t.nargs as usize).min(rest.len());
                if c.is_zero() {
                    self.jump(loc, body.succ(f), &rest[n..])
                } else {
                    self.jump(loc, t, &rest[..n])
                }
            }
            OpKind::Switch { dflt, cases } => {
                let (v, rest) = match vs.split_first() {
                    Some((&v, rest)) => (v, rest),
                    None => return stuck(loc, "cf.switch needs an integer"),
                };
                let w = match v {
                    Value::Int { w, .. } | Value::Wide { w, .. } => w,
                    Value::Poison { .. } => return ub(UbKind::Poison, loc, "branch on poison"),
                    _ => return stuck(loc, "cf.switch needs an integer"),
                };
                let dflt = body.succ(dflt);
                let take = |at: usize, n: u32| {
                    let end = (at + n as usize).min(rest.len());
                    &rest[at.min(end)..end]
                };
                let mut at = dflt.nargs as usize;
                for c in body.cases(cases) {
                    if self.key_matches(body.int(c.key), w, v) {
                        return self.jump(loc, c.succ, take(at, c.succ.nargs));
                    }
                    at += c.succ.nargs as usize;
                }
                self.jump(loc, dflt, take(0, dflt.nargs))
            }
            OpKind::Throw => match vs {
                &[v] if self.has_ty(v, Ty::Ptr) => self.throw_exn(loc, v),
                [_] => stuck(loc, "exn.throw needs a ptr"),
                _ => stuck(loc, "exn.throw takes one value"),
            },
            _ => stuck(loc, "not a terminator"),
        }
    }

    /// Throw the exception `v` (Lean's `throwExn`): pop frames, ending their stack memory and
    /// closing the scopes of the calls they leave, up to the nearest `cf.try` frame or call
    /// frame of a `func.invoke`, and run its handler with `v`; or end the run with `threw`.
    fn throw_exn(&mut self, loc: Option<Loc>, v: Value) -> R<()> {
        loop {
            match self.frames.last() {
                None => {
                    let mut out = String::new();
                    self.render_value(v, &mut out);
                    return Err(Box::new(Halt {
                        behavior: Behavior::Threw(out),
                        loc,
                        note: String::new(),
                        leaks: self.leaks(),
                    }));
                }
                Some(&Frame::Block { allocs, .. }) => {
                    self.frames.pop();
                    self.release_from(allocs);
                }
                Some(&Frame::Try { op, allocs }) => {
                    self.release_from(allocs);
                    self.frames.pop();
                    self.frames.push(Frame::IfJoin { op });
                    let handler = self.body().regions(op)[1];
                    return self.enter_body(loc, handler, &[v]);
                }
                Some(&Frame::Call {
                    op,
                    func,
                    base,
                    scopes,
                    allocs,
                }) => {
                    self.release_from(allocs);
                    self.scopes.truncate(scopes as usize);
                    self.marks.truncate(scopes as usize);
                    self.frames.pop();
                    let Some(op) = op else {
                        continue;
                    };
                    self.slots.truncate(self.base as usize);
                    self.func = func;
                    self.base = base;
                    let body = self.body();
                    if let OpKind::Invoke { unwind, .. } | OpKind::InvokeIndirect { unwind, .. } =
                        body.kind(op)
                    {
                        return self.jump(loc, body.succ(unwind), &[v]);
                    }
                }
                Some(Frame::IfJoin { .. } | Frame::Loop { .. } | Frame::Blocks { .. })
                | Some(Frame::ExternRet { .. }) => {
                    self.frames.pop();
                }
            }
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
            OpKind::Blocks { progress } => {
                let Some(&entry) = body.regions(op).first() else {
                    return stuck(loc, "malformed op");
                };
                self.frames.push(Frame::Blocks {
                    op,
                    progress,
                    allocs: self.stack_allocs.len() as u32,
                });
                self.enter_body(loc, entry, &[])?;
            }
            OpKind::Try => {
                let regions = body.regions(op);
                if regions.len() != 2 {
                    return stuck(loc, "malformed op");
                }
                self.frames.push(Frame::Try {
                    op,
                    allocs: self.stack_allocs.len() as u32,
                });
                self.push_block(regions[0]);
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
            OpKind::Call { .. }
            | OpKind::CallIndirect(_)
            | OpKind::Invoke { .. }
            | OpKind::InvokeIndirect { .. } => {
                self.operands(op, loc, &mut vs)?;
                let (f, args) = match kind {
                    OpKind::Call { callee } | OpKind::Invoke { callee, .. } => {
                        let name = body.str(callee);
                        let Some(&f) = self.funcs.get(name) else {
                            return stuck(loc, format!("no function @{name}"));
                        };
                        (f, 0)
                    }
                    OpKind::CallIndirect(sig) | OpKind::InvokeIndirect { sig, .. } => {
                        (self.call_target(loc, sig, &vs)?, 1)
                    }
                    _ => unreachable!(),
                };
                if f >= self.nfuncs {
                    self.call_extern(op, loc, f - self.nfuncs, &vs[args..])?;
                    self.scratch = vs;
                    return Ok(());
                }
                let (caller, caller_base) = (self.func, self.base);
                let scopes = self.scopes.len() as u32;
                self.func = f;
                self.base = self.slots.len() as u32;
                let n = self.body().num_values();
                self.slots.resize(self.slots.len() + n, Value::Unset);
                self.enter_call(loc, &vs[args..])?;
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
            OpKind::MemStack { .. } | OpKind::MemStackOf { .. } => {
                let (size, align) = match kind {
                    OpKind::MemStack { size, align } => (size, align),
                    OpKind::MemStackOf { ty, align } => {
                        let (size, a) = body.types().dims(self.space, ty);
                        (size as u64, align.max(a as u32))
                    }
                    _ => unreachable!(),
                };
                let p = self.new_alloc(loc, size, align, Kind::Stack);
                self.bind(loc, body.results(op), &[Value::Ptr(p)])?;
                let Ptr::Rel { alloc, .. } = self.ptrs[p as usize] else {
                    unreachable!()
                };
                self.stack_allocs.push(alloc);
            }
            OpKind::Yield
            | OpKind::Break
            | OpKind::Continue
            | OpKind::Ret
            | OpKind::Br { .. }
            | OpKind::CondBr { .. }
            | OpKind::Switch { .. }
            | OpKind::Throw => {
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
                if let OpKind::Overflow { op: aop, signed } = kind {
                    let w = match rty {
                        Some(Ty::Int(w)) => w,
                        _ => 0,
                    };
                    let (a, b) = match vs[..] {
                        [a, b] => (self.bits(loc, a)?, self.bits(loc, b)?),
                        _ => return stuck(loc, "malformed op"),
                    };
                    let out = match (a, b) {
                        (Some(a), Some(b)) => {
                            let (r, o) = sem::overflow_pair(aop, signed, w, &a, &b);
                            [
                                self.int_value(w, Some(r)),
                                Value::Int {
                                    w: 1,
                                    bits: u64::from(o),
                                },
                            ]
                        }
                        _ => [Value::Poison { w }, Value::Poison { w: 1 }],
                    };
                    self.bind(loc, results, &out)?;
                    self.scratch = vs;
                    return Ok(());
                }
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
        if let Some(&Frame::ExternRet { op, ext }) = self.frames.last() {
            // The synthesized `func.ret`: bind the results as any callee's are bound.
            self.frames.pop();
            let module: &'m Module = self.module;
            let mut vs = std::mem::take(&mut self.scratch);
            vs.clear();
            for &t in &module.externs[ext as usize].rets {
                let v = self.zero(t);
                vs.push(v);
            }
            let body = self.body();
            let r = self.bind(body.loc(op), body.results(op), &vs);
            self.scratch = vs;
            return r;
        }
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

    /// The scalars an HFIR value of type `t` is represented by after lowering (Lean's
    /// `Lower.lowerValue`): its leaves, and for a union `poison` for the variants it doesn't hold.
    fn lower_value(&mut self, types: &Types, t: Ty, v: Value, out: &mut Vec<Value>) {
        let parts: Vec<Value> = match self.parts(v) {
            Some(ps) => ps.to_vec(),
            None => {
                out.push(v);
                return;
            }
        };
        match types.shape_of(t) {
            Some(Shape::Struct(_, fs)) => {
                for (&f, &p) in fs.iter().zip(&parts) {
                    self.lower_value(types, f, p, out);
                }
            }
            Some(Shape::Array(_, e)) => {
                for &p in &parts {
                    self.lower_value(types, e, p, out);
                }
            }
            Some(Shape::Union(vs)) => match parts[..] {
                [tag @ Value::Int { w: 32, bits }, payload] => {
                    out.push(tag);
                    for (j, &u) in vs.iter().enumerate() {
                        if j as u64 == bits {
                            self.lower_value(types, u, payload, out);
                        } else {
                            let mut ts = Vec::new();
                            types.scalars(self.space.addr_bits, u, &mut ts);
                            for t in ts {
                                let p = self.poison_of(t);
                                out.push(p);
                            }
                        }
                    }
                }
                _ => self.leaf_values(v, out),
            },
            _ => self.leaf_values(v, out),
        }
    }

    /// The `poison` value of a scalar type.
    fn poison_of(&mut self, t: Ty) -> Value {
        match t {
            Ty::Ptr => Value::PtrPoison,
            Ty::Float(f) => Value::FloatPoison(f),
            Ty::Byte(w) => {
                let start = self.byte_vals.len() as u32;
                self.byte_vals
                    .extend(std::iter::repeat_n(Byte::Poison, (w / 8) as usize));
                Value::Bytes { start, len: w / 8 }
            }
            t => Value::Poison {
                w: match t {
                    Ty::Int(w) => w,
                    _ => 0,
                },
            },
        }
    }

    /// Run at most `fuel` steps and describe the outcome (`fir-ref run`'s `drive`).
    fn drive(&mut self, fuel: u64) -> RunOutput {
        let mut steps = 0;
        loop {
            if steps >= fuel {
                let progress = self.frames.iter().any(|f| {
                    matches!(
                        f,
                        Frame::Loop { progress: true, .. } | Frame::Blocks { progress: true, .. }
                    )
                });
                let tail = if progress { " in a progress loop" } else { "" };
                return RunOutput {
                    line: format!("{}out of fuel after {fuel} steps{tail}", self.trace),
                    events: self.trace.clone(),
                    absorbing: false,
                    out_of_fuel: true,
                };
            }
            if let Err(h) = self.step() {
                return RunOutput {
                    line: format!("{}{}", self.trace, h.render()),
                    events: self.trace.clone(),
                    absorbing: matches!(h.behavior, Behavior::Ub(_) | Behavior::Stuck(_)),
                    out_of_fuel: false,
                };
            }
            steps += 1;
        }
    }
}
