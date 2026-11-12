//! Random well-typed FIR programs, for differential testing against the Lean reference.
//!
//! A program has one to three functions; `@f0` is the entry, and each function calls only the
//! ones after it, so there is no recursion. Bodies mix integer ops of every width class (1, 8,
//! 16, 32, 64, odd, and over 128 bits) with every edge-case modifier; `cf.if` (sometimes leaving
//! an enclosing loop) and counted `cf.loop`s (sometimes `progress`, sometimes with a bound from
//! an argument); `cf.blocks` (sometimes `progress`) whose blocks jump to each other with `cf.br`,
//! `cf.cond_br`, and `cf.switch` (on any width, with keys written signed or unsigned), forward
//! (fall-through), backward (loops bounded by a counter, except sometimes), and out of nested
//! `cf.if` regions, or leave by `cf.yield`, a loop exit, or `func.ret`; and memory. The generator tracks the allocations in scope, so most loads and
//! stores go to valid, aligned offsets and runs get far; the rest are out of bounds, misaligned,
//! through null, dangling, or freed pointers. Memory ops cover stack and heap allocations,
//! loads and stores of integers, pointers, and bytes (so pointers are read back as integers and
//! integers as pointers), frees (sometimes twice, or of the wrong family), pointer offsets,
//! address observation, exposure and `ptr.from_exposed` of nearby addresses, `ptr.with_addr`,
//! comparisons, facts on results and parameters, and calls passing possibly aliasing pointers to
//! `noalias` and `readonly` parameters.
//!
//! Structs (all three layouts) and arrays appear as typed stack slots, globals, and copies, with
//! `ty.size`/`ty.align`/`ty.offset` and field and element addresses (usually valid, sometimes
//! out of bounds or overflowing); programs declare globals of scalar and aggregate types with
//! every kind of initializer, some `const` (and sometimes written anyway), and sometimes a data
//! layout of their own. Functions' addresses are taken, stored, compared, exposed, and called
//! through, usually with the right signature and sometimes with another, or through a data, null,
//! offset, or poison pointer; globals hold function tables that calls dispatch through. External
//! functions (`@x0`, …) with random effects are called directly and through pointers and tables,
//! so their events, the exposure of what they reach, and the facts on their results are
//! covered. Programs sometimes declare their layer: `layer hfir`, or `layer mfir`, where field and
//! element addresses are `ptr.offset` by `ty.offset` or a multiplied stride instead of `ptr.field`
//! and `ptr.index`. Stores are sometimes followed at once by another store or a load through the
//! same pointer, and copies come in chains, so the passes' patterns occur.
//!
//! Exceptions: HFIR programs catch with `cf.try` (results of any value type, handlers that use
//! the exception, rethrow it, or fall through), anywhere a statement goes, loops and blocks
//! included; `exn.throw` ends `cf.if` branches, blocks, try regions, and functions, so
//! exceptions leave loops, `cf.blocks`, and calls, and sometimes the entry function (`threw`).
//! What is thrown is usually a fresh heap object holding an `i32` that handlers load, sometimes
//! a global, null, or any pointer. MFIR programs give some `cf.blocks` a handler block, which
//! direct and indirect calls in it name (`func.invoke`). Each program comes with argument lists
//! and fuel limits.
//!
//! Floats (`f32`, `f64`; not in the narrow mode, whose programs the AArch64 backend compiles):
//! every `float.*` op and `int.to_float`, with constants biased toward the edge cases (zeros of
//! both signs, subnormals, the largest values, infinities, NaNs with payloads, integers at the
//! conversions' limits, halfway cases), conversions to and from integers of every width class
//! with every edge-case modifier, `float.from_bits` of interesting integers, `select`,
//! `freeze`, `poison`, and `copy` of floats, and floats as parameters, results, loop and block
//! state, parts of aggregates and unions, globals, and values loaded and stored (and read back as
//! integers and bytes).

use std::fmt::Write;

use num_bigint::BigInt;

/// A small deterministic random number generator (SplitMix64). A *narrow* one also makes the
/// generator keep integers to at most 64 bits and the data layout to the default (64-bit
/// pointers), as the AArch64 backend needs.
pub struct Rng(u64, bool);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed, false)
    }

    // Only the AArch64 test uses it.
    #[allow(dead_code)]
    pub fn narrow(seed: u64) -> Rng {
        Rng(seed, true)
    }

    /// An integer width from `ws`, at most 64 for a narrow generator.
    pub fn width(&mut self, ws: &[u32]) -> u32 {
        let w = self.pick(ws);
        if self.1 { w.min(64) } else { w }
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number below `n`.
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// True with probability `p` percent.
    pub fn chance(&mut self, p: u64) -> bool {
        self.below(100) < p
    }

    pub fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum T {
    I(u32),
    P,
    B(u32),
    /// `f32` or `f64`, by width.
    F(u32),
    /// An HFIR aggregate, union, or slice type: an index into the program's `VTYS`.
    V(u8),
}

/// An HFIR value type that isn't a scalar.
#[derive(Clone, Debug)]
enum VTy {
    Struct(&'static str, Vec<T>),
    Array(u64, T),
    Union(Vec<T>),
    Slice,
}

thread_local! {
    /// The value types of the program being generated, so that `T` stays `Copy` and prints
    /// itself.
    static VTYS: std::cell::RefCell<Vec<VTy>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn vty(i: u8) -> VTy {
    VTYS.with(|v| v.borrow()[i as usize].clone())
}

fn num_vtys() -> usize {
    VTYS.with(|v| v.borrow().len())
}

impl T {
    /// Whether memory can hold the type, so it can be a struct field or array element.
    fn has_layout(self) -> bool {
        match self {
            T::I(w) => w % 8 == 0,
            T::P | T::B(_) | T::F(_) => true,
            T::V(i) => !matches!(vty(i), VTy::Union(_)),
        }
    }
}

impl std::fmt::Display for T {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let list = |f: &mut std::fmt::Formatter<'_>, ts: &[T]| -> std::fmt::Result {
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{t}")?;
            }
            Ok(())
        };
        match self {
            T::I(w) => write!(f, "i{w}"),
            T::P => f.write_str("ptr"),
            T::B(w) => write!(f, "b{w}"),
            T::F(w) => write!(f, "f{w}"),
            T::V(i) => match vty(*i) {
                VTy::Struct(p, fs) => {
                    write!(f, "struct<{p}>{{")?;
                    list(f, &fs)?;
                    f.write_str("}")
                }
                VTy::Array(n, e) => write!(f, "array<{n} x {e}>"),
                VTy::Union(vs) => {
                    f.write_str("union<")?;
                    list(f, &vs)?;
                    f.write_str(">")
                }
                VTy::Slice => f.write_str("slice"),
            },
        }
    }
}

/// The HFIR value types of a program: a few structs, arrays, unions, and slices, which may
/// nest the earlier ones.
fn make_vtys(rng: &mut Rng) {
    let mut out: Vec<VTy> = Vec::new();
    let n = 2 + rng.below(4);
    for _ in 0..n {
        let earlier: Vec<T> = (0..out.len() as u8).map(T::V).collect();
        let part = |rng: &mut Rng, layout: bool| -> T {
            let nested: Vec<T> = earlier
                .iter()
                .copied()
                .filter(|&t| match t {
                    T::V(i) => !(layout && matches!(out[i as usize], VTy::Union(_))),
                    _ => true,
                })
                .collect();
            if !nested.is_empty() && rng.chance(25) {
                return rng.pick(&nested);
            }
            if !rng.1 && rng.chance(15) {
                return T::F(rng.pick(&[32, 64]));
            }
            match rng.below(10) {
                0..=1 => T::P,
                2 if !layout => T::I(rng.width(&[1, 7, 65])),
                3 => T::B(32),
                _ => T::I(rng.pick(&[8, 16, 32, 64])),
            }
        };
        let t = match rng.below(10) {
            0..=3 => {
                let p = rng.pick(&["C", "C", "packed", "auto"]);
                let k = 1 + rng.below(3);
                VTy::Struct(p, (0..k).map(|_| part(rng, true)).collect())
            }
            4..=5 => VTy::Array(1 + rng.below(3), part(rng, true)),
            6..=8 => {
                let k = 1 + rng.below(3);
                VTy::Union((0..k).map(|_| part(rng, false)).collect())
            }
            _ => VTy::Slice,
        };
        out.push(t);
    }
    VTYS.with(|v| *v.borrow_mut() = out);
}

/// A generated program, with the arguments and fuel to run its entry `@f0` with.
pub struct Program {
    pub text: String,
    pub runs: Vec<(Vec<String>, u64)>,
}

struct Sig {
    params: Vec<T>,
    rets: Vec<T>,
}

/// A struct or array type, or a value type inside one.
#[derive(Clone, PartialEq, Debug)]
enum Agg {
    Scalar(T),
    Struct(&'static str, Vec<Agg>),
    Array(u64, Box<Agg>),
}

impl std::fmt::Display for Agg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Agg::Scalar(t) => write!(f, "{t}"),
            Agg::Struct(p, fs) => {
                write!(f, "struct<{p}>{{")?;
                for (i, x) in fs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str("}")
            }
            Agg::Array(n, e) => write!(f, "array<{n} x {e}>"),
        }
    }
}

/// The program's data layout, for the generator's own layout computations.
#[derive(Clone)]
struct Layout {
    ptr_size: u64,
    ptr_align: u64,
    /// `(width, alignment)` by increasing width.
    ints: Vec<(u32, u64)>,
}

/// The largest power of two at most `x` (and at least 1).
fn floor_pow2(x: u64) -> u64 {
    1 << x.max(1).ilog2()
}

fn align_up(x: u64, a: u64) -> u64 {
    x.div_ceil(a.max(1)) * a.max(1)
}

impl Layout {
    fn int_align(&self, w: u32) -> u64 {
        match self.ints.iter().find(|e| e.0 >= w) {
            Some(e) => e.1,
            None => self.ints.last().map_or(1, |e| e.1),
        }
    }

    /// Size and alignment.
    fn dims(&self, a: &Agg) -> (u64, u64) {
        match a {
            Agg::Scalar(T::I(w) | T::B(w) | T::F(w)) => (u64::from(*w / 8), self.int_align(*w)),
            Agg::Scalar(T::P) => (self.ptr_size, self.ptr_align),
            Agg::Struct(p, fs) => {
                let (offs, size, align) = self.place(p, fs);
                let _ = offs;
                (size, align)
            }
            Agg::Array(n, e) => {
                let (s, a) = self.dims(e);
                (n * align_up(s, a), a)
            }
            Agg::Scalar(T::V(_)) => unreachable!("memory aggregates hold scalars"),
        }
    }

    fn stride(&self, a: &Agg) -> u64 {
        let (s, al) = self.dims(a);
        align_up(s, al)
    }

    /// Field offsets in declared order, size, and alignment.
    fn place(&self, p: &str, fs: &[Agg]) -> (Vec<u64>, u64, u64) {
        let mut ds: Vec<(usize, u64, u64)> = fs
            .iter()
            .enumerate()
            .map(|(i, f)| (i, self.stride(f), self.dims(f).1))
            .collect();
        let align = ds.iter().map(|d| d.2).max().unwrap_or(1).max(1);
        if p == "auto" {
            ds.sort_by_key(|d| std::cmp::Reverse(d.2));
        }
        let mut offs = vec![0; fs.len()];
        let mut o = 0;
        for &(i, s, a) in &ds {
            if p != "packed" {
                o = align_up(o, a);
            }
            offs[i] = o;
            o += s;
        }
        if p == "packed" {
            (offs, o, 1)
        } else {
            (offs, align_up(o, align), align)
        }
    }
}

/// A global: its name, type, and whether it is `const`; and, for a table of function pointers
/// (an array of `ptr`), the function each element points at.
#[derive(Clone)]
struct GlobalInfo {
    name: String,
    agg: Agg,
    constant: bool,
    align: u64,
    table: Option<Vec<usize>>,
}

/// A pointer in scope known to point at the start of an allocation (or assumed to, for pointer
/// parameters).
#[derive(Clone)]
struct Mem {
    name: String,
    size: u64,
    align: u64,
    /// The heap family, for frees.
    family: Option<&'static str>,
    /// What it holds, when it was allocated or found with a type.
    agg: Option<Agg>,
    /// A `const` global: writing it is UB.
    constant: bool,
}

const WIDTHS: &[u32] = &[1, 8, 8, 16, 32, 32, 32, 64, 64, 7, 65, 128, 200];

/// A `cf.blocks` being generated. Every block after the entry starts with a counter, the number
/// of jumps so far, and usually jumps to the exit block once it reaches a limit, so back edges
/// end; the exit block yields the op's results.
struct Blocks {
    /// Each block's label and parameter types (the counter first, except for the entry and the
    /// exit).
    labels: Vec<(String, Vec<T>)>,
    /// What a jump from the current block passes as the counter.
    next: String,
    /// The label of its handler block (MFIR), which calls may name with `func.invoke`.
    handler: Option<String>,
}

/// A constant of width `w`, biased toward edge cases. Written signed or unsigned.
fn interesting(rng: &mut Rng, w: u32) -> BigInt {
    let one = BigInt::from(1);
    let max_u = (&one << w) - 1u32;
    let max_s = (&one << (w - 1)) - 1u32;
    let min_s = -(&one << (w - 1));
    match rng.below(10) {
        0 => BigInt::from(0),
        1 => BigInt::from(1),
        2 => BigInt::from(-1).max(min_s),
        3 => max_s,
        4 => min_s,
        5 => max_u,
        6 | 7 => BigInt::from(rng.below(8)) & max_u,
        _ => {
            let mut x = BigInt::from(0);
            for _ in 0..w.div_ceil(64) {
                x = (x << 64u32) + BigInt::from(rng.next());
            }
            let x = x & &max_u;
            if rng.chance(50) && x > max_s {
                x - (&one << w)
            } else {
                x
            }
        }
    }
}

struct Gen<'r> {
    rng: &'r mut Rng,
    out: String,
    line: u32,
    /// The functions' signatures, then the external functions'.
    sigs: Vec<Sig>,
    /// How many functions there are; the rest of `sigs` are external functions.
    nfuncs: usize,
    func: usize,
    /// The values visible here, with their types.
    scope: Vec<(String, T)>,
    /// The visible pointers to allocations.
    mems: Vec<Mem>,
    /// Visible address-size integers that are exposed addresses.
    exposed: Vec<String>,
    next: u32,
    depth: usize,
    /// The enclosing loops' parameter and result types, innermost last.
    loops: Vec<(Vec<T>, Vec<T>)>,
    /// The enclosing `cf.blocks`, innermost last.
    blocks: Vec<Blocks>,
    addr: u32,
    ptr_size: u32,
    ops_left: u32,
    layout: Layout,
    globals: Vec<GlobalInfo>,
    /// Visible pointers to functions, with the function they point at.
    fnptrs: Vec<(String, usize)>,
    /// Whether the module is MFIR, which has no `ptr.field` or `ptr.index`.
    mfir: bool,
    /// Values read back after stores in the function's top region, which `func.ret` prefers, so
    /// that what memory holds shows in the outcome.
    watch: Vec<(String, T)>,
}

impl Gen<'_> {
    /// The name of function `k`: `f0`, `f1`, …, then the external functions `x0`, `x1`, ….
    fn fn_name(&self, k: usize) -> String {
        if k < self.nfuncs {
            format!("f{k}")
        } else {
            format!("x{}", k - self.nfuncs)
        }
    }

    /// The external functions, with random effects. Pointers passed to them are exposed along
    /// with what their effects let them reach, so later `ptr.from_exposed` can find more.
    fn declare_externs(&mut self) {
        for k in self.nfuncs..self.sigs.len() {
            let sig = &self.sigs[k];
            let ps: Vec<String> = sig.params.iter().map(T::to_string).collect();
            let rs: Vec<String> = sig.rets.iter().map(T::to_string).collect();
            let rets = match rs.len() {
                0 => String::new(),
                1 => format!(" -> {}", rs[0]),
                _ => format!(" -> ({})", rs.join(", ")),
            };
            let mut all = vec![
                "read(args)",
                "write(args)",
                "read(exposed)",
                "write(exposed)",
                "read(globals)",
                "write(globals)",
                "alloc",
                "free",
                "trap",
                "diverge",
            ];
            let mut effects = Vec::new();
            while !all.is_empty() && self.rng.chance(55) {
                let i = self.rng.below(all.len() as u64) as usize;
                effects.push(all.remove(i));
            }
            let trust = if self.rng.chance(80) {
                "assume"
            } else {
                "check"
            };
            let name = self.fn_name(k);
            write!(
                self.out,
                "extern func @{name}({}){rets} effects[{}] {trust}",
                ps.join(", "),
                effects.join(", ")
            )
            .unwrap();
            self.newline();
        }
        if self.sigs.len() > self.nfuncs {
            self.newline();
        }
    }

    fn fresh(&mut self) -> String {
        self.next += 1;
        format!("v{}", self.next)
    }

    fn indent(&mut self) {
        for _ in 0..self.depth + 1 {
            self.out.push_str("  ");
        }
    }

    fn loc(&mut self) -> String {
        if self.rng.chance(92) {
            format!(" @{}:{}", self.line, self.depth * 2 + 3)
        } else {
            String::new()
        }
    }

    fn newline(&mut self) {
        self.out.push('\n');
        self.line += 1;
    }

    /// What is visible, to restore when a region ends.
    fn mark(&self) -> (usize, usize, usize, usize) {
        (
            self.scope.len(),
            self.mems.len(),
            self.exposed.len(),
            self.fnptrs.len(),
        )
    }

    fn restore(&mut self, m: (usize, usize, usize, usize)) {
        self.scope.truncate(m.0);
        self.mems.truncate(m.1);
        self.exposed.truncate(m.2);
        self.fnptrs.truncate(m.3);
    }

    /// Emit `results = body @loc` and define the results.
    fn op(&mut self, results: &[(String, T, String)], body: &str) {
        self.indent();
        let rs: Vec<String> = results
            .iter()
            .map(|(n, t, facts)| format!("%{n}: {t}{facts}"))
            .collect();
        if !rs.is_empty() {
            write!(self.out, "{} = ", rs.join(", ")).unwrap();
        }
        let loc = self.loc();
        write!(self.out, "{body}{loc}").unwrap();
        self.newline();
        for (n, t, _) in results {
            self.scope.push((n.clone(), *t));
        }
    }

    /// Define one result of type `t`, sometimes with a fact.
    fn def(&mut self, t: T, body: &str) -> String {
        let n = self.fresh();
        let facts = if self.rng.chance(1) {
            self.fact(t, false)
        } else {
            String::new()
        };
        self.op(&[(n.clone(), t, facts)], body);
        n
    }

    /// A bracketed fact for a value of type `t`, or nothing.
    fn fact(&mut self, t: T, param: bool) -> String {
        let trust = self.rng.pick(&["assume", "check", "proved"]);
        let f = match t {
            T::I(w) => {
                let signed = self.rng.chance(50);
                let m = BigInt::from(1) << w;
                let norm = |x: BigInt| {
                    if signed && x >= (&m >> 1u32) {
                        x - &m
                    } else if !signed && x < BigInt::from(0) {
                        x + &m
                    } else {
                        x
                    }
                };
                let (a, b) = if self.rng.chance(60) {
                    // Wide: usually holds.
                    if signed {
                        (
                            -(&m >> 1u32),
                            (&m >> 1u32) - 1u32 - BigInt::from(self.rng.below(2)),
                        )
                    } else {
                        (BigInt::from(self.rng.below(2)).min(&m - 1u32), &m - 1u32)
                    }
                } else {
                    let a = interesting(self.rng, w);
                    let b = interesting(self.rng, w);
                    (norm(a), norm(b))
                };
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                format!("range.{}({lo}, {hi})", if signed { "s" } else { "u" })
            }
            T::P => {
                let choices: &[&str] = if param {
                    &[
                        "noalias", "noalias", "noalias", "readonly", "nonnull", "align",
                    ]
                } else {
                    &["nonnull", "align"]
                };
                match self.rng.pick(choices) {
                    "align" => format!("align({})", self.rng.pick(&[1, 1, 2, 4, 8, 32])),
                    f => f.to_owned(),
                }
            }
            T::B(_) | T::V(_) | T::F(_) => return String::new(),
        };
        format!(" [{f} {trust}]")
    }

    fn values(&self, t: T) -> Vec<String> {
        self.scope
            .iter()
            .filter(|(_, u)| *u == t)
            .map(|(n, _)| n.clone())
            .collect()
    }

    fn int_type(&mut self) -> T {
        T::I(self.rng.width(WIDTHS))
    }

    fn size_of(&self, t: T) -> u64 {
        match t {
            T::I(w) | T::B(w) | T::F(w) => u64::from(w / 8),
            T::P => u64::from(self.ptr_size / 8),
            T::V(_) => unreachable!("aggregates are not memory types here"),
        }
    }

    /// An operand of type `t`: usually an existing value, otherwise a new one.
    fn operand(&mut self, t: T) -> String {
        if self.rng.below(1500) == 0 {
            return format!("?h{}: {t}", self.rng.below(3));
        }
        let vs = self.values(t);
        if !vs.is_empty() && self.rng.chance(75) {
            let i = self.rng.below(vs.len() as u64) as usize;
            return format!("%{}", vs[i]);
        }
        let n = match t {
            T::I(w) => self.konst(w),
            T::P => {
                if !self.mems.is_empty() && self.rng.chance(70) {
                    let i = self.rng.below(self.mems.len() as u64) as usize;
                    return format!("%{}", self.mems[i].name);
                }
                self.new_ptr()
            }
            T::B(w) => {
                let (p, a) = self.access(u64::from(w / 8), false);
                self.def(t, &format!("mem.load {p}, align {a}"))
            }
            T::F(w) => self.fconst(w),
            T::V(i) => self.build(i),
        };
        format!("%{n}")
    }

    /// A float constant, biased toward the edge cases; sometimes the bits of an interesting
    /// integer.
    fn fconst(&mut self, w: u32) -> String {
        if self.rng.chance(15) {
            let n = interesting(self.rng, w);
            let i = self.def(T::I(w), &format!("int.const {n}"));
            return self.def(T::F(w), &format!("float.from_bits %{i}"));
        }
        let lit = float_lit(self.rng);
        self.def(T::F(w), &format!("float.const {lit}"))
    }

    /// One float op.
    fn float_op(&mut self) {
        let w = self.rng.pick(&[32, 64, 64]);
        let t = T::F(w);
        match self.rng.below(24) {
            0..=4 => {
                let op = self.rng.pick(&["add", "sub", "mul", "div", "copysign"]);
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(t, &format!("float.{op} {a}, {b}"));
            }
            5..=6 => {
                let op = self.rng.pick(&["neg", "abs", "sqrt"]);
                let a = self.operand(t);
                self.def(t, &format!("float.{op} {a}"));
            }
            7 => {
                let (a, b, c) = (self.operand(t), self.operand(t), self.operand(t));
                self.def(t, &format!("float.fma {a}, {b}, {c}"));
            }
            8..=10 => {
                let p = self.rng.pick(&[
                    "oeq", "one", "olt", "ole", "ogt", "oge", "ord", "ueq", "une", "ult", "ule",
                    "ugt", "uge", "uno",
                ]);
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(T::I(1), &format!("float.cmp.{p} {a}, {b}"));
            }
            11..=12 => {
                if self.rng.chance(50) {
                    let a = self.operand(T::F(32));
                    self.def(T::F(64), &format!("float.ext {a}"));
                } else {
                    let a = self.operand(T::F(64));
                    self.def(T::F(32), &format!("float.trunc {a}"));
                }
            }
            13..=15 => {
                let iw = self.rng.width(WIDTHS);
                let s = self.rng.pick(&["s", "u"]);
                let e = self.rng.pick(&["sat", "sat", "trap", "ub"]);
                let a = self.operand(t);
                self.def(T::I(iw), &format!("float.to_int.{s}.{e} {a}"));
            }
            16..=17 => {
                let iw = self.rng.width(WIDTHS);
                let s = self.rng.pick(&["s", "u"]);
                let a = self.operand(T::I(iw));
                self.def(t, &format!("int.to_float.{s} {a}"));
            }
            18 => {
                let a = self.operand(T::I(w));
                self.def(t, &format!("float.from_bits {a}"));
            }
            19 => {
                let a = self.operand(t);
                self.def(T::I(w), &format!("float.to_bits {a}"));
            }
            20 => {
                let c = self.operand(T::I(1));
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(t, &format!("select {c}, {a}, {b}"));
            }
            21 => match self.rng.below(3) {
                0 => {
                    self.def(t, "poison");
                }
                1 => {
                    let a = self.operand(t);
                    self.def(t, &format!("freeze {a}"));
                }
                _ => {
                    let a = self.operand(t);
                    self.def(t, &format!("copy {a}"));
                }
            },
            _ => {
                self.fconst(w);
            }
        }
    }

    fn konst(&mut self, w: u32) -> String {
        let n = interesting(self.rng, w);
        self.def(T::I(w), &format!("int.const {n}"))
    }

    /// A constant of width `w` in `lo..=hi`, wrapped to the width.
    fn small(&mut self, w: u32, lo: i64, hi: i64) -> String {
        let n = lo + self.rng.below((hi - lo + 1) as u64) as i64;
        let n = if w < 64 {
            i128::from(n).rem_euclid(1i128 << w).to_string()
        } else {
            n.to_string()
        };
        let name = self.fresh();
        self.op(
            &[(name.clone(), T::I(w), String::new())],
            &format!("int.const {n}"),
        );
        format!("%{name}")
    }

    fn align(&mut self) -> u64 {
        self.rng.pick(&[1, 1, 2, 4, 4, 8, 8, 16])
    }

    /// A new allocation (or, rarely, null).
    fn new_ptr(&mut self) -> String {
        let align = self.align();
        match self.rng.below(10) {
            0 => self.def(T::P, "ptr.null"),
            1..=3 => {
                let family = self.rng.pick(&["c.malloc", "c.malloc", "cpp.new"]);
                let fail = self.rng.pick(&["null", "trap"]);
                let size = self.rng.pick(&[0, 4, 8, 8, 16, 24, 32]);
                let n = self.small(self.addr, size, size);
                let name = self.def(
                    T::P,
                    &format!("mem.alloc.{fail} {family} {n}, align {align}"),
                );
                self.mems.push(Mem {
                    name: name.clone(),
                    size: size as u64,
                    align,
                    family: Some(family),
                    agg: None,
                    constant: false,
                });
                name
            }
            _ => {
                let size = self.rng.pick(&[0, 1, 4, 8, 8, 16, 16, 24, 32, 64]);
                let name = self.def(T::P, &format!("mem.stack {size}, align {align}"));
                self.mems.push(Mem {
                    name: name.clone(),
                    size,
                    align,
                    family: None,
                    agg: None,
                    constant: false,
                });
                name
            }
        }
    }

    /// A pointer to access `size` bytes through, and the alignment to access with: usually a
    /// valid, aligned offset into an allocation in scope.
    fn access(&mut self, size: u64, write: bool) -> (String, u64) {
        // Writes to `const` globals are UB: rarely aim them there.
        let allow_const = !write || self.rng.chance(10);
        let fits: Vec<Mem> = self
            .mems
            .iter()
            .filter(|m| m.size >= size && (allow_const || !m.constant))
            .cloned()
            .collect();
        if fits.is_empty() || self.rng.chance(12) {
            if self.rng.chance(40) {
                // A fresh allocation that fits.
                let align = self.rng.pick(&[1, 4, 8, 16]);
                let total = size + self.rng.pick(&[0, 0, 8]);
                let name = self.def(T::P, &format!("mem.stack {total}, align {align}"));
                self.mems.push(Mem {
                    name: name.clone(),
                    size: total,
                    align,
                    family: None,
                    agg: None,
                    constant: false,
                });
                return (format!("%{name}"), align.min(floor_pow2(size)));
            }
            let p = self.operand(T::P);
            return (p, self.align());
        }
        let m = fits[self.rng.below(fits.len() as u64) as usize].clone();
        // Usually the largest alignment both the allocation and the access allow; sometimes a
        // smaller one, sometimes one too large.
        let max = m.align.min(floor_pow2(size));
        let smaller: Vec<u64> = [1, 2, 4, 8, 16].into_iter().filter(|&a| a <= max).collect();
        let align = if self.rng.chance(60) {
            max
        } else {
            self.rng.pick(&smaller)
        };
        let align = if self.rng.chance(6) { align * 2 } else { align };
        let slots = (m.size - size) / align;
        let mut off = self.rng.below(slots + 1) * align;
        if self.rng.chance(8) {
            off = m.size - size + self.rng.pick(&[1, align, 8]);
        }
        if off == 0 {
            return (format!("%{}", m.name), align);
        }
        let n = self.small(self.addr, off as i64, off as i64);
        let p = self.def(T::P, &format!("ptr.offset.inbounds %{}, {n}", m.name));
        (format!("%{p}"), align)
    }

    fn mem_type(&mut self) -> T {
        if !self.rng.1 && self.rng.chance(12) {
            return T::F(self.rng.pick(&[32, 64]));
        }
        match self.rng.below(10) {
            0..=4 => T::I(self.rng.width(&[8, 16, 32, 32, 64, 64, 128])),
            5..=7 => T::P,
            _ => T::B(self.rng.pick(&[8, 32, 64])),
        }
    }

    /// One random op (possibly with regions).
    fn stmt(&mut self) {
        self.ops_left = self.ops_left.saturating_sub(1);
        if !self.rng.1 && self.rng.chance(14) {
            return self.float_op();
        }
        if !self.mfir && self.depth < 3 && self.rng.chance(4) {
            return self.try_op();
        }
        let blocks = !self.mfir && num_vtys() > 0;
        match self.rng.below(if blocks { 138 } else { 124 }) {
            118..=120 => self.store_pair(),
            121..=123 => self.copies(),
            124..=127 => self.overflow_op(),
            128..=130 => self.agg_op(),
            131..=132 => self.union_op(),
            133..=135 => self.slice_op(),
            136..=137 => self.agg_mem_op(),
            100..=101 => self.layout_query(),
            102..=104 => self.stack_of(),
            105..=107 => self.field_addr(),
            108..=109 => self.elem_addr(),
            110 => self.copy(),
            111..=112 => self.global_addr(),
            113..=114 => self.func_addr(),
            115..=116 => self.indirect_call(),
            117 => self.table_dispatch(),
            0..=3 => {
                let w = self.rng.width(WIDTHS);
                self.konst(w);
            }
            4..=15 => {
                let t = self.int_type();
                let op = self.rng.pick(&["add", "sub", "mul"]);
                let m = self.rng.pick(&[
                    "wrap", "wrap", "nsw", "nuw", "nsw.nuw", "s.sat", "u.sat", "s.trap", "u.trap",
                    "s.ub", "u.ub",
                ]);
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(t, &format!("int.{op}.{m} {a}, {b}"));
            }
            16..=19 => {
                let t = self.int_type();
                let op = self.rng.pick(&["and", "or", "xor"]);
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(t, &format!("int.{op} {a}, {b}"));
            }
            20..=25 => {
                let t = self.int_type();
                let T::I(w) = t else { unreachable!() };
                let op = self.rng.pick(&["div.s", "div.u", "rem.s", "rem.u"]);
                let m = if op.ends_with(".u") {
                    self.rng.pick(&["ub", "trap", "total"]).to_owned()
                } else {
                    let z = self.rng.pick(&["ub", "trap", "total"]);
                    let o = self.rng.pick(&["ub", "trap", "wrap"]);
                    match (z, o) {
                        ("ub", "ub") | ("trap", "trap") | ("total", "wrap") => z.to_owned(),
                        _ => format!("{z}.{o}"),
                    }
                };
                let a = self.operand(t);
                let b = if self.rng.chance(30) {
                    self.small(w, -1, 1)
                } else {
                    self.operand(t)
                };
                self.def(t, &format!("int.{op}.{m} {a}, {b}"));
            }
            26..=31 => {
                let t = self.int_type();
                let T::I(w) = t else { unreachable!() };
                let op = self.rng.pick(&["shl", "shr.u", "shr.s"]);
                let e = self.rng.pick(&["ub", "trap", "mask", "total"]);
                let a = self.operand(t);
                let n = if self.rng.chance(75) {
                    self.small(w, 0, i64::from(w.min(200)) + 2)
                } else {
                    self.operand(t)
                };
                self.def(t, &format!("int.{op}.{e} {a}, {n}"));
            }
            32..=36 => {
                let t = self.int_type();
                let p = self.rng.pick(&[
                    "eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge",
                ]);
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(T::I(1), &format!("int.cmp.{p} {a}, {b}"));
            }
            37..=38 => {
                let t = if self.rng.chance(20) {
                    T::P
                } else {
                    self.int_type()
                };
                let t = if t == T::P { self.int_type() } else { t };
                let c = self.operand(T::I(1));
                let (a, b) = (self.operand(t), self.operand(t));
                self.def(t, &format!("select {c}, {a}, {b}"));
            }
            39..=42 => {
                let (mut v, mut w) = (self.rng.width(WIDTHS), self.rng.width(WIDTHS));
                if v == w {
                    if w < 64 || !self.rng.1 {
                        w += 1;
                    } else {
                        v -= 1;
                    }
                }
                if v > w {
                    std::mem::swap(&mut v, &mut w);
                }
                if self.rng.chance(50) {
                    let op = self.rng.pick(&["zext", "sext"]);
                    let a = self.operand(T::I(v));
                    self.def(T::I(w), &format!("int.{op} {a}"));
                } else {
                    let m = self.rng.pick(&["wrap", "nsw", "nuw"]);
                    let a = self.operand(T::I(w));
                    self.def(T::I(v), &format!("int.trunc.{m} {a}"));
                }
            }
            43..=45 => {
                let t = self.int_type();
                match self.rng.below(3) {
                    0 => {
                        self.def(t, "poison");
                    }
                    1 => {
                        let a = self.operand(t);
                        self.def(t, &format!("freeze {a}"));
                    }
                    _ => {
                        let t = if self.rng.chance(30) { T::P } else { t };
                        let a = self.operand(t);
                        self.def(t, &format!("copy {a}"));
                    }
                }
            }
            46..=49 => {
                self.new_ptr();
            }
            50..=58 => {
                let t = self.mem_type();
                let (p, a) = self.access(self.size_of(t), false);
                self.def(t, &format!("mem.load {p}, align {a}"));
            }
            59..=66 => {
                let t = self.mem_type();
                let v = self.operand(t);
                let (p, a) = self.access(self.size_of(t), true);
                self.op(&[], &format!("mem.store {t} {v}, {p}, align {a}"));
            }
            67..=69 => {
                let p = self.operand(T::P);
                let n = if self.rng.chance(80) {
                    self.small(self.addr, -8, 40)
                } else {
                    self.operand(T::I(self.addr))
                };
                let m = self.rng.pick(&["inbounds", "inbounds", "wrap"]);
                self.def(T::P, &format!("ptr.offset.{m} {p}, {n}"));
            }
            70..=73 => {
                // Sometimes the end of an allocation: where the next one may start.
                let p = match self.mems.len() {
                    n if n > 0 && self.rng.chance(35) => {
                        let m = self.mems[self.rng.below(n as u64) as usize].clone();
                        let size = self.small(self.addr, m.size as i64, m.size as i64);
                        format!(
                            "%{}",
                            self.def(T::P, &format!("ptr.offset.wrap %{}, {size}", m.name))
                        )
                    }
                    _ => self.operand(T::P),
                };
                if self.rng.chance(30) {
                    self.def(T::I(self.addr), &format!("ptr.addr {p}"));
                } else {
                    let a = self.def(T::I(self.addr), &format!("ptr.expose {p}"));
                    self.exposed.push(a);
                }
            }
            74..=78 => self.address_op(),
            79..=80 => {
                let p = self
                    .rng
                    .pick(&["eq", "ne", "eq", "ne", "ult", "ule", "ugt", "uge"]);
                let (a, b) = (self.operand(T::P), self.operand(T::P));
                self.def(T::I(1), &format!("ptr.cmp.{p} {a}, {b}"));
            }
            81..=82 => {
                let heap: Vec<Mem> = self
                    .mems
                    .iter()
                    .filter(|m| m.family.is_some())
                    .cloned()
                    .collect();
                if heap.is_empty() && self.rng.chance(70) {
                    return;
                }
                let (p, family) = if !heap.is_empty() && self.rng.chance(85) {
                    let m = heap[self.rng.below(heap.len() as u64) as usize].clone();
                    let family = if self.rng.chance(85) {
                        m.family.unwrap()
                    } else {
                        "cpp.new"
                    };
                    (format!("%{}", m.name), family)
                } else {
                    (self.operand(T::P), "c.malloc")
                };
                self.op(&[], &format!("mem.free {family} {p}"));
            }
            83..=85 if self.depth < 3 => self.if_op(),
            86..=88 if self.depth < 3 => self.loop_op(),
            89..=93 if self.depth < 3 => self.blocks_op(),
            94..=98 if self.func + 1 < self.sigs.len() => self.call_op(),
            _ => {
                let w = self.rng.width(WIDTHS);
                self.konst(w);
            }
        }
    }

    /// Two allocations given addresses one after the other, both exposed, and a pointer from
    /// the address where the first ends and the second starts: it may belong to either.
    fn boundary(&mut self) {
        let size = self.rng.pick(&[0, 4, 8, 16]);
        let align = self.rng.pick(&[1, 4, 8]);
        let a = self.def(T::P, &format!("mem.stack {size}, align {align}"));
        let b = self.def(T::P, &format!("mem.stack 8, align {align}"));
        let ea = self.def(T::I(self.addr), &format!("ptr.expose %{a}"));
        let eb = self.def(T::I(self.addr), &format!("ptr.expose %{b}"));
        self.exposed.extend([ea.clone(), eb]);
        let d = self.small(self.addr, size, size);
        let x = self.def(T::I(self.addr), &format!("int.add.wrap %{ea}, {d}"));
        let p = self.def(T::P, &format!("ptr.from_exposed %{x}"));
        for (name, size) in [(a, size as u64), (b, 8), (p, 4)] {
            self.mems.push(Mem {
                name,
                size,
                align,
                family: None,
                agg: None,
                constant: false,
            });
        }
    }

    /// `ptr.from_exposed` or `ptr.with_addr` of an address near an observed one.
    fn address_op(&mut self) {
        if self.rng.chance(25) {
            return self.boundary();
        }
        let aw = T::I(self.addr);
        let a = if !self.exposed.is_empty() && self.rng.chance(80) {
            let i = self.rng.below(self.exposed.len() as u64) as usize;
            format!("%{}", self.exposed[i])
        } else {
            self.operand(aw)
        };
        let a = if self.rng.chance(40) {
            let d = self.small(self.addr, -4, 12);
            format!("%{}", self.def(aw, &format!("int.add.wrap {a}, {d}")))
        } else {
            a
        };
        if self.rng.chance(75) {
            let p = self.def(T::P, &format!("ptr.from_exposed {a}"));
            // Treat it as a small allocation: accesses through it are often valid.
            if self.rng.chance(50) {
                self.mems.push(Mem {
                    name: p,
                    size: 4,
                    align: 1,
                    family: None,
                    agg: None,
                    constant: false,
                });
            }
        } else {
            let p = self.operand(T::P);
            self.def(T::P, &format!("ptr.with_addr {p}, {a}"));
        }
    }

    /// Ops, then a terminator chosen by `end`, inside a region; the region's values are hidden
    /// afterwards.
    fn region(&mut self, n: u32, end: impl FnOnce(&mut Self)) {
        let mark = self.mark();
        self.depth += 1;
        for _ in 0..n {
            if self.ops_left == 0 {
                break;
            }
            self.stmt();
        }
        end(self);
        self.depth -= 1;
        self.restore(mark);
    }

    fn close(&mut self) {
        self.indent();
        self.out.push('}');
    }

    /// `%r..: T.. = ` for an op with regions.
    fn results_prefix(&mut self, names: &[(String, T)]) {
        self.indent();
        if !names.is_empty() {
            let rs: Vec<String> = names.iter().map(|(n, t)| format!("%{n}: {t}")).collect();
            write!(self.out, "{} = ", rs.join(", ")).unwrap();
        }
    }

    fn if_op(&mut self) {
        let c = self.operand(T::I(1));
        let rets: Vec<T> = (0..self.rng.below(3)).map(|_| self.state_type()).collect();
        let names: Vec<(String, T)> = rets.iter().map(|t| (self.fresh(), *t)).collect();
        self.results_prefix(&names);
        let loc = self.loc();
        write!(self.out, "cf.if {c}{loc} {{").unwrap();
        self.newline();
        for branch in 0..2 {
            let n = self.rng.below(5) as u32;
            let rets = rets.clone();
            self.region(n, |g| {
                // A branch without results may leave the enclosing loop, or jump to a block of
                // the enclosing cf.blocks, instead.
                if g.rng.chance(5) {
                    g.throw_term();
                } else if rets.is_empty() && !g.blocks.is_empty() && g.rng.chance(25) {
                    g.jump();
                } else if rets.is_empty() && !g.loops.is_empty() && g.rng.chance(30) {
                    g.loop_exit();
                } else if !rets.is_empty() || g.rng.chance(50) {
                    let vs: Vec<String> = rets.iter().map(|t| g.operand(*t)).collect();
                    g.op(&[], format!("cf.yield {}", vs.join(", ")).trim_end());
                }
            });
            self.close();
            if branch == 0 {
                self.out.push_str(" else {");
                self.newline();
            }
        }
        self.newline();
        self.scope.extend(names);
    }

    fn state_type(&mut self) -> T {
        if !self.mfir && num_vtys() > 0 && self.rng.chance(15) {
            return T::V(self.rng.below(num_vtys() as u64) as u8);
        }
        if !self.rng.1 && self.rng.chance(12) {
            return T::F(self.rng.pick(&[32, 64]));
        }
        if self.rng.chance(25) {
            T::P
        } else {
            T::I(self.rng.width(&[1, 8, 32, 64]))
        }
    }

    /// `cf.break` or `cf.continue` of the innermost loop.
    fn loop_exit(&mut self) {
        let (params, results) = self.loops.last().unwrap().clone();
        let (kw, ts) = if self.rng.chance(60) {
            ("cf.break", results)
        } else {
            ("cf.continue", params)
        };
        let vs: Vec<String> = ts.iter().map(|t| self.operand(*t)).collect();
        self.op(&[], format!("{kw} {}", vs.join(", ")).trim_end());
    }

    /// A counted loop: `%i` counts up from 0 to a bound; other state is random.
    fn loop_op(&mut self) {
        let bound = if self.rng.chance(85) {
            self.small(32, 0, 5)
        } else {
            self.operand(T::I(32))
        };
        let zero = self.small(32, 0, 0);
        let one = self.small(32, 1, 1);
        let extra: Vec<T> = (0..self.rng.below(3)).map(|_| self.state_type()).collect();
        let inits: Vec<String> = extra.iter().map(|t| self.operand(*t)).collect();
        let i = self.fresh();
        let state: Vec<(String, T)> = std::iter::once((i.clone(), T::I(32)))
            .chain(extra.iter().map(|t| (self.fresh(), *t)))
            .collect();
        let names: Vec<(String, T)> = extra.iter().map(|t| (self.fresh(), *t)).collect();
        self.results_prefix(&names);
        let progress = if self.rng.chance(40) { " progress" } else { "" };
        let iter: Vec<String> = state
            .iter()
            .zip(std::iter::once(zero).chain(inits))
            .map(|((n, t), init)| format!("%{n}: {t} = {init}"))
            .collect();
        let loc = self.loc();
        write!(
            self.out,
            "cf.loop{progress} iter({}){loc} {{",
            iter.join(", ")
        )
        .unwrap();
        self.newline();
        self.loops
            .push((state.iter().map(|(_, t)| *t).collect(), extra.clone()));
        let mark = self.mark();
        self.scope.extend(state.iter().cloned());
        self.depth += 1;
        // Leave when the counter reaches the bound.
        let done = self.def(T::I(1), &format!("int.cmp.sge %{i}, {bound}"));
        self.indent();
        let loc = self.loc();
        write!(self.out, "cf.if %{done}{loc} {{").unwrap();
        self.newline();
        self.depth += 1;
        let branch = self.mark();
        let outs: Vec<String> = extra.iter().map(|t| self.operand(*t)).collect();
        self.op(&[], format!("cf.break {}", outs.join(", ")).trim_end());
        self.restore(branch);
        self.depth -= 1;
        self.close();
        self.newline();
        self.depth -= 1;
        let n = 1 + self.rng.below(6) as u32;
        self.region(n, |g| {
            let next = g.def(T::I(32), &format!("int.add.wrap %{i}, {one}"));
            let mut vs = vec![format!("%{next}")];
            for t in &extra {
                vs.push(g.operand(*t));
            }
            g.op(&[], &format!("cf.continue {}", vs.join(", ")));
        });
        self.loops.pop();
        self.restore(mark);
        self.close();
        self.newline();
        self.scope.extend(names);
    }

    /// The arguments for a jump to block `i` of the innermost `cf.blocks`.
    fn jump_args(&mut self, i: usize) -> String {
        let b = self.blocks.last().unwrap();
        let (label, params) = b.labels[i].clone();
        let exit = i + 1 == b.labels.len();
        let next = b.next.clone();
        let mut args = Vec::new();
        for (j, t) in params.iter().enumerate() {
            args.push(if j == 0 && !exit && i > 0 {
                format!("%{next}")
            } else {
                self.operand(*t)
            });
        }
        if args.is_empty() {
            format!("^{label}")
        } else {
            format!("^{label}({})", args.join(", "))
        }
    }

    /// A target block for a jump from block `from`: usually not the entry (which has no
    /// counter), often the next one (C's fall-through).
    fn target(&mut self, from: usize) -> usize {
        let n = self.blocks.last().unwrap().labels.len();
        if from + 1 < n && self.rng.chance(35) {
            from + 1
        } else if self.rng.chance(3) {
            0
        } else {
            1 + self.rng.below((n - 1) as u64) as usize
        }
    }

    /// A jump to a block of the innermost `cf.blocks`, from inside a block or a region nested
    /// in one.
    fn jump(&mut self) {
        let n = self.blocks.last().unwrap().labels.len();
        let to = 1 + self.rng.below((n - 1) as u64) as usize;
        let t = self.jump_args(to);
        self.op(&[], &format!("cf.br {t}"));
    }

    /// `cf.switch` on a random integer: distinct keys modulo `2^w`, written signed or unsigned.
    fn switch(&mut self, from: usize) {
        let w = self.rng.width(&[1, 8, 8, 32, 32, 64, 7, 65, 128]);
        let v = self.operand(T::I(w));
        let d = self.target(from);
        let d = self.jump_args(d);
        let modulus = BigInt::from(1) << w;
        let mut seen: Vec<BigInt> = Vec::new();
        let mut cases = Vec::new();
        for _ in 0..self.rng.below(5) {
            let k = if self.rng.chance(60) {
                BigInt::from(self.rng.below(6) as i64 - 1)
            } else {
                interesting(self.rng, w)
            };
            let norm = ((&k % &modulus) + &modulus) % &modulus;
            if seen.contains(&norm) || !(fits(&k, w)) {
                continue;
            }
            seen.push(norm);
            let to = self.target(from);
            let t = self.jump_args(to);
            cases.push(format!("{k}: {t}"));
        }
        self.op(
            &[],
            &format!("cf.switch {v}, default {d}, [{}]", cases.join(", ")),
        );
    }

    /// `cf.blocks`: an entry block, blocks with a counter parameter and maybe more, and an exit
    /// block that yields the results.
    fn blocks_op(&mut self) {
        let rets: Vec<T> = (0..self.rng.below(3)).map(|_| self.state_type()).collect();
        let limit = self.small(32, 0, 4);
        let one = self.small(32, 1, 1);
        let zero = self.small(32, 0, 0);
        let n = 2 + self.rng.below(4) as usize;
        let mut labels = vec![("entry".to_owned(), Vec::new())];
        for k in 1..n {
            let mut ps = vec![T::I(32)];
            ps.extend((0..self.rng.below(3)).map(|_| self.state_type()));
            labels.push((format!("b{k}"), ps));
        }
        labels.push(("exit".to_owned(), rets.clone()));
        let names: Vec<(String, T)> = rets.iter().map(|t| (self.fresh(), *t)).collect();
        self.results_prefix(&names);
        let progress = if self.rng.chance(30) { " progress" } else { "" };
        let loc = self.loc();
        write!(self.out, "cf.blocks{progress}{loc} {{").unwrap();
        self.newline();
        let handler = (self.mfir && self.rng.chance(40)).then(|| "h".to_owned());
        let first = zero.trim_start_matches('%').to_owned();
        self.blocks.push(Blocks {
            labels: labels.clone(),
            next: first.clone(),
            handler: handler.clone(),
        });
        let mark = self.mark();
        let exit = labels.len() - 1;
        for (k, (label, params)) in labels.iter().enumerate() {
            self.restore(mark);
            let ps: Vec<(String, T)> = params.iter().map(|t| (self.fresh(), *t)).collect();
            self.indent();
            if ps.is_empty() {
                write!(self.out, "^{label}:").unwrap();
            } else {
                let items: Vec<String> = ps.iter().map(|(n, t)| format!("%{n}: {t}")).collect();
                write!(self.out, "^{label}({}):", items.join(", ")).unwrap();
            }
            self.newline();
            self.depth += 1;
            self.scope.extend(ps.iter().cloned());
            if k == exit {
                let vs: Vec<String> = ps.iter().map(|(n, _)| format!("%{n}")).collect();
                self.op(&[], format!("cf.yield {}", vs.join(", ")).trim_end());
                self.depth -= 1;
                continue;
            }
            if k > 0 {
                // Count the jump; at the limit, usually leave.
                let c = &ps[0].0;
                let next = self.def(T::I(32), &format!("int.add.wrap %{c}, {one}"));
                self.blocks.last_mut().unwrap().next = next;
                if self.rng.chance(95) {
                    let stop = self.def(T::I(1), &format!("int.cmp.sge %{c}, {limit}"));
                    self.indent();
                    let loc = self.loc();
                    write!(self.out, "cf.if %{stop}{loc} {{").unwrap();
                    self.newline();
                    self.depth += 1;
                    let inner = self.mark();
                    let t = self.jump_args(exit);
                    self.op(&[], &format!("cf.br {t}"));
                    self.restore(inner);
                    self.depth -= 1;
                    self.close();
                    self.newline();
                }
            }
            for _ in 0..self.rng.below(5) {
                if self.ops_left == 0 {
                    break;
                }
                self.stmt();
            }
            match self.rng.below(100) {
                0..=29 => {
                    let to = self.target(k);
                    let t = self.jump_args(to);
                    self.op(&[], &format!("cf.br {t}"));
                }
                30..=59 => {
                    let c = self.operand(T::I(1));
                    let (a, b) = (self.target(k), self.target(k));
                    let (a, b) = (self.jump_args(a), self.jump_args(b));
                    self.op(&[], &format!("cf.cond_br {c}, {a}, {b}"));
                }
                60..=79 => self.switch(k),
                80..=89 => {
                    let vs: Vec<String> = rets.iter().map(|t| self.operand(*t)).collect();
                    self.op(&[], format!("cf.yield {}", vs.join(", ")).trim_end());
                }
                90..=94 if !self.loops.is_empty() => self.loop_exit(),
                _ if self.rng.chance(25) => self.throw_term(),
                _ => {
                    let rets = self.sigs[self.func].rets.clone();
                    let vs: Vec<String> = rets.iter().map(|t| self.operand(*t)).collect();
                    self.op(&[], format!("func.ret {}", vs.join(", ")).trim_end());
                }
            }
            self.depth -= 1;
        }
        if let Some(h) = handler {
            // The handler block: it gets what calls naming it throw. Its jumps pass the counter
            // the entry's do (the blocks' own counters are out of scope here).
            self.restore(mark);
            self.blocks.last_mut().unwrap().next = first;
            let e = self.fresh();
            self.indent();
            write!(self.out, "^{h}(%{e}: ptr):").unwrap();
            self.newline();
            self.depth += 1;
            self.catch_scope(&e);
            for _ in 0..self.rng.below(3) {
                if self.ops_left == 0 {
                    break;
                }
                self.stmt();
            }
            match self.rng.below(10) {
                0..=5 => {
                    let vs: Vec<String> = rets.iter().map(|t| self.operand(*t)).collect();
                    self.op(&[], format!("cf.yield {}", vs.join(", ")).trim_end());
                }
                6..=7 => self.op(&[], &format!("exn.throw %{e}")),
                _ => {
                    let rets = self.sigs[self.func].rets.clone();
                    let vs: Vec<String> = rets.iter().map(|t| self.operand(*t)).collect();
                    self.op(&[], format!("func.ret {}", vs.join(", ")).trim_end());
                }
            }
            self.depth -= 1;
        }
        self.restore(mark);
        self.blocks.pop();
        self.close();
        self.newline();
        self.scope.extend(names);
    }

    /// The handler of the innermost `cf.blocks`, if calls here may name it.
    fn handler(&mut self) -> Option<String> {
        let h = self.blocks.last().and_then(|b| b.handler.clone())?;
        self.rng.chance(60).then_some(h)
    }

    /// What a throw throws: usually a fresh heap object holding an `i32`, which handlers load;
    /// sometimes a global, null, or any pointer.
    fn exn_value(&mut self) -> String {
        match self.rng.below(10) {
            0..=5 => {
                let n = self.small(self.addr, 8, 8);
                let p = self.def(T::P, &format!("mem.alloc.trap c.malloc {n}, align 8"));
                let v = self.operand(T::I(32));
                self.op(&[], &format!("mem.store i32 {v}, %{p}, align 8"));
                format!("%{p}")
            }
            6 if !self.globals.is_empty() => {
                let g = self.globals[self.rng.below(self.globals.len() as u64) as usize]
                    .name
                    .clone();
                format!("%{}", self.def(T::P, &format!("mem.global @{g}")))
            }
            7 => format!("%{}", self.def(T::P, "ptr.null")),
            _ => self.operand(T::P),
        }
    }

    /// `exn.throw`, as a region's terminator.
    fn throw_term(&mut self) {
        let v = self.exn_value();
        self.op(&[], &format!("exn.throw {v}"));
    }

    /// The exception `%e` in a handler: a value, and usually a heap object to load from (and
    /// sometimes free) as `exn_value` makes them.
    fn catch_scope(&mut self, e: &str) {
        self.scope.push((e.to_owned(), T::P));
        if self.rng.chance(70) {
            self.mems.push(Mem {
                name: e.to_owned(),
                size: 8,
                align: 8,
                family: Some("c.malloc"),
                agg: None,
                constant: false,
            });
            if self.rng.chance(60) {
                self.def(T::I(32), &format!("mem.load %{e}, align 8"));
            }
        }
    }

    /// How a `cf.try` region ends: `cf.yield` of its results, a throw, a loop exit, or (without
    /// results) falling off its end.
    fn try_end(&mut self, rets: &[T]) {
        match self.rng.below(20) {
            0..=1 => self.throw_term(),
            2 if !self.loops.is_empty() && rets.is_empty() => self.loop_exit(),
            3..=5 if rets.is_empty() => {}
            _ => {
                let vs: Vec<String> = rets.iter().map(|t| self.operand(*t)).collect();
                self.op(&[], format!("cf.yield {}", vs.join(", ")).trim_end());
            }
        }
    }

    /// `cf.try { … } catch(%e: ptr) { … }` (HFIR). Jumps can't leave its regions, so the
    /// enclosing `cf.blocks` are out of reach inside.
    fn try_op(&mut self) {
        let rets: Vec<T> = (0..self.rng.below(3)).map(|_| self.state_type()).collect();
        let names: Vec<(String, T)> = rets.iter().map(|t| (self.fresh(), *t)).collect();
        self.results_prefix(&names);
        let loc = self.loc();
        write!(self.out, "cf.try{loc} {{").unwrap();
        self.newline();
        let blocks = std::mem::take(&mut self.blocks);
        let n = 1 + self.rng.below(6) as u32;
        self.region(n, |g| g.try_end(&rets));
        self.close();
        let e = self.fresh();
        write!(self.out, " catch(%{e}: ptr) {{").unwrap();
        self.newline();
        let mark = self.mark();
        self.depth += 1;
        self.catch_scope(&e);
        for _ in 0..self.rng.below(4) {
            if self.ops_left == 0 {
                break;
            }
            self.stmt();
        }
        if self.rng.chance(15) {
            self.op(&[], &format!("exn.throw %{e}"));
        } else {
            self.try_end(&rets);
        }
        self.depth -= 1;
        self.restore(mark);
        self.blocks = blocks;
        self.close();
        self.newline();
        self.scope.extend(names);
    }

    /// A value type for a field or element.
    fn field_type(&mut self) -> T {
        if !self.rng.1 && self.rng.chance(10) {
            return T::F(self.rng.pick(&[32, 64]));
        }
        match self.rng.below(12) {
            0..=1 => T::I(8),
            2 => T::I(16),
            3..=4 => T::I(32),
            5 => T::I(64),
            6 => T::I(self.rng.width(&[24, 128])),
            7..=9 => T::P,
            _ => T::B(self.rng.pick(&[8, 32])),
        }
    }

    fn agg_once(&mut self, depth: u32) -> Agg {
        match self.rng.below(10) {
            0..=4 if depth < 2 => {
                let p = self.rng.pick(&["C", "C", "C", "packed", "auto"]);
                let n = self.rng.pick(&[0, 1, 2, 2, 3, 3, 4]);
                let fs = (0..n)
                    .map(|_| {
                        if self.rng.chance(25) {
                            self.agg_once(depth + 1)
                        } else {
                            Agg::Scalar(self.field_type())
                        }
                    })
                    .collect();
                Agg::Struct(p, fs)
            }
            5..=7 if depth < 2 => {
                let n = self.rng.pick(&[0, 1, 2, 3, 4, 4]);
                let e = if self.rng.chance(25) {
                    self.agg_once(depth + 1)
                } else {
                    Agg::Scalar(self.field_type())
                };
                Agg::Array(n, Box::new(e))
            }
            _ => Agg::Scalar(self.field_type()),
        }
    }

    /// A struct, array, or value type of at most 160 bytes.
    fn agg(&mut self) -> Agg {
        loop {
            let a = self.agg_once(0);
            if self.layout.dims(&a).0 <= 160 {
                return a;
            }
        }
    }

    /// A struct with at least one field.
    fn struct_agg(&mut self) -> Agg {
        loop {
            let a = self.agg_once(0);
            if matches!(&a, Agg::Struct(_, fs) if !fs.is_empty()) && self.layout.dims(&a).0 <= 160 {
                return a;
            }
        }
    }

    /// `ty.size`, `ty.align`, or `ty.offset`.
    fn layout_query(&mut self) {
        let aw = T::I(self.addr);
        match self.rng.below(3) {
            0 => {
                let a = self.agg();
                self.def(aw, &format!("ty.size {a}"));
            }
            1 => {
                let a = self.agg();
                self.def(aw, &format!("ty.align {a}"));
            }
            _ => {
                let a = self.struct_agg();
                let Agg::Struct(_, fs) = &a else {
                    unreachable!()
                };
                let i = self.rng.below(fs.len() as u64);
                self.def(aw, &format!("ty.offset {a}, {i}"));
            }
        }
    }

    /// A typed stack slot.
    fn stack_of(&mut self) {
        let a = self.agg();
        let align = self.rng.pick(&[1, 1, 1, 2, 4, 8, 16]);
        let (size, natural) = self.layout.dims(&a);
        let name = self.def(T::P, &format!("mem.stack.of {a}, align {align}"));
        self.mems.push(Mem {
            name,
            size,
            align: align.max(natural),
            family: None,
            agg: Some(a),
            constant: false,
        });
    }

    /// A pointer to a field or element of a known allocation: track it, and sometimes load or
    /// store its value right away.
    fn sub_mem(&mut self, name: String, base: &Mem, off: u64, part: Agg, align: u64) {
        let size = self.layout.dims(&part).0;
        if off + size > base.size {
            return;
        }
        // The address is aligned to the base's alignment and to the offset's.
        let off_align = if off == 0 {
            base.align
        } else {
            1 << off.trailing_zeros().min(16)
        };
        let align = align.min(base.align).min(off_align).max(1);
        let m = Mem {
            name: name.clone(),
            size,
            align,
            family: None,
            agg: Some(part.clone()),
            constant: base.constant,
        };
        self.mems.push(m);
        if let Agg::Scalar(t) = part
            && self.rng.chance(50)
        {
            let a = align.min(floor_pow2(size));
            if self.rng.chance(50) && (!base.constant || self.rng.chance(5)) {
                let v = self.operand(t);
                self.op(&[], &format!("mem.store {t} {v}, %{name}, align {a}"));
            } else {
                self.def(t, &format!("mem.load %{name}, align {a}"));
            }
        }
    }

    /// Field `i` of the struct `a` at `p` (an operand): `ptr.field`, or in MFIR `ptr.offset` by
    /// `ty.offset`.
    fn field_ptr(&mut self, mode: &str, a: &Agg, p: &str, i: usize) -> String {
        if self.mfir {
            let o = self.def(T::I(self.addr), &format!("ty.offset {a}, {i}"));
            self.def(T::P, &format!("ptr.offset.{mode} {p}, %{o}"))
        } else {
            self.def(T::P, &format!("ptr.field.{mode} {a} {p}, {i}"))
        }
    }

    /// Element `idx` (an operand) of an array of `elem` at `p`: `ptr.index`, or in MFIR
    /// `ptr.offset` by the index times the stride.
    fn index_ptr(&mut self, mode: &str, elem: &Agg, p: &str, idx: &str) -> String {
        if self.mfir {
            let stride = self.layout.stride(elem) as i64;
            let s = self.small(self.addr, stride, stride);
            let ovf = if mode == "inbounds" { "nsw" } else { "wrap" };
            let n = self.def(T::I(self.addr), &format!("int.mul.{ovf} {idx}, {s}"));
            self.def(T::P, &format!("ptr.offset.{mode} {p}, %{n}"))
        } else {
            self.def(T::P, &format!("ptr.index.{mode} {elem} {p}, {idx}"))
        }
    }

    /// `ptr.field`: usually of a struct in a known allocation, with a valid index.
    fn field_addr(&mut self) {
        let mode = if self.rng.chance(80) {
            "inbounds"
        } else {
            "wrap"
        };
        let typed: Vec<Mem> = self
            .mems
            .iter()
            .filter(|m| matches!(&m.agg, Some(Agg::Struct(_, fs)) if !fs.is_empty()))
            .cloned()
            .collect();
        if !typed.is_empty() && self.rng.chance(80) {
            let m = typed[self.rng.below(typed.len() as u64) as usize].clone();
            let Some(a @ Agg::Struct(p, fs)) = &m.agg else {
                unreachable!()
            };
            let i = self.rng.below(fs.len() as u64) as usize;
            let name = self.field_ptr(mode, a, &format!("%{}", m.name), i);
            let (offs, _, _) = self.layout.place(p, fs);
            let align = if *p == "packed" {
                1
            } else {
                self.layout.dims(&fs[i]).1
            };
            self.sub_mem(name, &m, offs[i], fs[i].clone(), align);
        } else {
            // Another struct over whatever the pointer points at.
            let a = self.struct_agg();
            let Agg::Struct(_, fs) = &a else {
                unreachable!()
            };
            let i = self.rng.below(fs.len() as u64 + 1).min(fs.len() as u64 - 1);
            let p = self.operand(T::P);
            self.field_ptr(mode, &a, &p, i as usize);
        }
    }

    /// `ptr.index`: usually of an array in a known allocation, usually in range.
    fn elem_addr(&mut self) {
        let mode = if self.rng.chance(80) {
            "inbounds"
        } else {
            "wrap"
        };
        let typed: Vec<Mem> = self
            .mems
            .iter()
            .filter(|m| matches!(&m.agg, Some(Agg::Array(n, _)) if *n > 0))
            .cloned()
            .collect();
        let (base, elem, n) = if !typed.is_empty() && self.rng.chance(80) {
            let m = typed[self.rng.below(typed.len() as u64) as usize].clone();
            let Some(Agg::Array(n, e)) = m.agg.clone() else {
                unreachable!()
            };
            (Some(m), *e, n)
        } else {
            let e = if self.rng.chance(60) {
                Agg::Scalar(self.field_type())
            } else {
                self.agg()
            };
            (None, e, 4)
        };
        let i: i64 = match self.rng.below(10) {
            0 => -1,
            1 => n as i64,
            2 => n as i64 + 1,
            _ => self.rng.below(n) as i64,
        };
        let idx = if self.rng.chance(5) {
            self.operand(T::I(self.addr))
        } else if self.rng.chance(3) {
            // Large enough that the product overflows.
            let k = format!("%{}", self.konst(self.addr));
            k
        } else {
            self.small(self.addr, i, i)
        };
        let p = match &base {
            Some(m) => format!("%{}", m.name),
            None => self.operand(T::P),
        };
        let name = self.index_ptr(mode, &elem, &p, &idx);
        if let Some(m) = base
            && i >= 0
            && (i as u64) < n
        {
            let stride = self.layout.stride(&elem);
            let align = self.layout.dims(&elem).1;
            self.sub_mem(name, &m, i as u64 * stride, elem, align);
        }
    }

    /// Back-to-back accesses through one pointer, for dead store elimination and forwarding: a
    /// store, then a second store, a load, or both. The second access usually has the stored
    /// type, sometimes another of the same size (`bN` for `iN`, an integer for a pointer), and
    /// sometimes one of another size; it sometimes goes through another pointer. Values read back
    /// at the top of the function are usually returned.
    fn store_pair(&mut self) {
        let t = self.mem_type();
        let v = self.operand(t);
        let (p, a) = self.access(self.size_of(t), true);
        let t2 = match t {
            T::I(w) if self.rng.chance(25) => T::B(w),
            T::B(w) if self.rng.chance(25) => T::I(w),
            T::P if self.rng.chance(20) => T::I(self.ptr_size),
            _ if self.rng.chance(20) => self.mem_type(),
            _ => t,
        };
        let v2 = self.operand(t2);
        // Sometimes the second access goes through another pointer, which may alias.
        let (p2, a2) = if self.rng.chance(15) {
            self.access(self.size_of(t2), true)
        } else {
            (p.clone(), a)
        };
        let (store, load) = match self.rng.below(3) {
            0 => (true, false),
            1 => (false, true),
            _ => (true, true),
        };
        self.op(&[], &format!("mem.store {t} {v}, {p}, align {a}"));
        if store {
            self.op(&[], &format!("mem.store {t2} {v2}, {p2}, align {a2}"));
        }
        if load {
            let lt = if store || self.rng.chance(20) { t2 } else { t };
            let r = self.def(lt, &format!("mem.load {p2}, align {a2}"));
            if self.depth == 0 {
                self.watch.push((r, lt));
            }
        }
        // Read back what the first store wrote, if something else may have overwritten it.
        if store && (p2 != p || t2 != t) && self.rng.chance(60) {
            let r = self.def(t, &format!("mem.load {p}, align {a}"));
            if self.depth == 0 {
                self.watch.push((r, t));
            }
        }
    }

    /// A chain of copies, usually read at once, for copy propagation.
    fn copies(&mut self) {
        let t = if self.rng.chance(25) {
            T::P
        } else {
            self.int_type()
        };
        let mut x = self.operand(t);
        for _ in 0..=self.rng.below(3) {
            x = format!("%{}", self.def(t, &format!("copy {x}")));
        }
        if let (T::I(_), true) = (t, self.rng.chance(70)) {
            let y = self.operand(t);
            self.def(t, &format!("int.xor {x}, {y}"));
        }
    }

    /// `mem.copy` between two allocations that usually hold the type.
    fn copy(&mut self) {
        let a = self.agg();
        let size = self.layout.dims(&a).0;
        let (d, da) = self.access(size, true);
        let (s, sa) = self.access(size, false);
        let align = da.min(sa);
        self.op(&[], &format!("mem.copy {a} {d}, {s}, align {align}"));
    }

    /// `mem.global`, tracked like an allocation.
    fn global_addr(&mut self) {
        if self.globals.is_empty() {
            return self.stack_of();
        }
        let g = self.globals[self.rng.below(self.globals.len() as u64) as usize].clone();
        let name = self.def(T::P, &format!("mem.global @{}", g.name));
        let (size, natural) = self.layout.dims(&g.agg);
        // Sometimes write a `const` one anyway, through a byte.
        if g.constant && size > 0 && self.rng.chance(15) {
            let v = self.operand(T::I(8));
            self.op(&[], &format!("mem.store i8 {v}, %{name}, align 1"));
        }
        self.mems.push(Mem {
            name,
            size,
            align: g.align.max(natural),
            family: None,
            agg: Some(g.agg),
            constant: g.constant,
        });
    }

    /// `func.addr` of any function; sometimes its address goes through an integer and back.
    fn func_addr(&mut self) {
        let k = self.rng.below(self.sigs.len() as u64) as usize;
        let f = self.fn_name(k);
        let mut name = self.def(T::P, &format!("func.addr @{f}"));
        match self.rng.below(10) {
            0..=1 => {
                let a = self.def(T::I(self.addr), &format!("ptr.expose %{name}"));
                self.exposed.push(a.clone());
                name = self.def(T::P, &format!("ptr.from_exposed %{a}"));
            }
            2 if !self.fnptrs.is_empty() => {
                let i = self.rng.below(self.fnptrs.len() as u64) as usize;
                let other = self.fnptrs[i].0.clone();
                let p = self.rng.pick(&["eq", "ne"]);
                self.def(T::I(1), &format!("ptr.cmp.{p} %{name}, %{other}"));
            }
            _ => {}
        }
        self.fnptrs.push((name, k));
    }

    /// The text of function `k`'s type.
    fn sig_text(&self, k: usize) -> String {
        let sig = &self.sigs[k];
        let ps: Vec<String> = sig.params.iter().map(T::to_string).collect();
        let rs: Vec<String> = sig.rets.iter().map(T::to_string).collect();
        let rets = match rs.len() {
            0 => String::new(),
            1 => format!(" -> {}", rs[0]),
            _ => format!(" -> ({})", rs.join(", ")),
        };
        format!("func<({}){rets}>", ps.join(", "))
    }

    /// `func.call.indirect`: usually through a known function pointer with its signature;
    /// sometimes with another signature, or through some other pointer. Calls to the current
    /// function or earlier ones recurse until the fuel runs out.
    fn indirect_call(&mut self) {
        let later = self.func + 1 < self.sigs.len();
        let (p, k) = if !self.fnptrs.is_empty() && self.rng.chance(70) {
            let (p, k) = self.fnptrs[self.rng.below(self.fnptrs.len() as u64) as usize].clone();
            (format!("%{p}"), k)
        } else if self.rng.chance(85) {
            let k = if later && self.rng.chance(85) {
                self.func + 1 + self.rng.below((self.sigs.len() - self.func - 1) as u64) as usize
            } else {
                self.rng.below(self.sigs.len() as u64) as usize
            };
            (
                format!("%{}", {
                    let f = self.fn_name(k);
                    self.def(T::P, &format!("func.addr @{f}"))
                }),
                k,
            )
        } else {
            (
                self.operand(T::P),
                self.rng.below(self.sigs.len() as u64) as usize,
            )
        };
        // The signature: usually the callee's own.
        let k = if self.rng.chance(8) {
            self.rng.below(self.sigs.len() as u64) as usize
        } else {
            k
        };
        let sig = self.sig_text(k);
        let params = self.sigs[k].params.clone();
        let rets = self.sigs[k].rets.clone();
        let args: Vec<String> = params.iter().map(|t| self.operand(*t)).collect();
        let results: Vec<(String, T, String)> = rets
            .iter()
            .map(|t| (self.fresh(), *t, String::new()))
            .collect();
        let call = match self.handler() {
            Some(h) => format!(
                "func.invoke.indirect {sig} {p}({}) unwind ^{h}",
                args.join(", ")
            ),
            None => format!("func.call.indirect {sig} {p}({})", args.join(", ")),
        };
        self.op(&results, &call);
    }

    /// Load a function pointer from a global table, then sometimes call it.
    fn table_dispatch(&mut self) {
        let tables: Vec<GlobalInfo> = self
            .globals
            .iter()
            .filter(|g| g.table.is_some())
            .cloned()
            .collect();
        if tables.is_empty() {
            return self.func_addr();
        }
        let g = tables[self.rng.below(tables.len() as u64) as usize].clone();
        let table = g.table.clone().unwrap();
        let t = self.def(T::P, &format!("mem.global @{}", g.name));
        let i = self.rng.below(table.len() as u64 + 1);
        let idx = self.small(self.addr, i as i64, i as i64);
        let e = self.index_ptr("inbounds", &Agg::Scalar(T::P), &format!("%{t}"), &idx);
        let align = self
            .layout
            .ptr_align
            .min(g.align.max(self.layout.ptr_align));
        let f = self.def(T::P, &format!("mem.load %{e}, align {align}"));
        if let Some(&k) = table.get(i as usize) {
            self.fnptrs.push((f, k));
            if self.rng.chance(50) {
                self.indirect_call();
            }
        }
    }

    /// An initializer for a value of type `a` in a module whose globals are `g0..gn`.
    fn init(&mut self, a: &Agg, n: usize) -> String {
        if self.rng.chance(10) {
            return "zero".to_owned();
        }
        if self.rng.chance(6) {
            let size = self.layout.dims(a).0;
            let hex: String = (0..size)
                .map(|_| format!("{:02x}", self.rng.below(256)))
                .collect();
            return format!("bytes \"{hex}\"");
        }
        match a {
            Agg::Scalar(T::I(w) | T::B(w)) => interesting(self.rng, *w).to_string(),
            // A float's initializer is `zero` or its bytes.
            Agg::Scalar(T::F(_)) => "zero".to_owned(),
            Agg::Scalar(T::P) => match self.rng.below(3) {
                0 => "null".to_owned(),
                1 if n > 0 => format!("@g{}", self.rng.below(n as u64)),
                _ => {
                    let k = self.rng.below(self.sigs.len() as u64) as usize;
                    format!("@{}", self.fn_name(k))
                }
            },
            Agg::Struct(_, fs) => {
                let items: Vec<String> = fs.iter().map(|f| self.init(f, n)).collect();
                format!("{{{}}}", items.join(", "))
            }
            Agg::Array(k, e) => {
                let items: Vec<String> = (0..*k).map(|_| self.init(e, n)).collect();
                format!("{{{}}}", items.join(", "))
            }
            Agg::Scalar(T::V(_)) => unreachable!("memory aggregates hold scalars"),
        }
    }

    /// Up to three globals, some of them tables of function pointers.
    fn declare_globals(&mut self) {
        let n = self.rng.pick(&[0, 0, 1, 1, 2, 3]);
        for i in 0..n {
            let constant = self.rng.chance(30);
            let align = if self.rng.chance(70) {
                1
            } else {
                self.rng.pick(&[2, 4, 8, 16, 32])
            };
            let (agg, init, table) = if self.rng.chance(15) {
                let ks: Vec<usize> = (0..1 + self.rng.below(3))
                    .map(|_| self.rng.below(self.sigs.len() as u64) as usize)
                    .collect();
                let items: Vec<String> = ks
                    .iter()
                    .map(|&k| format!("@{}", self.fn_name(k)))
                    .collect();
                let agg = Agg::Array(ks.len() as u64, Box::new(Agg::Scalar(T::P)));
                (agg, format!("{{{}}}", items.join(", ")), Some(ks))
            } else {
                let agg = if self.rng.chance(40) {
                    Agg::Scalar(self.field_type())
                } else {
                    self.agg()
                };
                let init = self.init(&agg, n);
                (agg, init, None)
            };
            let c = if constant { "const " } else { "" };
            let al = if align == 1 {
                String::new()
            } else {
                format!(" align {align}")
            };
            write!(self.out, "global {c}@g{i}: {agg}{al} = {init}").unwrap();
            self.newline();
            self.globals.push(GlobalInfo {
                name: format!("g{i}"),
                agg,
                constant,
                align,
                table,
            });
        }
        if n > 0 {
            self.newline();
        }
    }

    /// A value of HFIR type `V(i)`, built from operands.
    fn build(&mut self, i: u8) -> String {
        let t = T::V(i);
        match vty(i) {
            VTy::Struct(_, fs) => {
                let vs: Vec<String> = fs.iter().map(|f| self.operand(*f)).collect();
                self.def(t, &format!("agg.make {}", vs.join(", ")))
            }
            VTy::Array(n, e) => {
                let vs: Vec<String> = (0..n).map(|_| self.operand(e)).collect();
                self.def(t, &format!("agg.make {}", vs.join(", ")))
            }
            VTy::Union(vs) => {
                let k = self.rng.below(vs.len() as u64) as usize;
                let v = self.operand(vs[k]);
                self.def(t, &format!("union.make {v}, {k}"))
            }
            VTy::Slice => {
                let (p, n) = if !self.mems.is_empty() && self.rng.chance(85) {
                    let m = self.mems[self.rng.below(self.mems.len() as u64) as usize].clone();
                    let n = (m.size / 4) as i64 + self.rng.below(2) as i64;
                    (format!("%{}", m.name), self.small(self.addr, n, n))
                } else {
                    (self.operand(T::P), self.operand(T::I(self.addr)))
                };
                self.def(t, &format!("slice.make {p}, {n}"))
            }
        }
    }

    /// A random HFIR value type matching `pick`, if the program has one.
    fn pick_vty(&mut self, pick: impl Fn(&VTy) -> bool) -> Option<u8> {
        let ok: Vec<u8> = (0..num_vtys() as u8).filter(|&i| pick(&vty(i))).collect();
        if ok.is_empty() {
            None
        } else {
            Some(self.rng.pick(&ok))
        }
    }

    /// `int.add.overflow.s` and friends.
    fn overflow_op(&mut self) {
        let op = self.rng.pick(&["add", "sub", "mul"]);
        // The lowering checks at one more bit (twice the bits for `mul`), which a narrow program
        // keeps to 64.
        let t = match (self.rng.1, op) {
            (false, _) => self.int_type(),
            (true, "mul") => T::I(self.rng.pick(&[1, 7, 8, 16, 32])),
            (true, _) => T::I(self.rng.pick(&[1, 7, 8, 16, 32, 63])),
        };
        let sign = self.rng.pick(&["s", "u"]);
        let (a, b) = (self.operand(t), self.operand(t));
        let (r, o) = (self.fresh(), self.fresh());
        let facts = if self.rng.chance(3) {
            self.fact(t, false)
        } else {
            String::new()
        };
        self.op(
            &[(r, t, facts), (o, T::I(1), String::new())],
            &format!("int.{op}.overflow.{sign} {a}, {b}"),
        );
    }

    /// `agg.extract`, `agg.insert`, or `copy` of a struct or array value.
    fn agg_op(&mut self) {
        let Some(i) = self.pick_vty(|v| matches!(v, VTy::Struct(..) | VTy::Array(..))) else {
            return;
        };
        let parts: Vec<T> = match vty(i) {
            VTy::Struct(_, fs) => fs,
            VTy::Array(n, e) => vec![e; n as usize],
            _ => unreachable!(),
        };
        let a = self.operand(T::V(i));
        let k = self.rng.below(parts.len() as u64) as usize;
        match self.rng.below(5) {
            0..=2 => {
                self.def(parts[k], &format!("agg.extract {a}, {k}"));
            }
            3 => {
                let v = self.operand(parts[k]);
                self.def(T::V(i), &format!("agg.insert {a}, {v}, {k}"));
            }
            _ => {
                self.def(T::V(i), &format!("copy {a}"));
            }
        }
    }

    /// `union.tag` or `union.get` of a union value, sometimes of the variant it holds.
    fn union_op(&mut self) {
        let Some(i) = self.pick_vty(|v| matches!(v, VTy::Union(_))) else {
            return;
        };
        let VTy::Union(vs) = vty(i) else {
            unreachable!()
        };
        let u = self.operand(T::V(i));
        if self.rng.chance(30) {
            self.def(T::I(32), &format!("union.tag {u}"));
            return;
        }
        let k = self.rng.below(vs.len() as u64) as usize;
        let mode = self.rng.pick(&["trap", "trap", "ub"]);
        self.def(vs[k], &format!("union.get.{mode} {u}, {k}"));
    }

    /// `slice.len`, `slice.ptr`, `slice.get`, or `slice.set` of a slice value: indices are
    /// usually in bounds, for elements of four bytes, or of a struct.
    fn slice_op(&mut self) {
        let Some(i) = self.pick_vty(|v| matches!(v, VTy::Slice)) else {
            return;
        };
        let s = self.operand(T::V(i));
        let aw = self.addr;
        match self.rng.below(6) {
            0 => {
                self.def(T::I(aw), &format!("slice.len {s}"));
            }
            1 => {
                self.def(T::P, &format!("slice.ptr {s}"));
            }
            k => {
                let elem = match self.pick_vty(|v| matches!(v, VTy::Struct(..))) {
                    Some(j) if self.rng.chance(20) && T::V(j).has_layout() => T::V(j),
                    _ => self.rng.pick(&[T::I(32), T::I(32), T::B(32), T::I(8)]),
                };
                let idx = if self.rng.chance(85) {
                    self.small(aw, 0, 3)
                } else {
                    self.operand(T::I(aw))
                };
                let mode = self.rng.pick(&["trap", "trap", "ub"]);
                let align = self.rng.pick(&[1, 1, 2, 4]);
                if k < 4 {
                    self.def(elem, &format!("slice.get.{mode} {s}, {idx}, align {align}"));
                } else {
                    let v = self.operand(elem);
                    self.op(
                        &[],
                        &format!("slice.set.{mode} {elem} {v}, {s}, {idx}, align {align}"),
                    );
                }
            }
        }
    }

    /// A store and load of a struct, array, or slice value, through stack memory for it.
    fn agg_mem_op(&mut self) {
        let Some(i) = self.pick_vty(|v| !matches!(v, VTy::Union(_))) else {
            return;
        };
        let t = T::V(i);
        let align = self.rng.pick(&[1, 2, 4, 8]);
        let p = self.def(T::P, &format!("mem.stack.of {t}, align {align}"));
        if self.rng.chance(70) {
            let v = self.operand(t);
            self.op(&[], &format!("mem.store {t} {v}, %{p}, align {align}"));
        }
        self.def(t, &format!("mem.load %{p}, align {align}"));
    }

    fn call_op(&mut self) {
        let callee =
            self.func + 1 + self.rng.below((self.sigs.len() - self.func - 1) as u64) as usize;
        let params = self.sigs[callee].params.clone();
        let rets = self.sigs[callee].rets.clone();
        let args: Vec<String> = params.iter().map(|t| self.operand(*t)).collect();
        // An external function's results sometimes carry facts, which the world's zeros may
        // break: UB after the event.
        let external = callee >= self.nfuncs;
        let results: Vec<(String, T, String)> = rets
            .iter()
            .map(|t| {
                let facts = if external && self.rng.chance(15) {
                    self.fact(*t, false)
                } else {
                    String::new()
                };
                (self.fresh(), *t, facts)
            })
            .collect();
        let call = match self.handler() {
            Some(h) => format!(
                "func.invoke @{}({}) unwind ^{h}",
                self.fn_name(callee),
                args.join(", ")
            ),
            None => format!("func.call @{}({})", self.fn_name(callee), args.join(", ")),
        };
        self.op(&results, &call);
    }

    fn func(&mut self, idx: usize) {
        self.func = idx;
        self.scope.clear();
        self.mems.clear();
        self.exposed.clear();
        self.fnptrs.clear();
        self.ops_left = 45;
        self.watch.clear();
        let (params, rets) = (self.sigs[idx].params.clone(), self.sigs[idx].rets.clone());
        let mut ps = Vec::new();
        for t in &params {
            let n = self.fresh();
            let facts = if *t == T::P && idx == 0 {
                // The entry gets null or poison: only scope facts let it run.
                if self.rng.chance(30) {
                    format!(" [{} assume]", self.rng.pick(&["noalias", "readonly"]))
                } else {
                    String::new()
                }
            } else if (*t == T::P && self.rng.chance(50)) || self.rng.chance(3) {
                self.fact(*t, true)
            } else {
                String::new()
            };
            ps.push(format!("%{n}: {t}{facts}"));
            if *t == T::P && idx > 0 {
                self.mems.push(Mem {
                    name: n.clone(),
                    size: 8,
                    align: 1,
                    family: None,
                    agg: None,
                    constant: false,
                });
            }
            self.scope.push((n, *t));
        }
        let rs = match rets.len() {
            0 => String::new(),
            1 => format!(" -> {}", rets[0]),
            _ => {
                let ts: Vec<String> = rets.iter().map(T::to_string).collect();
                format!(" -> ({})", ts.join(", "))
            }
        };
        let file = if self.rng.chance(30) {
            " loc \"gen.c\""
        } else {
            ""
        };
        write!(self.out, "func @f{idx}({}){rs}{file} {{", ps.join(", ")).unwrap();
        self.newline();
        let n = 4 + self.rng.below(18);
        for _ in 0..n {
            if self.ops_left == 0 {
                break;
            }
            self.stmt();
        }
        let vs: Vec<String> = rets
            .iter()
            .map(|&t| {
                let w: Vec<String> = self
                    .watch
                    .iter()
                    .filter(|(_, u)| *u == t)
                    .map(|(n, _)| format!("%{n}"))
                    .collect();
                if !w.is_empty() && self.rng.chance(60) {
                    w[self.rng.below(w.len() as u64) as usize].clone()
                } else {
                    self.operand(t)
                }
            })
            .collect();
        if self.rng.chance(6) {
            self.throw_term();
        } else {
            self.op(&[], format!("func.ret {}", vs.join(", ")).trim_end());
        }
        self.out.push('}');
        self.newline();
        self.newline();
    }
}

/// Whether `k` fits in `w` bits, signed or unsigned.
fn fits(k: &BigInt, w: u32) -> bool {
    let one = BigInt::from(1);
    (-(&one << (w - 1)) <= *k && *k < (&one << w)) || (*k >= BigInt::from(0) && *k < (one << w))
}

fn arg(rng: &mut Rng, t: T) -> String {
    match t {
        T::I(w) => {
            if rng.chance(6) {
                "poison".to_owned()
            } else if rng.chance(50) {
                (rng.below(10) as i64 - 3).to_string()
            } else {
                interesting(rng, w).to_string()
            }
        }
        T::P => if rng.chance(85) { "null" } else { "poison" }.to_owned(),
        T::F(_) => {
            if rng.chance(6) {
                "poison".to_owned()
            } else {
                float_lit(rng).to_owned()
            }
        }
        T::B(_) | T::V(_) => unreachable!("byte and aggregate parameters are not generated"),
    }
}

/// A float literal, biased toward the edge cases (read in either format, rounded).
fn float_lit(rng: &mut Rng) -> &'static str {
    rng.pick(&[
        "0.0",
        "-0.0",
        "1.0",
        "-1.0",
        "0.5",
        "1.5",
        "2.5",
        "-2.5",
        "0.1",
        "3.0",
        "100.0",
        "1e-7",
        "inf",
        "-inf",
        "nan",
        "-nan",
        "nan(0x1)",
        "-nan(0x2a)",
        "nan(0x400001)",
        "5e-324",
        "1e-310",
        "2.2250738585072014e-308",
        "1.7976931348623157e308",
        "1e-45",
        "1.1754944e-38",
        "3.4028235e38",
        "16777217.0",
        "9007199254740993.0",
        "2147483647.5",
        "-2147483648.0",
        "4294967296.0",
        "9223372036854775807.0",
        "-9223372036854775808.0",
        "18446744073709551616.0",
        "127.5",
        "-128.5",
        "255.5",
        "-0.75",
        "1e300",
        "1e30",
    ])
}

/// A random program.
pub fn program(rng: &mut Rng) -> Program {
    let narrow = rng.1;
    let (ptr_size, addr) = match rng.below(20) {
        _ if narrow => (64, 64),
        0..=11 => (64, 64),
        12 | 13 => (32, 32),
        14 | 15 => (64, 32),
        16 | 17 => (128, 64),
        18 => (16, 16),
        _ => (8, 8),
    };
    let nfuncs = 1 + rng.below(3) as usize;
    let layer = match rng.below(8) {
        0 => Some("hfir"),
        1..=3 => Some("mfir"),
        _ => None,
    };
    if layer == Some("mfir") {
        VTYS.with(|v| v.borrow_mut().clear());
    } else {
        make_vtys(rng);
    }
    let pick_v = |rng: &mut Rng, p: u64| -> Option<T> {
        let n = num_vtys() as u64;
        (n > 0 && rng.chance(p)).then(|| T::V(rng.below(n) as u8))
    };
    let mut sigs = Vec::new();
    for i in 0..nfuncs {
        let np = rng.below(if i == 0 { 3 } else { 4 });
        let params: Vec<T> = (0..np)
            .map(|_| {
                if i > 0
                    && let Some(t) = pick_v(rng, 20)
                {
                    t
                } else if rng.chance(if i == 0 { 15 } else { 55 }) {
                    T::P
                } else if !narrow && rng.chance(15) {
                    T::F(rng.pick(&[32, 64]))
                } else {
                    T::I(rng.width(&[1, 8, 32, 64, 7, 128]))
                }
            })
            .collect();
        let rets: Vec<T> = (0..rng.below(3))
            .map(|_| match pick_v(rng, 15) {
                Some(t) => t,
                None if !narrow && rng.chance(15) => T::F(rng.pick(&[32, 64])),
                None => match rng.below(10) {
                    0..=1 => T::P,
                    2 => T::B(rng.pick(&[8, 32])),
                    _ => T::I(rng.width(&[1, 8, 32, 64, 65, 128])),
                },
            })
            .collect();
        sigs.push(Sig { params, rets });
    }
    // External functions: their parameters are often pointers, so calls expose memory.
    for _ in 0..rng.pick(&[0, 0, 1, 1, 2, 3]) {
        let params: Vec<T> = (0..rng.below(4))
            .map(|_| {
                if rng.chance(55) {
                    T::P
                } else if !narrow && rng.chance(10) {
                    T::F(rng.pick(&[32, 64]))
                } else {
                    T::I(rng.width(&[1, 8, 32, 64, 128]))
                }
            })
            .collect();
        let rets: Vec<T> = (0..rng.below(3))
            .map(|_| match rng.below(10) {
                _ if !narrow && rng.chance(8) => T::F(rng.pick(&[32, 64])),
                0..=2 => T::P,
                3 => T::B(rng.pick(&[8, 32])),
                _ => T::I(rng.width(&[1, 8, 32, 64, 65, 128])),
            })
            .collect();
        sigs.push(Sig { params, rets });
    }
    let entry_params = sigs[0].params.clone();
    // The data layout: usually the default alignments, sometimes others.
    let natural = 1u64 << (u64::from(ptr_size) / 8).max(1).ilog2();
    let ptr_align = match rng.below(12) {
        _ if narrow => natural,
        0 => natural * 2,
        1 if natural > 1 => natural / 2,
        _ => natural,
    };
    let ints: Vec<(u32, u64)> = match rng.below(12) {
        _ if narrow => vec![(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)],
        0 => vec![(8, 1), (16, 2), (32, 4), (64, 4)],
        1 => vec![(8, 1), (16, 1), (32, 2), (64, 2), (128, 8)],
        _ => vec![(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)],
    };
    let custom_ints = ints.len() != 5 || ints[4].1 != 16;
    let layout = Layout {
        ptr_size: u64::from(ptr_size / 8),
        ptr_align,
        ints: ints.clone(),
    };
    let mut g = Gen {
        rng,
        out: String::new(),
        line: 1,
        sigs,
        nfuncs,
        func: 0,
        scope: Vec::new(),
        mems: Vec::new(),
        exposed: Vec::new(),
        next: 0,
        depth: 0,
        loops: Vec::new(),
        blocks: Vec::new(),
        addr,
        ptr_size,
        ops_left: 0,
        layout,
        globals: Vec::new(),
        fnptrs: Vec::new(),
        mfir: layer == Some("mfir"),
        watch: Vec::new(),
    };
    if let Some(l) = layer {
        write!(g.out, "layer {l}").unwrap();
        g.newline();
    }
    let memspace = (ptr_size, addr) != (64, 64) || ptr_align != natural || custom_ints;
    if memspace {
        write!(g.out, "memspace default ptr {ptr_size} addr {addr}").unwrap();
        if ptr_align != natural || g.rng.chance(10) {
            write!(g.out, " align {ptr_align}").unwrap();
        }
        if custom_ints {
            g.out.push_str(" int");
            for (w, a) in &ints {
                write!(g.out, " {w}:{a}").unwrap();
            }
        }
        g.newline();
    }
    if layer.is_some() || memspace {
        g.newline();
    }
    g.declare_globals();
    g.declare_externs();
    for i in 0..nfuncs {
        g.func(i);
    }
    let text = g.out;
    let rng = g.rng;
    let runs = (0..3)
        .map(|_| {
            let args = entry_params.iter().map(|t| arg(rng, *t)).collect();
            let fuel = rng.pick(&[3000, 3000, 3000, 200, 40]);
            (args, fuel)
        })
        .collect();
    Program { text, runs }
}
