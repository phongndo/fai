//! ABI torture (decision: C ABI for aggregates): random signatures of structs and arrays (fields
//! of `i8`…`i64`, `f32`, `f64`, `ptr`, arrays, nested `struct<C>`, `struct<packed>`, and
//! `struct<auto>` structs, 16-byte aligned ones, HFAs whose members are reordered by `auto`'s
//! layout) and scalars, compiled on one side by the AArch64 C compiler (GCC in the dev shell) and
//! on the other by FIR, with and without `-O`, then run (natively on AArch64, under
//! `qemu-aarch64` elsewhere). Every field must arrive in each direction:
//!
//! * C calls a FIR function with constant arguments; FIR reports every leaf it received and
//!   returns a constant result, whose leaves C reports.
//! * C calls a variadic FIR function with the same arguments after `...` (C's promotions turn a
//!   narrow integer into an `int` and a `float` into a `double`, which FIR reads and narrows);
//!   FIR reads them with `va.arg` and reports them. A composite that isn't a C composite (packed
//!   or `auto` somewhere in it) travels as its *twin*, a C composite of the same layout and
//!   AAPCS64 class (an HFA's `struct<C>` of its floats, else `array<N x i8>` of its bytes): C
//!   passes the struct, FIR reads the twin, stores it, and reports the leaves loaded from it, and
//!   the other way FIR builds the twin from the leaves (only for composites without pointers,
//!   which bytes would carry as integers). 16-byte aligned composites can't be variadic in FIR
//!   (no C composite is 16-byte aligned without an `i128` leaf, which the backend rejects).
//! * FIR calls a C function, a variadic C function, and its own callee and variadic function
//!   with constant arguments; each reports them and returns a constant result, whose leaves FIR
//!   reports.
//!
//! Pointers point into a 64-byte buffer, and every report of one dereferences it and prints the
//! byte it reads, so a pointer arrives as a usable pointer. The externals read memory through
//! their arguments (`read(args)`), and the FIR calls (to C and to FIR) also run in the
//! interpreter, with the buffer a FIR global, as MFIR and as LFIR before and after register
//! allocation: their events must agree exactly but for allocation numbers, so a pointer leaf
//! that crossed as bare address bits (losing the provenance a `read(args)` callee reaches its
//! memory by) is caught there too.
//!
//! A third of the signatures exhaust a register class: they take `x` registers (or FP ones)
//! until a composite no longer fits and goes on the stack, then pass scalars of that class after
//! it. The test classifies every argument itself (an independent AAPCS64) and counts the
//! signatures that put each class on the stack. A signature with a composite passed as `x`
//! register words whose pointer leaf doesn't fill a word (a packed pointer) must be refused by
//! instruction selection, and is checked to be.
//!
//! The expected output is computed here from the values. `FIR_ABI=N` sets how many signatures
//! (default 240), `FIR_ABI_SEED` the seed (default 1); `FIR_CC` the C compiler. Without a C
//! compiler or a way to run AArch64 binaries it skips, unless `FIR_REQUIRE_FULL=1`; it records
//! its counts for `cargo xtask verify` (`abi_torture`).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use fir::backend::aarch64 as a64;

#[allow(dead_code)]
mod common;
use common::evidence::{Evidence, require};

/// A deterministic random source (xorshift64*).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Scalar {
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Ptr,
}

use Scalar::*;

impl Scalar {
    fn fir(self) -> &'static str {
        match self {
            I8 => "i8",
            I16 => "i16",
            I32 => "i32",
            I64 => "i64",
            F32 => "f32",
            F64 => "f64",
            Ptr => "ptr",
        }
    }

    fn c(self) -> &'static str {
        match self {
            I8 => "int8_t",
            I16 => "int16_t",
            I32 => "int32_t",
            I64 => "int64_t",
            F32 => "float",
            F64 => "double",
            Ptr => "char *",
        }
    }

    fn bits(self) -> u32 {
        match self {
            I8 => 8,
            I16 => 16,
            I32 | F32 => 32,
            _ => 64,
        }
    }
}

/// A struct's layout policy.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Policy {
    C,
    Packed,
    Auto,
}

/// A type of the signatures.
#[derive(Clone, Debug)]
enum T {
    S(Scalar),
    Struct {
        policy: Policy,
        fields: Vec<T>,
    },
    Array(u32, Box<T>),
    /// A zero-length array of `__int128`: no leaves, 16-byte alignment.
    Align16,
}

/// A leaf's value.
#[derive(Clone, Copy, Debug)]
enum V {
    Int(i64),
    F32(f32),
    F64(f64),
    /// An offset into the shared buffer, or null.
    Ptr(Option<u32>),
}

/// The byte at offset `o` of the shared buffer.
fn pattern(o: u32) -> u32 {
    (o * 37 + 11) & 255
}

// Layout and classification, computed here independently of FIR's (`types.rs`, `abi.rs`).

fn align_up(x: u64, a: u64) -> u64 {
    x.div_ceil(a) * a
}

impl Scalar {
    fn size(self) -> u64 {
        u64::from(self.bits() / 8)
    }
}

/// A type's alignment.
fn align_of(t: &T) -> u64 {
    match t {
        T::S(s) => s.size(),
        T::Struct {
            policy: Policy::Packed,
            ..
        } => 1,
        T::Struct { fields, .. } => fields.iter().map(align_of).max().unwrap_or(1),
        T::Array(_, e) => align_of(e),
        T::Align16 => 16,
    }
}

/// A struct's fields' offsets (in declared order) and its size: `auto` places fields by
/// decreasing alignment (stably), `packed` without alignment.
fn place(policy: Policy, fields: &[T]) -> (Vec<u64>, u64) {
    let mut order: Vec<usize> = (0..fields.len()).collect();
    if policy == Policy::Auto {
        order.sort_by_key(|&i| std::cmp::Reverse(align_of(&fields[i])));
    }
    let mut offs = vec![0; fields.len()];
    let mut o = 0;
    for i in order {
        if policy != Policy::Packed {
            o = align_up(o, align_of(&fields[i]));
        }
        offs[i] = o;
        o += size_of(&fields[i]);
    }
    (
        offs,
        align_up(
            o,
            align_of(&T::Struct {
                policy,
                fields: fields.to_vec(),
            }),
        ),
    )
}

/// A type's size.
fn size_of(t: &T) -> u64 {
    match t {
        T::S(s) => s.size(),
        T::Struct { policy, fields } => place(*policy, fields).1,
        T::Array(n, e) => u64::from(*n) * size_of(e),
        T::Align16 => 0,
    }
}

/// The offsets of a type's leaves, in the order of [`leaves`].
fn leaf_offs(t: &T, base: u64, out: &mut Vec<(u64, Scalar)>) {
    match t {
        T::S(s) => out.push((base, *s)),
        T::Struct { policy, fields } => {
            let (offs, _) = place(*policy, fields);
            for (f, o) in fields.iter().zip(offs) {
                leaf_offs(f, base + o, out);
            }
        }
        T::Array(n, e) => {
            let sz = size_of(e);
            for j in 0..u64::from(*n) {
                leaf_offs(e, base + j * sz, out);
            }
        }
        T::Align16 => {}
    }
}

fn has_ptr(t: &T) -> bool {
    let mut ls = Vec::new();
    leaf_offs(t, 0, &mut ls);
    ls.iter().any(|l| l.1 == Ptr)
}

fn has_align16(t: &T) -> bool {
    match t {
        T::Struct { fields, .. } => fields.iter().any(has_align16),
        T::Array(_, e) => has_align16(e),
        T::Align16 => true,
        T::S(_) => false,
    }
}

/// How AAPCS64 passes a composite.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Class {
    Nothing,
    /// An HFA of this many members of the format (`true` for `double`).
    Hfa(bool, u32),
    /// This many `x` registers, from an even one if 16-byte aligned.
    Words(u32, bool),
    Ref,
}

fn class_of(t: &T) -> Class {
    let size = size_of(t);
    if size == 0 {
        return Class::Nothing;
    }
    let mut ls = Vec::new();
    leaf_offs(t, 0, &mut ls);
    if let Some(&(_, f @ (F32 | F64))) = ls.first() {
        let b = f.size();
        let mut offs: Vec<u64> = ls.iter().map(|l| l.0).collect();
        offs.sort_unstable();
        if !has_align16(t)
            && ls.len() <= 4
            && ls.iter().all(|l| l.1 == f)
            && offs.iter().enumerate().all(|(i, &o)| o == i as u64 * b)
            && size == ls.len() as u64 * b
        {
            return Class::Hfa(f == F64, ls.len() as u32);
        }
    }
    if size <= 16 {
        Class::Words(size.div_ceil(8) as u32, align_of(t) >= 16)
    } else {
        Class::Ref
    }
}

/// Whether instruction selection must refuse to pass a value of this type: a composite passed
/// as `x` register words with a pointer leaf that doesn't fill one.
fn splits_ptr(t: &T) -> bool {
    if matches!(t, T::S(_)) || !matches!(class_of(t), Class::Words(..)) {
        return false;
    }
    let mut ls = Vec::new();
    leaf_offs(t, 0, &mut ls);
    ls.iter().any(|&(o, s)| s == Ptr && o % 8 != 0)
}

/// What a signature's arguments do to the registers (AAPCS64 stage C).
#[derive(Default, Clone, Copy)]
struct Use {
    /// An `x`-register argument went on the stack.
    gp_stack: bool,
    /// An FP-register argument went on the stack.
    fp_stack: bool,
    /// A scalar of a class followed a composite of its class that went on the stack.
    scalar_after: bool,
    /// Whether a composite of each class (gp, fp) went on the stack.
    comp: (bool, bool),
}

fn simulate(ts: &[&T]) -> Use {
    let (mut g, mut f) = (0u32, 0u32);
    let mut u = Use::default();
    for t in ts {
        match t {
            T::S(F32 | F64) => {
                if f < 8 {
                    f += 1;
                } else {
                    u.fp_stack = true;
                    u.scalar_after |= u.comp.1;
                }
            }
            T::S(_) => {
                if g < 8 {
                    g += 1;
                } else {
                    u.gp_stack = true;
                    u.scalar_after |= u.comp.0;
                }
            }
            t => match class_of(t) {
                Class::Nothing => {}
                Class::Hfa(_, n) => {
                    if f + n <= 8 {
                        f += n;
                    } else {
                        f = 8;
                        u.fp_stack = true;
                        u.comp.1 = true;
                    }
                }
                Class::Words(n, even) => {
                    if even {
                        g = g.next_multiple_of(2);
                    }
                    if g + n <= 8 {
                        g += n;
                    } else {
                        g = 8;
                        u.gp_stack = true;
                        u.comp.0 = true;
                    }
                }
                Class::Ref => {
                    if g < 8 {
                        g += 1;
                    } else {
                        u.gp_stack = true;
                    }
                }
            },
        }
    }
    u
}

fn gen_scalar(rng: &mut Rng, floats: bool) -> Scalar {
    if floats {
        return if rng.chance(50) { F32 } else { F64 };
    }
    [I8, I16, I32, I64, F32, F64, Ptr][rng.below(7) as usize]
}

/// A struct of floats of format `s` (one to four leaves, sometimes five), nested in `packed`,
/// `C`, and `auto` structs and arrays, so `auto`'s layout can put a later field first.
fn gen_float_nest(rng: &mut Rng, s: Scalar) -> T {
    let most = if rng.chance(15) { 5 } else { 4 };
    let n = 1 + rng.below(most) as usize;
    let mut fields = Vec::new();
    let mut left = n;
    while left > 0 {
        let k = 1 + rng.below(left as u64) as usize;
        left -= k;
        fields.push(match rng.below(4) {
            0 => T::Struct {
                policy: Policy::Packed,
                fields: vec![T::S(s); k],
            },
            1 if k > 1 => T::Array(k as u32, Box::new(T::S(s))),
            2 => T::Struct {
                policy: Policy::C,
                fields: vec![T::S(s); k],
            },
            _ => {
                left += k - 1;
                T::S(s)
            }
        });
    }
    T::Struct {
        policy: if rng.chance(60) {
            Policy::Auto
        } else {
            Policy::C
        },
        fields,
    }
}

fn gen_policy(rng: &mut Rng) -> Policy {
    match rng.below(100) {
        0..=14 => Policy::Packed,
        15..=29 => Policy::Auto,
        _ => Policy::C,
    }
}

fn gen_struct(rng: &mut Rng, depth: u32) -> T {
    match rng.below(12) {
        // An HFA candidate: one to four floats of one format, perhaps through an array.
        0..=2 => {
            let s = gen_scalar(rng, true);
            let n = 1 + rng.below(4) as u32;
            let fields = if n >= 2 && rng.chance(30) {
                vec![T::S(s), T::Array(n - 1, Box::new(T::S(s)))]
            } else {
                vec![T::S(s); n as usize]
            };
            T::Struct {
                policy: if rng.chance(20) {
                    Policy::Packed
                } else {
                    Policy::C
                },
                fields,
            }
        }
        // Floats nested so that memory order and declared order differ.
        3 => {
            let s = gen_scalar(rng, true);
            gen_float_nest(rng, s)
        }
        _ => {
            let most = if rng.chance(50) { 3 } else { 6 };
            let n = 1 + rng.below(most) as usize;
            let mut fields = Vec::new();
            if rng.chance(6) {
                fields.push(T::Align16);
            }
            for _ in 0..n {
                fields.push(match rng.below(10) {
                    0 if depth < 2 => gen_struct(rng, depth + 1),
                    1 => T::Array(
                        1 + rng.below(4) as u32,
                        Box::new(T::S(gen_scalar(rng, false))),
                    ),
                    _ => T::S(gen_scalar(rng, false)),
                });
            }
            let mut policy = gen_policy(rng);
            if policy == Policy::Packed && fields.iter().any(|f| matches!(f, T::Align16)) {
                policy = Policy::C;
            }
            T::Struct { policy, fields }
        }
    }
}

/// A composite of integers and pointers (an `x`-register class: words or a reference).
fn gen_gp_struct(rng: &mut Rng) -> T {
    let most = if rng.chance(20) { 5 } else { 3 };
    let n = 1 + rng.below(most) as usize;
    let fields = (0..n)
        .map(|_| match rng.below(8) {
            0 => T::Array(1 + rng.below(3) as u32, Box::new(T::S(I8))),
            k => T::S([I8, I16, I32, I64, Ptr, I64, I32][k as usize - 1]),
        })
        .collect();
    T::Struct {
        policy: gen_policy(rng),
        fields,
    }
}

/// An HFA: one to four floats of one format.
fn gen_hfa(rng: &mut Rng) -> T {
    let s = gen_scalar(rng, true);
    if rng.chance(30) {
        return gen_float_nest(rng, s);
    }
    T::Struct {
        policy: Policy::C,
        fields: vec![T::S(s); 1 + rng.below(4) as usize],
    }
}

fn gen_value(rng: &mut Rng, s: Scalar) -> V {
    match s {
        F32 => V::F32((rng.below(8001) as f32 - 4000.0) / 8.0),
        F64 => V::F64((rng.below(2_000_001) as f64 - 1_000_000.0) / 64.0),
        Ptr => V::Ptr(if rng.chance(10) {
            None
        } else {
            Some(rng.below(64) as u32)
        }),
        _ => {
            let b = s.bits();
            let x = rng.next() as i64;
            V::Int(if b == 64 {
                x
            } else {
                (x << (64 - b)) >> (64 - b)
            })
        }
    }
}

/// A signature's parameter or result, with the values of its leaves.
struct Arg {
    t: T,
    vals: Vec<V>,
}

/// The leaves of a type, as C member paths and FIR part paths.
fn leaves(t: &T, cpath: &str, fpath: &[u32], out: &mut Vec<(Scalar, String, Vec<u32>)>) {
    match t {
        T::S(s) => out.push((*s, cpath.to_owned(), fpath.to_vec())),
        T::Struct { fields, .. } => {
            for (i, f) in fields.iter().enumerate() {
                let mut p = fpath.to_vec();
                p.push(i as u32);
                leaves(f, &format!("{cpath}.f{i}"), &p, out);
            }
        }
        T::Array(n, e) => {
            for j in 0..*n {
                let mut p = fpath.to_vec();
                p.push(j);
                leaves(e, &format!("{cpath}.e[{j}]"), &p, out);
            }
        }
        T::Align16 => {}
    }
}

/// The FIR text of a type.
fn fir_ty(t: &T) -> String {
    match t {
        T::S(s) => s.fir().to_owned(),
        T::Struct { policy, fields } => format!(
            "struct<{}>{{{}}}",
            match policy {
                Policy::C => "C",
                Policy::Packed => "packed",
                Policy::Auto => "auto",
            },
            fields.iter().map(fir_ty).collect::<Vec<_>>().join(", ")
        ),
        T::Array(n, e) => format!("array<{n} x {}>", fir_ty(e)),
        T::Align16 => "array<0 x i128>".to_owned(),
    }
}

/// C struct definitions, one per distinct type.
#[derive(Default)]
struct CDefs {
    defs: String,
    names: Vec<String>,
}

impl CDefs {
    fn ty(&mut self, t: &T) -> String {
        match t {
            T::S(s) => s.c().to_owned(),
            _ => {
                let key = fir_ty(t);
                if let Some(i) = self.names.iter().position(|n| *n == key) {
                    return format!("struct s{i}");
                }
                let body = match t {
                    T::Struct { policy, fields } => {
                        // An `auto` struct's fields in its layout's order, keeping their names.
                        let mut order: Vec<usize> = (0..fields.len()).collect();
                        if *policy == Policy::Auto {
                            let (offs, _) = place(*policy, fields);
                            order.sort_by_key(|&i| (offs[i], size_of(&fields[i]) > 0));
                        }
                        order
                            .into_iter()
                            .map(|i| match &fields[i] {
                                T::Align16 => format!(" __int128 f{i}[0];"),
                                T::S(s) => format!(" {} f{i};", s.c()),
                                f => format!(" {} f{i};", self.ty(f)),
                            })
                            .collect::<String>()
                    }
                    T::Array(n, e) => format!(" {} e[{n}];", self.ty(e)),
                    _ => unreachable!(),
                };
                let packed = matches!(
                    t,
                    T::Struct {
                        policy: Policy::Packed,
                        ..
                    }
                );
                let i = self.names.len();
                self.names.push(key);
                writeln!(
                    self.defs,
                    "struct{} s{i} {{{body} }};",
                    if packed {
                        " __attribute__((packed))"
                    } else {
                        ""
                    }
                )
                .unwrap();
                format!("struct s{i}")
            }
        }
    }
}

/// A C expression of a value of type `t` from its leaves.
fn c_value(defs: &mut CDefs, t: &T, vals: &mut std::slice::Iter<'_, V>) -> String {
    match t {
        T::S(_) => match vals.next().unwrap() {
            V::Int(x) => format!("{x}LL"),
            V::F32(x) => format!("{x:?}f"),
            V::F64(x) => format!("{x:?}"),
            V::Ptr(Some(o)) => format!("cbuf + {o}"),
            V::Ptr(None) => "(char *)0".to_owned(),
        },
        T::Struct { fields, .. } => {
            let name = defs.ty(t);
            let parts: Vec<String> = fields
                .iter()
                .filter(|f| !matches!(f, T::Align16))
                .map(|f| c_value(defs, f, vals))
                .collect();
            // Designated by name: an aligned field takes no initializer.
            let mut items = Vec::new();
            let mut k = 0;
            for (i, f) in fields.iter().enumerate() {
                if !matches!(f, T::Align16) {
                    items.push(format!(".f{i} = {}", parts[k]));
                    k += 1;
                }
            }
            format!("({name}){{{}}}", items.join(", "))
        }
        T::Array(n, e) => {
            let name = defs.ty(t);
            let parts: Vec<String> = (0..*n).map(|_| c_value(defs, e, vals)).collect();
            format!("({name}){{{{{}}}}}", parts.join(", "))
        }
        T::Align16 => unreachable!(),
    }
}

/// The expected report of a leaf: a pointer's offset into the buffer and the byte it reads.
fn report(v: V) -> String {
    match v {
        V::Int(x) => format!("i {x}\n"),
        V::F32(x) => format!("f {:016x}\n", f64::from(x).to_bits()),
        V::F64(x) => format!("f {:016x}\n", x.to_bits()),
        V::Ptr(Some(o)) => format!("p {o} {}\n", pattern(o)),
        V::Ptr(None) => "p null\n".to_owned(),
    }
}

/// C code reporting the leaves of expression `e` of type `t`.
fn c_report(t: &T, e: &str) -> String {
    let mut ls = Vec::new();
    leaves(t, "", &[], &mut ls);
    ls.into_iter()
        .map(|(s, path, _)| {
            let x = format!("{e}{path}");
            match s {
                F32 | F64 => format!("  rec_f({x});\n"),
                Ptr => format!("  rec_p({x});\n"),
                _ => format!("  rec_i({x});\n"),
            }
        })
        .collect()
}

/// FIR text building a value of type `t` from its leaves, into `%name`; the ops go to `out`.
struct FirGen {
    out: String,
    n: u32,
}

impl FirGen {
    fn fresh(&mut self) -> String {
        self.n += 1;
        format!("%t{}", self.n)
    }

    /// A scalar of the next leaf.
    fn scalar(&mut self, s: Scalar, v: V) -> String {
        let r = self.fresh();
        match v {
            V::Int(x) => writeln!(self.out, "  {r}: {} = int.const {x}", s.fir()).unwrap(),
            V::F32(x) => writeln!(self.out, "  {r}: f32 = float.const {x:?}").unwrap(),
            V::F64(x) => writeln!(self.out, "  {r}: f64 = float.const {x:?}").unwrap(),
            V::Ptr(None) => writeln!(self.out, "  {r}: ptr = ptr.null").unwrap(),
            V::Ptr(Some(o)) => {
                let b = self.fresh();
                let k = self.fresh();
                writeln!(self.out, "  {b}: ptr = mem.load %base, align 8").unwrap();
                writeln!(self.out, "  {k}: i64 = int.const {o}").unwrap();
                writeln!(self.out, "  {r}: ptr = ptr.offset.wrap {b}, {k}").unwrap();
            }
        }
        r
    }

    /// A value of type `t` made of the next leaves.
    fn make(&mut self, t: &T, vals: &mut std::slice::Iter<'_, V>) -> String {
        match t {
            T::S(s) => self.scalar(*s, *vals.next().unwrap()),
            T::Struct { fields, .. } => {
                let parts: Vec<String> = fields.iter().map(|f| self.make(f, vals)).collect();
                let v = self.fresh();
                writeln!(
                    self.out,
                    "  {v}: {} = agg.make {}",
                    fir_ty(t),
                    parts.join(", ")
                )
                .unwrap();
                v
            }
            T::Array(n, e) => {
                let parts: Vec<String> = (0..*n).map(|_| self.make(e, vals)).collect();
                let v = self.fresh();
                writeln!(
                    self.out,
                    "  {v}: {} = agg.make {}",
                    fir_ty(t),
                    parts.join(", ")
                )
                .unwrap();
                v
            }
            T::Align16 => {
                let v = self.fresh();
                // No operands: a location ends the op.
                writeln!(self.out, "  {v}: array<0 x i128> = agg.make @1:1").unwrap();
                v
            }
        }
    }

    /// The address `off` bytes into `slot`.
    fn at(&mut self, slot: &str, off: u64) -> String {
        let k = self.fresh();
        let q = self.fresh();
        writeln!(self.out, "  {k}: i64 = int.const {off}").unwrap();
        writeln!(self.out, "  {q}: ptr = ptr.offset.wrap {slot}, {k}").unwrap();
        q
    }

    /// The twin of a value of type `t` made of `vals`: its leaves stored at their offsets in a
    /// slot, which is loaded as the twin.
    fn make_twin(&mut self, t: &T, vals: &[V]) -> String {
        let slot = self.fresh();
        writeln!(
            self.out,
            "  {slot}: ptr = mem.stack {}, align 8",
            size_of(t).max(1)
        )
        .unwrap();
        let mut ls = Vec::new();
        leaf_offs(t, 0, &mut ls);
        for (&(o, s), &v) in ls.iter().zip(vals) {
            let x = self.scalar(s, v);
            let q = self.at(&slot, o);
            writeln!(self.out, "  mem.store {} {x}, {q}, align 1", s.fir()).unwrap();
        }
        let v = self.fresh();
        writeln!(self.out, "  {v}: {} = mem.load {slot}, align 1", twin(t)).unwrap();
        v
    }

    /// Report a twin `v` of a value of type `t`: stored, then each leaf loaded at its offset.
    fn report_twin(&mut self, t: &T, v: &str) {
        let slot = self.fresh();
        writeln!(
            self.out,
            "  {slot}: ptr = mem.stack {}, align 8",
            size_of(t).max(1)
        )
        .unwrap();
        writeln!(self.out, "  mem.store {} {v}, {slot}, align 1", twin(t)).unwrap();
        let mut ls = Vec::new();
        leaf_offs(t, 0, &mut ls);
        for (o, s) in ls {
            let q = self.at(&slot, o);
            let x = self.fresh();
            writeln!(self.out, "  {x}: {} = mem.load {q}, align 1", s.fir()).unwrap();
            self.report(&T::S(s), &x);
        }
    }

    /// Report the leaves of `%v` of type `t`.
    fn report(&mut self, t: &T, v: &str) {
        match t {
            T::S(s) => match s {
                F32 => {
                    let d = self.fresh();
                    writeln!(self.out, "  {d}: f64 = float.ext {v}").unwrap();
                    writeln!(self.out, "  func.call @rec_f({d})").unwrap();
                }
                F64 => writeln!(self.out, "  func.call @rec_f({v})").unwrap(),
                Ptr => writeln!(self.out, "  func.call @rec_p({v})").unwrap(),
                I64 => writeln!(self.out, "  func.call @rec_i({v})").unwrap(),
                _ => {
                    let d = self.fresh();
                    writeln!(self.out, "  {d}: i64 = int.sext {v}").unwrap();
                    writeln!(self.out, "  func.call @rec_i({d})").unwrap();
                }
            },
            T::Struct { fields, .. } => {
                for (i, f) in fields.iter().enumerate() {
                    if matches!(f, T::Align16) {
                        continue;
                    }
                    let p = self.fresh();
                    writeln!(self.out, "  {p}: {} = agg.extract {v}, {i}", fir_ty(f)).unwrap();
                    self.report(f, &p);
                }
            }
            T::Array(n, e) => {
                for j in 0..*n {
                    let p = self.fresh();
                    writeln!(self.out, "  {p}: {} = agg.extract {v}, {j}", fir_ty(e)).unwrap();
                    self.report(e, &p);
                }
            }
            T::Align16 => {}
        }
    }
}

/// Whether FIR takes this type as a variadic argument as it is: scalars and C composites
/// (`struct<C>` and nonempty arrays), so no packed or `auto` struct or zero-length array.
fn va_ok(t: &T) -> bool {
    match t {
        T::S(_) => true,
        T::Struct { policy, fields } => *policy == Policy::C && fields.iter().all(va_ok),
        T::Array(n, e) => *n > 0 && va_ok(e),
        T::Align16 => false,
    }
}

/// How a parameter goes through `...`, if it can.
#[derive(Clone, Copy, PartialEq)]
enum Va {
    /// As it is (promoted, if a narrow scalar).
    Direct,
    /// As its twin.
    Twin,
}

fn va_pass(t: &T) -> Option<Va> {
    if va_ok(t) {
        Some(Va::Direct)
    } else if !has_align16(t) && size_of(t) > 0 && !has_ptr(t) {
        Some(Va::Twin)
    } else {
        None
    }
}

/// The C composite of the same layout and AAPCS64 class as a composite (its alignment is at most
/// 8, so classes agree on alignment too): an HFA's `struct<C>` of its members, else the array
/// of its bytes.
fn twin(t: &T) -> String {
    match class_of(t) {
        Class::Hfa(d, n) => format!(
            "struct<C>{{{}}}",
            vec![if d { "f64" } else { "f32" }; n as usize].join(", ")
        ),
        _ => format!("array<{} x i8>", size_of(t)),
    }
}

/// The type a variadic argument of this type is passed as in C: an integer narrower than `int`
/// as `int`, a `float` as a `double`.
fn promoted(t: &T) -> T {
    match t {
        T::S(I8 | I16) => T::S(I32),
        T::S(F32) => T::S(F64),
        t => t.clone(),
    }
}

struct Sig {
    params: Vec<Arg>,
    ret: Option<Arg>,
}

impl Sig {
    fn uses(&self) -> Use {
        simulate(&self.params.iter().map(|p| &p.t).collect::<Vec<_>>())
    }

    /// Whether instruction selection must refuse it.
    fn refused(&self) -> bool {
        self.params
            .iter()
            .chain(&self.ret)
            .any(|a| splits_ptr(&a.t))
    }

    /// How its parameters go through `...`, if they all can.
    fn va(&self) -> Option<Vec<Va>> {
        self.params.iter().map(|p| va_pass(&p.t)).collect()
    }
}

fn gen_arg(rng: &mut Rng, t: T) -> Arg {
    let mut ls = Vec::new();
    leaves(&t, "", &[], &mut ls);
    let vals = ls.iter().map(|(s, ..)| gen_value(rng, *s)).collect();
    Arg { t, vals }
}

/// Parameters that exhaust the `x` registers (or the FP ones, if `fp`): arguments of the class
/// until a composite of it goes on the stack, then scalars of the class after it.
fn gen_exhaust(rng: &mut Rng, fp: bool, ts: &mut Vec<T>) {
    for _ in 0..24 {
        let u = simulate(&ts.iter().collect::<Vec<_>>());
        if if fp { u.comp.1 } else { u.comp.0 } {
            break;
        }
        ts.push(match (fp, rng.below(10)) {
            (true, 0..=5) => gen_hfa(rng),
            (false, 0..=5) => gen_gp_struct(rng),
            (true, _) => T::S(gen_scalar(rng, true)),
            (false, _) => T::S([I8, I16, I32, I64, Ptr][rng.below(5) as usize]),
        });
    }
    for _ in 0..1 + rng.below(3) {
        ts.push(T::S(if fp {
            gen_scalar(rng, true)
        } else {
            [I8, I32, I64, Ptr][rng.below(4) as usize]
        }));
    }
}

fn gen_sig(rng: &mut Rng) -> Sig {
    let ts: Vec<T> = if rng.chance(35) {
        let mut ts = Vec::new();
        // A few arguments of either class first, then the exhaustion.
        for _ in 0..rng.below(3) {
            ts.push(if rng.chance(50) {
                gen_struct(rng, 0)
            } else {
                T::S(gen_scalar(rng, false))
            });
        }
        match rng.below(3) {
            0 => gen_exhaust(rng, false, &mut ts),
            1 => gen_exhaust(rng, true, &mut ts),
            _ => {
                gen_exhaust(rng, false, &mut ts);
                gen_exhaust(rng, true, &mut ts);
            }
        }
        ts
    } else {
        let most = if rng.chance(30) { 12 } else { 5 };
        let n = 1 + rng.below(most) as usize;
        (0..n)
            .map(|_| {
                if rng.chance(75) {
                    gen_struct(rng, 0)
                } else {
                    T::S(gen_scalar(rng, false))
                }
            })
            .collect()
    };
    let params = ts.into_iter().map(|t| gen_arg(rng, t)).collect();
    let ret = match rng.below(10) {
        0 => None,
        1 => {
            let t = T::S(gen_scalar(rng, false));
            Some(gen_arg(rng, t))
        }
        _ => {
            let t = gen_struct(rng, 0);
            Some(gen_arg(rng, t))
        }
    };
    Sig { params, ret }
}

/// The C and FIR sources of a batch of signatures, and the expected output.
fn sources(sigs: &[Sig]) -> (String, String, String) {
    let mut defs = CDefs::default();
    let mut c = String::new();
    let mut f = String::from(
        "extern func @rec_i(i64) effects[] assume\n\
         extern func @rec_f(f64) effects[] assume\n\
         extern func @rec_p(ptr) effects[read(args)] assume\n\
         global @base: ptr = null\n\
         global @buf: array<64 x i8> = zero\n\
         func @set_base(%p: ptr) {\n  %b: ptr = mem.global @base\n  mem.store ptr %p, %b, align 8\n  func.ret\n}\n",
    );
    let mut want = String::new();
    let mut main = String::from(
        "int main(void) {\n  for (int i = 0; i < 64; i++) cbuf[i] = (char)(i * 37 + 11);\n  fir_set_base(cbuf);\n",
    );
    for (i, sig) in sigs.iter().enumerate() {
        let cps: Vec<String> = sig.params.iter().map(|p| defs.ty(&p.t)).collect();
        let cret = sig
            .ret
            .as_ref()
            .map_or("void".to_owned(), |r| defs.ty(&r.t));
        let fps: Vec<String> = sig.params.iter().map(|p| fir_ty(&p.t)).collect();
        let fret = sig
            .ret
            .as_ref()
            .map_or(String::new(), |r| format!(" -> {}", fir_ty(&r.t)));
        let cparams = |names: bool| -> String {
            cps.iter()
                .enumerate()
                .map(|(k, t)| {
                    if names {
                        format!("{t} a{k}")
                    } else {
                        t.clone()
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        };
        let ret_c = |defs: &mut CDefs| -> String {
            match &sig.ret {
                Some(r) => format!("  return {};\n", c_value(defs, &r.t, &mut r.vals.iter())),
                None => String::new(),
            }
        };
        let args_report: String = sig
            .params
            .iter()
            .flat_map(|p| p.vals.iter())
            .map(|&v| report(v))
            .collect();
        let ret_report: String = sig.ret.as_ref().map_or(String::new(), |r| {
            r.vals.iter().map(|&v| report(v)).collect()
        });
        let cargs: Vec<String> = sig
            .params
            .iter()
            .map(|p| c_value(&mut defs, &p.t, &mut p.vals.iter()))
            .collect();
        // C calls FIR.
        writeln!(
            c,
            "{cret} fir_callee{i}({}) __asm__(\"fir_callee{i}\");",
            cparams(false)
        )
        .unwrap();
        writeln!(c, "{cret} fir_va{i}(int n, ...) __asm__(\"fir_va{i}\");").unwrap();
        writeln!(main, "  puts(\"T{i} c->fir\");").unwrap();
        let call = format!("fir_callee{i}({})", cargs.join(", "));
        match &sig.ret {
            Some(r) => {
                writeln!(main, "  {{ {cret} r = {call};\n{} }}", c_report(&r.t, "r")).unwrap()
            }
            None => writeln!(main, "  {call};").unwrap(),
        }
        writeln!(want, "T{i} c->fir\n{args_report}{ret_report}").unwrap();
        // C calls FIR through `...`: C passes every composite as it is, FIR reads a twin.
        let va = sig.va();
        if va.is_some() {
            writeln!(main, "  puts(\"T{i} c->fir va\");").unwrap();
            let call = format!("fir_va{i}({}, {})", sig.params.len(), cargs.join(", "));
            match &sig.ret {
                Some(r) => {
                    writeln!(main, "  {{ {cret} r = {call};\n{} }}", c_report(&r.t, "r")).unwrap()
                }
                None => writeln!(main, "  {call};").unwrap(),
            }
            writeln!(want, "T{i} c->fir va\n{args_report}{ret_report}").unwrap();
        }
        // FIR's callees.
        let mut g = FirGen {
            out: String::new(),
            n: 0,
        };
        let names: Vec<String> = (0..sig.params.len()).map(|k| format!("%a{k}")).collect();
        for (p, v) in sig.params.iter().zip(&names) {
            g.report(&p.t, v);
        }
        let ret_fir = |g: &mut FirGen| match &sig.ret {
            Some(r) => {
                let v = g.make(&r.t, &mut r.vals.iter());
                writeln!(g.out, "  func.ret {v}").unwrap();
            }
            None => g.out.push_str("  func.ret\n"),
        };
        g.out.push_str("  %base: ptr = mem.global @base\n");
        ret_fir(&mut g);
        let params: Vec<String> = names
            .iter()
            .zip(&fps)
            .map(|(n, t)| format!("{n}: {t}"))
            .collect();
        writeln!(
            f,
            "func @callee{i}({}){fret} {{\n{}}}",
            params.join(", "),
            g.out
        )
        .unwrap();
        let mut g = FirGen {
            out: String::new(),
            n: 0,
        };
        g.out
            .push_str("  %ap: ptr = mem.stack.of va_list, align 8\n  va.start %ap\n");
        let va_params: Vec<(&Arg, Va)> = match &va {
            Some(how) => sig.params.iter().zip(how.iter().copied()).collect(),
            None => Vec::new(),
        };
        for (k, (p, how)) in va_params.iter().enumerate() {
            let v = format!("%v{k}");
            if *how == Va::Twin {
                writeln!(g.out, "  {v}: {} = va.arg %ap", twin(&p.t)).unwrap();
                g.report_twin(&p.t, &v);
                continue;
            }
            let pt = promoted(&p.t);
            writeln!(g.out, "  {v}: {} = va.arg %ap", fir_ty(&pt)).unwrap();
            let v = match (&p.t, &pt) {
                (T::S(F32), _) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: f32 = float.trunc {v}").unwrap();
                    n
                }
                (T::S(s @ (I8 | I16)), _) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: {} = int.trunc.wrap {v}", s.fir()).unwrap();
                    n
                }
                _ => v,
            };
            g.report(&p.t, &v);
        }
        g.out
            .push_str("  va.end %ap\n  %base: ptr = mem.global @base\n");
        ret_fir(&mut g);
        writeln!(f, "func @va{i}(%n: i32, ...){fret} {{\n{}}}", g.out).unwrap();
        // FIR calls C (which reads through its pointers), and its own functions.
        writeln!(
            f,
            "extern func @c_callee{i}({}){fret} effects[read(args)] assume",
            fps.join(", ")
        )
        .unwrap();
        writeln!(
            f,
            "extern func @c_va{i}(i32, ...){fret} effects[read(args)] assume"
        )
        .unwrap();
        writeln!(c, "{cret} c_callee{i}({}) {{", cparams(true)).unwrap();
        for (k, p) in sig.params.iter().enumerate() {
            c.push_str(&c_report(&p.t, &format!("a{k}")));
        }
        let rc = ret_c(&mut defs);
        c.push_str(&rc);
        c.push_str("}\n");
        writeln!(
            c,
            "{cret} c_va{i}(int n, ...) {{\n  va_list ap;\n  va_start(ap, n);"
        )
        .unwrap();
        for (k, (p, _)) in va_params.iter().enumerate() {
            let pt = promoted(&p.t);
            writeln!(
                c,
                "  {} a{k} = va_arg(ap, {});",
                defs.ty(&p.t),
                defs.ty(&pt)
            )
            .unwrap();
            c.push_str(&c_report(&p.t, &format!("a{k}")));
        }
        c.push_str("  va_end(ap);\n");
        c.push_str(&rc);
        c.push_str("}\n");
        let mut g = FirGen {
            out: String::new(),
            n: 0,
        };
        g.out.push_str("  %base: ptr = mem.global @base\n");
        let fargs: Vec<String> = sig
            .params
            .iter()
            .map(|p| g.make(&p.t, &mut p.vals.iter()))
            .collect();
        // Through `...`, the promoted types, or the twins.
        let mut vargs = Vec::new();
        for ((p, how), a) in va_params.iter().zip(&fargs) {
            vargs.push(match (&p.t, how) {
                (t, Va::Twin) => g.make_twin(t, &p.vals),
                (T::S(F32), _) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: f64 = float.ext {a}").unwrap();
                    n
                }
                (T::S(I8 | I16), _) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: i32 = int.sext {a}").unwrap();
                    n
                }
                _ => a.clone(),
            });
        }
        let mut calls = vec![format!("func.call @c_callee{i}({})", fargs.join(", "))];
        if va.is_some() {
            calls.push(format!(
                "func.call @c_va{i}(%cnt, ... {})",
                vargs.join(", ")
            ));
        }
        calls.push(format!("func.call @callee{i}({})", fargs.join(", ")));
        if va.is_some() {
            calls.push(format!("func.call @va{i}(%cnt, ... {})", vargs.join(", ")));
        }
        writeln!(g.out, "  %cnt: i32 = int.const {}", sig.params.len()).unwrap();
        let ncalls = calls.len();
        for (k, call) in calls.into_iter().enumerate() {
            match &sig.ret {
                Some(r) => {
                    let v = format!("%r{k}");
                    writeln!(g.out, "  {v}: {} = {call}", fir_ty(&r.t)).unwrap();
                    g.report(&r.t, &v);
                }
                None => writeln!(g.out, "  {call}").unwrap(),
            }
        }
        g.out.push_str("  func.ret\n");
        writeln!(f, "func @drive{i}() {{\n{}}}", g.out).unwrap();
        // The same calls in the interpreter, with the buffer a FIR allocation.
        writeln!(
            f,
            "func @idrive{i}() {{\n  %buf: ptr = mem.global @buf\n  func.call @set_base(%buf)\n  func.call @drive{i}()\n  func.ret\n}}"
        )
        .unwrap();
        writeln!(c, "void fir_drive{i}(void) __asm__(\"fir_drive{i}\");").unwrap();
        writeln!(main, "  puts(\"T{i} fir->c\");\n  fir_drive{i}();").unwrap();
        writeln!(want, "T{i} fir->c").unwrap();
        for _ in 0..ncalls {
            want.push_str(&args_report);
            want.push_str(&ret_report);
        }
    }
    main.push_str("  return 0;\n}\n");
    let head = "#include <stdarg.h>\n#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n\
        char cbuf[64];\n\
        void rec_i(int64_t v) { printf(\"i %lld\\n\", (long long)v); }\n\
        void rec_f(double v) { uint64_t b; memcpy(&b, &v, 8); printf(\"f %016llx\\n\", (unsigned long long)b); }\n\
        void rec_p(char *p) { if (p) printf(\"p %ld %d\\n\", (long)(p - cbuf), *(unsigned char *)p); else printf(\"p null\\n\"); }\n\
        void fir_set_base(char *p) __asm__(\"fir_set_base\");\n";
    let csrc = format!("{head}{}{c}{main}", defs.defs);
    // `puts` adds the newline the expected text has after each header; reports follow.
    let want = want.replace("\n\n", "\n");
    (csrc, f, want)
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The torture test's counts.
#[derive(Default)]
struct Counts {
    leaves: usize,
    gp_stack: usize,
    fp_stack: usize,
    scalar_after: usize,
    refused: usize,
    va: usize,
    twins: usize,
    auto: usize,
    reordered_hfa: usize,
    interp_runs: usize,
}

fn has_auto(t: &T) -> bool {
    match t {
        T::Struct { policy, fields } => *policy == Policy::Auto || fields.iter().any(has_auto),
        T::Array(_, e) => has_auto(e),
        _ => false,
    }
}

/// Whether an HFA's members are in a different order in memory than declared.
fn reordered_hfa(t: &T) -> bool {
    if matches!(t, T::S(_)) || !matches!(class_of(t), Class::Hfa(..)) {
        return false;
    }
    let mut ls = Vec::new();
    leaf_offs(t, 0, &mut ls);
    ls.windows(2).any(|w| w[0].0 > w[1].0)
}

#[test]
fn structs_cross_the_c_abi_both_ways() {
    // The signatures are checked against AAPCS64 as Linux defines it, built for Linux; macOS's
    // C compiler follows Apple's variant (variadic arguments on the stack), and the macOS dev
    // shell has no Linux toolchain or qemu-user, so `cargo xtask verify` declares a host gap.
    if cfg!(target_os = "macos") {
        let ev = Evidence::new("abi_torture");
        common::evidence::host_gap(
            &ev,
            "checks Linux's AAPCS64 against a Linux C compiler; macOS has Apple's variant and no Linux toolchain",
        );
        ev.write();
        return;
    }
    let native = cfg!(target_arch = "aarch64") && cfg!(target_os = "linux");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("aarch64-unknown-linux-gnu-cc") => {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => {
            require("no AArch64 C compiler (set FIR_CC, or use the dev shell)");
            return;
        }
    };
    let runner = if native {
        None
    } else if on_path("qemu-aarch64") {
        Some("qemu-aarch64")
    } else {
        require("no qemu-aarch64");
        return;
    };
    let count: usize = std::env::var("FIR_ABI")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(240);
    let seed: u64 = std::env::var("FIR_ABI_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let sigs: Vec<Sig> = (0..count).map(|_| gen_sig(&mut rng)).collect();
    let dir: PathBuf =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("fir-abi-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut failures = Vec::new();
    let mut n = Counts::default();
    let (refused, sigs): (Vec<Sig>, Vec<Sig>) = sigs.into_iter().partition(Sig::refused);
    // Instruction selection refuses each of these, whatever else the module has.
    for sig in &refused {
        n.refused += 1;
        let (_, fsrc, _) = sources(std::slice::from_ref(sig));
        let m = fir::parse_module(&fsrc).unwrap();
        fir::verify_module(&m).unwrap();
        match fir::backend::prepare(&m, false).and_then(|m| a64::compile(&m, &options())) {
            Err(e) if e.contains("can't be passed by value in registers") => {}
            r => failures.push(format!(
                "a signature with a split pointer wasn't refused ({:?}):\n{fsrc}",
                r.map(|_| "compiled")
            )),
        }
    }
    for s in &sigs {
        let u = s.uses();
        n.gp_stack += usize::from(u.gp_stack);
        n.fp_stack += usize::from(u.fp_stack);
        n.scalar_after += usize::from(u.scalar_after);
        n.va += usize::from(s.va().is_some());
        n.twins += s
            .va()
            .map_or(0, |v| v.iter().filter(|&&k| k == Va::Twin).count());
        let args = s.params.iter().chain(&s.ret);
        n.auto += usize::from(args.clone().any(|a| has_auto(&a.t)));
        n.reordered_hfa += usize::from(args.clone().any(|a| reordered_hfa(&a.t)));
        n.leaves += args.map(|a| a.vals.len()).sum::<usize>();
    }
    for (b, batch) in sigs.chunks(40).enumerate() {
        let (csrc, fsrc, want) = sources(batch);
        for opt in [false, true] {
            let name = format!("b{b}{}", if opt { "-O" } else { "" });
            match run_batch(&dir, &name, opt, &cc, runner, &csrc, &fsrc, batch.len()) {
                Ok((got, runs)) if got == want => n.interp_runs += runs,
                Ok((got, _)) => {
                    let line = want
                        .lines()
                        .zip(got.lines())
                        .position(|(a, g)| a != g)
                        .unwrap_or(0);
                    let header = want
                        .lines()
                        .take(line + 1)
                        .filter(|l| l.starts_with('T'))
                        .last();
                    failures.push(format!(
                        "{name}: first difference at line {line} (in {header:?}): want {:?}, got {:?}",
                        want.lines().nth(line),
                        got.lines().nth(line)
                    ));
                    std::fs::write(dir.join(format!("{name}.want")), &want).unwrap();
                    std::fs::write(dir.join(format!("{name}.got")), &got).unwrap();
                }
                Err(e) => failures.push(format!("{name}: {e}")),
            }
        }
    }
    eprintln!(
        "{count} signatures (seed {seed}): {} compiled with and without -O, {} leaves each way, through `...` ({} signatures, {} composites as twins), and FIR to FIR; {} exhaust the x registers and {} the FP ones, {} pass a scalar after a composite that went on the stack; {} with struct<auto>, {} with an HFA reordered in memory; {} refused (a split pointer); {} interpreter runs (MFIR and LFIR) agree",
        sigs.len(),
        n.leaves,
        n.va,
        n.twins,
        n.gp_stack,
        n.fp_stack,
        n.scalar_after,
        n.auto,
        n.reordered_hfa,
        n.refused,
        n.interp_runs
    );
    let ev = Evidence::new("abi_torture");
    ev.count("signatures", count as u64);
    ev.count("leaves", n.leaves as u64);
    ev.count("batches", sigs.len().div_ceil(40) as u64);
    ev.count("gp_exhausted", n.gp_stack as u64);
    ev.count("fp_exhausted", n.fp_stack as u64);
    ev.count("scalar_after_stack_composite", n.scalar_after as u64);
    ev.count("variadic_twins", n.twins as u64);
    ev.count("auto", n.auto as u64);
    ev.count("reordered_hfa", n.reordered_hfa as u64);
    ev.count("refused_split_pointer", n.refused as u64);
    ev.count("interpreter_runs", n.interp_runs as u64);
    ev.count("failures", failures.len() as u64);
    ev.write();
    if failures.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} failures (files in {}):\n{}",
        failures.len(),
        dir.display(),
        failures.join("\n")
    );
}

fn options() -> a64::Options {
    a64::Options {
        os: a64::Os::Linux,
        prefix: "fir_".to_owned(),
        extern_prefix: String::new(),
        debug_lines: false,
    }
}

/// A run's events with allocation numbers dropped (the machines number allocations their own
/// way), so a pointer shows only whether it has provenance (`#`) or is an address (`0x…`).
fn events(line: &str) -> String {
    let mut out = String::new();
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '#' {
            while chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                chars.next();
            }
        }
    }
    out
}

/// Whether `got` refines `want`: the same tokens, except where `want` has `poison` (a twin's
/// padding bytes), which any value refines.
fn refines(want: &str, got: &str) -> bool {
    let toks = |s: &'_ str| -> Vec<String> {
        s.split([' ', ',', ';', '{', '}', '(', ')'])
            .filter(|t| !t.is_empty())
            .map(str::to_owned)
            .collect()
    };
    let (w, g) = (toks(want), toks(got));
    w.len() == g.len() && w.iter().zip(&g).all(|(a, b)| a == b || a == "poison")
}

/// Each `@idrive` of the module (`n` of them) in the interpreter, as MFIR and as LFIR before
/// and after register allocation: the events must agree (LFIR may pick a value for `poison`).
/// How many runs agreed.
fn interp_check(m: &fir::Module, n: usize) -> Result<usize, String> {
    let mut mm = a64::select(m)?;
    let before = a64::lfir::to_module(m, &mm);
    a64::allocate(m, &mut mm)?;
    let after = a64::lfir::to_module(m, &mm);
    for i in 0..n {
        let f = format!("idrive{i}");
        let run = |m: &fir::Module, fuel| {
            fir::interp::run_detail(m, &f, &[], fuel, false).map(|r| events(&r.line))
        };
        let want = run(m, 1_000_000)?;
        if !want.ends_with("returned") {
            return Err(format!("@{f} in the interpreter: {want}"));
        }
        for (what, l) in [("before", &before), ("after", &after)] {
            let got = run(l, 64_000_000)?;
            if !refines(&want, &got) {
                return Err(format!(
                    "@{f}: LFIR {what} register allocation differs:\n  MFIR {want}\n  LFIR {got}"
                ));
            }
        }
    }
    Ok(3 * n)
}

/// Compile and run one batch, giving its output, after checking its FIR calls in the
/// interpreter (and how many interpreter runs agreed).
#[allow(clippy::too_many_arguments)]
fn run_batch(
    dir: &Path,
    name: &str,
    opt: bool,
    cc: &str,
    runner: Option<&str>,
    csrc: &str,
    fsrc: &str,
    n: usize,
) -> Result<(String, usize), String> {
    let m = fir::parse_module(fsrc).map_err(|e| format!("FIR doesn't parse: {e}"))?;
    fir::verify_module(&m).map_err(|e| format!("FIR doesn't verify: {e}"))?;
    std::fs::write(dir.join(format!("{name}.fir")), fsrc).unwrap();
    let m = fir::backend::prepare(&m, opt)?;
    let runs = interp_check(&m, n)?;
    let asm = a64::compile(&m, &options())?;
    let (c, s, bin) = (
        dir.join(format!("{name}.c")),
        dir.join(format!("{name}.s")),
        dir.join(name),
    );
    std::fs::write(&c, csrc).unwrap();
    std::fs::write(&s, asm).unwrap();
    let out = Command::new(cc)
        .args(["-O1", "-w"])
        .arg(&c)
        .arg(&s)
        .arg("-o")
        .arg(&bin)
        .output()
        .map_err(|e| format!("running {cc}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{cc} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let out = match runner {
        Some(r) => Command::new(r).arg(&bin).output(),
        None => Command::new(&bin).output(),
    }
    .map_err(|e| format!("running: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "exit {:?}: {}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok((String::from_utf8_lossy(&out.stdout).into_owned(), runs))
}
