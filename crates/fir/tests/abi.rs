//! ABI torture (decision: C ABI for aggregates): random signatures of structs and arrays (fields
//! of `i8`…`i64`, `f32`, `f64`, `ptr`, arrays, nested and packed structs, 16-byte aligned ones)
//! and scalars, compiled on one side by the AArch64 C compiler (GCC in the dev shell) and on the
//! other by FIR, then run (natively on AArch64, under `qemu-aarch64` elsewhere). Every field must
//! arrive in each direction:
//!
//! * C calls a FIR function with constant arguments; FIR reports every leaf it received and
//!   returns a constant result, whose leaves C reports.
//! * C calls a variadic FIR function with the same arguments after `...` (C's promotions turn a
//!   narrow integer into an `int` and a `float` into a `double`, which FIR reads and narrows);
//!   FIR reads them with `va.arg` and reports them.
//! * FIR calls a C function, and a variadic C function, with constant arguments; C reports them
//!   and returns a constant result, whose leaves FIR reports.
//!
//! The expected output is computed here from the values. `FIR_ABI=N` sets how many signatures
//! (default 240), `FIR_ABI_SEED` the seed (default 1); `FIR_CC` the C compiler.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use fir::backend::aarch64 as a64;

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

/// A type of the signatures.
#[derive(Clone, Debug)]
enum T {
    S(Scalar),
    Struct {
        packed: bool,
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

fn gen_scalar(rng: &mut Rng, floats: bool) -> Scalar {
    if floats {
        return if rng.chance(50) { F32 } else { F64 };
    }
    [I8, I16, I32, I64, F32, F64, Ptr][rng.below(7) as usize]
}

fn gen_struct(rng: &mut Rng, depth: u32) -> T {
    match rng.below(10) {
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
                packed: false,
                fields,
            }
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
            let packed = !fields.iter().any(|f| matches!(f, T::Align16)) && rng.chance(8);
            T::Struct { packed, fields }
        }
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
        T::Struct { packed, fields } => format!(
            "struct<{}>{{{}}}",
            if *packed { "packed" } else { "C" },
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
                    T::Struct { fields, .. } => fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| match f {
                            T::Align16 => format!(" __int128 f{i}[0];"),
                            T::S(s) => format!(" {} f{i};", s.c()),
                            f => format!(" {} f{i};", self.ty(f)),
                        })
                        .collect::<String>(),
                    T::Array(n, e) => format!(" {} e[{n}];", self.ty(e)),
                    _ => unreachable!(),
                };
                let packed = matches!(t, T::Struct { packed: true, .. });
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
            // Designated by position: an aligned field takes no initializer.
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

/// The expected report of a leaf.
fn report(v: V) -> String {
    match v {
        V::Int(x) => format!("i {x}\n"),
        V::F32(x) => format!("f {:016x}\n", f64::from(x).to_bits()),
        V::F64(x) => format!("f {:016x}\n", x.to_bits()),
        V::Ptr(Some(o)) => format!("p {o}\n"),
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

    /// A value of type `t` made of the next leaves.
    fn make(&mut self, t: &T, vals: &mut std::slice::Iter<'_, V>) -> String {
        match t {
            T::S(s) => {
                let v = self.fresh();
                match (vals.next().unwrap(), s) {
                    (V::Int(x), _) => {
                        writeln!(self.out, "  {v}: {} = int.const {x}", s.fir()).unwrap()
                    }
                    (V::F32(x), _) => writeln!(self.out, "  {v}: f32 = float.const {x:?}").unwrap(),
                    (V::F64(x), _) => writeln!(self.out, "  {v}: f64 = float.const {x:?}").unwrap(),
                    (V::Ptr(None), _) => writeln!(self.out, "  {v}: ptr = ptr.null").unwrap(),
                    (V::Ptr(Some(o)), _) => {
                        let b = self.fresh();
                        let k = self.fresh();
                        writeln!(self.out, "  {b}: ptr = mem.load %base, align 8").unwrap();
                        writeln!(self.out, "  {k}: i64 = int.const {o}").unwrap();
                        writeln!(self.out, "  {v}: ptr = ptr.offset.wrap {b}, {k}").unwrap();
                    }
                }
                v
            }
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

/// Whether FIR takes this type as a variadic argument: scalars and C composites (`struct<C>` and
/// nonempty arrays), so no packed struct or zero-length array.
fn va_ok(t: &T) -> bool {
    match t {
        T::S(_) => true,
        T::Struct { packed, fields } => !packed && fields.iter().all(va_ok),
        T::Array(n, e) => *n > 0 && va_ok(e),
        T::Align16 => false,
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

fn gen_arg(rng: &mut Rng, t: T) -> Arg {
    let mut ls = Vec::new();
    leaves(&t, "", &[], &mut ls);
    let vals = ls.iter().map(|(s, ..)| gen_value(rng, *s)).collect();
    Arg { t, vals }
}

fn gen_sig(rng: &mut Rng) -> Sig {
    let most = if rng.chance(30) { 12 } else { 5 };
    let n = 1 + rng.below(most) as usize;
    let params = (0..n)
        .map(|_| {
            let t = if rng.chance(75) {
                gen_struct(rng, 0)
            } else {
                T::S(gen_scalar(rng, false))
            };
            gen_arg(rng, t)
        })
        .collect();
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
         extern func @rec_p(ptr) effects[] assume\n\
         global @base: ptr = null\n\
         func @set_base(%p: ptr) {\n  %b: ptr = mem.global @base\n  mem.store ptr %p, %b, align 8\n  func.ret\n}\n",
    );
    let mut want = String::new();
    let mut main = String::from("int main(void) {\n  fir_set_base(cbuf);\n");
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
        // C calls FIR through `...`.
        let va = sig.params.iter().all(|p| va_ok(&p.t));
        if va {
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
        let va_params: &[Arg] = if va { &sig.params } else { &[] };
        for (k, p) in va_params.iter().enumerate() {
            let pt = promoted(&p.t);
            let v = format!("%v{k}");
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
        // FIR calls C.
        writeln!(
            f,
            "extern func @c_callee{i}({}){fret} effects[] assume",
            fps.join(", ")
        )
        .unwrap();
        writeln!(f, "extern func @c_va{i}(i32, ...){fret} effects[] assume").unwrap();
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
        for (k, p) in va_params.iter().enumerate() {
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
        // Through `...`, the promoted types.
        let mut vargs = Vec::new();
        for (p, a) in sig.params.iter().zip(&fargs) {
            vargs.push(match &p.t {
                T::S(F32) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: f64 = float.ext {a}").unwrap();
                    n
                }
                T::S(I8 | I16) => {
                    let n = g.fresh();
                    writeln!(g.out, "  {n}: i32 = int.sext {a}").unwrap();
                    n
                }
                _ => a.clone(),
            });
        }
        let mut calls = vec![format!("func.call @c_callee{i}({})", fargs.join(", "))];
        if va {
            calls.push(format!(
                "func.call @c_va{i}(%cnt, ... {})",
                vargs.join(", ")
            ));
        }
        for (k, call) in calls.into_iter().enumerate() {
            if k == 1 {
                writeln!(g.out, "  %cnt: i32 = int.const {}", sig.params.len()).unwrap();
            }
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
        writeln!(c, "void fir_drive{i}(void) __asm__(\"fir_drive{i}\");").unwrap();
        writeln!(main, "  puts(\"T{i} fir->c\");\n  fir_drive{i}();").unwrap();
        if va {
            writeln!(
                want,
                "T{i} fir->c\n{args_report}{ret_report}{args_report}{ret_report}"
            )
            .unwrap();
        } else {
            writeln!(want, "T{i} fir->c\n{args_report}{ret_report}").unwrap();
        }
    }
    main.push_str("  return 0;\n}\n");
    let head = "#include <stdarg.h>\n#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n\
        char cbuf[64];\n\
        void rec_i(int64_t v) { printf(\"i %lld\\n\", (long long)v); }\n\
        void rec_f(double v) { uint64_t b; memcpy(&b, &v, 8); printf(\"f %016llx\\n\", (unsigned long long)b); }\n\
        void rec_p(char *p) { if (p) printf(\"p %ld\\n\", (long)(p - cbuf)); else printf(\"p null\\n\"); }\n\
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

#[test]
fn structs_cross_the_c_abi_both_ways() {
    let native = cfg!(target_arch = "aarch64") && cfg!(target_os = "linux");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("aarch64-unknown-linux-gnu-cc") => {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => {
            eprintln!("skipped: no AArch64 C compiler (set FIR_CC, or use the dev shell)");
            return;
        }
    };
    let runner = if native {
        None
    } else if on_path("qemu-aarch64") {
        Some("qemu-aarch64")
    } else {
        eprintln!("skipped: no qemu-aarch64");
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
    let (mut leaves_n, mut stack_args) = (0usize, 0usize);
    for (b, batch) in sigs.chunks(40).enumerate() {
        let (csrc, fsrc, want) = sources(batch);
        leaves_n += batch
            .iter()
            .map(|s| {
                s.params.iter().map(|p| p.vals.len()).sum::<usize>()
                    + s.ret.as_ref().map_or(0, |r| r.vals.len())
            })
            .sum::<usize>();
        stack_args += batch.iter().filter(|s| s.params.len() > 4).count();
        match run_batch(&dir, b, &cc, runner, &csrc, &fsrc) {
            Ok(got) if got == want => {}
            Ok(got) => {
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
                    "batch {b}: first difference at line {line} (in {header:?}): want {:?}, got {:?}",
                    want.lines().nth(line),
                    got.lines().nth(line)
                ));
                std::fs::write(dir.join(format!("b{b}.want")), &want).unwrap();
                std::fs::write(dir.join(format!("b{b}.got")), &got).unwrap();
            }
            Err(e) => failures.push(format!("batch {b}: {e}")),
        }
    }
    eprintln!(
        "{count} signatures (seed {seed}), {leaves_n} leaves each way and through `...`, {stack_args} with more than four arguments"
    );
    if failures.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} batches differ (files in {}):\n{}",
        failures.len(),
        dir.display(),
        failures.join("\n")
    );
}

/// Compile and run one batch, giving its output.
fn run_batch(
    dir: &Path,
    b: usize,
    cc: &str,
    runner: Option<&str>,
    csrc: &str,
    fsrc: &str,
) -> Result<String, String> {
    let m = fir::parse_module(fsrc).map_err(|e| format!("FIR doesn't parse: {e}"))?;
    fir::verify_module(&m).map_err(|e| format!("FIR doesn't verify: {e}"))?;
    let m = fir::backend::prepare(&m, b % 2 == 1)?;
    let o = a64::Options {
        os: a64::Os::Linux,
        prefix: "fir_".to_owned(),
        extern_prefix: String::new(),
    };
    let asm = a64::compile(&m, &o)?;
    let (c, s, bin) = (
        dir.join(format!("b{b}.c")),
        dir.join(format!("b{b}.s")),
        dir.join(format!("b{b}")),
    );
    std::fs::write(&c, csrc).unwrap();
    std::fs::write(&s, asm).unwrap();
    std::fs::write(dir.join(format!("b{b}.fir")), fsrc).unwrap();
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
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}
