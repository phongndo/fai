//! What the native backend tests share (`aarch64.rs`, `x86_64.rs`): the C harness that calls a
//! compiled module's functions with a run's arguments and prints the outcome in `fir run`'s
//! format, the test runtime (trap handler, printing), running binaries, and comparing their output
//! with the interpreter's (normalizing what the semantics leaves to the target, and the address
//! layouts that excuse differences only in what may depend on addresses). The harness is plain C
//! over 64-bit integers, pointers, floats, and C structs, so it serves any target whose calling
//! convention matches C's for those; see `aarch64.rs` for what each part checks.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::taint::matches;
use fir::{Module, Ty};

pub struct Toolchain {
    pub cc: String,
    /// The emulator binaries run under, if not natively.
    pub runner: Option<String>,
    pub runtime: PathBuf,
}

pub fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The test runtime: the trap handler and value printing, in `fir run`'s format.
pub const RUNTIME: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *reasons[] = {"div0", "overflow", "shift", "oom", "bounds", "tag", "convert"};

/* The exception slot (decision: Exceptions at run time): a nonzero flag while an exception is
   pending, and its value. The compiled code defines it weakly; this definition wins. */
struct fir_exn { void *flag; void *value; } __fir_exn;

void __fir_trap(uint32_t reason, uint32_t line, uint32_t col) {
    printf("trap %s", reason < 7 ? reasons[reason] : "?");
    if (line != 0xffffffffu) printf(" @%u:%u", line, col);
    printf("\n");
    fflush(stdout);
    exit(0);
}

/* Floats from their bits, and back. */
double fir_f64(uint64_t b) { double x; memcpy(&x, &b, 8); return x; }
float fir_f32(uint32_t b) { float x; memcpy(&x, &b, 4); return x; }
uint64_t fir_b64(double x) { uint64_t b; memcpy(&b, &x, 8); return b; }
uint64_t fir_b32(float x) { uint32_t b; memcpy(&b, &x, 4); return b; }

/* One value: 'i' an iW, 'p' a pointer, 'b' a bW, 'f' an fW (as its bits, which the test
   renders). */
void fir_print(char kind, unsigned w, uint64_t v) {
    if (kind == 'f') {
        printf("f%u 0x%llx", w, (unsigned long long)(w == 32 ? v & 0xffffffffull : v));
    } else if (kind == 'p') {
        printf(v == 0 ? "ptr null" : "ptr ?");
    } else if (kind == 'b') {
        printf("b%u (", w);
        for (unsigned i = 0; i < w / 8; i++) printf(i ? ", 0x%x" : "0x%x", (unsigned)((v >> (8 * i)) & 0xff));
        printf(")");
    } else if (w == 1) {
        printf("i1 %u", (unsigned)(v & 1));
    } else {
        uint64_t m = w >= 64 ? ~0ull : ((1ull << w) - 1);
        uint64_t x = v & m;
        if (w < 64 && (x >> (w - 1)) & 1) x |= ~m;
        printf("i%u %lld", w, (long long)x);
    }
}
"#;

/// The C types of a module's composites (decision: C ABI for aggregates): a struct with the
/// FIR type's layout and AAPCS64 class for each, named by its text. A `struct<C>`'s fields are
/// its parts in order, a `struct<packed>` is packed, a `struct<auto>`'s fields are in its layout's
/// order, and an array is a struct holding a C array; integers and bytes of 8 to 64 bits are
/// `uintN_t` (others `unsigned _BitInt(N)`, which C lays out as FIR does), pointers `void *`.
#[derive(Default)]
pub struct CTypes {
    defs: String,
    names: Vec<String>,
}

impl CTypes {
    /// The C type of a value of type `t` of table `types` (scalars as they travel).
    fn ty(&mut self, types: &fir::Types, sp: &fir::SpaceCfg, t: Ty) -> String {
        if !types.is_composite(t) {
            return c_ty(t).to_owned();
        }
        let key = types.show(t);
        if let Some(i) = self.names.iter().position(|n| *n == key) {
            return format!("struct c{i}");
        }
        let fields: Vec<(String, String)> = match types.shape_of(t) {
            Some(fir::Shape::Struct(p, fs)) => {
                let fs = fs.to_vec();
                let mut order: Vec<usize> = (0..fs.len()).collect();
                if p == fir::Policy::Auto {
                    order.sort_by_key(|&i| std::cmp::Reverse(types.align(sp, fs[i])));
                }
                order
                    .into_iter()
                    .map(|i| (self.field_ty(types, sp, fs[i]), format!("f{i}")))
                    .collect()
            }
            Some(fir::Shape::Array(n, e)) => {
                vec![(self.field_ty(types, sp, e), format!("e[{n}]"))]
            }
            _ => Vec::new(),
        };
        let packed = matches!(
            types.shape_of(t),
            Some(fir::Shape::Struct(fir::Policy::Packed, _))
        );
        let i = self.names.len();
        self.names.push(key);
        let body: String = fields
            .iter()
            .map(|(ty, name)| format!(" {ty} {name};"))
            .collect();
        let attr = if packed {
            " __attribute__((packed))"
        } else {
            ""
        };
        writeln!(self.defs, "struct{attr} c{i} {{{body} }};").unwrap();
        format!("struct c{i}")
    }

    /// The C type of a part of a composite.
    fn field_ty(&mut self, types: &fir::Types, sp: &fir::SpaceCfg, t: Ty) -> String {
        match t {
            Ty::Int(w) | Ty::Byte(w) if [8, 16, 32, 64].contains(&w) => format!("uint{w}_t"),
            Ty::Int(w) | Ty::Byte(w) => format!("unsigned _BitInt({w})"),
            Ty::Ptr => "void *".to_owned(),
            _ => self.ty(types, sp, t),
        }
    }

    /// Code printing the C expression `e` of FIR type `t` as `fir run` renders the value.
    fn print(&mut self, types: &fir::Types, t: Ty, e: &str) -> String {
        let parts: Vec<(Ty, String)> = match types.shape_of(t) {
            Some(fir::Shape::Struct(_, fs)) => fs
                .iter()
                .enumerate()
                .map(|(i, &f)| (f, format!("{e}.f{i}")))
                .collect(),
            Some(fir::Shape::Array(n, el)) => (0..n).map(|j| (el, format!("{e}.e[{j}]"))).collect(),
            _ => {
                let e = match t {
                    Ty::Ptr => format!("(uint64_t)(uintptr_t)({e})"),
                    Ty::Float(_) => e.to_owned(),
                    _ => format!("(uint64_t)({e})"),
                };
                return c_print(t, &e);
            }
        };
        let mut out = String::from("printf(\"{\"); ");
        for (k, (pt, pe)) in parts.into_iter().enumerate() {
            if k > 0 {
                out.push_str("printf(\", \"); ");
            }
            out.push_str(&self.print(types, pt, &pe));
            out.push(' ');
        }
        out.push_str("printf(\"}\");");
        out
    }
}

/// A value type's kind and width for `fir_print`.
pub fn kind(t: Ty) -> (char, u32) {
    match t {
        Ty::Int(w) => ('i', w),
        Ty::Byte(w) => ('b', w),
        Ty::Float(f) => ('f', f.width()),
        _ => ('p', 64),
    }
}

/// The C type a value of type `t` travels as.
pub fn c_ty(t: Ty) -> &'static str {
    match t {
        Ty::Float(fir::FloatTy::F32) => "float",
        Ty::Float(fir::FloatTy::F64) => "double",
        _ => "uint64_t",
    }
}

/// `fir_print` of the C expression `e` holding a value of type `t`.
pub fn c_print(t: Ty, e: &str) -> String {
    let (kd, w) = kind(t);
    let bits = match t {
        Ty::Float(fir::FloatTy::F32) => format!("fir_b32({e})"),
        Ty::Float(fir::FloatTy::F64) => format!("fir_b64({e})"),
        _ => e.to_owned(),
    };
    format!("fir_print('{kd}', {w}, {bits});")
}

/// The C type of results `rets` under the backend's convention, defining the struct it needs:
/// one result as itself; two as a struct of 8-byte fields (an HFA of `float`s or `double`s when
/// both are floats of one format); more as a struct of 8-byte slots in memory.
pub fn c_ret(rets: &[Ty], defs: &mut String) -> String {
    let name: String = rets
        .iter()
        .map(|&t| match t {
            Ty::Float(f) => f.name().to_owned(),
            _ => "i".to_owned(),
        })
        .collect::<Vec<_>>()
        .join("_");
    match rets.len() {
        0 => "void".to_owned(),
        1 => c_ty(rets[0]).to_owned(),
        n => {
            let hfa = rets[0].is_float() && rets.iter().all(|&t| t == rets[0]);
            let fields: Vec<String> = rets
                .iter()
                .enumerate()
                .map(|(i, &t)| match t {
                    _ if n > 2 => format!("union fir_slot r{i};"),
                    Ty::Float(fir::FloatTy::F32) if !hfa => {
                        format!("union {{ float f; uint64_t pad; }} r{i};")
                    }
                    t => format!("{} r{i};", c_ty(t)),
                })
                .collect();
            let def = format!("struct r_{name} {{ {} }};\n", fields.join(" "));
            if !defs.contains(&def) {
                defs.push_str(&def);
            }
            format!("struct r_{name}")
        }
    }
}

/// Field `i` of a result struct of type `rets`, as a C expression of the value's C type.
pub fn c_field(rets: &[Ty], i: usize, var: &str) -> String {
    let hfa = rets[0].is_float() && rets.iter().all(|&t| t == rets[0]);
    match rets[i] {
        Ty::Float(fir::FloatTy::F32) if rets.len() > 2 || !hfa => format!("{var}.r{i}.f"),
        Ty::Float(fir::FloatTy::F64) if rets.len() > 2 => format!("{var}.r{i}.d"),
        _ if rets.len() > 2 => format!("{var}.r{i}.i"),
        _ => format!("{var}.r{i}"),
    }
}

/// An argument as `fir run` reads it, as its C type's value (`poison` passes as 0).
pub fn c_arg(t: Ty, s: &str) -> String {
    match (t, s) {
        (_, "poison") | (_, "null") => "0".to_owned(),
        (Ty::Float(f), _) => {
            let bits = fir::float::parse_lit(s)
                .and_then(|l| l.to_bits(f))
                .unwrap_or_default();
            match f {
                fir::FloatTy::F32 => format!("fir_f32({bits:#x}u)"),
                fir::FloatTy::F64 => format!("fir_f64({bits:#x}ull)"),
            }
        }
        _ => {
            let n: num_bigint::BigInt = fir::interp::parse_int(s).unwrap_or_default();
            let m = num_bigint::BigInt::from(1) << 64;
            let v = ((n % &m) + &m) % &m;
            format!("{v}ull")
        }
    }
}

/// A variadic argument as a run line writes it (`i32 5`): its type and value.
pub fn typed_arg(s: &str) -> (Ty, &str) {
    let (t, v) = s.split_once(' ').unwrap_or(("i64", s));
    let ty = match t {
        "ptr" => Ty::Ptr,
        "f32" => Ty::Float(fir::FloatTy::F32),
        "f64" => Ty::Float(fir::FloatTy::F64),
        _ => match t.as_bytes()[0] {
            b'b' => Ty::Byte(t[1..].parse().unwrap_or(64)),
            _ => Ty::Int(t[1..].parse().unwrap_or(64)),
        },
    };
    (ty, v.trim())
}

/// The argument types of each call of each variadic external function, by name: the call
/// sites' operand types (a call through a variadic signature may reach any variadic external
/// function of that signature whose address is taken).
pub fn vararg_sites(m: &Module) -> (fir::Types, std::collections::BTreeMap<String, Vec<Vec<Ty>>>) {
    use fir::OpKind as K;
    let mut out: std::collections::BTreeMap<String, Vec<Vec<Ty>>> = Default::default();
    // The sites' types, composites in one table.
    let mut st = fir::Types::new();
    let mut taken = Vec::new();
    for g in 0..m.globals.len() {
        m.globals.syms(m.globals.init(g), &mut taken);
    }
    let mut taken: Vec<String> = taken.into_iter().map(str::to_owned).collect();
    for f in &m.funcs {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                if let K::FuncAddr { callee } = b.kind(op) {
                    taken.push(b.str(callee).to_owned());
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    for f in &m.funcs {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                let mut tys = |skip: usize| -> Vec<Ty> {
                    b.operands(op)[skip..]
                        .iter()
                        .map(|o| match o.get() {
                            fir::OperandKind::Value(v) => b.ty(v),
                            fir::OperandKind::Hole(h) => b.hole_ty(h),
                        })
                        .map(|t| st.import(b.types(), t))
                        .collect()
                };
                let mut add = |name: &str, site: Vec<Ty>| {
                    let sites = out.entry(name.to_owned()).or_default();
                    if !sites.contains(&site) {
                        sites.push(site);
                    }
                };
                match b.kind(op) {
                    K::Call { callee } | K::Invoke { callee, .. } => {
                        let name = b.str(callee);
                        if m.externs.iter().any(|x| x.name == name && x.variadic) {
                            let site = tys(0);
                            add(name, site);
                        }
                    }
                    K::CallIndirect(sig) | K::InvokeIndirect { sig, .. } => {
                        if let Some(fir::Shape::Func(ps, rs, true)) = b.types().shape_of(sig) {
                            // The signature's types are this function's, the external
                            // function's the module's: compared by structure.
                            let gt = &m.globals.types;
                            let same = |xs: &[Ty], ys: &[Ty]| {
                                xs.len() == ys.len()
                                    && xs.iter().zip(ys).all(|(&x, &y)| gt.same(x, b.types(), y))
                            };
                            for x in m.externs.iter().filter(|x| {
                                x.variadic
                                    && taken.contains(&x.name)
                                    && same(&x.params, ps)
                                    && same(&x.rets, rs)
                            }) {
                                let site = tys(1);
                                add(&x.name, site);
                            }
                        }
                    }
                    _ => {}
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    (st, out)
}

/// The C side of a program: stubs for the external functions, and a `main` that performs run
/// `argv[1]`. A variadic external function's stub takes the one argument list its calls pass
/// (on Linux, AAPCS64 passes variadic arguments as fixed ones); a variadic FIR function is
/// called through a prototype of the run's argument types, as FIR calls one.
pub fn harness(m: &Module, runs: &[(String, Vec<String>)], darwin: bool) -> String {
    let us = if darwin { "_" } else { "" };
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n\
         void fir_print(char kind, unsigned w, uint64_t v);\n\
         double fir_f64(uint64_t b);\nfloat fir_f32(uint32_t b);\n\
         uint64_t fir_b64(double x);\nuint64_t fir_b32(float x);\n\
         union fir_slot { uint64_t i; double d; float f; };\n\
         extern struct fir_exn { void *flag; void *value; } __fir_exn;\n",
    );
    let mut defs = String::new();
    let mut body = String::new();
    let mut ct = CTypes::default();
    let sp = &m.space;
    let params = |ct: &mut CTypes, types: &fir::Types, ps: &[Ty]| -> String {
        if ps.is_empty() {
            "void".to_owned()
        } else {
            ps.iter()
                .enumerate()
                .map(|(k, &t)| format!("{} a{k}", ct.ty(types, sp, t)))
                .collect::<Vec<_>>()
                .join(", ")
        }
    };
    // One composite result travels as the C struct; scalars by the backend's convention.
    let ret_ty = |ct: &mut CTypes, types: &fir::Types, rets: &[Ty], defs: &mut String| match rets {
        [t] if types.is_composite(*t) => ct.ty(types, sp, *t),
        _ => c_ret(rets, defs),
    };
    let (stypes, sites) = vararg_sites(m);
    let gtypes = &m.globals.types;
    for (i, x) in m.externs.iter().enumerate() {
        // A variadic stub takes its calls' one argument list, of the sites' table.
        let (site, ptypes) = match sites.get(&x.name).map(Vec::as_slice) {
            Some([site]) if x.variadic => (site.clone(), &stypes),
            _ => (x.params.clone(), gtypes),
        };
        let ps = params(&mut ct, ptypes, &site);
        let ret = ret_ty(&mut ct, gtypes, &x.rets, &mut defs);
        writeln!(
            body,
            "{ret} ext{i}({ps}) __asm__(\"{us}fir_ext_{}\");",
            x.name
        )
        .unwrap();
        writeln!(body, "{ret} ext{i}({ps}) {{").unwrap();
        writeln!(body, "  printf(\"@{}(\");", x.name).unwrap();
        for (k, &t) in x.params.iter().enumerate() {
            if k > 0 {
                body.push_str("  printf(\", \");\n");
            }
            writeln!(body, "  {}", ct.print(gtypes, t, &format!("a{k}"))).unwrap();
        }
        for (k, &t) in site.iter().enumerate().skip(x.params.len()) {
            if k > 0 {
                body.push_str("  printf(\", \");\n");
            }
            writeln!(body, "  {}", ct.print(ptypes, t, &format!("a{k}"))).unwrap();
        }
        body.push_str("  printf(\") -> \");\n");
        if x.rets.is_empty() {
            body.push_str("  printf(\"()\");\n");
        }
        let whole = matches!(x.rets[..], [t] if gtypes.is_composite(t));
        if whole {
            writeln!(
                body,
                "  {{ {ret} z; memset(&z, 0, sizeof z); {} }}",
                ct.print(gtypes, x.rets[0], "z")
            )
            .unwrap();
        } else {
            for (k, &t) in x.rets.iter().enumerate() {
                if k > 0 {
                    body.push_str("  printf(\", \");\n");
                }
                writeln!(body, "  {}", c_print(t, "0")).unwrap();
            }
        }
        body.push_str("  printf(\"; \");\n");
        match x.rets.len() {
            0 => {}
            1 if !whole => body.push_str("  return 0;\n"),
            _ => writeln!(body, "  {ret} r; memset(&r, 0, sizeof r); return r;").unwrap(),
        }
        body.push_str("}\n");
    }
    for (i, f) in m.funcs.iter().enumerate() {
        let b = &f.body;
        let ps: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        let ret = ret_ty(&mut ct, b.types(), &f.rets, &mut defs);
        let mut ps = params(&mut ct, b.types(), &ps);
        if f.variadic {
            ps = if ps == "void" {
                "...".to_owned()
            } else {
                ps + ", ..."
            };
        }
        writeln!(body, "{ret} fn{i}({ps}) __asm__(\"{us}fir_{}\");", f.name).unwrap();
    }
    body.push_str("int main(int argc, char **argv) {\n  (void)argc;\n  switch (atoi(argv[1])) {\n");
    for (k, (name, args)) in runs.iter().enumerate() {
        let i = m.funcs.iter().position(|f| &f.name == name).unwrap();
        let f = &m.funcs[i];
        let b = &f.body;
        let mut tys: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        let mut cargs: Vec<String> = tys.iter().zip(args).map(|(&t, a)| c_arg(t, a)).collect();
        for a in &args[tys.len()..] {
            let (t, v) = typed_arg(a);
            cargs.push(c_arg(t, v));
            tys.push(t);
        }
        let ret = ret_ty(&mut ct, b.types(), &f.rets, &mut defs);
        let call = if f.variadic {
            let ps: Vec<&str> = tys.iter().map(|&t| c_ty(t)).collect();
            let ps = if ps.is_empty() {
                "void".to_owned()
            } else {
                ps.join(", ")
            };
            format!("(({ret} (*)({ps}))fn{i})({})", cargs.join(", "))
        } else {
            format!("fn{i}({})", cargs.join(", "))
        };
        writeln!(body, "  case {k}: {{").unwrap();
        // An exception that leaves the function is pending in `__fir_exn` when it returns.
        let threw = "if (__fir_exn.flag) {\n      printf(\"threw \");\n      fir_print('p', 64, (uint64_t)(uintptr_t)__fir_exn.value);\n    } else ";
        match f.rets.len() {
            0 => writeln!(body, "    {call};\n    {threw}printf(\"returned\");").unwrap(),
            1 => {
                writeln!(
                    body,
                    "    {ret} r = {call};\n    {threw}{{\n      printf(\"returned \");\n      {}\n    }}",
                    ct.print(b.types(), f.rets[0], "r")
                )
                .unwrap();
            }
            _ => {
                writeln!(
                    body,
                    "    {ret} r = {call};\n    {threw}{{\n      printf(\"returned \");"
                )
                .unwrap();
                for (k, &t) in f.rets.iter().enumerate() {
                    if k > 0 {
                        body.push_str("      printf(\", \");\n");
                    }
                    writeln!(body, "      {}", c_print(t, &c_field(&f.rets, k, "r"))).unwrap();
                }
                body.push_str("    }\n");
            }
        }
        body.push_str("    printf(\"\\n\");\n    break;\n  }\n");
    }
    body.push_str("  }\n  return 0;\n}\n");
    c.push_str("#include <string.h>\n");
    c.push_str(&ct.defs);
    c.push_str(&defs);
    c.push_str(&body);
    c
}

/// A native output line with its floats (printed as `f64 0x…` bits) rendered as `fir run`
/// renders them.
pub fn render_floats(line: &str) -> String {
    let mut out = String::new();
    let mut prev = "";
    for (i, tok) in line.split(' ').enumerate() {
        if i > 0 {
            out.push(' ');
        }
        // The type is its own word, or follows `(` in an event's arguments.
        let ty = prev.rsplit(['(', '{']).next().unwrap_or(prev);
        let f = match ty {
            "f32" => Some(fir::FloatTy::F32),
            "f64" => Some(fir::FloatTy::F64),
            _ => None,
        };
        match (f, tok.strip_prefix("0x")) {
            (Some(f), Some(rest)) => {
                let hex: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
                let bits = u64::from_str_radix(&hex, 16).unwrap_or(0);
                out.push_str(&fir::float::render(f, bits));
                out.push_str(&rest[hex.len()..]);
            }
            _ => out.push_str(tok),
        }
        prev = tok;
    }
    out
}

/// Run `bin k` and give its output line (or what went wrong).
pub fn run_native(tc: &Toolchain, bin: &Path, k: usize) -> String {
    let mut cmd = match &tc.runner {
        Some(r) => {
            let mut c = Command::new(r);
            c.arg(bin);
            c
        }
        None => Command::new(bin),
    };
    let mut child = match cmd
        .arg(k.to_string())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => return format!("<can't run: {e}>"),
    };
    use std::io::Read as _;
    // Drain both pipes while the program runs: one that prints more than a pipe holds would
    // otherwise block until the time limit.
    let drain = |p: Option<Box<dyn std::io::Read + Send>>| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut p) = p {
                let _ = p.read_to_end(&mut buf);
            }
            buf
        })
    };
    let out = drain(child.stdout.take().map(|p| Box::new(p) as _));
    let err = drain(child.stderr.take().map(|p| Box::new(p) as _));
    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(st)) => break st,
            Ok(None) if start.elapsed() > Duration::from_secs(20) => {
                let _ = child.kill();
                let _ = child.wait();
                return "<timed out>".to_owned();
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(2)),
            Err(e) => return format!("<wait failed: {e}>"),
        }
    };
    let (stdout, stderr) = (out.join().unwrap(), err.join().unwrap());
    let s = render_floats(String::from_utf8_lossy(&stdout).trim_end());
    if status.success() {
        s
    } else {
        format!(
            "{s}<exit {:?}: {}>",
            status.code(),
            String::from_utf8_lossy(&stderr).trim_end()
        )
    }
}

/// Whether a reference outcome can be compared, and if so its normal form: leak notes dropped,
/// non-null pointers as `?`. `None`, with the reason, for runs that aren't comparable.
pub fn normalize(reference: &str) -> Result<(String, bool), String> {
    let parts: Vec<&str> = reference.split("; ").collect();
    let ending = parts
        .iter()
        .find(|p| !p.starts_with('@'))
        .copied()
        .unwrap_or("");
    for skip in [
        "ub ",
        "stuck",
        "hole",
        "ambiguous",
        "out of fuel",
        "diverges",
    ] {
        if ending.starts_with(skip) {
            let k = ending.split([' ', ':']).next().unwrap_or(ending);
            return Err(if skip == "out of fuel" {
                "out of fuel".to_owned()
            } else {
                k.to_owned()
            });
        }
    }
    let leaks = parts.iter().any(|p| p.starts_with("leak:"));
    let kept: Vec<&str> = parts
        .into_iter()
        .filter(|p| !p.starts_with("leak:"))
        .collect();
    // A `va_list` cursor's byte (`va(#2, 1)[0]`) is the target's own: any byte refines it
    // (decision: va_list).
    let mut joined = kept.join("; ");
    while let Some(at) = joined.find("va(#") {
        let end = joined[at..].find(']').map_or(joined.len(), |e| at + e + 1);
        joined.replace_range(at..end, "?");
    }
    let mut out = String::new();
    for (i, tok) in joined.split(' ').enumerate() {
        if i > 0 {
            out.push(' ');
        }
        // `#3`, `#3+8`, `(#3[0],` (a fragment), `0x1000` after `ptr`: an allocation's pointer.
        // A fragment of null is a zero byte.
        // An aggregate's opening braces stay as they are.
        let braces = tok.len() - tok.trim_start_matches('{').len();
        out.push_str(&tok[..braces]);
        let tok = &tok[braces..];
        let open = tok.strip_prefix('(');
        let body = open.unwrap_or(tok);
        let frag = body.contains('[');
        if body.starts_with('#') || frag || (out.ends_with("ptr ") && tok.starts_with("0x")) {
            if open.is_some() {
                out.push('(');
            }
            out.push_str(if body.starts_with("null[") {
                "0x0"
            } else {
                "?"
            });
            out.extend(
                body.chars()
                    .skip_while(|c| !matches!(c, ',' | ';' | ')' | '}')),
            );
        } else {
            out.push_str(tok);
        }
    }
    Ok((out, leaks))
}

/// The bases of the first-fit address layouts besides the reference's that each comparable run is
/// also made under. The first two start from bitwise complements (`0101…` and `1010…` over 48
/// bits), so between them the base's bits take both values. The third is where qemu-user puts
/// the stack.
pub const LAYOUTS: [u64; 3] = [0x5555_5555_5555, 0xaaaa_aaaa_aaaa, 0x7ffd_9a3c_5a40];

/// Every alternative layout: [`LAYOUTS`], and two seeds of `Addresses::Scatter` in both phases.
/// First fit packs allocations in one order under every base, so an allocation's bits just
/// above its alignment can agree in all of them by accident (found in review: a zero-size
/// 8-aligned slot had bit 3 set in each, while the native stack aligns it to 16). Scatter's two
/// phases flip each allocation's alignment bit, so the bits every layout agrees on are those the
/// semantics forces (an allocation's alignment, `fir::interp`'s `realize`), not a sample's
/// accident, and its regions vary the bits above per allocation.
pub fn layouts() -> Vec<fir::interp::Addresses> {
    use fir::interp::Addresses;
    let scatter = [1u64, 2]
        .into_iter()
        .flat_map(|seed| [false, true].map(|odd| Addresses::Scatter { seed, odd }));
    LAYOUTS
        .into_iter()
        .map(Addresses::From)
        .chain(scatter)
        .collect()
}

pub fn toks(s: &str) -> Vec<&str> {
    s.split([' ', ',', ';', '(', ')'])
        .filter(|t| !t.is_empty())
        .collect()
}

/// Whether each integer of `got` that differs from `want` at a position some address layout
/// (`alts`, the same run under [`layouts`]) moves stays within the span of bits that moved: from
/// the lowest bit a layout changed to the highest. Bits below the span are forced (an alignment,
/// which `Addresses::Scatter`'s phases make the lowest bit that moves), bits above it too (a
/// mask, the address space's size). Positions no layout moves, and results
/// whose shape differs from `want`'s, are left to the taint analysis.
pub fn within_moved_bits(want: &str, alts: &[String], got: &str) -> bool {
    moved_bits(want, alts, got, true)
}

/// [`within_moved_bits`] for a run's comparable layouts, `alts`: when some layouts weren't
/// comparable (undefined there: an access their placement misaligns, say), the rest needn't
/// flip any allocation's alignment bit, so bits below the span aren't known to be forced and
/// only the bits above it are held (found in review: a slot of alignment 2 read at alignment
/// 8, whose surviving layouts all put it at a multiple of 64).
pub fn within_layout_bits(want: &str, alts: &[String], got: &str) -> bool {
    moved_bits(want, alts, got, alts.len() == layouts().len())
}

fn moved_bits(want: &str, alts: &[String], got: &str, low_forced: bool) -> bool {
    let (w, g) = (toks(want), toks(got));
    if w.len() != g.len() {
        return true;
    }
    let alts: Vec<Vec<&str>> = alts
        .iter()
        .map(|a| toks(a))
        .filter(|a| a.len() == w.len())
        .collect();
    let int = |t: &str| t.parse::<i128>().ok().map(|x| x as u64);
    w.iter().zip(&g).enumerate().all(|(i, (a, b))| {
        let (Some(w0), Some(got)) = (int(a), int(b)) else {
            return true;
        };
        let moved = alts
            .iter()
            .filter_map(|alt| int(alt[i]))
            .fold(0, |m, x| m | (x ^ w0));
        if moved == 0 {
            return true;
        }
        let lo = if low_forced {
            moved.trailing_zeros()
        } else {
            0
        };
        let hi = 63 - moved.leading_zeros();
        let span = (u64::MAX >> (63 - hi)) & (u64::MAX << lo);
        (got ^ w0) & !span == 0
    })
}

/// A native execution proxy from a complete, agreeing run of the exact compiled module. A
/// relaxed comparison that mixes tokens from several layouts has no single execution profile.
pub fn native_profile(
    m: &Module,
    f: &str,
    args: &[String],
    fuel: u64,
    got: &str,
) -> Option<fir::interp::ExecutionProfile> {
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    for addrs in std::iter::once(fir::interp::Addresses::Low).chain(layouts()) {
        let r =
            fir::interp::run_detail_in(m, f, &a, fuel, m.layer == fir::Layer::Hfir, addrs).unwrap();
        if let Ok((line, _)) = normalize(&r.line)
            && matches(&line, got)
        {
            return Some(r.profile);
        }
    }
    None
}

#[derive(Default)]
pub struct Tally {
    pub stats: BTreeMap<String, u64>,
    pub fails: Vec<String>,
}

impl Tally {
    pub fn count(&mut self, k: impl Into<String>) {
        *self.stats.entry(k.into()).or_default() += 1;
    }
}

pub fn scratch(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

pub fn report(what: &str, tally: Tally, ev: &crate::common::evidence::Evidence) {
    eprintln!("{what}:");
    for (k, n) in &tally.stats {
        eprintln!("  {n:6}  {k}");
        ev.count(k.clone(), *n);
    }
    ev.count("failures", tally.fails.len() as u64);
    ev.write();
    assert!(
        tally.fails.is_empty(),
        "{} differences:\n{}",
        tally.fails.len(),
        tally.fails.join("\n")
    );
}

/// The `// run:` lines of a test file: function and arguments.
pub fn run_lines(text: &str) -> Vec<(String, Vec<String>)> {
    text.lines()
        .filter_map(|l| l.trim().strip_prefix("// run:"))
        .filter_map(|body| {
            let (call, _) = body.split_once(" -> ")?;
            let (name, rest) = call.trim().strip_prefix('@')?.split_once('(')?;
            let inner = rest.strip_suffix(')')?;
            let args = if inner.trim().is_empty() {
                Vec::new()
            } else {
                inner.split(',').map(|a| a.trim().to_owned()).collect()
            };
            Some((name.to_owned(), args))
        })
        .collect()
}

/// `m` with only the functions and external functions that `roots` reach through calls and
/// function addresses, and those that globals' initializers name.
pub fn prune(m: &Module, roots: &[&str]) -> Module {
    use fir::OpKind as K;
    let mut keep: Vec<String> = roots.iter().map(|r| (*r).to_owned()).collect();
    let mut syms = Vec::new();
    for g in 0..m.globals.len() {
        m.globals.syms(m.globals.init(g), &mut syms);
    }
    keep.extend(syms.into_iter().map(str::to_owned));
    let mut i = 0;
    while i < keep.len() {
        if let Some(f) = m.funcs.iter().find(|f| f.name == keep[i]) {
            let b = &f.body;
            let mut stack = vec![b.entry()];
            while let Some(r) = stack.pop() {
                for op in b.ops(r) {
                    if let K::Call { callee } | K::FuncAddr { callee } = b.kind(op) {
                        let name = b.str(callee);
                        if !keep.iter().any(|k| k == name) {
                            keep.push(name.to_owned());
                        }
                    }
                    stack.extend_from_slice(b.regions(op));
                }
            }
        }
        i += 1;
    }
    let mut out = m.clone();
    out.funcs.retain(|f| keep.contains(&f.name));
    out.externs.retain(|x| keep.contains(&x.name));
    out
}

pub fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}
