//! The AArch64 backend, checked against the interpreter.
//!
//! Every `// run:` line of the `.fir` files under `tests/`, and the runs of random programs
//! from the fuzzer (`progs`, in its narrow mode: integers of at most 64 bits, the default data
//! layout), are compiled to AArch64, linked with a generated C `main` that calls the function
//! with the run's arguments and prints the outcome in `fir run`'s format, run (natively on
//! AArch64, under `qemu-aarch64` elsewhere), and compared with `fir run`:
//!
//! * A fixture is compiled with only the functions its runs reach; a run whose functions the
//!   backend can't compile (holes, integers wider than 64 bits, other data layouts) is skipped
//!   and counted, and the rest of its file still runs.
//! * Floats pass as C's `float` and `double`, and print as their bits, which the test renders as
//!   `fir run` does. The reference run picks NaN results by Arm's rule (`NanRule::Arm`, an
//!   oracle the semantics allows), so a native NaN must be exactly the one that oracle gives,
//!   payload and sign included; the LFIR machine follows Arm's rule too.
//! * External functions are stubs that print the event and return zeros, as `fir run`'s world
//!   does. Traps reach the test runtime's `__fir_trap`, which prints the reason and location.
//!   An exception that leaves the called function is pending in the runtime's `__fir_exn` when
//!   it returns, and `main` prints it as `threw ptr …`.
//! * Runs that end in UB, get stuck, reach a hole, are ambiguous, or run out of fuel are not
//!   comparable (UB allows anything) and are only counted.
//! * Addresses are the interpreter's and the hardware's own choices, so a taint analysis
//!   (`taint`) finds what may depend on them: `ptr.addr` and `ptr.expose` of possibly non-null
//!   pointers, pointer comparisons, `ptr.from_exposed`, `ptr.with_addr`, and numeric loads from
//!   objects that stores (or address initializers) may have put pointer bytes in, followed
//!   through values, memory (allocation-site points-to sets), calls, exceptions, and branches
//!   (which taint their whole function); `freeze` of what may be `poison` is the oracle's
//!   choice too. A run whose output differs only in tainted values, and only in their numbers,
//!   or where one run ends in an arithmetic or conversion trap at a tainted location and the
//!   other ends otherwise, is counted, not failed. Each comparable run is also made under other
//!   address layouts the semantics allows (`fir::interp::Addresses::From`, and
//!   `Addresses::Scatter`, which places each allocation on its own and, in its two phases, flips
//!   the bit of each allocation's alignment): a result one of them gives matches, and a tainted
//!   integer that those layouts move may differ only within the span of bits they moved (so
//!   `addr & 255` can't come out as 256, and an aligned address stays aligned, but only as
//!   aligned as the semantics requires); tainted values no layout moves (the oracle's `freeze`)
//!   are left to the taint analysis.
//! * Where `fir run` prints `poison` or a byte of a `va_list` cursor, any value matches; a
//!   non-null pointer prints as `ptr ?`
//!   (allocation numbers are the interpreter's); leak notes are dropped (counted).
//!
//! HFIR modules (the fixtures under `tests/blocks/` and most random programs, which use the
//! building blocks: aggregate, union, and slice values, checked arithmetic, `cf.check`) compile
//! as `fir compile` compiles them: lowered to MFIR first (`fir::backend::prepare`). Their
//! reference is `fir run` of the HFIR program, with returned aggregates, unions, and slices
//! shown as the lowering returns them (`run_detail` with `lower_rets`, as the lowering's own
//! tests compare them: as their scalars, except one struct or array result, which calls pass
//! whole), so the native output, which prints the lowered function's results, is compared with
//! the HFIR semantics directly. Where the default `-O` pipeline changes the MFIR, the optimized
//! program is built and run natively too.
//!
//! Structs and arrays cross the C boundary by value (decision: C ABI for aggregates): the
//! generated `main` declares a C struct with each composite's layout and AAPCS64 class (a
//! `struct<packed>` packed, a `struct<auto>` with its fields in layout order, an array as a
//! struct holding a C array), receives a composite result as one, and prints it as `fir run`
//! renders it; external functions' stubs take and print composite arguments, variadic ones
//! included, and return zeroed ones. `tests/abi.rs` checks the ABI against the C compiler with
//! random signatures.
//!
//! The comparison also runs each program's LFIR in the interpreter, before and after register
//! allocation, and expects what the source run gives (with the same normalization): this checks
//! instruction selection and register allocation against the LFIR semantics without hardware.
//! For the fixtures and the first `FIR_FUZZ_LEAN` (default 100) random programs, the Lean
//! reference tool runs the LFIR text too, and must print exactly what `fir run` prints.
//!
//! Coverage counts dispatches only in runs that agreed. For native runs it uses the executed
//! interpreter profile of the exact module compiled (including `-O` and direct HFIR), on the
//! same arguments, only when that profiled outcome matches the native result. This is a proxy
//! for native execution, not a hardware trace. An address comparison that only matches mixed
//! tokens from several layouts contributes no profile unless one complete layout run matches.
//!
//! A run whose functions the backend can't compile is skipped only for a limitation it declares
//! (holes, integers wider than 64 bits, data layouts other than 64-bit, offsets the lowering
//! can't represent); any other failure to compile, a register allocation the validator refuses
//! included, fails the test.
//!
//! `FIR_FUZZ=N` sets the number of random programs (default 100), `FIR_FUZZ_SEED` the seed;
//! `FIR_SHOW_ADDRESS_DIFFS=1` prints the runs that differ only in address-dependent outcomes.
//! Without a toolchain (`$FIR_CC`, `cc` on AArch64, else `aarch64-unknown-linux-gnu-cc`) or a
//! way to run the binaries, the native half is skipped with a note (a failure under
//! `FIR_REQUIRE_FULL=1`); the LFIR half always runs. Each test writes its counts to the
//! evidence (`common::evidence`).

#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod progs;
mod taint;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use fir::backend::aarch64 as a64;
use fir::interp::NanRule;
use fir::{Module, Ty};
use taint::{Taint, matches};

struct Toolchain {
    cc: String,
    /// The emulator binaries run under, if not natively.
    runner: Option<String>,
    runtime: PathBuf,
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

/// The test runtime: the trap handler and value printing, in `fir run`'s format.
const RUNTIME: &str = r#"
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

fn toolchain(dir: &Path) -> Result<Toolchain, String> {
    let native = cfg!(target_arch = "aarch64");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("aarch64-unknown-linux-gnu-cc") => {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => return Err("no AArch64 C compiler (set FIR_CC, or use the dev shell)".to_owned()),
    };
    let runner = if native {
        None
    } else if on_path("qemu-aarch64") {
        Some("qemu-aarch64".to_owned())
    } else {
        return Err("no qemu-aarch64 to run AArch64 binaries".to_owned());
    };
    let src = dir.join("runtime.c");
    std::fs::write(&src, RUNTIME).unwrap();
    let runtime = dir.join("runtime.o");
    let ok = Command::new(&cc)
        .args(["-c", "-O1", "-fno-builtin"])
        .arg(&src)
        .arg("-o")
        .arg(&runtime)
        .status()
        .map_err(|e| format!("running {cc}: {e}"))?
        .success();
    if !ok {
        return Err(format!("{cc} can't compile the runtime"));
    }
    Ok(Toolchain {
        cc,
        runner,
        runtime,
    })
}

/// The C types of a module's composites (decision: C ABI for aggregates): a struct with the
/// FIR type's layout and AAPCS64 class for each, named by its text. A `struct<C>`'s fields are
/// its parts in order, a `struct<packed>` is packed, a `struct<auto>`'s fields are in its layout's
/// order, and an array is a struct holding a C array; integers and bytes of 8 to 64 bits are
/// `uintN_t` (others `unsigned _BitInt(N)`, which C lays out as FIR does), pointers `void *`.
#[derive(Default)]
struct CTypes {
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
fn kind(t: Ty) -> (char, u32) {
    match t {
        Ty::Int(w) => ('i', w),
        Ty::Byte(w) => ('b', w),
        Ty::Float(f) => ('f', f.width()),
        _ => ('p', 64),
    }
}

/// The C type a value of type `t` travels as.
fn c_ty(t: Ty) -> &'static str {
    match t {
        Ty::Float(fir::FloatTy::F32) => "float",
        Ty::Float(fir::FloatTy::F64) => "double",
        _ => "uint64_t",
    }
}

/// `fir_print` of the C expression `e` holding a value of type `t`.
fn c_print(t: Ty, e: &str) -> String {
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
fn c_ret(rets: &[Ty], defs: &mut String) -> String {
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
fn c_field(rets: &[Ty], i: usize, var: &str) -> String {
    let hfa = rets[0].is_float() && rets.iter().all(|&t| t == rets[0]);
    match rets[i] {
        Ty::Float(fir::FloatTy::F32) if rets.len() > 2 || !hfa => format!("{var}.r{i}.f"),
        Ty::Float(fir::FloatTy::F64) if rets.len() > 2 => format!("{var}.r{i}.d"),
        _ if rets.len() > 2 => format!("{var}.r{i}.i"),
        _ => format!("{var}.r{i}"),
    }
}

/// An argument as `fir run` reads it, as its C type's value (`poison` passes as 0).
fn c_arg(t: Ty, s: &str) -> String {
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
fn typed_arg(s: &str) -> (Ty, &str) {
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
fn vararg_sites(m: &Module) -> (fir::Types, std::collections::BTreeMap<String, Vec<Vec<Ty>>>) {
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
fn harness(m: &Module, runs: &[(String, Vec<String>)], darwin: bool) -> String {
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
fn render_floats(line: &str) -> String {
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

/// Compile `m` with a harness for `runs` into `dir/name`.
fn build(
    tc: &Toolchain,
    m: &Module,
    runs: &[(String, Vec<String>)],
    dir: &Path,
    name: &str,
) -> Result<PathBuf, String> {
    let o = a64::Options {
        os: a64::Os::host(),
        prefix: "fir_".to_owned(),
        extern_prefix: "fir_ext_".to_owned(),
    };
    let asm = a64::compile(m, &o)?;
    let s = dir.join(format!("{name}.s"));
    let c = dir.join(format!("{name}.c"));
    let bin = dir.join(name);
    std::fs::write(&s, asm).unwrap();
    std::fs::write(&c, harness(m, runs, o.os == a64::Os::Darwin)).unwrap();
    let out = Command::new(&tc.cc)
        .args(["-O0", "-w"])
        .arg(&c)
        .arg(&s)
        .arg(&tc.runtime)
        .arg("-o")
        .arg(&bin)
        .output()
        .map_err(|e| format!("running {}: {e}", tc.cc))?;
    if !out.status.success() {
        return Err(format!(
            "linking failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(bin)
}

/// Run `bin k` and give its output line (or what went wrong).
fn run_native(tc: &Toolchain, bin: &Path, k: usize) -> String {
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
    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) if start.elapsed() > Duration::from_secs(20) => {
                let _ = child.kill();
                let _ = child.wait();
                return "<timed out>".to_owned();
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(2)),
            Err(e) => return format!("<wait failed: {e}>"),
        }
    }
    let out = child.wait_with_output().unwrap();
    let s = render_floats(String::from_utf8_lossy(&out.stdout).trim_end());
    if out.status.success() {
        s
    } else {
        format!(
            "{s}<exit {:?}: {}>",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr).trim_end()
        )
    }
}

/// Whether a reference outcome can be compared, and if so its normal form: leak notes dropped,
/// non-null pointers as `?`. `None`, with the reason, for runs that aren't comparable.
fn normalize(reference: &str) -> Result<(String, bool), String> {
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
const LAYOUTS: [u64; 3] = [0x5555_5555_5555, 0xaaaa_aaaa_aaaa, 0x7ffd_9a3c_5a40];

/// Every alternative layout: [`LAYOUTS`], and two seeds of `Addresses::Scatter` in both phases.
/// First fit packs allocations in one order under every base, so an allocation's bits just
/// above its alignment can agree in all of them by accident (found in review: a zero-size
/// 8-aligned slot had bit 3 set in each, while the native stack aligns it to 16). Scatter's two
/// phases flip each allocation's alignment bit, so the bits every layout agrees on are those the
/// semantics forces (an allocation's alignment, `fir::interp`'s `realize`), not a sample's
/// accident, and its regions vary the bits above per allocation.
fn layouts() -> Vec<fir::interp::Addresses> {
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

/// Why a compile failure is a declared limitation of the backend, if it is one (decision: C ABI
/// for aggregates refuses to pass a composite whose pointer leaf doesn't fill an `x` register's
/// word, which could travel only as address bits).
fn known_limit(e: &str) -> Option<&'static str> {
    [
        ("can't be compiled", "holes"),
        ("wider than 64 bits", "integers wider than 64 bits"),
        ("needs 64-bit pointers", "a data layout other than 64-bit"),
        ("cannot lower:", "an offset the lowering can't represent"),
        (
            "can't be passed by value in registers",
            "a composite whose pointer doesn't fill a register word",
        ),
    ]
    .into_iter()
    .find(|(k, _)| e.contains(k))
    .map(|(_, why)| why)
}

fn toks(s: &str) -> Vec<&str> {
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
fn within_moved_bits(want: &str, alts: &[String], got: &str) -> bool {
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
        let (lo, hi) = (moved.trailing_zeros(), 63 - moved.leading_zeros());
        let span = (u64::MAX >> (63 - hi)) & (u64::MAX << lo);
        (got ^ w0) & !span == 0
    })
}

/// The LFIR of a module, before and after register allocation, verified.
fn lfir_modules(m: &Module) -> Result<[Module; 2], String> {
    let mut mm = a64::select(m)?;
    let before = a64::lfir::to_module(m, &mm);
    fir::verify_module(&before)
        .map_err(|e| format!("LFIR before allocation doesn't verify: {e}"))?;
    a64::allocate(m, &mut mm)?;
    let after = a64::lfir::to_module(m, &mm);
    fir::verify_module(&after).map_err(|e| format!("LFIR after allocation doesn't verify: {e}"))?;
    Ok([before, after])
}

/// The machine code takes more steps than the source: give it plenty.
fn lfir_fuel(fuel: u64) -> u64 {
    fuel.saturating_mul(64)
}

/// A native execution proxy from a complete, agreeing run of the exact compiled module. A
/// relaxed comparison that mixes tokens from several layouts has no single execution profile.
fn native_profile(
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
struct Tally {
    stats: BTreeMap<String, u64>,
    fails: Vec<String>,
}

impl Tally {
    fn count(&mut self, k: impl Into<String>) {
        *self.stats.entry(k.into()).or_default() += 1;
    }
}

/// The HFIR building blocks a module uses, by name, for the statistics.
fn blocks_used(m: &Module) -> Vec<&'static str> {
    use fir::OpKind as K;
    let mut out = Vec::new();
    for f in &m.funcs {
        let b = &f.body;
        let sig = b
            .params(b.entry())
            .map(|v| b.ty(v))
            .chain(f.rets.iter().copied());
        if sig.into_iter().any(|t| !t.is_value()) {
            out.push("aggregate parameters or results");
        }
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                stack.extend_from_slice(b.regions(op));
                out.push(match b.kind(op) {
                    K::AggMake | K::AggExtract { .. } | K::AggInsert { .. } => "agg.*",
                    K::Overflow { .. } => "int.*.overflow.*",
                    K::UnionMake { .. } | K::UnionTag | K::UnionGet { .. } => "union.*",
                    K::SliceMake | K::SlicePtr | K::SliceLen => "slice.make/ptr/len",
                    K::SliceGet { .. } | K::SliceSet { .. } => "slice.get/set",
                    K::Check(_) => "cf.check",
                    K::Try => "cf.try",
                    K::Throw => "exn.throw",
                    K::Invoke { .. } | K::InvokeIndirect { .. } => "func.invoke",
                    K::Load { .. } | K::Store { .. } => {
                        let t = match b.kind(op) {
                            K::Store { ty, .. } => ty,
                            _ => b.ty(b.results(op).next().unwrap()),
                        };
                        if t.is_value() {
                            continue;
                        }
                        "aggregate loads and stores"
                    }
                    _ => continue,
                });
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// How the compiled module passes composites (decision: C ABI for aggregates), for the
/// statistics: to and from external functions, and as variadic arguments.
fn composites_used(m: &Module) -> Vec<&'static str> {
    use fir::OpKind as K;
    let mut out = Vec::new();
    let gt = &m.globals.types;
    if m.externs
        .iter()
        .any(|x| x.params.iter().chain(&x.rets).any(|&t| gt.is_composite(t)))
    {
        out.push("structs or arrays to or from external functions");
    }
    for f in &m.funcs {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                stack.extend_from_slice(b.regions(op));
                let n = match b.kind(op) {
                    K::Call { callee } | K::Invoke { callee, .. } => {
                        let name = b.str(callee);
                        match m.funcs.iter().find(|g| g.name == name) {
                            Some(g) if g.variadic => g.body.params(g.body.entry()).len(),
                            Some(_) => continue,
                            None => match m.externs.iter().find(|x| x.name == name) {
                                Some(x) if x.variadic => x.params.len(),
                                _ => continue,
                            },
                        }
                    }
                    K::CallIndirect(sig) | K::InvokeIndirect { sig, .. } => {
                        match b.types().shape_of(sig) {
                            Some(fir::Shape::Func(ps, _, true)) => ps.len() + 1,
                            _ => continue,
                        }
                    }
                    K::VaArg => {
                        if b.results(op).any(|v| b.types().is_composite(b.ty(v))) {
                            out.push("va.arg of structs or arrays");
                        }
                        continue;
                    }
                    _ => continue,
                };
                if b.operands(op)[n.min(b.operands(op).len())..].iter().any(|o| {
                    matches!(o.get(), fir::OperandKind::Value(v) if b.types().is_composite(b.ty(v)))
                }) {
                    out.push("structs or arrays as variadic arguments");
                }
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Check one module's runs: `(function, args, fuel)`. An HFIR module is lowered first, as
/// `fir compile` does. `out` takes the statistics and the evidence (native, LFIR).
fn check_module(
    tc: Option<&Toolchain>,
    lean: Option<&Path>,
    src: &Module,
    runs: &[(String, Vec<String>, u64)],
    dir: &Path,
    name: &str,
    out: (
        &Mutex<Tally>,
        &common::evidence::Evidence,
        &common::evidence::Evidence,
    ),
) -> bool {
    let (tally, ev_native, ev_lfir) = out;
    let lowered = src.layer == fir::Layer::Hfir;
    let m = match fir::backend::prepare(src, false) {
        Ok(m) => m,
        Err(e) => {
            let mut t = tally.lock().unwrap();
            match known_limit(&e) {
                Some(why) => t.count(format!("not lowered: {why}")),
                None => {
                    t.fails.push(format!("{name}: not lowered: {e}"));
                    return false;
                }
            }
            return true;
        }
    };
    let m = &m;
    let blocks = blocks_used(src);
    let text = src.render(false);
    let floats = text.contains("float.") || text.contains(": f32") || text.contains(": f64");
    let varargs = text.contains("...");
    // Composites in the compiled module's signatures (calls pass them by value).
    let by_value_uses = composites_used(m);
    let by_value = !by_value_uses.is_empty()
        || m.funcs.iter().any(|f| {
            let b = &f.body;
            b.params(b.entry())
                .map(|v| b.ty(v))
                .chain(f.rets.iter().copied())
                .any(|t| b.types().is_composite(t))
        });
    {
        let mut t = tally.lock().unwrap();
        if lowered {
            t.count("(HFIR modules, lowered)");
        }
        if floats {
            t.count("(modules with floats)");
        }
        if varargs {
            t.count("(modules with variadic functions)");
        }
        for b in &blocks {
            t.count(format!("(modules using {b})"));
        }
        for c in &by_value_uses {
            t.count(format!("(modules passing {c})"));
        }
    }
    let mut comparable = Vec::new();
    for (f, args, fuel) in runs {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        let reference = fir::interp::run_detail_with(src, f, &a, *fuel, lowered, NanRule::Arm)
            .map(|r| r.line)
            .unwrap_or_else(|e| format!("error {e}"));
        match normalize(&reference) {
            Ok((want, leaks)) => {
                if leaks {
                    tally.lock().unwrap().count("(leak notes dropped)");
                }
                // The same run under the other address layouts, where it is comparable too.
                let alts: Vec<String> = layouts()
                    .into_iter()
                    .filter_map(|addrs| {
                        let r =
                            fir::interp::run_detail_in(src, f, &a, *fuel, lowered, addrs).ok()?;
                        normalize(&r.line).ok().map(|x| x.0)
                    })
                    .collect();
                comparable.push((f.clone(), args.clone(), *fuel, want, alts));
            }
            Err(why) => tally.lock().unwrap().count(format!("skipped: {why}")),
        }
    }
    if comparable.is_empty() {
        return true;
    }
    let mut ok = true;
    let taint = Taint::of(m);
    if taint.any() {
        tally
            .lock()
            .unwrap()
            .count("(modules with address-dependent outcomes)");
    }
    // A difference only in what may depend on addresses isn't a failure: another legal layout's
    // result, or a tainted outcome whose moving integers stay within the bits the layouts moved.
    let differs = |f: &str, want: &str, alts: &[String], got: &str, what: &str| -> bool {
        if alts.iter().any(|a| matches(a, got)) {
            tally
                .lock()
                .unwrap()
                .count(format!("{what} matches another address layout"));
            return false;
        }
        if !taint.exempt(f, want, got) {
            return true;
        }
        if !within_moved_bits(want, alts, got) {
            return true;
        }
        tally
            .lock()
            .unwrap()
            .count(format!("{what} differs in address-dependent outcomes"));
        if std::env::var_os("FIR_SHOW_ADDRESS_DIFFS").is_some() {
            eprintln!("{name}: {what}\n  want {want}\n  alts {alts:?}\n  got  {got}");
        }
        false
    };
    // The LFIR in the interpreter, and in the Lean reference tool when there is one.
    let modules = match lfir_modules(m) {
        Ok(ms) => ms,
        Err(e) => {
            let mut t = tally.lock().unwrap();
            match known_limit(&e) {
                Some(why) => t.count(format!("not compiled: {why}")),
                None => {
                    t.fails.push(format!("{name}: not compiled: {e}"));
                    return false;
                }
            }
            return true;
        }
    };
    let files: Vec<PathBuf> = match lean {
        Some(_) => ["vregs", "allocated"]
            .iter()
            .zip(&modules)
            .map(|(stage, lm)| {
                let p = dir.join(format!("{name}.{stage}.fir"));
                std::fs::write(&p, lm.render(true)).unwrap();
                p
            })
            .collect(),
        None => Vec::new(),
    };
    for (f, args, fuel, want, alts) in &comparable {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        // The lowering takes up to 16 times the steps of the HFIR program.
        let fuel = if lowered { 16 * *fuel } else { *fuel };
        let run = |lm: &Module| fir::interp::run_detail(lm, f, &a, lfir_fuel(fuel), false);
        match modules.iter().map(run).collect::<Result<Vec<_>, String>>() {
            Ok(got) => {
                if let Some(tool) = lean {
                    for (file, g) in files.iter().zip(&got) {
                        let out = Command::new(tool)
                            .arg("run")
                            .arg(file)
                            .arg(format!("@{f}"))
                            .args(args)
                            .args(["--fuel", &lfir_fuel(fuel).to_string()])
                            .output()
                            .unwrap();
                        let r = String::from_utf8_lossy(&out.stdout).trim_end().to_owned();
                        if out.status.success() && out.stderr.is_empty() && r == g.line {
                            ev_lfir.executed(&g.profile);
                            tally.lock().unwrap().count("LFIR: fir-ref run agrees");
                        } else {
                            ok = false;
                            tally.lock().unwrap().fails.push(format!(
                                "{}: @{f}({}): fir-ref run {r:?} (exit {}, stderr {:?}), fir run {:?}",
                                file.display(),
                                args.join(", "), out.status,
                                String::from_utf8_lossy(&out.stderr), g.line
                            ));
                        }
                    }
                }
                for (stage, g) in ["vregs", "allocated"].iter().zip(&got) {
                    let g = normalize(&g.line)
                        .map(|x| x.0)
                        .unwrap_or_else(|_| g.line.clone());
                    if matches(want, &g) {
                        tally
                            .lock()
                            .unwrap()
                            .count(format!("LFIR ({stage}) matches"));
                    } else if differs(f, want, alts, &g, &format!("LFIR ({stage})")) {
                        ok = false;
                        tally.lock().unwrap().fails.push(format!(
                            "{name} @{f}({}): LFIR ({stage})\n  want {want}\n  alts {alts:?}\n  got  {g}",
                            args.join(", ")
                        ));
                    }
                }
            }
            Err(e) => {
                ok = false;
                tally
                    .lock()
                    .unwrap()
                    .fails
                    .push(format!("{name} @{f}: {e}"));
            }
        }
    }
    if ok {
        for file in &files {
            let _ = std::fs::remove_file(file);
        }
    }
    let Some(tc) = tc else { return ok };
    // A variadic external function's stub takes one argument list (see `harness`).
    if vararg_sites(m).1.values().any(|sites| sites.len() > 1) {
        tally
            .lock()
            .unwrap()
            .count("native skipped: a variadic external function called with several signatures");
        return ok;
    }
    let runs: Vec<(String, Vec<String>)> = comparable
        .iter()
        .map(|(f, a, _, _, _)| (f.clone(), a.clone()))
        .collect();
    // The program as compiled, and with `-O` when that changes it.
    let mut builds = vec![("native", m.clone())];
    match fir::backend::prepare(src, true) {
        Ok(o) if o.render(false) != m.render(false) => builds.push(("native -O", o)),
        Ok(_) => {}
        Err(e) => {
            tally.lock().unwrap().fails.push(format!("{name}: -O: {e}"));
            return false;
        }
    }
    // HFIR whose only building blocks are `ptr.field` and `ptr.index` (no aggregate values, no
    // `cf.try`) also compiles without lowering: instruction selection handles those two itself.
    // Nothing else reaches those cases, so run it too.
    if lowered && a64::select(src).is_ok() && fir::backend::aarch64::isel::check_module(src).is_ok()
    {
        builds.push(("native, HFIR selected directly", src.clone()));
    }
    for (what, bm) in &builds {
        let bname = match *what {
            "native" => name.to_owned(),
            "native -O" => format!("{name}-O"),
            _ => format!("{name}-hfir"),
        };
        let bin = match build(tc, bm, &runs, dir, &bname) {
            Ok(b) => b,
            Err(e) => {
                tally
                    .lock()
                    .unwrap()
                    .fails
                    .push(format!("{name} ({what}): {e}"));
                return false;
            }
        };
        ev_native.fact("execution coverage", "interpreter profile of the exact compiled module, same arguments; native proxy, not a hardware trace");
        for (k, (f, args, fuel, want, alts)) in comparable.iter().enumerate() {
            let got = run_native(tc, &bin, k);
            let mut agreed = true;
            if matches(want, &got) {
                let mut t = tally.lock().unwrap();
                t.count(format!("{what} matches"));
                if floats {
                    t.count(format!("{what} matches (floats)"));
                }
                if varargs {
                    t.count(format!("{what} matches (varargs)"));
                }
                if by_value {
                    t.count(format!("{what} matches (structs by value)"));
                }
                if want.contains("nan") {
                    t.count(format!("{what} matches (NaN results)"));
                }
                if !blocks.is_empty() {
                    t.count(format!("{what} matches (building blocks)"));
                }
                if blocks
                    .iter()
                    .any(|b| ["cf.try", "exn.throw", "func.invoke"].contains(b))
                {
                    t.count(format!("{what} matches (exceptions)"));
                }
                if want.contains("threw ") {
                    t.count(format!("{what} matches (threw)"));
                }
            } else if differs(f, want, alts, &got, what) {
                agreed = false;
                ok = false;
                tally.lock().unwrap().fails.push(format!(
                    "{name} @{f}({}): {what}\n  want {want}\n  alts {alts:?}\n  got  {got}",
                    args.join(", ")
                ));
            }
            if agreed {
                // Profile the module that was actually compiled, not the HFIR source of an
                // optimized/lowered build. Other layouts can take different branches, so use
                // only the first complete profiled result that matches this native run.
                let fuel = if lowered { 16 * *fuel } else { *fuel };
                if let Some(profile) = native_profile(bm, f, args, fuel, &got) {
                    ev_native.executed(&profile);
                    ev_native.count("native runs with execution profile", 1);
                } else {
                    ev_native.count("native runs without a matching execution profile", 1);
                }
            }
        }
    }
    ok
}

#[test]
fn native_profiles_require_agreement_and_use_the_compiled_module() {
    let m = fir::parse_module(
        "func @f(%x: i32) -> i32 {
  %dead: i32 = int.mul.wrap %x, %x
  func.ret %x
}",
    )
    .unwrap();
    fir::verify_module(&m).unwrap();
    let optimized = fir::backend::prepare(&m, true).unwrap();
    let args = vec!["3".to_owned()];
    let before = native_profile(&m, "f", &args, 100, "returned i32 3").unwrap();
    assert!(before.counts().any(|(k, n)| k == "int.mul.wrap" && n == 1));
    let after = native_profile(&optimized, "f", &args, 100, "returned i32 3").unwrap();
    assert!(!after.counts().any(|(k, _)| k == "int.mul.wrap"));
    assert!(native_profile(&optimized, "f", &args, 100, "returned i32 9").is_none());
    assert!(native_profile(&optimized, "f", &args, 0, "returned i32 3").is_none());
}

fn scratch(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn report(what: &str, tally: Tally, ev: &common::evidence::Evidence) {
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
fn run_lines(text: &str) -> Vec<(String, Vec<String>)> {
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
fn prune(m: &Module, roots: &[&str]) -> Module {
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

#[test]
fn fixtures_run_natively() {
    let ev = common::evidence::Evidence::new("aarch64_fixtures");
    let ev_lfir = common::evidence::Evidence::new("aarch64_lfir");
    let dir = scratch("aarch64-fixtures");
    let tc = native(&dir, &ev);
    let tally = Mutex::new(Tally::default());
    let lean = common::reference();
    let mut modules = 0;
    for file in common::fir_files() {
        let text = std::fs::read_to_string(&file).unwrap();
        let runs = run_lines(&text);
        if runs.is_empty() {
            continue;
        }
        let name = common::display_name(&file);
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() {
            continue;
        }
        if let fir::Layer::Lfir(_) = m.layer {
            tally.lock().unwrap().count("module skipped: already LFIR");
            continue;
        }
        // Each run needs the functions it reaches to compile; the others are left out.
        let compiles =
            |m: &Module| fir::backend::prepare(m, false).and_then(|l| a64::select(&l).map(|_| ()));
        let mut kept = Vec::new();
        for (f, a) in runs {
            match compiles(&prune(&m, &[&f])) {
                Ok(()) => kept.push((f, a)),
                Err(e) => {
                    let mut t = tally.lock().unwrap();
                    match known_limit(&e) {
                        Some(why) => t.count(format!("run skipped, not compiled: {why}")),
                        None => t.fails.push(format!("{name}: @{f}: not compiled: {e}")),
                    }
                }
            }
        }
        if kept.is_empty() {
            continue;
        }
        let roots: Vec<&str> = kept.iter().map(|(f, _)| f.as_str()).collect();
        let m = prune(&m, &roots);
        modules += 1;
        let runs = kept;
        let runs: Vec<_> = runs
            .into_iter()
            .map(|(f, a)| (f, a, fir::interp::DEFAULT_FUEL))
            .collect();
        let stem = name.replace(['/', '.'], "_");
        check_module(
            tc.as_ref(),
            lean.as_deref(),
            &m,
            &runs,
            &dir,
            &stem,
            (&tally, &ev, &ev_lfir),
        );
    }
    eprintln!("{modules} fixture modules compiled");
    ev.count("fixture modules compiled", modules);
    ev_lfir.write();
    report("fixtures", tally.into_inner().unwrap(), &ev);
}

/// The native toolchain, or `None` with a note (a failure when a full run is required), recorded
/// in the evidence.
fn native(dir: &Path, ev: &common::evidence::Evidence) -> Option<Toolchain> {
    match toolchain(dir) {
        Ok(tc) => {
            ev.fact(
                "native",
                tc.runner.clone().unwrap_or_else(|| "native".to_owned()),
            );
            ev.fact("cc", tc.cc.clone());
            Some(tc)
        }
        Err(e) => {
            common::evidence::require(&format!("native AArch64 runs: {e}"));
            ev.skip(format!("native runs: {e}"));
            None
        }
    }
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[test]
fn random_programs_run_natively() {
    let ev = common::evidence::Evidence::new("aarch64_fuzz");
    let ev_lfir = common::evidence::Evidence::new("aarch64_lfir_fuzz");
    let dir = scratch("aarch64-fuzz");
    let tc = native(&dir, &ev);
    let count = env_u64("FIR_FUZZ", 100);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let lean = common::reference();
    let lean_count = env_u64("FIR_FUZZ_LEAN", 100);
    let tally = Mutex::new(Tally::default());
    let next = Mutex::new(0u64);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let k = {
                        let mut n = next.lock().unwrap();
                        *n += 1;
                        *n - 1
                    };
                    if k >= count {
                        return;
                    }
                    let mut rng = progs::Rng::narrow(seed.wrapping_mul(0x1_0000_0001) ^ k);
                    let prog = progs::program(&mut rng);
                    let name = format!("s{seed}-p{k}");
                    let m = fir::parse_module(&prog.text)
                        .and_then(|m| fir::verify_module(&m).map(|_| m))
                        .unwrap_or_else(|e| panic!("generated program {name} is invalid: {e}"));
                    let runs: Vec<_> = prog
                        .runs
                        .iter()
                        .map(|(a, fuel)| ("f0".to_owned(), a.clone(), *fuel))
                        .collect();
                    tally.lock().unwrap().count("(programs)");
                    // The Lean reference tool runs the LFIR of the first programs.
                    let lean = lean.as_deref().filter(|_| k < lean_count);
                    if !check_module(
                        tc.as_ref(),
                        lean,
                        &m,
                        &runs,
                        &dir,
                        &name,
                        (&tally, &ev, &ev_lfir),
                    ) {
                        std::fs::write(dir.join(format!("{name}.fir")), &prog.text).unwrap();
                    } else {
                        for ext in ["", ".s", ".c", "-O", "-O.s", "-O.c"] {
                            let _ = std::fs::remove_file(dir.join(format!("{name}{ext}")));
                        }
                    }
                }
            });
        }
    });
    ev.fact("seed", seed.to_string());
    ev_lfir.write();
    report(
        &format!("{count} random programs (seed {seed})"),
        tally.into_inner().unwrap(),
        &ev,
    );
}

/// Found in review: an excused integer was any number. Now one that a legal address layout moves
/// may differ only in the span of bits the layouts moved, so a masked address stays within its
/// mask.
#[test]
fn review_address_exemption_preserves_masked_integer_range() {
    let m = fir::parse_module("func @f() -> i64 {\n  %p: ptr = mem.stack 1, align 1\n  %a: i64 = ptr.addr %p\n  %mask: i64 = int.const 255\n  %r: i64 = int.and %a, %mask\n  func.ret %r\n}").unwrap();
    fir::verify_module(&m).unwrap();
    let result = |addrs| {
        normalize(
            &fir::interp::run_detail_in(&m, "f", &[], 100, false, addrs)
                .unwrap()
                .line,
        )
        .unwrap()
        .0
    };
    let want = result(fir::interp::Addresses::Low);
    let alts: Vec<_> = layouts().into_iter().map(result).collect();
    assert_eq!(want, "returned i64 0");
    assert_eq!(
        alts[..3],
        ["returned i64 85", "returned i64 170", "returned i64 64"]
    );
    // Another value within the bits that move is a legal address's.
    assert!(within_moved_bits(&want, &alts, "returned i64 240"));
    // Every permitted address, including layouts not sampled here, gives a result <= 255.
    assert!(!within_moved_bits(&want, &alts, "returned i64 256"));
    // The taint analysis alone would excuse it: only the layouts bound the number.
    assert!(taint_of("func @f() -> i64 {\n  %p: ptr = mem.stack 1, align 1\n  %a: i64 = ptr.addr %p\n  %mask: i64 = int.const 255\n  %r: i64 = int.and %a, %mask\n  func.ret %r\n}").exempt("f", &want, "returned i64 256"));
}

/// The layouts are real behaviors of the interpreter: a run that observes an address gives a
/// different number under each, and an unrelated result stays the same.
#[test]
fn layouts_move_only_addresses() {
    let m = fir::parse_module(
        "func @f(%x: i32) -> (i64, i32) {
  %p: ptr = mem.stack 8, align 8
  %a: i64 = ptr.addr %p
  %y: i32 = int.mul.wrap %x, %x
  func.ret %a, %y
}
",
    )
    .unwrap();
    fir::verify_module(&m).unwrap();
    let run = |l| {
        fir::interp::run_detail_in(&m, "f", &["3"], 1000, false, l)
            .unwrap()
            .line
    };
    let low = run(fir::interp::Addresses::Low);
    assert_eq!(low, "returned i64 4096, i32 9");
    for l in layouts() {
        let other = run(l);
        assert_ne!(other, low);
        assert!(other.ends_with(", i32 9"), "{other}");
    }
}

/// Found in review (`s71-p534`, `FIR_FUZZ_SEED=71`): the address of a zero-size 8-aligned stack
/// slot had bit 3 set under every first-fit layout, so the 16-aligned address the native stack
/// gives it counted as a difference, though the semantics requires only a multiple of 8. The
/// scatter layouts flip bit 3, so any multiple of 8 within the moved bits is allowed, and a
/// multiple of 4 that isn't one of 8 still isn't.
#[test]
fn review_forced_address_bits_come_from_alignment() {
    let m = fir::parse_module(
        "func @f() -> i64 {\n  %p: ptr = mem.stack 0, align 8\n  %q: ptr = mem.stack 8, align 8\n  %b: i64 = ptr.expose %q\n  %a: i64 = ptr.expose %p\n  func.ret %a\n}",
    )
    .unwrap();
    fir::verify_module(&m).unwrap();
    let result = |addrs| {
        normalize(
            &fir::interp::run_detail_in(&m, "f", &[], 100, false, addrs)
                .unwrap()
                .line,
        )
        .unwrap()
        .0
    };
    let want = result(fir::interp::Addresses::Low);
    let alts: Vec<_> = layouts().into_iter().map(result).collect();
    let n: u64 = want.rsplit(' ').next().unwrap().parse().unwrap();
    assert_eq!(n % 8, 0);
    // The two first-fit layouts the review's run had (the others weren't comparable there)
    // agree on bit 3, as the reference does; scatter's phases move it.
    let bit3 = |alts: &[String]| {
        alts.iter()
            .any(|a| (a.rsplit(' ').next().unwrap().parse::<u64>().unwrap() ^ n) & 8 != 0)
    };
    assert_eq!(n & 8, 8);
    assert!(!bit3(&alts[1..3]));
    assert!(bit3(&alts[3..]));
    let flipped = format!("returned i64 {}", n ^ 8);
    let off4 = format!("returned i64 {}", n ^ 4);
    assert!(!within_moved_bits(&want, &alts[1..3], &flipped));
    assert!(within_moved_bits(&want, &alts, &flipped));
    assert!(!within_moved_bits(&want, &alts, &off4));
}

/// The address-dependence analysis of `text`, on the module the backend compiles.
fn taint_of(text: &str) -> Taint {
    let m = fir::parse_module(text).unwrap();
    fir::verify_module(&m).unwrap();
    Taint::of(&fir::backend::prepare(&m, false).unwrap())
}

#[test]
fn address_exemptions_need_tainted_outcomes() {
    // An address observed (of null, which is no observation) doesn't excuse an unrelated
    // float or trap.
    let t = taint_of(
        "func @f() -> f64 {
           %p: ptr = ptr.null
           %a: i64 = ptr.addr %p
           %r: f64 = float.const 1.0
           func.ret %r
         }",
    );
    assert!(!t.exempt("f", "returned f64 1.0", "returned f64 2.0"));
    assert!(!t.exempt("f", "returned f64 1.0", "trap convert @1:1"));
    // Nor does a real address that doesn't reach the outcome.
    let t = taint_of(
        "func @f(%x: f64) -> (i64, f64) {
           %p: ptr = mem.stack 8, align 8
           %a: i64 = ptr.addr %p
           %y: f64 = float.add %x, %x
           %i: i32 = float.to_int.s.trap %y @2:1
           func.ret %a, %y
         }",
    );
    assert!(t.exempt(
        "f",
        "returned i64 4096, f64 1.0",
        "returned i64 77, f64 1.0"
    ));
    assert!(!t.exempt(
        "f",
        "returned i64 4096, f64 1.0",
        "returned i64 4096, f64 2.0"
    ));
    assert!(!t.exempt("f", "returned i64 4096, f64 1.0", "trap convert @2:1"));
    // An address that does reach the trap, or the float, excuses them.
    let t = taint_of(
        "func @f() -> f64 {
           %p: ptr = mem.stack 8, align 8
           %a: i64 = ptr.addr %p
           %y: f64 = int.to_float.s %a
           %i: i32 = float.to_int.s.trap %y @2:1
           func.ret %y
         }",
    );
    assert!(t.exempt("f", "returned f64 4096.0", "returned f64 1e15"));
    assert!(t.exempt("f", "trap convert @2:1", "returned f64 1e15"));
    // The run that traps at the tainted location may stop before a trap the other reaches.
    assert!(t.exempt("f", "trap overflow @9:9", "trap convert @2:1"));
    assert!(!t.exempt("f", "trap overflow @9:9", "trap convert @8:8"));
    // So does a branch on one, for what it controls.
    let t = taint_of(
        "func @f() -> i32 {
           %p: ptr = mem.stack 8, align 8
           %a: i64 = ptr.addr %p
           %z: i64 = int.const 0
           %c: i1 = int.cmp.eq %a, %z
           %r: i32 = cf.if %c {
             %one: i32 = int.const 1
             cf.yield %one
           } else {
             %two: i32 = int.const 2
             cf.yield %two
           }
           func.ret %r
         }",
    );
    assert!(t.exempt("f", "returned i32 2", "returned i32 1"));
    // `freeze` of what may be `poison` is the oracle's choice too; of a number, it isn't.
    let text = |modifier: &str| {
        format!(
            "func @f() -> i8 {{
               %x: i8 = int.const -1
               %y: i8 = int.add.{modifier} %x, %x
               %z: i8 = freeze %y
               func.ret %z
             }}"
        )
    };
    assert!(taint_of(&text("nuw")).exempt("f", "returned i8 0", "returned i8 -2"));
    assert!(!taint_of(&text("wrap")).exempt("f", "returned i8 0", "returned i8 -2"));
}

#[test]
fn variadic_arguments_taint_only_their_callees() {
    // An address passed to one variadic function doesn't reach another's `va.arg`.
    let text = |to: &str| {
        format!(
            "func @discard(...) -> i64 {{
               %z: i64 = int.const 0
               func.ret %z
             }}
             func @take(...) -> i64 {{
               %ap: ptr = mem.stack.of va_list, align 8
               va.start %ap
               %x: i64 = va.arg %ap
               func.ret %x
             }}
             func @main() -> i64 {{
               %p: ptr = mem.stack 8, align 8
               %a: i64 = ptr.addr %p
               %u: i64 = func.call @{to}(... %a)
               %n: i64 = int.const 42
               %r: i64 = func.call @take(... %n)
               func.ret %r
             }}"
        )
    };
    assert!(!taint_of(&text("discard")).exempt("main", "returned i64 42", "returned i64 99"));
    assert!(taint_of(&text("take")).exempt("main", "returned i64 42", "returned i64 99"));
    // Through a `va_list` passed to another function, `va.arg` reads the arguments of the
    // function whose `va.start` filled it, and only those.
    let text = |to: &str| {
        format!(
            "func @read(%ap: ptr) -> i64 {{
               %x: i64 = va.arg %ap
               func.ret %x
             }}
             func @outer(...) -> i64 {{
               %ap: ptr = mem.stack.of va_list, align 8
               va.start %ap
               %aq: ptr = mem.stack.of va_list, align 8
               mem.copy va_list %aq, %ap, align 8
               %x: i64 = func.call @read(%aq)
               func.ret %x
             }}
             func @other(...) -> i64 {{
               %z: i64 = int.const 0
               func.ret %z
             }}
             func @main() -> i64 {{
               %p: ptr = mem.stack 8, align 8
               %a: i64 = ptr.addr %p
               %u: i64 = func.call @{to}(... %a)
               %n: i64 = int.const 42
               %r: i64 = func.call @outer(... %n)
               func.ret %r
             }}"
        )
    };
    assert!(!taint_of(&text("other")).exempt("main", "returned i64 42", "returned i64 99"));
    assert!(taint_of(&text("outer")).exempt("main", "returned i64 42", "returned i64 99"));
    // An indirect call reaches every variadic function whose address is taken.
    let t = taint_of(
        "func @take(...) -> i64 {
           %ap: ptr = mem.stack.of va_list, align 8
           va.start %ap
           %x: i64 = va.arg %ap
           func.ret %x
         }
         func @main() -> i64 {
           %f: ptr = func.addr @take
           %p: ptr = mem.stack 8, align 8
           %a: i64 = ptr.addr %p
           %u: i64 = func.call.indirect func<(...) -> i64> %f(... %a)
           %n: i64 = int.const 42
           %r: i64 = func.call @take(... %n)
           func.ret %r
         }",
    );
    assert!(t.exempt("main", "returned i64 42", "returned i64 99"));
}

#[test]
fn only_ops_that_can_trap_excuse_traps() {
    // A tainted op that can't trap excuses no trap at its location.
    let text = |op: &str| {
        format!(
            "func @main() -> i64 {{
               %p: ptr = mem.stack 8, align 8
               %a: i64 = ptr.addr %p
               %unused: i64 = {op} %a, %a @9:9
               %r: i64 = int.const 42
               func.ret %r
             }}"
        )
    };
    let t = taint_of(&text("int.add.wrap"));
    assert!(!t.exempt("main", "returned i64 42", "trap overflow @9:9"));
    // One that can excuses its own reason, and no other.
    let t = taint_of(&text("int.add.s.trap"));
    assert!(t.exempt("main", "returned i64 42", "trap overflow @9:9"));
    assert!(!t.exempt("main", "returned i64 42", "trap div0 @9:9"));
    let t = taint_of(&text("int.div.s.trap"));
    assert!(t.exempt("main", "returned i64 42", "trap div0 @9:9"));
    assert!(t.exempt("main", "returned i64 42", "trap overflow @9:9"));
    assert!(!t.exempt("main", "returned i64 42", "trap shift @9:9"));
    let t = taint_of(&text("int.shl.trap"));
    assert!(t.exempt("main", "returned i64 42", "trap shift @9:9"));
    assert!(!t.exempt("main", "returned i64 42", "trap overflow @9:9"));
    // Where an untainted op at the same location can trap with the same reason, the trap may
    // be its: not excused.
    let t = taint_of(
        "func @main(%x: i64) -> i64 {
           %p: ptr = mem.stack 8, align 8
           %a: i64 = ptr.addr %p
           %u: i64 = int.add.s.trap %a, %a @9:9
           %v: i64 = int.add.s.trap %x, %x @9:9
           %r: i64 = int.const 42
           func.ret %r
         }",
    );
    assert!(!t.exempt("main", "returned i64 42", "trap overflow @9:9"));
}

#[test]
fn pointer_bytes_taint_only_where_pointers_go() {
    // A pointer stored in one slot makes integer loads from it tainted, not from another.
    let text = |from: &str| {
        format!(
            "func @f() -> i64 {{
               %a: ptr = mem.stack 8, align 8
               %b: ptr = mem.stack 8, align 8
               %z: i64 = int.const 0
               mem.store i64 %z, %b, align 8
               mem.store ptr %a, %a, align 8
               %v: i64 = mem.load %{from}, align 8
               func.ret %v
             }}"
        )
    };
    assert!(taint_of(&text("a")).exempt("f", "returned i64 4096", "returned i64 7"));
    assert!(!taint_of(&text("b")).exempt("f", "returned i64 0", "returned i64 7"));
    // An aggregate global without addresses holds no pointer bytes; one with an address does.
    let text = |init: &str| {
        format!(
            "global @x: i64 = 0
             global @g: struct<C>{{ptr, i64}} = {init}
             func @f() -> i64 {{
               %g: ptr = mem.global @g
               %v: i64 = mem.load %g, align 8
               func.ret %v
             }}"
        )
    };
    assert!(!taint_of(&text("{null, 5}")).exempt("f", "returned i64 0", "returned i64 7"));
    assert!(taint_of(&text("{@x, 5}")).exempt("f", "returned i64 4096", "returned i64 7"));
}

/// Found by the coverage gate's direct-HFIR builds (random program s1-p102 at 200 programs):
/// instruction selection accepted a `mem.load` of a struct, a core op over an HFIR value, and
/// emitted it as one wide integer (`lsl x0, x0, #64`, which doesn't assemble). It refuses such
/// values now; the lowering scalarizes them first.
#[test]
fn aggregate_values_need_lowering() {
    let m = fir::parse_module(
        "func @f(%p: ptr, %q: ptr) {
  %s: struct<C>{i64, i32} = mem.load %p, align 8
  mem.store struct<C>{i64, i32} %s, %q, align 8
  func.ret
}
",
    )
    .unwrap();
    fir::verify_module(&m).unwrap();
    let e = a64::select(&m).unwrap_err();
    assert!(
        e.contains("HFIR only: lower the module to MFIR first"),
        "{e}"
    );
    let lowered = fir::backend::prepare(&m, false).unwrap();
    a64::compile(&lowered, &a64::Options::default()).unwrap();
}

/// Found in review: a `struct<packed>{i8, ptr}` passed by value had its pointer shifted across
/// two `x` registers, which leaves its address bits only, so a `read(args)` callee no longer
/// reached the allocation in the LFIR machine (and natively) as it does in the semantics: the
/// LFIR wasn't a refinement. Passing such a composite by value is refused now, as a parameter,
/// an argument (to FIR or C), or a result (variadic composites are `struct<C>` and arrays, whose
/// pointers fill words); a pointer that fills a word, or a packed composite passed by reference
/// (over 16 bytes), is passed as before.
#[test]
fn review_split_pointers_are_refused() {
    let refused = |text: &str| {
        let m = fir::parse_module(text).unwrap();
        fir::verify_module(&m).unwrap();
        let lowered = fir::backend::prepare(&m, false).unwrap();
        let e = a64::compile(&lowered, &a64::Options::default()).unwrap_err();
        assert!(
            e.contains("can't be passed by value in registers") && known_limit(&e).is_some(),
            "{e}"
        );
    };
    refused(
        "extern func @see(struct<packed>{i8, ptr}) -> i64 effects[read(args)] assume
func @f() -> i64 {
  %p: ptr = mem.stack.of i64, align 8
  %v: i64 = int.const 42
  mem.store i64 %v, %p, align 8
  %one: i8 = int.const 1
  %s: struct<packed>{i8, ptr} = agg.make %one, %p
  %r: i64 = func.call @see(%s)
  func.ret %r
}
",
    );
    refused(
        "func @g(%s: struct<packed>{i8, ptr}) -> i8 {
  %a: i8 = agg.extract %s, 0
  func.ret %a
}
",
    );
    refused(
        "func @h(%p: ptr) -> struct<packed>{i16, ptr} {
  %a: i16 = int.const 1
  %s: struct<packed>{i16, ptr} = agg.make %a, %p
  func.ret %s
}
",
    );
    for ok in [
        "func @g(%s: struct<packed>{i64, ptr}) -> i64 {\n  %a: i64 = agg.extract %s, 0\n  func.ret %a\n}\n",
        "func @g(%s: struct<packed>{i8, ptr, i64, i64}) -> i8 {\n  %a: i8 = agg.extract %s, 0\n  func.ret %a\n}\n",
    ] {
        let m = fir::parse_module(ok).unwrap();
        fir::verify_module(&m).unwrap();
        let lowered = fir::backend::prepare(&m, false).unwrap();
        a64::compile(&lowered, &a64::Options::default()).unwrap();
    }
}
