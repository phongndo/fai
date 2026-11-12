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
//!   other ends otherwise, is counted, not failed.
//! * Where `fir run` prints `poison`, any value matches; a non-null pointer prints as `ptr ?`
//!   (allocation numbers are the interpreter's); leak notes are dropped (counted).
//!
//! HFIR modules (the fixtures under `tests/blocks/` and most random programs, which use the
//! building blocks: aggregate, union, and slice values, checked arithmetic, `cf.check`) compile
//! as `fir compile` compiles them: lowered to MFIR first (`fir::backend::prepare`). Their
//! reference is `fir run` of the HFIR program, with returned aggregates, unions, and slices
//! shown as the scalars the lowering returns (`run_detail` with `lower_rets`, as the lowering's
//! own tests compare them), so the native output, which prints the lowered function's results,
//! is compared with the HFIR semantics directly. Where the default `-O` pipeline changes the
//! MFIR, the optimized program is built and run natively too.
//!
//! The comparison also runs each program's LFIR in the interpreter, before and after register
//! allocation, and expects what the source run gives (with the same normalization): this checks
//! instruction selection and register allocation against the LFIR semantics without hardware.
//! For the fixtures and the first `FIR_FUZZ_LEAN` (default 100) random programs, the Lean
//! reference tool runs the LFIR text too, and must print exactly what `fir run` prints.
//!
//! `FIR_FUZZ=N` sets the number of random programs (default 100), `FIR_FUZZ_SEED` the seed;
//! `FIR_SHOW_ADDRESS_DIFFS=1` prints the runs that differ only in address-dependent outcomes.
//! Without a toolchain (`$FIR_CC`, `cc` on AArch64, else `aarch64-unknown-linux-gnu-cc`) or a
//! way to run the binaries, the native half is skipped with a note; the LFIR half always runs.

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

/// The C side of a program: stubs for the external functions, and a `main` that performs run
/// `argv[1]`.
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
    let params = |ps: &[Ty]| -> String {
        if ps.is_empty() {
            "void".to_owned()
        } else {
            ps.iter()
                .enumerate()
                .map(|(k, &t)| format!("{} a{k}", c_ty(t)))
                .collect::<Vec<_>>()
                .join(", ")
        }
    };
    for (i, x) in m.externs.iter().enumerate() {
        let ps = params(&x.params);
        let ret = c_ret(&x.rets, &mut defs);
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
            writeln!(body, "  {}", c_print(t, &format!("a{k}"))).unwrap();
        }
        body.push_str("  printf(\") -> \");\n");
        if x.rets.is_empty() {
            body.push_str("  printf(\"()\");\n");
        }
        for (k, &t) in x.rets.iter().enumerate() {
            if k > 0 {
                body.push_str("  printf(\", \");\n");
            }
            writeln!(body, "  {}", c_print(t, "0")).unwrap();
        }
        body.push_str("  printf(\"; \");\n");
        match x.rets.len() {
            0 => {}
            1 => body.push_str("  return 0;\n"),
            _ => writeln!(body, "  {ret} r; memset(&r, 0, sizeof r); return r;").unwrap(),
        }
        body.push_str("}\n");
    }
    for (i, f) in m.funcs.iter().enumerate() {
        let b = &f.body;
        let ps: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        let ret = c_ret(&f.rets, &mut defs);
        writeln!(
            body,
            "{ret} fn{i}({}) __asm__(\"{us}fir_{}\");",
            params(&ps),
            f.name
        )
        .unwrap();
    }
    body.push_str("int main(int argc, char **argv) {\n  (void)argc;\n  switch (atoi(argv[1])) {\n");
    for (k, (name, args)) in runs.iter().enumerate() {
        let i = m.funcs.iter().position(|f| &f.name == name).unwrap();
        let f = &m.funcs[i];
        let b = &f.body;
        let tys: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        let args: Vec<String> = tys.iter().zip(args).map(|(&t, a)| c_arg(t, a)).collect();
        let call = format!("fn{i}({})", args.join(", "));
        let ret = c_ret(&f.rets, &mut defs);
        writeln!(body, "  case {k}: {{").unwrap();
        // An exception that leaves the function is pending in `__fir_exn` when it returns.
        let threw = "if (__fir_exn.flag) {\n      printf(\"threw \");\n      fir_print('p', 64, (uint64_t)(uintptr_t)__fir_exn.value);\n    } else ";
        match f.rets.len() {
            0 => writeln!(body, "    {call};\n    {threw}printf(\"returned\");").unwrap(),
            1 => {
                writeln!(
                    body,
                    "    {ret} r = {call};\n    {threw}{{\n      printf(\"returned \");\n      {}\n    }}",
                    c_print(f.rets[0], "r")
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
        let ty = prev.rsplit('(').next().unwrap_or(prev);
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
    let mut out = String::new();
    for (i, tok) in kept.join("; ").split(' ').enumerate() {
        if i > 0 {
            out.push(' ');
        }
        // `#3`, `#3+8`, `(#3[0],` (a fragment), `0x1000` after `ptr`: an allocation's pointer.
        // A fragment of null is a zero byte.
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
            out.extend(body.chars().skip_while(|c| !matches!(c, ',' | ';' | ')')));
        } else {
            out.push_str(tok);
        }
    }
    Ok((out, leaks))
}

/// The LFIR of a module, before and after register allocation, verified.
fn lfir_modules(m: &Module) -> Result<[Module; 2], String> {
    let mut mm = a64::select(m)?;
    let before = a64::lfir::to_module(m, &mm);
    fir::verify_module(&before)
        .map_err(|e| format!("LFIR before allocation doesn't verify: {e}"))?;
    a64::allocate(m, &mut mm);
    let after = a64::lfir::to_module(m, &mm);
    fir::verify_module(&after).map_err(|e| format!("LFIR after allocation doesn't verify: {e}"))?;
    Ok([before, after])
}

/// The machine code takes more steps than the source: give it plenty.
fn lfir_fuel(fuel: u64) -> u64 {
    fuel.saturating_mul(64)
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

/// Check one module's runs: `(function, args, fuel)`. An HFIR module is lowered first, as
/// `fir compile` does.
fn check_module(
    tc: Option<&Toolchain>,
    lean: Option<&Path>,
    src: &Module,
    runs: &[(String, Vec<String>, u64)],
    dir: &Path,
    name: &str,
    tally: &Mutex<Tally>,
) -> bool {
    let lowered = src.layer == fir::Layer::Hfir;
    let m = match fir::backend::prepare(src, false) {
        Ok(m) => m,
        Err(e) => {
            tally.lock().unwrap().count(format!(
                "not lowered: {}",
                e.rsplit(':').next().unwrap_or(&e).trim()
            ));
            return true;
        }
    };
    let m = &m;
    let blocks = blocks_used(src);
    let text = src.render(false);
    let floats = text.contains("float.") || text.contains(": f32") || text.contains(": f64");
    {
        let mut t = tally.lock().unwrap();
        if lowered {
            t.count("(HFIR modules, lowered)");
        }
        if floats {
            t.count("(modules with floats)");
        }
        for b in &blocks {
            t.count(format!("(modules using {b})"));
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
                comparable.push((f.clone(), args.clone(), *fuel, want));
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
    // A difference only in what may depend on addresses isn't a failure.
    let differs = |f: &str, want: &str, got: &str, what: &str| -> bool {
        if taint.exempt(f, want, got) {
            tally
                .lock()
                .unwrap()
                .count(format!("{what} differs in address-dependent outcomes"));
            if std::env::var_os("FIR_SHOW_ADDRESS_DIFFS").is_some() {
                eprintln!("{name}: {what}\n  want {want}\n  got  {got}");
            }
            false
        } else {
            true
        }
    };
    // The LFIR in the interpreter, and in the Lean reference tool when there is one.
    let modules = match lfir_modules(m) {
        Ok(ms) => ms,
        Err(e) => {
            tally.lock().unwrap().count(format!(
                "not compiled: {}",
                e.rsplit(':').next().unwrap_or(&e).trim()
            ));
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
    for (f, args, fuel, want) in &comparable {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        // The lowering takes up to 16 times the steps of the HFIR program.
        let fuel = if lowered { 16 * *fuel } else { *fuel };
        let run = |lm: &Module| fir::interp::run(lm, f, &a, lfir_fuel(fuel));
        match modules
            .iter()
            .map(run)
            .collect::<Result<Vec<String>, String>>()
        {
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
                        if &r == g {
                            tally.lock().unwrap().count("LFIR: fir-ref run agrees");
                        } else {
                            ok = false;
                            tally.lock().unwrap().fails.push(format!(
                                "{}: @{f}({}): fir-ref run {r:?}, fir run {g:?}",
                                file.display(),
                                args.join(", ")
                            ));
                        }
                    }
                }
                for (stage, g) in ["vregs", "allocated"].iter().zip(&got) {
                    let g = normalize(g).map(|x| x.0).unwrap_or_else(|_| g.clone());
                    if matches(want, &g) {
                        tally
                            .lock()
                            .unwrap()
                            .count(format!("LFIR ({stage}) matches"));
                    } else if differs(f, want, &g, &format!("LFIR ({stage})")) {
                        ok = false;
                        tally.lock().unwrap().fails.push(format!(
                            "{name} @{f}({}): LFIR ({stage})\n  want {want}\n  got  {g}",
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
    let runs: Vec<(String, Vec<String>)> = comparable
        .iter()
        .map(|(f, a, _, _)| (f.clone(), a.clone()))
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
    for (what, bm) in &builds {
        let bname = if *what == "native" {
            name.to_owned()
        } else {
            format!("{name}-O")
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
        for (k, (f, args, _, want)) in comparable.iter().enumerate() {
            let got = run_native(tc, &bin, k);
            if matches(want, &got) {
                let mut t = tally.lock().unwrap();
                t.count(format!("{what} matches"));
                if floats {
                    t.count(format!("{what} matches (floats)"));
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
            } else if differs(f, want, &got, what) {
                ok = false;
                tally.lock().unwrap().fails.push(format!(
                    "{name} @{f}({}): {what}\n  want {want}\n  got  {got}",
                    args.join(", ")
                ));
            }
        }
    }
    ok
}

fn scratch(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn report(what: &str, tally: Tally) {
    eprintln!("{what}:");
    for (k, n) in &tally.stats {
        eprintln!("  {n:6}  {k}");
    }
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
    let dir = scratch("aarch64-fixtures");
    let tc = toolchain(&dir)
        .map_err(|e| eprintln!("native runs skipped: {e}"))
        .ok();
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
                    eprintln!("  {name}: @{f}: not compiled: {e}");
                    tally.lock().unwrap().count("run skipped: not compiled");
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
        check_module(tc.as_ref(), lean.as_deref(), &m, &runs, &dir, &stem, &tally);
    }
    eprintln!("{modules} fixture modules compiled");
    report("fixtures", tally.into_inner().unwrap());
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[test]
fn random_programs_run_natively() {
    let dir = scratch("aarch64-fuzz");
    let tc = toolchain(&dir)
        .map_err(|e| eprintln!("native runs skipped: {e}"))
        .ok();
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
                    if !check_module(tc.as_ref(), lean, &m, &runs, &dir, &name, &tally) {
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
    report(
        &format!("{count} random programs (seed {seed})"),
        tally.into_inner().unwrap(),
    );
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
