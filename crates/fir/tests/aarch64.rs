//! The AArch64 backend, checked against the interpreter.
//!
//! Every `// run:` line of the `.fir` files under `tests/`, and the runs of random programs
//! from the fuzzer (`progs`, in its narrow mode: integers of at most 64 bits, the default data
//! layout), are compiled to AArch64, linked with a generated C `main` that calls the function
//! with the run's arguments and prints the outcome in `fir run`'s format, run (natively on
//! AArch64, under `qemu-aarch64` elsewhere), and compared with `fir run`:
//!
//! * External functions are stubs that print the event and return zeros, as `fir run`'s world
//!   does. Traps reach the test runtime's `__fir_trap`, which prints the reason and location.
//! * Runs that end in UB, get stuck, reach a hole, are ambiguous, or run out of fuel are not
//!   comparable (UB allows anything) and are only counted.
//! * Where `fir run` prints `poison`, any value matches; a non-null pointer prints as `ptr ?`
//!   (allocation numbers are the interpreter's); leak notes are dropped (counted).
//!
//! The comparison also runs each program's LFIR in the interpreter, before and after register
//! allocation, and expects what the source run gives (with the same normalization): this checks
//! instruction selection and register allocation against the LFIR semantics without hardware.
//! For the fixtures and the first `FIR_FUZZ_LEAN` (default 100) random programs, the Lean
//! reference tool runs the LFIR text too, and must print exactly what `fir run` prints.
//!
//! `FIR_FUZZ=N` sets the number of random programs (default 100), `FIR_FUZZ_SEED` the seed;
//! `FIR_SHOW_ADDRESS_DIFFS=1` prints the runs that differ only where addresses are observed.
//! Without a toolchain (`$FIR_CC`, `cc` on AArch64, else `aarch64-unknown-linux-gnu-cc`) or a
//! way to run the binaries, the native half is skipped with a note; the LFIR half always runs.

#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod progs;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use fir::backend::aarch64 as a64;
use fir::{Module, Ty};

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

static const char *reasons[] = {"div0", "overflow", "shift", "oom"};

void __fir_trap(uint32_t reason, uint32_t line, uint32_t col) {
    printf("trap %s", reason < 4 ? reasons[reason] : "?");
    if (line != 0xffffffffu) printf(" @%u:%u", line, col);
    printf("\n");
    fflush(stdout);
    exit(0);
}

/* One value: 'i' an iW, 'p' a pointer, 'b' a bW. */
void fir_print(char kind, unsigned w, uint64_t v) {
    if (kind == 'p') {
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
        _ => ('p', 64),
    }
}

/// A C return type for `n` results under the backend's convention.
fn c_ret(n: usize) -> String {
    match n {
        0 => "void".to_owned(),
        1 => "uint64_t".to_owned(),
        n => format!("struct r{n}"),
    }
}

/// An argument as `fir run` reads it, as 64 bits (`poison` passes as 0).
fn c_arg(t: Ty, s: &str) -> String {
    match (t, s) {
        (_, "poison") | (_, "null") => "0".to_owned(),
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
         void fir_print(char kind, unsigned w, uint64_t v);\n",
    );
    let mut sizes: Vec<usize> = m.externs.iter().map(|x| x.rets.len()).collect();
    sizes.extend(m.funcs.iter().map(|f| f.rets.len()));
    sizes.sort_unstable();
    sizes.dedup();
    for n in sizes.into_iter().filter(|&n| n >= 2) {
        writeln!(c, "struct r{n} {{ uint64_t r[{n}]; }};").unwrap();
    }
    for (i, x) in m.externs.iter().enumerate() {
        let params: Vec<String> = (0..x.params.len())
            .map(|k| format!("uint64_t a{k}"))
            .collect();
        let params = if params.is_empty() {
            "void".to_owned()
        } else {
            params.join(", ")
        };
        let ret = c_ret(x.rets.len());
        writeln!(
            c,
            "{ret} ext{i}({params}) __asm__(\"{us}fir_ext_{}\");",
            x.name
        )
        .unwrap();
        writeln!(c, "{ret} ext{i}({params}) {{").unwrap();
        writeln!(c, "  printf(\"@{}(\");", x.name).unwrap();
        for (k, &t) in x.params.iter().enumerate() {
            let (kd, w) = kind(t);
            if k > 0 {
                c.push_str("  printf(\", \");\n");
            }
            writeln!(c, "  fir_print('{kd}', {w}, a{k});").unwrap();
        }
        c.push_str("  printf(\") -> \");\n");
        if x.rets.is_empty() {
            c.push_str("  printf(\"()\");\n");
        }
        for (k, &t) in x.rets.iter().enumerate() {
            let (kd, w) = kind(t);
            if k > 0 {
                c.push_str("  printf(\", \");\n");
            }
            writeln!(c, "  fir_print('{kd}', {w}, 0);").unwrap();
        }
        c.push_str("  printf(\"; \");\n");
        match x.rets.len() {
            0 => {}
            1 => c.push_str("  return 0;\n"),
            n => writeln!(c, "  struct r{n} r = {{{{0}}}}; return r;").unwrap(),
        }
        c.push_str("}\n");
    }
    for (i, f) in m.funcs.iter().enumerate() {
        let b = &f.body;
        let np = b.params(b.entry()).len();
        let params: Vec<&str> = (0..np).map(|_| "uint64_t").collect();
        let params = if params.is_empty() {
            "void".to_owned()
        } else {
            params.join(", ")
        };
        writeln!(
            c,
            "{} fn{i}({params}) __asm__(\"{us}fir_{}\");",
            c_ret(f.rets.len()),
            f.name
        )
        .unwrap();
    }
    c.push_str("int main(int argc, char **argv) {\n  (void)argc;\n  switch (atoi(argv[1])) {\n");
    for (k, (name, args)) in runs.iter().enumerate() {
        let i = m.funcs.iter().position(|f| &f.name == name).unwrap();
        let f = &m.funcs[i];
        let b = &f.body;
        let tys: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        let args: Vec<String> = tys.iter().zip(args).map(|(&t, a)| c_arg(t, a)).collect();
        let call = format!("fn{i}({})", args.join(", "));
        writeln!(c, "  case {k}: {{").unwrap();
        match f.rets.len() {
            0 => writeln!(c, "    {call};\n    printf(\"returned\");").unwrap(),
            1 => {
                let (kd, w) = kind(f.rets[0]);
                writeln!(c, "    uint64_t r = {call};\n    printf(\"returned \");\n    fir_print('{kd}', {w}, r);").unwrap();
            }
            n => {
                writeln!(c, "    struct r{n} r = {call};\n    printf(\"returned \");").unwrap();
                for (k, &t) in f.rets.iter().enumerate() {
                    let (kd, w) = kind(t);
                    if k > 0 {
                        c.push_str("    printf(\", \");\n");
                    }
                    writeln!(c, "    fir_print('{kd}', {w}, r.r[{k}]);").unwrap();
                }
            }
        }
        c.push_str("    printf(\"\\n\");\n    break;\n  }\n");
    }
    c.push_str("  }\n  return 0;\n}\n");
    c
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
    let s = String::from_utf8_lossy(&out.stdout).trim_end().to_owned();
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

/// Whether a module's runs can depend on where allocations are: it observes addresses
/// (`ptr.addr`, `ptr.expose`), turns them into pointers, compares pointers (which across
/// allocations is a nondeterministic choice), or reads memory that may hold pointers as integers.
fn observes_addresses(m: &Module) -> bool {
    use fir::OpKind as K;
    let mut int_loads = false;
    // A global initialized with addresses, or (below) a pointer store or copy, puts pointer
    // bytes in memory.
    let mut ptr_bytes = (0..m.globals.len())
        .any(|g| matches!(m.globals.init(g), fir::Init::Sym(_) | fir::Init::List(_)));
    for f in &m.funcs {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                match b.kind(op) {
                    K::PtrAddr
                    | K::PtrExpose
                    | K::PtrFromExposed
                    | K::PtrWithAddr
                    | K::PtrCmp(_) => {
                        return true;
                    }
                    K::Load { .. } => {
                        int_loads |= b.results(op).any(|v| b.ty(v) != Ty::Ptr);
                    }
                    K::Store { ty: Ty::Ptr, .. } | K::MemCopy { .. } => ptr_bytes = true,
                    _ => {}
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    int_loads && ptr_bytes
}

/// Whether `got` differs from `want` only in integer values, as runs that observe addresses
/// may.
fn differs_in_integers(want: &str, got: &str) -> bool {
    let toks = |s: &str| -> Vec<String> {
        s.split([' ', ',', ';', '(', ')'])
            .filter(|t| !t.is_empty())
            .map(str::to_owned)
            .collect()
    };
    let num = |t: &str| t.parse::<i128>().is_ok() || t.starts_with("0x") || t == "?" || t == "null";
    let (w, g) = (toks(want), toks(got));
    w.len() == g.len()
        && w.iter()
            .zip(&g)
            .all(|(a, b)| a == b || a == "poison" || (num(a) && num(b)))
}

/// Whether `got` matches the normalized reference, where `poison` matches anything.
fn matches(want: &str, got: &str) -> bool {
    let toks = |s: &str| -> Vec<String> {
        s.split([' ', ',', ';', '(', ')'])
            .filter(|t| !t.is_empty())
            .map(str::to_owned)
            .collect()
    };
    let (w, g) = (toks(want), toks(got));
    // `?` is a non-null pointer, or a byte of one (any value).
    w.len() == g.len()
        && w.iter()
            .zip(&g)
            .all(|(a, b)| a == b || a == "poison" || (a == "?" && b.starts_with("0x")))
}

/// What the LFIR of a module gives for a run, before and after register allocation.
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

/// Check one module's runs: `(function, args, fuel)`.
fn check_module(
    tc: Option<&Toolchain>,
    lean: Option<&Path>,
    m: &Module,
    runs: &[(String, Vec<String>, u64)],
    dir: &Path,
    name: &str,
    tally: &Mutex<Tally>,
) -> bool {
    let mut comparable = Vec::new();
    for (f, args, fuel) in runs {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        let reference = fir::interp::run(m, f, &a, *fuel).unwrap_or_else(|e| format!("error {e}"));
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
    let addresses = observes_addresses(m);
    // A difference only in integers, where addresses are observed, isn't a failure.
    let differs = |want: &str, got: &str, what: &str| -> bool {
        if addresses && differs_in_integers(want, got) {
            tally
                .lock()
                .unwrap()
                .count(format!("{what} differs where addresses are observed"));
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
        let run = |lm: &Module| fir::interp::run(lm, f, &a, lfir_fuel(*fuel));
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
                            .args(["--fuel", &lfir_fuel(*fuel).to_string()])
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
                    } else if differs(want, &g, &format!("LFIR ({stage})")) {
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
    let bin = match build(tc, m, &runs, dir, name) {
        Ok(b) => b,
        Err(e) => {
            tally.lock().unwrap().fails.push(format!("{name}: {e}"));
            return false;
        }
    };
    for (k, (f, args, _, want)) in comparable.iter().enumerate() {
        let got = run_native(tc, &bin, k);
        if matches(want, &got) {
            tally.lock().unwrap().count("native matches");
        } else if differs(want, &got, "native") {
            ok = false;
            tally.lock().unwrap().fails.push(format!(
                "{name} @{f}({}): native\n  want {want}\n  got  {got}",
                args.join(", ")
            ));
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
        if let Err(e) = a64::select(&m) {
            eprintln!("  {name}: not compiled: {e}");
            tally
                .lock()
                .unwrap()
                .count(format!("module skipped ({} runs)", runs.len()));
            continue;
        }
        modules += 1;
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
                        for ext in ["", ".s", ".c"] {
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
