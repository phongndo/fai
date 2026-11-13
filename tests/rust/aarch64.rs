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
//! program is built and run natively too; `FIR_PASSES=p,q,…` runs that pipeline instead
//! (experimental passes included).
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
mod native;
#[allow(dead_code)]
mod progs;
mod taint;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use fir::Module;
use fir::backend::aarch64 as a64;
use fir::interp::NanRule;
use native::*;
use taint::{Taint, matches};

/// The pipeline the optimized builds run: the default `-O` one, or `FIR_PASSES=p,q,…` (run to a
/// fixed point; experimental passes allowed), as `tests/opt.rs` takes it.
fn opt_pipeline() -> fir::passes::Pipeline {
    match std::env::var("FIR_PASSES") {
        Ok(spec) if !spec.is_empty() => {
            fir::passes::Pipeline::parse_fixpoint(&spec, true).expect("FIR_PASSES")
        }
        _ => fir::passes::Pipeline::default_opt(),
    }
}

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
        debug_lines: false,
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

/// Why emitting for macOS failed, if it is what the backend declares it doesn't support there yet
/// (Apple's AAPCS64 variant: variadic arguments on the stack, composites passed on the stack).
/// Only a macOS host emits for macOS, and only after selection and allocation, which don't
/// depend on the OS, succeeded; anything else failing there is a failure.
fn darwin_limit(e: &str) -> Option<&'static str> {
    [
        (
            "variadic functions aren't supported on macOS yet",
            "variadic functions on macOS (not supported yet)",
        ),
        (
            "on the stack, which isn't supported on macOS yet",
            "a composite passed on the stack on macOS (not supported yet)",
        ),
    ]
    .into_iter()
    .find(|(k, _)| e.contains(k))
    .map(|(_, why)| why)
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
        if !within_layout_bits(want, alts, got) {
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
    // The program as compiled, and with `-O` (or the `FIR_PASSES` pipeline) when that changes
    // it.
    let mut builds = vec![("native", m.clone())];
    match fir::backend::prepare_with(src, Some(&opt_pipeline())) {
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
            Err(e) if a64::Os::host() == a64::Os::Darwin && darwin_limit(&e).is_some() => {
                let why = darwin_limit(&e).unwrap();
                tally
                    .lock()
                    .unwrap()
                    .count(format!("{what} not built: {why}"));
                continue;
            }
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
    ev.fact("pipeline", common::evidence::pipeline());
    ev.fact("os", format!("{:?}", a64::Os::host()));
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

/// Found by the layer audit: instruction selection checked only the pointer and address widths
/// of a module's data layout and hard-coded the rest of AAPCS64's. A 64-bit layout with 4-byte
/// `i64` alignment compiled a struct argument to C with its `i64` where C doesn't look (the
/// callee saw 0 for 2); one with an 8-byte `va_list` compiled `va.start` writing AAPCS64's 32
/// bytes into it, over the frame (stuck in the LFIR machine, a crash natively). The backend now
/// refuses any layout but AAPCS64's; the same modules with the default layout compile.
#[test]
fn layer_audit_foreign_data_layouts_are_refused() {
    let cases = [
        "memspace default ptr 64 addr 64 int 8:1 16:2 32:4 64:4
extern func @take(struct<C>{i32, i64}) -> i64 effects[] assume
func @go() -> i64 {
  %a: i32 = int.const 1
  %b: i64 = int.const 2
  %s: struct<C>{i32, i64} = agg.make %a, %b
  %r: i64 = func.call @take(%s)
  func.ret %r
}
",
        "memspace default ptr 64 addr 64 valist 8:8
func @first(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %n: i64 = va.arg %ap
  va.end %ap
  func.ret %n
}
",
        "memspace default ptr 64 addr 64 align 4
func @f() -> i64 {
  %n: i64 = int.const 1
  func.ret %n
}
",
    ];
    for text in cases {
        let m = fir::parse_module(text).unwrap();
        fir::verify_module(&m).unwrap();
        let lowered = fir::backend::prepare(&m, false).unwrap();
        // Linux's AAPCS64, on every host: macOS refuses the variadic case for another reason.
        let linux = a64::Options {
            os: a64::Os::Linux,
            ..a64::Options::default()
        };
        let e = a64::compile(&lowered, &linux).unwrap_err();
        assert!(e.contains("needs AAPCS64's data layout"), "{e}");
        let default = text.lines().skip(1).collect::<Vec<_>>().join("\n");
        let m = fir::parse_module(&default).unwrap();
        fir::verify_module(&m).unwrap();
        a64::compile(&fir::backend::prepare(&m, false).unwrap(), &linux).unwrap();
    }
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
