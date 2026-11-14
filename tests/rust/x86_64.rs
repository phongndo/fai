//! The x86-64 backend, checked against the interpreter natively.
//!
//! Every `// run:` line of the `.fir` files under `tests/`, and the runs of random integer
//! programs from the fuzzer (`progs`, in its integer mode: integers of at most 64 bits, the
//! default data layout, no floats, no variadic functions, no structs by value), are compiled to
//! x86-64, linked with the generated C `main` the AArch64 test uses (`native::harness`: it calls
//! the function with the run's arguments and prints the outcome in `fir run`'s format), run
//! natively on x86-64 Linux, and compared with `fir run`, with the AArch64 test's rules
//! (`aarch64.rs`): runs that end in UB, get stuck, or run out of fuel aren't comparable; `poison`
//! matches anything; non-null pointers print as `ptr ?`; and a difference only in what a taint
//! analysis finds may depend on addresses, within the bits other legal address layouts move, is
//! counted, not failed. HFIR modules compile as `fir compile` compiles them (lowered first),
//! where the `-O` pipeline changes the MFIR the optimized program runs too, and HFIR that
//! selection takes directly (`ptr.field`, `ptr.index`) runs unlowered as well.
//!
//! Three rules of its own, each counted where it applies (decision: x86-64 backend testing): a
//! native outcome may differ from another layout's outcome as it may from the reference's; where
//! the reference ends in an address-dependent arithmetic trap, the native events are compared
//! only up to it (the native run may go on where the reference stopped); and a run whose function
//! branches on what addresses decide, with no other layout finishing to compare against, isn't
//! comparable.
//!
//! A run whose functions the backend can't compile is skipped and counted only for a limitation
//! it declares (`known_limit`: holes, integers wider than 64 bits, data layouts other than
//! System V's, floats,
//! variadic functions defined in FIR, structs and arrays by value, and integer arguments narrower
//! than 32 bits to callees that may be C's); any other failure to compile, an assignment the
//! register allocator's check refuses included, fails the test.
//!
//! There is no LFIR stage: x86-64's machine code is not yet an LFIR dialect (decision: x86-64
//! target), so these native runs are the only check of instruction selection and allocation.
//! Without an x86-64 Linux host (or `$FIR_CC` or `x86_64-unknown-linux-gnu-cc`, and
//! `qemu-x86_64`, elsewhere) the test is skipped
//! with a note, a failure under `FIR_REQUIRE_FULL=1`. `FIR_FUZZ=N` sets the number of random
//! programs (default 100), `FIR_FUZZ_SEED` the seed.

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
use fir::backend::x86_64 as x64;
use native::*;
use taint::{Taint, matches};

fn toolchain(dir: &Path) -> Result<Toolchain, String> {
    let native = cfg!(all(target_arch = "x86_64", target_os = "linux"));
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("x86_64-unknown-linux-gnu-cc") => {
            "x86_64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => return Err("no x86-64 Linux C compiler (set FIR_CC)".to_owned()),
    };
    let runner = if native {
        None
    } else if on_path("qemu-x86_64") {
        Some("qemu-x86_64".to_owned())
    } else {
        return Err("not an x86-64 Linux host, and no qemu-x86_64".to_owned());
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

fn native(dir: &Path, ev: &common::evidence::Evidence) -> Option<Toolchain> {
    ev.fact("pipeline", common::evidence::pipeline());
    // The output is Linux ELF: on macOS nothing can run it (qemu-user is Linux-only), which
    // `fai verify` declares as a host gap there.
    if cfg!(target_os = "macos") {
        common::evidence::host_gap(
            ev,
            "the x86-64 backend emits Linux ELF, which macOS can't run (qemu-user is Linux-only)",
        );
        return None;
    }
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
            common::evidence::require(&format!("native x86-64 runs: {e}"));
            ev.skip(format!("native runs: {e}"));
            None
        }
    }
}

/// Why a compile failure is a declared limitation of the x86-64 backend, if it is one.
fn known_limit(e: &str) -> Option<&'static str> {
    [
        ("can't be compiled", "holes"),
        ("wider than 64 bits", "integers wider than 64 bits"),
        ("needs 64-bit pointers", "a data layout other than 64-bit"),
        (
            "needs System V's data layout",
            "a data layout other than System V's",
        ),
        ("cannot lower:", "an offset the lowering can't represent"),
        ("floats aren't supported", "floats"),
        (
            "structs and arrays by value aren't supported",
            "structs and arrays by value",
        ),
        ("variadic functions aren't supported", "variadic functions"),
        (
            "needs its C signedness",
            "narrow integer arguments to callees that may be C's",
        ),
        (
            "a variadic call with more than two results",
            "variadic calls with more than two results",
        ),
        (
            "a variadic function with more than two results",
            "variadic calls with more than two results",
        ),
    ]
    .into_iter()
    .find(|(k, _)| e.contains(k))
    .map(|(_, why)| why)
}

/// Compile `m` with a harness for `runs` into `dir/name`.
fn build(
    tc: &Toolchain,
    m: &Module,
    runs: &[(String, Vec<String>)],
    dir: &Path,
    name: &str,
) -> Result<PathBuf, String> {
    let o = x64::Options {
        prefix: "fir_".to_owned(),
        extern_prefix: "fir_ext_".to_owned(),
    };
    let asm = x64::compile(m, &o)?;
    let s = dir.join(format!("{name}.s"));
    let c = dir.join(format!("{name}.c"));
    let bin = dir.join(name);
    std::fs::write(&s, asm).unwrap();
    std::fs::write(&c, harness(m, runs, false)).unwrap();
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

/// An outcome's events (`@f(…) -> …`) and its ending (`returned …`, `trap …`).
fn outcome_parts(o: &str) -> (Vec<&str>, &str) {
    let parts: Vec<&str> = o.split("; ").collect();
    let n = parts.iter().take_while(|p| p.starts_with('@')).count();
    (
        parts[..n].to_vec(),
        parts[n..].first().copied().unwrap_or(""),
    )
}

const ADDRESS_DIFF: &str = "differs in address-dependent outcomes";

/// Whether a native outcome `got` of `@f` that isn't the reference's (`want`) is one the
/// semantics allows anyway, and why (for the tally); `None` for a difference. `alts` are the
/// run's outcomes under the other address layouts that are comparable.
fn allowed(taint: &Taint, f: &str, want: &str, alts: &[String], got: &str) -> Option<&'static str> {
    // A native run that crashed, or ran out of time, is never an outcome the semantics allows.
    // (`run_native` marks those `<…>`.)
    if got.starts_with('<') || got.contains("<exit ") {
        return None;
    }
    // A function that branches on what addresses decide, and that no other layout runs to an
    // end the interpreter can compare (each runs out of fuel, say, where the reference's low
    // addresses made a loop short), has only the reference layout's outcome to compare with,
    // which the native addresses needn't reproduce: not comparable, and counted.
    if alts.is_empty() && taint.control(f) {
        return Some("not comparable: control depends on addresses, and no other layout finishes");
    }
    if alts.iter().any(|a| matches(a, got)) {
        return Some("matches another address layout");
    }
    // `exempt` lets an address-dependent trap on one side stand for any ending on the other.
    // That covers a native run that traps where a layout didn't; but a native run that finishes
    // where a layout trapped must answer to a layout that finished too (found in review: a
    // reference's trap excused `returned 8`, and crashes, where every other layout returned 7).
    let traps = |o: &str| outcome_parts(o).1.starts_with("trap ");
    // Against the reference's outcome, or another layout's: each is one the semantics allows,
    // so a native outcome that differs from one of them only in what may depend on addresses
    // (and within the bits the layouts move) is allowed too.
    let excused = |r: &str| {
        (!traps(r) || traps(got)) && taint.exempt(f, r, got) && within_layout_bits(r, alts, got)
    };
    // A reference that ends in a trap may have stopped before events the native run went on to
    // make (decision: Backend testing): compare the native events up to its trap, and the trap
    // with the native ending, which `exempt` allows only for an arithmetic trap that may depend
    // on addresses.
    let early_trap = |r: &str| {
        let (rev, rend) = outcome_parts(r);
        let (gev, gend) = outcome_parts(got);
        if !rend.starts_with("trap ") || gev.len() < rev.len() {
            return false;
        }
        let mut cut: Vec<&str> = gev[..rev.len()].to_vec();
        cut.push(gend);
        taint.exempt(f, r, &cut.join("; "))
    };
    if excused(want) || alts.iter().any(|a| excused(a)) || traps(got) && early_trap(want) {
        return Some(ADDRESS_DIFF);
    }
    // A native run that finishes where the reference and every other
    // layout stop at a trap that may depend on addresses has no finished outcome to compare
    // with: not comparable, and counted.
    if early_trap(want) && alts.iter().all(|a| traps(a)) {
        return Some("not comparable: finishes where every layout traps on addresses");
    }
    None
}

/// Compile and run one module's comparable runs natively, against `fir run` of `src`.
fn check_module(
    tc: &Toolchain,
    src: &Module,
    runs: &[(String, Vec<String>, u64)],
    dir: &Path,
    name: &str,
    tally: &Mutex<Tally>,
    ev: &common::evidence::Evidence,
) -> bool {
    let lowered = src.layer == fir::Layer::Hfir;
    let m = match fir::backend::prepare(src, false).and_then(|m| x64::select(&m).map(|_| m)) {
        Ok(m) => m,
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
    if lowered {
        tally.lock().unwrap().count("(HFIR modules, lowered)");
    }
    let mut comparable = Vec::new();
    for (f, args, fuel) in runs {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        let reference = fir::interp::run_detail(src, f, &a, *fuel, lowered)
            .map(|r| r.line)
            .unwrap_or_else(|e| format!("error {e}"));
        match normalize(&reference) {
            Ok((want, leaks)) => {
                if leaks {
                    tally.lock().unwrap().count("(leak notes dropped)");
                }
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
    let taint = Taint::of(&m);
    if taint.any() {
        tally
            .lock()
            .unwrap()
            .count("(modules with address-dependent outcomes)");
    }
    let differs = |f: &str, want: &str, alts: &[String], got: &str, what: &str| -> bool {
        let Some(why) = allowed(&taint, f, want, alts, got) else {
            return true;
        };
        tally.lock().unwrap().count(format!("{what} {why}"));
        if why == ADDRESS_DIFF && std::env::var_os("FIR_SHOW_ADDRESS_DIFFS").is_some() {
            eprintln!("{name}: {what}\n  want {want}\n  alts {alts:?}\n  got  {got}");
        }
        false
    };
    if vararg_sites(&m).1.values().any(|sites| sites.len() > 1) {
        tally
            .lock()
            .unwrap()
            .count("native skipped: a variadic external function called with several signatures");
        return true;
    }
    let runs: Vec<(String, Vec<String>)> = comparable
        .iter()
        .map(|(f, a, _, _, _)| (f.clone(), a.clone()))
        .collect();
    let mut builds = vec![("native", m.clone())];
    // `FIR_PASSES` tests that pipeline instead of `-O`, as `aarch64.rs` does.
    let optimized = match std::env::var("FIR_PASSES") {
        Ok(spec) if !spec.is_empty() => fir::backend::prepare_with(
            src,
            Some(&fir::passes::Pipeline::parse_fixpoint(&spec, true).expect("FIR_PASSES")),
        ),
        _ => fir::backend::prepare(src, true),
    };
    match optimized {
        Ok(o) if o.render(false) != m.render(false) => builds.push(("native -O", o)),
        Ok(_) => {}
        Err(e) => {
            tally.lock().unwrap().fails.push(format!("{name}: -O: {e}"));
            return false;
        }
    }
    // HFIR whose only building blocks are `ptr.field` and `ptr.index` also compiles without
    // lowering: instruction selection handles those two itself. Nothing else reaches them.
    if lowered && x64::select(src).is_ok() {
        builds.push(("native, HFIR selected directly", src.clone()));
    }
    let mut ok = true;
    for (what, bm) in &builds {
        let bname = match *what {
            "native" => name.to_owned(),
            "native -O" => format!("{name}-O"),
            _ => format!("{name}-hfir"),
        };
        let bin = match build(tc, bm, &runs, dir, &bname) {
            Ok(b) => b,
            Err(e) => {
                let mut t = tally.lock().unwrap();
                match known_limit(&e) {
                    Some(why) => t.count(format!("{what} not compiled: {why}")),
                    None => {
                        t.fails.push(format!("{name} ({what}): {e}"));
                        ok = false;
                    }
                }
                continue;
            }
        };
        ev.fact("execution coverage", "interpreter profile of the exact compiled module, same arguments; native proxy, not a hardware trace");
        for (k, (f, args, fuel, want, alts)) in comparable.iter().enumerate() {
            let got = run_native(tc, &bin, k);
            if matches(want, &got) {
                let mut t = tally.lock().unwrap();
                t.count(format!("{what} matches"));
                if want.starts_with("trap ") || want.contains("; trap ") {
                    t.count(format!("{what} matches (traps)"));
                }
                if want.contains("threw ") {
                    t.count(format!("{what} matches (threw)"));
                }
            } else if differs(f, want, alts, &got, what) {
                ok = false;
                tally.lock().unwrap().fails.push(format!(
                    "{name} @{f}({}): {what}\n  want {want}\n  alts {alts:?}\n  got  {got}",
                    args.join(", ")
                ));
                continue;
            }
            let fuel = if lowered { 16 * *fuel } else { *fuel };
            match native_profile(bm, f, args, fuel, &got) {
                Some(profile) => {
                    ev.executed(&profile);
                    ev.count("native runs with execution profile", 1);
                }
                None => ev.count("native runs without a matching execution profile", 1),
            }
        }
    }
    ok
}

#[test]
fn fixtures_run_natively() {
    let ev = common::evidence::Evidence::new("x86_64_fixtures");
    let dir = scratch("x86_64-fixtures");
    let Some(tc) = native(&dir, &ev) else {
        ev.write();
        return;
    };
    let tally = Mutex::new(Tally::default());
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
            |m: &Module| fir::backend::prepare(m, false).and_then(|l| x64::select(&l).map(|_| ()));
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
        let runs: Vec<_> = kept
            .into_iter()
            .map(|(f, a)| (f, a, fir::interp::DEFAULT_FUEL))
            .collect();
        let stem = name.replace(['/', '.'], "_");
        check_module(&tc, &m, &runs, &dir, &stem, &tally, &ev);
    }
    eprintln!("{modules} fixture modules compiled");
    ev.count("fixture modules compiled", modules);
    report("x86-64 fixtures", tally.into_inner().unwrap(), &ev);
}

#[test]
fn random_programs_run_natively() {
    let ev = common::evidence::Evidence::new("x86_64_fuzz");
    let dir = scratch("x86_64-fuzz");
    let Some(tc) = native(&dir, &ev) else {
        ev.write();
        return;
    };
    let count = env_u64("FIR_FUZZ", 100);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
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
                    let mut rng = progs::Rng::integers(seed.wrapping_mul(0x1_0000_0001) ^ k);
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
                    if !check_module(&tc, &m, &runs, &dir, &name, &tally, &ev) {
                        std::fs::write(dir.join(format!("{name}.fir")), &prog.text).unwrap();
                    } else {
                        for ext in [
                            "", ".s", ".c", "-O", "-O.s", "-O.c", "-hfir", "-hfir.s", "-hfir.c",
                        ] {
                            let _ = std::fs::remove_file(dir.join(format!("{name}{ext}")));
                        }
                    }
                }
            });
        }
    });
    ev.fact("seed", seed.to_string());
    report(
        &format!("{count} random integer programs (seed {seed})"),
        tally.into_inner().unwrap(),
        &ev,
    );
}

/// What the backend refuses, it refuses with a declared limitation.
#[test]
fn refusals_name_their_limitation() {
    let cases = [
        "func @f(%x: f64) -> f64 {\n  func.ret %x\n}\n",
        "extern func @g(i8) effects[] assume\nfunc @f(%x: i8) {\n  func.call @g(%x)\n  func.ret\n}\n",
        "func @f(%x: i64, ...) -> i64 {\n  func.ret %x\n}\n",
        "func @f(%x: struct<C>{i64, i64}) -> i64 {\n  %a: i64 = agg.extract %x, 0\n  func.ret %a\n}\n",
    ];
    for text in cases {
        let m = fir::parse_module(text).unwrap();
        fir::verify_module(&m).unwrap();
        let e = fir::backend::prepare(&m, false)
            .and_then(|m| x64::compile(&m, &x64::Options::default()))
            .unwrap_err();
        assert!(known_limit(&e).is_some(), "{text}: {e}");
    }
}

/// Found with the x86-64 fuzzer: an address passed to a block of `cf.blocks` (by `cf.br`, from
/// inside a `cf.if` too, `cf.cond_br`, or `cf.switch`) lost its taint, so a returned address
/// wasn't excused. A jump's label and its block's are compared as text now.
#[test]
fn taint_flows_through_block_parameters() {
    for jump in [
        "cf.br ^exit(%a)",
        "cf.if %c {\n      cf.br ^exit(%a)\n    }\n    cf.br ^exit(%a)",
        "cf.cond_br %c, ^exit(%a), ^exit(%a)",
        "cf.switch %c, default ^exit(%a), [1: ^exit(%a)]",
    ] {
        let text = format!(
            "extern func @x0() -> ptr effects[] assume\nfunc @f0() -> i64 {{\n  %p: ptr = func.addr @x0\n  %a: i64 = ptr.expose %p\n  %c: i1 = int.const 0\n  %r: i64 = cf.blocks {{\n  ^entry:\n    {jump}\n  ^exit(%x: i64):\n    cf.yield %x\n  }}\n  func.ret %r\n}}\n"
        );
        let m = fir::parse_module(&text).unwrap();
        fir::verify_module(&m).unwrap();
        let t = Taint::of(&m);
        assert!(
            t.exempt("f0", "returned i64 4096", "returned i64 93824992235936"),
            "{text}"
        );
    }
}

/// Found in review: a frame's locals were sized in 32 bits, so a 4 GiB slot left a 16-byte frame
/// whose other slots were written far past `rsp`. Frames the 32-bit displacements can't reach
/// are refused.
#[test]
fn oversized_frames_are_refused() {
    let text = "func @f() -> i64 {\n  %big: ptr = mem.stack 4294967296, align 8\n  %p: ptr = mem.stack 8, align 8\n  %v: i64 = int.const 42\n  mem.store i64 %v, %p, align 8\n  %r: i64 = mem.load %p, align 8\n  func.ret %r\n}\n";
    let m = fir::parse_module(text).unwrap();
    fir::verify_module(&m).unwrap();
    let e = fir::backend::prepare(&m, false)
        .and_then(|m| x64::compile(&m, &x64::Options::default()))
        .unwrap_err();
    assert!(e.contains("frame needs"), "{e}");
}

/// Found in review: a reference that traps on an address-dependent division excused any native
/// ending, a wrong number, a crash, or a time limit, though every other layout returned 7.
#[test]
fn a_reference_trap_does_not_excuse_any_ending() {
    let text = "func @f() -> i64 {\n  %p: ptr = mem.stack 8, align 8\n  %a: i64 = ptr.addr %p\n  %k: i64 = int.const 4096\n  %d: i64 = int.sub.wrap %a, %k\n  %one: i64 = int.const 1\n  %q: i64 = int.div.s.trap %one, %d @1:1\n  %r: i64 = int.const 7\n  func.ret %r\n}\n";
    let m = fir::parse_module(text).unwrap();
    fir::verify_module(&m).unwrap();
    let run = |addrs| {
        let r = fir::interp::run_detail_in(&m, "f", &[], 100, false, addrs).unwrap();
        normalize(&r.line).ok().map(|x| x.0)
    };
    let want = run(fir::interp::Addresses::Low).unwrap();
    assert!(want.starts_with("trap div0"), "{want}");
    let alts: Vec<String> = layouts().into_iter().filter_map(run).collect();
    assert!(!alts.is_empty() && alts.iter().all(|a| a == "returned i64 7"));
    let taint = Taint::of(&fir::backend::prepare(&m, false).unwrap());
    for got in ["returned i64 7", "trap div0 @1:1"] {
        assert!(allowed(&taint, "f", &want, &alts, got).is_some(), "{got}");
    }
    for got in [
        "returned i64 8",
        "<exit None: >",
        "<timed out>",
        "trap div0 @1:1<exit Some(1): >",
    ] {
        assert!(allowed(&taint, "f", &want, &alts, got).is_none(), "{got}");
    }
    // With no layout that finishes to answer to, a finished native run isn't comparable; a
    // crash still differs.
    let none: &[String] = &[];
    assert!(allowed(&taint, "f", &want, none, "returned i64 8").is_some());
    assert!(allowed(&taint, "f", &want, none, "<timed out>").is_none());
}

/// Found in review: layouts where a run is undefined are left out of the comparison, and the
/// rest may agree on bits that no alignment forces (a slot of alignment 2 read at 8, every
/// surviving layout a multiple of 64). Bits below those that move are then not held.
#[test]
fn low_bits_are_free_when_layouts_were_left_out() {
    let n = layouts().len();
    let want = "returned i64 4096".to_owned();
    let alts: Vec<String> = ["returned i64 1048576", "returned i64 2097152"]
        .map(str::to_owned)
        .to_vec();
    assert!(alts.len() < n);
    assert!(!within_moved_bits(&want, &alts, "returned i64 4320"));
    assert!(within_layout_bits(&want, &alts, "returned i64 4320"));
    // The bits above still hold.
    assert!(!within_layout_bits(
        &want,
        &alts,
        "returned i64 1099511627776"
    ));
}

/// As on AArch64 (found by the layer audit there): selection hard-codes System V's alignments,
/// so a module laid out otherwise is refused; the same modules with the default layout compile.
#[test]
fn foreign_data_layouts_are_refused() {
    let cases = [
        "memspace default ptr 64 addr 64 int 8:1 16:2 32:4 64:4
func @f(%p: ptr) -> i64 {
  %r: i64 = mem.load %p, align 4
  func.ret %r
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
        let e = x64::compile(&lowered, &x64::Options::default()).unwrap_err();
        assert!(e.contains("needs System V's data layout"), "{e}");
        assert!(known_limit(&e).is_some(), "{e}");
        let default = text.lines().skip(1).collect::<Vec<_>>().join("\n");
        let m = fir::parse_module(&default).unwrap();
        fir::verify_module(&m).unwrap();
        x64::compile(
            &fir::backend::prepare(&m, false).unwrap(),
            &x64::Options::default(),
        )
        .unwrap();
    }
}
