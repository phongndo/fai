//! Differential testing of the passes: every fixture under `tests/` and random programs (see
//! `progs`) are optimized with the default pipeline, verifying after every pass, and each run of
//! the optimized module must refine the same run of the original, in this crate's interpreter:
//!
//! * the original is UB or stuck after some events: the optimized run must perform those events
//!   first, then may do anything (Lean's trace refinement);
//! * the original runs out of fuel: the optimized run (which never takes more steps) must
//!   perform its events first;
//! * the original is `ambiguous`: nothing is compared (the theorems assume `Func.Decided`);
//! * otherwise both print the same line: the same events, then the same ending.
//!
//! The optimized module must also verify, print, and parse back to the same text, and for the
//! fixtures `fir-ref check` must accept it too. Random HFIR programs are also lowered to MFIR,
//! whose exceptions are calls that name their handlers (`func.invoke`) and blocks that pass them
//! on, and the lowering is optimized and compared the same way (with 16 times the fuel); the
//! statistics count the programs with exceptions and their runs.
//!
//! `FIR_PASSES=p,q` tests that pipeline instead of `-O`, to a fixed point (experimental passes
//! included).
//! By default 200 programs run; `FIR_FUZZ=N` runs N, `FIR_FUZZ_SEED=S` picks another seed (as in
//! `fuzz.rs`). The test prints how often each pass fired and how the runs compared. Failing
//! programs are written to `target/tmp/opt/`, with their optimized form. `FIR_REF=none` skips
//! only the `fir-ref check` of the fixtures.

#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod progs;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Mutex;

use fir::passes::{PASSES, Pipeline, Remarks};

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).map_or(default, |s| s.parse().expect(name))
}

/// A run's line split into its events and its ending.
fn split(line: &str) -> (Vec<&str>, &str) {
    let mut events = Vec::new();
    let mut rest = line;
    while rest.starts_with('@') {
        match rest.split_once("; ") {
            Some((e, r)) => {
                events.push(e);
                rest = r;
            }
            None => break,
        }
    }
    (events, rest)
}

/// How a target run compared with its source run.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Cmp {
    /// Same line.
    Equal,
    /// The source is UB or stuck: only its events were compared.
    SourceUb,
    /// The source ran out of fuel: only its events were compared.
    SourceFuel,
    /// The source is ambiguous: nothing was compared.
    SourceAmbiguous,
}

/// A run's line with its allocations renumbered in order of first appearance (`ptr #7` and
/// `ptr #7+8` become `#a0` and `#a0+8`, the next one `#a1`, …): what is left of a run once
/// allocation numbers are taken as unobservable.
fn rename_allocs(line: &str) -> String {
    let mut names: Vec<&str> = Vec::new();
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(i) = rest.find('#') {
        out.push_str(&rest[..=i]);
        rest = &rest[i + 1..];
        let n = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        if n > 0 {
            let id = &rest[..n];
            let k = names.iter().position(|x| *x == id).unwrap_or_else(|| {
                names.push(id);
                names.len() - 1
            });
            out.push_str(&format!("a{k}"));
            rest = &rest[n..];
        }
    }
    out.push_str(rest);
    out
}

/// Whether target run `t` refines source run `s` (both as `fir run` prints them, or the error).
/// With `stackdce` in the pipeline, which deletes allocations and so renumbers the later ones,
/// the runs are compared up to renaming allocations ([`rename_allocs`]), the assumption that
/// pass rests on.
fn refines(t: &Result<String, String>, s: &Result<String, String>) -> Result<Cmp, String> {
    if in_pipeline("stackdce") {
        let (t, s) = (
            t.clone().map(|l| rename_allocs(&l)),
            s.clone().map(|l| rename_allocs(&l)),
        );
        return refines_exactly(&t, &s);
    }
    refines_exactly(t, s)
}

fn refines_exactly(t: &Result<String, String>, s: &Result<String, String>) -> Result<Cmp, String> {
    let (Ok(tl), Ok(sl)) = (t, s) else {
        return if t == s {
            Ok(Cmp::Equal)
        } else {
            Err("different errors".into())
        };
    };
    let ((te, tend), (se, send)) = (split(tl), split(sl));
    let prefix = || {
        if te.len() >= se.len() && te[..se.len()] == se[..] {
            Ok(())
        } else {
            Err(format!("the events {se:?} don't start the target's {te:?}"))
        }
    };
    if send.starts_with("ub ") || send.starts_with("stuck") {
        prefix().map(|()| Cmp::SourceUb)
    } else if send.starts_with("out of fuel") {
        prefix().map(|()| Cmp::SourceFuel)
    } else if send.starts_with("ambiguous") {
        Ok(Cmp::SourceAmbiguous)
    } else if tl == sl {
        Ok(Cmp::Equal)
    } else {
        Err(format!("the ending {send:?} became {tend:?}"))
    }
}

/// The pipeline under test: the default `-O` one, or `FIR_PASSES=p,q,…` (in order, to a fixed
/// point, as `fir compile --passes`, `fir measure`, and the backend suites run it; experimental
/// passes allowed), so a new or experimental pass gets this whole differential suite without
/// editing it, in the same configuration `fai experiment` measures. A full verification
/// clears `FIR_PASSES`.
fn pipeline() -> Pipeline {
    match std::env::var("FIR_PASSES") {
        Ok(spec) if !spec.is_empty() => Pipeline::parse_fixpoint(&spec, true).expect("FIR_PASSES"),
        _ => Pipeline::default_opt(),
    }
}

/// Whether the pipeline under test runs this pass.
fn in_pipeline(name: &str) -> bool {
    pipeline().passes.iter().any(|p| p.name == name)
}

/// Optimize a verified module with [`pipeline`], verifying after every pass. Gives the
/// optimized module and the changes per pass, or what went wrong.
fn optimize(m: &fir::Module) -> Result<(fir::Module, Vec<u64>), String> {
    let mut opt = m.clone();
    let mut p = pipeline();
    p.verify_each = true;
    let report = p
        .run(&mut opt, &mut Remarks::new(false))
        .map_err(|e| e.to_string())?;
    fir::verify_module(&opt).map_err(|e| format!("the result doesn't verify: {e}"))?;
    let text = opt.render(true);
    let back =
        fir::parse_module(&text).map_err(|e| format!("the result doesn't parse back: {e}"))?;
    fir::verify_module(&back).map_err(|e| format!("the result doesn't verify as text: {e}"))?;
    if back.render(true) != text {
        return Err("the result doesn't print back the same".into());
    }
    let counts = PASSES.iter().map(|p| report.changes_by(p.name)).collect();
    Ok((opt, counts))
}

fn run(m: &fir::Module, f: &str, args: &[String], fuel: u64) -> Result<String, String> {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    fir::interp::run(m, f, &args, fuel)
}

#[test]
fn optimized_fixtures_refine_the_originals() {
    let tool = common::reference();
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("opt");
    std::fs::create_dir_all(&dir).unwrap();
    let mut fails = Vec::new();
    let mut totals = vec![0u64; PASSES.len()];
    let (mut files, mut runs) = (0, 0);
    for file in &common::fir_files() {
        let name = common::display_name(file);
        let text = std::fs::read_to_string(file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() {
            continue;
        }
        files += 1;
        let (opt, counts) = match optimize(&m) {
            Ok(x) => x,
            Err(e) => {
                fails.push(format!("{name}: {e}"));
                continue;
            }
        };
        for (t, c) in totals.iter_mut().zip(&counts) {
            *t += c;
        }
        if let Some(tool) = &tool {
            let out = dir.join(name.replace('/', "_"));
            std::fs::write(&out, opt.render(true)).unwrap();
            let theirs = common::outcome(&common::run(tool, "check", &out, &[]), &out);
            let ours = fir::verify_module(&opt).map(|_| ());
            if theirs.is_err() || ours.is_err() {
                fails.push(format!(
                    "{name}: fir-ref check of the optimized module: {theirs:?}"
                ));
            }
        }
        for line in text.lines() {
            let Some(body) = line.trim().strip_prefix("// run:") else {
                continue;
            };
            let (call, _) = body.split_once(" -> ").unwrap();
            let (f, rest) = call.trim()[1..].split_once('(').unwrap();
            let inner = rest.strip_suffix(')').unwrap();
            let args: Vec<String> = if inner.trim().is_empty() {
                vec![]
            } else {
                inner.split(',').map(|a| a.trim().to_owned()).collect()
            };
            runs += 1;
            let fuel = fir::interp::DEFAULT_FUEL;
            let (s, t) = (run(&m, f, &args, fuel), run(&opt, f, &args, fuel));
            if let Err(e) = refines(&t, &s) {
                fails.push(format!(
                    "{name}: @{f}({}): {e}\n  original:  {s:?}\n  optimized: {t:?}",
                    args.join(", ")
                ));
            }
        }
    }
    eprintln!("{files} fixtures, {runs} runs; changes:");
    let ev = common::evidence::Evidence::new("opt_fixtures");
    ev.fact("pipeline", common::evidence::pipeline());
    for (p, n) in PASSES.iter().zip(&totals) {
        eprintln!("  {n:6}  {}", p.name);
        ev.count(format!("pass {}: changes", p.name), *n);
    }
    ev.count("fixtures", files as u64);
    ev.count("runs compared", runs as u64);
    ev.write();
    assert!(files > 0 && runs > 0);
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

#[test]
fn optimized_random_programs_refine_the_originals() {
    let count = env_u64("FIR_FUZZ", 200);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("opt");
    std::fs::create_dir_all(&dir).unwrap();
    // Per pass: changes, and programs it changed.
    let fired = Mutex::new(vec![(0u64, 0u64); PASSES.len()]);
    let compared = Mutex::new(BTreeMap::<Cmp, u64>::new());
    let lowered = Mutex::new(BTreeMap::<Cmp, u64>::new());
    let exceptions = Mutex::new(BTreeMap::<&'static str, u64>::new());
    let fails = Mutex::new(Vec::<String>::new());
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
                    let mut rng = progs::Rng::new(seed.wrapping_mul(0x1_0000_0001) ^ k);
                    let prog = progs::program(&mut rng);
                    let file = dir.join(format!("s{seed}-p{k}.fir"));
                    let m = fir::parse_module(&prog.text)
                        .and_then(|m| fir::verify_module(&m).map(|_| m))
                        .unwrap_or_else(|e| panic!("generated program s{seed}-p{k} is invalid: {e}"));
                    let keep = |msg: String, opt: Option<&fir::Module>| {
                        std::fs::write(&file, &prog.text).unwrap();
                        if let Some(o) = opt {
                            std::fs::write(file.with_extension("opt.fir"), o.render(true)).unwrap();
                        }
                        fails
                            .lock()
                            .unwrap()
                            .push(format!("{}: {msg}", file.display()));
                    };
                    let (opt, counts) = match optimize(&m) {
                        Ok(x) => x,
                        Err(e) => {
                            keep(e, None);
                            continue;
                        }
                    };
                    {
                        let mut f = fired.lock().unwrap();
                        for (x, &c) in f.iter_mut().zip(&counts) {
                            x.0 += c;
                            x.1 += u64::from(c > 0);
                        }
                    }
                    let throws = ["cf.try", "exn.throw", "func.invoke"]
                        .iter()
                        .any(|op| prog.text.contains(op));
                    for (args, fuel) in &prog.runs {
                        let (s, t) = (run(&m, "f0", args, *fuel), run(&opt, "f0", args, *fuel));
                        if throws {
                            let mut x = exceptions.lock().unwrap();
                            *x.entry("runs of programs with exceptions").or_default() += 1;
                            if s.as_ref().is_ok_and(|l| l.contains("threw ")) {
                                *x.entry("runs that threw").or_default() += 1;
                            }
                        }
                        match refines(&t, &s) {
                            Ok(c) => *compared.lock().unwrap().entry(c).or_default() += 1,
                            Err(e) => keep(
                                format!(
                                    "@f0 {} --fuel {fuel}: {e}\n  original:  {s:?}\n  optimized: {t:?}",
                                    args.join(" ")
                                ),
                                Some(&opt),
                            ),
                        }
                    }
                    // The lowering, optimized: MFIR with handlers.
                    if m.layer != fir::Layer::Hfir {
                        continue;
                    }
                    let Ok(l) = fir::lower_checked(&m) else {
                        keep("the lowering failed".into(), None);
                        continue;
                    };
                    let (lopt, _) = match optimize(&l) {
                        Ok(x) => x,
                        Err(e) => {
                            keep(format!("optimizing the lowering: {e}"), Some(&l));
                            continue;
                        }
                    };
                    if l.render(false).contains("func.invoke") {
                        *exceptions
                            .lock()
                            .unwrap()
                            .entry("lowered programs with func.invoke")
                            .or_default() += 1;
                    }
                    for (args, fuel) in &prog.runs {
                        let fuel = 16 * fuel;
                        let (s, t) = (run(&l, "f0", args, fuel), run(&lopt, "f0", args, fuel));
                        match refines(&t, &s) {
                            Ok(c) => *lowered.lock().unwrap().entry(c).or_default() += 1,
                            Err(e) => keep(
                                format!(
                                    "lowered: @f0 {} --fuel {fuel}: {e}\n  original:  {s:?}\n  optimized: {t:?}",
                                    args.join(" ")
                                ),
                                Some(&lopt),
                            ),
                        }
                    }
                }
            });
        }
    });
    let fired = fired.into_inner().unwrap();
    let ev = common::evidence::Evidence::new("opt_fuzz");
    ev.fact("pipeline", common::evidence::pipeline());
    ev.fact("seed", seed.to_string());
    ev.count("programs", count);
    eprintln!("{count} programs (seed {seed}); changes, and programs changed, per pass:");
    for (p, (n, progs)) in PASSES.iter().zip(&fired) {
        eprintln!("  {n:8} {progs:6}  {}", p.name);
        ev.count(format!("pass {}: changes", p.name), *n);
        ev.count(format!("pass {}: programs changed", p.name), *progs);
    }
    eprintln!("runs compared:");
    for (c, n) in compared.into_inner().unwrap() {
        eprintln!("  {n:8}  {c:?}");
        ev.count(format!("runs compared: {c:?}"), n);
    }
    ev.write();
    eprintln!("runs of lowered HFIR programs compared:");
    for (c, n) in lowered.into_inner().unwrap() {
        eprintln!("  {n:8}  {c:?}");
    }
    eprintln!("exceptions:");
    for (c, n) in exceptions.into_inner().unwrap() {
        eprintln!("  {n:8}  {c}");
    }
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
    if count >= 200 {
        for (p, (n, _)) in PASSES
            .iter()
            .zip(&fired)
            .filter(|(p, _)| in_pipeline(p.name))
        {
            assert!(*n > 0, "pass {} never fired on {count} programs", p.name);
        }
    }
}

/// A small function whose outcome shows what memory holds, for the memory passes: one 16-byte
/// stack slot, zeroed, then stores and loads of integers, bytes, and pointers of 1 to 8 bytes at
/// offsets 0, 4, and 8 (all with align 1, so nothing is misaligned), through pointer variables
/// that alias (`%p` and `%z`, its offset by 0). Stores often come back to back through one
/// pointer, of the same size or not, and are often read back at once. Copies, calls, and `cf.if`
/// regions cut the straight line. Every integer load is folded into the returned `i64`.
struct Soup<'r> {
    rng: &'r mut progs::Rng,
    body: String,
    /// Values by type.
    vals: Vec<(String, &'static str)>,
    /// Integer values to fold into the result, with their widths.
    folds: Vec<(String, u32)>,
    next: u32,
}

const SOUP_PTRS: [&str; 4] = ["%p", "%p4", "%p8", "%z"];
const SOUP_TYS: [&str; 10] = [
    "i8", "i16", "i24", "i32", "i64", "b8", "b16", "b32", "b64", "ptr",
];

impl Soup<'_> {
    fn fresh(&mut self) -> String {
        self.next += 1;
        format!("%v{}", self.next)
    }

    fn line(&mut self, s: &str) {
        self.body.push_str("  ");
        self.body.push_str(s);
        self.body.push('\n');
    }

    /// Define `v: t = body`; fold it if it is an integer.
    fn def(&mut self, t: &'static str, body: &str) -> String {
        let v = self.fresh();
        self.line(&format!("{v}: {t} = {body}"));
        if let Some(w) = t.strip_prefix('i') {
            self.folds.push((v.clone(), w.parse().unwrap()));
        }
        self.vals.push((v.clone(), t));
        v
    }

    /// A value of type `t`, defining what it needs.
    fn value(&mut self, t: &'static str) -> String {
        let have: Vec<String> = self
            .vals
            .iter()
            .filter(|v| v.1 == t)
            .map(|v| v.0.clone())
            .collect();
        if !have.is_empty() && self.rng.chance(70) {
            return have[self.rng.below(have.len() as u64) as usize].clone();
        }
        match t {
            "ptr" => self.rng.pick(&["%p", "%q"]).to_owned(),
            "i64" => {
                let n = self.rng.below(1000);
                self.def(t, &format!("int.const {n}"))
            }
            _ if t.starts_with('i') => {
                let src = self.rng.pick(&["%a", "%b"]);
                self.def(t, &format!("int.trunc.wrap {src}"))
            }
            _ => {
                let p = self.rng.pick(&SOUP_PTRS);
                self.def(t, &format!("mem.load {p}, align 1"))
            }
        }
    }

    fn stmt(&mut self) {
        let t = self.rng.pick(&SOUP_TYS);
        let p = self.rng.pick(&SOUP_PTRS);
        match self.rng.below(10) {
            0..=4 => {
                // A store, often followed through the same pointer by another store, a load,
                // or both.
                let t2 = if self.rng.chance(70) {
                    t
                } else {
                    self.rng.pick(&SOUP_TYS)
                };
                let p2 = if self.rng.chance(80) {
                    p
                } else {
                    self.rng.pick(&SOUP_PTRS)
                };
                let (v, v2) = (self.value(t), self.value(t2));
                self.line(&format!("mem.store {t} {v}, {p}, align 1"));
                if self.rng.chance(50) {
                    self.line(&format!("mem.store {t2} {v2}, {p2}, align 1"));
                }
                if self.rng.chance(50) {
                    let lt = self.rng.pick(&[t, t2]);
                    self.def(lt, &format!("mem.load {p2}, align 1"));
                }
            }
            5..=6 => {
                self.def(t, &format!("mem.load {p}, align 1"));
            }
            7 => {
                let x = self.value(t);
                let c = self.def(t, &format!("copy {x}"));
                if self.rng.chance(50) {
                    self.def(t, &format!("copy {c}"));
                }
            }
            8 => {
                let x = self.value("i64");
                self.def("i64", &format!("func.call @g({x})"));
            }
            _ => {
                let v = self.value(t);
                self.line("cf.if %c {");
                for _ in 0..2 {
                    self.line(&format!("  mem.store {t} {v}, {p}, align 1"));
                }
                self.line("}");
            }
        }
    }
}

fn soup(rng: &mut progs::Rng) -> String {
    let mut g = Soup {
        rng,
        body: String::new(),
        vals: vec![
            ("%a".into(), "i64"),
            ("%b".into(), "i64"),
            ("%q".into(), "ptr"),
        ],
        folds: Vec::new(),
        next: 0,
    };
    for _ in 0..g.rng.below(14) + 4 {
        g.stmt();
    }
    let mut acc = "%zero".to_owned();
    for (v, w) in std::mem::take(&mut g.folds) {
        let wide = if w == 64 {
            v
        } else {
            let x = g.fresh();
            g.line(&format!("{x}: i64 = int.zext {v}"));
            x
        };
        let x = g.fresh();
        g.line(&format!("{x}: i64 = int.xor {acc}, {wide}"));
        acc = x;
    }
    format!(
        "func @g(%x: i64) -> i64 {{
  func.ret %x
}}

func @f0(%a: i64, %b: i64, %q: ptr, %c: i1) -> i64 {{
  %p: ptr = mem.stack 16, align 8
  %zero: i64 = int.const 0
  mem.store i64 %zero, %p, align 1
  %n4: i64 = int.const 4
  %p4: ptr = ptr.offset.inbounds %p, %n4
  %n8: i64 = int.const 8
  %p8: ptr = ptr.offset.inbounds %p, %n8
  mem.store i64 %zero, %p8, align 1
  %z: ptr = ptr.offset.inbounds %p, %zero
{}  func.ret {acc}
}}
",
        g.body
    )
}

#[test]
fn optimized_memory_programs_refine_the_originals() {
    let count = env_u64("FIR_FUZZ", 200) * 2;
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("opt");
    std::fs::create_dir_all(&dir).unwrap();
    let mut fired = vec![0u64; PASSES.len()];
    let mut compared = BTreeMap::<Cmp, u64>::new();
    let mut fails = Vec::new();
    for k in 0..count {
        let mut rng = progs::Rng::new(seed.wrapping_mul(0x1_0000_0003) ^ k);
        let text = soup(&mut rng);
        let file = dir.join(format!("mem-s{seed}-p{k}.fir"));
        let m = fir::parse_module(&text)
            .and_then(|m| fir::verify_module(&m).map(|_| m))
            .unwrap_or_else(|e| panic!("memory program {k} is invalid: {e}\n{text}"));
        let (opt, counts) = match optimize(&m) {
            Ok(x) => x,
            Err(e) => {
                std::fs::write(&file, &text).unwrap();
                fails.push(format!("{}: {e}", file.display()));
                continue;
            }
        };
        for (f, c) in fired.iter_mut().zip(&counts) {
            *f += c;
        }
        for args in [["5", "-1", "null", "1"], ["70000", "3", "null", "0"]] {
            let args: Vec<String> = args.iter().map(|a| (*a).to_owned()).collect();
            let fuel = fir::interp::DEFAULT_FUEL;
            let (s, t) = (run(&m, "f0", &args, fuel), run(&opt, "f0", &args, fuel));
            match refines(&t, &s) {
                Ok(c) => *compared.entry(c).or_default() += 1,
                Err(e) => {
                    std::fs::write(&file, &text).unwrap();
                    std::fs::write(file.with_extension("opt.fir"), opt.render(true)).unwrap();
                    fails.push(format!(
                        "{}: @f0 {}: {e}\n  original:  {s:?}\n  optimized: {t:?}",
                        file.display(),
                        args.join(" ")
                    ));
                }
            }
        }
    }
    eprintln!("{count} memory programs (seed {seed}); changes per pass:");
    for (p, n) in PASSES.iter().zip(&fired) {
        eprintln!("  {n:8}  {}", p.name);
    }
    eprintln!("runs compared:");
    for (c, n) in &compared {
        eprintln!("  {n:8}  {c:?}");
    }
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
    // The memory programs' slots escape, or are read with another type than they are written,
    // so promotion (and deleting the slots it leaves) has nothing to do there: `tests/mem2reg.rs`
    // generates programs for it.
    for (p, n) in PASSES
        .iter()
        .zip(&fired)
        .filter(|(p, _)| in_pipeline(p.name) && !["mem2reg", "stackdce"].contains(&p.name))
    {
        assert!(*n > 0, "pass {} never fired on the memory programs", p.name);
    }
}

/// `fir opt`: the default pipeline, named passes, remarks, stats, and errors.
#[test]
fn command_line() {
    use std::process::Command;
    let fir = env!("CARGO_BIN_EXE_fir");
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("opt");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("cli.fir");
    std::fs::write(
        &file,
        "func @f(%x: i32) -> i32 {
  %p: ptr = mem.stack 4, align 4 @1:3
  mem.store i32 %x, %p, align 4 @2:3
  mem.store i32 %x, %p, align 4 @3:3
  %y: i32 = mem.load %p, align 4 @4:3
  func.ret %y @5:3
}
",
    )
    .unwrap();
    let opt = |args: &[&str]| {
        let out = Command::new(fir)
            .arg("opt")
            .arg(&file)
            .args(args)
            .output()
            .unwrap();
        (
            String::from_utf8(out.stdout).unwrap(),
            String::from_utf8(out.stderr).unwrap(),
            out.status.code(),
        )
    };
    let (out, err, code) = opt(&["--remarks", "--no-locs"]);
    assert_eq!(code, Some(0), "{err}");
    assert_eq!(
        out,
        "func @f(%x: i32) -> i32 {\n  %p: ptr = mem.stack 4, align 4\n  mem.store i32 %x, %p, align 4\n  func.ret %x\n}\n"
    );
    assert_eq!(
        err,
        "fwd: load @4:3 forwarded from store @3:3 (now a copy)
copyprop: %y read as %x at @5:3 (copy @4:3)
dse: deleted store @2:3 (overwritten by @3:3)
dce: deleted unused copy @4:3
"
    );
    let (out, err, code) = opt(&["--passes", "dse", "--remarks"]);
    assert_eq!(code, Some(0));
    assert_eq!(out.matches("mem.store").count(), 1);
    assert!(out.contains("mem.load"));
    assert_eq!(err, "dse: deleted store @2:3 (overwritten by @3:3)\n");
    let (_, err, code) = opt(&["-O", "--stats"]);
    assert_eq!(code, Some(0));
    assert!(
        err.starts_with("2 rounds\n") && err.contains("dse:"),
        "{err}"
    );
    let (_, err, code) = opt(&["--passes", "gvn"]);
    assert_eq!(code, Some(1));
    assert!(
        err.ends_with(
            "no pass \"gvn\"; the passes are dse, fwd, copyprop, dce, mem2reg, stackdce\n"
        )
    );
}

#[test]
fn renames_allocations_in_order() {
    assert_eq!(
        rename_allocs("@x0(ptr #6+8, ptr #13) -> (); threw ptr #6"),
        "@x0(ptr #a0+8, ptr #a1) -> (); threw ptr #a0"
    );
    assert_eq!(rename_allocs("returned i32 3"), "returned i32 3");
}

#[test]
fn split_and_refines() {
    let ok = |s: &str| Ok::<_, String>(s.to_owned());
    assert_eq!(
        split("@x0(1) -> (); returned"),
        (vec!["@x0(1) -> ()"], "returned")
    );
    assert_eq!(
        refines(
            &ok("@x0(1) -> (); returned i32 3"),
            &ok("@x0(1) -> (); ub poison @1:1")
        ),
        Ok(Cmp::SourceUb)
    );
    assert!(refines(&ok("returned i32 3"), &ok("@x0(1) -> (); ub poison @1:1")).is_err());
    assert!(refines(&ok("returned i32 3"), &ok("returned i32 4")).is_err());
    assert_eq!(
        refines(&ok("returned"), &ok("ambiguous @1:1")),
        Ok(Cmp::SourceAmbiguous)
    );
}

/// How many ops are in the body's regions.
fn linked_ops(body: &fir::Body) -> usize {
    let mut n = 0;
    let mut regions = vec![body.entry()];
    while let Some(r) = regions.pop() {
        for op in body.ops(r) {
            n += 1;
            regions.extend(body.regions(op));
        }
    }
    n
}

/// Large inputs, timed pass by pass: `cargo test --release --test opt -- --ignored --nocapture`.
///
/// * `slots`: frontend-style code where four stack slots take every access, so each slot
///   pointer has hundreds of thousands of uses: a store and the load after it (forwarding), a
///   copy (copy propagation), a store overwritten at once (dead stores), and dead arithmetic
///   (dead code), with a call every 64 statements and a `cf.if` every 256.
/// * `fanout`: one copy read a million times, half of them after a call (a partial run).
/// * `chain`: a chain of copies, each read by the next op.
#[test]
#[ignore]
fn large_inputs() {
    use std::fmt::Write;
    use std::time::Instant;
    let n = env_u64("FIR_OPT_SIZE", 200_000);
    let mut slots = String::from(
        "func @g(%x: i32) -> i32 {\n  func.ret %x\n}\n\nfunc @f(%x: i32, %c: i1) -> i32 {\n  %one: i32 = int.const 1\n",
    );
    for s in 0..4 {
        writeln!(slots, "  %s{s}: ptr = mem.stack 4, align 4").unwrap();
        writeln!(slots, "  mem.store i32 %x, %s{s}, align 4").unwrap();
    }
    let mut last = "%x".to_owned();
    for i in 0..n {
        let (a, b) = (i % 4, (i + 1) % 4);
        writeln!(
            slots,
            "  mem.store i32 {last}, %s{a}, align 4
  %l{i}: i32 = mem.load %s{a}, align 4
  %c{i}: i32 = copy %l{i}
  %a{i}: i32 = int.add.wrap %c{i}, %one
  mem.store i32 %a{i}, %s{b}, align 4
  mem.store i32 %a{i}, %s{b}, align 4
  %d{i}: i32 = int.mul.wrap %a{i}, %c{i}"
        )
        .unwrap();
        last = format!("%a{i}");
        if i % 64 == 63 {
            writeln!(slots, "  %k{i}: i32 = func.call @g({last})").unwrap();
            last = format!("%k{i}");
        }
        if i % 256 == 255 {
            writeln!(
                slots,
                "  cf.if %c {{\n    mem.store i32 {last}, %s0, align 4\n    %m{i}: i32 = mem.load %s0, align 4\n    mem.store i32 %m{i}, %s1, align 4\n  }}"
            )
            .unwrap();
        }
    }
    writeln!(slots, "  func.ret {last}\n}}").unwrap();

    let mut fanout = String::from(
        "func @g(%x: i32) -> i32 {\n  func.ret %x\n}\n\nfunc @f(%x: i32) -> i32 {\n  %y: i32 = copy %x\n",
    );
    let mut last = "%x".to_owned();
    for i in 0..n * 2 {
        if i == n {
            writeln!(fanout, "  %k: i32 = func.call @g(%y)").unwrap();
        }
        writeln!(fanout, "  %u{i}: i32 = int.add.wrap {last}, %y").unwrap();
        last = format!("%u{i}");
    }
    writeln!(fanout, "  func.ret {last}\n}}").unwrap();

    let mut chain = String::from("func @f(%x: i32) -> i32 {\n  %c0: i32 = copy %x\n");
    for i in 1..n * 2 {
        writeln!(
            chain,
            "  %c{i}: i32 = copy %c{}\n  %u{i}: i32 = int.add.wrap %c{i}, %c{i}",
            i - 1
        )
        .unwrap();
    }
    writeln!(chain, "  func.ret %c{}\n}}", n * 2 - 1).unwrap();

    for (name, text) in [("slots", slots), ("fanout", fanout), ("chain", chain)] {
        let t = Instant::now();
        let m = fir::parse_module(&text).unwrap();
        let parse = t.elapsed();
        let t = Instant::now();
        fir::verify_module(&m).unwrap();
        let verify = t.elapsed();
        let ops: usize = m.funcs.iter().map(|f| f.body.num_ops()).sum();
        eprintln!(
            "{name}: {ops} ops, {} bytes; parse {:.1} ms, verify {:.1} ms",
            text.len(),
            parse.as_secs_f64() * 1e3,
            verify.as_secs_f64() * 1e3
        );
        for p in PASSES {
            let mut m = m.clone();
            let mut r = Remarks::new(false);
            let t = Instant::now();
            let changes =
                fir::passes::run_pass(p, &mut m, &mut r, fir::contract::Policy::VerifiedOnly)
                    .unwrap();
            let dt = t.elapsed();
            eprintln!(
                "  {:>9} alone: {changes:8} changes, {:7.1} ms, {:5.1} ns/op",
                p.name,
                dt.as_secs_f64() * 1e3,
                dt.as_secs_f64() * 1e9 / ops as f64
            );
        }
        let mut opt = m.clone();
        let mut p = Pipeline::default_opt();
        p.verify_each = false;
        let t = Instant::now();
        let report = p.run(&mut opt, &mut Remarks::new(false)).unwrap();
        let dt = t.elapsed();
        fir::verify_module(&opt).unwrap();
        let left: usize = opt.funcs.iter().map(|f| linked_ops(&f.body)).sum();
        eprintln!(
            "  -O: {} rounds, {} changes, {:.1} ms ({:.1} ns/op), {left} ops left",
            report.rounds,
            report.changes(),
            dt.as_secs_f64() * 1e3,
            dt.as_secs_f64() * 1e9 / ops as f64
        );
        let mut r = Remarks::new(true);
        let mut p = Pipeline::default_opt();
        p.verify_each = false;
        let t = Instant::now();
        p.run(&mut m.clone(), &mut r).unwrap();
        eprintln!(
            "  -O with remarks: {:.1} ms, {} remarks",
            t.elapsed().as_secs_f64() * 1e3,
            r.list().len()
        );
    }
}
