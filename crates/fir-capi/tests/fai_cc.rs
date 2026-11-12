//! `fai-cc`, the C frontend in `frontends/c/`, against a reference C compiler.
//!
//! Builds `fai-cc` with CMake against this crate's static library, then compiles every program
//! of the corpus (`frontends/c/tests/*.c`) three ways: by the reference compiler (the AArch64 C
//! compiler: `$FIR_CC`, `cc` on AArch64, else `aarch64-unknown-linux-gnu-cc`, at `-O1`, with
//! `-ffp-contract=off`: `fai-cc` never fuses `a * b + c` into an `fma`), by `fai-cc`, and by
//! `fai-cc -O`. Each binary is linked with the output helpers of
//! `frontends/c/tests/runtime/fai_runtime.c` and libm, and with `frontends/c/tests/extern/NAME.c`
//! compiled by the reference compiler if the program has one (C functions it calls, and that
//! call it, compiled separately), and run (under `qemu-aarch64` off AArch64), and the three must
//! print the same and exit with the same code. Each program's HFIR
//! (`fai-cc --emit hfir`) also runs in the interpreter, under Arm's NaN choice (the NaNs the
//! hardware gives, as the backend's harness does), whose calls of the output helpers (events)
//! must spell the same text and whose result the same exit code; a program that calls other
//! external functions (libm's, or libc's `printf`) isn't comparable there, since the
//! interpreter's world answers them with zeros: it is listed with the first such function.
//!
//! The programs under `frontends/c/tests/errors/` use what `fai-cc` doesn't support yet: each
//! says where and what in `// expect: LINE:COL: TEXT` lines, and `fai-cc` must report exactly
//! those diagnostics (`FILE:LINE:COL: error: …TEXT…`) and exit with 1, not crash.
//!
//! The test needs the dev shell's CMake, Ninja, Clang libraries, AArch64 C compiler, and (off
//! AArch64) `qemu-aarch64`, and fails with a message naming what's missing. It runs by default
//! on Linux; elsewhere (macOS, whose binaries aren't Linux ones) only with `FAI_CC_TESTS=1`, and
//! `FAI_CC_TESTS=0` turns it off. `FAI_CC_ONLY=name` runs only the programs whose names contain
//! `name`; `--nocapture` shows the summary.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

fn enabled() -> bool {
    match std::env::var("FAI_CC_TESTS").as_deref() {
        Ok("0") => {
            eprintln!("fai-cc: FAI_CC_TESTS=0, so the corpus doesn't run");
            false
        }
        Ok(_) => true,
        Err(_) if cfg!(target_os = "linux") => true,
        Err(_) => {
            eprintln!(
                "fai-cc: the corpus runs Linux binaries; on this host it runs only with FAI_CC_TESTS=1"
            );
            false
        }
    }
}

fn check(cmd: &mut Command, what: &str) -> Output {
    let out = cmd
        .output()
        .unwrap_or_else(|e| panic!("running {what}: {e}"));
    assert!(
        out.status.success(),
        "{what} failed:\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

/// `libfir_capi.a` from the current sources, in a target directory of its own (as `tests/c.rs`
/// builds it).
fn static_lib() -> PathBuf {
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("capi-target");
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    check(
        Command::new(cargo)
            .current_dir(repo())
            .args([
                "build",
                "--quiet",
                "--release",
                "-p",
                "fir-capi",
                "--target-dir",
            ])
            .arg(&target),
        "cargo build -p fir-capi",
    );
    target.join("release/libfir_capi.a")
}

/// `fai-cc`, built once for the tests here.
fn fai_cc() -> &'static Path {
    static FAI: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    FAI.get_or_init(build_fai_cc)
}

/// Configure and build `fai-cc`; its path.
fn build_fai_cc() -> PathBuf {
    for tool in ["cmake", "ninja"] {
        assert!(
            on_path(tool),
            "fai-cc: {tool} is missing: run the tests in the dev shell (`nix develop`), or set \
             FAI_CC_TESTS=0 to skip the C frontend's corpus"
        );
    }
    let lib = static_lib();
    let build = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fai-cc-build");
    let configured = Command::new("cmake")
        .arg("-S")
        .arg(repo().join("frontends/c"))
        .arg("-B")
        .arg(&build)
        .args(["-G", "Ninja", "-DFAI_CC_BUILD_CAPI=OFF"])
        .arg(format!("-DFIR_CAPI_LIB={}", lib.display()))
        .output()
        .expect("running cmake");
    assert!(
        configured.status.success(),
        "configuring fai-cc failed (are Clang's libraries on CMAKE_PREFIX_PATH, as in the dev \
         shell?):\n{}",
        String::from_utf8_lossy(&configured.stderr)
    );
    check(
        Command::new("cmake").arg("--build").arg(&build),
        "building fai-cc",
    );
    build.join("fai-cc")
}

struct Toolchain {
    cc: String,
    runner: Option<String>,
}

fn toolchain() -> Toolchain {
    let native = cfg!(target_arch = "aarch64");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) => "aarch64-unknown-linux-gnu-cc".to_owned(),
    };
    assert!(
        on_path(&cc) || Path::new(&cc).is_file(),
        "fai-cc: no AArch64 C compiler ('{cc}'): use the dev shell, or set FIR_CC"
    );
    let runner = if native {
        None
    } else {
        assert!(
            on_path("qemu-aarch64"),
            "fai-cc: qemu-aarch64 is missing: use the dev shell"
        );
        Some("qemu-aarch64".to_owned())
    };
    Toolchain { cc, runner }
}

/// Run a command with a time limit; its output, or why it didn't finish.
fn run_limited(cmd: &mut Command, limit: Duration) -> Result<Output, String> {
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    let start = Instant::now();
    loop {
        if child.try_wait().map_err(|e| e.to_string())?.is_some() {
            return child.wait_with_output().map_err(|e| e.to_string());
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("timed out after {limit:?}"));
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// What a run printed and its exit code.
#[derive(PartialEq, Eq, Debug)]
struct Behavior {
    stdout: String,
    code: i32,
}

fn run_native(tc: &Toolchain, exe: &Path) -> Result<Behavior, String> {
    let mut cmd = match &tc.runner {
        Some(r) => {
            let mut c = Command::new(r);
            c.arg(exe);
            c
        }
        None => Command::new(exe),
    };
    // In the binary's directory, where a crash's core file (qemu writes one) belongs.
    cmd.current_dir(exe.parent().unwrap());
    let out = run_limited(&mut cmd, Duration::from_secs(60))?;
    match out.status.code() {
        Some(code) => Ok(Behavior {
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            code,
        }),
        None => Err(format!(
            "killed by a signal; stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        )),
    }
}

/// What the interpreter's run of `main` gives.
enum FirRun {
    /// The output helpers' events spelled out, and the returned value as an exit code.
    Ran(Behavior),
    /// The program calls this other external function, so its run can't be compared.
    Calls(String),
}

/// The interpreter's run of `main`, as a native run's behavior.
fn run_fir(hfir: &str) -> Result<FirRun, String> {
    let m = fir::parse_module(hfir).map_err(|e| format!("the HFIR doesn't parse: {e}"))?;
    fir::verify_module(&m).map_err(|e| format!("the HFIR doesn't verify: {e}"))?;
    let r = fir::interp::run_detail_with(
        &m,
        "main",
        &[],
        2_000_000_000,
        false,
        fir::interp::NanRule::Arm,
    )?;
    if r.out_of_fuel {
        return Err("fir run ran out of fuel".to_owned());
    }
    let mut stdout = String::new();
    for ev in r.events.split("; ").filter(|e| !e.is_empty()) {
        let (call, _) = ev.split_once(" -> ").ok_or(format!("event '{ev}'"))?;
        let arg = |prefix: &str| {
            call.strip_prefix(prefix)
                .and_then(|s| s.strip_suffix(')'))
                .and_then(|s| s.parse::<i64>().ok())
        };
        if let Some(v) = arg("@fai_put_long(i64 ") {
            stdout += &v.to_string();
        } else if let Some(c) = arg("@fai_put_char(i32 ") {
            stdout.push(char::from(c as u8));
        } else {
            let callee = call.split_once('(').map_or(call, |c| c.0);
            return Ok(FirRun::Calls(callee.trim_start_matches('@').to_owned()));
        }
    }
    let outcome = r.line[r.events.len()..]
        .split("; ")
        .next()
        .unwrap_or_default();
    let code = match outcome.strip_prefix("returned i32 ") {
        Some(v) => v.parse::<i64>().map_err(|e| format!("'{outcome}': {e}"))? & 0xff,
        None => return Err(format!("fir run: {outcome}")),
    };
    Ok(FirRun::Ran(Behavior {
        stdout,
        code: code as i32,
    }))
}

fn corpus(dir: &Path) -> Vec<PathBuf> {
    let only = std::env::var("FAI_CC_ONLY").unwrap_or_default();
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "c"))
        .filter(|p| p.file_stem().unwrap().to_string_lossy().contains(&only))
        .collect();
    files.sort();
    files
}

#[derive(Default)]
struct Tally {
    programs: usize,
    native: usize,
    native_opt: usize,
    fir_match: usize,
    fir_other_externs: Vec<String>,
    failures: Vec<String>,
}

/// One corpus program: build it three ways, run, and compare.
fn one(file: &Path, fai: &Path, tc: &Toolchain, rt: &Path, out: &Path, tally: &Mutex<Tally>) {
    let name = file.file_stem().unwrap().to_string_lossy().into_owned();
    let inc = repo().join("frontends/c/tests/runtime");
    let fail = |msg: String| {
        tally
            .lock()
            .unwrap()
            .failures
            .push(format!("{name}: {msg}"))
    };
    // The program's separately compiled C functions, if it has any.
    let helper = file
        .parent()
        .unwrap()
        .join("extern")
        .join(format!("{name}.c"));
    let mut objs = vec![rt.to_path_buf()];
    if helper.is_file() {
        let obj = out.join(format!("{name}.extern.o"));
        let built = Command::new(&tc.cc)
            .args(["-O1", "-w", "-std=gnu17", "-ffp-contract=off", "-c", "-I"])
            .arg(&inc)
            .arg(&helper)
            .arg("-o")
            .arg(&obj)
            .output()
            .unwrap();
        if !built.status.success() {
            return fail(format!(
                "the reference compiler failed on {}:\n{}",
                helper.display(),
                String::from_utf8_lossy(&built.stderr)
            ));
        }
        objs.push(obj);
    }
    let reference = out.join(format!("{name}.ref"));
    let built = Command::new(&tc.cc)
        .args(["-O1", "-w", "-std=gnu17", "-ffp-contract=off", "-I"])
        .arg(&inc)
        .arg(file)
        .args(&objs)
        .arg("-lm")
        .arg("-o")
        .arg(&reference)
        .output()
        .unwrap();
    if !built.status.success() {
        return fail(format!(
            "the reference compiler failed:\n{}",
            String::from_utf8_lossy(&built.stderr)
        ));
    }
    let want = match run_native(tc, &reference) {
        Ok(b) => b,
        Err(e) => return fail(format!("the reference binary: {e}")),
    };
    let mut ok = [false; 2];
    for (i, opt) in [false, true].into_iter().enumerate() {
        let exe = out.join(format!("{name}{}", if opt { ".O" } else { "" }));
        let mut cmd = Command::new(fai);
        cmd.arg(file)
            .arg("-I")
            .arg(&inc)
            .args(&objs)
            .arg("-lm")
            .arg("-o")
            .arg(&exe);
        if opt {
            cmd.arg("-O");
        }
        let built = run_limited(&mut cmd, Duration::from_secs(120));
        match built {
            Ok(o) if o.status.success() => {}
            Ok(o) => {
                fail(format!(
                    "fai-cc{} failed:\n{}",
                    if opt { " -O" } else { "" },
                    String::from_utf8_lossy(&o.stderr)
                ));
                continue;
            }
            Err(e) => {
                fail(format!("fai-cc: {e}"));
                continue;
            }
        }
        match run_native(tc, &exe) {
            Ok(got) if got == want => ok[i] = true,
            Ok(got) => fail(format!(
                "fai-cc{} gives {got:?}, the reference {want:?}",
                if opt { " -O" } else { "" }
            )),
            Err(e) => fail(format!("fai-cc{}: {e}", if opt { " -O" } else { "" })),
        }
    }
    let hfir = Command::new(fai)
        .arg(file)
        .arg("-I")
        .arg(&inc)
        .args(["--emit", "hfir"])
        .output()
        .unwrap();
    let fir_ok = if !hfir.status.success() {
        fail(format!(
            "fai-cc --emit hfir failed:\n{}",
            String::from_utf8_lossy(&hfir.stderr)
        ));
        false
    } else {
        match run_fir(&String::from_utf8_lossy(&hfir.stdout)) {
            Ok(FirRun::Ran(got)) if got == want => true,
            Ok(FirRun::Ran(got)) => {
                fail(format!("fir run gives {got:?}, the reference {want:?}"));
                false
            }
            Ok(FirRun::Calls(callee)) => {
                tally
                    .lock()
                    .unwrap()
                    .fir_other_externs
                    .push(format!("{name} ({callee})"));
                false
            }
            Err(e) => {
                fail(e);
                false
            }
        }
    };
    let mut t = tally.lock().unwrap();
    t.programs += 1;
    t.native += usize::from(ok[0]);
    t.native_opt += usize::from(ok[1]);
    t.fir_match += usize::from(fir_ok);
}

/// The `// expect: LINE:COL: TEXT` lines of an error test.
fn expectations(src: &str) -> Vec<(String, String)> {
    src.lines()
        .filter_map(|l| l.trim().strip_prefix("// expect: "))
        .map(|e| {
            let mut parts = e.splitn(3, ':');
            let (line, col) = (parts.next().unwrap(), parts.next().unwrap());
            (
                format!("{}:{}", line.trim(), col.trim()),
                parts.next().unwrap().trim().to_owned(),
            )
        })
        .collect()
}

fn error_test(file: &Path, fai: &Path) -> Result<(), String> {
    let src = std::fs::read_to_string(file).unwrap();
    let want = expectations(&src);
    if want.is_empty() {
        return Err("no `// expect:` lines".to_owned());
    }
    let out = run_limited(
        Command::new(fai)
            .arg(file)
            .arg("-I")
            .arg(repo().join("frontends/c/tests/runtime"))
            .args(["--emit", "hfir"]),
        Duration::from_secs(60),
    )?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    if out.status.code() != Some(1) {
        return Err(format!("exit status {:?}, want 1:\n{stderr}", out.status));
    }
    let errors: Vec<&str> = stderr.lines().filter(|l| l.contains(": error: ")).collect();
    for (loc, text) in &want {
        let tag = format!(".c:{loc}: error: ");
        if !errors
            .iter()
            .any(|e| e.contains(&tag) && e.contains(text.as_str()))
        {
            return Err(format!("no error '{text}' at {loc}:\n{stderr}"));
        }
    }
    if errors.len() != want.len() {
        return Err(format!(
            "{} errors, want {}:\n{stderr}",
            errors.len(),
            want.len()
        ));
    }
    Ok(())
}

#[test]
fn fai_cc_corpus() {
    if !enabled() {
        return;
    }
    let tc = toolchain();
    let fai = fai_cc();
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fai-cc-corpus");
    std::fs::create_dir_all(&out).unwrap();
    let rt = out.join("fai_runtime.o");
    check(
        Command::new(&tc.cc)
            .arg("-c")
            .arg(repo().join("frontends/c/tests/runtime/fai_runtime.c"))
            .arg("-o")
            .arg(&rt),
        "compiling fai_runtime.c",
    );

    let tests = repo().join("frontends/c/tests");
    let files = corpus(&tests);
    let tally = Mutex::new(Tally::default());
    let next = Mutex::new(files.iter());
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let Some(file) = next.lock().unwrap().next() else {
                        break;
                    };
                    one(file, fai, &tc, &rt, &out, &tally);
                }
            });
        }
    });

    let mut errors = 0;
    let mut t = tally.into_inner().unwrap();
    for file in corpus(&tests.join("errors")) {
        errors += 1;
        if let Err(e) = error_test(&file, fai) {
            t.failures.push(format!("{}: {e}", file.display()));
        }
    }

    t.fir_other_externs.sort();
    eprintln!(
        "fai-cc corpus: {} programs; native runs matching the reference: {} without -O, {} with \
         -O; fir run matching: {}, not comparable: {} (calling other external functions: {}); \
         error tests: {}",
        t.programs,
        t.native,
        t.native_opt,
        t.fir_match,
        t.fir_other_externs.len(),
        t.fir_other_externs.join(", "),
        errors
    );
    assert!(
        t.failures.is_empty(),
        "{} failures:\n{}",
        t.failures.len(),
        t.failures.join("\n")
    );
    assert!(!files.is_empty(), "no programs in {}", tests.display());
}

// Interop torture: random signatures of structs and unions (every AAPCS64 class, bitfields,
// unions, 16-byte aligned members, `aligned` attributes, nesting, arrays, pointers), written in
// C, with the callers in one file and the callees in another. Each file is compiled by `fai-cc`
// (with and without `-O`) or by the reference compiler, and every pairing must agree: the
// callees check every member of every argument they receive (directly, through a function
// pointer, and through `...` read by `va_arg`) and the callers every member of every result.
// `FAI_CC_ABI=N` sets the number of signatures (default 240), `FAI_CC_ABI_SEED` the seed.

/// A deterministic random source (xorshift64*), as `crates/fir/tests/abi.rs`'s.
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

    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Sc {
    Bool,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F32,
    F64,
    Ptr,
}

impl Sc {
    fn c(self) -> &'static str {
        match self {
            Sc::Bool => "_Bool",
            Sc::I8 => "signed char",
            Sc::U8 => "unsigned char",
            Sc::I16 => "short",
            Sc::U16 => "unsigned short",
            Sc::I32 => "int",
            Sc::U32 => "unsigned",
            Sc::I64 => "long",
            Sc::U64 => "unsigned long",
            Sc::F32 => "float",
            Sc::F64 => "double",
            Sc::Ptr => "char *",
        }
    }

    fn bits(self) -> u32 {
        match self {
            Sc::Bool | Sc::I8 | Sc::U8 => 8,
            Sc::I16 | Sc::U16 => 16,
            Sc::I32 | Sc::U32 | Sc::F32 => 32,
            _ => 64,
        }
    }

    fn signed(self) -> bool {
        matches!(self, Sc::I8 | Sc::I16 | Sc::I32 | Sc::I64)
    }

    /// The type `va_arg` reads it as after C's default argument promotions.
    fn promoted(self) -> &'static str {
        match self {
            Sc::Bool | Sc::I8 | Sc::U8 | Sc::I16 | Sc::U16 => "int",
            Sc::F32 => "double",
            s => s.c(),
        }
    }

    /// A random value as a C expression.
    fn value(self, rng: &mut Rng) -> String {
        match self {
            Sc::Bool => rng.below(2).to_string(),
            Sc::F32 => format!("{:.3}f", (rng.below(8001) as f64 - 4000.0) / 8.0),
            Sc::F64 => format!("{:.6}", (rng.below(2_000_001) as f64 - 1_000_000.0) / 64.0),
            Sc::Ptr if rng.chance(10) => "(char *)0".to_owned(),
            Sc::Ptr => format!("bufp() + {}", rng.below(64)),
            Sc::U64 => format!("{:#x}UL", rng.next()),
            Sc::U32 => format!("{}u", rng.next() as u32),
            s => bits_value(rng, s.bits().min(63), s.signed()),
        }
    }
}

/// A random integer of `width` bits as a C literal.
fn bits_value(rng: &mut Rng, width: u32, signed: bool) -> String {
    let x = rng.next() & ((1u64 << width) - 1);
    if signed {
        let v = ((x << (64 - width)) as i64) >> (64 - width);
        format!("{v}L")
    } else {
        format!("{x}UL")
    }
}

#[derive(Clone)]
enum Ty {
    S(Sc),
    Arr(u32, Box<Ty>),
    Rec(usize),
}

enum Member {
    Plain {
        ty: Ty,
        align16: bool,
    },
    /// A bitfield; width 0 is an unnamed zero-width one.
    Bits {
        sc: Sc,
        width: u32,
    },
}

struct Rec {
    union: bool,
    members: Vec<Member>,
    /// An `aligned` attribute on the type (0 for none).
    attr: u32,
}

#[derive(Default)]
struct Torture {
    recs: Vec<Rec>,
    hfa_like: usize,
    unions: usize,
    bitfields: usize,
    aligned: usize,
    empty: usize,
}

impl Torture {
    fn scalar(rng: &mut Rng) -> Sc {
        use Sc::*;
        rng.pick(&[
            Bool, I8, U8, I16, U16, I32, U32, I64, U64, F32, F64, Ptr, I32, I64, F64,
        ])
    }

    /// A record whose members are all floats of one format, through arrays, nested structs, and
    /// unions: an HFA for GCC when it has 1 to 4 floats and no padding.
    fn hfa(&mut self, rng: &mut Rng, f: Sc, depth: u32) -> usize {
        let union = depth < 2 && rng.chance(20);
        let mut members = Vec::new();
        let most = if union { 3 } else { 4 };
        for _ in 0..1 + rng.below(most) {
            let ty = match rng.below(6) {
                0 => Ty::Arr(1 + rng.below(3) as u32, Box::new(Ty::S(f))),
                1 if depth < 2 => Ty::Rec(self.hfa(rng, f, depth + 1)),
                _ => Ty::S(f),
            };
            members.push(Member::Plain { ty, align16: false });
        }
        if !union && rng.chance(10) {
            let at = rng.below(members.len() as u64 + 1) as usize;
            members.insert(
                at,
                Member::Bits {
                    sc: Sc::I32,
                    width: 0,
                },
            );
        }
        // An empty struct takes no bytes: still an HFA.
        if rng.chance(6) {
            let at = rng.below(members.len() as u64 + 1) as usize;
            let ty = Ty::Rec(self.empty());
            members.insert(at, Member::Plain { ty, align16: false });
        }
        let attr = if rng.chance(10) { 8 } else { 0 };
        self.hfa_like += 1;
        self.unions += usize::from(union);
        self.push(Rec {
            union,
            members,
            attr,
        })
    }

    fn general(&mut self, rng: &mut Rng, depth: u32) -> usize {
        let union = rng.chance(18);
        let mut members = Vec::new();
        let most = if union { 3 } else { 5 };
        let mut bits = false;
        for _ in 0..1 + rng.below(most) {
            match rng.below(20) {
                0..=2 if depth < 2 => {
                    let r = if rng.chance(30) {
                        let f = rng.pick(&[Sc::F32, Sc::F64]);
                        self.hfa(rng, f, depth + 1)
                    } else {
                        self.general(rng, depth + 1)
                    };
                    let ty = if rng.chance(25) {
                        Ty::Arr(1 + rng.below(2) as u32, Box::new(Ty::Rec(r)))
                    } else {
                        Ty::Rec(r)
                    };
                    members.push(Member::Plain { ty, align16: false });
                }
                3 if rng.chance(25) => members.push(Member::Plain {
                    ty: Ty::Rec(self.empty()),
                    align16: false,
                }),
                3..=5 => members.push(Member::Plain {
                    ty: Ty::Arr(1 + rng.below(4) as u32, Box::new(Ty::S(Self::scalar(rng)))),
                    align16: false,
                }),
                6..=8 if !union => {
                    bits = true;
                    let nbits = 1 + rng.below(3);
                    for _ in 0..nbits {
                        use Sc::*;
                        let sc = rng.pick(&[I8, U8, I16, U16, I32, U32, I64, U64]);
                        let width = 1 + rng.below(u64::from(sc.bits().min(24))) as u32;
                        members.push(Member::Bits { sc, width });
                        if rng.chance(10) {
                            members.push(Member::Bits { sc: I32, width: 0 });
                        }
                    }
                }
                _ => {
                    let sc = Self::scalar(rng);
                    let align16 = !matches!(sc, Sc::F32 | Sc::F64) && rng.chance(7);
                    members.push(Member::Plain {
                        ty: Ty::S(sc),
                        align16,
                    });
                }
            }
        }
        // `aligned(16)` only beside an integer, pointer, or bitfield, so that neither this
        // record nor one holding it is an HFA: GCC aligns a 16-byte aligned HFA on the stack,
        // which FIR can't, and `fai-cc` rejects it (`tests/errors/struct_by_value.c`).
        let not_hfa = members.iter().any(|m| match m {
            Member::Plain { ty: Ty::S(s), .. } => !matches!(s, Sc::F32 | Sc::F64),
            Member::Plain {
                ty: Ty::Arr(_, e), ..
            } => {
                matches!(**e, Ty::S(s) if !matches!(s, Sc::F32 | Sc::F64))
            }
            Member::Plain { .. } => false,
            Member::Bits { .. } => true,
        });
        let attr = match rng.below(14) {
            0 if not_hfa => 16,
            0 | 1 => 8,
            _ => 0,
        };
        self.unions += usize::from(union);
        self.bitfields += usize::from(bits);
        self.aligned += usize::from(attr != 0 || self.align16_fields(&members));
        self.push(Rec {
            union,
            members,
            attr,
        })
    }

    /// An empty struct (a GNU extension): no bytes, and passed as nothing.
    fn empty(&mut self) -> usize {
        self.empty += 1;
        self.push(Rec {
            union: false,
            members: Vec::new(),
            attr: 0,
        })
    }

    fn push(&mut self, r: Rec) -> usize {
        self.recs.push(r);
        self.recs.len() - 1
    }

    fn align16_fields(&self, ms: &[Member]) -> bool {
        ms.iter().any(|m| match m {
            Member::Plain { ty, align16 } => *align16 || self.mem_align16(ty),
            Member::Bits { .. } => false,
        })
    }

    /// Whether a type's memory alignment is 16.
    fn mem_align16(&self, t: &Ty) -> bool {
        match t {
            Ty::S(_) => false,
            Ty::Arr(_, e) => self.mem_align16(e),
            Ty::Rec(r) => self.recs[*r].attr == 16 || self.align16_fields(&self.recs[*r].members),
        }
    }

    /// Whether GCC aligns an argument of this type to 16 (its fields' alignment, not an
    /// attribute on the type itself): `fai-cc` doesn't pass those through `...`.
    fn arg_align16(&self, t: &Ty) -> bool {
        match t {
            Ty::Rec(r) => self.align16_fields(&self.recs[*r].members),
            _ => false,
        }
    }

    fn c_ty(&self, t: &Ty) -> String {
        match t {
            Ty::S(s) => s.c().to_owned(),
            Ty::Rec(r) => format!(
                "{} r{r}",
                if self.recs[*r].union {
                    "union"
                } else {
                    "struct"
                }
            ),
            Ty::Arr(..) => unreachable!("arrays are only members"),
        }
    }

    fn decls(&self) -> String {
        let mut out = String::new();
        for (i, r) in self.recs.iter().enumerate() {
            let _ = write!(out, "{} r{i} {{", if r.union { "union" } else { "struct" });
            for (k, m) in r.members.iter().enumerate() {
                match m {
                    Member::Plain { ty, align16 } => {
                        let al = if *align16 { "_Alignas(16) " } else { "" };
                        match ty {
                            Ty::Arr(n, e) => {
                                let _ = write!(out, " {al}{} m{k}[{n}];", self.c_ty(e));
                            }
                            t => {
                                let _ = write!(out, " {al}{} m{k};", self.c_ty(t));
                            }
                        }
                    }
                    Member::Bits { sc, width: 0 } => {
                        let _ = write!(out, " {} : 0;", sc.c());
                    }
                    Member::Bits { sc, width } => {
                        let _ = write!(out, " {} m{k} : {width};", sc.c());
                    }
                }
            }
            out.push_str(" }");
            if r.attr != 0 {
                let _ = write!(out, " __attribute__((aligned({})))", r.attr);
            }
            out.push_str(";\n");
        }
        out
    }

    /// The members a value of type `t` at `path` sets and checks, with their values: a union's
    /// first member only.
    fn leaves(&self, t: &Ty, path: &str, rng: &mut Rng, out: &mut Vec<(String, String)>) {
        match t {
            Ty::S(s) => out.push((path.to_owned(), s.value(rng))),
            Ty::Arr(n, e) => {
                for j in 0..*n {
                    self.leaves(e, &format!("{path}[{j}]"), rng, out);
                }
            }
            Ty::Rec(r) => {
                let rec = &self.recs[*r];
                for (k, m) in rec.members.iter().enumerate() {
                    let p = format!("{path}.m{k}");
                    match m {
                        Member::Plain { ty, .. } => self.leaves(ty, &p, rng, out),
                        Member::Bits { width: 0, .. } => {}
                        Member::Bits { sc, width } => {
                            out.push((p, bits_value(rng, *width, sc.signed())))
                        }
                    }
                    if rec.union {
                        break;
                    }
                }
            }
        }
    }
}

/// One signature: its parameters and result (`None`: void), with each value's members.
struct TSig {
    params: Vec<(Ty, Vec<(String, String)>)>,
    ret: Option<(Ty, Vec<(String, String)>)>,
}

/// What one batch's files check.
#[derive(Default)]
struct TCounts {
    sigs: usize,
    params: usize,
    va_params: usize,
    checks: usize,
}

/// A batch of signatures as two C files: the callers (with `main`) and the callees.
fn torture_batch(seed: u64, n: usize) -> (String, String, TCounts, Torture) {
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let mut g = Torture::default();
    let mut sigs = Vec::new();
    let pick_ty = |g: &mut Torture, rng: &mut Rng| -> Ty {
        match rng.below(10) {
            0 if rng.chance(10) => Ty::Rec(g.empty()),
            0..=2 => Ty::S(Torture::scalar(rng)),
            3..=5 => {
                let f = rng.pick(&[Sc::F32, Sc::F64]);
                Ty::Rec(g.hfa(rng, f, 0))
            }
            _ => Ty::Rec(g.general(rng, 0)),
        }
    };
    for _ in 0..n {
        let most = if rng.chance(30) { 14 } else { 6 };
        let np = 1 + rng.below(most) as usize;
        let mut params = Vec::new();
        for k in 0..np {
            let t = pick_ty(&mut g, &mut rng);
            let mut ls = Vec::new();
            let path = format!("a{k}");
            g.leaves(&t, &path, &mut rng, &mut ls);
            params.push((t, ls));
        }
        let ret = if rng.chance(15) {
            None
        } else {
            let t = pick_ty(&mut g, &mut rng);
            let mut ls = Vec::new();
            g.leaves(&t, "r", &mut rng, &mut ls);
            Some((t, ls))
        };
        sigs.push(TSig { params, ret });
    }

    let mut counts = TCounts::default();
    let head = format!(
        "#include <stdarg.h>\n#include <stdio.h>\nchar *bufp(void);\nvoid bad(int id);\n{}",
        g.decls()
    );
    let mut callers = head.clone();
    callers.push_str(
        "static char buf[64];\nchar *bufp(void) { return buf; }\nstatic int nbad;\n\
         void bad(int id) { nbad++; printf(\"bad %d\\n\", id); }\n",
    );
    let mut callees = head;
    let mut main = String::from("int main(void) {\n");
    // Each check has a number of its own (string literals would be generated globals whose
    // names clash between two `fai-cc` objects: FIR has no linkage yet).
    let id = std::cell::Cell::new(0usize);
    let checks = |ls: &[(String, String)], out: &mut String| {
        for (p, v) in ls {
            id.set(id.get() + 1);
            let _ = writeln!(out, "  if ({p} != {v}) bad({});", id.get());
        }
    };
    let sets = |ls: &[(String, String)], out: &mut String| {
        for (p, v) in ls {
            let _ = writeln!(out, "  {p} = {v};");
        }
    };
    for (i, sig) in sigs.iter().enumerate() {
        counts.sigs += 1;
        counts.params += sig.params.len();
        let rty = sig
            .ret
            .as_ref()
            .map_or("void".to_owned(), |(t, _)| g.c_ty(t));
        let ptys: Vec<String> = sig.params.iter().map(|(t, _)| g.c_ty(t)).collect();
        let decl = |names: bool| -> String {
            ptys.iter()
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
        let va: Vec<usize> = (0..sig.params.len())
            .filter(|&k| !g.arg_align16(&sig.params[k].0))
            .collect();
        counts.va_params += va.len();

        // The callee, checking its arguments, and its variadic twin.
        let _ = writeln!(callees, "{rty} f{i}({}) {{", decl(true));
        for (_, ls) in &sig.params {
            checks(ls, &mut callees);
        }
        if let Some((t, ls)) = &sig.ret {
            let _ = writeln!(callees, "  {} r;", g.c_ty(t));
            if matches!(t, Ty::S(_)) {
                let _ = writeln!(callees, "  r = {};", ls[0].1);
            } else {
                sets(ls, &mut callees);
            }
            callees.push_str("  return r;\n");
        }
        callees.push_str("}\n");
        let _ = writeln!(
            callees,
            "void v{i}(int n, ...) {{\n  va_list ap;\n  va_start(ap, n);"
        );
        for &k in &va {
            let (t, ls) = &sig.params[k];
            let read = match t {
                Ty::S(s) => format!("({})va_arg(ap, {})", s.c(), s.promoted()),
                t => format!("va_arg(ap, {})", g.c_ty(t)),
            };
            let _ = writeln!(callees, "  {} a{k} = {read};", g.c_ty(t));
            checks(ls, &mut callees);
        }
        callees.push_str("  va_end(ap);\n}\n");

        // The caller: directly, through a pointer, and through `...`.
        let _ = writeln!(callers, "{rty} f{i}({});", decl(false));
        let _ = writeln!(callers, "void v{i}(int n, ...);");
        let _ = writeln!(callers, "{rty} (*p{i})({}) = f{i};", decl(false));
        let _ = writeln!(callers, "static void t{i}(void) {{");
        for (k, (t, ls)) in sig.params.iter().enumerate() {
            let _ = writeln!(callers, "  {} a{k};", g.c_ty(t));
            if matches!(t, Ty::S(_)) {
                let _ = writeln!(callers, "  a{k} = {};", ls[0].1);
            } else {
                sets(ls, &mut callers);
            }
        }
        let args: Vec<String> = (0..sig.params.len()).map(|k| format!("a{k}")).collect();
        for callee in [format!("f{i}"), format!("p{i}")] {
            match &sig.ret {
                Some((t, ls)) => {
                    let _ = writeln!(
                        callers,
                        "  {{\n  {} r = {callee}({});",
                        g.c_ty(t),
                        args.join(", ")
                    );
                    checks(ls, &mut callers);
                    callers.push_str("  }\n");
                    counts.checks += ls.len();
                }
                None => {
                    let _ = writeln!(callers, "  {callee}({});", args.join(", "));
                }
            }
        }
        let vargs: String = va.iter().map(|k| format!(", a{k}")).collect();
        let _ = writeln!(callers, "  v{i}(0{vargs});\n}}");
        let _ = writeln!(main, "  t{i}();");
        for (k, (_, ls)) in sig.params.iter().enumerate() {
            counts.checks += ls.len() * (2 + usize::from(va.contains(&k)));
        }
    }
    main.push_str("  printf(\"done %d\\n\", nbad);\n  return nbad != 0;\n}\n");
    callers.push_str(&main);
    (callers, callees, counts, g)
}

#[test]
fn fai_cc_abi_torture() {
    if !enabled() {
        return;
    }
    let tc = toolchain();
    let fai = fai_cc();
    let n: usize = std::env::var("FAI_CC_ABI")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(240);
    let seed: u64 = std::env::var("FAI_CC_ABI_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1);
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("fai-cc-abi-{seed}"));
    let _ = std::fs::remove_dir_all(&out);
    std::fs::create_dir_all(&out).unwrap();
    const BATCH: usize = 20;
    let batches = n.div_ceil(BATCH);
    // The pairings: (callers, callees), each `gcc`, `fai`, or `fai -O`.
    const PAIRS: &[(&str, &str)] = &[
        ("gcc", "gcc"),
        ("fai", "gcc"),
        ("faiO", "gcc"),
        ("gcc", "fai"),
        ("gcc", "faiO"),
        ("fai", "faiO"),
    ];
    // What ran, and the record types made: in all, HFA-like, unions, with bitfields, aligned,
    // empty.
    let totals = Mutex::new((TCounts::default(), [0usize; 6]));
    let failures = Mutex::new(Vec::<String>::new());
    let next = Mutex::new(0..batches);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let Some(b) = next.lock().unwrap().next() else {
                        break;
                    };
                    let count = BATCH.min(n - b * BATCH);
                    let (callers, callees, counts, g) =
                        torture_batch(seed * 1_000_003 + b as u64, count);
                    let dir = out.join(format!("b{b}"));
                    std::fs::create_dir_all(&dir).unwrap();
                    let fail = |m: String| failures.lock().unwrap().push(format!("batch {b}: {m}"));
                    let mut objs = std::collections::HashMap::new();
                    let mut ok = true;
                    for (side, src) in [("callers", &callers), ("callees", &callees)] {
                        let c = dir.join(format!("{side}.c"));
                        std::fs::write(&c, src).unwrap();
                        for how in ["gcc", "fai", "faiO"] {
                            let o = dir.join(format!("{side}.{how}.o"));
                            let mut cmd = if how == "gcc" {
                                let mut cmd = Command::new(&tc.cc);
                                cmd.args(["-O1", "-w", "-std=gnu17", "-c"]);
                                cmd
                            } else {
                                let mut cmd = Command::new(fai);
                                if how == "faiO" {
                                    cmd.arg("-O");
                                }
                                cmd
                            };
                            cmd.arg(&c).arg("-o").arg(&o);
                            match run_limited(&mut cmd, Duration::from_secs(300)) {
                                Ok(r) if r.status.success() => {
                                    objs.insert((side, how), o);
                                }
                                Ok(r) => {
                                    ok = false;
                                    fail(format!(
                                        "{how} on {}:\n{}",
                                        c.display(),
                                        String::from_utf8_lossy(&r.stderr)
                                    ));
                                }
                                Err(e) => {
                                    ok = false;
                                    fail(format!("{how} on {}: {e}", c.display()));
                                }
                            }
                        }
                    }
                    if !ok {
                        continue;
                    }
                    for &(a, c) in PAIRS {
                        let exe = dir.join(format!("t-{a}-{c}"));
                        let linked = Command::new(&tc.cc)
                            .arg(&objs[&("callers", a)])
                            .arg(&objs[&("callees", c)])
                            .arg("-o")
                            .arg(&exe)
                            .output()
                            .unwrap();
                        if !linked.status.success() {
                            fail(format!(
                                "linking {a} callers with {c} callees:\n{}",
                                String::from_utf8_lossy(&linked.stderr)
                            ));
                            continue;
                        }
                        match run_native(&tc, &exe) {
                            Ok(r) if r.stdout == "done 0\n" && r.code == 0 => {}
                            Ok(r) => fail(format!(
                                "{a} callers with {c} callees (in {}): {:?}",
                                dir.display(),
                                r
                            )),
                            Err(e) => fail(format!("{a} callers with {c} callees: {e}")),
                        }
                    }
                    let mut t = totals.lock().unwrap();
                    t.0.sigs += counts.sigs;
                    t.0.params += counts.params;
                    t.0.va_params += counts.va_params;
                    t.0.checks += counts.checks;
                    let kinds = [
                        g.recs.len(),
                        g.hfa_like,
                        g.unions,
                        g.bitfields,
                        g.aligned,
                        g.empty,
                    ];
                    for (t, k) in t.1.iter_mut().zip(kinds) {
                        *t += k;
                    }
                }
            });
        }
    });
    let (c, k) = totals.into_inner().unwrap();
    eprintln!(
        "fai-cc ABI torture (seed {seed}): {} signatures over {} record types ({} of floats only, \
         {} unions, {} with bitfields, {} aligned by an attribute or a 16-byte member, {} \
         empty); {} \
         parameters, {} of them also through `...`; {} members checked in each of {} pairings \
         (callers/callees: {})",
        c.sigs,
        k[0],
        k[1],
        k[2],
        k[3],
        k[4],
        k[5],
        c.params,
        c.va_params,
        c.checks,
        PAIRS.len(),
        PAIRS
            .iter()
            .map(|(a, b)| format!("{a}/{b}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let failures = failures.into_inner().unwrap();
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
