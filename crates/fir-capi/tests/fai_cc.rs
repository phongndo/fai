//! `fai-cc`, the C frontend in `frontends/c/`, against a reference C compiler.
//!
//! Builds `fai-cc` with CMake against this crate's static library, then compiles every program
//! of the corpus (`frontends/c/tests/*.c`) three ways: by the reference compiler (the AArch64 C
//! compiler: `$FIR_CC`, `cc` on AArch64, else `aarch64-unknown-linux-gnu-cc`, at `-O1`, with
//! `-ffp-contract=off`: `fai-cc` never fuses `a * b + c` into an `fma`), by `fai-cc`, and by
//! `fai-cc -O`. Each binary is linked with the output helpers of
//! `frontends/c/tests/runtime/fai_runtime.c` and libm, and run (under `qemu-aarch64` off
//! AArch64), and the three must print the same and exit with the same code. Each program's HFIR
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
    let reference = out.join(format!("{name}.ref"));
    let built = Command::new(&tc.cc)
        .args(["-O1", "-w", "-std=gnu17", "-ffp-contract=off", "-I"])
        .arg(&inc)
        .arg(file)
        .arg(rt)
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
            .arg(rt)
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
    let fai = build_fai_cc();
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
                    one(file, &fai, &tc, &rt, &out, &tally);
                }
            });
        }
    });

    let mut errors = 0;
    let mut t = tally.into_inner().unwrap();
    for file in corpus(&tests.join("errors")) {
        errors += 1;
        if let Err(e) = error_test(&file, &fai) {
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
