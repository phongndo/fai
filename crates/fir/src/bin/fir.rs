//! `fir`: the FIR command-line tool.
//!
//! ```text
//! fir run FILE [@FUNC] [ARG...] [--fuel N]   run a function (default @main)
//! fir check FILE                             verify; list holes
//! fir fmt FILE [--no-locs] [--unverified]     print canonical text (--unverified: parse only)
//! fir opt FILE [-O | --passes P,...] [--remarks] [--stats] [--verify-each] [--no-locs]
//!                                            optimize, print canonical text
//! fir compile FILE [-o OUT] [--emit asm|lfir|lfir-vregs] [--os linux|darwin]
//!                                            compile to AArch64 (see `compile`)
//! ```
//!
//! `check` prints what `fir-ref check` prints: `ok`, or one `hole ?NAME: TYPE @LOC` line per
//! hole; on failure, `FILE: MESSAGE` on stderr and exit code 1. `run` prints the one-line
//! outcome `fir-ref run` prints, for the same oracle (every choice answers `0`); arguments are
//! integers, `null`, or `poison`, parsed as Lean parses them.
//!
//! `opt` runs a pipeline of passes (`fir::passes`): the default `-O` one to a fixed point, or the
//! passes named by `--passes`, once each, in order. It prints the optimized module; `--remarks`
//! prints what each pass changed on stderr (`dse: deleted store @3:5 (overwritten by @4:5)`),
//! and `--stats` how often each pass fired and how long it took. Debug builds, or
//! `--verify-each`, verify after every pass and name the pass that broke the module; the output
//! is always verified.

use std::process::ExitCode;

fn read(file: &str) -> Result<String, ExitCode> {
    std::fs::read_to_string(file).map_err(|e| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    })
}

fn run(args: &[&str]) -> Result<(), ExitCode> {
    let fail = |file: &str, e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    match args {
        ["run", file, rest @ ..] => {
            let (fuel, rest) = match rest {
                [r @ .., "--fuel", n] => (
                    fir::interp::parse_nat(n).map_or(fir::interp::DEFAULT_FUEL, |n| {
                        u64::try_from(n).unwrap_or(u64::MAX)
                    }),
                    r,
                ),
                _ => (fir::interp::DEFAULT_FUEL, rest),
            };
            let (name, call_args) = match rest {
                [f, r @ ..] if f.starts_with('@') => (&f[1..], r),
                _ => ("main", rest),
            };
            let m = fir::parse_module(&read(file)?).map_err(|e| fail(file, e))?;
            fir::verify_module(&m).map_err(|e| fail(file, e))?;
            match fir::interp::run(&m, name, call_args, fuel) {
                Ok(s) => {
                    println!("{s}");
                    Ok(())
                }
                Err(e) => {
                    eprintln!("{e}");
                    Err(ExitCode::FAILURE)
                }
            }
        }
        ["check", file] => {
            let m = fir::parse_module(&read(file)?).map_err(|e| fail(file, e))?;
            let holes = fir::verify_module(&m).map_err(|e| fail(file, e))?;
            if holes.is_empty() {
                println!("ok");
            }
            for h in holes {
                println!("hole ?{}: {} {}", h.name, h.ty, fir::render_loc(h.loc));
            }
            Ok(())
        }
        ["fmt", file, opts @ ..] => {
            let m = fir::parse_module(&read(file)?).map_err(|e| fail(file, e))?;
            if !opts.contains(&"--unverified") {
                fir::verify_module(&m).map_err(|e| fail(file, e))?;
            }
            print!("{}", m.render(!opts.contains(&"--no-locs")));
            Ok(())
        }
        ["opt", file, opts @ ..] => opt(file, opts),
        ["compile", file, opts @ ..] => compile(file, opts),
        _ => {
            eprintln!(
                "usage:\n  fir run FILE [@FUNC] [ARG...] [--fuel N]\n  fir check FILE\n  fir fmt FILE [--no-locs] [--unverified]\n  fir opt FILE [-O | --passes P,...] [--remarks] [--stats] [--verify-each] [--no-locs]\n  fir compile FILE [-o OUT] [--emit asm|lfir|lfir-vregs] [--os linux|darwin]"
            );
            Err(ExitCode::from(2))
        }
    }
}

fn opt(file: &str, opts: &[&str]) -> Result<(), ExitCode> {
    use fir::passes::{Pipeline, Remarks};
    let fail = |e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    let mut pipeline = Pipeline::default_opt();
    let (mut remarks, mut stats, mut locs) = (false, false, true);
    let mut it = opts.iter();
    while let Some(&o) = it.next() {
        match o {
            "-O" => pipeline = Pipeline::default_opt(),
            "--passes" => {
                let spec = it
                    .next()
                    .ok_or_else(|| fail("--passes needs a list".into()))?;
                pipeline = Pipeline::parse(spec).map_err(fail)?;
            }
            "--remarks" => remarks = true,
            "--stats" => stats = true,
            "--verify-each" => {}
            "--no-locs" => locs = false,
            _ => return Err(fail(format!("unknown option {o}"))),
        }
    }
    pipeline.verify_each = cfg!(debug_assertions) || opts.contains(&"--verify-each");
    let mut m = fir::parse_module(&read(file)?).map_err(fail)?;
    fir::verify_module(&m).map_err(fail)?;
    let mut log = Remarks::new(remarks);
    let report = pipeline
        .run(&mut m, &mut log)
        .map_err(|e| fail(e.to_string()))?;
    fir::verify_module(&m)
        .map_err(|e| fail(format!("the optimized module doesn't verify: {e}")))?;
    for r in log.list() {
        eprintln!("{r}");
    }
    if stats {
        eprint!("{report}");
    }
    print!("{}", m.render(locs));
    Ok(())
}

/// `fir compile FILE`: compile an MFIR (or core-op HFIR) module to AArch64. `--emit lfir` and
/// `--emit lfir-vregs` print the LFIR after and before register allocation; `--emit asm` (or
/// `-o` naming a `.s` file) the assembly. Otherwise `-o OUT` is an object file (`.o`) or an
/// executable, assembled and linked by `$FIR_CC`, or else by `cc` on an AArch64 host and by
/// `aarch64-unknown-linux-gnu-cc` (from the dev shell) elsewhere. Linux ELF by default, or the
/// host's format on macOS; `--os` picks one.
fn compile(file: &str, opts: &[&str]) -> Result<(), ExitCode> {
    use fir::backend::aarch64 as a64;
    let fail = |e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    let mut out = None;
    let mut emit = None;
    let mut o = a64::Options::default();
    let mut it = opts.iter();
    while let Some(&opt) = it.next() {
        match (opt, it.next()) {
            ("-o", Some(&v)) => out = Some(v),
            ("--emit", Some(&v)) => emit = Some(v),
            ("--os", Some(&"linux")) => o.os = a64::Os::Linux,
            ("--os", Some(&"darwin")) => o.os = a64::Os::Darwin,
            _ => {
                eprintln!("fir compile: bad option '{opt}'");
                return Err(ExitCode::from(2));
            }
        }
    }
    let m = fir::parse_module(&read(file)?).map_err(fail)?;
    fir::verify_module(&m).map_err(fail)?;
    let mut mm = a64::select(&m).map_err(fail)?;
    let write = |text: String| -> Result<(), ExitCode> {
        match out {
            Some(p) => std::fs::write(p, text).map_err(|e| {
                eprintln!("{p}: {e}");
                ExitCode::FAILURE
            }),
            None => {
                print!("{text}");
                Ok(())
            }
        }
    };
    if emit == Some("lfir-vregs") {
        return write(a64::lfir::to_module(&m, &mm).render(true));
    }
    a64::allocate(&m, &mut mm);
    match emit {
        Some("lfir") => return write(a64::lfir::to_module(&m, &mm).render(true)),
        Some("asm") => return write(a64::emit::emit(&m, &mm, &o)),
        Some(e) => {
            eprintln!("fir compile: unknown --emit '{e}'");
            return Err(ExitCode::from(2));
        }
        None => {}
    }
    let asm = a64::emit::emit(&m, &mm, &o);
    let Some(out) = out.filter(|p| !p.ends_with(".s")) else {
        return write(asm);
    };
    let dir = std::env::temp_dir().join(format!("fir-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| fail(e.to_string()))?;
    let s = dir.join("out.s");
    std::fs::write(&s, asm).map_err(|e| fail(e.to_string()))?;
    let cc = std::env::var("FIR_CC").unwrap_or_else(|_| {
        if cfg!(target_arch = "aarch64") {
            "cc".to_owned()
        } else {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
    });
    let mut cmd = std::process::Command::new(&cc);
    cmd.arg(&s).arg("-o").arg(out);
    if out.ends_with(".o") {
        cmd.arg("-c");
    }
    let status = cmd.status();
    let _ = std::fs::remove_dir_all(&dir);
    match status {
        Ok(st) if st.success() => Ok(()),
        Ok(_) => Err(fail(format!("{cc} failed"))),
        Err(e) => Err(fail(format!("running {cc}: {e}"))),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => code,
    }
}
