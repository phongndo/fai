//! `fir`: the FIR command-line tool.
//!
//! ```text
//! fir run FILE [@FUNC] [ARG...] [--fuel N]   run a function (default @main)
//! fir check FILE                             verify; list holes
//! fir fmt FILE [--no-locs] [--unverified]     print canonical text (--unverified: parse only)
//! fir opt FILE [-O | --passes P,...] [--experimental] [--remarks] [--stats] [--verify-each]
//!              [--no-locs] [--print-before P,...] [--print-after P,...] [--print-changed]
//!              [--dump-dir DIR] [--check-dce FIR-REF]
//!                                            optimize, print canonical text
//! fir opt --list-passes                      the passes, with what backs each
//! fir compile FILE [-O [--check-dce FIR-REF] | --passes P,... [--experimental]] [-g] [-o OUT]
//!             [--emit mfir|asm|lfir|lfir-vregs] [--os linux|darwin]   compile to AArch64 (see `compile`)
//! fir lower FILE [--no-locs]                  lower an HFIR module to MFIR and print it
//! ```
//!
//! `check` prints what `fir-ref check` prints: `ok`, or one `hole ?NAME: TYPE @LOC` line per
//! hole; on failure, `FILE: MESSAGE` on stderr and exit code 1. `run` prints the one-line
//! outcome `fir-ref run` prints, for the same oracle (every choice answers `0`); arguments are
//! integers, `null`, or `poison`, parsed as Lean parses them. `lower` prints what `fir-ref lower`
//! prints: the verified MFIR lowering of a verified HFIR module.
//!
//! `opt` runs a pipeline of passes (`fir::passes`): the default `-O` one to a fixed point, or the
//! passes named by `--passes`, once each, in order. It prints the optimized module; `--remarks`
//! prints what each pass changed on stderr (`dse: deleted store @3:5 (overwritten by @4:5)`),
//! and `--stats` how often each pass fired and how long it took. Debug builds, or
//! `--verify-each`, verify after every pass and name the pass that broke the module; the output
//! is always verified.
//!
//! Observing a run: `--print-before P` and `--print-after P` print the module (to stderr, each
//! after a `// ---- after P (round R): N changes ----` line) around every run of the passes named
//! (`all` for every pass); `--print-changed` prints only after runs that changed something (all
//! passes, unless `--print-after` names some). `--dump-dir DIR` writes the input and the module
//! after every pass run to numbered files (`000-input.fir`, `001-r1-fwd.fir`, …; with
//! `--print-changed`, only runs that changed something), to diff. `--check-dce FIR-REF` runs the
//! proved Lean checker (`fir-ref check-dce`) on every step of `dce` in this run and fails if it
//! refuses one (`fir::passes::reference`), and prints a summary on stderr (how many steps it checked, and the time).
//! Without the flag, `FIR_CHECK_DCE=FIR-REF` in the environment does the same, as for
//! `fir compile -O` and the C API.
//! Experimental passes (unproved; `--list-passes` labels each pass) run only with
//! `--experimental`, and are never in `-O`. A FILE of `-` is standard input.

use std::process::ExitCode;

fn read(file: &str) -> Result<String, ExitCode> {
    if file == "-" {
        let mut s = String::new();
        return std::io::Read::read_to_string(&mut std::io::stdin(), &mut s)
            .map(|_| s)
            .map_err(|e| {
                eprintln!("stdin: {e}");
                ExitCode::FAILURE
            });
    }
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
        ["lower", file, opts @ ..] => {
            let m = fir::parse_module(&read(file)?).map_err(|e| fail(file, e))?;
            fir::verify_module(&m).map_err(|e| fail(file, e))?;
            let l = fir::lower_checked(&m).map_err(|e| fail(file, e))?;
            print!("{}", l.render(!opts.contains(&"--no-locs")));
            Ok(())
        }
        _ => {
            eprintln!(
                "usage:\n  fir run FILE [@FUNC] [ARG...] [--fuel N]\n  fir check FILE\n  fir fmt FILE [--no-locs] [--unverified]\n  fir opt FILE [-O | --passes P,...] [--experimental] [--remarks] [--stats] [--verify-each] [--no-locs]\n         [--print-before P,...] [--print-after P,...] [--print-changed] [--dump-dir DIR] [--check-dce FIR-REF]\n  fir opt --list-passes\n  fir compile FILE [-O [--check-dce FIR-REF] | --passes P,... [--experimental]] [-g] [-o OUT] [--emit mfir|asm|lfir|lfir-vregs] [--os linux|darwin]\n  fir lower FILE [--no-locs]"
            );
            Err(ExitCode::from(2))
        }
    }
}

/// IR dumps around chosen passes, for `fir opt --print-before/--print-after/--dump-dir`.
struct Dumps {
    before: Vec<String>,
    after: Vec<String>,
    changed_only: bool,
    locs: bool,
    dir: Option<std::path::PathBuf>,
    seq: u32,
}

impl Dumps {
    fn wants(list: &[String], pass: &str) -> bool {
        list.iter().any(|p| p == "all" || p == pass)
    }

    fn write(&mut self, label: &str, m: &fir::Module) -> Result<(), String> {
        if let Some(dir) = &self.dir {
            let f = dir.join(format!("{:03}-{label}.fir", self.seq));
            self.seq += 1;
            std::fs::write(&f, m.render(self.locs)).map_err(|e| format!("{}: {e}", f.display()))?;
        }
        Ok(())
    }
}

impl fir::passes::Observer for Dumps {
    fn before(&mut self, pass: &fir::passes::Pass, round: u32, m: &fir::Module) {
        if Dumps::wants(&self.before, pass.name) {
            eprint!(
                "// ---- before {} (round {round}) ----\n{}",
                pass.name,
                m.render(self.locs)
            );
        }
    }

    fn after(
        &mut self,
        pass: &fir::passes::Pass,
        round: u32,
        changes: u32,
        m: &fir::Module,
    ) -> Result<(), String> {
        if Dumps::wants(&self.after, pass.name) && (changes > 0 || !self.changed_only) {
            eprint!(
                "// ---- after {} (round {round}): {changes} changes ----\n{}",
                pass.name,
                m.render(self.locs)
            );
        }
        if changes > 0 || !self.changed_only {
            self.write(&format!("r{round}-{}", pass.name), m)?;
        }
        Ok(())
    }
}

/// Both observers in turn.
struct Both<'a>(
    &'a mut dyn fir::passes::Observer,
    &'a mut dyn fir::passes::Observer,
);

impl fir::passes::Observer for Both<'_> {
    fn before(&mut self, pass: &fir::passes::Pass, round: u32, m: &fir::Module) {
        self.0.before(pass, round, m);
        self.1.before(pass, round, m);
    }

    fn after(
        &mut self,
        pass: &fir::passes::Pass,
        round: u32,
        changes: u32,
        m: &fir::Module,
    ) -> Result<(), String> {
        self.0.after(pass, round, changes, m)?;
        self.1.after(pass, round, changes, m)
    }
}

fn list_passes() {
    for p in fir::passes::PASSES {
        let default = if fir::passes::DEFAULT.contains(&p.name) {
            " [-O]"
        } else {
            ""
        };
        println!(
            "{:<10}{default} {}\n           {}",
            p.name, p.summary, p.assurance
        );
    }
}

fn opt(file: &str, opts: &[&str]) -> Result<(), ExitCode> {
    use fir::passes::{Pipeline, Remarks, reference::CheckDce};
    if file == "--list-passes" {
        list_passes();
        return Ok(());
    }
    let fail = |e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    let (mut remarks, mut stats, mut locs, mut experimental) = (false, false, true, false);
    let mut spec: Option<&str> = None;
    let mut dumps = Dumps {
        before: Vec::new(),
        after: Vec::new(),
        changed_only: false,
        locs: true,
        dir: None,
        seq: 0,
    };
    let mut check_dce: Option<CheckDce> = None;
    let mut it = opts.iter();
    fn value<'a>(it: &mut std::slice::Iter<'_, &'a str>, o: &str) -> Result<&'a str, ExitCode> {
        it.next().copied().ok_or_else(|| {
            eprintln!("fir opt: {o} needs a value");
            ExitCode::from(2)
        })
    }
    while let Some(&o) = it.next() {
        match o {
            "-O" => spec = None,
            "--passes" => spec = Some(value(&mut it, o)?),
            "--experimental" => experimental = true,
            "--remarks" => remarks = true,
            "--stats" => stats = true,
            "--verify-each" => {}
            "--no-locs" => locs = false,
            "--print-before" => dumps
                .before
                .extend(value(&mut it, o)?.split(',').map(str::to_owned)),
            "--print-after" => dumps
                .after
                .extend(value(&mut it, o)?.split(',').map(str::to_owned)),
            "--print-changed" => dumps.changed_only = true,
            "--dump-dir" => dumps.dir = Some(value(&mut it, o)?.into()),
            "--check-dce" => {
                check_dce = Some(CheckDce::in_temp_dir(value(&mut it, o)?).map_err(fail)?);
            }
            _ => return Err(fail(format!("unknown option {o}"))),
        }
    }
    dumps.locs = locs;
    // As `fir compile -O` and the C API do (`fir::backend::optimize`).
    if check_dce.is_none() {
        check_dce = CheckDce::from_env().map_err(fail)?;
    }
    if dumps.changed_only && dumps.after.is_empty() && dumps.dir.is_none() {
        dumps.after.push("all".to_owned());
    }
    let mut pipeline = match spec {
        None => Pipeline::default_opt(),
        Some(s) if experimental => Pipeline::parse_experimental(s).map_err(fail)?,
        Some(s) => Pipeline::parse(s).map_err(fail)?,
    };
    if pipeline.is_experimental() {
        eprintln!(
            "{file}: warning: running experimental (unproved) passes; see `fir opt --list-passes`"
        );
    }
    pipeline.verify_each = cfg!(debug_assertions) || opts.contains(&"--verify-each");
    let mut m = fir::parse_module(&read(file)?).map_err(fail)?;
    fir::verify_module(&m).map_err(fail)?;
    if let Some(dir) = &dumps.dir {
        std::fs::create_dir_all(dir).map_err(|e| fail(format!("{}: {e}", dir.display())))?;
        dumps.write("input", &m).map_err(fail)?;
    }
    let mut log = Remarks::new(remarks);
    let mut none = ();
    let checker: &mut dyn fir::passes::Observer = match &mut check_dce {
        Some(c) => c,
        None => &mut none,
    };
    let report = pipeline.run_observed(&mut m, &mut log, &mut Both(&mut dumps, checker));
    if let Some(c) = &check_dce {
        c.finish();
    }
    let report = report.map_err(|e| fail(e.to_string()))?;
    fir::verify_module(&m)
        .map_err(|e| fail(format!("the optimized module doesn't verify: {e}")))?;
    for r in log.list() {
        eprintln!("{r}");
    }
    if stats {
        eprint!("{report}");
    }
    // A checked run always says so, as `fir compile` does.
    if let Some(c) = &check_dce {
        eprintln!("fir: {}", c.summary());
    }
    print!("{}", m.render(locs));
    Ok(())
}

/// `fir compile FILE`: compile an HFIR or MFIR module to AArch64. HFIR is lowered to MFIR first
/// (what `fir lower` prints), and `-O` runs the default pass pipeline on the MFIR (what `fir opt`
/// does); `--emit mfir` prints the MFIR that is compiled. `--emit lfir` and `--emit lfir-vregs`
/// print the LFIR after and before register allocation; `--emit asm` (or `-o` naming a `.s`
/// file) the assembly. Otherwise `-o OUT` is an object file (`.o`) or an
/// executable, assembled and linked by `$FIR_CC`, or else by `cc` on an AArch64 host and by
/// `aarch64-unknown-linux-gnu-cc` (from the dev shell) elsewhere. Linux ELF by default, or the
/// host's format on macOS; `--os` picks one. `-g` writes source lines (`.file`/`.loc`) for the
/// assembler's DWARF line table, from the locations the LFIR carries (`Options::debug_lines`).
/// `--check-dce FIR-REF` (with `-O`) checks every step of `dce` with the proved Lean checker, as
/// `fir opt --check-dce` does, fails if it refuses one, and prints a summary on stderr; so does
/// `FIR_CHECK_DCE=FIR-REF` in the environment (`fir::backend::optimize`).
fn compile(file: &str, opts: &[&str]) -> Result<(), ExitCode> {
    use fir::backend::aarch64 as a64;
    let fail = |e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    let mut out = None;
    let mut emit = None;
    let mut optimize = false;
    let mut check_dce = None;
    let (mut passes, mut experimental) = (None, false);
    let mut o = a64::Options::default();
    let mut it = opts.iter();
    while let Some(&opt) = it.next() {
        if opt == "-O" {
            optimize = true;
            continue;
        }
        if opt == "--experimental" {
            experimental = true;
            continue;
        }
        if opt == "-g" {
            o.debug_lines = true;
            continue;
        }
        match (opt, it.next()) {
            ("-o", Some(&v)) => out = Some(v),
            ("--emit", Some(&v)) => emit = Some(v),
            ("--check-dce", Some(&v)) => check_dce = Some(v),
            ("--passes", Some(&v)) => passes = Some(v),
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
    let m = if let Some(spec) = passes {
        if check_dce.is_some() {
            eprintln!("fir compile: --check-dce checks the -O pipeline's dce, not --passes");
            return Err(ExitCode::from(2));
        }
        let p = fir::passes::Pipeline::parse_fixpoint(spec, experimental).map_err(fail)?;
        if p.is_experimental() {
            eprintln!(
                "{file}: warning: running experimental (unproved) passes; see `fir opt --list-passes`"
            );
        }
        fir::backend::prepare_with(&m, Some(&p)).map_err(fail)?
    } else {
        match check_dce {
            None => fir::backend::prepare(&m, optimize).map_err(fail)?,
            Some(_) if !optimize => {
                eprintln!("fir compile: --check-dce checks the -O pipeline's dce; add -O");
                return Err(ExitCode::from(2));
            }
            Some(tool) => {
                let mut c = fir::passes::reference::CheckDce::in_temp_dir(tool).map_err(fail)?;
                let r = fir::backend::prepare_observed(&m, true, &mut c);
                c.finish();
                let m = r.map_err(fail)?;
                eprintln!("fir: {}", c.summary());
                m
            }
        }
    };
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
    if emit == Some("mfir") {
        return write(m.render(true));
    }
    let mut mm = a64::select(&m).map_err(fail)?;
    if emit == Some("lfir-vregs") {
        return write(a64::lfir::to_module(&m, &mm).render(true));
    }
    a64::allocate(&m, &mut mm).map_err(fail)?;
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
