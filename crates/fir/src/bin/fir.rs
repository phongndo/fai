//! `fir`: the FIR command-line tool.
//!
//! ```text
//! fir check FILE                             verify; list holes
//! fir fmt FILE [--no-locs] [--unverified]     print canonical text (--unverified: parse only)
//! ```
//!
//! `check` prints what `fir-ref check` prints: `ok`, or one `hole ?NAME: TYPE @LOC` line per
//! hole; on failure, `FILE: MESSAGE` on stderr and exit code 1.

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
        _ => {
            eprintln!("usage:\n  fir check FILE\n  fir fmt FILE [--no-locs] [--unverified]");
            Err(ExitCode::from(2))
        }
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
