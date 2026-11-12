//! `fir`: the FIR command-line tool.
//!
//! ```text
//! fir fmt FILE [--no-locs]   print canonical text
//! ```

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["fmt", file, opts @ ..] => {
            let text = match std::fs::read_to_string(file) {
                Ok(t) => t,
                Err(e) => {
                    eprintln!("{file}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            match fir::parse_module(&text) {
                Ok(m) => {
                    print!("{}", m.render(!opts.contains(&"--no-locs")));
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("{file}: {e}");
                    ExitCode::FAILURE
                }
            }
        }
        _ => {
            eprintln!("usage:\n  fir fmt FILE [--no-locs]");
            ExitCode::from(2)
        }
    }
}
