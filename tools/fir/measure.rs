//! `fir measure FILE [-O | --none | --passes P,... [--experimental]] [--fuel N]`: what a pipeline
//! does to one module, as numbers that don't depend on the machine, and whether it kept the
//! module's meaning on the runs the file declares.
//!
//! The module is prepared as `fir compile` prepares it (HFIR lowered to MFIR, then the pipeline:
//! `-O` by default, `--none` for no passes, or `--passes` run to a fixed point as `fir compile
//! --passes` runs them), and then measured:
//!
//! * `ops.static`: ops in the prepared MFIR, every function and region;
//! * `ops.executed`, `mem.executed`, `calls.executed`: ops the interpreter dispatched running
//!   the prepared MFIR on every `// run:` line of the file (all ops; `mem.*` ops; `func.call*` and
//!   `func.invoke*` ops), counted only over runs whose source run is defined (not UB, stuck,
//!   ambiguous, or out of fuel), since otherwise the optimized program may do anything;
//! * `aarch64.insns`, `x86_64.insns`: instruction lines in the assembly each backend emits for
//!   the prepared MFIR (AArch64 as Linux ELF on every host, so the count is the same everywhere),
//!   or the backend's refusal;
//! * `prepare.us`: how long preparing took, in microseconds. The only number that depends on the
//!   machine; reported, never compared by `fai experiment`.
//!
//! Each run is also checked: the source module's run (the original, in this crate's interpreter)
//! must print what the `// run:` line expects (an error line counts as what `fir run` prints on
//! stderr), and the prepared module's run must refine it, as
//! `tests/rust/opt.rs` defines refinement (the same line; or, when the source is UB, stuck, or out
//! of fuel, the source's events first; nothing when it is ambiguous; allocations renumbered when
//! `stackdce` runs). The output is one JSON object on stdout. The exit code is 0 when every run
//! refines its source and matches its expectation, 1 when one doesn't (the JSON says which) or
//! the module can't be prepared, and 2 for bad usage. This checks only the runs the file names,
//! in the interpreter: it is evidence about this module, not a proof, and no substitute for the
//! differential suites (`fai experiment` runs both).

use std::fmt::Write as _;
use std::process::ExitCode;
use std::time::Instant;

use fir::backend::aarch64 as a64;
use fir::backend::x86_64 as x64;
use fir::passes::{Assurance, Pipeline};

/// A JSON string literal.
fn js(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A `// run: @f(ARGS) -> OUTCOME` line, as `tests/rust/run.rs` reads it.
struct RunLine {
    func: String,
    args: Vec<String>,
    want: String,
}

fn run_lines(text: &str) -> Result<Vec<RunLine>, String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let Some(body) = line.trim().strip_prefix("// run:") else {
            continue;
        };
        let bad = || format!("bad run line: {line}");
        let (call, want) = body.split_once(" -> ").ok_or_else(bad)?;
        let (name, rest) = call
            .trim()
            .strip_prefix('@')
            .and_then(|c| c.split_once('('))
            .ok_or_else(bad)?;
        let inner = rest.strip_suffix(')').ok_or_else(bad)?;
        let args = if inner.trim().is_empty() {
            Vec::new()
        } else {
            inner.split(',').map(|a| a.trim().to_owned()).collect()
        };
        out.push(RunLine {
            func: name.to_owned(),
            args,
            want: want.trim().to_owned(),
        });
    }
    Ok(out)
}

/// A run's line split into its events and its ending (`tests/rust/opt.rs`).
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

/// Allocation numbers renumbered in order of first appearance (`tests/rust/opt.rs`).
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
        if n == 0 {
            continue;
        }
        let id = &rest[..n];
        let k = names.iter().position(|x| *x == id).unwrap_or_else(|| {
            names.push(id);
            names.len() - 1
        });
        write!(out, "a{k}").unwrap();
        rest = &rest[n..];
    }
    out.push_str(rest);
    out
}

/// How a target run compared with its source run: `Ok(kind)` if it refines it.
fn refines(t: &Result<String, String>, s: &Result<String, String>) -> Result<&'static str, String> {
    let (Ok(tl), Ok(sl)) = (t, s) else {
        return if t == s {
            Ok("equal")
        } else {
            Err(format!("different errors: {s:?} became {t:?}"))
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
        prefix().map(|()| "source-ub")
    } else if send.starts_with("out of fuel") {
        prefix().map(|()| "source-fuel")
    } else if send.starts_with("ambiguous") {
        Ok("source-ambiguous")
    } else if tl == sl {
        Ok("equal")
    } else {
        Err(format!("the ending {send:?} became {tend:?}"))
    }
}

/// Ops in every function and region of `m`.
fn static_ops(m: &fir::Module) -> u64 {
    let mut n = 0;
    for f in &m.funcs {
        let body = &f.body;
        let mut regions = vec![body.entry()];
        while let Some(r) = regions.pop() {
            for op in body.ops(r) {
                n += 1;
                regions.extend(body.regions(op));
            }
        }
    }
    n
}

/// Instruction lines in assembly text: not blank, a directive, a label, or a comment.
fn insns(asm: &str) -> u64 {
    asm.lines()
        .map(str::trim)
        .filter(|l| {
            !l.is_empty()
                && !l.starts_with('.')
                && !l.ends_with(':')
                && !l.starts_with("//")
                && !l.starts_with('#')
                && !l.starts_with(';')
        })
        .count() as u64
}

pub fn measure(file: &str, opts: &[&str], text: &str) -> Result<(), ExitCode> {
    let usage = || {
        eprintln!(
            "usage: fir measure FILE [-O | --none | --passes P,... [--experimental]] [--fuel N]"
        );
        ExitCode::from(2)
    };
    let (mut spec, mut experimental, mut none) = (None, false, false);
    let mut fuel = fir::interp::DEFAULT_FUEL;
    let mut it = opts.iter();
    while let Some(&o) = it.next() {
        match o {
            "-O" => (spec, none) = (None, false),
            "--none" => (spec, none) = (None, true),
            "--experimental" => experimental = true,
            "--passes" => spec = Some(*it.next().ok_or_else(usage)?),
            "--fuel" => {
                fuel = it.next().and_then(|n| n.parse().ok()).ok_or_else(usage)?;
            }
            _ => return Err(usage()),
        }
    }
    let fail = |e: String| {
        eprintln!("{file}: {e}");
        ExitCode::FAILURE
    };
    let pipeline = match (spec, none) {
        (_, true) => None,
        (None, false) => Some(Pipeline::default_opt()),
        (Some(s), false) => Some(Pipeline::parse_fixpoint(s, experimental).map_err(fail)?),
    };
    let names: Vec<&'static str> = match (spec, none) {
        (_, true) => Vec::new(),
        (None, false) => fir::passes::DEFAULT.to_vec(),
        (Some(s), false) => s
            .split(',')
            .map(str::trim)
            .filter(|n| !n.is_empty())
            .filter_map(|n| fir::passes::PASSES.iter().find(|p| p.name == n))
            .map(|p| p.name)
            .collect(),
    };
    let renames = names.contains(&"stackdce");
    let m = fir::parse_module(text).map_err(fail)?;
    fir::verify_module(&m).map_err(fail)?;
    let lowered = m.layer == fir::Layer::Hfir;
    let runs = run_lines(text).map_err(fail)?;

    let start = Instant::now();
    let prepared = fir::backend::prepare_with(&m, pipeline.as_ref());
    let prepare_us = start.elapsed().as_micros() as u64;

    let mut out = String::from("{");
    write!(
        out,
        "\"file\": {}, \"layer\": {}, \"fuel\": {fuel}, \"pipeline\": {{\"spec\": {}, \"passes\": [",
        js(file),
        js(if lowered { "hfir" } else { "mfir" }),
        js(match (spec, none) {
            (_, true) => "none",
            (None, false) => "-O",
            (Some(s), false) => s,
        }),
    )
    .unwrap();
    for (i, n) in names.iter().enumerate() {
        let p = fir::passes::PASSES.iter().find(|p| p.name == *n).unwrap();
        let (proved, why) = match p.assurance {
            Assurance::Proved(t) => (true, t),
            Assurance::Experimental(w) => (false, w),
        };
        write!(
            out,
            "{}{{\"name\": {}, \"proved\": {proved}, \"assurance\": {}}}",
            if i > 0 { ", " } else { "" },
            js(n),
            js(why)
        )
        .unwrap();
    }
    out.push_str("]}");

    let prepared = match prepared.and_then(|p| fir::verify_module(&p).map(|_| p)) {
        Ok(p) => p,
        Err(e) => {
            write!(out, ", \"error\": {}}}", js(&format!("preparing: {e}"))).unwrap();
            println!("{out}");
            return Err(ExitCode::FAILURE);
        }
    };

    let (mut executed, mut mem, mut calls) = (0u64, 0u64, 0u64);
    let (mut measured, mut problems) = (0u64, 0u64);
    out.push_str(", \"runs\": [");
    for (i, r) in runs.iter().enumerate() {
        let args: Vec<&str> = r.args.iter().map(String::as_str).collect();
        let src = fir::interp::run_detail(&m, &r.func, &args, fuel, lowered);
        let tfuel = if lowered {
            fuel.saturating_mul(16)
        } else {
            fuel
        };
        let tgt = fir::interp::run_detail(&prepared, &r.func, &args, tfuel, false);
        let line = |x: &Result<fir::interp::RunOutput, String>| {
            x.as_ref().map(|o| o.line.clone()).map_err(String::clone)
        };
        let (sl, tl) = (line(&src), line(&tgt));
        let (sl, tl) = if renames {
            (sl.map(|l| rename_allocs(&l)), tl.map(|l| rename_allocs(&l)))
        } else {
            (sl, tl)
        };
        let verdict = refines(&tl, &sl);
        // The source must print what the file expects (as `fir run` prints it: an HFIR run is
        // compared with the lowering as the lowering returns, so it is run again for this).
        let plain = if lowered {
            fir::interp::run_detail(&m, &r.func, &args, fuel, false)
        } else {
            src.clone()
        };
        let expected = plain
            .as_ref()
            .map_or_else(|e| *e == r.want, |o| o.line == r.want);
        if verdict.is_err() || !expected {
            problems += 1;
        }
        if let (Ok("equal"), Ok(t)) = (&verdict, &tgt) {
            measured += 1;
            for (k, n) in t.profile.counts() {
                executed += n;
                if k.starts_with("mem.") {
                    mem += n;
                }
                if k.starts_with("func.call") || k.starts_with("func.invoke") {
                    calls += n;
                }
            }
        }
        let show = |x: &Result<String, String>| match x {
            Ok(l) => js(l),
            Err(e) => js(&format!("error: {e}")),
        };
        write!(
            out,
            "{}{{\"call\": {}, \"expected\": {}, \"source\": {}, \"target\": {}, \"matches expectation\": {expected}, \"refines\": {}, \"how\": {}}}",
            if i > 0 { ", " } else { "" },
            js(&format!("@{}({})", r.func, r.args.join(", "))),
            js(&r.want),
            show(&sl),
            show(&tl),
            verdict.is_ok(),
            js(&verdict.map_or_else(|e| e, str::to_owned)),
        )
        .unwrap();
    }
    out.push(']');

    let mut targets = String::new();
    let a64o = a64::Options {
        os: a64::Os::Linux,
        ..a64::Options::default()
    };
    for (name, asm) in [
        ("aarch64", a64::compile(&prepared, &a64o)),
        ("x86_64", x64::compile(&prepared, &x64::Options::default())),
    ] {
        match asm {
            Ok(a) => write!(out, ", \"{name}.refused\": null").map(|()| {
                write!(targets, ", \"{name}.insns\": {}", insns(&a)).unwrap();
            }),
            Err(e) => {
                let first = e.lines().next().unwrap_or("").to_owned();
                write!(out, ", \"{name}.refused\": {}", js(&first))
            }
        }
        .unwrap();
    }
    write!(
        out,
        ", \"metrics\": {{\"ops.static\": {}, \"ops.executed\": {executed}, \"mem.executed\": {mem}, \"calls.executed\": {calls}, \"runs\": {}, \"runs measured\": {measured}, \"run problems\": {problems}{targets}, \"prepare.us\": {prepare_us}}}}}",
        static_ops(&prepared),
        runs.len(),
    )
    .unwrap();
    println!("{out}");
    if problems > 0 {
        return Err(ExitCode::FAILURE);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refinement_as_the_optimizer_suite_defines_it() {
        let ok = |s: &str| Ok::<String, String>(s.to_owned());
        assert_eq!(
            refines(&ok("returned i32 1"), &ok("returned i32 1")),
            Ok("equal")
        );
        assert!(refines(&ok("returned i32 2"), &ok("returned i32 1")).is_err());
        assert_eq!(
            refines(&ok("@f(); returned i32 9"), &ok("@f(); ub div0 @1:1")),
            Ok("source-ub")
        );
        assert!(refines(&ok("returned i32 9"), &ok("@f(); ub div0 @1:1")).is_err());
        assert_eq!(
            rename_allocs("ptr #7 ptr #9+8 ptr #7"),
            "ptr #a0 ptr #a1+8 ptr #a0"
        );
        assert_eq!(insns(".text\nf:\n  add x0, x0, x1\n  // c\n  ret\n"), 2);
    }
}
