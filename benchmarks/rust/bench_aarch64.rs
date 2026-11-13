//! Time the AArch64 backend on one file: `cargo run --release --example bench_aarch64 FILE
//! [RUNS]`: instruction selection, register allocation (with the frame and its validation), and
//! assembly output. The validation (`regcheck::validate`, part of register allocation) is also
//! timed on its own. `FILE` may be `synthetic:N`: N functions that each keep 32 values live
//! across a call and a join, so they spill and use callee-saved registers.

use std::time::Instant;

use fir::backend::aarch64 as a64;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let text = match args[0].strip_prefix("synthetic:") {
        Some(n) => synthetic(n.parse().unwrap()),
        None => std::fs::read_to_string(&args[0]).unwrap(),
    };
    let runs: u32 = args.get(1).map_or(5, |s| s.parse().unwrap());
    let t = Instant::now();
    let m = fir::parse_module(&text).unwrap();
    fir::verify_module(&m).unwrap();
    let front = t.elapsed().as_secs_f64();
    let ops: usize = m.funcs.iter().map(|f| f.body.num_ops()).sum();
    let (mut isel, mut ra, mut emit) = (0.0, 0.0, 0.0);
    let mut insts = 0;
    let mut size = 0;
    for _ in 0..runs {
        let t = Instant::now();
        let mut mm = a64::select(&m).unwrap();
        isel += t.elapsed().as_secs_f64();
        let t = Instant::now();
        a64::allocate(&m, &mut mm).unwrap();
        ra += t.elapsed().as_secs_f64();
        let t = Instant::now();
        let s = a64::emit::emit(&m, &mm, &a64::Options::default());
        emit += t.elapsed().as_secs_f64();
        insts = mm.funcs.iter().map(|f| f.insts.len()).sum();
        size = s.len();
    }
    // The validation alone, on the same inputs and outputs.
    let input = a64::select(&m).unwrap();
    let mut out = input.clone();
    a64::allocate(&m, &mut out).unwrap();
    let shapes = a64::shapes(&m);
    let mut validate = 0.0;
    for _ in 0..runs {
        // The validator consumes the output and borrows the destination. Prepare fresh pairs
        // outside the timer so cloning is not attributed to validation.
        let mut inputs = input.clone();
        let outputs = out.clone();
        let t = Instant::now();
        for (i, o) in inputs.funcs.iter_mut().zip(outputs.funcs) {
            let own = i.index as usize;
            drop(a64::regcheck::validate(i, o, &shapes, &shapes[own]).unwrap());
        }
        validate += t.elapsed().as_secs_f64();
    }
    // Allocation function by function on one thread (validation included), for the share.
    let t = Instant::now();
    for _ in 0..runs {
        for i in &input.funcs {
            let mut f = i.clone();
            a64::regalloc::allocate(&mut f, &shapes, &shapes[i.index as usize]).unwrap();
        }
    }
    let seq = t.elapsed().as_secs_f64();
    let ms = |s: f64| s / f64::from(runs) * 1e3;
    println!(
        "one thread: allocation with validation {:.1} ms, of which validation {:.1} ms ({:.0}% over allocation alone)",
        ms(seq),
        ms(validate),
        100.0 * validate / (seq - validate)
    );
    let total = (isel + ra + emit) / f64::from(runs);
    println!(
        "{} functions, {ops} ops -> {insts} instructions ({:.1} MB of assembly); parse+verify {:.1} ms; isel {:.1} ms, regalloc {:.1} ms, emit {:.1} ms; backend {:.1} ms ({:.0} ops/ms)",
        m.funcs.len(),
        size as f64 / 1e6,
        front * 1e3,
        ms(isel),
        ms(ra),
        ms(emit),
        total * 1e3,
        ops as f64 / (total * 1e3)
    );
}

/// `n` functions that keep 32 values live across a call and a `cf.if`.
fn synthetic(n: usize) -> String {
    let mut s = String::from("extern func @g(i64) -> i64 effects[] assume\n\n");
    for f in 0..n {
        s += &format!("func @f{f}(%x: i64, %c: i1) -> i64 {{\n");
        for k in 0..32 {
            s += &format!(
                "  %k{k}: i64 = int.const {}\n  %a{k}: i64 = int.add.wrap %x, %k{k}\n",
                k + f
            );
        }
        s += "  %r: i64 = func.call @g(%x)\n";
        s += "  %y: i64 = cf.if %c {\n    %t: i64 = int.add.wrap %a0, %r\n    cf.yield %t\n  } else {\n    cf.yield %a1\n  }\n";
        s += "  %s0: i64 = int.add.wrap %y, %a2\n";
        for k in 3..32 {
            s += &format!("  %s{}: i64 = int.add.wrap %s{}, %a{k}\n", k - 2, k - 3);
        }
        s += "  func.ret %s29\n}\n\n";
    }
    s
}
