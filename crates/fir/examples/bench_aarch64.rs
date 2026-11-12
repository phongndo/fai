//! Time the AArch64 backend on one file: `cargo run --release --example bench_aarch64 FILE
//! [RUNS]`: instruction selection, register allocation (with the frame), and assembly output.

use std::time::Instant;

use fir::backend::aarch64 as a64;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let text = std::fs::read_to_string(&args[0]).unwrap();
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
        a64::allocate(&m, &mut mm);
        ra += t.elapsed().as_secs_f64();
        let t = Instant::now();
        let s = a64::emit::emit(&m, &mm, &a64::Options::default());
        emit += t.elapsed().as_secs_f64();
        insts = mm.funcs.iter().map(|f| f.insts.len()).sum();
        size = s.len();
    }
    let ms = |s: f64| s / f64::from(runs) * 1e3;
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
