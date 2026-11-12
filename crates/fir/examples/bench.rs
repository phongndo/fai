//! Time each phase on one file: `cargo run --release --example bench FILE [RUNS]`. The total is
//! parse, verify, and print; building the use lists (which passes do) is timed separately.

use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let text = std::fs::read_to_string(&args[0]).unwrap();
    let runs: u32 = args.get(1).map_or(10, |s| s.parse().unwrap());
    let (mut parse, mut verify, mut print, mut uses) = (0.0, 0.0, 0.0, 0.0);
    let mut out_len = 0;
    for _ in 0..runs {
        let t = Instant::now();
        let mut m = fir::parse_module(&text).unwrap();
        parse += t.elapsed().as_secs_f64();
        let t = Instant::now();
        let holes = fir::verify_module(&m).unwrap();
        verify += t.elapsed().as_secs_f64();
        let t = Instant::now();
        let out = m.render(true);
        print += t.elapsed().as_secs_f64();
        let t = Instant::now();
        for f in &mut m.funcs {
            f.body.build_uses();
        }
        uses += t.elapsed().as_secs_f64();
        out_len = out.len() + holes.len();
    }
    let mb = text.len() as f64 / 1e6;
    let ms = |s: f64| s / runs as f64 * 1e3;
    println!(
        "{:.1} MB: parse {:.1} ms ({:.0} MB/s), verify {:.1} ms, print {:.1} ms; total {:.1} ms; use lists {:.1} ms [{out_len}]",
        mb,
        ms(parse),
        mb / (parse / runs as f64),
        ms(verify),
        ms(print),
        ms(parse + verify + print),
        ms(uses)
    );
}
