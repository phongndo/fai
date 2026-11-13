//! Profiles follow dispatch through control flow and calls, rather than walking syntax. These
//! tests deliberately include unseen ops, stops, and repeated ops so static counting fails.

use std::collections::BTreeMap;

fn run(text: &str, name: &str, args: &[&str], fuel: u64) -> fir::interp::RunOutput {
    let m = fir::parse_module(text).unwrap();
    fir::verify_module(&m).unwrap();
    fir::interp::run_detail(&m, name, args, fuel, false).unwrap()
}

const BRANCHES: &str = "
func @unused(%x: i32) -> i32 {
  %y: i32 = int.mul.wrap %x, %x
  func.ret %y
}
func @callee(%x: i32) -> i32 {
  %y: i32 = int.and %x, %x
  func.ret %y
}
func @f(%c: i1, %x: i32) -> i32 {
  %r: i32 = cf.if %c {
    %y: i32 = func.call @callee(%x)
    cf.yield %y
  } else {
    %z: i32 = int.or %x, %x
    cf.yield %z
  }
  func.ret %r
}
";

#[test]
fn only_taken_regions_and_called_functions_count() {
    let r = run(BRANCHES, "f", &["1", "7"], 100);
    assert_eq!(r.line, "returned i32 7");
    assert_eq!(
        r.profile.counts().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([
            ("cf.if", 1),
            ("cf.yield", 1),
            ("func.call", 1),
            ("func.ret", 2),
            ("int.and", 1),
        ])
    );
    let r = run(BRANCHES, "f", &["0", "7"], 100);
    assert_eq!(
        r.profile.counts().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([
            ("cf.if", 1),
            ("cf.yield", 1),
            ("func.ret", 1),
            ("int.or", 1),
        ])
    );
}

#[test]
fn halting_op_counts_but_nothing_after_ub_or_past_fuel() {
    let r = run(
        "func @f(%x: i32, %zero: i32) -> i32 {
  %bad: i32 = int.div.u.ub %x, %zero
  %late: i32 = int.xor %bad, %x
  func.ret %late
}",
        "f",
        &["1", "0"],
        100,
    );
    assert!(r.line.starts_with("ub div0"), "{}", r.line);
    assert_eq!(
        r.profile.counts().collect::<Vec<_>>(),
        [("int.div.u.ub", 1)]
    );
    let r = run(BRANCHES, "f", &["1", "7"], 0);
    assert!(r.out_of_fuel);
    assert_eq!(r.profile.counts().count(), 0);
    let r = run(BRANCHES, "f", &["1", "7"], 1);
    assert!(r.out_of_fuel);
    assert_eq!(r.profile.counts().collect::<Vec<_>>(), [("cf.if", 1)]);
}

#[test]
fn repeated_dispatches_are_counted_and_runs_do_not_share_counts() {
    let text = "func @f() {
  cf.loop {
    %zero: i32 = int.const 0
    cf.continue
  }
  func.ret
}";
    let a = run(text, "f", &[], 12);
    let b = run(text, "f", &[], 12);
    let counts: BTreeMap<_, _> = a.profile.counts().collect();
    assert!(counts["int.const"] > 1);
    assert!(!counts.contains_key("func.ret"));
    assert_eq!(a.profile, b.profile);
}

#[test]
fn lfir_counts_entered_containers_calls_and_only_reached_instructions() {
    let text = "layer lfir aarch64
func @g(%x: i64) -> i64 {
  aarch64.code {
  ^entry:
    aarch64.add.imm.x x0, x0, 1
    aarch64.ret
  }
}
func @f(%x: i64) -> i64 {
  aarch64.code {
  ^entry:
    aarch64.bl @g
    aarch64.b ^done
  ^unseen:
    aarch64.mul.x x0, x0, x0
    aarch64.ret
  ^done:
    aarch64.ret
  }
}
func @stop() {
  aarch64.code {
  ^entry:
    aarch64.trap.div0
  ^unseen:
    aarch64.movz.w x0, 1, 0
    aarch64.ret
  }
}
func @ub() {
  aarch64.code {
  ^entry:
    aarch64.movz.x x0, 0, 0
    aarch64.ldr.x x1, x0, 0
    aarch64.movn.w x0, 1, 0
    aarch64.ret
  }
}
";
    let r = run(text, "f", &["4"], 100);
    assert_eq!(r.line, "returned i64 5");
    assert_eq!(
        r.profile.counts().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([
            ("aarch64.code", 2),
            ("aarch64.bl", 1),
            ("aarch64.add.imm.x", 1),
            ("aarch64.b", 1),
            ("aarch64.ret", 2),
        ])
    );
    let r = run(text, "stop", &[], 100);
    assert_eq!(
        r.profile.counts().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([("aarch64.code", 1), ("aarch64.trap.div0", 1),])
    );
    let r = run(text, "f", &["4"], 0);
    assert!(r.out_of_fuel);
    // LFIR enters the initial container during initialization, before its instruction budget.
    assert_eq!(
        r.profile.counts().collect::<Vec<_>>(),
        [("aarch64.code", 1)]
    );
    let r = run(text, "ub", &[], 100);
    assert!(r.absorbing);
    assert_eq!(
        r.profile.counts().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([
            ("aarch64.code", 1),
            ("aarch64.movz.x", 1),
            ("aarch64.ldr.x", 1),
        ])
    );
}
