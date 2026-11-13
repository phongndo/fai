//! Dead code elimination, translation-validated by the checker proved in Lean.
//!
//! For every verified fixture and `FIR_FUZZ` (default 200) random programs, and the MFIR their
//! lowering gives: the other passes run first (`fwd,copyprop,dse`, so there are dead copies to
//! delete), then the Rust pass (`plan`, the Rust `check`, `apply`), and `fir-ref check-dce`
//! runs `Fir.Dce.checkModule` on the module before and after it (`Fir.Dce.checkFuncL` on each
//! pair of functions, proved equal to `Fir.Dce.checkFunc`). `Fir.Dce.checkModule_sound` says
//! that, conditional on `Decided`, each accepted function refines its source in the fixed source
//! module. The receipt binds this evidence to both complete snapshots; this does not prove
//! refinement when composing the changed functions into a different module.
//!
//! The same modules also go through the default `-O` pipeline, run to its fixed point, with
//! every step of `dce` checked as it happens (`fir::passes::reference::CheckDce`, which
//! `fir opt --check-dce` uses), so the configuration the compiler runs is checked too.
//!
//! Then the checkers themselves: candidates that delete an op whose result is read, or an unread
//! op the contracts keep (a trapping add, `freeze`, a load, a store, `ptr.addr`, a call), must be
//! refused by the Rust checker for that reason; the same deletions written out as modules must
//! be refused by the Lean checker (or, where the deletion leaves a use without a definition, by
//! the verifier before it); and an op changed rather than deleted must be refused by the Lean
//! checker.

//!
//! Last, the compiler's own entry points: `fir compile -O --check-dce FIR-REF`, and
//! `FIR_CHECK_DCE=FIR-REF` with no flag (what `fai-cc -O --check-dce` and the C API use, and
//! `fir opt -O` honours), must run
//! the proved checker on a module with deletions, and must fail when the `fir-ref` they are given
//! refuses, or accepts with a receipt for other modules.

#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod progs;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use fir::contract::Policy;
use fir::passes::dce::{self, Candidate};
use fir::passes::{Pipeline, Remarks};

use common::evidence::Evidence;

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).map_or(default, |s| s.parse().expect(name))
}

fn scratch() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("dce-check");
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Evidence about these immutable snapshots, not permission to use some other module. Keeping
/// both borrows prevents a checked snapshot from being edited while this receipt is in use.
#[derive(Debug)]
struct LeanAccepted<'a> {
    source: &'a fir::Module,
    target: &'a fir::Module,
}

impl LeanAccepted<'_> {
    fn functions(&self) -> u64 {
        assert_eq!(self.source.funcs.len(), self.target.funcs.len());
        self.target.funcs.len() as u64
    }
}

fn receipt(src: &fir::Module, tgt: &fir::Module) -> String {
    format!(
        "ok {}\nsource:\n{}target:\n{}",
        src.funcs.len(),
        src.render(true),
        tgt.render(true)
    )
}

/// Match the Lean-parsed snapshots too: the printer/parser boundary is part of the trusted
/// base, and a successful exit about different text must not count as checking our output.
fn accept_receipt<'a>(
    src: &'a fir::Module,
    tgt: &'a fir::Module,
    text: &str,
) -> Result<LeanAccepted<'a>, String> {
    if text != receipt(src, tgt) {
        return Err(
            "checker receipt does not match the submitted source and target modules".to_owned(),
        );
    }
    Ok(LeanAccepted {
        source: src,
        target: tgt,
    })
}

/// `fir-ref check-dce SRC TGT`, with a receipt bound to both complete module snapshots.
fn lean_check<'a>(
    tool: &Path,
    src: &'a fir::Module,
    tgt: &'a fir::Module,
    name: &str,
) -> Result<LeanAccepted<'a>, String> {
    let dir = scratch();
    let (s, t) = (
        dir.join(format!("{name}.src.fir")),
        dir.join(format!("{name}.tgt.fir")),
    );
    std::fs::write(&s, src.render(true)).unwrap();
    std::fs::write(&t, tgt.render(true)).unwrap();
    let out = Command::new(tool)
        .arg("check-dce")
        .arg(&s)
        .arg(&t)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let r = if out.status.success() {
        accept_receipt(src, tgt, &stdout)
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_owned())
    };
    if r.is_ok() {
        let _ = std::fs::remove_file(&s);
        let _ = std::fs::remove_file(&t);
    }
    r
}

/// The other passes, then dead code elimination through the checked seam: the module before and
/// after it, and how many ops it deleted.
fn run_dce(m: &fir::Module) -> Result<(fir::Module, fir::Module, u64), String> {
    let mut src = m.clone();
    Pipeline::parse("fwd,copyprop,dse")
        .unwrap()
        .run(&mut src, &mut Remarks::new(false))
        .map_err(|e| e.to_string())?;
    let mut tgt = src.clone();
    let mut n = 0;
    for f in &mut tgt.funcs {
        let c = dce::plan(&f.body, Policy::VerifiedOnly);
        let a = dce::check(&mut f.body, c, Policy::VerifiedOnly)
            .map_err(|e| format!("@{}: {e}", f.name))?;
        n += u64::from(dce::apply(a, &mut Remarks::new(false)));
    }
    fir::verify_module(&tgt).map_err(|e| format!("after dce: {e}"))?;
    Ok((src, tgt, n))
}

fn check_one(tool: &Path, m: &fir::Module, name: &str, ev: &Evidence, fails: &Mutex<Vec<String>>) {
    match run_dce(m) {
        Err(e) => fails.lock().unwrap().push(format!("{name}: {e}")),
        Ok((src, tgt, n)) => {
            ev.count("modules", 1);
            ev.count("ops deleted", n);
            match lean_check(tool, &src, &tgt, name) {
                Ok(accepted) => {
                    ev.count(
                        "functions accepted by Fir.Dce.checkFunc",
                        accepted.functions(),
                    );
                    if n > 0 {
                        ev.count("modules with deletions accepted", 1);
                    }
                }
                Err(e) => fails
                    .lock()
                    .unwrap()
                    .push(format!("{name}: fir-ref check-dce: {e}")),
            }
        }
    }
    // The production configuration: the `-O` pipeline to its fixed point, with every step of
    // `dce` checked as it happens (`fir opt -O --check-dce`).
    let mut m = m.clone();
    let mut checker =
        fir::passes::reference::CheckDce::new(tool, scratch().join(format!("{name}-pipeline")));
    match Pipeline::default_opt().run_observed(&mut m, &mut Remarks::new(false), &mut checker) {
        Ok(_) => {
            ev.count("-O dce steps accepted by Fir.Dce.checkFunc", checker.steps);
            ev.count("-O deletions accepted", checker.deletions);
        }
        Err(e) => fails.lock().unwrap().push(format!("{name}: -O: {e}")),
    }
}

#[test]
fn the_pass_is_validated_by_the_proved_checker() {
    let ev = Evidence::new("dce_check");
    let Some(tool) = common::reference() else {
        ev.skip("no Lean reference");
        ev.write();
        return;
    };
    let fails = Mutex::new(Vec::new());
    for file in common::fir_files() {
        let text = std::fs::read_to_string(&file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() || matches!(m.layer, fir::Layer::Lfir(_)) {
            continue;
        }
        let name = common::display_name(&file).replace(['/', '.'], "_");
        check_one(&tool, &m, &name, &ev, &fails);
    }
    let count = env_u64("FIR_FUZZ", 200);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    ev.fact("seed", seed.to_string());
    let next = Mutex::new(0u64);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let k = {
                        let mut n = next.lock().unwrap();
                        *n += 1;
                        *n - 1
                    };
                    if k >= count {
                        return;
                    }
                    let mut rng = progs::Rng::new(seed.wrapping_mul(0x1_0000_0001) ^ k);
                    let prog = progs::program(&mut rng);
                    let m = fir::parse_module(&prog.text).unwrap();
                    fir::verify_module(&m).unwrap();
                    ev.count("random programs", 1);
                    check_one(&tool, &m, &format!("s{seed}-p{k}"), &ev, &fails);
                    if let Ok(l) = fir::lower_checked(&m) {
                        ev.count("random programs, lowered", 1);
                        check_one(&tool, &l, &format!("s{seed}-p{k}-mfir"), &ev, &fails);
                    }
                }
            });
        }
    });
    ev.write();
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
}

/// A function with one unread op of each kind the contracts keep, and a dead copy chain.
const KEPT: &str = "extern func @g(i32) -> i32 effects[] assume

func @f(%x: i32, %p: ptr) -> i32 {
  %y: i32 = copy %x @2:3
  %a: i32 = int.add.s.trap %x, %x @3:3
  %b: i32 = freeze %x @4:3
  %c: i32 = mem.load %p, align 4 @5:3
  mem.store i32 %x, %p, align 4 @6:3
  %d: i64 = ptr.addr %p @7:3
  %e: i32 = func.call @g(%x) @8:3
  %z: i32 = int.add.wrap %y, %x @9:3
  %w: i32 = int.mul.wrap %z, %z @10:3
  func.ret %z @11:3
}
";

fn op_at(m: &fir::Module, line: u32) -> fir::OpId {
    let b = &m.funcs[0].body;
    b.ops(b.entry())
        .find(|&op| b.loc(op).is_some_and(|l| l.line == line))
        .unwrap()
}

#[test]
fn the_checkers_refuse_what_dce_may_not_do() {
    let ev = Evidence::new("dce_adversarial");
    let mut m = fir::parse_module(KEPT).unwrap();
    fir::verify_module(&m).unwrap();
    let body = &m.funcs[0].body;
    let pol = Policy::VerifiedOnly;
    // The pass deletes only the unread pure op; %y and %z are read.
    let plan = dce::plan(body, pol);
    assert_eq!(plan.erase, vec![op_at(&m, 10)]);
    assert!(dce::check(&mut m.funcs[0].body, plan, pol).is_ok());
    let lean = common::reference();
    let mut refused = 0;
    // Unread ops the contracts keep: the Rust checker cites the contract, the Lean checker
    // refuses the module without them.
    for (line, what) in [
        (3, "int.add.s.trap"),
        (4, "freeze"),
        (5, "mem.load"),
        (6, "mem.store"),
        (7, "ptr.addr"),
        (8, "func.call"),
    ] {
        let op = op_at(&m, line);
        let e = dce::check(&mut m.funcs[0].body, Candidate { erase: vec![op] }, pol).unwrap_err();
        assert!(
            e.starts_with(what) && e.contains("the contract doesn't let"),
            "{what}: {e}"
        );
        refused += 1;
        if let Some(tool) = &lean {
            let mut tgt = m.clone();
            tgt.funcs[0].body.erase_many(&[op]);
            fir::verify_module(&tgt).unwrap();
            let e = lean_check(tool, &m, &tgt, &format!("kept-{line}")).unwrap_err();
            assert!(
                e.contains("rejected: not the source with deletable unread ops removed"),
                "{what}: {e}"
            );
            ev.count("refused by Fir.Dce.checkFunc", 1);
        }
    }
    // A read op: the Rust checker names the reader; written out, the module doesn't verify.
    let read = op_at(&m, 9);
    let e = dce::check(&mut m.funcs[0].body, Candidate { erase: vec![read] }, pol).unwrap_err();
    assert!(
        e.contains("reads a result of int.add.wrap @9:3, which is deleted"),
        "{e}"
    );
    refused += 1;
    let mut tgt = m.clone();
    tgt.funcs[0].body.erase_many(&[op_at(&m, 9)]);
    assert!(
        fir::verify_module(&tgt)
            .unwrap_err()
            .contains("is not defined")
    );
    // Malformed candidates.
    let w = op_at(&m, 10);
    assert!(
        dce::check(&mut m.funcs[0].body, Candidate { erase: vec![w, w] }, pol)
            .unwrap_err()
            .contains("twice")
    );
    let mut other = fir::parse_module(KEPT).unwrap();
    other.funcs[0].body.erase_many(&[w]);
    assert!(
        dce::check(&mut other.funcs[0].body, Candidate { erase: vec![w] }, pol)
            .unwrap_err()
            .contains("not in the body")
    );
    refused += 2;
    // An op changed, not deleted: no deletion explains it.
    if let Some(tool) = &lean {
        let changed =
            fir::parse_module(&KEPT.replace("int.mul.wrap %z, %z", "int.add.wrap %z, %z")).unwrap();
        let e = lean_check(tool, &m, &changed, "changed").unwrap_err();
        assert!(e.contains("rejected"), "{e}");
        ev.count("refused by Fir.Dce.checkFunc", 1);
        // And the honest deletion is accepted.
        let mut ok = m.clone();
        ok.funcs[0].body.erase_many(&[w]);
        assert_eq!(lean_check(tool, &m, &ok, "honest").unwrap().functions(), 1);
        ev.count("accepted by Fir.Dce.checkFunc", 1);
    }
    ev.count("refused by the Rust checker", refused);
    ev.write();
}

#[test]
fn lean_receipts_cannot_be_reused_for_other_code_or_context() {
    let m = fir::parse_module(KEPT).unwrap();
    let (_, tgt, _) = run_dce(&m).unwrap();
    let honest = receipt(&m, &tgt);
    assert!(accept_receipt(&m, &tgt, &honest).is_ok());
    let changed =
        fir::parse_module(&KEPT.replace("int.mul.wrap %z, %z", "int.sub.wrap %z, %z")).unwrap();
    let other_context = fir::parse_module(&KEPT.replace("effects[]", "effects[diverge]")).unwrap();
    for (src, out) in [
        (&changed, &tgt),
        (&m, &changed),
        (&other_context, &tgt),
        (&tgt, &m),
    ] {
        assert!(
            accept_receipt(src, out, &honest)
                .unwrap_err()
                .contains("receipt does not match")
        );
    }
    assert!(accept_receipt(&m, &tgt, "ok 1\n").is_err());
    if let Some(tool) = common::reference() {
        let err = lean_check(&tool, &m, &other_context, "changed-context").unwrap_err();
        assert!(
            err.contains("modules differ outside their functions"),
            "{err}"
        );
        let mut other_file = m.clone();
        other_file.funcs[0].file = Some("different.fir".to_owned());
        let err = lean_check(&tool, &m, &other_file, "changed-file").unwrap_err();
        assert!(err.contains("source file changed"), "{err}");
    }
}

/// A `dce` that changes the module but says it changed nothing. It moves the function to
/// another source file, which the verifier allows and the proved checker refuses.
fn lies(m: &mut fir::Module, _: &mut Remarks, _: Policy) -> Result<u32, String> {
    m.funcs[0].file = Some("elsewhere.fir".to_owned());
    Ok(0)
}

static LYING_DCE: fir::passes::Pass = fir::passes::Pass {
    name: "dce",
    summary: "changes the module and reports no changes",
    assurance: fir::passes::Assurance::Experimental("a test of CheckDce"),
    run: fir::passes::PassFn::Module(lies),
};

/// `CheckDce` doesn't take a pass's word that a step changed nothing (found by review: it
/// skipped any step reporting zero changes, so this one went unchecked).
#[test]
fn check_dce_checks_steps_that_report_no_changes_but_change_the_module() {
    let Some(tool) = common::reference() else {
        return;
    };
    let mut m = fir::parse_module(KEPT).unwrap();
    let mut p = Pipeline::parse("dse").unwrap();
    p.passes = vec![&LYING_DCE];
    let mut checker = fir::passes::reference::CheckDce::new(tool, scratch().join("lying-dce"));
    let err = p
        .run_observed(&mut m, &mut Remarks::new(false), &mut checker)
        .unwrap_err();
    assert!(err.rejected, "{err}");
    assert!(err.to_string().contains("source file changed"), "{err}");
    assert_eq!(checker.unchanged, 0);
    // An honest step that changes nothing is still not sent to the checker.
    let mut m = fir::parse_module(KEPT).unwrap();
    let mut p = Pipeline::parse("dce").unwrap();
    p.fixpoint = false;
    let mut checker = fir::passes::reference::CheckDce::new(
        common::reference().unwrap(),
        scratch().join("honest-dce"),
    );
    p.run_observed(&mut m, &mut Remarks::new(false), &mut checker)
        .unwrap();
    p.run_observed(&mut m, &mut Remarks::new(false), &mut checker)
        .unwrap();
    assert_eq!((checker.steps, checker.unchanged), (1, 1));
}

/// Every op of a body, outer before inner, as the pass walks them.
fn all_ops(b: &fir::Body) -> Vec<fir::OpId> {
    let mut out = Vec::new();
    let mut stack = vec![b.ops(b.entry())];
    while let Some(it) = stack.last_mut() {
        match it.next() {
            Some(op) => {
                out.push(op);
                for &r in b.regions(op).iter().rev() {
                    stack.push(b.ops(r));
                }
            }
            None => {
                stack.pop();
            }
        }
    }
    out
}

/// How the Lean side judged one candidate deletion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Accepted,
    /// The deletion leaves a use without its definition: the verifier refuses the module (Rust's
    /// and, when `fir-ref` loads it, Lean's), so the Lean checker never sees it.
    Unverifiable,
    /// `fir-ref check-dce` refused it.
    LeanRefused,
}

/// The production Rust checker (`passes::dce::check`) and the proved Lean one (`Fir.Dce.checkFunc`)
/// must agree on what a deletion may be, not only on the pass's own plans: for each module, random
/// candidates go to both checkers: each kind of unread op the plan leaves (calls, loads,
/// `freeze`, terminators, …) deleted alone, once per function, and random mixes of one to three
/// ops from the plan, from those unread ops, or from any op. A candidate the Rust checker
/// accepts and the proved checker refuses would mean the compiler's checker is weaker than the
/// proved one; one the proved checker accepts and Rust refuses, that Rust is stricter. Neither
/// may occur. This is evidence on the inputs tried, not a proof of correspondence.
#[test]
fn the_rust_and_lean_checkers_agree_on_random_candidates() {
    let ev = Evidence::new("dce_agreement");
    let Some(tool) = common::reference() else {
        ev.skip("no Lean reference");
        ev.write();
        return;
    };
    let count = env_u64("FIR_FUZZ", 200) / 4;
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let mut modules: Vec<(String, fir::Module)> = Vec::new();
    for file in common::fir_files() {
        let text = std::fs::read_to_string(&file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() || matches!(m.layer, fir::Layer::Lfir(_)) {
            continue;
        }
        modules.push((common::display_name(&file).replace(['/', '.'], "_"), m));
    }
    for k in 0..count {
        let mut rng = progs::Rng::new(seed.wrapping_mul(0x2_0000_0003) ^ k);
        let m = fir::parse_module(&progs::program(&mut rng).text).unwrap();
        modules.push((format!("agree-s{seed}-p{k}"), m));
    }
    let tally = Mutex::new(std::collections::BTreeMap::<&'static str, u64>::new());
    let fails = Mutex::new(Vec::new());
    let next = Mutex::new(0usize);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let i = {
                        let mut n = next.lock().unwrap();
                        *n += 1;
                        *n - 1
                    };
                    let Some((name, m)) = modules.get(i) else {
                        return;
                    };
                    let mut src = m.clone();
                    if Pipeline::parse("fwd,copyprop,dse")
                        .unwrap()
                        .run(&mut src, &mut Remarks::new(false))
                        .is_err()
                    {
                        continue;
                    }
                    let mut rng = progs::Rng::new(seed ^ (i as u64).wrapping_mul(0x9e37));
                    let mut cands: Vec<(usize, Vec<fir::OpId>)> = Vec::new();
                    for f in 0..src.funcs.len() {
                        let b = &src.funcs[f].body;
                        let ops = all_ops(b);
                        if ops.is_empty() {
                            continue;
                        }
                        let planned = dce::plan(b, Policy::VerifiedOnly).erase;
                        // Unread ops the plan leaves: deleting one still verifies, so only
                        // a checker can refuse it.
                        let mut read = std::collections::HashSet::new();
                        for &op in &ops {
                            for o in b.operands(op) {
                                if let fir::OperandKind::Value(v) = o.get() {
                                    read.insert(v);
                                }
                            }
                        }
                        let kept: Vec<fir::OpId> = ops
                            .iter()
                            .copied()
                            .filter(|&op| {
                                !planned.contains(&op) && b.results(op).all(|v| !read.contains(&v))
                            })
                            .collect();
                        // One of each kind kept, alone, so rare kinds (an unread `freeze`)
                        // are always tried; then random mixes.
                        let mut kinds = std::collections::HashSet::new();
                        for &op in &kept {
                            if kinds.insert(b.kind(op)) {
                                cands.push((f, vec![op]));
                            }
                        }
                        for _ in 0..4 {
                            let mut erase = Vec::new();
                            for _ in 0..1 + rng.below(3) {
                                let r = rng.below(10);
                                let pool = if !planned.is_empty() && r < 4 {
                                    &planned
                                } else if !kept.is_empty() && r < 8 {
                                    &kept
                                } else {
                                    &ops
                                };
                                let op = pool[rng.below(pool.len() as u64) as usize];
                                if !erase.contains(&op) {
                                    erase.push(op);
                                }
                            }
                            cands.push((f, erase));
                        }
                    }
                    for (c, (f, erase)) in cands.into_iter().enumerate() {
                        let mut body = src.funcs[f].body.clone();
                        let rust_ok = dce::check(
                            &mut body,
                            Candidate {
                                erase: erase.clone(),
                            },
                            Policy::VerifiedOnly,
                        )
                        .is_ok();
                        // A deletion that leaves a read of its result can't be written out
                        // (`erase_many` refuses it in debug builds; the verifier would).
                        let b = &src.funcs[f].body;
                        // Erasing an op erases the ops in its regions too.
                        let mut gone = erase.clone();
                        let mut i = 0;
                        while i < gone.len() {
                            for &r in b.regions(gone[i]) {
                                gone.extend(b.ops(r));
                            }
                            i += 1;
                        }
                        let dangling = all_ops(b).into_iter().any(|op| {
                            !gone.contains(&op)
                                && b.operands(op).iter().any(|o| {
                                    matches!(o.get(), fir::OperandKind::Value(v)
                                        if matches!(b.def(v), fir::ValueDef::Result { op: d, .. }
                                            if gone.contains(&d)))
                                })
                        });
                        let mut tgt = src.clone();
                        if !dangling {
                            tgt.funcs[f].body.erase_many(&erase);
                        }
                        let lean = if dangling || fir::verify_module(&tgt).is_err() {
                            Verdict::Unverifiable
                        } else {
                            match lean_check(&tool, &src, &tgt, &format!("{name}-c{c}")) {
                                Ok(_) => Verdict::Accepted,
                                Err(_) => Verdict::LeanRefused,
                            }
                        };
                        let what = match (rust_ok, lean) {
                            (true, Verdict::Accepted) => "both accepted",
                            (false, Verdict::LeanRefused) => "both refused",
                            (false, Verdict::Unverifiable) => "Rust refused, target doesn't verify",
                            (true, v) => {
                                fails.lock().unwrap().push(format!(
                                    "{name} @{}: Rust accepted {erase:?}, Lean: {v:?}",
                                    src.funcs[f].name
                                ));
                                "Rust accepted, Lean refused"
                            }
                            (false, _) => {
                                fails.lock().unwrap().push(format!(
                                    "{name} @{}: Lean accepted {erase:?}, Rust refused",
                                    src.funcs[f].name
                                ));
                                "Lean accepted, Rust refused"
                            }
                        };
                        *tally.lock().unwrap().entry(what).or_default() += 1;
                    }
                }
            });
        }
    });
    for (what, n) in tally.into_inner().unwrap() {
        eprintln!("dce agreement: {what}: {n}");
        ev.count(what, n);
    }
    ev.write();
    let fails = fails.into_inner().unwrap();
    assert!(
        fails.is_empty(),
        "{} disagreements:\n{}",
        fails.len(),
        fails.join("\n")
    );
}

/// A fixture whose `-O` deletes ops (219 of them, in one step of `dce`).
const DELETES: &str = "tests/abi/classes.fir";

fn fir_compile(file: &Path, flag: Option<&Path>, env: Option<&Path>) -> std::process::Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_fir"));
    cmd.arg("compile").arg(file).args(["-O", "--emit", "mfir"]);
    if let Some(t) = flag {
        cmd.arg("--check-dce").arg(t);
    }
    cmd.env_remove(fir::passes::reference::ENV);
    if let Some(t) = env {
        cmd.env(fir::passes::reference::ENV, t);
    }
    cmd.output().unwrap()
}

/// A stand-in for `fir-ref` that runs `body` as a shell script.
fn fake_fir_ref(name: &str, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let p = scratch().join(name);
    std::fs::write(&p, format!("#!/bin/sh\n{body}\n")).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
    p
}

#[test]
fn the_compiler_runs_the_proved_checker_when_asked() {
    let Some(tool) = common::reference() else {
        return;
    };
    let ev = Evidence::new("dce_compile");
    let file = common::repo().join(DELETES);
    let plain = fir_compile(&file, None, None);
    assert!(plain.status.success());
    assert!(
        plain.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&plain.stderr)
    );
    for (how, out) in [
        ("--check-dce", fir_compile(&file, Some(&tool), None)),
        ("FIR_CHECK_DCE", fir_compile(&file, None, Some(&tool))),
    ] {
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{how}: {err}");
        // The checked compilation produces the same module as the unchecked one.
        assert_eq!(out.stdout, plain.stdout, "{how}");
        let steps: u64 = err
            .strip_prefix("fir: check-dce: ")
            .and_then(|r| r.split(' ').next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("{how}: no summary: {err}"));
        assert!(
            steps > 0 && err.contains("accepted by Fir.Dce.checkModule"),
            "{how}: {err}"
        );
        ev.count(format!("checked compilations ({how})"), 1);
        ev.count("dce steps accepted by Fir.Dce.checkModule", steps);
    }
    // `fir opt -O` honours the variable too.
    let opt = Command::new(env!("CARGO_BIN_EXE_fir"))
        .arg("opt")
        .arg(&file)
        .arg("-O")
        .env(fir::passes::reference::ENV, &tool)
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&opt.stderr);
    assert!(
        opt.status.success() && err.contains("accepted by Fir.Dce.checkModule"),
        "fir opt: {err}"
    );
    // A checker that refuses, or that accepts something else, fails the compilation.
    let refuses = fake_fir_ref("refusing-fir-ref", "echo 'no' >&2; exit 1");
    let other = fake_fir_ref(
        "other-receipt-fir-ref",
        "echo 'ok 1'; echo 'source:'; exit 0",
    );
    for (tool, want) in [(&refuses, "refused it"), (&other, "receipt doesn't match")] {
        for out in [
            fir_compile(&file, Some(tool), None),
            fir_compile(&file, None, Some(tool)),
        ] {
            let err = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success() && err.contains(want),
                "{}: {err}",
                tool.display()
            );
            ev.count("checker objections that failed the compilation", 1);
        }
    }
    // A path that isn't an executable file fails even where nothing would be sent to the
    // checker.
    let text = scratch().join("not-executable-fir-ref");
    std::fs::write(&text, "not a program\n").unwrap();
    let out = fir_compile(
        &common::repo().join("tests/fir1/calls.fir"),
        None,
        Some(&text),
    );
    assert!(
        !out.status.success() && String::from_utf8_lossy(&out.stderr).contains("no executable"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let out = fir_compile(
        &common::repo().join("tests/fir1/calls.fir"),
        None,
        Some(Path::new("/nonexistent/fir-ref")),
    );
    assert!(
        !out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    ev.write();
}

/// Found in review: snapshots were written through whatever was at their path, so a symlink
/// planted there redirected the write. They replace the link instead.
#[test]
fn snapshots_are_not_written_through_symlinks() {
    let Some(tool) = common::reference() else {
        return;
    };
    let dir = scratch().join("symlinked-snapshots");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let victim = dir.join("victim.txt");
    std::fs::write(&victim, "keep me\n").unwrap();
    for end in ["src", "tgt"] {
        std::os::unix::fs::symlink(&victim, dir.join(format!("step.{end}.fir"))).unwrap();
    }
    let m = fir::parse_module(KEPT).unwrap();
    let n = fir::passes::reference::check_dce(&tool, &dir, "step", &m, &m).unwrap();
    assert_eq!(n, m.funcs.len() as u64);
    assert_eq!(std::fs::read_to_string(&victim).unwrap(), "keep me\n");
}
