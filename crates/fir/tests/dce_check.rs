//! Dead code elimination, translation-validated by the checker proved in Lean.
//!
//! For every verified fixture and `FIR_FUZZ` (default 200) random programs, and the MFIR their
//! lowering gives: the other passes run first (`fwd,copyprop,dse`, so there are dead copies to
//! delete), then the Rust pass (`plan`, the Rust `check`, `apply`), and `fir-ref check-dce`
//! runs `Fir.Dce.checkFunc` on the module before and after it. `Fir.Dce.checkFunc_sound` says
//! that, conditional on `Decided`, each accepted function refines its source in the fixed source
//! module. The receipt binds this evidence to both complete snapshots; this does not prove
//! refinement when composing the changed functions into a different module.
//!
//! Then the checkers themselves: candidates that delete an op whose result is read, or an unread
//! op the contracts keep (a trapping add, `freeze`, a load, a store, `ptr.addr`, a call), must be
//! refused by the Rust checker for that reason; the same deletions written out as modules must
//! be refused by the Lean checker (or, where the deletion leaves a use without a definition, by
//! the verifier before it); and an op changed rather than deleted must be refused by the Lean
//! checker.

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
