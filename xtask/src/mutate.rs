//! `cargo xtask mutate [NAME…]`: adversarial checks of the checkers themselves.
//!
//! Each mutation plants one defect a checker exists to catch (a stale generated file, an op the
//! Rust side doesn't handle, an unprovable or contradictory permission, `sorry`, a custom
//! axiom, a changed theorem statement or semantic dependency, a disabled or skipped check, an
//! invalid rewrite, a corrupted register allocation, wrong output code), runs the narrowest
//! command that should catch it, and requires that command to fail *for that reason*: its output
//! must contain the expected diagnostic. A mutation that is caught for another reason (an
//! unrelated compile error, say) counts as a harness failure, as does one that isn't caught.
//! Every command is also run on the unmutated tree first and must pass, so a failure can't be
//! blamed on the environment.
//!
//! The mutations run in a copy of the repository under `target/mutate/tree` (the working tree's
//! tracked files, and Lean's build directory so that only what a mutation touches rebuilds),
//! with its own Cargo target directory. The original tree is never changed. Results go to
//! `target/mutate/report.json` and `report.md`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Instant;

use serde_json::json;

/// A command run in the copy: a program, its arguments, a directory relative to the copy's root,
/// and extra environment.
#[derive(Clone)]
struct Cmd {
    prog: &'static str,
    args: Vec<&'static str>,
    dir: &'static str,
    env: Vec<(&'static str, &'static str)>,
}

fn cmd(prog: &'static str, args: &[&'static str]) -> Cmd {
    Cmd {
        prog,
        args: args.to_vec(),
        dir: "",
        env: Vec::new(),
    }
}

fn in_spec(prog: &'static str, args: &[&'static str]) -> Cmd {
    Cmd {
        dir: "spec",
        ..cmd(prog, args)
    }
}

fn with_env(mut c: Cmd, env: &[(&'static str, &'static str)]) -> Cmd {
    c.env.extend_from_slice(env);
    c
}

/// One edit: in `file`, replace `from` (which must occur) with `to`.
struct Edit {
    file: &'static str,
    from: &'static str,
    to: &'static str,
}

const fn edit(file: &'static str, from: &'static str, to: &'static str) -> Edit {
    Edit { file, from, to }
}

struct Mutation {
    name: &'static str,
    /// What the defect is, and which checker should catch it.
    what: &'static str,
    edits: Vec<Edit>,
    /// Commands run after the edits; the last must fail with every `expect` string in its output
    /// (the earlier ones regenerate files, as a developer would, and must succeed).
    steps: Vec<Cmd>,
    expect: Vec<&'static str>,
    /// For a proof that should break: the file and the line opening the declaration that the
    /// reported error must fall in (up to the next declaration), so a failure elsewhere doesn't
    /// count.
    in_decl: Option<(&'static str, &'static str)>,
}

fn lake_build() -> Cmd {
    in_spec("lake", &["build"])
}

fn audit() -> Cmd {
    in_spec(
        "lake",
        &[
            "exe",
            "fir-audit",
            "--lock",
            "../docs/assurance/proofs.lock.json",
        ],
    )
}

fn regen_ops() -> Cmd {
    in_spec(
        "sh",
        &[
            "-c",
            "lake build gen-rust gen-builder && lake exe gen-rust > ../crates/fir/src/generated/ops.rs && lake exe gen-rust contracts > ../crates/fir/src/generated/contracts.rs && lake exe gen-builder rust > ../crates/fir/src/generated/builder.rs && lake exe gen-builder capi > ../crates/fir-capi/src/generated/ops.rs",
        ],
    )
}

fn test(args: &[&'static str]) -> Cmd {
    let mut a = vec!["test"];
    a.extend_from_slice(args);
    cmd("cargo", &a)
}

fn mutations() -> Vec<Mutation> {
    vec![
        Mutation {
            name: "stale-generated-contract",
            what: "a generated contract edited by hand (a trapping add made deletable); the freshness check refuses it",
            edits: vec![edit(
                "crates/fir/src/generated/contracts.rs",
                "name: \"int.add.s.trap\", calls: false, dce: Dce::Keep }",
                "name: \"int.add.s.trap\", calls: false, dce: Dce::Delete(Evidence::Proved(DCE_THEOREM)) }",
            )],
            steps: vec![test(&["-p", "fir", "--test", "generated"])],
            expect: vec!["crates/fir/src/generated/contracts.rs is stale"],
            in_decl: None,
        },
        Mutation {
            name: "new-op-without-rust-support",
            what: "a new op declared in Lean and regenerated; the Rust components' support declarations no longer match every variant",
            edits: vec![edit(
                "spec/Fir/Syntax.lean",
                "  /-- `int.zext %a`: the result type is the wider type. -/\n",
                "  /-- `int.popcount %x` -/\n  op popcount\n    name \"int.popcount\"\n    format \"%\"\n    rule\n      operands t \"int.popcount takes one operand\"\n      ints t\n      results [t]\n  /-- `int.zext %a`: the result type is the wider type. -/\n",
            )],
            steps: vec![regen_ops(), cmd("cargo", &["build", "-p", "fir"])],
            expect: vec![
                "non-exhaustive patterns: `ops::OpKind::Popcount` not covered",
                "--> crates/fir/src/lower.rs:",
                "--> crates/fir/src/interp.rs:",
                "--> crates/fir/src/backend/aarch64/isel.rs:",
                "could not compile `fir` (lib) due to 3 previous errors",
            ],
            in_decl: None,
        },
        Mutation {
            name: "unprovable-permission",
            what: "DCE's classification made to delete a trapping add (a modifier whose trap is observable); the purity proof fails",
            edits: vec![edit(
                "spec/Fir/DceKinds.lean",
                "  | .arith _ ovf => if ovf.traps then .keep else .delete",
                "  | .arith _ _ => .delete",
            )],
            steps: vec![lake_build()],
            expect: vec!["error: Fir/DceKinds.lean"],
            in_decl: Some(("spec/Fir/DceKinds.lean", "theorem dcePerm_sound")),
        },
        Mutation {
            name: "contradictory-permission",
            what: "a call marked deletable on trust; the contract generator finds the contradiction with the declaration",
            edits: vec![edit(
                "spec/Fir/DceKinds.lean",
                "  | .unionGet trap _ => if trap then .keep else .delete\n",
                "  | .unionGet trap _ => if trap then .keep else .delete\n  | .call _ => .trusted \"calls are cheap\"\n",
            )],
            steps: vec![
                lake_build(),
                in_spec("lake", &["exe", "gen-rust", "contracts"]),
            ],
            expect: vec!["func.call: dead code elimination may delete it, but it calls"],
            in_decl: None,
        },
        Mutation {
            name: "trusted-permission-under-verified-only",
            what: "freeze marked deletable on trust (no proof); the generated contract says Trusted and the verified-only policy refuses it",
            edits: vec![edit(
                "spec/Fir/DceKinds.lean",
                "  | .unionGet trap _ => if trap then .keep else .delete\n",
                "  | .unionGet trap _ => if trap then .keep else .delete\n  | .freeze => .trusted \"believed pure\"\n",
            )],
            steps: vec![regen_ops(), test(&["-p", "fir", "--test", "contracts"])],
            expect: vec!["trusted permissions under the verified-only policy: freeze"],
            in_decl: None,
        },
        Mutation {
            name: "sorry-in-a-proof",
            what: "a lemma proved with sorry (in no claim's proof); the audit's scan of every Fir declaration reports it",
            edits: vec![edit(
                "spec/Fir/Dse.lean",
                "end Fir.Dse\n",
                "theorem unfinished : 1 = 2 := sorry\n\nend Fir.Dse\n",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec!["Fir.Dse.unfinished: uses sorryAx"],
            in_decl: None,
        },
        Mutation {
            name: "sorry-in-a-claim",
            what: "the DCE classification theorem proved by sorry; the audit reports that the claim depends on sorryAx",
            edits: vec![edit(
                "spec/Fir/DceKinds.lean",
                "theorem dcePerm_sound : ∀ k, dcePerm k = .delete → PureKind k := by\n",
                "theorem dcePerm_sound : ∀ k, dcePerm k = .delete → PureKind k := by\n  stop\n",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec!["Fir.Dce.dcePerm_sound: depends on sorryAx"],
            in_decl: None,
        },
        Mutation {
            name: "custom-axiom",
            what: "a claim proved from a new axiom; the audit refuses the axiom and the claim's dependence on it",
            edits: vec![
                edit(
                    "spec/Fir/DceKinds.lean",
                    "/-! ## A declared effect list is not a proof -/",
                    "axiom trust_me : ∀ k, dcePerm k = .delete → PureKind k\n\n/-! ## A declared effect list is not a proof -/",
                ),
                edit(
                    "spec/Fir/DceCheck.lean",
                    "  refine ⟨_, rfl, rfl, Pure.of_kind (dcePerm_sound k hk) ?_, fun r hr => hres r hr⟩",
                    "  refine ⟨_, rfl, rfl, Pure.of_kind (trust_me k hk) ?_, fun r hr => hres r hr⟩",
                ),
            ],
            steps: vec![lake_build(), audit()],
            expect: vec![
                "an axiom declared in a Fir module",
                "Fir.Dce.checkFunc_sound: depends on the unapproved axiom Fir.Dce.trust_me",
            ],
            in_decl: None,
        },
        Mutation {
            name: "changed-assumptions",
            what: "a hypothesis added to the DSE theorem (it still builds); the audit asks for review of the changed statement",
            edits: vec![edit(
                "spec/Fir/Dse.lean",
                "theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)",
                "theorem refines {mod : Module} {tgt src : Func} (_hsmall : src.rets.length < 4) (hparams : tgt.params = src.params)",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec![
                "Fir.Dse.refines: its statement changed",
                "its number of hypotheses changed",
            ],
            in_decl: None,
        },
        Mutation {
            name: "changed-semantic-dependency",
            what: "a definition the claims depend on changed without changing any statement (an interpreter note); the audit asks for review",
            edits: vec![edit(
                "spec/Fir/Interp.lean",
                "  | .func f => s!\"@{f} is a function\"",
                "  | .func f => s!\"@{f} is a function, not data\"",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec![
                "definitions it depends on changed",
                "Fir.deadNote (changed)",
            ],
            in_decl: None,
        },
        Mutation {
            name: "unregistered-theorem",
            what: "a new refinement theorem not registered as a claim; the audit refuses it",
            edits: vec![edit(
                "spec/Fir/DceCheck.lean",
                "end Fir.Dce\n",
                "theorem checkFunc_sound' {mod : Module} {tgt src : Func} (h : checkFunc tgt src = true)\n    (dec : src.Decided mod) : tgt.Refines mod src := checkFunc_sound h dec\n\nend Fir.Dce\n",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec!["Fir.Dce.checkFunc_sound': an assurance theorem that isn't registered"],
            in_decl: None,
        },
        Mutation {
            name: "unregistered-private-theorem",
            what: "a private refinement theorem with a bold assurance headline must not silently escape registration",
            edits: vec![edit(
                "spec/Fir/DceCheck.lean",
                "end Fir.Dce\n",
                "/-- **A private assurance theorem must also be registered.** -/\nprivate theorem review_unregistered_private {mod : Module} {tgt src : Func}\n    (h : checkFunc tgt src = true) (dec : src.Decided mod) : tgt.Refines mod src :=\n  checkFunc_sound h dec\n\nend Fir.Dce\n",
            )],
            steps: vec![lake_build(), audit()],
            expect: vec!["review_unregistered_private: an assurance theorem that isn't registered"],
            in_decl: None,
        },
        Mutation {
            name: "reference-disabled",
            what: "FIR_REF=none with a full run required; the test refuses to skip",
            edits: vec![],
            steps: vec![with_env(
                test(&["-p", "fir", "--test", "run"]),
                &[("FIR_REF", "none"), ("FIR_REQUIRE_FULL", "1")],
            )],
            expect: vec!["FIR_REQUIRE_FULL=1: this check can't be skipped: FIR_REF=none"],
            in_decl: None,
        },
        Mutation {
            name: "native-runner-missing",
            what: "no qemu or cross compiler on PATH with a full run required; the AArch64 test refuses to skip",
            edits: vec![],
            steps: vec![with_env(
                test(&["-p", "fir", "--test", "aarch64", "fixtures"]),
                &[("FIR_CC", "/nonexistent/cc"), ("FIR_REQUIRE_FULL", "1")],
            )],
            expect: vec!["FIR_REQUIRE_FULL=1: this check can't be skipped: native AArch64 runs"],
            in_decl: None,
        },
        Mutation {
            name: "evidence-suite-missing",
            what: "a suite's evidence missing, one skipped, one short of programs; the evidence check refuses them",
            edits: vec![],
            steps: vec![cmd(
                "sh",
                &[
                    "-c",
                    "rm -rf ../ev && cp -r ../../verify/evidence/debug ../ev && rm ../ev/aarch64_fuzz.json && sed -i 's/\"skipped\": \\[\\]/\"skipped\": [\"no qemu\"]/' ../ev/capi_e2e.json && sed -i 's/\"programs\": 200/\"programs\": 3/' ../ev/interp_fuzz.json && cargo run -q -p xtask -- evidence ../ev",
                ],
            )],
            expect: vec![
                "aarch64_fuzz: no evidence",
                "capi_e2e: skipped \"no qemu\"",
                "interp_fuzz: programs is 3, expected 200",
            ],
            in_decl: None,
        },
        Mutation {
            name: "dce-deletes-a-trap",
            what: "the Rust DCE planner deletes ops the contract keeps; its independent checker refuses the candidate",
            edits: vec![edit(
                "crates/fir/src/passes/dce.rs",
                "        is_pure(body, op, policy) && body.results(op).all(|v| uses[v.index()] == 0)",
                "        body.regions(op).is_empty()\n            && !body.kind(op).is_terminator()\n            && !body.kind(op).contract().calls\n            && body.results(op).next().is_some()\n            && body.results(op).all(|v| uses[v.index()] == 0)",
            )],
            steps: vec![test(&["-p", "fir", "--test", "opt", "fixtures"])],
            expect: vec![
                "its checker rejected the change",
                "the contract doesn't let dead code elimination delete it",
            ],
            in_decl: None,
        },
        Mutation {
            name: "dce-checker-weaker-than-proved",
            what: "the Rust DCE checker alone lets `freeze` go (the planner is right, so no pass output shows it); the agreement test's random candidates reach the proved checker, which refuses",
            edits: vec![edit(
                "crates/fir/src/passes/dce.rs",
                "        if !k.contract().dce.allows(policy) {",
                "        if !k.contract().dce.allows(policy) && k.mnemonic() != \"freeze\" {",
            )],
            steps: vec![test(&[
                "-p",
                "fir",
                "--test",
                "dce_check",
                "the_rust_and_lean_checkers_agree",
            ])],
            expect: vec!["disagreements", "Rust accepted", "Lean: LeanRefused"],
            in_decl: None,
        },
        Mutation {
            name: "compiler-ignores-check-dce",
            what: "the compiler's -O path ignores FIR_CHECK_DCE, so `fcc -O --check-dce` and the C API would check nothing; the compile-path test finds no checker summary",
            edits: vec![edit(
                "crates/fir/src/backend/mod.rs",
                "    let Some(mut check) = CheckDce::from_env()? else {",
                "    let Some(mut check) = CheckDce::from_env()?.filter(|_| false) else {",
            )],
            steps: vec![test(&[
                "-p",
                "fir",
                "--test",
                "dce_check",
                "the_compiler_runs_the_proved_checker",
            ])],
            expect: vec!["FIR_CHECK_DCE: no summary"],
            in_decl: None,
        },
        Mutation {
            name: "dce-checker-also-wrong",
            what: "the planner and the Rust checker both wrong (a checker bug); the Lean-proved checker refuses the output",
            edits: vec![
                edit(
                    "crates/fir/src/passes/dce.rs",
                    "        is_pure(body, op, policy) && body.results(op).all(|v| uses[v.index()] == 0)",
                    "        body.regions(op).is_empty()\n            && !body.kind(op).is_terminator()\n            && !body.kind(op).contract().calls\n            && body.results(op).next().is_some()\n            && body.results(op).all(|v| uses[v.index()] == 0)",
                ),
                edit(
                    "crates/fir/src/passes/dce.rs",
                    "        if !k.contract().dce.allows(policy) {",
                    "        if !k.contract().dce.allows(policy) && false {",
                ),
            ],
            steps: vec![test(&["-p", "fir", "--test", "dce_check", "validated"])],
            expect: vec![
                "fir-ref check-dce",
                "rejected: not the source with deletable unread ops removed",
            ],
            in_decl: None,
        },
        Mutation {
            name: "corrupted-allocation",
            what: "the rewriter puts every value assigned x9 in x10 when it is written; the allocation validator refuses the code",
            edits: vec![edit(
                "crates/fir/src/backend/aarch64/regalloc.rs",
                "                match a.homes[r.virt_index() as usize] {\n                    Home::Reg(p) => p,",
                "                match a.homes[r.virt_index() as usize] {\n                    Home::Reg(p) if is_def && p == Reg::x(9) => Reg::x(10),\n                    Home::Reg(p) => p,",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            expect: vec!["failed validation", "not compiled"],
            in_decl: None,
        },
        Mutation {
            name: "spill-store-dropped",
            what: "spill stores dropped from the rewritten code; the allocation validator refuses the reloads",
            edits: vec![edit(
                "crates/fir/src/backend/aarch64/regalloc.rs",
                "            for (t, s) in stores {\n                out.slot_access(false, t, spill_base + 8 * i64::from(s), loc);\n            }",
                "            for (t, s) in stores {\n                let _ = (t, s, loc);\n            }",
            )],
            steps: vec![test(&["-p", "fir", "--test", "regcheck", "honest"])],
            expect: vec!["failed validation", "reads"],
            in_decl: None,
        },
        Mutation {
            name: "bad-output-code",
            what: "the emitter prints `sub` for every three-register `add`; the native comparison refuses it (the validator checks LFIR, not text)",
            edits: vec![edit(
                "crates/fir/src/backend/aarch64/emit.rs",
                "AluOp::Add => \"add\",",
                "AluOp::Add => \"sub\",",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            expect: vec!["native\n  want", "differences"],
            in_decl: None,
        },
        Mutation {
            name: "miscompile-next-to-an-address",
            what: "multiplication by a constant miscompiled; a fixture that observes an unrelated address must still fail (the previous rule excused it)",
            edits: vec![edit(
                "crates/fir/src/backend/aarch64/emit.rs",
                "AluOp::Mul => \"mul\",",
                "AluOp::Mul => \"add\",",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            expect: vec!["tests_aarch64_address-unrelated_fir @f", "differences"],
            in_decl: None,
        },
    ]
}

/// Copy the tracked files of the working tree (as they are now), and Lean's build directory.
fn make_copy(root: &Path, tree: &Path) {
    let _ = std::fs::remove_dir_all(tree);
    std::fs::create_dir_all(tree).unwrap();
    let files = Command::new("git")
        .args(["ls-files", "-z"])
        .current_dir(root)
        .output()
        .unwrap();
    for f in files.stdout.split(|&b| b == 0).filter(|f| !f.is_empty()) {
        let rel = Path::new(std::str::from_utf8(f).unwrap());
        let src = root.join(rel);
        if !src.is_file() {
            continue;
        }
        let dst = tree.join(rel);
        std::fs::create_dir_all(dst.parent().unwrap()).unwrap();
        std::fs::copy(&src, &dst).unwrap();
    }
    let status = Command::new("cp")
        .args(["-a"])
        .arg(root.join("spec/.lake"))
        .arg(tree.join("spec/.lake"))
        .status()
        .unwrap();
    assert!(status.success(), "copying spec/.lake failed");
}

fn run(c: &Cmd, tree: &Path, target: &Path) -> (bool, String) {
    let mut p = Command::new(c.prog);
    p.args(&c.args)
        .current_dir(tree.join(c.dir))
        .env("CARGO_TARGET_DIR", target)
        .stdin(Stdio::null());
    for v in [
        "FIR_REF",
        "FIR_REQUIRE_FULL",
        "FIR_EVIDENCE",
        "FIR_CC",
        "FIR_FUZZ",
    ] {
        p.env_remove(v);
    }
    // Small fuzz counts: these runs look for one planted defect, not for coverage.
    p.env("FIR_FUZZ", "40");
    for (k, v) in &c.env {
        p.env(k, v);
    }
    match p.output() {
        Ok(o) => (
            o.status.success(),
            format!(
                "{}\n{}",
                String::from_utf8_lossy(&o.stdout),
                String::from_utf8_lossy(&o.stderr)
            ),
        ),
        Err(e) => (false, format!("can't run {}: {e}", c.prog)),
    }
}

pub fn main(root: &Path, names: &[String]) -> i32 {
    let base = root.join("target/mutate");
    let tree = base.join("tree");
    let target = base.join("target");
    std::fs::create_dir_all(&base).unwrap();
    let all = mutations();
    let chosen: Vec<&Mutation> = all
        .iter()
        .filter(|m| names.is_empty() || names.iter().any(|n| n == m.name))
        .collect();
    if chosen.is_empty() {
        eprintln!("no such mutation; the mutations are:");
        for m in &all {
            eprintln!("  {}: {}", m.name, m.what);
        }
        return 2;
    }
    eprintln!("copying the tree to {}", tree.display());
    make_copy(root, &tree);
    let pristine: BTreeMap<&str, String> = all
        .iter()
        .flat_map(|m| m.edits.iter().map(|e| e.file))
        .map(|f| (f, std::fs::read_to_string(tree.join(f)).unwrap()))
        .collect();
    // Baselines: every command must pass on the unmutated copy.
    let mut baselines: BTreeMap<String, bool> = BTreeMap::new();
    let mut results = Vec::new();
    let mut ok_all = true;
    for m in chosen {
        let start = Instant::now();
        for e in &m.edits {
            std::fs::write(tree.join(e.file), &pristine[e.file]).unwrap();
        }
        let last = m.steps.last().unwrap();
        let key = format!("{} {} {:?}", last.prog, last.args.join(" "), last.env);
        let baseline_ok = *baselines.entry(key.clone()).or_insert_with(|| {
            if m.name == "evidence-suite-missing" {
                // Its baseline is the real evidence, which `cargo xtask verify` checks.
                return true;
            }
            let control = Cmd {
                env: Vec::new(),
                ..last.clone()
            };
            let (ok, out) = run(&control, &tree, &target);
            if !ok {
                eprintln!("baseline failed for `{key}`:\n{}", tail(&out));
            }
            ok
        });
        // Apply the edits; each anchor must exist.
        let mut problem = None;
        for e in &m.edits {
            let path = tree.join(e.file);
            let text = std::fs::read_to_string(&path).unwrap();
            if !text.contains(e.from) {
                problem = Some(format!("anchor not found in {}: {:?}", e.file, e.from));
                break;
            }
            std::fs::write(&path, text.replacen(e.from, e.to, 1)).unwrap();
        }
        let mut output = String::new();
        let mut caught = false;
        let mut reason_ok = false;
        if problem.is_none() {
            for (i, step) in m.steps.iter().enumerate() {
                let (ok, out) = run(step, &tree, &target);
                output = out;
                if i + 1 < m.steps.len() && !ok {
                    problem = Some(format!("setup step {} failed: {}", i + 1, tail(&output)));
                    break;
                }
                if i + 1 == m.steps.len() {
                    caught = !ok;
                    reason_ok = m.expect.iter().all(|x| output.contains(x))
                        && m.in_decl
                            .is_none_or(|(f, d)| error_in_decl(&tree, f, d, &output));
                }
            }
        }
        // Restore, and rebuild Lean so the next mutation starts clean.
        for e in &m.edits {
            std::fs::write(tree.join(e.file), &pristine[e.file]).unwrap();
        }
        if m.edits.iter().any(|e| e.file.starts_with("spec/")) {
            let _ = run(&regen_ops(), &tree, &target);
        }
        let passed = baseline_ok && problem.is_none() && caught && reason_ok;
        ok_all &= passed;
        let verdict = if !baseline_ok {
            "baseline failed".to_owned()
        } else if let Some(p) = &problem {
            p.clone()
        } else if !caught {
            "NOT CAUGHT: the command passed".to_owned()
        } else if !reason_ok {
            format!("caught for another reason (expected {:?})", m.expect)
        } else {
            "caught for the intended reason".to_owned()
        };
        eprintln!(
            "[{}] {} ({:.0}s): {verdict}",
            if passed { "ok  " } else { "FAIL" },
            m.name,
            start.elapsed().as_secs_f64()
        );
        let evidence: Vec<String> = output
            .lines()
            .filter(|l| {
                m.expect
                    .iter()
                    .any(|x| x.lines().any(|xl| !xl.is_empty() && l.contains(xl)))
            })
            .take(4)
            .map(|l| l.trim().chars().take(240).collect())
            .collect();
        results.push(json!({
            "name": m.name, "what": m.what, "passed": passed, "verdict": verdict,
            "expected": m.expect, "matching_output": evidence,
            "seconds": start.elapsed().as_secs_f64(),
            "output_tail": if passed { String::new() } else { tail(&output) },
        }));
    }
    let report = json!({"mutations": results, "all_caught_for_the_intended_reason": ok_all});
    std::fs::write(
        base.join("report.json"),
        serde_json::to_string_pretty(&report).unwrap(),
    )
    .unwrap();
    let mut md = String::from("| Mutation | Defect | Result | Diagnostic |\n|---|---|---|---|\n");
    for r in &results {
        let diag = r["matching_output"]
            .as_array()
            .and_then(|a| a.first())
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .replace('|', "/");
        writeln!(
            md,
            "| `{}` | {} | {} | `{}` |",
            r["name"].as_str().unwrap(),
            r["what"].as_str().unwrap(),
            r["verdict"].as_str().unwrap(),
            diag
        )
        .unwrap();
    }
    std::fs::write(base.join("report.md"), &md).unwrap();
    eprintln!("\n{}", md);
    if ok_all { 0 } else { 1 }
}

/// Whether some `error: FILE:LINE:` in `out` is inside the declaration of `file` (as mutated)
/// that starts with the line `decl`, up to the next `theorem`, `def`, or `set_option` line.
fn error_in_decl(tree: &Path, file: &str, decl: &str, out: &str) -> bool {
    let Ok(text) = std::fs::read_to_string(tree.join(file)) else {
        return false;
    };
    let lines: Vec<&str> = text.lines().collect();
    let Some(start) = lines.iter().position(|l| l.starts_with(decl)) else {
        return false;
    };
    let end = lines[start + 1..]
        .iter()
        .position(|l| {
            l.starts_with("theorem ") || l.starts_with("def ") || l.starts_with("set_option ")
        })
        .map_or(lines.len(), |k| start + 1 + k);
    let short = file.trim_start_matches("spec/");
    out.lines().any(|l| {
        l.strip_prefix(&format!("error: {short}:"))
            .and_then(|r| r.split(':').next())
            .and_then(|n| n.parse::<usize>().ok())
            .is_some_and(|n| n > start && n <= end)
    })
}

fn tail(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    lines[lines.len().saturating_sub(25)..].join("\n")
}

#[cfg(test)]
mod review_tests {
    use super::*;

    /// Every mutation's anchor is in the current sources, so a mutation can't silently stop
    /// running when code moves (found in review: the generated contracts gained a field).
    #[test]
    fn mutation_anchors_match_current_sources() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let mut missing = Vec::new();
        for mutation in mutations() {
            for edit in mutation.edits {
                let source = std::fs::read_to_string(root.join(edit.file)).unwrap();
                if !source.contains(edit.from) {
                    missing.push(format!("{}: {}: {:?}", mutation.name, edit.file, edit.from));
                }
            }
        }
        assert!(
            missing.is_empty(),
            "stale mutation anchors:\n{}",
            missing.join("\n")
        );
    }
}
