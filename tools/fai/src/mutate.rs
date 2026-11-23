//! `fai mutate [NAME…]`: adversarial checks of the checkers themselves.
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
//! `fai mutate --quick [NAME…]` measures the quick tier instead: each defect is planted the same
//! way, and `fai verify quick` runs in place of the narrow command. It reports how many of the
//! defects quick catches (and writes `target/mutate/quick.json`); a miss is a finding, not a
//! failure, since quick leaves tests out on purpose.
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
            "lake build gen-rust gen-builder && lake exe gen-rust > ../compiler/ir/src/generated/ops.rs && lake exe gen-rust contracts > ../compiler/ir/src/generated/contracts.rs && lake exe gen-builder rust > ../compiler/ir/src/generated/builder.rs && lake exe gen-builder capi > ../sdk/c/src/generated/ops.rs",
        ],
    )
}

/// The gate's verdict on made-up measurements (`projbench.py gate --self-test`).
fn gate_self_test() -> Cmd {
    cmd(
        "uv",
        &[
            "run",
            "--locked",
            "benchmarks/projects/projbench.py",
            "gate",
            "--self-test",
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
                "compiler/ir/src/generated/contracts.rs",
                "name: \"int.add.s.trap\", calls: false, dce: Dce::Keep }",
                "name: \"int.add.s.trap\", calls: false, dce: Dce::Delete(Evidence::Proved(DCE_THEOREM)) }",
            )],
            steps: vec![test(&["-p", "fir", "--test", "generated"])],
            expect: vec!["compiler/ir/src/generated/contracts.rs is stale"],
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
            // Each component that declares its support is its own crate, and none depends on
            // another's, so with --keep-going every one of them reports the new op.
            steps: vec![
                regen_ops(),
                cmd("cargo", &["build", "--keep-going", "-p", "fir"]),
            ],
            expect: vec![
                "OpKind::Popcount` not covered",
                "--> compiler/lowering/src/lib.rs:",
                "--> compiler/interp/src/lib.rs:",
                "--> targets/aarch64/src/isel.rs:",
                "--> targets/x86_64/src/isel.rs:",
                "could not compile `fai-lowering` (lib) due to 1 previous error",
                "could not compile `fai-interp` (lib) due to 1 previous error",
                "could not compile `fai-target-aarch64` (lib) due to 1 previous error",
                "could not compile `fai-target-x86_64` (lib) due to 1 previous error",
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
                    "rm -rf ../ev && cp -r ../../verify/evidence/debug ../ev && rm ../ev/aarch64_fuzz.json && sed -i 's/\"skipped\": \\[\\]/\"skipped\": [\"no qemu\"]/' ../ev/capi_e2e.json && sed -i 's/\"programs\": 200/\"programs\": 3/' ../ev/interp_fuzz.json && cargo run -q -p fai-tools --bin fai -- evidence ../ev",
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
                "compiler/transforms/src/dce.rs",
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
                "compiler/transforms/src/dce.rs",
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
            name: "dce-apply-deletes-more",
            what: "applying an approved deletion also erases every store (which verifies, and no candidate check sees); the output check, run on every compilation, refuses the result",
            edits: vec![edit(
                "compiler/transforms/src/dce.rs",
                "    body.erase_many(&a.erase);\n    a.erase.len() as u32",
                "    let mut erase = a.erase.clone();\n    let mut all = Vec::new();\n    walk(body, &mut all);\n    erase.extend(all.into_iter().filter(|&o| body.kind(o).mnemonic() == \"mem.store\"));\n    body.erase_many(&erase);\n    a.erase.len() as u32",
            )],
            steps: vec![test(&["-p", "fai-transforms", "--lib", "dce::tests"])],
            expect: vec![
                "its output failed the output check",
                "mem.store @3:3 is missing from the target, and may not be deleted",
            ],
            in_decl: None,
        },
        Mutation {
            name: "dce-output-check-weaker-than-proved",
            what: "the compiler's DCE output check lets `freeze` go; the agreement test gives it targets the proved checker refuses",
            edits: vec![edit(
                "compiler/transforms/src/dce.rs",
                "        if !pure_kind(k, self.policy) {",
                "        if !pure_kind(k, self.policy) && k.mnemonic() != \"freeze\" {",
            )],
            steps: vec![test(&[
                "-p",
                "fir",
                "--test",
                "dce_check",
                "the_rust_and_lean_checkers_agree",
            ])],
            expect: vec!["disagreements", "the output check accepted, Lean refused"],
            in_decl: None,
        },
        Mutation {
            name: "compiler-ignores-check-dce",
            what: "the compiler's -O path ignores FIR_CHECK_DCE, so `fcc -O --check-dce` and the C API would check nothing; the compile-path test finds no checker summary",
            edits: vec![edit(
                "compiler/driver/src/lib.rs",
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
                    "compiler/transforms/src/dce.rs",
                    "        is_pure(body, op, policy) && body.results(op).all(|v| uses[v.index()] == 0)",
                    "        body.regions(op).is_empty()\n            && !body.kind(op).is_terminator()\n            && !body.kind(op).contract().calls\n            && body.results(op).next().is_some()\n            && body.results(op).all(|v| uses[v.index()] == 0)",
                ),
                edit(
                    "compiler/transforms/src/dce.rs",
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
                "targets/aarch64/src/regalloc.rs",
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
                "targets/aarch64/src/regalloc.rs",
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
                "targets/aarch64/src/emit.rs",
                "AluOp::Add => \"add\",",
                "AluOp::Add => \"sub\",",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            expect: vec!["native\n  want", "differences"],
            in_decl: None,
        },
        Mutation {
            name: "x86-64-corrupted-allocation",
            what: "the x86-64 allocator puts every value in rbx; its assignment check refuses it",
            edits: vec![edit(
                "targets/x86_64/src/regalloc.rs",
                "        if let Some(r) = pick {\n            homes[v] = Home::Reg(r);",
                "        if let Some(r) = pick {\n            homes[v] = Home::Reg(3);",
            )],
            steps: vec![test(&["-p", "fir", "--test", "x86_64", "fixtures"])],
            expect: vec!["register allocation is invalid", "differences"],
            in_decl: None,
        },
        Mutation {
            name: "x86-64-bad-output-code",
            what: "the x86-64 emitter prints `subq` for every `addq`; the native comparison refuses it",
            edits: vec![edit(
                "targets/x86_64/src/emit.rs",
                "AluOp::Add => \"addq\",",
                "AluOp::Add => \"subq\",",
            )],
            steps: vec![test(&["-p", "fir", "--test", "x86_64", "fixtures"])],
            expect: vec!["native\n  want", "differences"],
            in_decl: None,
        },
        Mutation {
            name: "miscompile-next-to-an-address",
            what: "multiplication by a constant miscompiled; a fixture that observes an unrelated address must still fail (the previous rule excused it)",
            edits: vec![edit(
                "targets/aarch64/src/emit.rs",
                "AluOp::Mul => \"mul\",",
                "AluOp::Mul => \"add\",",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            expect: vec!["tests_aarch64_address-unrelated_fir @f", "differences"],
            in_decl: None,
        },
        Mutation {
            name: "experiment-rejects-a-miscompile",
            what: "store-to-load forwarding ignores the pointer, so a load through another pointer gets the stored value; `fai experiment` must reject the change from its measurements alone",
            edits: vec![edit(
                "compiler/transforms/src/fwd.rs",
                "|| lp != p || body.ty(r) != ty",
                "|| body.ty(r) != ty",
            )],
            steps: vec![cmd(
                "cargo",
                &["fai", "experiment", "mutate-fwd", "--gate", "none"],
            )],
            expect: vec![
                "REJECTED",
                "doesn't refine the source's",
                "tests/fir1/noalias.fir",
            ],
            in_decl: None,
        },
        Mutation {
            name: "gate-tolerance-widened",
            what: "the gate calls a count the same when it is within 5% (it was one part in 100,000), so a 1% slowdown would pass; the gate's self-test refuses it",
            edits: vec![edit(
                "benchmarks/projects/projbench.py",
                "GATE_SAME = 1e-5",
                "GATE_SAME = 5e-2",
            )],
            steps: vec![gate_self_test()],
            expect: vec![
                "gate self-test: FAILED",
                "1% more instructions on one workload fails",
            ],
            in_decl: None,
        },
        Mutation {
            name: "gate-passes-a-partial-build",
            what: "a build with files compiled another way (`--plain`), which were not judged, gets PASS; the gate's self-test refuses it",
            edits: vec![edit(
                "benchmarks/projects/projbench.py",
                "        report[\"verdict\"] = \"PARTIAL\"\n",
                "        report[\"verdict\"] = \"PASS\"\n",
            )],
            steps: vec![gate_self_test()],
            expect: vec![
                "gate self-test: FAILED",
                "a partial build that is otherwise fine is PARTIAL",
            ],
            in_decl: None,
        },
        Mutation {
            name: "gate-baseline-moves-up",
            what: "`gate --update` writes whatever it measured, so a count inside the tolerance creeps up run by run; the gate's self-test refuses it",
            edits: vec![edit(
                "benchmarks/projects/projbench.py",
                "new[\"instructions\"][w] = n if n < b * (1 - GATE_SAME) else b",
                "new[\"instructions\"][w] = n",
            )],
            steps: vec![gate_self_test()],
            expect: vec!["gate self-test: FAILED", "the baseline only moves down"],
            in_decl: None,
        },
        Mutation {
            name: "validator-budget-removed",
            what: "the allocation validator never checks its budget, so it runs for as long as an input takes (minutes and gigabytes on the promotion passes' output); its test refuses a validation over budget that isn't refused",
            edits: vec![edit(
                "targets/aarch64/src/regcheck.rs",
                "        if state::work() > limit {",
                "        if state::work() > limit && limit == 0 {",
            )],
            steps: vec![test(&["-p", "fir", "--test", "regcheck", "budget"])],
            expect: vec![
                "a_validation_over_its_budget_is_refused",
                "one unit of work can't validate a function",
            ],
            in_decl: None,
        },
        Mutation {
            name: "accept-ignores-the-gate",
            what: "`fai accept` fails only when verification failed too, so a change that the gate refuses is accepted; the verdict's unit test refuses it",
            edits: vec![edit(
                "tools/fai/src/accept.rs",
                "    if gated == Gated::Fail {",
                "    if gated == Gated::Fail && verified == Verified::Failed {",
            )],
            steps: vec![test(&["-p", "fai-tools", "the_four_verdicts"])],
            expect: vec!["the_four_verdicts_and_their_order", "Full Fail"],
            in_decl: None,
        },
        Mutation {
            name: "lazy-value-reused-across-blocks",
            what: "selection reuses a lazy value's register in a block other than the one that built it, so a path that never ran the first block reads a register nothing wrote; the fixtures' code must not run as the source does",
            edits: vec![edit(
                "targets/aarch64/src/isel.rs",
                "            && b == self.cur\n",
                "            && (b == self.cur || b != self.cur)\n",
            )],
            steps: vec![test(&["-p", "fir", "--test", "aarch64", "fixtures"])],
            // In two fixtures the allocator's own check of its assignment sees the read of a
            // register that no path wrote.
            expect: vec![
                "differences:",
                "not compiled: register allocation of function",
            ],
            in_decl: None,
        },
        Mutation {
            name: "slower-code",
            what: "selection forgets what it knows of a register's high bits, so it extends again what is already extended: the same behavior in more instructions; the gate, run for real on Lua and SQLite, refuses it",
            edits: vec![edit(
                "targets/aarch64/src/isel.rs",
                "        if !self.cx.eager && r.is_virtual() && !r.is_fp() && (1..64).contains(&width) {",
                "        if self.cx.eager && r.is_virtual() && !r.is_fp() && (1..64).contains(&width) {",
            )],
            // One command, so that the run on the unchanged copy does the same: the copy
            // shares the sources the tree fetched, if it has (the gate fetches them
            // otherwise), and then the gate runs.
            steps: vec![cmd(
                "sh",
                &[
                    "-c",
                    "mkdir -p target/projbench && if [ -d \"$FAI_MUTATE_FROM/target/projbench/src\" ] && [ ! -e target/projbench/src ]; then ln -s \"$FAI_MUTATE_FROM/target/projbench/src\" target/projbench/src; fi; exec cargo fai gate",
                ],
            )],
            expect: vec!["WORSE   instructions: lua-", "gate: FAIL"],
            in_decl: None,
        },
        Mutation {
            name: "struct-parameter-lowered-apart",
            what: "the lowering takes a struct parameter apart in the signature, where calls pass it whole, in Lean and in Rust alike, so the two print the same text; where the function has a caller in its module the lowering's output no longer verifies, and where it has none (tests/blocks/lone-composite-parameters.fir) only running it on its arguments' encoding shows that it doesn't take them",
            edits: vec![
                edit(
                    "spec/Fir/Lower.lean",
                    "    if p.ty.isComposite then\n      let (o, _) ← extractWhole",
                    "    if p.ty.isComposite && ps.isEmpty then\n      let (o, _) ← extractWhole",
                ),
                edit(
                    "compiler/lowering/src/lib.rs",
                    "        if src.types().is_composite(src.ty(v)) {",
                    "        if src.types().is_composite(src.ty(v)) && params.is_empty() {",
                ),
                edit(
                    "compiler/lowering/src/lib.rs",
                    "        if src.types().is_composite(src.ty(v)) {",
                    "        if src.types().is_composite(src.ty(v)) && params.is_empty() {",
                ),
            ],
            steps: vec![lake_build(), test(&["-p", "fir", "--test", "lower"])],
            expect: vec![
                // A function with a caller: the verifier sees it.
                "arguments of @swap: expected (i8, i32) but got (struct<C>{i8, i32})",
                // A function without one: the comparison on generated arguments sees it.
                "@fields is lowered to 2 parameters, and its arguments' encoding has 1 values",
            ],
            in_decl: None,
        },
        Mutation {
            name: "judging-list-drops-the-tests",
            what: "the judging list stops counting files under a `tests` directory, so an edited fixture would go unnamed; the list's own unit test refuses it (it needs no git, which this copy doesn't have)",
            edits: vec![edit(
                "tools/fai/src/judging.rs",
                "dirs.split('/').any(|c| c == \"tests\").then_some(Kind::Test)",
                "dirs.split('/').any(|c| c == \"no tests\").then_some(Kind::Test)",
            )],
            steps: vec![test(&["-p", "fai-tools", "judging"])],
            expect: vec!["tests/rust/regcheck.rs", "panicked"],
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
    // The tree this is a copy of (`target/mutate/tree` in it), for what a command may share
    // with it and can't change: the gate's fetched sources.
    if let Some(from) = tree.ancestors().nth(3) {
        p.env("FAI_MUTATE_FROM", from);
    }
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
    // `--quick`: measure the quick tier. Each defect is planted as usual, and then
    // `fai verify quick` runs in place of the command that is known to catch it. Nothing is
    // required of the result: the count of defects quick catches is what its verdict is worth.
    let quick = names.iter().any(|n| n == "--quick");
    let names: Vec<String> = names.iter().filter(|n| *n != "--quick").cloned().collect();
    let names = &names[..];
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
    // The tree these results are of (`fai status`).
    let judged = crate::judging::tree_hash(root).unwrap_or_default();
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
        let quick_cmd = cmd("cargo", &["fai", "verify", "quick"]);
        let last = if quick {
            &quick_cmd
        } else {
            m.steps.last().unwrap()
        };
        let key = format!("{} {} {:?}", last.prog, last.args.join(" "), last.env);
        let baseline_ok = *baselines.entry(key.clone()).or_insert_with(|| {
            if m.name == "evidence-suite-missing" {
                // Its baseline is the real evidence, which `fai verify` checks.
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
                let is_last = i + 1 == m.steps.len();
                let step = if is_last { last } else { step };
                let (ok, out) = run(step, &tree, &target);
                output = out;
                if !is_last && !ok {
                    problem = Some(format!("setup step {} failed: {}", i + 1, tail(&output)));
                    break;
                }
                if is_last {
                    caught = !ok;
                    // The quick tier is not asked for the diagnostic, only to fail.
                    reason_ok = quick
                        || (m.expect.iter().all(|x| output.contains(x))
                            && m.in_decl
                                .is_none_or(|(f, d)| error_in_decl(&tree, f, d, &output)));
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
        // In a `--quick` run a defect the quick tier misses is a finding, not a failure.
        ok_all &= passed || (quick && baseline_ok && problem.is_none());
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
    let report = json!({
        "tree": judged,
        "subset": !names.is_empty(),
        "mutations": results,
        "all_caught_for_the_intended_reason": ok_all,
    });
    if quick {
        let caught = results
            .iter()
            .filter(|r| r["passed"] == json!(true))
            .count();
        let missed: Vec<&str> = results
            .iter()
            .filter(|r| r["passed"] != json!(true))
            .filter_map(|r| r["name"].as_str())
            .collect();
        std::fs::write(
            base.join("quick.json"),
            serde_json::to_string_pretty(&report).unwrap(),
        )
        .unwrap();
        eprintln!(
            "\nfai verify quick catches {caught} of {} planted defects{}",
            results.len(),
            if missed.is_empty() {
                String::new()
            } else {
                format!("; it misses: {}", missed.join(", "))
            }
        );
        return if ok_all { 0 } else { 1 };
    }
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
        let root = crate::repo_root();
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
