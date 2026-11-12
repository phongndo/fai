//! The op contracts (`fir::contract`), checked against the op declarations and against what
//! each Rust component declares it does with each kind.
//!
//! The contracts are generated from Lean (`lake exe gen-rust contracts`), so this test doesn't
//! compare two hand-written lists: it checks that the generated registry is complete and
//! consistent with the declarations, and that the Rust components' declarations
//! (`interp::support`, `lower_support`, `isel::support`, all matched without wildcards) don't
//! contradict the declarations. Each contradiction is reported with the kind and the rule it
//! breaks; the test fails on any.
//!
//! It also writes the support table to the evidence (see `common::evidence`), so `cargo xtask
//! verify` can match each claimed support against the kinds the differential tests exercised.

#[allow(dead_code)]
mod common;

use fir::contract::{CONTRACTS, Dce, Evidence as Ev, KINDS, Lowering, Policy, Support};
use fir::{OpKind, op_kind};

use common::evidence::Evidence;

/// Every rule a kind breaks.
fn contradictions(k: OpKind) -> Vec<String> {
    let c = k.contract();
    let d = k.decl();
    let name = c.name;
    let mut out = Vec::new();
    let mut bad = |s: String| out.push(format!("{name}: {s}"));
    // The registry: one entry per op name, found from the kind.
    if k.mnemonic() != name {
        bad(format!("the contract is for {}, not {name}", k.mnemonic()));
    }
    // Some names only print (a kind the parser never produces, such as an unsigned division
    // whose overflow edge differs from its zero edge's); one that parses must come back here.
    if let Some(p) = op_kind(name)
        && p.contract().name != name
    {
        bad(format!(
            "the name parses to the contract of {}",
            p.contract().name
        ));
    }
    // Dead code elimination: a deletable kind is a simple op that doesn't call.
    if let Dce::Delete(e) = c.dce {
        if d.terminator || c.calls || d.rule.is_none() {
            bad("deletable, but it ends a block, calls, or is control flow".into());
        }
        if let Ev::Proved(t) = e
            && t != fir::contract::DCE_THEOREM
        {
            bad(format!(
                "its deletion cites {t}, not the classification's theorem"
            ));
        }
    }
    // The lowering: HFIR-only kinds are rewritten, MFIR kinds stay, LFIR kinds are refused.
    let lowering = fir::lower_support(k);
    let hfir_only = d.layers.hfir && !d.layers.mfir;
    match lowering {
        Lowering::Keep if !d.layers.mfir => bad("the lowering keeps it, but it isn't MFIR".into()),
        Lowering::Expand | Lowering::Scalarize | Lowering::LowerExn if !hfir_only => bad(format!(
            "the lowering rewrites it ({lowering:?}), but it isn't HFIR only"
        )),
        Lowering::No(_) if d.layers.hfir => bad("the lowering refuses an HFIR op".into()),
        _ => {}
    }
    if hfir_only && matches!(lowering, Lowering::Keep | Lowering::No(_)) {
        bad("HFIR only, but the lowering doesn't rewrite it".into());
    }
    // Instruction selection: only kinds a module it accepts can contain (MFIR, or the core
    // ops HFIR shares with it).
    let isel = fir::backend::aarch64::isel::support(k);
    if isel.is_yes()
        && !d.layers.mfir
        && !matches!(k, OpKind::PtrField { .. } | OpKind::PtrIndex { .. })
    {
        bad("instruction selection claims it, but it isn't MFIR".into());
    }
    if !isel.is_yes() && d.layers.mfir {
        bad(format!(
            "an MFIR op instruction selection refuses: {isel:?}"
        ));
    }
    // The interpreter runs every op of every layer.
    if let Support::No(why) = fir::interp::support(k) {
        bad(format!("the interpreter refuses it: {why}"));
    }
    out
}

#[test]
fn contracts_agree_with_the_declarations_and_components() {
    let ev = Evidence::new("contracts");
    assert_eq!(KINDS.len(), CONTRACTS.len());
    let mut problems = Vec::new();
    for (i, &k) in KINDS.iter().enumerate() {
        assert!(
            std::ptr::eq(k.contract(), &CONTRACTS[i]),
            "{}: KINDS and CONTRACTS are out of order",
            CONTRACTS[i].name
        );
        problems.extend(contradictions(k));
        let c = k.contract();
        ev.count("kinds", 1);
        match c.dce {
            Dce::Delete(Ev::Proved(_)) => ev.count("dce: delete (proved)", 1),
            Dce::Delete(Ev::Trusted(_)) => ev.count("dce: delete (trusted)", 1),
            Dce::Keep => ev.count("dce: keep", 1),
        }
        for (comp, f) in fir::contract::components() {
            let s = match f(k) {
                Support::Yes => "yes",
                Support::No(_) => "no",
            };
            ev.count(format!("{comp}: {s}"), 1);
            if s == "yes" {
                ev.fact(&format!("support {comp} {}", c.name), "yes");
            }
        }
        ev.count(
            format!("lowering: {:?}", fir::lower_support(k))
                .replace(['(', ')', '"'], " ")
                .trim()
                .to_owned(),
            1,
        );
    }
    ev.write();
    assert!(
        problems.is_empty(),
        "{} contradictions:\n{}",
        problems.len(),
        problems.join("\n")
    );
}

/// The policies: a verified-only pass refuses a trusted permission that the default accepts.
#[test]
fn trusted_permissions_need_the_permissive_policy() {
    let proved = Dce::Delete(Ev::Proved(fir::contract::DCE_THEOREM));
    let trusted = Dce::Delete(Ev::Trusted("no proof yet"));
    assert!(proved.allows(Policy::VerifiedOnly) && proved.allows(Policy::AllowTrusted));
    assert!(!trusted.allows(Policy::VerifiedOnly) && trusted.allows(Policy::AllowTrusted));
    assert!(!Dce::Keep.allows(Policy::AllowTrusted));
}

/// The repository's policy is verified-only: a permission without a proof fails this test
/// (and so `cargo xtask verify`) unless `FIR_ALLOW_TRUSTED=1` says it is accepted on purpose.
#[test]
fn no_trusted_permissions_under_the_verified_only_policy() {
    let trusted: Vec<&str> = CONTRACTS
        .iter()
        .filter(|c| matches!(c.dce, Dce::Delete(Ev::Trusted(_))))
        .map(|c| c.name)
        .collect();
    if std::env::var("FIR_ALLOW_TRUSTED").is_ok_and(|s| s == "1") {
        return;
    }
    assert!(
        trusted.is_empty(),
        "trusted permissions under the verified-only policy: {}",
        trusted.join(", ")
    );
}

/// Kinds that differ only in a modifier get their own contracts: the trapping forms stay.
#[test]
fn modifiers_decide() {
    let dce = |s: &str| op_kind(s).unwrap().contract().dce;
    assert!(matches!(dce("int.add.nsw"), Dce::Delete(_)));
    assert_eq!(dce("int.add.s.trap"), Dce::Keep);
    assert!(matches!(dce("int.div.s.ub"), Dce::Delete(_)));
    assert_eq!(dce("int.div.s.trap"), Dce::Keep);
    assert!(matches!(dce("union.get.ub"), Dce::Delete(_)));
    assert_eq!(dce("union.get.trap"), Dce::Keep);
    // Declared without effects, but the oracle and addresses make them impure.
    for s in ["freeze", "ptr.addr", "ptr.with_addr", "func.addr"] {
        assert!(op_kind(s).unwrap().decl().effects.is_empty(), "{s}");
        assert_eq!(dce(s), Dce::Keep, "{s}");
    }
}
