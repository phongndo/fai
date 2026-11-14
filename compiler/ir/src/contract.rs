//! Op contracts: what the Lean proofs let the Rust code do with each op kind, and what each Rust
//! component does with it.
//!
//! **Generated half.** [`OpKind::contract`] and [`KINDS`] are generated from the Lean op
//! declarations and classifications (`lake exe gen-rust contracts`, from `Fir.Dce.dcePerm` in
//! `spec/Fir/DceKinds.lean`) into `src/generated/contracts.rs`, one entry per kind an op name
//! spells (modifiers included, immediates not). Its `match` names every variant and modifier
//! without a wildcard, so a kind the Lean name table doesn't spell doesn't compile. Passes read
//! their permissions here instead of keeping their own lists: dead code elimination deletes a
//! kind only if [`Dce::allows`] says so, and copy propagation stops at kinds whose contract says
//! they call. A permission backed by a theorem names it ([`Evidence::Proved`]); one that isn't
//! is [`Evidence::Trusted`], and the [`Policy::VerifiedOnly`] policy refuses it.
//!
//! **Declared half.** Each component that dispatches on op kinds declares what it does with each
//! ([`Support`]) in a function next to its code: `fir::interp::support`, `fir::lower_support`,
//! `fir::backend::aarch64::isel::support`, and `fir::backend::x86_64::isel::support` (the list
//! is `fir::contract::components`). They match every
//! variant without a wildcard (`clippy::wildcard_enum_match_arm` is denied there), so a new op
//! is a compile error until each component decides. `tests/contracts.rs` checks the declarations
//! against the generated contracts and the op declarations (an HFIR-only op the lowering doesn't
//! handle, or one instruction selection claims, is a contradiction), and the differential tests
//! record which kinds they exercised, so `fai verify` can refuse a claimed support that
//! no test runs.
//!
//! None of this shows that the Rust implementation of an op means what the Lean one does: that
//! is what the differential tests against `fir-ref` and the proved checkers are for. A contract
//! records which claims are proved, which are tested, and which are only declared.

pub use crate::generated_contracts::{CONTRACTS, DCE_THEOREM, KINDS};
use crate::ir::OpKind;

/// What the Lean side says about one op kind (one op name).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OpContract {
    /// Its position in [`CONTRACTS`] and [`KINDS`], for tables indexed by kind (such as the
    /// interpreter's execution profile).
    pub index: u32,
    /// The op's printed name, modifiers included.
    pub name: &'static str,
    /// Whether it calls a function (Lean's `OpKind.callee?` is `some`).
    pub calls: bool,
    /// What dead code elimination may do with an op of this kind that nothing reads.
    pub dce: Dce,
}

/// Dead code elimination's permission for a kind (Lean's `Fir.Dce.DcePerm`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Dce {
    /// The pass may delete it when nothing reads its results, it has no regions, and its
    /// operands are values (Lean's `Dce.Pure`, with `Dce.Pure.of_kind`).
    Delete(Evidence),
    /// The pass must keep it.
    Keep,
}

/// Why a permission holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Evidence {
    /// A Lean theorem proves it; the name of the theorem.
    Proved(&'static str),
    /// Nothing proves it; why it is believed.
    Trusted(&'static str),
}

/// Which permissions a pass may use.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Policy {
    /// Proved and trusted permissions (trusted ones are reported in the assurance report).
    #[default]
    AllowTrusted,
    /// Proved permissions only.
    VerifiedOnly,
}

impl Dce {
    /// Whether the pass may delete the kind under `policy`.
    pub fn allows(self, policy: Policy) -> bool {
        match (self, policy) {
            (Dce::Delete(Evidence::Proved(_)), _) => true,
            (Dce::Delete(Evidence::Trusted(_)), Policy::AllowTrusted) => true,
            (Dce::Delete(Evidence::Trusted(_)), Policy::VerifiedOnly) | (Dce::Keep, _) => false,
        }
    }
}

/// What a Rust component does with ops of a kind.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Support {
    /// The component handles the kind.
    Yes,
    /// The component rejects the kind, with an error saying why.
    No(&'static str),
}

impl Support {
    pub fn is_yes(self) -> bool {
        self == Support::Yes
    }
}

/// How the HFIR → MFIR lowering treats a kind, and what backs it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lowering {
    /// The op is MFIR too and stays as it is (calls and throws may gain handlers).
    Keep,
    /// The expansion pass rewrites it; `Fir.Lower.Proof.Expand.refines` proves the expansion.
    Expand,
    /// Scalarizing rewrites it (aggregate, union, and slice values): differential tests only.
    Scalarize,
    /// Scalarizing rewrites it, except where it makes or takes apart a struct or array that calls
    /// pass whole, which stays, and which the lowering emits too (`agg.make`, `agg.extract`,
    /// `agg.insert`, which are MFIR ops as well; decision: C ABI for aggregates): differential
    /// tests only.
    ScalarizeOrKeep,
    /// Lowering exceptions rewrites it (`cf.try`): differential tests only.
    LowerExn,
    /// The lowering rejects it (LFIR ops).
    No(&'static str),
}

/// A component's declaration of what it does with each kind.
pub type SupportFn = fn(OpKind) -> Support;
