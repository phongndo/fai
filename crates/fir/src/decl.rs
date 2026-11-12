//! Op declarations, mirroring `spec/Fir/OpDSL.lean`.
//!
//! Every op is declared once, in `spec/Fir/Syntax.lean`. `lake exe gen-rust` writes the Rust
//! side to `generated/ops.rs`: [`OpKind`], its names ([`op_kind`](crate::op_kind),
//! [`OpKind::mnemonic`]), and one [`OpDecl`] per variant ([`OpKind::decl`]). The parser, printer,
//! and verifier interpret the declarations, as the Lean ones do.

use crate::body::{Body, CasesId, IntId, StrId, SuccId};
use crate::ir::{OpKind, Ty};
use crate::ops::TARGETS;

/// What an op's declaration says. The parser, printer, and verifier read `imms`, `items`, and
/// `rule`, and `terminator` through [`OpKind::is_terminator`]; the verifier reads `layers` and
/// `dialect` ([`Layer::allows`]); `effects` and `tier` are declared but not yet read.
#[derive(Debug)]
pub struct OpDecl {
    /// The Lean constructor, such as `memAlloc`.
    pub ctor: &'static str,
    /// The immediates: fields written in the op's format, not its name.
    pub imms: &'static [Field],
    /// The readable form after the op's name. Its location goes before its first region.
    pub items: &'static [Item],
    pub terminator: bool,
    /// How an op without regions is typed; `None` for control flow, which the verifier checks
    /// against the regions around it.
    pub rule: Option<&'static [Check]>,
    pub effects: &'static [Effect],
    pub tier: Tier,
    /// The layers whose modules may contain the op.
    pub layers: Layers,
    /// The op group it belongs to: `int`, `mem`, … (decision: Dialects).
    pub dialect: &'static str,
}

/// The layers an op is allowed in (Lean's `List LayerKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Layers {
    pub hfir: bool,
    pub mfir: bool,
    pub lfir: bool,
}

/// A module's layer (Lean's `Layer`): `layer hfir`, `layer mfir`, or `layer lfir aarch64`. HFIR
/// when the module doesn't say.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Layer {
    #[default]
    Hfir,
    Mfir,
    /// LFIR for a target, one of [`TARGETS`].
    Lfir(&'static str),
}

impl Layer {
    /// The target with this name, from [`TARGETS`].
    pub fn target(name: &str) -> Option<&'static str> {
        TARGETS.iter().copied().find(|t| *t == name)
    }

    /// Whether a module of this layer may contain the op: the op lists the layer, and in LFIR,
    /// an op of a target's dialect belongs to the module's target (Lean's `Layer.allows`).
    #[inline]
    pub fn allows(self, d: &OpDecl) -> bool {
        match self {
            Layer::Hfir => d.layers.hfir,
            Layer::Mfir => d.layers.mfir,
            Layer::Lfir(t) => d.layers.lfir && (d.dialect == t || !TARGETS.contains(&d.dialect)),
        }
    }
}

impl std::fmt::Display for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Layer::Hfir => f.write_str("hfir"),
            Layer::Mfir => f.write_str("mfir"),
            Layer::Lfir(t) => write!(f, "lfir {t}"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Field {
    pub name: &'static str,
    pub ty: FieldTy,
}

/// How an immediate is written and stored.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FieldTy {
    /// An integer, [`Imm::Int`].
    Int,
    /// A size, [`Imm::Nat`].
    Nat,
    /// An alignment, [`Imm::Align`].
    Align,
    /// A field index, [`Imm::Index`].
    Index,
    /// A dotted name such as `c.malloc`, [`Imm::Str`].
    Symbol,
    /// A function, `@f`, [`Imm::Str`].
    Func,
    /// A global, `@g`, [`Imm::Str`].
    Global,
    Ty,
    /// A keyword named after the field (`true` or `false` in the generic form), [`Imm::Flag`].
    Flag,
    /// A branch target, `^b(%x, …)`, [`Imm::Succ`]. Its arguments are among the op's operands;
    /// the generic form writes it as `^b(1)`.
    Succ,
    /// `cf.switch`'s cases, `[k: ^b(…), …]`, [`Imm::Cases`].
    Cases,
    /// A target register, `x3` or `v12`, [`Imm::Reg`].
    Reg,
}

/// An immediate's value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Imm {
    Int(IntId),
    Nat(u64),
    Align(u32),
    Index(u32),
    Str(StrId),
    Ty(Ty),
    Flag(bool),
    Succ(SuccId),
    Cases(CasesId),
    Reg(crate::ir::Reg),
}

/// One piece of an op's readable format (Lean's `Item`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Item {
    /// The immediate with this index in [`OpDecl::imms`].
    Imm(u8),
    Operand,
    Comma,
    Keyword(&'static str),
    /// Zero or more operands.
    Variadic,
    /// `(%a, %b)`
    Args,
    /// A loop's optional `iter(%x: T = %init, …)`: its operands, and the first region's
    /// parameters.
    Iter,
    /// A region; one introduced by a keyword is left out when empty.
    Region(Option<&'static str>),
    /// `cf.blocks`'s labeled blocks, `{ ^a: … ^b(%x: T): … }`: any number of regions.
    Blocks,
}

/// A type in a rule (Lean's `TyE`), with names resolved: the types named by earlier checks are
/// numbered in order, and `Field` is an immediate of type `Ty`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyE {
    Ptr,
    /// The address-sized integer.
    Addr,
    Slice,
    Int(u32),
    Var(u8),
    Field(u8),
}

/// One check of an op's typing rule (Lean's `Check`). Field numbers index [`OpDecl::imms`].
#[derive(Clone, Copy, Debug)]
pub enum Check {
    /// Name the operand types (the next variables), or fail with the message.
    TakeIns(u8, &'static str),
    /// Name the result types, or fail with the message.
    TakeOuts(u8, &'static str),
    /// The operand types are these; the label starts the message.
    Ins(&'static str, &'static [TyE]),
    Outs(&'static [TyE]),
    NoOuts,
    Same(&'static str, &'static [TyE], &'static [TyE]),
    Ints(&'static [TyE]),
    Pow2(u8),
    /// The integer fits in the type, signed or unsigned.
    Fits(u8, TyE),
    /// The second type is wider than the first.
    Widens(TyE, TyE),
    /// The second type is narrower than the first.
    Narrows(TyE, TyE),
    /// Memory holds the type in whole bytes; the verb is for the message.
    Loadable(TyE, &'static str),
    /// Fail with the message on these op names.
    Deny(&'static [&'static str], &'static str),
    /// The operands and results match the function's signature.
    Call(u8),
    /// The type has a layout.
    Sized(TyE),
    /// The type is a struct with the field the immediate names.
    Field(TyE, u8),
    /// The immediate is a function type; the operands are a pointer and its parameters, and the
    /// results its results.
    Sig(u8),
    /// The global exists.
    Global(u8),
    /// The function exists.
    Func(u8),
    /// The type is a struct or an array, and the operands are its fields or elements.
    Parts(TyE),
    /// The first type is a struct or an array whose part (the immediate) has the second type.
    Part(TyE, u8, TyE),
    /// The first type is a union whose variant (the immediate) has the second type.
    Variant(TyE, u8, TyE),
    /// The type is a union.
    Union(TyE),
    /// The type is a scalar value type.
    Scalar(TyE),
}

/// Effect categories (decision: Effects); resource tags come later.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Effect {
    Read,
    Write,
    Alloc,
    Free,
    Trap,
    Diverge,
    Unwind,
    Sync,
    Extern,
}

/// How far an op's declared effects are trusted (decision: Effect soundness).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tier {
    Verified,
    Specified,
    Opaque,
}

impl OpDecl {
    /// The layers that allow the op, for messages: `hfir, mfir`, or `lfir aarch64` for a
    /// target's op (Lean's `OpDecl.layersText`).
    pub fn layers_text(&self) -> String {
        let mut out = Vec::new();
        if self.layers.hfir {
            out.push("hfir".to_owned());
        }
        if self.layers.mfir {
            out.push("mfir".to_owned());
        }
        if self.layers.lfir {
            out.push(if TARGETS.contains(&self.dialect) {
                format!("lfir {}", self.dialect)
            } else {
                "lfir".to_owned()
            });
        }
        out.join(", ")
    }

    /// The items before the first region.
    pub fn head(&self) -> &'static [Item] {
        let n = self
            .items
            .iter()
            .position(|i| matches!(i, Item::Region(_) | Item::Blocks))
            .unwrap_or(self.items.len());
        &self.items[..n]
    }

    /// Whether the op's regions are labeled blocks (`cf.blocks`). `blocks` is always the last
    /// item.
    pub fn has_blocks(&self) -> bool {
        self.items.last() == Some(&Item::Blocks)
    }

    /// The regions, each with the keyword that introduces it, if any.
    pub fn regions(&self) -> impl Iterator<Item = Option<&'static str>> + use<> {
        self.items.iter().filter_map(|i| match i {
            Item::Region(kw) => Some(*kw),
            _ => None,
        })
    }

    /// Whether the readable form can show an op with `operands` operands, `succ_args()` of
    /// them its branch targets' arguments, and regions with these parameter counts and labels:
    /// as many operands as the format holds, and the regions it lists, unlabeled and with
    /// parameters only where `%iter` gives them or after a keyword; or, for `cf.blocks`, regions that all have
    /// labels. Otherwise the op prints in the generic form (Lean's `OpDecl.fits`).
    #[inline]
    pub fn fits(
        &self,
        operands: usize,
        succ_args: impl FnOnce() -> usize,
        mut regions: impl ExactSizeIterator<Item = (usize, bool)>,
    ) -> bool {
        let (mut fixed, mut any, mut iter, mut n_regions, mut blocks) = (0, false, false, 0, false);
        let mut targets = false;
        // Which regions are introduced by a keyword: those may have parameters.
        let mut keyword_regions = 0u64;
        for item in self.items {
            match item {
                Item::Operand => fixed += 1,
                Item::Imm(i) => {
                    targets |= matches!(
                        self.imms[usize::from(*i)].ty,
                        FieldTy::Succ | FieldTy::Cases
                    );
                }
                Item::Variadic | Item::Args => any = true,
                Item::Iter => iter = true,
                Item::Region(kw) => {
                    if kw.is_some() && n_regions < 64 {
                        keyword_regions |= 1 << n_regions;
                    }
                    n_regions += 1;
                }
                Item::Blocks => blocks = true,
                _ => {}
            }
        }
        let mut first = None;
        if blocks {
            if !regions.all(|(_, labeled)| labeled) {
                return false;
            }
        } else {
            if regions.len() != n_regions {
                return false;
            }
            for (i, (n, labeled)) in regions.enumerate() {
                if i == 0 {
                    first = Some(n);
                }
                let keyword = i < 64 && keyword_regions & (1 << i) != 0;
                if labeled || (n != 0 && !(iter && i == 0) && !keyword) {
                    return false;
                }
            }
        }
        if any {
            true
        } else if iter {
            first == Some(operands)
        } else {
            operands == fixed + if targets { succ_args() } else { 0 }
        }
    }
}

impl OpKind {
    /// The op's name with its modifiers, as written in text.
    pub fn name(&self) -> String {
        self.mnemonic().to_owned()
    }

    /// Append the op's name with its modifiers.
    pub fn write_name(&self, out: &mut String) {
        out.push_str(self.mnemonic());
    }

    /// How many of the op's operands are its branch targets' arguments (Lean's
    /// `OpKind.succArgs`).
    pub fn succ_args(&self, body: &Body) -> usize {
        let mut n = 0;
        for (i, f) in self.decl().imms.iter().enumerate() {
            match (f.ty, self.imm(i)) {
                (FieldTy::Succ, Some(Imm::Succ(s))) => n += body.succ(s).nargs as usize,
                (FieldTy::Cases, Some(Imm::Cases(c))) => {
                    n += body
                        .cases(c)
                        .iter()
                        .map(|c| c.succ.nargs as usize)
                        .sum::<usize>();
                }
                _ => {}
            }
        }
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::body::IntId;

    /// No target has ops yet, so the target rule is checked on a made-up AArch64 op, as in
    /// `spec/Fir/Syntax.lean`.
    static AARCH64_OP: OpDecl = OpDecl {
        ctor: "nop",
        imms: &[],
        items: &[],
        terminator: false,
        rule: None,
        effects: &[],
        tier: Tier::Verified,
        layers: Layers {
            hfir: false,
            mfir: false,
            lfir: true,
        },
        dialect: "aarch64",
    };

    #[test]
    fn lfir_allows_its_target_and_func_ret() {
        let aarch64 = Layer::Lfir(Layer::target("aarch64").unwrap());
        assert!(aarch64.allows(&AARCH64_OP));
        assert!(!Layer::Lfir("x86").allows(&AARCH64_OP));
        assert!(!Layer::Mfir.allows(&AARCH64_OP) && !Layer::Hfir.allows(&AARCH64_OP));
        assert_eq!(AARCH64_OP.layers_text(), "lfir aarch64");
        assert!(aarch64.allows(OpKind::Ret.decl()));
        assert!(!aarch64.allows(OpKind::Const(IntId::PLACEHOLDER).decl()));
        assert_eq!(Layer::target("x86"), None);
    }
}
