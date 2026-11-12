//! Op declarations, mirroring `spec/Fir/OpDSL.lean`.
//!
//! Every op is declared once, in `spec/Fir/Syntax.lean`. `lake exe gen-rust` writes the Rust
//! side to `generated/ops.rs`: [`OpKind`], its names ([`op_kind`](crate::op_kind),
//! [`OpKind::mnemonic`]), and one [`OpDecl`] per variant ([`OpKind::decl`]). The parser, printer,
//! and verifier interpret the declarations, as the Lean ones do.

use crate::body::{IntId, StrId};
use crate::ir::{OpKind, Ty};

/// What an op's declaration says. The parser, printer, and verifier read `imms`, `items`, and
/// `rule`, and `terminator` through [`OpKind::is_terminator`]; `effects` and `tier` are declared
/// but not yet read.
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
    /// A dotted name such as `c.malloc`, [`Imm::Str`].
    Symbol,
    /// A function, `@f`, [`Imm::Str`].
    Func,
    Ty,
    /// A keyword named after the field (`true` or `false` in the generic form), [`Imm::Flag`].
    Flag,
}

/// An immediate's value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Imm {
    Int(IntId),
    Nat(u64),
    Align(u32),
    Str(StrId),
    Ty(Ty),
    Flag(bool),
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
}

/// A type in a rule (Lean's `TyE`), with names resolved: the types named by earlier checks are
/// numbered in order, and `Field` is an immediate of type `Ty`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyE {
    Ptr,
    /// The address-sized integer.
    Addr,
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
    /// The items before the first region.
    pub fn head(&self) -> &'static [Item] {
        let n = self
            .items
            .iter()
            .position(|i| matches!(i, Item::Region(_)))
            .unwrap_or(self.items.len());
        &self.items[..n]
    }

    /// The regions, each with the keyword that introduces it, if any.
    pub fn regions(&self) -> impl Iterator<Item = Option<&'static str>> + use<> {
        self.items.iter().filter_map(|i| match i {
            Item::Region(kw) => Some(*kw),
            _ => None,
        })
    }

    /// Whether the readable form can show an op with `operands` operands and regions with
    /// `params` parameters each: as many operands as the format holds, and the regions it lists,
    /// with parameters only where `%iter` gives them. Otherwise the op prints in the generic
    /// form (Lean's `OpDecl.fits`).
    pub fn fits(&self, operands: usize, params: impl ExactSizeIterator<Item = usize>) -> bool {
        let (mut fixed, mut any, mut iter, mut regions) = (0, false, false, 0);
        for item in self.items {
            match item {
                Item::Operand => fixed += 1,
                Item::Variadic | Item::Args => any = true,
                Item::Iter => iter = true,
                Item::Region(_) => regions += 1,
                _ => {}
            }
        }
        if params.len() != regions {
            return false;
        }
        let mut first = None;
        for (i, n) in params.enumerate() {
            if i == 0 {
                first = Some(n);
            }
            if n != 0 && !(iter && i == 0) {
                return false;
            }
        }
        if any {
            true
        } else if iter {
            first == Some(operands)
        } else {
            operands == fixed
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
}
