//! The builder API: modules built op by op, with every UB choice spelled out.
//!
//! A [`ModuleBuilder`] holds the module under construction: its memory space, its struct, array,
//! and function types, its globals and external functions, and the functions finished so far.
//! [`ModuleBuilder::func`] starts a function and returns a [`FuncBuilder`], which appends ops at
//! an insertion point and is finished with [`FuncBuilder::finish`]. One function is built at a
//! time; the module's own declarations can still be added meanwhile, through
//! [`FuncBuilder::module`].
//!
//! Each op has a method generated from its declaration in `spec/Fir/Syntax.lean` (see
//! `generated/builder.rs`), named after its dialect and constructor (`int_arith`, `mem_load`,
//! `cf_cond_br`). Its arguments, in order, are the result types the op can't imply, its
//! modifiers (every one required: [`Ovf`], [`Edge`], [`ShiftEdge`], [`TruncMode`], [`Pred`],
//! [`AllocFail`], and `bool`s such as `inbounds`), then its immediates and operands in the order
//! its text writes them. Ops with regions have a `_begin` method that makes the op with empty
//! regions, and a scoped method that builds each region in a closure (`cf_if`, `cf_loop`,
//! `cf_blocks`).
//!
//! ```
//! use fir::{ModuleBuilder, Ovf, Pred, Ty};
//!
//! let mut mb = ModuleBuilder::new();
//! let i32 = Ty::Int(32);
//! // func @sum(%n: i32) -> i32: 0 + 1 + … + (n - 1)
//! let mut f = mb.func("sum", &[i32], &[i32])?;
//! let n = f.param(0);
//! f.name(n, "n");
//! let zero = f.int_const(i32, 0)?;
//! let r = f.cf_loop(&[i32], false, &[zero.into(), zero.into()], |f, st| {
//!     let (i, acc) = (st.get(0), st.get(1));
//!     let done = f.int_cmp(Pred::Sge, i, n)?;
//!     f.cf_if(&[], done, |f| f.cf_break(&[acc.into()]).map(drop), |_| Ok(()))?;
//!     let one = f.int_const(i32, 1)?;
//!     let i2 = f.int_arith(fir::ArithOp::Add, Ovf::Nsw, i, one)?;
//!     let acc2 = f.int_arith(fir::ArithOp::Add, Ovf::Wrap, acc, i)?;
//!     f.cf_continue(&[i2.into(), acc2.into()])?;
//!     Ok(())
//! })?;
//! f.func_ret(&[r.get(0).into()])?;
//! f.finish()?;
//! let m = mb.finish();
//! fir::verify_module(&m).unwrap();
//! assert_eq!(fir::interp::run(&m, "sum", &["5"], 1000).unwrap(), "returned i32 10");
//! # Ok::<(), fir::BuildError>(())
//! ```
//!
//! **Checks.** Building checks what is cheap to check at once: operand counts and types against
//! the op's typing rule, result types the rule implies, alignments, extensions and truncations,
//! calls against the callee's signature, and that every id names something in the function. A
//! failed check returns a [`BuildError`] and adds nothing. Scoping, terminators, branch targets,
//! the layout of types, and everything else the verifier checks are left to
//! [`verify_module`](crate::verify_module), which a built module must pass before it runs.
//!
//! **Storage.** The builder writes straight into the function's [`Body`]: ids, not references,
//! and no heap memory per op. It reuses one body for every function and copies each out exactly
//! sized when it is finished, as the parser does. Struct, array, and function types live in the
//! module's table ([`Globals::types`]); a function's ops name copies in its own table, made the
//! first time the function uses each type.
//!
//! **Names.** Values and region parameters are made without names. [`FuncBuilder::name`] names
//! one; when the function is finished, each value still unnamed is named after its id (`%12`),
//! so names made only of digits are best left to the builder. Blocks of `cf.blocks` are labeled
//! the same way when their label is empty.

use std::fmt;

use num_bigint::BigInt;
use rustc_hash::FxHashMap;

use crate::body::{
    Body, CasesId, IntId, OpId, Operand, OperandKind, RegionId, StrId, Succ, SuccId, ValueId,
    ValueSpec,
};
use crate::decl::{Check, Imm, TyE};
use crate::ir::*;
use crate::types::Shape;

/// Why building failed: an argument that names nothing, a type the op's rule rejects, or a
/// declaration that clashes with another.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BuildError {
    msg: String,
}

impl BuildError {
    pub fn new(msg: impl Into<String>) -> BuildError {
        BuildError { msg: msg.into() }
    }

    pub fn message(&self) -> &str {
        &self.msg
    }
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

impl std::error::Error for BuildError {}

fn err<T>(msg: impl Into<String>) -> Result<T, BuildError> {
    Err(BuildError::new(msg))
}

/// An integer immediate: a constant, a switch key, or a range bound.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum IntImm {
    Small(i64),
    Big(BigInt),
}

macro_rules! int_imm_from {
    ($($t:ty),*) => {$(
        impl From<$t> for IntImm {
            fn from(n: $t) -> IntImm {
                match i64::try_from(n) {
                    Ok(n) => IntImm::Small(n),
                    Err(_) => IntImm::Big(BigInt::from(n)),
                }
            }
        }
    )*};
}

int_imm_from!(
    i8, i16, i32, i64, i128, u8, u16, u32, u64, u128, isize, usize
);

impl From<BigInt> for IntImm {
    fn from(n: BigInt) -> IntImm {
        match i64::try_from(&n) {
            Ok(n) => IntImm::Small(n),
            Err(_) => IntImm::Big(n),
        }
    }
}

/// A function of the module being built, defined in it or external: an index into the
/// builder's functions, in declaration order.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FuncRef(u32);

/// A global of the module being built: its index in [`Globals`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct GlobalRef(u32);

macro_rules! raw_id {
    ($($t:ident),*) => {$(
        impl $t {
            pub fn index(self) -> usize {
                self.0 as usize
            }

            pub fn raw(self) -> u32 {
                self.0
            }

            /// The id a [`raw`](Self::raw) number stands for. Building checks that it exists.
            pub fn from_raw(n: u32) -> $t {
                $t(n)
            }
        }
    )*};
}

raw_id!(FuncRef, GlobalRef);

/// Consecutive values: a region's parameters or an op's results.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Values {
    start: u32,
    len: u32,
}

impl Values {
    fn of(mut vs: impl ExactSizeIterator<Item = ValueId>) -> Values {
        let len = vs.len() as u32;
        let start = vs.next().map_or(0, ValueId::raw);
        Values { start, len }
    }

    /// Value `i`; panics if there are fewer.
    pub fn get(self, i: usize) -> ValueId {
        assert!(i < self.len as usize, "value {i} of {}", self.len);
        ValueId::from_raw(self.start + i as u32)
    }

    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    pub fn iter(self) -> impl ExactSizeIterator<Item = ValueId> {
        (self.start..self.start + self.len).map(ValueId::from_raw)
    }
}

/// An op and its results.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Results {
    pub op: OpId,
    pub values: Values,
}

impl Results {
    /// Result `i`; panics if there are fewer.
    pub fn get(self, i: usize) -> ValueId {
        self.values.get(i)
    }

    pub fn len(self) -> usize {
        self.values.len()
    }

    pub fn is_empty(self) -> bool {
        self.values.is_empty()
    }
}

/// A branch target: a block of the nearest enclosing `cf.blocks` (made with
/// [`FuncBuilder::block`]) and the arguments passed to its parameters.
#[derive(Clone, Copy, Debug)]
pub struct Target<'a> {
    pub block: RegionId,
    pub args: &'a [Operand],
}

impl<'a> Target<'a> {
    pub fn new(block: RegionId, args: &'a [Operand]) -> Target<'a> {
        Target { block, args }
    }
}

/// One case of `cf.switch`.
#[derive(Clone, Debug)]
pub struct SwitchCase<'a> {
    pub key: IntImm,
    pub target: Target<'a>,
}

/// A fact to put on a value (see [`Fact`]), with its integers given directly.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FactArg {
    RangeS(IntImm, IntImm),
    RangeU(IntImm, IntImm),
    NonNull,
    Align(u64),
    NoAlias,
    ReadOnly,
}

/// Where an op's results come from, for [`FuncBuilder::simple`].
pub(crate) enum Res<'a> {
    /// The op has none (control flow).
    None,
    /// The rule gives them (`results [a]`).
    Implied,
    /// The caller gives them (`results t "msg"`).
    Given(&'a [Ty]),
    /// The callee's results.
    Callee(FuncRef),
    /// The results of the function type (already in the body's table).
    Sig(Ty),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SymKind {
    Declared,
    Building,
    Defined,
    Extern,
}

/// A function's name and signature. Its types are value types, so they need no table.
#[derive(Clone, Debug)]
struct Sym {
    name: String,
    params: Vec<Ty>,
    rets: Vec<Ty>,
    kind: SymKind,
}

/// Where the next op goes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InsertPoint {
    /// At the end of a region.
    End(RegionId),
    /// Right before an op.
    Before(OpId),
}

const NONE: u32 = u32::MAX;

/// The function being built. Its arrays are reused from one function to the next.
#[derive(Default)]
struct FuncState {
    func: Option<FuncRef>,
    file: Option<String>,
    body: Body,
    at: Option<InsertPoint>,
    loc: Option<Loc>,
    /// Each module type's copy in the body's table (`NONE` until made), by [`TyId`] index.
    ty_map: Vec<u32>,
    /// Each function's and global's name in the body's strings (`NONE` until stored).
    func_names: Vec<u32>,
    global_names: Vec<u32>,
    /// The blocks made for each `cf.blocks` op not yet given its regions.
    blocks: Vec<(OpId, Vec<RegionId>)>,
    /// Scratch: the operands of the op being built, and types.
    operands: Vec<Operand>,
    tys: Vec<Ty>,
    in_tys: Vec<Ty>,
}

/// Builds a module. See the [module documentation](self).
#[derive(Default)]
pub struct ModuleBuilder {
    module: Module,
    syms: Vec<Sym>,
    by_name: FxHashMap<String, u32>,
    globals_by_name: FxHashMap<String, u32>,
    st: FuncState,
}

/// Bodies with fewer ops than this are copied out of the reused body when finished.
const SMALL_BODY: usize = 1 << 12;

impl ModuleBuilder {
    pub fn new() -> ModuleBuilder {
        ModuleBuilder::default()
    }

    /// Continue building a module, such as a parsed one: its functions, external functions,
    /// and globals can be referred to by name ([`ModuleBuilder::func_ref`],
    /// [`ModuleBuilder::global_ref`]), and new functions are added after its own.
    pub fn from_module(module: Module) -> Result<ModuleBuilder, BuildError> {
        let mut mb = ModuleBuilder::new();
        for i in 0..module.globals.len() {
            mb.globals_by_name
                .insert(module.globals.name(i).to_owned(), i as u32);
        }
        for x in &module.externs {
            mb.add_sym(&x.name, &x.params, &x.rets, SymKind::Extern)?;
        }
        for f in &module.funcs {
            let params: Vec<Ty> = f
                .body
                .params(f.body.entry())
                .map(|v| f.body.ty(v))
                .collect();
            mb.add_sym(&f.name, &params, &f.rets, SymKind::Defined)?;
        }
        mb.module = module;
        Ok(mb)
    }

    /// The module so far: the functions finished, not the one being built.
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The module. A function still being built is dropped.
    pub fn finish(self) -> Module {
        self.module
    }

    /// Set the default memory space's data layout. Set it before building functions: ops whose
    /// types are address-sized read it as they are built.
    pub fn set_space(&mut self, space: SpaceCfg) {
        self.module.space = space;
    }

    /// The table of the module's struct, array, and function types.
    pub fn types(&self) -> &Types {
        &self.module.globals.types
    }

    /// `struct<policy>{fields}`; the fields are types of this builder.
    pub fn struct_ty(&mut self, policy: Policy, fields: &[Ty]) -> Result<Ty, BuildError> {
        self.check_tys(fields)?;
        Ok(self.module.globals.types.structure(policy, fields))
    }

    /// `array<n x elem>`
    pub fn array_ty(&mut self, n: u64, elem: Ty) -> Result<Ty, BuildError> {
        self.check_tys(&[elem])?;
        Ok(self.module.globals.types.array(n, elem))
    }

    /// `func<(params) -> rets>`, for `func.call.indirect`.
    pub fn func_ty(&mut self, params: &[Ty], rets: &[Ty]) -> Result<Ty, BuildError> {
        self.check_tys(params)?;
        self.check_tys(rets)?;
        Ok(self.module.globals.types.func(params, rets))
    }

    /// Every type is a type of this builder.
    fn check_tys(&self, ts: &[Ty]) -> Result<(), BuildError> {
        for &t in ts {
            match t {
                Ty::Agg(id) if id.index() >= self.module.globals.types.len() => {
                    return err(format!("type {} is not a type of this module", id.index()));
                }
                Ty::Int(0) | Ty::Byte(0) => return err("a type's width must be positive"),
                _ => {}
            }
        }
        Ok(())
    }

    fn value_tys(&self, what: &str, name: &str, ts: &[Ty]) -> Result<(), BuildError> {
        self.check_tys(ts)?;
        if let Some(&t) = ts.iter().find(|t| !t.is_value()) {
            return err(format!(
                "{what} @{name}: {} is not a value type",
                self.types().show(t)
            ));
        }
        Ok(())
    }

    fn add_sym(
        &mut self,
        name: &str,
        params: &[Ty],
        rets: &[Ty],
        kind: SymKind,
    ) -> Result<FuncRef, BuildError> {
        if self.by_name.contains_key(name) || self.globals_by_name.contains_key(name) {
            return err(format!("@{name} is defined more than once"));
        }
        let id = self.syms.len() as u32;
        self.syms.push(Sym {
            name: name.to_owned(),
            params: params.to_vec(),
            rets: rets.to_vec(),
            kind,
        });
        self.by_name.insert(name.to_owned(), id);
        Ok(FuncRef(id))
    }

    /// Declare a function, to call it or take its address before it is defined (with
    /// [`ModuleBuilder::define`]). Parameters and results are value types.
    pub fn declare_func(
        &mut self,
        name: &str,
        params: &[Ty],
        rets: &[Ty],
    ) -> Result<FuncRef, BuildError> {
        check_name(name)?;
        self.value_tys("func", name, params)?;
        self.value_tys("func", name, rets)?;
        self.add_sym(name, params, rets, SymKind::Declared)
    }

    /// `extern func @name(params) -> rets effects[effects] trust`: a function outside the module.
    pub fn extern_func(
        &mut self,
        name: &str,
        params: &[Ty],
        rets: &[Ty],
        effects: &[ExtEffect],
        trust: Trust,
    ) -> Result<FuncRef, BuildError> {
        check_name(name)?;
        self.value_tys("extern", name, params)?;
        self.value_tys("extern", name, rets)?;
        let f = self.add_sym(name, params, rets, SymKind::Extern)?;
        self.module.externs.push(Extern {
            name: name.to_owned(),
            params: params.to_vec(),
            rets: rets.to_vec(),
            effects: effects.to_vec(),
            trust,
        });
        Ok(f)
    }

    /// The function or external function with this name.
    pub fn func_ref(&self, name: &str) -> Option<FuncRef> {
        self.by_name.get(name).map(|&i| FuncRef(i))
    }

    /// A function's name.
    pub fn func_name(&self, f: FuncRef) -> &str {
        &self.syms[f.index()].name
    }

    fn sym(&self, f: FuncRef) -> Result<&Sym, BuildError> {
        match self.syms.get(f.index()) {
            Some(s) => Ok(s),
            None => err(format!("function {} does not exist", f.0)),
        }
    }

    /// Start a new function: [`ModuleBuilder::declare_func`] then [`ModuleBuilder::define`].
    pub fn func(
        &mut self,
        name: &str,
        params: &[Ty],
        rets: &[Ty],
    ) -> Result<FuncBuilder<'_>, BuildError> {
        if self.st.func.is_some() {
            return err("a function is already being built");
        }
        let f = self.declare_func(name, params, rets)?;
        self.define(f)
    }

    /// Start building a declared function's body, with the insertion point at the end of its
    /// entry region. Functions are added to the module in the order they are finished.
    pub fn define(&mut self, f: FuncRef) -> Result<FuncBuilder<'_>, BuildError> {
        if let Some(cur) = self.st.func {
            return err(format!(
                "@{} is still being built",
                self.syms[cur.index()].name
            ));
        }
        self.sym(f)?;
        let sym = &self.syms[f.index()];
        match sym.kind {
            SymKind::Declared => {}
            SymKind::Extern => return err(format!("@{} is external", sym.name)),
            _ => return err(format!("@{} is already defined", sym.name)),
        }
        let st = &mut self.st;
        st.body.clear();
        let entry = st.body.entry();
        st.body.set_params(
            entry,
            sym.params.iter().map(|&ty| ValueSpec {
                name: "",
                ty,
                facts: Vec::new(),
            }),
        );
        st.func = Some(f);
        st.file = None;
        st.at = Some(InsertPoint::End(entry));
        st.loc = None;
        st.ty_map.clear();
        st.func_names.clear();
        st.global_names.clear();
        st.blocks.clear();
        self.syms[f.index()].kind = SymKind::Building;
        Ok(FuncBuilder { m: self })
    }

    /// The function being built, if any, to continue it.
    pub fn current(&mut self) -> Option<FuncBuilder<'_>> {
        self.st.func?;
        Some(FuncBuilder { m: self })
    }

    /// Drop the function being built; it stays declared, and can be defined again.
    pub fn abandon_func(&mut self) {
        if let Some(f) = self.st.func.take() {
            self.syms[f.index()].kind = SymKind::Declared;
            self.st.body.clear();
        }
    }

    /// `global [const] @name: ty [align align] = init`. Make initializers with the `init_`
    /// methods; one that takes the address of a global declared later is set afterwards
    /// with [`ModuleBuilder::set_global_init`].
    pub fn global(
        &mut self,
        name: &str,
        ty: Ty,
        constant: bool,
        align: u32,
        init: Init,
    ) -> Result<GlobalRef, BuildError> {
        check_name(name)?;
        self.check_tys(&[ty])?;
        if self.by_name.contains_key(name) || self.globals_by_name.contains_key(name) {
            return err(format!("@{name} is defined more than once"));
        }
        let g = self.module.globals.len() as u32;
        self.module.globals.push(name, ty, constant, align, init);
        self.globals_by_name.insert(name.to_owned(), g);
        Ok(GlobalRef(g))
    }

    pub fn set_global_init(&mut self, g: GlobalRef, init: Init) -> Result<(), BuildError> {
        self.global_check(g)?;
        self.module.globals.set_init(g.index(), init);
        Ok(())
    }

    fn global_check(&self, g: GlobalRef) -> Result<(), BuildError> {
        if g.index() < self.module.globals.len() {
            Ok(())
        } else {
            err(format!("global {} does not exist", g.0))
        }
    }

    /// The global with this name.
    pub fn global_ref(&self, name: &str) -> Option<GlobalRef> {
        self.globals_by_name.get(name).map(|&i| GlobalRef(i))
    }

    /// An integer initializer, for an `iN` or `bN`.
    pub fn init_int(&mut self, n: impl Into<IntImm>) -> Init {
        let n = match n.into() {
            IntImm::Small(n) => BigInt::from(n),
            IntImm::Big(n) => n,
        };
        self.module.globals.int_init(n)
    }

    /// `@f`: a function's address.
    pub fn init_func(&mut self, f: FuncRef) -> Result<Init, BuildError> {
        self.sym(f)?;
        let name = &self.syms[f.index()].name;
        Ok(self.module.globals.sym_init(name))
    }

    /// `@g`: a global's address.
    pub fn init_global(&mut self, g: GlobalRef) -> Result<Init, BuildError> {
        self.global_check(g)?;
        let name = self.module.globals.name(g.index()).to_owned();
        Ok(self.module.globals.sym_init(&name))
    }

    /// `bytes "…"`: the whole object's bytes.
    pub fn init_bytes(&mut self, bytes: &[u8]) -> Init {
        self.module.globals.bytes_init(bytes.iter().copied())
    }

    /// `{…}`: one initializer per struct field or array element.
    pub fn init_list(&mut self, items: &[Init]) -> Init {
        self.module.globals.list_init(items.iter().copied())
    }
}

/// Names written after `@` in text: letters, digits, `_`, and `.`, not starting with a digit.
fn check_name(name: &str) -> Result<(), BuildError> {
    let b = name.as_bytes();
    let ok = !b.is_empty()
        && !b[0].is_ascii_digit()
        && b.iter()
            .all(|&c| c.is_ascii_alphanumeric() || c == b'_' || c == b'.');
    if ok {
        Ok(())
    } else {
        err(format!("'{name}' is not a valid name"))
    }
}

/// Value names and labels: letters, digits, `_`, and `.`.
fn check_value_name(name: &str) -> Result<(), BuildError> {
    let ok = !name.is_empty()
        && name
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'.');
    if ok {
        Ok(())
    } else {
        err(format!("'{name}' is not a valid name"))
    }
}

/// Builds one function of a [`ModuleBuilder`]. See the [module documentation](self).
pub struct FuncBuilder<'m> {
    m: &'m mut ModuleBuilder,
}

impl<'m> FuncBuilder<'m> {
    /// The module builder, to declare types, globals, and functions while building.
    pub fn module(&mut self) -> &mut ModuleBuilder {
        self.m
    }

    /// The function being built.
    pub fn func(&self) -> FuncRef {
        self.m.st.func.expect("a function is being built")
    }

    /// The body so far.
    pub fn body(&self) -> &Body {
        &self.m.st.body
    }

    /// Finish the function: give each unnamed value its id as a name, and add the function to
    /// the module.
    pub fn finish(self) -> Result<FuncRef, BuildError> {
        let m = self.m;
        let f = m.st.func.take().expect("a function is being built");
        let st = &mut m.st;
        for (op, blocks) in std::mem::take(&mut st.blocks) {
            st.body.set_regions(op, &blocks);
        }
        let mut digits = String::new();
        for v in 0..st.body.num_values() as u32 {
            let v = ValueId::from_raw(v);
            if st.body.name(v).is_empty() {
                use std::fmt::Write;
                digits.clear();
                write!(digits, "{}", v.raw()).unwrap();
                st.body.set_name(v, &digits);
            }
        }
        // As in the parser: a small body is copied out exactly sized, and the builder keeps its
        // arrays for the next function; a large one is handed over.
        let body = if st.body.num_ops() < SMALL_BODY {
            st.body.clone()
        } else {
            let mut body = std::mem::take(&mut st.body);
            body.shrink_to_fit();
            body
        };
        let sym = &mut m.syms[f.index()];
        sym.kind = SymKind::Defined;
        m.module.funcs.push(Func {
            name: sym.name.clone(),
            rets: sym.rets.clone(),
            file: st.file.take(),
            body,
        });
        Ok(f)
    }

    // Position, locations, names, and facts.

    /// Parameter `i` of the function.
    pub fn param(&self, i: usize) -> ValueId {
        self.params().get(i)
    }

    pub fn params(&self) -> Values {
        let b = &self.m.st.body;
        Values::of(b.params(b.entry()))
    }

    /// The function's entry region.
    pub fn entry(&self) -> RegionId {
        self.m.st.body.entry()
    }

    pub fn insert_point(&self) -> InsertPoint {
        self.m.st.at.expect("a function is being built")
    }

    pub fn set_insert_point(&mut self, at: InsertPoint) -> Result<(), BuildError> {
        match at {
            InsertPoint::End(r) => self.check_region(r)?,
            InsertPoint::Before(op) => {
                self.check_op(op)?;
                if !self.m.st.body.is_linked(op) {
                    return err("the op is in no region");
                }
            }
        }
        self.m.st.at = Some(at);
        Ok(())
    }

    /// Put the next ops at the end of `r`.
    pub fn position_at_end(&mut self, r: RegionId) -> Result<(), BuildError> {
        self.set_insert_point(InsertPoint::End(r))
    }

    /// Put the next ops right before `op`.
    pub fn position_before(&mut self, op: OpId) -> Result<(), BuildError> {
        self.set_insert_point(InsertPoint::Before(op))
    }

    /// The location the next ops get (`None`: unknown). It stays until changed.
    pub fn set_loc(&mut self, loc: Option<Loc>) {
        self.m.st.loc = loc;
    }

    /// The source file the function's locations are in (`loc "main.c"`).
    pub fn set_file(&mut self, file: Option<&str>) {
        self.m.st.file = file.map(str::to_owned);
    }

    /// Name a value (a result or a parameter), as `%name` in text.
    pub fn name(&mut self, v: ValueId, name: &str) -> Result<(), BuildError> {
        self.check_value(v)?;
        check_value_name(name)?;
        self.m.st.body.set_name(v, name);
        Ok(())
    }

    /// Put these facts on a value, replacing any it has.
    pub fn set_facts(&mut self, v: ValueId, facts: &[(FactArg, Trust)]) -> Result<(), BuildError> {
        self.check_value(v)?;
        let b = &mut self.m.st.body;
        let mut out = Vec::with_capacity(facts.len());
        for (f, trust) in facts {
            let fact = match f {
                FactArg::RangeS(lo, hi) => Fact::RangeS(int_id(b, lo), int_id(b, hi)),
                FactArg::RangeU(lo, hi) => Fact::RangeU(int_id(b, lo), int_id(b, hi)),
                FactArg::NonNull => Fact::NonNull,
                FactArg::Align(n) => Fact::Align(*n),
                FactArg::NoAlias => Fact::NoAlias,
                FactArg::ReadOnly => Fact::ReadOnly,
            };
            out.push(TrustedFact {
                fact,
                trust: *trust,
            });
        }
        b.set_facts(v, out);
        Ok(())
    }

    /// A hole, `?name: ty`: an operand standing for a value not written yet.
    pub fn hole(&mut self, name: &str, ty: Ty) -> Result<Operand, BuildError> {
        check_value_name(name)?;
        let ty = self.ty_imm(ty)?;
        Ok(self.m.st.body.add_hole(name, ty))
    }

    /// A value's type. Struct, array, and function types are in the body's table, not the
    /// module's; values only have value types.
    pub fn ty(&self, v: ValueId) -> Ty {
        self.m.st.body.ty(v)
    }

    /// Region `i` of `op`.
    pub fn region(&self, op: OpId, i: usize) -> Result<RegionId, BuildError> {
        self.check_op(op)?;
        match self.m.st.body.regions(op).get(i) {
            Some(&r) => Ok(r),
            None => err(format!("the op has no region {i}")),
        }
    }

    /// A region's parameters.
    pub fn region_params(&self, r: RegionId) -> Result<Values, BuildError> {
        self.check_region(r)?;
        Ok(Values::of(self.m.st.body.params(r)))
    }

    /// An op's results.
    pub fn results(&self, op: OpId) -> Result<Results, BuildError> {
        self.check_op(op)?;
        Ok(Results {
            op,
            values: Values::of(self.m.st.body.results(op)),
        })
    }

    /// A new block of the `cf.blocks` op `op`, with this label (empty: its region id) and
    /// parameters. The first block is the entry; it has no parameters. Blocks are added to the
    /// op in the order they are made, when [`FuncBuilder::end_blocks`] is called or the
    /// function is finished.
    pub fn block(&mut self, op: OpId, label: &str, params: &[Ty]) -> Result<RegionId, BuildError> {
        self.check_op(op)?;
        let st = &mut self.m.st;
        let Some(i) = st.blocks.iter().rposition(|(o, _)| *o == op) else {
            return err("blocks can only be added to a cf.blocks op not yet ended");
        };
        let tys = self.import_list(params)?;
        let st = &mut self.m.st;
        let label = if label.is_empty() {
            st.body.add_str(&st.body.num_regions().to_string())
        } else {
            check_value_name(label)?;
            st.body.add_str(label)
        };
        let r = st.body.new_block(
            op,
            label,
            tys.iter().map(|&ty| ValueSpec {
                name: "",
                ty,
                facts: Vec::new(),
            }),
        );
        st.tys = tys;
        st.blocks[i].1.push(r);
        Ok(r)
    }

    /// Give a `cf.blocks` op the blocks made for it so far; no more can be added.
    pub fn end_blocks(&mut self, op: OpId) -> Result<(), BuildError> {
        let st = &mut self.m.st;
        let Some(i) = st.blocks.iter().rposition(|(o, _)| *o == op) else {
            return err("the op is not a cf.blocks op being built");
        };
        let (op, blocks) = st.blocks.remove(i);
        st.body.set_regions(op, &blocks);
        Ok(())
    }

    // Checks of ids from outside.

    fn check_value(&self, v: ValueId) -> Result<(), BuildError> {
        if v.index() < self.m.st.body.num_values() {
            Ok(())
        } else {
            err(format!("value {} does not exist in this function", v.raw()))
        }
    }

    fn check_op(&self, op: OpId) -> Result<(), BuildError> {
        if op.index() < self.m.st.body.num_ops() {
            Ok(())
        } else {
            err(format!("op {} does not exist in this function", op.raw()))
        }
    }

    fn check_region(&self, r: RegionId) -> Result<(), BuildError> {
        if r.index() < self.m.st.body.num_regions() {
            Ok(())
        } else {
            err(format!(
                "region {} does not exist in this function",
                r.raw()
            ))
        }
    }

    /// An operand's type, checking that it exists.
    fn operand_ty(&self, o: Operand) -> Result<Ty, BuildError> {
        let b = &self.m.st.body;
        match o.get() {
            OperandKind::Value(v) if v.index() < b.num_values() => Ok(b.ty(v)),
            OperandKind::Hole(h) if h.index() < b.num_holes() => Ok(b.hole_ty(h)),
            OperandKind::Value(v) => {
                err(format!("value {} does not exist in this function", v.raw()))
            }
            OperandKind::Hole(h) => {
                err(format!("hole {} does not exist in this function", h.raw()))
            }
        }
    }

    // What the generated methods use.

    /// Start an op: no operands yet.
    pub(crate) fn begin_op(&mut self) {
        self.m.st.operands.clear();
    }

    pub(crate) fn operand(&mut self, o: Operand) {
        self.m.st.operands.push(o);
    }

    pub(crate) fn operand_list(&mut self, os: &[Operand]) {
        self.m.st.operands.extend_from_slice(os);
    }

    pub(crate) fn int_imm(&mut self, n: IntImm) -> IntId {
        int_id(&mut self.m.st.body, &n)
    }

    pub(crate) fn str_imm(&mut self, s: &str) -> Result<StrId, BuildError> {
        check_value_name(s)?;
        Ok(self.m.st.body.add_str(s))
    }

    /// A function's name in the body's strings, stored once per function built.
    pub(crate) fn func_imm(&mut self, f: FuncRef) -> Result<StrId, BuildError> {
        self.m.sym(f)?;
        let st = &mut self.m.st;
        if st.func_names.len() <= f.index() {
            st.func_names.resize(self.m.syms.len(), NONE);
        }
        if st.func_names[f.index()] == NONE {
            st.func_names[f.index()] = st.body.add_str(&self.m.syms[f.index()].name).raw();
        }
        Ok(StrId::from_raw(st.func_names[f.index()]))
    }

    pub(crate) fn global_imm(&mut self, g: GlobalRef) -> Result<StrId, BuildError> {
        self.m.global_check(g)?;
        let st = &mut self.m.st;
        let gs = &self.m.module.globals;
        if st.global_names.len() <= g.index() {
            st.global_names.resize(gs.len(), NONE);
        }
        if st.global_names[g.index()] == NONE {
            st.global_names[g.index()] = st.body.add_str(gs.name(g.index())).raw();
        }
        Ok(StrId::from_raw(st.global_names[g.index()]))
    }

    /// A type of the module, as a type of the body's table.
    pub(crate) fn ty_imm(&mut self, t: Ty) -> Result<Ty, BuildError> {
        self.m.check_tys(&[t])?;
        Ok(import(
            &self.m.module.globals.types,
            &mut self.m.st.body,
            &mut self.m.st.ty_map,
            t,
        ))
    }

    fn import_list(&mut self, ts: &[Ty]) -> Result<Vec<Ty>, BuildError> {
        self.m.check_tys(ts)?;
        let mut out = std::mem::take(&mut self.m.st.tys);
        out.clear();
        for &t in ts {
            out.push(import(
                &self.m.module.globals.types,
                &mut self.m.st.body,
                &mut self.m.st.ty_map,
                t,
            ));
        }
        Ok(out)
    }

    /// A branch target, its arguments added to the operands.
    pub(crate) fn succ(&mut self, t: Target<'_>) -> Result<SuccId, BuildError> {
        let s = self.target(t)?;
        Ok(self.m.st.body.add_succ(s))
    }

    fn target(&mut self, t: Target<'_>) -> Result<Succ, BuildError> {
        self.check_region(t.block)?;
        let Some(label) = self.m.st.body.label(t.block) else {
            return err("a branch target must be a block of cf.blocks");
        };
        self.operand_list(t.args);
        Ok(Succ {
            label,
            nargs: t.args.len() as u32,
        })
    }

    pub(crate) fn cases(&mut self, cs: &[SwitchCase<'_>]) -> Result<CasesId, BuildError> {
        let mut cases = Vec::with_capacity(cs.len());
        for c in cs {
            let succ = self.target(c.target)?;
            let key = self.int_imm(c.key.clone());
            cases.push(crate::body::Case { key, succ });
        }
        Ok(self.m.st.body.add_cases(cases))
    }

    pub(crate) fn result(&self, op: OpId, i: usize) -> ValueId {
        Values::of(self.m.st.body.results(op)).get(i)
    }

    pub(crate) fn all_results(&self, op: OpId) -> Results {
        Results {
            op,
            values: Values::of(self.m.st.body.results(op)),
        }
    }

    /// Make an op without regions from the operands added since [`FuncBuilder::begin_op`],
    /// after checking it by its typing rule as far as that is cheap.
    pub(crate) fn simple(&mut self, kind: OpKind, res: Res<'_>) -> Result<OpId, BuildError> {
        let operands = std::mem::take(&mut self.m.st.operands);
        let mut outs = std::mem::take(&mut self.m.st.tys);
        outs.clear();
        let r = self
            .check_rule(kind, &operands, res, &mut outs)
            .map(|()| self.push(kind, &operands, &outs, std::iter::empty()));
        self.m.st.operands = operands;
        self.m.st.tys = outs;
        r.map_err(|e| BuildError::new(format!("{}: {}", kind.mnemonic(), e.msg)))
    }

    /// Make an op with regions; `results` are its result types. With `iter`, the first region's
    /// parameters take the operands' types (`cf.loop`'s state); `blocks` ops get their blocks
    /// later, from [`FuncBuilder::block`].
    pub(crate) fn region_op(
        &mut self,
        kind: OpKind,
        results: &[Ty],
        regions: usize,
        iter: bool,
    ) -> Result<OpId, BuildError> {
        let operands = std::mem::take(&mut self.m.st.operands);
        let r = self.region_op_with(kind, &operands, results, regions, iter);
        self.m.st.operands = operands;
        r.map_err(|e| BuildError::new(format!("{}: {}", kind.mnemonic(), e.msg)))
    }

    fn region_op_with(
        &mut self,
        kind: OpKind,
        operands: &[Operand],
        results: &[Ty],
        regions: usize,
        iter: bool,
    ) -> Result<OpId, BuildError> {
        let mut params = Vec::new();
        for &o in operands {
            let t = self.operand_ty(o)?;
            if iter {
                params.push(t);
            }
        }
        let outs = self.import_list(results)?;
        let specs = |ts: &[Ty]| -> Vec<ValueSpec<'static>> {
            ts.iter()
                .map(|&ty| ValueSpec {
                    name: "",
                    ty,
                    facts: Vec::new(),
                })
                .collect()
        };
        let op = self.push(
            kind,
            operands,
            &outs,
            (0..regions).map(|i| if i == 0 { specs(&params) } else { Vec::new() }),
        );
        self.m.st.tys = outs;
        if kind.decl().has_blocks() {
            self.m.st.blocks.push((op, Vec::new()));
        }
        Ok(op)
    }

    /// Build in region `r`, then go back to where the builder was.
    pub(crate) fn in_region(
        &mut self,
        r: RegionId,
        f: impl FnOnce(&mut Self) -> Result<(), BuildError>,
    ) -> Result<(), BuildError> {
        let saved = self.m.st.at;
        self.m.st.at = Some(InsertPoint::End(r));
        let out = f(self);
        self.m.st.at = saved;
        out
    }

    /// Run `f` (which builds a `cf.blocks` op's blocks), go back to where the builder was, and
    /// give the op its blocks.
    pub(crate) fn in_blocks(
        &mut self,
        op: OpId,
        f: impl FnOnce(&mut Self, OpId) -> Result<(), BuildError>,
    ) -> Result<(), BuildError> {
        let saved = self.m.st.at;
        let out = f(self, op);
        self.m.st.at = saved;
        out?;
        self.end_blocks(op)
    }

    fn push<'s>(
        &mut self,
        kind: OpKind,
        operands: &[Operand],
        results: &[Ty],
        regions: impl IntoIterator<Item = Vec<ValueSpec<'s>>>,
    ) -> OpId {
        let st = &mut self.m.st;
        let specs = results.iter().map(|&ty| ValueSpec {
            name: "",
            ty,
            facts: Vec::new(),
        });
        let operands = operands.iter().copied();
        match st.at.expect("a function is being built") {
            InsertPoint::End(r) => st.body.append_op(r, kind, operands, specs, regions, st.loc),
            InsertPoint::Before(at) => st
                .body
                .insert_before(at, kind, operands, specs, regions, st.loc),
        }
    }

    /// Check an op by its rule as far as that is cheap, and find its result types.
    fn check_rule(
        &mut self,
        kind: OpKind,
        operands: &[Operand],
        res: Res<'_>,
        outs: &mut Vec<Ty>,
    ) -> Result<(), BuildError> {
        let mut ins = std::mem::take(&mut self.m.st.in_tys);
        ins.clear();
        let r = self.check_rule_with(kind, operands, res, &mut ins, outs);
        self.m.st.in_tys = ins;
        r
    }

    fn check_rule_with(
        &mut self,
        kind: OpKind,
        operands: &[Operand],
        res: Res<'_>,
        ins: &mut Vec<Ty>,
        outs: &mut Vec<Ty>,
    ) -> Result<(), BuildError> {
        for &o in operands {
            ins.push(self.operand_ty(o)?);
        }
        let ins: &[Ty] = ins;
        match res {
            Res::None | Res::Implied => {}
            Res::Given(ts) => {
                self.m.check_tys(ts)?;
                for &t in ts {
                    outs.push(import(
                        &self.m.module.globals.types,
                        &mut self.m.st.body,
                        &mut self.m.st.ty_map,
                        t,
                    ));
                }
            }
            Res::Callee(f) => {
                let sym = self.m.sym(f)?;
                if ins != sym.params.as_slice() {
                    return err(format!(
                        "arguments of @{}: expected {} but got {}",
                        sym.name,
                        self.show_list(&sym.params),
                        self.show_list(ins)
                    ));
                }
                outs.extend_from_slice(&sym.rets);
            }
            Res::Sig(t) => {
                let types = self.m.st.body.types();
                let Some(Shape::Func(ps, rs)) = types.shape_of(t) else {
                    return err(format!("{} is not a function type", types.show(t)));
                };
                if ins.is_empty() || ins[0] != Ty::Ptr || ins[1..] != *ps {
                    let mut want = vec![Ty::Ptr];
                    want.extend_from_slice(ps);
                    return err(format!(
                        "operands: expected {} but got {}",
                        self.show_list(&want),
                        self.show_list(ins)
                    ));
                }
                outs.extend_from_slice(rs);
            }
        }
        let Some(rule) = kind.decl().rule else {
            return Ok(());
        };
        let addr = Ty::Int(self.m.module.space.addr_bits);
        let mut vars = [Ty::Ptr; 4];
        let mut named = 0;
        let ty = |vars: &[Ty; 4], e: TyE| match e {
            TyE::Ptr => Ty::Ptr,
            TyE::Addr => addr,
            TyE::Int(w) => Ty::Int(w),
            TyE::Var(i) => vars[usize::from(i)],
            TyE::Field(i) => match kind.imm(i.into()) {
                Some(Imm::Ty(t)) => t,
                _ => Ty::Ptr,
            },
        };
        let same = |vars: &[Ty; 4], got: &[Ty], want: &[TyE]| {
            got.len() == want.len() && got.iter().zip(want).all(|(g, w)| *g == ty(vars, *w))
        };
        for check in rule {
            match *check {
                Check::TakeIns(n, msg) => {
                    if ins.len() != usize::from(n) {
                        return err(msg);
                    }
                    vars[named..named + ins.len()].copy_from_slice(ins);
                    named += ins.len();
                }
                Check::TakeOuts(n, msg) => {
                    if outs.len() != usize::from(n) {
                        return err(msg);
                    }
                    vars[named..named + outs.len()].copy_from_slice(outs);
                    named += outs.len();
                }
                Check::Ins(label, want) => {
                    if !same(&vars, ins, want) {
                        let want: Vec<Ty> = want.iter().map(|e| ty(&vars, *e)).collect();
                        return err(format!(
                            "{label}: expected {} but got {}",
                            self.show_list(&want),
                            self.show_list(ins)
                        ));
                    }
                }
                Check::Outs(want) => {
                    if matches!(res, Res::Implied) {
                        outs.extend(want.iter().map(|e| ty(&vars, *e)));
                    }
                }
                Check::NoOuts => {}
                Check::Same(label, got, want) => {
                    let got: Vec<Ty> = got.iter().map(|e| ty(&vars, *e)).collect();
                    if !same(&vars, &got, want) {
                        let want: Vec<Ty> = want.iter().map(|e| ty(&vars, *e)).collect();
                        return err(format!(
                            "{label}: expected {} but got {}",
                            self.show_list(&want),
                            self.show_list(&got)
                        ));
                    }
                }
                Check::Ints(ts) => {
                    let ts: Vec<Ty> = ts.iter().map(|e| ty(&vars, *e)).collect();
                    if !ts.iter().all(|t| matches!(t, Ty::Int(_))) {
                        return err(format!("expected integers but got {}", self.show_list(&ts)));
                    }
                }
                Check::Pow2(i) => {
                    if let Some(Imm::Align(a)) = kind.imm(i.into())
                        && !a.is_power_of_two()
                    {
                        return err("alignment must be a power of two");
                    }
                }
                Check::Widens(a, t) | Check::Narrows(a, t) => {
                    let (a, t) = (ty(&vars, a), ty(&vars, t));
                    let (wa, wt) = (width(a), width(t));
                    if matches!(check, Check::Widens(..)) && wt <= wa {
                        return err(format!(
                            "cannot extend {} to {}",
                            self.show(a),
                            self.show(t)
                        ));
                    }
                    if matches!(check, Check::Narrows(..)) && wt >= wa {
                        return err(format!(
                            "cannot truncate {} to {}",
                            self.show(a),
                            self.show(t)
                        ));
                    }
                }
                Check::Deny(names, msg) => {
                    if names.contains(&kind.mnemonic()) {
                        return err(msg);
                    }
                }
                // Integer ranges, layouts, and names are left to the verifier.
                Check::Fits(..)
                | Check::Loadable(..)
                | Check::Call(_)
                | Check::Sized(_)
                | Check::Field(..)
                | Check::Sig(_)
                | Check::Global(_)
                | Check::Func(_) => {}
            }
        }
        Ok(())
    }

    fn show(&self, t: Ty) -> String {
        self.m.st.body.types().show(t)
    }

    fn show_list(&self, ts: &[Ty]) -> String {
        self.m.st.body.types().show_list(ts)
    }
}

fn width(t: Ty) -> u32 {
    match t {
        Ty::Int(w) | Ty::Byte(w) => w,
        _ => 0,
    }
}

fn int_id(b: &mut Body, n: &IntImm) -> IntId {
    match n {
        IntImm::Small(n) => b.add_small_int(*n),
        IntImm::Big(n) => b.add_int(n.clone()),
    }
}

/// Copy a type of the module's table into the body's, once per function.
fn import(from: &Types, body: &mut Body, map: &mut Vec<u32>, t: Ty) -> Ty {
    let Ty::Agg(id) = t else { return t };
    if map.len() <= id.index() {
        map.resize(from.len(), NONE);
    }
    if map[id.index()] != NONE {
        return Ty::Agg(TyId::from_raw(map[id.index()]));
    }
    let list = |ts: &[Ty], body: &mut Body, map: &mut Vec<u32>| -> Vec<Ty> {
        ts.iter().map(|&t| import(from, body, map, t)).collect()
    };
    let out = match from.shape(id) {
        Shape::Struct(p, fs) => {
            let fs = list(fs, body, map);
            body.types_mut().structure(p, &fs)
        }
        Shape::Array(n, e) => {
            let e = import(from, body, map, e);
            body.types_mut().array(n, e)
        }
        Shape::Func(ps, rs) => {
            let ps = list(ps, body, map);
            let rs = list(rs, body, map);
            body.types_mut().func(&ps, &rs)
        }
    };
    if let Ty::Agg(new) = out {
        map[id.index()] = new.raw();
    }
    out
}
