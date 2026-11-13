//! Differential testing of promotion (`mem2reg`, experimental) and of deleting the slots it
//! leaves (`stackdce`, experimental), on random programs made for them.
//!
//! The generator writes mostly defined programs whose locals are typed stack slots
//! (`mem.stack.of` of `i8`, `i16`, `i32`, `i64`, `ptr`, `f32`, `f64`, at the function's entry
//! and sometimes inside a loop body or a block, so they are made again each time), each written
//! and read only with its own type, across nested `cf.if` (with and without results, regions
//! that fall off their end), counted `cf.loop`s with state of their own (`cf.break` with results
//! and `cf.continue` from nested `cf.if`s), and `cf.blocks` (`cf.br`, `cf.cond_br`, `cf.switch`
//! with cases sharing a target, `cf.yield` from any block, branches out of nested `cf.if`s,
//! back edges bounded by a counter each block passes on, blocks in loops and loops in blocks,
//! `cf.break` and `cf.continue` from inside blocks), with `func.ret` from nested regions too.
//! Values reach external calls (`@out`, `@outp`: events) and the result. Some slots are read
//! before anything is stored (`poison`), and some are not promotable (passed to `@esc`, or read
//! with another type than they are written), to check they are left alone. Some slots are C
//! structs (`struct<C>{…}` of those types), whose fields are reached by `ptr.offset` by an
//! `int.const`: through a pointer made with the slot, or one made at the access (in a nested
//! region), sometimes from another field's pointer; each field is promoted on its own. A struct
//! one of whose fields' pointers escapes is not promotable.
//!
//! Each program is promoted with `mem2reg` alone, verifying after the pass: exactly the
//! promotable slots that have accesses are promoted, none of their loads and stores remain, the
//! other slots keep theirs, a second run changes nothing, the result prints and parses back to
//! the same text, and each run of the result refines the original's run in the interpreter, as
//! `tests/opt.rs` compares them (same line, or the source's events first where it is UB, stuck,
//! or out of fuel; nothing where it is ambiguous). The pipeline `mem2reg,stackdce,fwd,copyprop,
//! dse,dce` to a fixed point is compared the same way, up to renaming allocations (the
//! assumption `stackdce` rests on). Every fifth program is also compiled to AArch64 (alternately
//! after `mem2reg` alone and after the whole pipeline), run (under `qemu-aarch64` off AArch64),
//! and compared with the interpreter's run of the original under Arm's NaN rule, pointers
//! printed as `?` and `poison` matching anything; runs that are UB, stuck, or out of fuel aren't
//! compared natively.
//!
//! By default 500 programs run; `FIR_FUZZ=N` runs N, `FIR_FUZZ_SEED=S` picks another seed.
//! `FIR_MEM2REG_NATIVE=0` skips the native runs (which otherwise need an AArch64 C compiler,
//! `FIR_CC` or `aarch64-unknown-linux-gnu-cc`, and `qemu-aarch64` off AArch64). Failing
//! programs are written to `target/tmp/mem2reg/`.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use fir::backend::aarch64 as a64;
use fir::interp::NanRule;
use fir::passes::{Pipeline, Remarks};

const FUEL: u64 = 2_000_000;
const FULL: &str = "mem2reg,stackdce,fwd,copyprop,dse,dce";

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).map_or(default, |s| s.parse().expect(name))
}

// The comparison of runs, as `tests/opt.rs` makes it.

/// A run's line split into its events and its ending.
fn split(line: &str) -> (Vec<&str>, &str) {
    let mut events = Vec::new();
    let mut rest = line;
    while rest.starts_with('@') {
        match rest.split_once("; ") {
            Some((e, r)) => {
                events.push(e);
                rest = r;
            }
            None => break,
        }
    }
    (events, rest)
}

/// How a target run compared with its source run.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Cmp {
    Equal,
    SourceUb,
    SourceFuel,
    SourceAmbiguous,
}

/// Whether target run `t` refines source run `s`.
fn refines(t: &Result<String, String>, s: &Result<String, String>) -> Result<Cmp, String> {
    let (Ok(tl), Ok(sl)) = (t, s) else {
        return if t == s {
            Ok(Cmp::Equal)
        } else {
            Err("different errors".into())
        };
    };
    let ((te, tend), (se, send)) = (split(tl), split(sl));
    let prefix = || {
        if te.len() >= se.len() && te[..se.len()] == se[..] {
            Ok(())
        } else {
            Err(format!("the events {se:?} don't start the target's {te:?}"))
        }
    };
    if send.starts_with("ub ") || send.starts_with("stuck") {
        prefix().map(|()| Cmp::SourceUb)
    } else if send.starts_with("out of fuel") {
        prefix().map(|()| Cmp::SourceFuel)
    } else if send.starts_with("ambiguous") {
        Ok(Cmp::SourceAmbiguous)
    } else if tl == sl {
        Ok(Cmp::Equal)
    } else {
        Err(format!("the ending {send:?} became {tend:?}"))
    }
}

/// A run's line with its allocations renumbered in order of first appearance.
fn rename_allocs(line: &str) -> String {
    let mut names: Vec<&str> = Vec::new();
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(i) = rest.find('#') {
        out.push_str(&rest[..=i]);
        rest = &rest[i + 1..];
        let n = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        if n > 0 {
            let id = &rest[..n];
            let k = names.iter().position(|x| *x == id).unwrap_or_else(|| {
                names.push(id);
                names.len() - 1
            });
            write!(out, "a{k}").unwrap();
            rest = &rest[n..];
        }
    }
    out.push_str(rest);
    out
}

fn run(m: &fir::Module, args: &[String]) -> Result<String, String> {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    fir::interp::run(m, "f0", &args, FUEL)
}

// The generator.

/// A small deterministic generator (splitmix64, as `progs` uses).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    /// True `p` percent of the time.
    fn chance(&mut self, p: u64) -> bool {
        self.below(100) < p
    }
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum T {
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    P,
}

const TYS: [T; 7] = [T::I8, T::I16, T::I32, T::I64, T::F32, T::F64, T::P];
const INTS: [T; 4] = [T::I8, T::I16, T::I32, T::I64];

impl T {
    fn name(self) -> &'static str {
        match self {
            T::I8 => "i8",
            T::I16 => "i16",
            T::I32 => "i32",
            T::I64 => "i64",
            T::F32 => "f32",
            T::F64 => "f64",
            T::P => "ptr",
        }
    }
    fn size(self) -> u64 {
        match self {
            T::I8 => 1,
            T::I16 => 2,
            T::I32 | T::F32 => 4,
            T::I64 | T::F64 | T::P => 8,
        }
    }
    fn align(self) -> u32 {
        match self {
            T::I8 => 1,
            T::I16 => 2,
            T::I32 | T::F32 => 4,
            T::I64 | T::F64 | T::P => 8,
        }
    }
}

/// The blocks of a `cf.blocks`: each one's label and extra parameter.
type Blocks = Vec<(String, Option<T>)>;

/// Where the generator is: what ends the region it writes, and where jumps go.
#[derive(Clone)]
enum Ctx {
    /// A `cf.if` region (its own `cf.yield`s are written where it ends).
    If,
    /// A loop body: its results, the next counter (every `cf.continue` passes it), and the
    /// types of the rest of its state.
    Loop {
        results: Vec<T>,
        next: String,
        state: Vec<T>,
    },
    /// A block of a `cf.blocks`: each block's label and extra parameter, which block this is,
    /// and the counter it passes on.
    Block {
        blocks: Vec<(String, Option<T>)>,
        index: usize,
        next: String,
    },
}

struct Gen {
    rng: Rng,
    out: String,
    indent: usize,
    fresh: u32,
    /// The values in scope, innermost last.
    vals: Vec<(String, T)>,
    /// The promotable slots in scope.
    slots: Vec<(String, T)>,
    /// The non-promotable slots (at the entry): written as `i64`, read as `i32`, or escaped.
    others: Vec<String>,
    ctx: Vec<Ctx>,
    budget: i32,
    depth: u32,
    /// Promotable slots with an access, by name.
    accessed: HashSet<String>,
    /// The pointers to struct fields in `slots`: each one's struct slot and offset.
    fields: HashMap<String, (String, u64)>,
    /// The pointers promotable fields were accessed through.
    field_addrs: HashSet<String>,
    /// Promotable struct slots with an access.
    structs: HashSet<String>,
    /// Whether `@f1` exists to call.
    callee: bool,
}

/// A generated program: its text, how many slots promotion must promote, the names of the
/// promotable and other slots, and the argument lists to run `@f0` with.
struct Prog {
    text: String,
    promotable: usize,
    /// How many of them are structs.
    structs: usize,
    slots: Vec<String>,
    others: Vec<String>,
    runs: Vec<Vec<String>>,
}

impl Gen {
    fn line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }

    /// Define a value of type `t` by `rhs`, and put it in scope.
    fn def(&mut self, t: T, rhs: &str) -> String {
        let v = self.name("v");
        self.line(&format!("%{v}: {} = {rhs}", t.name()));
        self.vals.push((v.clone(), t));
        format!("%{v}")
    }

    fn constant(&mut self, t: T) -> String {
        let rhs = match t {
            T::P => "ptr.null".to_owned(),
            T::F32 | T::F64 => format!(
                "float.const {}",
                self.rng
                    .pick(&["0.5", "1.5", "-2.0", "3.25", "0.0", "-0.0", "100.0"])
            ),
            _ => format!(
                "int.const {}",
                self.rng.pick(&[0i64, 1, 2, 3, -1, 5, 7, 42, -100, 127])
            ),
        };
        self.def(t, &rhs)
    }

    /// A value of type `t`: usually one in scope.
    fn val(&mut self, t: T) -> String {
        let have: Vec<String> = self
            .vals
            .iter()
            .filter(|v| v.1 == t)
            .map(|v| format!("%{}", v.0))
            .collect();
        if !have.is_empty() && self.rng.chance(85) {
            have[self.rng.below(have.len() as u64) as usize].clone()
        } else if t == T::P && self.rng.chance(70) {
            "%buf".to_owned()
        } else {
            self.constant(t)
        }
    }

    fn vals_of(&mut self, ts: &[T]) -> String {
        let vs: Vec<String> = ts.iter().map(|&t| self.val(t)).collect();
        vs.join(", ")
    }

    fn cond(&mut self) -> String {
        let t = self.rng.pick(&INTS);
        let (x, y) = (self.val(t), self.val(t));
        let p = self.rng.pick(&["slt", "eq", "ne", "ult", "sge"]);
        self.def_i1(&format!("int.cmp.{p} {x}, {y}"))
    }

    fn def_i1(&mut self, rhs: &str) -> String {
        let v = self.name("c");
        self.line(&format!("%{v}: i1 = {rhs}"));
        format!("%{v}")
    }

    fn types(&mut self, max: u64) -> Vec<T> {
        let n = self.rng.below(max + 1);
        (0..n).map(|_| self.rng.pick(&TYS)).collect()
    }

    fn results(&mut self, ts: &[T]) -> String {
        let rs: Vec<String> = ts
            .iter()
            .map(|t| {
                let v = self.name("v");
                self.vals.push((v.clone(), *t));
                format!("%{v}: {}", t.name())
            })
            .collect();
        if rs.is_empty() {
            String::new()
        } else {
            format!("{} = ", rs.join(", "))
        }
    }

    /// Make a promotable slot here, and usually store into it at once.
    fn slot(&mut self, store: u64) {
        if self.rng.chance(25) {
            return self.struct_slot(store);
        }
        let t = self.rng.pick(&TYS);
        let a = self.rng.pick(&[1, t.align(), t.align(), 16]);
        let s = self.name("p");
        self.line(&format!("%{s}: ptr = mem.stack.of {}, align {a}", t.name()));
        self.slots.push((s.clone(), t));
        if self.rng.chance(store) {
            self.store(&s, t);
        }
    }

    /// A promotable C struct of two to four fields, with a pointer to each field (`%fN`),
    /// usually stored into at once.
    fn struct_slot(&mut self, store: u64) {
        let ts: Vec<T> = (0..2 + self.rng.below(3))
            .map(|_| self.rng.pick(&TYS))
            .collect();
        let (mut end, mut align) = (0u64, 1u32);
        let mut offsets = Vec::new();
        for t in &ts {
            let a = u64::from(t.align());
            end = end.div_ceil(a) * a;
            offsets.push(end);
            end += t.size();
            align = align.max(t.align());
        }
        let s = self.name("p");
        let names: Vec<&str> = ts.iter().map(|t| t.name()).collect();
        self.line(&format!(
            "%{s}: ptr = mem.stack.of struct<C>{{{}}}, align {align}",
            names.join(", ")
        ));
        for (&t, &o) in ts.iter().zip(&offsets) {
            let f = self.field_ptr(&s, o);
            self.fields.insert(f.clone(), (s.clone(), o));
            self.slots.push((f.clone(), t));
            if self.rng.chance(store) {
                self.store(&f, t);
            }
        }
    }

    /// `ptr.offset` of `%base` by `offset` (an `int.const`).
    fn field_ptr(&mut self, base: &str, offset: u64) -> String {
        self.offset_ptr(base, offset as i64)
    }

    fn offset_ptr(&mut self, base: &str, offset: i64) -> String {
        let k = self.name("k");
        self.line(&format!("%{k}: i64 = int.const {offset}"));
        let f = self.name("f");
        let mode = if offset >= 0 && self.rng.chance(70) {
            "inbounds"
        } else {
            "wrap"
        };
        self.line(&format!("%{f}: ptr = ptr.offset.{mode} %{base}, %{k}"));
        f
    }

    /// The pointer to access slot `s` through (noting the access): `s` itself, or, for a struct
    /// field, sometimes a pointer made here, from the struct or from another field in scope.
    fn addr(&mut self, s: &str) -> String {
        let Some((st, off)) = self.fields.get(s).cloned() else {
            self.accessed.insert(s.to_owned());
            return s.to_owned();
        };
        self.accessed.insert(st.clone());
        self.structs.insert(st.clone());
        let a = if self.rng.chance(35) {
            let siblings: Vec<(String, u64)> = self
                .slots
                .iter()
                .filter_map(|(f, _)| {
                    self.fields
                        .get(f)
                        .filter(|x| x.0 == st)
                        .map(|x| (f.clone(), x.1))
                })
                .collect();
            if !siblings.is_empty() && self.rng.chance(40) {
                let (f, o) = siblings[self.rng.below(siblings.len() as u64) as usize].clone();
                self.offset_ptr(&f, off as i64 - o as i64)
            } else {
                self.field_ptr(&st, off)
            }
        } else {
            s.to_owned()
        };
        self.field_addrs.insert(a.clone());
        a
    }

    fn store(&mut self, s: &str, t: T) {
        let v = self.val(t);
        let a = self.addr(s);
        self.line(&format!(
            "mem.store {} {v}, %{a}, align {}",
            t.name(),
            t.align()
        ));
    }

    fn load(&mut self, s: &str, t: T) -> String {
        let a = self.addr(s);
        self.def(t, &format!("mem.load %{a}, align {}", t.align()))
    }

    /// Pass a value to an event: integers widened to `i64`, floats as their bits.
    fn out(&mut self, v: &str, t: T) {
        let w = match t {
            T::P => {
                self.line(&format!("func.call @outp({v})"));
                return;
            }
            T::I64 => v.to_owned(),
            T::I8 | T::I16 | T::I32 => self.def(T::I64, &format!("int.sext {v}")),
            T::F64 => self.def(T::I64, &format!("float.to_bits {v}")),
            T::F32 => {
                let b = self.def(T::I32, &format!("float.to_bits {v}"));
                self.def(T::I64, &format!("int.sext {b}"))
            }
        };
        self.line(&format!("func.call @out({w})"));
    }

    fn stmts(&mut self) {
        let n = 1 + self.rng.below(5);
        for _ in 0..n {
            if self.budget <= 0 {
                break;
            }
            self.stmt();
        }
    }

    fn stmt(&mut self) {
        self.budget -= 1;
        let nested = self.depth < 4 && self.budget > 3;
        match self.rng.below(100) {
            0..=14 => {
                let t = self.rng.pick(&TYS);
                match t {
                    T::P => {
                        let v = self.val(T::P);
                        self.out(&v, T::P);
                    }
                    T::F32 | T::F64 => {
                        let (x, y) = (self.val(t), self.val(t));
                        let op = self.rng.pick(&["add", "sub", "mul"]);
                        self.def(t, &format!("float.{op} {x}, {y}"));
                    }
                    _ => match self.rng.below(3) {
                        0 if t != T::I64 => {
                            let x = self.val(T::I64);
                            self.def(t, &format!("int.trunc.wrap {x}"));
                        }
                        1 if t != T::I64 => {
                            let x = self.val(t);
                            self.def(T::I64, &format!("int.sext {x}"));
                        }
                        _ => {
                            let (x, y) = (self.val(t), self.val(t));
                            let op = self.rng.pick(&[
                                "int.add.wrap",
                                "int.sub.wrap",
                                "int.mul.wrap",
                                "int.xor",
                                "int.and",
                                "int.or",
                            ]);
                            self.def(t, &format!("{op} {x}, {y}"));
                        }
                    },
                }
            }
            15..=36 if !self.slots.is_empty() => {
                let (s, t) = self.slots[self.rng.below(self.slots.len() as u64) as usize].clone();
                self.store(&s, t);
            }
            37..=58 if !self.slots.is_empty() => {
                let (s, t) = self.slots[self.rng.below(self.slots.len() as u64) as usize].clone();
                let v = self.load(&s, t);
                if self.rng.chance(40) {
                    self.out(&v, t);
                }
            }
            59..=68 => {
                let t = self.rng.pick(&TYS);
                let v = self.val(t);
                self.out(&v, t);
            }
            69..=72 if self.callee => {
                let x = self.val(T::I64);
                self.def(T::I64, &format!("func.call @f1({x})"));
            }
            73..=76 if !self.others.is_empty() => {
                let q = self.others[self.rng.below(self.others.len() as u64) as usize].clone();
                if self.rng.chance(50) {
                    let v = self.val(T::I64);
                    self.line(&format!("mem.store i64 {v}, %{q}, align 8"));
                } else {
                    let v = self.def(T::I32, &format!("mem.load %{q}, align 4"));
                    self.out(&v, T::I32);
                }
            }
            77..=79 if self.depth > 0 => self.slot(85),
            80..=87 if nested => self.if_(),
            88..=93 if nested => self.loop_(),
            94..=99 if nested => self.blocks(),
            _ => {
                let t = self.rng.pick(&INTS);
                let x = self.val(t);
                self.def(t, &format!("int.add.wrap {x}, {x}"));
            }
        }
    }

    /// Run `f` in a new scope one level deeper, inside context `c`.
    fn scoped(&mut self, c: Ctx, f: impl FnOnce(&mut Gen)) {
        let (nv, ns) = (self.vals.len(), self.slots.len());
        self.ctx.push(c);
        self.indent += 1;
        self.depth += 1;
        f(self);
        self.depth -= 1;
        self.indent -= 1;
        self.ctx.pop();
        self.vals.truncate(nv);
        self.slots.truncate(ns);
    }

    fn nearest_loop(&self) -> Option<(Vec<T>, String, Vec<T>)> {
        self.ctx.iter().rev().find_map(|c| match c {
            Ctx::Loop {
                results,
                next,
                state,
            } => Some((results.clone(), next.clone(), state.clone())),
            _ => None,
        })
    }

    fn nearest_block(&self) -> Option<(Blocks, usize, String)> {
        self.ctx.iter().rev().find_map(|c| match c {
            Ctx::Block {
                blocks,
                index,
                next,
                ..
            } => Some((blocks.clone(), *index, next.clone())),
            _ => None,
        })
    }

    /// The arguments of a jump to block `j` of the nearest `cf.blocks`.
    fn jump(&mut self, blocks: &[(String, Option<T>)], j: usize, next: &str) -> String {
        let (l, extra) = blocks[j - 1].clone();
        match extra {
            Some(t) => {
                let v = self.val(t);
                format!("^{l}({next}, {v})")
            }
            None => format!("^{l}({next})"),
        }
    }

    /// Sometimes leave the region another way than its own: `cf.break` or `cf.continue` of the
    /// nearest loop, a forward jump in the nearest `cf.blocks`, or `func.ret`. Whether it did.
    fn escape(&mut self) -> bool {
        match self.rng.below(100) {
            0..=4 => {
                let v = self.val(T::I64);
                self.line(&format!("func.ret {v}"));
                true
            }
            5..=9 if self.nearest_loop().is_some() => {
                let (results, _, _) = self.nearest_loop().unwrap();
                let vs = self.vals_of(&results);
                self.line(&format!("cf.break {vs}"));
                true
            }
            10..=14 if self.nearest_loop().is_some() => {
                let (_, next, state) = self.nearest_loop().unwrap();
                let vs = self.vals_of(&state);
                let sep = if vs.is_empty() { "" } else { ", " };
                self.line(&format!("cf.continue {next}{sep}{vs}"));
                true
            }
            15..=24 => match self.nearest_block() {
                Some((blocks, i, next)) if i < blocks.len() => {
                    let j = i + 1 + self.rng.below((blocks.len() - i) as u64) as usize;
                    let target = self.jump(&blocks, j, &next);
                    self.line(&format!("cf.br {target}"));
                    true
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn if_(&mut self) {
        let c = self.cond();
        let ts = if self.rng.chance(50) {
            Vec::new()
        } else {
            self.types(2)
        };
        // The results are defined after the regions: keep them out of scope until then.
        let n = self.vals.len();
        let rs = self.results(&ts);
        let defs: Vec<(String, T)> = self.vals.drain(n..).collect();
        self.line(&format!("{rs}cf.if {c} {{"));
        for i in 0..2 {
            if i == 1 {
                self.line("} else {");
            }
            let ts = ts.clone();
            self.scoped(Ctx::If, |g| {
                g.stmts();
                if g.escape() {
                    return;
                }
                if !ts.is_empty() || g.rng.chance(60) {
                    let vs = g.vals_of(&ts);
                    g.line(format!("cf.yield {vs}").trim_end());
                }
            });
        }
        self.line("}");
        self.vals.extend(defs);
    }

    fn loop_(&mut self) {
        let bound = if self.rng.chance(30) {
            let a = self.val(T::I64);
            let three = self.def(T::I64, "int.const 3");
            self.def(T::I64, &format!("int.and {a}, {three}"))
        } else {
            let k = self.rng.below(4);
            self.def(T::I64, &format!("int.const {k}"))
        };
        let results = self.types(2);
        let state = self.types(2);
        let k = self.name("k");
        let mut iter = vec![format!("%{k}: i64 = %zero")];
        let mut params = Vec::new();
        for &t in &state {
            let init = self.val(t);
            let p = self.name("s");
            iter.push(format!("%{p}: {} = {init}", t.name()));
            params.push((p, t));
        }
        let n = self.vals.len();
        let rs = self.results(&results);
        let defs: Vec<(String, T)> = self.vals.drain(n..).collect();
        self.line(&format!("{rs}cf.loop iter({}) {{", iter.join(", ")));
        self.indent += 1;
        let (nv, ns) = (self.vals.len(), self.slots.len());
        self.vals.push((k.clone(), T::I64));
        self.vals.extend(params);
        let done = self.def_i1(&format!("int.cmp.sge %{k}, {bound}"));
        self.line(&format!("cf.if {done} {{"));
        let inner = self.vals.len();
        self.indent += 1;
        let vs = self.vals_of(&results);
        self.line(format!("cf.break {vs}").trim_end());
        self.indent -= 1;
        self.vals.truncate(inner);
        self.line("} else {");
        self.line("}");
        let next = self.def(T::I64, &format!("int.add.wrap %{k}, %one"));
        if self.rng.chance(30) {
            self.slot(80);
        }
        self.indent -= 1;
        self.scoped(
            Ctx::Loop {
                results: results.clone(),
                next: next.clone(),
                state: state.clone(),
            },
            |g| {
                g.stmts();
                if g.escape() {
                    return;
                }
                if g.rng.chance(85) {
                    let vs = g.vals_of(&state);
                    let sep = if vs.is_empty() { "" } else { ", " };
                    g.line(&format!("cf.continue {next}{sep}{vs}"));
                } else {
                    let vs = g.vals_of(&results);
                    g.line(format!("cf.break {vs}").trim_end());
                }
            },
        );
        self.vals.truncate(nv);
        self.slots.truncate(ns);
        self.line("}");
        self.vals.extend(defs);
    }

    fn blocks(&mut self) {
        let results = self.types(2);
        let nblocks = 1 + self.rng.below(3) as usize;
        let blocks: Vec<(String, Option<T>)> = (0..nblocks)
            .map(|_| {
                let l = self.name("b");
                let extra = self.rng.chance(40).then(|| self.rng.pick(&TYS));
                (l, extra)
            })
            .collect();
        let n = self.vals.len();
        let rs = self.results(&results);
        let defs: Vec<(String, T)> = self.vals.drain(n..).collect();
        self.line(&format!("{rs}cf.blocks {{"));
        for i in 0..=nblocks {
            let (nv, ns) = (self.vals.len(), self.slots.len());
            let next = if i == 0 {
                let e = self.name("e");
                self.line(&format!("^{e}:"));
                "%zero".to_owned()
            } else {
                let (l, extra) = blocks[i - 1].clone();
                let c = self.name("n");
                let mut ps = format!("%{c}: i64");
                self.vals.push((c.clone(), T::I64));
                if let Some(t) = extra {
                    let x = self.name("x");
                    write!(ps, ", %{x}: {}", t.name()).unwrap();
                    self.vals.push((x, t));
                }
                self.line(&format!("^{l}({ps}):"));
                self.indent += 1;
                let next = self.def(T::I64, &format!("int.add.wrap %{c}, %one"));
                if self.rng.chance(30) {
                    // A back edge, bounded by the counter, from a nested cf.if.
                    let lim = self.def(T::I64, "int.const 3");
                    let g = self.def_i1(&format!("int.cmp.slt {next}, {lim}"));
                    let j = 1 + self.rng.below(i as u64) as usize;
                    self.line(&format!("cf.if {g} {{"));
                    let inner = self.vals.len();
                    self.indent += 1;
                    let target = self.jump(&blocks, j, &next);
                    self.line(&format!("cf.br {target}"));
                    self.indent -= 1;
                    self.vals.truncate(inner);
                    self.line("} else {");
                    self.line("}");
                }
                if self.rng.chance(25) {
                    self.slot(85);
                }
                self.indent -= 1;
                next
            };
            let ctx = Ctx::Block {
                blocks: blocks.clone(),
                index: i,
                next: next.clone(),
            };
            let results = results.clone();
            let blocks = blocks.clone();
            self.scoped(ctx, |g| {
                g.stmts();
                if g.escape() {
                    return;
                }
                let forward = i < nblocks;
                let pick = |g: &mut Gen| i + 1 + g.rng.below((nblocks - i) as u64) as usize;
                match g.rng.below(100) {
                    0..=29 if forward => {
                        let j = pick(g);
                        let t = g.jump(&blocks, j, &next);
                        g.line(&format!("cf.br {t}"));
                    }
                    30..=54 if forward => {
                        let c = g.cond();
                        let (j, k) = (pick(g), pick(g));
                        let (tj, tk) = (g.jump(&blocks, j, &next), g.jump(&blocks, k, &next));
                        g.line(&format!("cf.cond_br {c}, {tj}, {tk}"));
                    }
                    55..=74 if forward => {
                        let t = g.rng.pick(&INTS);
                        let v = g.val(t);
                        let d = pick(g);
                        let dt = g.jump(&blocks, d, &next);
                        let mut cases = Vec::new();
                        let ncases = 1 + g.rng.below(3);
                        let mut keys: Vec<i64> = vec![0, 1, 2, 3, 5, -1, 7];
                        for _ in 0..ncases {
                            let key = keys.remove(g.rng.below(keys.len() as u64) as usize);
                            let j = pick(g);
                            let tj = g.jump(&blocks, j, &next);
                            cases.push(format!("{key}: {tj}"));
                        }
                        g.line(&format!(
                            "cf.switch {v}, default {dt}, [{}]",
                            cases.join(", ")
                        ));
                    }
                    _ => {
                        let vs = g.vals_of(&results);
                        g.line(format!("cf.yield {vs}").trim_end());
                    }
                }
            });
            self.vals.truncate(nv);
            self.slots.truncate(ns);
        }
        self.line("}");
        self.vals.extend(defs);
    }

    /// A function `@name(params) -> i64`.
    fn func(&mut self, name: &str, params: &[&str], budget: i32) {
        self.vals.clear();
        self.slots.clear();
        self.others.clear();
        self.budget = budget;
        let ps: Vec<String> = params.iter().map(|p| format!("%{p}: i64")).collect();
        writeln!(self.out, "func @{name}({}) -> i64 {{", ps.join(", ")).unwrap();
        self.indent = 1;
        for p in params {
            self.vals.push(((*p).to_owned(), T::I64));
        }
        self.line("%zero: i64 = int.const 0");
        self.line("%one: i64 = int.const 1");
        self.line("%buf: ptr = mem.stack 16, align 8");
        self.line("func.call @esc(%buf)");
        for _ in 0..2 + self.rng.below(5) {
            self.slot(90);
        }
        for _ in 0..self.rng.below(3) {
            let q = self.name("q");
            self.line(&format!("%{q}: ptr = mem.stack.of i64, align 8"));
            if self.rng.chance(50) {
                self.line(&format!("func.call @esc(%{q})"));
            }
            let v = self.val(T::I64);
            self.line(&format!("mem.store i64 {v}, %{q}, align 8"));
            // Read with another type, so it isn't promotable even if it doesn't escape.
            let r = self.def(T::I32, &format!("mem.load %{q}, align 4"));
            self.out(&r, T::I32);
            self.others.push(q);
        }
        if self.rng.chance(30) {
            // A struct whose second field's pointer escapes: none of it is promotable.
            let q = self.name("q");
            self.line(&format!(
                "%{q}: ptr = mem.stack.of struct<C>{{i64, i64}}, align 8"
            ));
            let f0 = self.field_ptr(&q, 0);
            let f1 = self.field_ptr(&q, 8);
            self.line(&format!("func.call @esc(%{f1})"));
            let v = self.val(T::I64);
            self.line(&format!("mem.store i64 {v}, %{f0}, align 8"));
            let r = self.def(T::I64, &format!("mem.load %{f0}, align 8"));
            self.out(&r, T::I64);
            self.others.push(f0);
            self.others.push(f1);
        }
        self.stmts();
        while self.budget > 0 {
            self.stmt();
        }
        let v = match self.slots.iter().find(|s| s.1 == T::I64).cloned() {
            Some((s, t)) if self.rng.chance(70) => self.load(&s, t),
            _ => self.val(T::I64),
        };
        self.line(&format!("func.ret {v}"));
        self.out.push_str("}\n\n");
    }
}

fn generate(seed: u64) -> Prog {
    let mut g = Gen {
        rng: Rng(seed),
        out: String::from(
            "extern func @out(i64) effects[] assume\n\
             extern func @outp(ptr) effects[] assume\n\
             extern func @esc(ptr) effects[read(args), write(args)] assume\n\n",
        ),
        indent: 0,
        fresh: 0,
        vals: Vec::new(),
        slots: Vec::new(),
        others: Vec::new(),
        ctx: Vec::new(),
        budget: 0,
        depth: 0,
        accessed: HashSet::new(),
        fields: HashMap::new(),
        field_addrs: HashSet::new(),
        structs: HashSet::new(),
        callee: false,
    };
    let mut slots = Vec::new();
    let mut others = Vec::new();
    let callee = g.rng.chance(40);
    if callee {
        g.func("f1", &["x"], 10);
        g.callee = true;
        others.extend(g.others.clone());
    }
    let budget = 15 + g.rng.below(40) as i32;
    g.func("f0", &["a", "b"], budget);
    others.extend(g.others.clone());
    // Every `%pN` the generator made.
    for i in 1..=g.fresh {
        let s = format!("p{i}");
        if g.out.contains(&format!("%{s}: ptr = mem.stack.of")) {
            slots.push(s);
        }
    }
    slots.extend(g.field_addrs.iter().cloned());
    let mut runs = vec![vec!["0".to_owned(), "0".to_owned()]];
    for _ in 0..3 {
        let a = g.rng.pick(&[1i64, 2, 3, -1, 7, 100, -5]);
        let b = g.rng.pick(&[0i64, 1, 3, -2, 9, 1000]);
        runs.push(vec![a.to_string(), b.to_string()]);
    }
    Prog {
        text: g.out,
        promotable: g.accessed.len(),
        structs: g.structs.len(),
        slots,
        others,
        runs,
    }
}

// Checking one program.

fn pipeline(spec: &str, fixpoint: bool) -> Pipeline {
    let mut p = Pipeline::parse_experimental(spec).unwrap();
    p.verify_each = true;
    if fixpoint {
        p.fixpoint = true;
        p.max_rounds = 16;
    }
    p
}

/// Run `spec` on a copy of `m`; the result, and the changes `pass` made. The result must verify,
/// and print and parse back to the same text.
fn optimize(m: &fir::Module, spec: &str, fixpoint: bool) -> Result<(fir::Module, u64), String> {
    let mut out = m.clone();
    let report = pipeline(spec, fixpoint)
        .run(&mut out, &mut Remarks::new(false))
        .map_err(|e| e.to_string())?;
    fir::verify_module(&out).map_err(|e| format!("the result doesn't verify: {e}"))?;
    let text = out.render(true);
    let back =
        fir::parse_module(&text).map_err(|e| format!("the result doesn't parse back: {e}"))?;
    fir::verify_module(&back).map_err(|e| format!("the result doesn't verify as text: {e}"))?;
    if back.render(true) != text {
        return Err("the result doesn't print back the same".into());
    }
    Ok((out, report.changes_by("mem2reg")))
}

/// How many accesses (loads and stores) through the slot `%s` the text has.
fn accesses(text: &str, s: &str) -> usize {
    let (load, store) = (format!("mem.load %{s},"), format!(", %{s}, align"));
    text.lines()
        .filter(|l| l.contains(&load) || (l.contains("mem.store") && l.contains(&store)))
        .count()
}

/// Whether `line` names a value threaded for a slot (`%p3.1`).
fn threads(line: &str) -> bool {
    line.match_indices("%p").any(|(i, _)| {
        let rest = &line[i + 2..];
        let d = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        d > 0 && rest[d..].starts_with('.')
    })
}

#[derive(Default)]
struct Stats {
    programs: u64,
    promoted: u64,
    structs: u64,
    deleted_slots: u64,
    /// Ops of each kind that carry a promoted slot's value.
    threaded: BTreeMap<&'static str, u64>,
    exact: BTreeMap<Cmp, u64>,
    renamed: BTreeMap<Cmp, u64>,
    native: BTreeMap<&'static str, u64>,
    fails: Vec<String>,
}

fn check(i: u64, seed: u64, tc: Option<&Toolchain>, dir: &Path, stats: &Mutex<Stats>) {
    let prog = generate(seed.wrapping_mul(1_000_003).wrapping_add(i));
    let name = format!("s{seed}-p{i}");
    let fail = |e: String, extra: &str| {
        let path = dir.join(format!("{name}.fir"));
        std::fs::write(&path, format!("{}{extra}", prog.text)).unwrap();
        stats
            .lock()
            .unwrap()
            .fails
            .push(format!("{}: {e}", path.display()));
    };
    let m = match fir::parse_module(&prog.text) {
        Ok(m) => m,
        Err(e) => {
            return fail(
                format!("the generator wrote a program that doesn't parse: {e}"),
                "",
            );
        }
    };
    if let Err(e) = fir::verify_module(&m) {
        return fail(
            format!("the generator wrote a program that doesn't verify: {e}"),
            "",
        );
    }
    let (one, n) = match optimize(&m, "mem2reg", false) {
        Ok(x) => x,
        Err(e) => return fail(format!("mem2reg: {e}"), ""),
    };
    let text = one.render(false);
    let after = format!("\n// ---- after mem2reg ----\n/*\n{text}*/\n");
    if n != prog.promotable as u64 {
        return fail(
            format!("mem2reg promoted {n} slots, not the {}", prog.promotable),
            &after,
        );
    }
    let before = m.render(false);
    for s in &prog.slots {
        if accesses(&text, s) != 0 {
            return fail(format!("%{s} still has accesses after mem2reg"), &after);
        }
    }
    for q in &prog.others {
        if accesses(&text, q) != accesses(&before, q) {
            return fail(format!("mem2reg changed the accesses of %{q}"), &after);
        }
    }
    match optimize(&one, "mem2reg", false) {
        Ok((_, 0)) => {}
        Ok((_, n)) => return fail(format!("a second mem2reg promoted {n} more"), &after),
        Err(e) => return fail(format!("a second mem2reg: {e}"), &after),
    }
    let (full, _) = match optimize(&m, FULL, true) {
        Ok(x) => x,
        Err(e) => return fail(format!("{FULL}: {e}"), &after),
    };
    let mut threaded = BTreeMap::new();
    for l in text.lines().filter(|l| threads(l)) {
        let kind = if l.contains("cf.loop") {
            "cf.loop state"
        } else if l.contains("cf.if") {
            "cf.if results"
        } else if l.contains("cf.blocks") {
            "cf.blocks results"
        } else if l.trim_start().starts_with('^') {
            "block parameters"
        } else {
            continue;
        };
        *threaded.entry(kind).or_insert(0) += 1;
    }
    let mut exact = Vec::new();
    let mut renamed = Vec::new();
    for args in &prog.runs {
        let s = run(&m, args);
        let (t1, t2) = (run(&one, args), run(&full, args));
        match refines(&t1, &s) {
            Ok(c) => exact.push(c),
            Err(e) => {
                return fail(
                    format!(
                        "mem2reg: @f0({}): {e}\n  original:  {s:?}\n  promoted:  {t1:?}",
                        args.join(", ")
                    ),
                    &after,
                );
            }
        }
        let rn = |r: &Result<String, String>| r.clone().map(|l| rename_allocs(&l));
        match refines(&rn(&t2), &rn(&s)) {
            Ok(c) => renamed.push(c),
            Err(e) => {
                let full_text = format!(
                    "\n// ---- after {FULL} ----\n/*\n{}*/\n",
                    full.render(false)
                );
                return fail(
                    format!(
                        "{FULL}: @f0({}): {e}\n  original:  {s:?}\n  optimized: {t2:?}",
                        args.join(", ")
                    ),
                    &full_text,
                );
            }
        }
    }
    let deleted =
        before.matches("mem.stack").count() - full.render(false).matches("mem.stack").count();
    let mut native = Vec::new();
    if let Some(tc) = tc
        && i.is_multiple_of(5)
    {
        let (spec, fixpoint) = if i.is_multiple_of(10) {
            ("mem2reg", false)
        } else {
            (FULL, true)
        };
        match native_runs(tc, &m, &prog.runs, spec, fixpoint, dir, &name) {
            Ok(v) => native = v,
            Err(e) => return fail(format!("native, {spec}: {e}"), &after),
        }
    }
    let mut st = stats.lock().unwrap();
    st.programs += 1;
    st.promoted += n;
    st.deleted_slots += deleted as u64;
    st.structs += prog.structs as u64;
    for (k, v) in threaded {
        *st.threaded.entry(k).or_insert(0) += v;
    }
    for c in exact {
        *st.exact.entry(c).or_insert(0) += 1;
    }
    for c in renamed {
        *st.renamed.entry(c).or_insert(0) += 1;
    }
    for k in native {
        *st.native.entry(k).or_insert(0) += 1;
    }
}

// Native runs.

struct Toolchain {
    cc: String,
    runner: Option<String>,
}

fn on_path(name: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
}

fn toolchain() -> Result<Toolchain, String> {
    let native = cfg!(target_arch = "aarch64");
    let cc = match std::env::var("FIR_CC") {
        Ok(cc) => cc,
        Err(_) if native => "cc".to_owned(),
        Err(_) if on_path("aarch64-unknown-linux-gnu-cc") => {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
        Err(_) => return Err("no AArch64 C compiler (set FIR_CC, or use the dev shell)".into()),
    };
    let runner = if native {
        None
    } else if on_path("qemu-aarch64") {
        Some("qemu-aarch64".to_owned())
    } else {
        return Err("no qemu-aarch64 to run AArch64 binaries".into());
    };
    Ok(Toolchain { cc, runner })
}

/// `main` and the external functions, printing as `fir run` does (pointers as `?`).
fn harness(runs: &[Vec<String>]) -> String {
    let mut s = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n\
         struct fir_exn { void *flag; void *value; } __fir_exn;\n\
         void __fir_trap(uint32_t r, uint32_t l, uint32_t c) { printf(\"trap\\n\"); exit(0); }\n\
         int64_t fir_f0(int64_t, int64_t);\n\
         void fir_ext_out(int64_t x) { printf(\"@out(i64 %lld) -> (); \", (long long)x); }\n\
         void fir_ext_outp(void *p) { printf(p ? \"@outp(ptr ?) -> (); \" : \"@outp(ptr null) -> (); \"); }\n\
         void fir_ext_esc(void *p) { printf(p ? \"@esc(ptr ?) -> (); \" : \"@esc(ptr null) -> (); \"); }\n\
         static const long long args[][2] = {",
    );
    for r in runs {
        write!(s, "{{{}LL, {}LL}}, ", r[0], r[1]).unwrap();
    }
    s.push_str(
        "};\nint main(int argc, char **argv) {\n  int k = atoi(argv[1]);\n  \
         long long r = fir_f0(args[k][0], args[k][1]);\n  \
         printf(\"returned i64 %lld\\n\", r);\n  return 0;\n}\n",
    );
    s
}

/// The reference line for a native run of `@f0`, normalized (pointers as `?`, no leak notes),
/// or `None` if the run can't be compared natively.
fn reference(m: &fir::Module, args: &[String]) -> Option<String> {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let r = fir::interp::run_detail_with(m, "f0", &args, FUEL, false, NanRule::Arm).ok()?;
    if r.absorbing || r.out_of_fuel || r.line.contains("ambiguous") {
        return None;
    }
    let mut out = Vec::new();
    for part in r.line.split("; ") {
        if part.starts_with("leak:") {
            continue;
        }
        let mut p = String::new();
        let mut rest = part;
        while let Some(i) = rest.find("ptr #") {
            p.push_str(&rest[..i]);
            p.push_str("ptr ?");
            rest = rest[i + 5..].trim_start_matches(|c: char| c.is_ascii_digit() || c == '+');
        }
        p.push_str(rest);
        out.push(p);
    }
    Some(out.join("; "))
}

/// Whether native output `got` matches reference `want`, where `poison` matches anything.
fn matches_native(want: &str, got: &str) -> bool {
    let (w, g): (Vec<&str>, Vec<&str>) = (want.split(' ').collect(), got.split(' ').collect());
    w.len() == g.len()
        && w.iter().zip(&g).all(|(w, g)| {
            w == g
                || w.strip_prefix("poison")
                    .is_some_and(|tail| g.ends_with(tail))
        })
}

/// Compile `m` with the pipeline `spec`, run it natively for each run, and compare with the
/// interpreter's run of `m`. The categories of the runs.
fn native_runs(
    tc: &Toolchain,
    m: &fir::Module,
    runs: &[Vec<String>],
    spec: &str,
    fixpoint: bool,
    dir: &Path,
    name: &str,
) -> Result<Vec<&'static str>, String> {
    let lowered = fir::backend::prepare_with(m, Some(&pipeline(spec, fixpoint)))?;
    let o = a64::Options {
        os: a64::Os::host(),
        prefix: "fir_".to_owned(),
        extern_prefix: "fir_ext_".to_owned(),
        debug_lines: false,
    };
    let asm = a64::compile(&lowered, &o)?;
    let (s, c, bin) = (
        dir.join(format!("{name}.s")),
        dir.join(format!("{name}.c")),
        dir.join(name),
    );
    std::fs::write(&s, asm).unwrap();
    std::fs::write(&c, harness(runs)).unwrap();
    let out = Command::new(&tc.cc)
        .args(["-O0", "-w"])
        .arg(&c)
        .arg(&s)
        .arg("-o")
        .arg(&bin)
        .output()
        .map_err(|e| format!("running {}: {e}", tc.cc))?;
    if !out.status.success() {
        return Err(format!(
            "linking failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let mut cats = Vec::new();
    for (k, args) in runs.iter().enumerate() {
        let Some(want) = reference(m, args) else {
            cats.push("not comparable");
            continue;
        };
        let mut cmd = match &tc.runner {
            Some(r) => {
                let mut c = Command::new(r);
                c.arg(&bin);
                c
            }
            None => Command::new(&bin),
        };
        let out = cmd
            .arg(k.to_string())
            .output()
            .map_err(|e| format!("running {}: {e}", bin.display()))?;
        let got = String::from_utf8_lossy(&out.stdout).trim_end().to_owned();
        if !out.status.success() || !matches_native(&want, &got) {
            return Err(format!(
                "@f0({}): the interpreter gives {want:?}, the native run {got:?} ({:?})",
                args.join(", "),
                out.status.code()
            ));
        }
        cats.push("equal");
    }
    for p in [&s, &c, &bin] {
        let _ = std::fs::remove_file(p);
    }
    Ok(cats)
}

#[test]
fn promoted_random_programs_refine_the_originals() {
    let count = env_u64("FIR_FUZZ", 500);
    let seed = env_u64("FIR_FUZZ_SEED", 1);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("mem2reg");
    std::fs::create_dir_all(&dir).unwrap();
    let tc = if std::env::var("FIR_MEM2REG_NATIVE").is_ok_and(|v| v == "0") {
        None
    } else {
        Some(toolchain().unwrap_or_else(|e| panic!("{e}; FIR_MEM2REG_NATIVE=0 skips native runs")))
    };
    let stats = Mutex::new(Stats::default());
    let next = AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed) as u64;
                    if i >= count {
                        break;
                    }
                    check(i, seed, tc.as_ref(), &dir, &stats);
                }
            });
        }
    });
    let st = stats.into_inner().unwrap();
    eprintln!(
        "{} programs (seed {seed}); {} slots promoted ({} structs, field by field), {} stack \
         allocations deleted by {FULL}",
        st.programs, st.promoted, st.structs, st.deleted_slots
    );
    eprintln!("values threaded for promoted slots:");
    for (k, n) in &st.threaded {
        eprintln!("  {n:8}  {k}");
    }
    eprintln!("runs after mem2reg:");
    for (c, n) in &st.exact {
        eprintln!("  {n:8}  {c:?}");
    }
    eprintln!("runs after {FULL} (allocations renamed):");
    for (c, n) in &st.renamed {
        eprintln!("  {n:8}  {c:?}");
    }
    eprintln!("native runs:");
    for (c, n) in &st.native {
        eprintln!("  {n:8}  {c}");
    }
    assert!(
        st.fails.is_empty(),
        "{} failures:\n{}",
        st.fails.len(),
        st.fails.join("\n")
    );
    let total: u64 = st.exact.values().sum();
    let equal = st.exact.get(&Cmp::Equal).copied().unwrap_or(0);
    assert!(
        st.promoted >= st.programs * 2,
        "too few promotions: {}",
        st.promoted
    );
    assert!(
        equal * 10 >= total * 7,
        "too few defined runs: {equal} of {total}"
    );
    for k in [
        "cf.if results",
        "cf.loop state",
        "cf.blocks results",
        "block parameters",
    ] {
        if st.programs >= 100 {
            assert!(
                st.threaded.get(k).is_some_and(|&n| n > 0),
                "nothing threaded as {k}"
            );
        }
    }
    if tc.is_some() && st.programs >= 100 {
        assert!(st.native.get("equal").is_some_and(|&n| n > 0));
    }
}

// Focused cases.

/// Promote `src` with `mem2reg` alone; the text without locations, and how many it promoted.
/// Each `(args)` run of the result must be the same as the original's.
fn promote(src: &str, f: &str, runs: &[&[&str]]) -> (String, u64) {
    let m = fir::parse_module(src).unwrap();
    fir::verify_module(&m).unwrap();
    let (out, n) = optimize(&m, "mem2reg", false).unwrap();
    for args in runs {
        let (s, t) = (
            fir::interp::run(&m, f, args, FUEL),
            fir::interp::run(&out, f, args, FUEL),
        );
        assert_eq!(s, t, "@{f}({args:?})\n{}", out.render(false));
        assert!(s.as_ref().is_ok_and(|l| l.contains("returned")), "{s:?}");
    }
    (out.render(false), n)
}

/// A `cf.if` without results whose region falls off its end gets results, and so a `cf.yield`;
/// a slot made in a block is made again each time the block runs.
#[test]
fn if_without_yield_and_a_slot_in_a_block() {
    let src = "func @fresh() -> i32 {
  %zero: i1 = int.const 0
  %one: i1 = int.const 1
  %r: i32 = cf.blocks {
  ^entry:
    cf.br ^a(%zero)
  ^a(%again: i1):
    %p: ptr = mem.stack 4, align 4
    cf.if %again {
    } else {
      %seven: i32 = int.const 7
      mem.store i32 %seven, %p, align 4
    }
    %v: i32 = mem.load %p, align 4
    cf.cond_br %again, ^done(%v), ^a(%one)
  ^done(%x: i32):
    cf.yield %x
  }
  func.ret %r
}
";
    let m = fir::parse_module(src).unwrap();
    // The second time through, %p is new and nothing was stored: poison.
    assert_eq!(
        fir::interp::run(&m, "fresh", &[], FUEL).unwrap(),
        "returned i32 poison"
    );
    let (out, n) = promote(src, "fresh", &[&[]]);
    assert_eq!(n, 1);
    assert_eq!(accesses(&out, "p"), 0, "{out}");
    assert!(out.contains("= poison"), "{out}");
    assert_eq!(out.matches("cf.yield").count(), 3, "{out}");
}

/// Cases of a `cf.switch` that share a target each pass the slot's value.
#[test]
fn switch_with_shared_targets() {
    let src = "func @f(%k: i32) -> i64 {
  %s: ptr = mem.stack.of i64, align 8
  %ten: i64 = int.const 10
  mem.store i64 %ten, %s, align 8
  %r: i64 = cf.blocks {
  ^entry:
    %v: i64 = mem.load %s, align 8
    %w: i64 = int.add.wrap %v, %v
    mem.store i64 %w, %s, align 8
    cf.switch %k, default ^d, [1: ^a, 2: ^a, 3: ^d, 4: ^b]
  ^a:
    %x: i64 = mem.load %s, align 8
    %one: i64 = int.const 1
    %y: i64 = int.add.wrap %x, %one
    mem.store i64 %y, %s, align 8
    cf.br ^b
  ^b:
    %z: i64 = mem.load %s, align 8
    cf.yield %z
  ^d:
    cf.yield %ten
  }
  %t: i64 = mem.load %s, align 8
  %u: i64 = int.add.wrap %r, %t
  func.ret %u
}
";
    let (out, n) = promote(src, "f", &[&["0"], &["1"], &["2"], &["3"], &["4"]]);
    assert_eq!(n, 1);
    assert_eq!(accesses(&out, "s"), 0, "{out}");
    assert!(out.contains("[1: ^a(%"), "{out}");
}

/// A slot made in a loop body is new each iteration: it isn't loop state.
#[test]
fn slot_inside_a_loop_body() {
    let src = "func @f(%n: i64) -> i64 {
  %zero: i64 = int.const 0
  %one: i64 = int.const 1
  %acc: ptr = mem.stack.of i64, align 8
  mem.store i64 %zero, %acc, align 8
  %r: i64 = cf.loop iter(%i: i64 = %zero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      %a: i64 = mem.load %acc, align 8
      cf.break %a
    } else {
    }
    %t: ptr = mem.stack.of i64, align 8
    mem.store i64 %i, %t, align 8
    %ti: i64 = mem.load %t, align 8
    %a2: i64 = mem.load %acc, align 8
    %b: i64 = int.add.wrap %a2, %ti
    mem.store i64 %b, %acc, align 8
    %j: i64 = int.add.wrap %i, %one
    cf.continue %j
  }
  func.ret %r
}
";
    let (out, n) = promote(src, "f", &[&["0"], &["4"]]);
    assert_eq!(n, 2);
    assert_eq!(accesses(&out, "acc") + accesses(&out, "t"), 0, "{out}");
    // Only %acc is loop state.
    let head = out.lines().find(|l| l.contains("cf.loop")).unwrap();
    assert_eq!(head.matches(": i64 =").count(), 3, "{head}");
}

/// `cf.break` from a block of a `cf.blocks` inside a loop gives the loop the slot's value.
#[test]
fn break_out_of_a_loop_from_inside_blocks() {
    let src = "func @f(%n: i64) -> i64 {
  %zero: i64 = int.const 0
  %one: i64 = int.const 1
  %s: ptr = mem.stack.of i64, align 8
  mem.store i64 %one, %s, align 8
  cf.loop iter(%i: i64 = %zero) {
    %j: i64 = int.add.wrap %i, %one
    cf.blocks {
    ^entry:
      %v: i64 = mem.load %s, align 8
      %w: i64 = int.mul.wrap %v, %j
      mem.store i64 %w, %s, align 8
      %c: i1 = int.cmp.sge %j, %n
      cf.cond_br %c, ^out, ^more
    ^out:
      cf.break
    ^more:
      cf.continue %j
    }
    cf.continue %j
  }
  %r: i64 = mem.load %s, align 8
  func.ret %r
}
";
    let (out, n) = promote(src, "f", &[&["1"], &["5"]]);
    assert_eq!(n, 1);
    assert_eq!(accesses(&out, "s"), 0, "{out}");
}

/// A slot stored in a `cf.blocks` whose entry block a branch targets stays in memory (an entry
/// block takes no parameters); one only read there is still promoted.
#[test]
fn targeted_entry_block_keeps_its_slots() {
    let src = "func @f() -> i64 {
  %zero: i64 = int.const 0
  %one: i64 = int.const 1
  %three: i64 = int.const 3
  %s: ptr = mem.stack.of i64, align 8
  %t: ptr = mem.stack.of i64, align 8
  mem.store i64 %zero, %s, align 8
  mem.store i64 %three, %t, align 8
  %r: i64 = cf.blocks {
  ^entry:
    %v: i64 = mem.load %s, align 8
    %v1: i64 = int.add.wrap %v, %one
    mem.store i64 %v1, %s, align 8
    %lim: i64 = mem.load %t, align 8
    %c: i1 = int.cmp.slt %v1, %lim
    cf.cond_br %c, ^entry, ^done
  ^done:
    %w: i64 = mem.load %s, align 8
    cf.yield %w
  }
  func.ret %r
}
";
    let m = fir::parse_module(src).unwrap();
    if let Err(e) = fir::verify_module(&m) {
        // If entry blocks can't be targeted, the case can't arise.
        assert!(e.contains("entry"), "{e}");
        return;
    }
    assert_eq!(
        fir::interp::run(&m, "f", &[], FUEL).unwrap(),
        "returned i64 3"
    );
    let (out, n) = promote(src, "f", &[&[]]);
    assert_eq!(n, 1, "{out}");
    assert_eq!(accesses(&out, "s"), 4, "{out}");
    assert_eq!(accesses(&out, "t"), 0, "{out}");
}

/// A struct's fields are promoted one by one, through pointers made anywhere, chains of
/// `ptr.offset`s included; the `ptr.offset`s stay for dead code elimination.
#[test]
fn struct_fields_are_promoted_one_by_one() {
    let src = "func @f(%x: i64, %y: f64) -> i64 {
  %s: ptr = mem.stack.of struct<C>{i32, f64, i64}, align 8
  %k8: i64 = int.const 8
  %k16: i64 = int.const 16
  %fy: ptr = ptr.offset.inbounds %s, %k8
  %fz: ptr = ptr.offset.inbounds %s, %k16
  %x32: i32 = int.trunc.wrap %x
  mem.store i32 %x32, %s, align 4
  mem.store f64 %y, %fy, align 8
  mem.store i64 %x, %fz, align 8
  %c: i1 = int.cmp.slt %x, %k8
  cf.if %c {
    %k: i64 = int.const 8
    %g: ptr = ptr.offset.wrap %fy, %k
    %v: i64 = mem.load %g, align 8
    %w: i64 = int.add.wrap %v, %v
    mem.store i64 %w, %g, align 8
  }
  %a: i32 = mem.load %s, align 4
  %z: i64 = mem.load %fz, align 8
  %a64: i64 = int.sext %a
  %r: i64 = int.add.wrap %a64, %z
  func.ret %r
}
";
    let (out, n) = promote(src, "f", &[&["3", "1.5"], &["100", "0.0"]]);
    assert_eq!(n, 1, "{out}");
    assert!(
        !out.contains("mem.load") && !out.contains("mem.store"),
        "{out}"
    );
    assert!(out.contains("%s.at16.1: i64 = cf.if"), "{out}");
}

/// Fields that overlap, one offset read with two types, and an offset that isn't a constant
/// keep the struct in memory.
#[test]
fn overlapping_or_unknown_fields_keep_the_struct() {
    for (what, body) in [
        (
            "overlap",
            "mem.store i64 %x, %s, align 8
  %k4: i64 = int.const 4
  %f: ptr = ptr.offset.inbounds %s, %k4
  %v: i32 = mem.load %f, align 4
  %r: i64 = int.sext %v",
        ),
        (
            "two types",
            "mem.store i64 %x, %s, align 8
  %v: f64 = mem.load %s, align 8
  %r: i64 = float.to_bits %v",
        ),
        (
            "variable offset",
            "mem.store i64 %x, %s, align 8
  %f: ptr = ptr.offset.inbounds %s, %x
  %r: i64 = mem.load %f, align 8",
        ),
    ] {
        let src = format!(
            "func @f(%x: i64) -> i64 {{
  %s: ptr = mem.stack.of struct<C>{{i64, i64}}, align 8
  {body}
  func.ret %r
}}
"
        );
        let (out, n) = promote(&src, "f", &[&["0"]]);
        assert_eq!(n, 0, "{what}: {out}");
        assert!(out.contains("mem.store"), "{what}: {out}");
    }
}

/// A field at a negative offset (out of bounds, so UB to reach) still gets a name the text can
/// spell: `%s.atm8`, not `%s.at-8`.
#[test]
fn negative_offsets_name_their_values() {
    let src = "func @f(%x: i64, %c: i1) -> i64 {
  %s: ptr = mem.stack.of struct<C>{i64, i64}, align 8
  %k: i64 = int.const -8
  %f: ptr = ptr.offset.wrap %s, %k
  cf.if %c {
    mem.store i64 %x, %f, align 8
    cf.yield
  } else {
    cf.yield
  }
  mem.store i64 %x, %s, align 8
  %v: i64 = mem.load %f, align 8
  %w: i64 = mem.load %s, align 8
  %r: i64 = int.add.wrap %v, %w
  func.ret %r
}
";
    let m = fir::parse_module(src).unwrap();
    fir::verify_module(&m).unwrap();
    let (out, n) = optimize(&m, "mem2reg", false).unwrap();
    assert_eq!(n, 1);
    assert!(
        out.render(false).contains("%s.atm8.1"),
        "{}",
        out.render(false)
    );
}
