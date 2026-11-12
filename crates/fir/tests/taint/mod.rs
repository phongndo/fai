//! Which outcomes of a module's runs may depend on addresses, which the interpreter and the
//! hardware choose differently: a taint analysis over an MFIR module, and the comparison that
//! uses it to excuse only those differences.
//!
//! **Sources.** `ptr.addr` and `ptr.expose` of a pointer that may be non-null, `ptr.cmp` of two
//! pointers that may both be non-null (across allocations the answer is a choice),
//! `ptr.from_exposed` and `ptr.with_addr` (which allocation the address finds is the oracle's),
//! and integer or float loads from memory that may hold pointer bytes. `freeze` of what may be
//! `poison` is the oracle's choice as well (the interpreter's is 0, the hardware keeps what the
//! register holds), so the analysis also tracks what may be `poison`: `poison`, `.nsw`/`.nuw`
//! arithmetic and truncation, in-bounds pointer arithmetic, uninitialized memory, and
//! arguments (a run may pass `poison`).
//!
//! **Memory.** Each value carries the abstract objects it may point into (an allocation-site
//! points-to set: a global, a `mem.stack`/`mem.stack.of`/`mem.alloc` op, or *wild*, any object)
//! and whether it may carry pointer bytes. Each object records whether it may hold pointer bytes
//! (stores of possibly non-null pointers or of bytes that may be pointers, copies, and globals
//! whose initializers name addresses: not every aggregate global), the objects those pointers
//! point into, and whether its contents are tainted. A tainted pointer may point anywhere, so
//! loads through it are tainted and stores through it write the wild object, which every load
//! reads.
//!
//! **Flow.** Taint propagates through every op's operands to its results, through region and
//! block parameters from the terminators that reach them (`cf.yield`, `cf.break`,
//! `cf.continue`, `cf.br`, `cf.cond_br`, `cf.switch`) and the loop's initial state, through calls
//! (arguments to parameters, returns to results; an indirect call reaches every function and
//! external function whose address is taken), and through exceptions (one abstract exception
//! for the module). Every variadic argument passed to a FIR function flows to every `va.arg`
//! (one abstract list for the module, which may be `poison`: a run may pass it), and `va.start`
//! writes pointer bytes (the target's `va_list` holds addresses) that `va.end` replaces with
//! `poison`.
//!
//! **Control.** A branch on a tainted value (`cf.if`, `cf.cond_br`, `cf.switch`, a call through
//! a tainted pointer) taints the whole function: every value, store, trap, and event in it,
//! and every function it calls. A call of such a function taints the caller too when the module
//! can throw (whether the exception arrives is then address-dependent).
//!
//! **Outcomes.** A run's result at position `k` is tainted if the value its function returns
//! there is; an external function's argument at position `k` if some call passes a tainted
//! value there or makes the call under tainted control; a trap location if some op there has
//! a tainted operand or runs under tainted control. [`Taint::exempt`] then excuses a difference
//! only where each differing value is tainted and differs only in its numbers, or where the
//! runs' events agree that way and one of them ends in an arithmetic or conversion trap at a
//! tainted location while the other ends otherwise (the trapping run may have stopped before
//! whatever ended the other; anything deterministic before it, both runs would have reached).

use std::collections::{BTreeSet, HashMap, HashSet};

use fir::{Body, Module, OpId, OpKind as K, OperandKind, Ovf, TruncMode, Ty, ValueId};

/// Abstract objects: 0 is *wild*, any object; globals follow, then allocation sites.
type Objs = BTreeSet<u32>;
const WILD: u32 = 0;

/// What the analysis knows about a value or an object's contents.
#[derive(Clone, Default, PartialEq, Debug)]
struct Abs {
    /// May depend on addresses (or on `freeze`'s choice for `poison`).
    taint: bool,
    /// May be (or hold) `poison`.
    poison: bool,
    /// May carry the bytes of a non-null pointer.
    ptr: bool,
    /// The objects those pointers may point into.
    pts: Objs,
}

impl Abs {
    fn join(&mut self, o: &Abs) -> bool {
        let before = (self.taint, self.poison, self.ptr, self.pts.len());
        self.taint |= o.taint;
        self.poison |= o.poison;
        self.ptr |= o.ptr;
        self.pts.extend(&o.pts);
        before != (self.taint, self.poison, self.ptr, self.pts.len())
    }

    fn tainted(mut self, t: bool) -> Abs {
        self.taint |= t;
        self
    }

    /// The objects an access through this pointer may reach.
    fn reach(&self) -> Objs {
        let mut s = self.pts.clone();
        if self.taint {
            s.insert(WILD);
        }
        s
    }
}

struct Func {
    vals: Vec<Abs>,
    rets: Vec<Abs>,
    /// Control in the function may depend on addresses (or a caller's does).
    ctl: bool,
}

struct Analysis<'m> {
    m: &'m Module,
    fns: Vec<Func>,
    by_name: HashMap<&'m str, usize>,
    ext_by_name: HashMap<&'m str, usize>,
    globals: HashMap<&'m str, u32>,
    objs: Vec<Abs>,
    sites: HashMap<(usize, OpId), u32>,
    /// What may be thrown.
    exn: Abs,
    /// The variadic arguments passed to any FIR function, which `va.arg` may read.
    va: Abs,
    throws: bool,
    /// Functions and external functions whose address is taken.
    taken: Vec<usize>,
    taken_ext: Vec<usize>,
    events: Vec<Vec<bool>>,
    traps: HashSet<Option<(u32, u32)>>,
    changed: bool,
}

/// The outcomes of a module's runs that may depend on addresses.
#[derive(Debug, Default)]
pub struct Taint {
    rets: HashMap<String, Vec<bool>>,
    events: HashMap<String, Vec<bool>>,
    traps: HashSet<Option<(u32, u32)>>,
}

fn enclosing(b: &Body, op: OpId, pred: impl Fn(OpId) -> bool) -> Option<OpId> {
    let mut r = b.parent(op);
    while let Some(o) = b.parent_op(r) {
        if pred(o) {
            return Some(o);
        }
        r = b.parent(o);
    }
    None
}

impl<'m> Analysis<'m> {
    fn new(m: &'m Module) -> Analysis<'m> {
        let by_name = m
            .funcs
            .iter()
            .enumerate()
            .map(|(i, f)| (f.name.as_str(), i))
            .collect();
        let ext_by_name: HashMap<&str, usize> = m
            .externs
            .iter()
            .enumerate()
            .map(|(i, x)| (x.name.as_str(), i))
            .collect();
        let globals: HashMap<&str, u32> = (0..m.globals.len())
            .map(|g| (m.globals.name(g), 1 + g as u32))
            .collect();
        let mut objs = vec![Abs::default()];
        let mut named: Vec<&str> = Vec::new();
        for g in 0..m.globals.len() {
            let mut syms = Vec::new();
            m.globals.syms(m.globals.init(g), &mut syms);
            objs.push(Abs {
                taint: false,
                poison: false,
                ptr: !syms.is_empty(),
                pts: syms
                    .iter()
                    .filter_map(|s| globals.get(s).copied())
                    .collect(),
            });
            named.extend(syms);
        }
        let mut throws = false;
        for f in &m.funcs {
            let b = &f.body;
            let mut stack = vec![b.entry()];
            while let Some(r) = stack.pop() {
                for op in b.ops(r) {
                    match b.kind(op) {
                        K::FuncAddr { callee } => named.push(b.str(callee)),
                        K::Throw => throws = true,
                        _ => {}
                    }
                    stack.extend_from_slice(b.regions(op));
                }
            }
        }
        let mut a = Analysis {
            m,
            fns: m
                .funcs
                .iter()
                .map(|f| {
                    // Any function may be run, with `poison` arguments.
                    let mut vals = vec![Abs::default(); f.body.num_values()];
                    for p in f.body.params(f.body.entry()) {
                        vals[p.index()].poison = true;
                    }
                    Func {
                        vals,
                        rets: vec![Abs::default(); f.rets.len()],
                        ctl: false,
                    }
                })
                .collect(),
            by_name,
            ext_by_name,
            globals,
            objs,
            sites: HashMap::new(),
            exn: Abs::default(),
            va: Abs {
                poison: true,
                ..Abs::default()
            },
            throws,
            taken: Vec::new(),
            taken_ext: Vec::new(),
            events: m
                .externs
                .iter()
                .map(|x| vec![false; x.params.len()])
                .collect(),
            traps: HashSet::new(),
            changed: false,
        };
        for n in named {
            if let Some(&i) = a.by_name.get(n) {
                a.taken.push(i);
            } else if let Some(&i) = a.ext_by_name.get(n) {
                a.taken_ext.push(i);
            }
        }
        a.taken.sort_unstable();
        a.taken.dedup();
        a.taken_ext.sort_unstable();
        a.taken_ext.dedup();
        a
    }

    fn val(&self, fi: usize, o: fir::Operand) -> Abs {
        match o.get() {
            OperandKind::Value(v) => self.fns[fi].vals[v.index()].clone(),
            OperandKind::Hole(_) => Abs::default(),
        }
    }

    fn set(&mut self, fi: usize, v: ValueId, a: &Abs) {
        self.changed |= self.fns[fi].vals[v.index()].join(a);
    }

    fn set_ctl(&mut self, fi: usize) {
        if !self.fns[fi].ctl {
            self.fns[fi].ctl = true;
            self.changed = true;
        }
    }

    /// What a load through `p` may read.
    fn read(&self, s: &Objs) -> Abs {
        let mut out = self.objs[WILD as usize].clone();
        if s.contains(&WILD) {
            for o in &self.objs {
                out.join(o);
            }
        } else {
            for &o in s {
                out.join(&self.objs[o as usize]);
            }
        }
        out
    }

    fn write(&mut self, s: &Objs, a: &Abs) {
        if s.contains(&WILD) {
            self.changed |= self.objs[WILD as usize].join(a);
        } else {
            for &o in s {
                self.changed |= self.objs[o as usize].join(a);
            }
        }
    }

    fn load(&self, p: &Abs, ty: Ty) -> Abs {
        let m = self.read(&p.reach());
        // Pointer bytes read as a number are an address.
        let numeric = matches!(ty, Ty::Int(_) | Ty::Float(_));
        let taint = p.taint || m.taint || (m.ptr && !matches!(ty, Ty::Ptr | Ty::Byte(_)));
        if numeric {
            Abs {
                poison: m.poison,
                ..Abs::default()
            }
            .tainted(taint)
        } else {
            m.tainted(taint)
        }
    }

    fn site(&mut self, fi: usize, op: OpId) -> u32 {
        let n = self.objs.len() as u32;
        let id = *self.sites.entry((fi, op)).or_insert(n);
        if id == n {
            self.objs.push(Abs::default());
        }
        id
    }

    /// Pass `args` to the function `g` (`c`: under tainted control), and give its results.
    fn call_func(&mut self, fi: usize, g: usize, args: &[Abs], c: bool) -> Vec<Abs> {
        let b = &self.m.funcs[g].body;
        let params: Vec<ValueId> = b.params(b.entry()).collect();
        for (p, a) in params.iter().zip(args) {
            let a = a.clone().tainted(c);
            self.set(g, *p, &a);
        }
        for a in args.iter().skip(params.len()) {
            self.changed |= self.va.join(&a.clone().tainted(c));
        }
        if c {
            self.set_ctl(g);
        }
        if self.fns[g].ctl && self.throws {
            self.set_ctl(fi);
        }
        self.fns[g].rets.clone()
    }

    fn call_ext(&mut self, x: usize, args: &[Abs], c: bool) {
        for (k, a) in args.iter().enumerate() {
            // A variadic external function's event has an argument per variadic one too.
            if self.events[x].len() <= k {
                self.events[x].resize(k + 1, false);
            }
            if let Some(e) = self.events[x].get_mut(k)
                && !*e
                && (a.taint || c)
            {
                *e = true;
                self.changed = true;
            }
        }
    }

    /// A call: of `name` directly, or (`None`) through a pointer.
    fn call(&mut self, fi: usize, name: Option<&str>, args: &[Abs], c: bool) -> Vec<Abs> {
        let (funcs, exts) = match name {
            Some(n) => match (self.by_name.get(n), self.ext_by_name.get(n)) {
                (Some(&g), _) => (vec![g], vec![]),
                (None, Some(&x)) => (vec![], vec![x]),
                _ => (vec![], vec![]),
            },
            None => (
                self.taken
                    .iter()
                    .copied()
                    .filter(|&g| {
                        let f = &self.m.funcs[g];
                        let n = f.body.params(f.body.entry()).len();
                        n == args.len() || (f.variadic && n < args.len())
                    })
                    .collect(),
                self.taken_ext
                    .iter()
                    .copied()
                    .filter(|&x| {
                        let x = &self.m.externs[x];
                        x.params.len() == args.len() || (x.variadic && x.params.len() < args.len())
                    })
                    .collect(),
            ),
        };
        let mut out: Vec<Abs> = Vec::new();
        for g in funcs {
            for (k, r) in self.call_func(fi, g, args, c).into_iter().enumerate() {
                if out.len() <= k {
                    out.resize(k + 1, Abs::default());
                }
                out[k].join(&r);
            }
        }
        for x in exts {
            self.call_ext(x, args, c);
        }
        out
    }

    /// Jump to the block `label` of the nearest enclosing `cf.blocks` that has it.
    fn jump(&mut self, fi: usize, op: OpId, label: fir::StrId, args: &[Abs], c: bool) {
        let b = &self.m.funcs[fi].body;
        let Some(blocks) = enclosing(b, op, |o| {
            matches!(b.kind(o), K::Blocks { .. })
                && b.regions(o).iter().any(|&r| b.label(r) == Some(label))
        }) else {
            return;
        };
        let r = *b
            .regions(blocks)
            .iter()
            .find(|&&r| b.label(r) == Some(label))
            .unwrap();
        let params: Vec<ValueId> = b.params(r).collect();
        for (p, a) in params.iter().zip(args) {
            let a = a.clone().tainted(c);
            self.set(fi, *p, &a);
        }
    }

    fn walk(&mut self, fi: usize) {
        let m = self.m;
        let b = &m.funcs[fi].body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                stack.extend_from_slice(b.regions(op));
                self.op(fi, b, op);
            }
        }
    }

    fn op(&mut self, fi: usize, b: &'m Body, op: OpId) {
        let args: Vec<Abs> = b.operands(op).iter().map(|&o| self.val(fi, o)).collect();
        let c = self.fns[fi].ctl;
        let any = |s: &[Abs]| s.iter().any(|a| a.taint);
        if c || any(&args) {
            self.traps.insert(b.loc(op).map(|l| (l.line, l.col)));
        }
        let first = args.first().cloned().unwrap_or_default();
        let results: Vec<ValueId> = b.results(op).collect();
        let mut res: Vec<Abs> = Vec::new();
        let join_all = || {
            let mut a = Abs::default();
            for x in &args {
                a.join(x);
            }
            a
        };
        match b.kind(op) {
            K::PtrAddr | K::PtrExpose => {
                res.push(Abs::default().tainted(first.taint || first.ptr));
            }
            K::PtrFromExposed => res.push(Abs {
                taint: true,
                ptr: true,
                pts: [WILD].into(),
                ..Abs::default()
            }),
            // `freeze` of `poison` is the oracle's choice (the interpreter's is 0; the hardware
            // keeps what the register holds).
            K::Freeze => res.push(Abs {
                poison: false,
                ..first.clone().tainted(first.poison)
            }),
            K::PtrWithAddr => {
                let mut a = first.clone().tainted(true);
                a.ptr = true;
                a.pts.insert(WILD);
                res.push(a);
            }
            K::PtrCmp(_) => {
                let (x, y) = (&args[0], &args[1]);
                res.push(Abs::default().tainted(x.taint || y.taint || (x.ptr && y.ptr)));
            }
            K::MemStack { .. } | K::MemStackOf { .. } | K::MemAlloc { .. } => {
                let s = self.site(fi, op);
                // New memory is uninitialized: `poison`.
                let fresh = Abs {
                    poison: true,
                    ..Abs::default()
                };
                let fresh = fresh.tainted(any(&args) || c);
                self.changed |= self.objs[s as usize].join(&fresh);
                res.push(Abs {
                    ptr: true,
                    pts: [s].into(),
                    ..Abs::default()
                });
            }
            K::MemGlobal { global } => {
                let g = self.globals.get(b.str(global)).copied();
                res.push(Abs {
                    ptr: true,
                    pts: g.into_iter().collect(),
                    ..Abs::default()
                });
            }
            K::FuncAddr { .. } => res.push(Abs {
                ptr: true,
                ..Abs::default()
            }),
            K::Load { .. } => {
                let ty = b.ty(results[0]);
                res.push(self.load(&first, ty));
            }
            K::SliceGet { .. } => {
                let ty = b.ty(results[0]);
                let i = args.get(1).is_some_and(|a| a.taint);
                res.push(self.load(&first, ty).tainted(i));
            }
            K::Store { .. } => {
                let v = args[0].clone().tainted(c || args[1].taint);
                self.write(&args[1].reach(), &v);
            }
            K::SliceSet { .. } => {
                let v = args[0].clone().tainted(c || any(&args[1..]));
                self.write(&args[1].reach(), &v);
            }
            K::MemCopy { .. } => {
                let v = self.read(&args[1].reach()).tainted(c || any(&args));
                self.write(&args[0].reach(), &v);
            }
            // A `va_list` holds addresses on the target (a cursor, `poison` to loads, in FIR).
            K::VaStart => {
                let v = Abs {
                    poison: true,
                    ptr: true,
                    pts: [WILD].into(),
                    ..Abs::default()
                };
                self.write(&first.reach(), &v.tainted(c || first.taint));
            }
            K::VaArg => {
                let cursor = self.read(&first.reach());
                let v = self.va.clone().tainted(c || first.taint || cursor.taint);
                res.push(Abs { poison: true, ..v });
                let w = Abs {
                    poison: true,
                    ptr: true,
                    pts: [WILD].into(),
                    ..Abs::default()
                };
                self.write(&first.reach(), &w.tainted(c || first.taint));
            }
            K::VaEnd => {
                let v = Abs {
                    poison: true,
                    ..Abs::default()
                };
                self.write(&first.reach(), &v.tainted(c || first.taint));
            }
            K::Call { callee } => {
                res = self.call(fi, Some(b.str(callee)), &args, c);
            }
            K::Invoke { callee, unwind } => {
                res = self.call(fi, Some(b.str(callee)), &args, c);
                let e = self.exn.clone();
                self.jump(fi, op, b.succ(unwind).label, &[e], c);
            }
            K::CallIndirect(_) => {
                if first.taint {
                    self.set_ctl(fi);
                }
                res = self.call(fi, None, &args[1..], c);
            }
            K::InvokeIndirect { unwind, .. } => {
                if first.taint {
                    self.set_ctl(fi);
                }
                res = self.call(fi, None, &args[1..], c);
                let e = self.exn.clone();
                self.jump(fi, op, b.succ(unwind).label, &[e], c);
            }
            K::If | K::CondBr { .. } | K::Switch { .. } if first.taint => {
                self.set_ctl(fi);
            }
            _ => {}
        }
        match b.kind(op) {
            K::Loop { .. } => {
                let params: Vec<ValueId> = b.params(b.regions(op)[0]).collect();
                for (p, a) in params.iter().zip(&args) {
                    self.set(fi, *p, &a.clone().tainted(c));
                }
            }
            K::Try => {
                let e = self.exn.clone().tainted(c);
                if let Some(&p) = b.params(b.regions(op)[1]).collect::<Vec<_>>().first() {
                    self.set(fi, p, &e);
                }
            }
            K::Yield => {
                if let Some(target) = b.parent_op(b.parent(op)) {
                    for (v, a) in b.results(target).zip(&args) {
                        self.set(fi, v, &a.clone().tainted(c));
                    }
                }
            }
            K::Break | K::Continue => {
                if let Some(lp) = enclosing(b, op, |o| matches!(b.kind(o), K::Loop { .. })) {
                    let targets: Vec<ValueId> = if matches!(b.kind(op), K::Break) {
                        b.results(lp).collect()
                    } else {
                        b.params(b.regions(lp)[0]).collect()
                    };
                    for (v, a) in targets.iter().zip(&args) {
                        self.set(fi, *v, &a.clone().tainted(c));
                    }
                }
            }
            K::Ret => {
                for (k, a) in args.iter().enumerate() {
                    if let Some(r) = self.fns[fi].rets.get_mut(k) {
                        self.changed |= r.join(&a.clone().tainted(c));
                    }
                }
            }
            K::Throw => {
                self.changed |= self.exn.join(&first.tainted(c));
            }
            K::Br { dest } => self.jump(fi, op, b.succ(dest).label, &args, c),
            K::CondBr { t, f } => {
                let (t, f) = (b.succ(t), b.succ(f));
                let rest = &args[1..];
                let n = (t.nargs as usize).min(rest.len());
                self.jump(fi, op, t.label, &rest[..n], c);
                self.jump(fi, op, f.label, &rest[n..], c);
            }
            K::Switch { dflt, cases } => {
                let rest = &args[1..];
                let mut at = 0usize;
                let succs =
                    std::iter::once(b.succ(dflt)).chain(b.cases(cases).iter().map(|c| c.succ));
                for s in succs.collect::<Vec<_>>() {
                    let end = (at + s.nargs as usize).min(rest.len());
                    self.jump(fi, op, s.label, &rest[at.min(end)..end], c);
                    at = end;
                }
            }
            _ => {}
        }
        // Results not set above join the operands (pure ops, and a `cf.if`'s condition or a
        // loop's initial state for structured ops, whose terminators add the rest).
        let generic = res.is_empty()
            && !matches!(
                b.kind(op),
                K::Call { .. }
                    | K::Invoke { .. }
                    | K::CallIndirect(_)
                    | K::InvokeIndirect { .. }
                    | K::Const(_)
                    | K::FloatConst { .. }
                    | K::Poison
                    | K::PtrNull
                    | K::TySize(_)
                    | K::TyAlign(_)
                    | K::TyOffset { .. }
            );
        if generic {
            let a = join_all();
            res = vec![a; results.len()];
        }
        // `poison` comes from the ops that make it, and passes through the rest (loads and calls
        // say themselves, `freeze` and allocations end it).
        let kind = b.kind(op);
        let makes = matches!(
            kind,
            K::Poison
                | K::Arith(_, Ovf::Nsw | Ovf::Nuw | Ovf::NswNuw)
                | K::Trunc(TruncMode::Nsw | TruncMode::Nuw)
                | K::PtrOffset { inbounds: true }
                | K::PtrField { inbounds: true, .. }
                | K::PtrIndex { inbounds: true, .. }
        );
        let passes = !matches!(
            kind,
            K::Freeze
                | K::Load { .. }
                | K::SliceGet { .. }
                | K::Call { .. }
                | K::Invoke { .. }
                | K::CallIndirect(_)
                | K::InvokeIndirect { .. }
                | K::MemStack { .. }
                | K::MemStackOf { .. }
                | K::MemAlloc { .. }
        );
        let poison = makes || (passes && args.iter().any(|a| a.poison));
        for (k, v) in results.into_iter().enumerate() {
            let mut a = res.get(k).cloned().unwrap_or_default().tainted(c);
            a.poison |= poison;
            self.set(fi, v, &a);
        }
    }
}

impl Taint {
    /// Analyze a (verified, MFIR) module.
    pub fn of(m: &Module) -> Taint {
        let mut a = Analysis::new(m);
        loop {
            a.changed = false;
            for fi in 0..m.funcs.len() {
                a.walk(fi);
            }
            if !a.changed {
                break;
            }
        }
        Taint {
            rets: m
                .funcs
                .iter()
                .zip(&a.fns)
                .map(|(f, s)| {
                    (
                        f.name.clone(),
                        s.rets.iter().map(|r| r.taint || s.ctl).collect(),
                    )
                })
                .collect(),
            events: m
                .externs
                .iter()
                .zip(a.events)
                .map(|(x, e)| (x.name.clone(), e))
                .collect(),
            traps: a.traps,
        }
    }

    /// Whether any outcome may depend on addresses.
    pub fn any(&self) -> bool {
        !self.traps.is_empty()
            || self.rets.values().flatten().any(|&t| t)
            || self.events.values().flatten().any(|&t| t)
    }

    /// Whether a run of `func` that gives `got` where `fir run` gives `want` (normalized) differs
    /// only in what may depend on addresses (see the module documentation).
    pub fn exempt(&self, func: &str, want: &str, got: &str) -> bool {
        let (wp, we) = parts(want);
        let (gp, ge) = parts(got);
        if wp.len() != gp.len() || !wp.iter().zip(&gp).all(|(a, b)| self.event_ok(a, b)) {
            return false;
        }
        if matches(we, ge) {
            return true;
        }
        let rets = |e: &'_ str| -> Option<Vec<String>> {
            e.strip_prefix("returned").map(|r| {
                split_top(r.trim_start(), ", ")
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
            })
        };
        if let (Some(w), Some(g)) = (rets(we), rets(ge)) {
            let taint = self.rets.get(func).cloned().unwrap_or_default();
            return w.len() == g.len()
                && w.iter()
                    .zip(&g)
                    .enumerate()
                    .all(|(k, (a, b))| value_ok(a, b, taint.get(k).copied().unwrap_or(false)));
        }
        // One run traps where the other doesn't: allowed for an arithmetic or conversion trap,
        // when every trap involved is at a tainted location.
        let trap = |e: &str| -> Option<(bool, Option<(u32, u32)>)> {
            let rest = e.strip_prefix("trap ")?;
            let (reason, loc) = match rest.split_once(" @") {
                Some((r, l)) => {
                    let (line, col) = l.split_once(':')?;
                    (r, Some((line.parse().ok()?, col.parse().ok()?)))
                }
                None => (rest, None),
            };
            let arith = ["overflow", "div0", "shift", "convert"].contains(&reason);
            Some((arith, loc))
        };
        let traps: Vec<_> = [we, ge].into_iter().filter_map(trap).collect();
        traps.iter().any(|t| t.0 && self.traps.contains(&t.1))
    }

    fn event_ok(&self, want: &str, got: &str) -> bool {
        if matches(want, got) {
            return true;
        }
        let ev = |e: &'_ str| -> Option<(String, Vec<String>, String)> {
            let e = e.strip_prefix('@')?;
            let (name, rest) = e.split_once('(')?;
            let (args, rets) = rest.rsplit_once(") -> ")?;
            Some((
                name.to_owned(),
                split_top(args, ", ")
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                rets.to_owned(),
            ))
        };
        let (Some((wn, wa, wr)), Some((gn, ga, gr))) = (ev(want), ev(got)) else {
            return false;
        };
        let taint = self.events.get(&wn).cloned().unwrap_or_default();
        wn == gn
            && matches(&wr, &gr)
            && wa.len() == ga.len()
            && wa
                .iter()
                .zip(&ga)
                .enumerate()
                .all(|(k, (a, b))| value_ok(a, b, taint.get(k).copied().unwrap_or(false)))
    }
}

/// A line's events and its ending.
fn parts(line: &str) -> (Vec<&str>, &str) {
    let mut ps = split_top(line, "; ");
    let end = ps.pop().unwrap_or("");
    (ps, end)
}

/// `s` split at `sep` outside parentheses.
fn split_top<'a>(s: &'a str, sep: &str) -> Vec<&'a str> {
    let mut out = Vec::new();
    let (mut depth, mut start, mut i) = (0i32, 0, 0);
    let bytes = s.as_bytes();
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ if depth == 0 && s[i..].starts_with(sep) => {
                out.push(&s[start..i]);
                i += sep.len();
                start = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    if !s.is_empty() {
        out.push(&s[start..]);
    }
    out
}

fn toks(s: &str) -> Vec<&str> {
    s.split([' ', ',', ';', '(', ')'])
        .filter(|t| !t.is_empty())
        .collect()
}

/// Whether `got` matches the normalized reference `want`, where `poison` matches anything and
/// `?` (a non-null pointer, or a byte of one) any byte.
pub fn matches(want: &str, got: &str) -> bool {
    let (w, g) = (toks(want), toks(got));
    w.len() == g.len()
        && w.iter()
            .zip(&g)
            .all(|(a, b)| a == b || *a == "poison" || (*a == "?" && b.starts_with("0x")))
}

/// Whether one value matches, or (if `tainted`) differs only in its numbers.
fn value_ok(want: &str, got: &str, tainted: bool) -> bool {
    let num = |t: &str| {
        t.parse::<i128>().is_ok()
            || t.parse::<f64>().is_ok()
            || t.starts_with("0x")
            || t.starts_with("nan")
            || t.starts_with("-nan")
            || t == "?"
            || t == "null"
    };
    let (w, g) = (toks(want), toks(got));
    matches(want, got)
        || (tainted
            && w.len() == g.len()
            && w.iter().zip(&g).all(|(a, b)| a == b || (num(a) && num(b))))
}
