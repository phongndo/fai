//! The pass manager, and the rewrites proved in Lean as passes.
//!
//! A pass is a plain function over one function's [`Body`] (or a whole [`Module`]) that returns
//! how many changes it made, and records a [`Remark`] for each when asked to. Passes keep no
//! state between runs, so a builder or C API can call them directly:
//!
//! ```
//! let text = "func @f(%x: i32) -> i32 {
//!   %p: ptr = mem.stack 4, align 4
//!   mem.store i32 %x, %p, align 4
//!   %y: i32 = mem.load %p, align 4
//!   func.ret %y
//! }
//! ";
//! let mut m = fir::parse_module(text).unwrap();
//! fir::verify_module(&m).unwrap();
//! // One pass on one function:
//! let mut remarks = fir::passes::Remarks::new(true);
//! assert_eq!(fir::passes::fwd::run(&mut m.funcs[0].body, &mut remarks), 1);
//! // A pipeline on the module: by name, or the default `-O` one, run to a fixed point.
//! let pipeline = fir::passes::Pipeline::parse("copyprop,dce").unwrap();
//! let report = pipeline.run(&mut m, &mut remarks).unwrap();
//! assert_eq!(report.changes(), 2);
//! assert!(m.render(false).contains("func.ret %x"));
//! ```
//!
//! Each pass makes exactly the rewrite its Lean theorem proves, with the same side conditions;
//! the theorem is named in the pass's module docs, with any case the pass skips. Running a pass
//! many times, or at many places at once, is a sequence of single rewrites, each an instance of
//! the theorem on the program the previous one left, so the result refines the input by
//! `Func.Refines.trans`. Two steps of that argument aren't proved yet: each theorem assumes its
//! source never ends `ambiguous` (`Func.Decided`), which an intermediate program may not
//! inherit where the original is UB, and each is about one function in a fixed module, so
//! optimizing every function of a module also needs refinement to compose over calls. The
//! differential tests check the composed result (`tests/opt.rs`).
//!
//! | Pass | Rewrite | Theorem |
//! |---|---|---|
//! | [`dse`] | a store followed at once by a same-size store through the same pointer is deleted | `Fir.Dse.refines` |
//! | [`fwd`] | a load right after a store of its type through the same pointer becomes a copy of the stored value | `Fir.Fwd.refines` |
//! | [`copyprop`] | after `%y = copy %x`, later ops of the block up to the first with regions or a call read `%x` for `%y` | `Fir.CopyProp.refines` |
//! | [`dce`] | a pure op whose results nothing reads is deleted | `Fir.Dce.refines` |
//!
//! Passes need a verified module: they rely on every name being defined once per function and
//! used only where it is visible, so value ids and Lean's names agree. The pipeline verifies
//! after every pass in development builds and names the pass that broke the module (decision:
//! Verifier). Passes match core ops only, so they run on HFIR and MFIR modules alike.

pub mod copyprop;
pub mod dce;
pub mod dse;
pub mod fwd;

use std::fmt;
use std::time::{Duration, Instant};

use crate::body::{Body, OpId, Ops};
use crate::ir::{Loc, Module};
use crate::verify::render_loc;

/// What a pass runs over.
#[derive(Clone, Copy)]
pub enum PassFn {
    /// Each function's body in turn.
    Func(fn(&mut Body, &mut Remarks) -> u32),
    /// The whole module.
    Module(fn(&mut Module, &mut Remarks) -> u32),
}

/// A pass: a name for pipelines and remarks, and the function that runs it. Both return how
/// many changes they made.
#[derive(Clone, Copy)]
pub struct Pass {
    pub name: &'static str,
    /// One line on what it does, for `--help`-style listings.
    pub summary: &'static str,
    pub run: PassFn,
}

/// Every pass, by name.
pub const PASSES: &[Pass] = &[
    Pass {
        name: "dse",
        summary: "delete a store overwritten at once by a same-size store through the same pointer",
        run: PassFn::Func(dse::run),
    },
    Pass {
        name: "fwd",
        summary: "turn a load right after a store of its type through the same pointer into a copy",
        run: PassFn::Func(fwd::run),
    },
    Pass {
        name: "copyprop",
        summary: "read %x for %y after %y = copy %x, up to the first op with regions or a call",
        run: PassFn::Func(copyprop::run),
    },
    Pass {
        name: "dce",
        summary: "delete pure ops whose results nothing reads",
        run: PassFn::Func(dce::run),
    },
];

/// The default `-O` pipeline, run to a fixed point: forwarding makes copies, copy propagation
/// leaves them unread, dead code elimination deletes them, and the stores they separated become
/// adjacent for dead store elimination in the next round.
pub const DEFAULT: &[&str] = &["fwd", "copyprop", "dse", "dce"];

/// The pass with this name.
pub fn pass(name: &str) -> Option<&'static Pass> {
    PASSES.iter().find(|p| p.name == name)
}

/// One change a pass made (the seed of `--explain`, and the derivation side table of the
/// Provenance decision): the pass, the function (an index into [`Module::funcs`]), the op
/// changed or deleted, the op that justifies it (the overwriting store, the forwarded store,
/// the copy), and a sentence about it.
#[derive(Clone, Debug)]
pub struct Remark {
    pub pass: &'static str,
    pub func: u32,
    pub op: OpId,
    pub loc: Option<Loc>,
    pub cause: Option<(OpId, Option<Loc>)>,
    pub text: String,
}

/// `dse: deleted store @3:5 (overwritten by @4:5)`.
impl fmt::Display for Remark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.pass, self.text)
    }
}

/// Where passes record what they did. Disabled, it records nothing and costs nothing: passes
/// check [`Remarks::enabled`] before building any text.
#[derive(Clone, Debug, Default)]
pub struct Remarks {
    enabled: bool,
    /// The function being run, for the remarks' `func`.
    func: u32,
    list: Vec<Remark>,
}

impl Remarks {
    pub fn new(enabled: bool) -> Remarks {
        Remarks {
            enabled,
            func: 0,
            list: Vec::new(),
        }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// Set the function later remarks are about.
    pub fn set_func(&mut self, func: u32) {
        self.func = func;
    }

    /// Record a remark, if enabled. `text` is built only then.
    pub fn add(
        &mut self,
        pass: &'static str,
        op: (OpId, Option<Loc>),
        cause: Option<(OpId, Option<Loc>)>,
        text: impl FnOnce() -> String,
    ) {
        if self.enabled {
            self.list.push(Remark {
                pass,
                func: self.func,
                op: op.0,
                loc: op.1,
                cause,
                text: text(),
            });
        }
    }

    pub fn list(&self) -> &[Remark] {
        &self.list
    }

    pub fn take(&mut self) -> Vec<Remark> {
        std::mem::take(&mut self.list)
    }
}

/// `@line:col`, or `@?`.
fn at(loc: Option<Loc>) -> String {
    render_loc(loc)
}

/// What one pass did over a pipeline run.
#[derive(Clone, Debug)]
pub struct PassStats {
    pub name: &'static str,
    /// How many times it ran (once per round).
    pub runs: u32,
    pub changes: u64,
    pub time: Duration,
}

/// What a pipeline run did, pass by pass.
#[derive(Clone, Debug, Default)]
pub struct Report {
    pub rounds: u32,
    pub passes: Vec<PassStats>,
    /// Time spent verifying after passes.
    pub verify_time: Duration,
}

impl Report {
    pub fn changes(&self) -> u64 {
        self.passes.iter().map(|p| p.changes).sum()
    }

    /// The changes made by the pass with this name.
    pub fn changes_by(&self, name: &str) -> u64 {
        self.passes
            .iter()
            .filter(|p| p.name == name)
            .map(|p| p.changes)
            .sum()
    }
}

/// `--stats`: a line per pass.
impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{} rounds", self.rounds)?;
        for p in &self.passes {
            writeln!(
                f,
                "{:>10}: {:>8} changes in {} runs, {:.3} ms",
                p.name,
                p.changes,
                p.runs,
                p.time.as_secs_f64() * 1e3
            )?;
        }
        if !self.verify_time.is_zero() {
            writeln!(
                f,
                "{:>10}: {:.3} ms",
                "verify",
                self.verify_time.as_secs_f64() * 1e3
            )?;
        }
        Ok(())
    }
}

/// A module that failed verification after a pass: the pass (or `input`, for a module that was
/// broken before any pass ran), the round, and the verifier's message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassError {
    pub pass: &'static str,
    pub round: u32,
    pub message: String,
}

impl fmt::Display for PassError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.pass == "input" {
            write!(f, "the input doesn't verify: {}", self.message)
        } else {
            write!(
                f,
                "pass {} (round {}) broke the module: {}",
                self.pass, self.round, self.message
            )
        }
    }
}

/// Passes to run in order, possibly repeated until none changes anything.
#[derive(Clone)]
pub struct Pipeline {
    pub passes: Vec<&'static Pass>,
    /// Repeat the passes until a round changes nothing, at most `max_rounds` times.
    pub fixpoint: bool,
    pub max_rounds: u32,
    /// Verify the module (and check each body's internal links) before the first pass and after
    /// every pass. On in development builds (decision: Verifier).
    pub verify_each: bool,
}

impl Pipeline {
    /// These passes, run once each, in order.
    pub fn new(passes: Vec<&'static Pass>) -> Pipeline {
        Pipeline {
            passes,
            fixpoint: false,
            max_rounds: 1,
            verify_each: cfg!(debug_assertions),
        }
    }

    /// The default `-O` pipeline ([`DEFAULT`]), to a fixed point.
    pub fn default_opt() -> Pipeline {
        let mut p = Pipeline::new(DEFAULT.iter().filter_map(|n| pass(n)).collect());
        p.fixpoint = true;
        p.max_rounds = 16;
        p
    }

    /// Passes by name, separated by commas: `dse,fwd,copyprop,dce`, run once each.
    pub fn parse(spec: &str) -> Result<Pipeline, String> {
        let mut passes = Vec::new();
        for name in spec.split(',').map(str::trim).filter(|n| !n.is_empty()) {
            match pass(name) {
                Some(p) => passes.push(p),
                None => {
                    let known: Vec<&str> = PASSES.iter().map(|p| p.name).collect();
                    return Err(format!(
                        "no pass {name:?}; the passes are {}",
                        known.join(", ")
                    ));
                }
            }
        }
        Ok(Pipeline::new(passes))
    }

    /// Run the pipeline on a verified module.
    pub fn run(&self, m: &mut Module, remarks: &mut Remarks) -> Result<Report, PassError> {
        let mut report = Report {
            rounds: 0,
            passes: self
                .passes
                .iter()
                .map(|p| PassStats {
                    name: p.name,
                    runs: 0,
                    changes: 0,
                    time: Duration::ZERO,
                })
                .collect(),
            verify_time: Duration::ZERO,
        };
        if self.verify_each {
            check(m, "input", 0, &mut report.verify_time)?;
        }
        for round in 1..=self.max_rounds.max(1) {
            report.rounds = round;
            let mut changed = 0;
            for (i, p) in self.passes.iter().enumerate() {
                let start = Instant::now();
                let n = run_pass(p, m, remarks);
                let stats = &mut report.passes[i];
                stats.time += start.elapsed();
                stats.runs += 1;
                stats.changes += u64::from(n);
                changed += u64::from(n);
                if self.verify_each {
                    check(m, p.name, round, &mut report.verify_time)?;
                }
            }
            if !self.fixpoint || changed == 0 {
                break;
            }
        }
        Ok(report)
    }
}

/// Run one pass over the module; how many changes it made.
pub fn run_pass(p: &Pass, m: &mut Module, remarks: &mut Remarks) -> u32 {
    match p.run {
        PassFn::Func(f) => {
            let mut n = 0;
            for (i, func) in m.funcs.iter_mut().enumerate() {
                remarks.set_func(i as u32);
                n += f(&mut func.body, remarks);
            }
            n
        }
        PassFn::Module(f) => f(m, remarks),
    }
}

/// Check every body's links and verify the module, blaming `pass`.
fn check(m: &Module, pass: &'static str, round: u32, time: &mut Duration) -> Result<(), PassError> {
    let start = Instant::now();
    let fail = |message: String| PassError {
        pass,
        round,
        message,
    };
    for f in &m.funcs {
        f.body
            .check_invariants()
            .map_err(|e| fail(format!("@{}: {e}", f.name)))?;
    }
    crate::verify::verify_module(m).map_err(fail)?;
    *time += start.elapsed();
    Ok(())
}

/// Every op of the body in program order: each op, then the ops of its regions, in order.
pub(crate) fn walk(body: &Body, out: &mut Vec<OpId>) {
    out.clear();
    let mut stack: Vec<Ops<'_>> = vec![body.ops(body.entry())];
    while let Some(it) = stack.last_mut() {
        match it.next() {
            Some(op) => {
                out.push(op);
                for &r in body.regions(op).iter().rev() {
                    stack.push(body.ops(r));
                }
            }
            None => {
                stack.pop();
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test_util {
    use crate::ir::Module;

    use super::Remarks;

    /// Parse and verify a module, run `f` on its first function, verify again, and give the
    /// change count, the text without locations, and the remarks.
    pub fn apply(
        text: &str,
        f: fn(&mut crate::Body, &mut Remarks) -> u32,
    ) -> (u32, String, Vec<String>) {
        let mut m: Module = crate::parse_module(text).unwrap();
        crate::verify_module(&m).unwrap();
        let mut remarks = Remarks::new(true);
        let n = f(&mut m.funcs[0].body, &mut remarks);
        m.funcs[0].body.check_invariants().unwrap();
        crate::verify_module(&m).unwrap_or_else(|e| panic!("{e}\n{}", m.render(true)));
        let out = m.render(false);
        let remarks = remarks.list().iter().map(|r| r.to_string()).collect();
        (n, out, remarks)
    }

    /// The function bodies of `text` without locations, for comparing with [`apply`]'s.
    pub fn canon(text: &str) -> String {
        crate::parse_module(text).unwrap().render(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "func @f(%x: i32) -> i32 {
  %p: ptr = mem.stack 4, align 4 @1:3
  mem.store i32 %x, %p, align 4 @2:3
  mem.store i32 %x, %p, align 4 @3:3
  %y: i32 = mem.load %p, align 4 @4:3
  %z: i32 = int.add.wrap %y, %y @5:3
  func.ret %y @6:3
}
";

    #[test]
    fn default_pipeline_reaches_a_fixed_point() {
        let mut m = crate::parse_module(SRC).unwrap();
        let mut remarks = Remarks::new(true);
        let mut p = Pipeline::default_opt();
        p.verify_each = true;
        let report = p.run(&mut m, &mut remarks).unwrap();
        assert_eq!(report.rounds, 2);
        assert_eq!(
            m.render(false),
            "func @f(%x: i32) -> i32 {\n  %p: ptr = mem.stack 4, align 4\n  mem.store i32 %x, %p, align 4\n  func.ret %x\n}\n"
        );
        let text: Vec<String> = remarks.list().iter().map(|r| r.to_string()).collect();
        assert_eq!(
            text,
            [
                "fwd: load @4:3 forwarded from store @3:3 (now a copy)",
                "copyprop: %y read as %x at @5:3, @6:3 (copy @4:3)",
                "dse: deleted store @2:3 (overwritten by @3:3)",
                "dce: deleted unused copy @4:3",
                "dce: deleted unused int.add.wrap @5:3",
            ]
        );
        // Forwarding and the dead store name the same store as their cause.
        assert_eq!(
            remarks.list()[0].cause.map(|c| c.0),
            remarks.list()[2].cause.map(|c| c.0)
        );
        assert_eq!(
            [
                report.changes_by("fwd"),
                report.changes_by("copyprop"),
                report.changes_by("dse"),
                report.changes_by("dce")
            ],
            [1, 3, 1, 2]
        );
    }

    fn breaks(body: &mut Body, _: &mut Remarks) -> u32 {
        let last = body.ops(body.entry()).last().unwrap();
        body.erase(last);
        1
    }

    static BROKEN: Pass = Pass {
        name: "broken",
        summary: "deletes the function's func.ret",
        run: PassFn::Func(breaks),
    };

    #[test]
    fn names_the_pass_that_broke_the_module() {
        let mut m = crate::parse_module(SRC).unwrap();
        let mut p = Pipeline::parse("dse").unwrap();
        p.passes.push(&BROKEN);
        p.verify_each = true;
        let e = p.run(&mut m, &mut Remarks::new(false)).unwrap_err();
        assert_eq!(e.pass, "broken");
        assert_eq!(
            e.to_string(),
            "pass broken (round 1) broke the module: in @f: @?: the function body must end with func.ret"
        );
        // A broken input is blamed on no pass.
        let e = p.run(&mut m, &mut Remarks::new(false)).unwrap_err();
        assert_eq!(e.pass, "input");
    }

    #[test]
    fn parses_pipelines() {
        let p = Pipeline::parse("dse, fwd,copyprop,dce").unwrap();
        let names: Vec<&str> = p.passes.iter().map(|p| p.name).collect();
        assert_eq!(names, ["dse", "fwd", "copyprop", "dce"]);
        assert!(!p.fixpoint);
        assert_eq!(
            Pipeline::parse("dse,gvn").err().unwrap(),
            "no pass \"gvn\"; the passes are dse, fwd, copyprop, dce"
        );
    }
}
