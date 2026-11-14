//! Where a compilation's time goes, phase by phase: `FIR_TIME=1` in the environment turns it on
//! (as `-ftime-report` does for Clang and GCC, and `-Z time-passes` for rustc), and the command
//! that compiled prints the report on stderr (`fir compile`, `fir opt`, `fir lower`, and `fcc`,
//! through the C API's `fir_time_report`).
//!
//! Each [`time`]d phase records its **self** time: the time inside it minus the time of the
//! phases timed inside it on the same thread. So the self times of one thread's phases add up
//! to the time they cover, without counting anything twice: `verify` inside `lower` is
//! `verify`'s, not `lower`'s. Phases that worker threads record (the AArch64 register allocation
//! and its validation, which run in parallel) are summed over the threads, so they are CPU time,
//! not wall time; the report marks them.
//!
//! Off (the default), a phase costs one relaxed atomic load. Nothing is recorded, and the
//! compiler's output doesn't depend on whether it is on.

use std::borrow::Cow;
use std::cell::Cell;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

/// 0: not read yet; 1: off; 2: on.
static STATE: AtomicU8 = AtomicU8::new(0);

/// Every phase recorded so far, in the order each was first recorded.
static PHASES: Mutex<Vec<Phase>> = Mutex::new(Vec::new());

/// The thread that recorded first: the compiling thread. (A Rust library called from C, as in
/// `fcc`, can't ask for the process's main thread by name.)
static FIRST: OnceLock<ThreadId> = OnceLock::new();

thread_local! {
    /// The time of the phases timed inside the current one, on this thread.
    static INNER: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}

/// One phase's totals.
#[derive(Clone, Debug, PartialEq)]
pub struct Phase {
    pub name: Cow<'static, str>,
    /// How many times it ran.
    pub calls: u64,
    /// Its time, less the time of the phases timed inside it.
    pub self_time: Duration,
    /// Whether a thread other than the first to record anything recorded it: then the times
    /// are summed over threads.
    pub threads: bool,
}

/// Whether timing is on: `FIR_TIME` is set to something other than empty or `0`. Read once.
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        1 => false,
        2 => true,
        _ => {
            let on = std::env::var_os("FIR_TIME").is_some_and(|v| !v.is_empty() && v != "0");
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

/// Turn timing on or off for the rest of the process, whatever `FIR_TIME` says (for tests and
/// tools that time themselves).
pub fn set_enabled(on: bool) {
    STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
}

/// Run `f` as phase `name`, recording its self time when timing is on.
pub fn time<R>(name: &'static str, f: impl FnOnce() -> R) -> R {
    if !enabled() {
        return f();
    }
    let outer = INNER.with(|c| c.replace(Duration::ZERO));
    let start = Instant::now();
    let r = f();
    let total = start.elapsed();
    let inner = INNER.with(|c| c.replace(outer + total));
    record(Cow::Borrowed(name), total.saturating_sub(inner));
    r
}

/// Add `self_time` to phase `name` (a phase measured outside [`time`], such as a pass's own
/// statistics, or a C caller's step through `fir_time_record`). It counts as time inside the
/// enclosing phase, if any, which is charged that much less.
pub fn record(name: Cow<'static, str>, self_time: Duration) {
    if !enabled() {
        return;
    }
    let me = std::thread::current().id();
    let threads = *FIRST.get_or_init(|| me) != me;
    let mut phases = PHASES.lock().unwrap_or_else(|e| e.into_inner());
    match phases.iter_mut().find(|p| p.name == name) {
        Some(p) => {
            p.calls += 1;
            p.self_time += self_time;
            p.threads |= threads;
        }
        None => phases.push(Phase {
            name,
            calls: 1,
            self_time,
            threads,
        }),
    }
}

/// Charge `d` to the enclosing phase's inner time, so the enclosing phase's self time excludes
/// it: for time [`record`]ed by hand inside a [`time`]d phase.
pub fn exclude(d: Duration) {
    if enabled() {
        INNER.with(|c| c.set(c.get() + d));
    }
}

/// The phases recorded so far, in the order each was first recorded; recording starts afresh.
pub fn take() -> Vec<Phase> {
    std::mem::take(&mut *PHASES.lock().unwrap_or_else(|e| e.into_inner()))
}

/// The report of [`take`]'s phases, or `None` when timing is off. One line per phase: self time
/// in milliseconds, its share of the main thread's total, how many times it ran, its name. A `*`
/// marks phases summed over worker threads, which are not part of the total.
pub fn report() -> Option<String> {
    if !enabled() {
        return None;
    }
    Some(format_report(&take()))
}

/// [`report`]'s text for `phases`.
pub fn format_report(phases: &[Phase]) -> String {
    let total: Duration = phases
        .iter()
        .filter(|p| !p.threads)
        .map(|p| p.self_time)
        .sum();
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    let mut s = String::from("fir: time:     self ms   share  calls  phase\n");
    for p in phases {
        let share = if p.threads || total.is_zero() {
            "     ".to_owned()
        } else {
            format!(
                "{:4.0}%",
                100.0 * p.self_time.as_secs_f64() / total.as_secs_f64()
            )
        };
        s += &format!(
            "fir: time: {:11.3}   {share}  {:5}  {}{}\n",
            ms(p.self_time),
            p.calls,
            p.name,
            if p.threads { " *" } else { "" }
        );
    }
    s += &format!(
        "fir: time: {:11.3}   100%         total (main thread)\n",
        ms(total)
    );
    if phases.iter().any(|p| p.threads) {
        s += "fir: time: * summed over worker threads: CPU time, not part of the total\n";
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_time_excludes_inner_phases() {
        set_enabled(true);
        take();
        time("outer", || {
            std::thread::sleep(Duration::from_millis(20));
            time("inner", || std::thread::sleep(Duration::from_millis(30)));
        });
        let p = take();
        let get = |n: &str| p.iter().find(|x| x.name == n).unwrap().self_time;
        assert!(get("inner") >= Duration::from_millis(30));
        assert!(get("outer") >= Duration::from_millis(20));
        assert!(get("outer") < Duration::from_millis(30), "{p:?}");
        let r = format_report(&p);
        assert!(
            r.contains("outer") && r.contains("inner") && r.contains("total"),
            "{r}"
        );
        set_enabled(false);
        assert_eq!(time("off", || 7), 7);
        assert!(take().is_empty());
    }
}
