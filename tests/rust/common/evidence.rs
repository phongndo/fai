#![allow(dead_code)]

//! What a test actually checked, for `fai verify`.
//!
//! A test that skips part of its work (no Lean reference, no AArch64 toolchain, no C compiler)
//! passes, which is right for a quick local run and wrong for a release gate. So tests record
//! their counts here, and with `FIR_EVIDENCE=DIR` each writes `DIR/<name>.json`; `fai verify
//! full` reads the files and refuses a run whose counts show missing work, whatever the
//! exit status was. With `FIR_REQUIRE_FULL=1` a test also fails at once instead of skipping
//! ([`require`]).
//!
//! The format is a small JSON object, written by hand (the test crates have no JSON dependency):
//! `{"test": NAME, "counts": {KEY: N, …}, "executed ops": {MNEMONIC: N, …}, "skipped": [WHY, …],
//! "facts": {KEY: VALUE, …}}`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::Mutex;

/// Whether this run must not skip anything (`FIR_REQUIRE_FULL=1`).
pub fn full_required() -> bool {
    std::env::var("FIR_REQUIRE_FULL").is_ok_and(|s| s == "1")
}

/// Skip with `why`, or, when a full run is required, fail with it.
pub fn require(why: &str) {
    assert!(
        !full_required(),
        "FIR_REQUIRE_FULL=1: this check can't be skipped: {why}"
    );
    eprintln!("skipped: {why}");
}

/// Record that this host can't run `ev`'s check by construction (Linux binaries on macOS, say),
/// with why, instead of skipping it: not a failure under `FIR_REQUIRE_FULL`, because `fai verify`
/// accepts it only where its `HOST_GAPS` table declares that gap for this host, and then
/// reports the check as unverified there and the run as host verification, never full. Call it
/// only on a condition fixed at compile time (`cfg!`), never on a missing tool.
pub fn host_gap(ev: &Evidence, why: &str) {
    eprintln!(
        "host gap on {}-{}: {why}",
        std::env::consts::ARCH,
        std::env::consts::OS
    );
    ev.fact("host gap", why);
}

/// The pipeline the optimizing suites test: `FIR_PASSES`, or `-O` (recorded as the `pipeline`
/// fact, so `fai experiment` can check its gate tested the candidate's).
pub fn pipeline() -> String {
    match std::env::var("FIR_PASSES") {
        Ok(s) if !s.is_empty() => s,
        _ => "-O".to_owned(),
    }
}

/// One test's evidence. Thread-safe, so parallel workers can share one.
#[derive(Default)]
pub struct Evidence {
    name: String,
    inner: Mutex<Inner>,
}

#[derive(Default)]
struct Inner {
    counts: BTreeMap<String, u64>,
    executed_ops: BTreeMap<String, u64>,
    skipped: Vec<String>,
    facts: BTreeMap<String, String>,
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl Evidence {
    pub fn new(name: &str) -> Evidence {
        Evidence {
            name: name.to_owned(),
            inner: Mutex::default(),
        }
    }

    pub fn count(&self, key: impl Into<String>, n: u64) {
        *self
            .inner
            .lock()
            .unwrap()
            .counts
            .entry(key.into())
            .or_default() += n;
    }

    /// Add an actual execution profile only after that run's result was compared and agreed.
    /// For native comparisons this must profile the exact module compiled, with the same
    /// arguments: an interpreter execution is a proxy, not a trace of the native instructions.
    pub fn executed(&self, profile: &fir::interp::ExecutionProfile) {
        let mut inner = self.inner.lock().unwrap();
        for (name, n) in profile.counts() {
            *inner.executed_ops.entry(name.to_owned()).or_default() += n;
        }
    }

    pub fn skip(&self, why: impl Into<String>) {
        self.inner.lock().unwrap().skipped.push(why.into());
    }

    pub fn fact(&self, key: &str, value: impl Into<String>) {
        self.inner
            .lock()
            .unwrap()
            .facts
            .insert(key.to_owned(), value.into());
    }

    /// Write the evidence to `$FIR_EVIDENCE/<name>.json`, if that is set.
    pub fn write(&self) {
        let Ok(dir) = std::env::var("FIR_EVIDENCE") else {
            return;
        };
        let inner = self.inner.lock().unwrap();
        let map = |m: &BTreeMap<String, u64>| {
            let items: Vec<String> = m
                .iter()
                .map(|(k, v)| format!("{}: {v}", json_str(k)))
                .collect();
            format!("{{{}}}", items.join(", "))
        };
        let skipped: Vec<String> = inner.skipped.iter().map(|s| json_str(s)).collect();
        let facts: Vec<String> = inner
            .facts
            .iter()
            .map(|(k, v)| format!("{}: {}", json_str(k), json_str(v)))
            .collect();
        let text = format!(
            "{{\"test\": {}, \"run\": {}, \"counts\": {}, \"executed ops\": {}, \"skipped\": [{}], \"facts\": {{{}}}}}\n",
            json_str(&self.name),
            // The verification run this evidence belongs to (`FIR_EVIDENCE_RUN`), so evidence
            // left from an earlier run can't stand in for a suite that didn't run this time.
            json_str(&std::env::var("FIR_EVIDENCE_RUN").unwrap_or_default()),
            map(&inner.counts),
            map(&inner.executed_ops),
            skipped.join(", "),
            facts.join(", ")
        );
        std::fs::create_dir_all(&dir).unwrap();
        let file = std::path::Path::new(&dir).join(format!("{}.json", self.name));
        std::fs::write(&file, text).unwrap_or_else(|e| panic!("writing {}: {e}", file.display()));
    }
}
