//! fcc's cache of the include probe (`frontends/c/src/main.cpp`, `systemIncludes`): a cached
//! answer must be the probe's own, and anything that could change the probe's answer must make
//! fcc probe again. Each run's `FIR_TIME=1` report says which happened: `fcc: include probe (cc -E
//! -v)` is a probe, `fcc: include probe (cached)` alone is a cache hit.
//!
//! Runs where the corpus does (`fcc.rs`): by default on Linux, on macOS only with `FCC_TESTS=1`,
//! never with `FCC_TESTS=0`.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn enabled() -> bool {
    match std::env::var("FCC_TESTS").as_deref() {
        Ok("0") => false,
        Ok("1") => true,
        _ => cfg!(target_os = "linux"),
    }
}

fn static_lib() -> PathBuf {
    let status = Command::new(env!("CARGO"))
        .args(["build", "--release", "-q", "-p", "fir-capi"])
        .current_dir(repo())
        .status()
        .expect("running cargo");
    assert!(status.success(), "building the C API failed");
    repo().join("target/release/libfir_capi.a")
}

/// fcc, built as `fcc.rs` builds it (the same directory, so one build serves both).
fn fcc() -> PathBuf {
    let build = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fcc-build");
    let lib = static_lib();
    let configured = Command::new("cmake")
        .arg("-S")
        .arg(repo().join("frontends/c"))
        .arg("-B")
        .arg(&build)
        .args(["-G", "Ninja", "-DFCC_BUILD_CAPI=OFF"])
        .arg(format!("-DFIR_CAPI_LIB={}", lib.display()))
        .output()
        .expect("running cmake (run the tests in the dev shell)");
    assert!(
        configured.status.success(),
        "configuring fcc failed:\n{}",
        String::from_utf8_lossy(&configured.stderr)
    );
    let built = Command::new("cmake")
        .arg("--build")
        .arg(&build)
        .output()
        .expect("running cmake");
    assert!(
        built.status.success(),
        "building fcc failed:\n{}",
        String::from_utf8_lossy(&built.stdout)
    );
    build.join("fcc")
}

struct Run {
    probed: bool,
    cached: bool,
    ok: bool,
    hfir: String,
    stderr: String,
}

fn run(fcc: &Path, src: &Path, cache: &Path, env: &[(&str, &str)]) -> Run {
    let out = src.with_extension("hfir");
    let _ = std::fs::remove_file(&out);
    let mut cmd = Command::new(fcc);
    cmd.arg(src)
        .args(["--emit", "hfir", "-o"])
        .arg(&out)
        .env("FIR_TIME", "1")
        .env("FCC_CACHE_DIR", cache)
        .env_remove("FCC_CACHE")
        .env_remove("CPATH")
        .env_remove("C_INCLUDE_PATH");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let r = cmd.output().expect("running fcc");
    let stderr = String::from_utf8_lossy(&r.stderr).into_owned();
    Run {
        probed: stderr.contains("fcc: include probe (cc -E -v)"),
        cached: stderr.contains("fcc: include probe (cached)"),
        ok: r.status.success(),
        hfir: std::fs::read_to_string(&out).unwrap_or_default(),
        stderr,
    }
}

fn entries(cache: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(cache)
        .map(|d| d.map(|e| e.unwrap().path()).collect())
        .unwrap_or_default();
    v.retain(|p| {
        p.file_name()
            .is_some_and(|n| n.to_string_lossy().starts_with("include-probe-"))
    });
    v.sort();
    v
}

#[test]
fn include_probe_cache_is_used_only_while_it_holds() {
    if !enabled() {
        return;
    }
    let fcc = fcc();
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fcc-cache-test");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let cache = dir.join("cache");
    // A program that needs the system headers, and one that needs a header only an
    // environment-given directory has.
    let plain = dir.join("plain.c");
    std::fs::write(
        &plain,
        "#include <stdint.h>\n#include <string.h>\nint64_t f(const char *s) { return (int64_t)strlen(s); }\n",
    )
    .unwrap();
    let marked = dir.join("marked.c");
    std::fs::write(
        &marked,
        "#include <fcc_cache_marker.h>\nint g(void) { return MARKER; }\n",
    )
    .unwrap();

    // The first run probes and fills the cache; the second uses it; both compile alike, and like
    // a run with the cache off.
    let first = run(&fcc, &plain, &cache, &[]);
    assert!(first.ok && first.probed, "{}", first.stderr);
    assert_eq!(entries(&cache).len(), 1, "one entry after the first run");
    let second = run(&fcc, &plain, &cache, &[]);
    assert!(second.ok, "{}", second.stderr);
    assert!(
        second.cached && !second.probed,
        "the second run should use the cache:\n{}",
        second.stderr
    );
    let off = run(&fcc, &plain, &cache, &[("FCC_CACHE", "0")]);
    assert!(
        off.ok && off.probed && !off.cached,
        "FCC_CACHE=0 probes:\n{}",
        off.stderr
    );
    assert_eq!(first.hfir, second.hfir);
    assert_eq!(first.hfir, off.hfir);
    assert!(!first.hfir.is_empty());

    // The environment is part of the key: a CPATH directory is a new probe, whose answer finds
    // the header there.
    let inc = dir.join("inc");
    std::fs::create_dir_all(&inc).unwrap();
    std::fs::write(inc.join("fcc_cache_marker.h"), "#define MARKER 7\n").unwrap();
    let inc_s = inc.to_str().unwrap();
    let with = run(&fcc, &marked, &cache, &[("CPATH", inc_s)]);
    assert!(
        with.ok && with.probed,
        "a new environment probes:\n{}",
        with.stderr
    );
    assert!(with.hfir.contains("7"), "{}", with.hfir);
    assert_eq!(entries(&cache).len(), 2);
    let again = run(&fcc, &marked, &cache, &[("CPATH", inc_s)]);
    assert!(
        again.ok && again.cached && !again.probed,
        "{}",
        again.stderr
    );
    // Without it, the header isn't found (the cache doesn't leak one environment's answer
    // into another's).
    let without = run(&fcc, &marked, &cache, &[]);
    assert!(
        !without.ok && without.cached,
        "without CPATH the header is missing:\n{}",
        without.stderr
    );

    // A directory the probe left out because it didn't exist, which then appears, is a new
    // probe: it might hold headers that come first.
    let later = dir.join("later");
    let later_s = later.to_str().unwrap();
    let missing = run(&fcc, &marked, &cache, &[("CPATH", later_s)]);
    assert!(!missing.ok && missing.probed, "{}", missing.stderr);
    let missing_again = run(&fcc, &marked, &cache, &[("CPATH", later_s)]);
    assert!(
        !missing_again.ok && missing_again.cached && !missing_again.probed,
        "{}",
        missing_again.stderr
    );
    std::fs::create_dir_all(&later).unwrap();
    std::fs::write(later.join("fcc_cache_marker.h"), "#define MARKER 9\n").unwrap();
    let appeared = run(&fcc, &marked, &cache, &[("CPATH", later_s)]);
    assert!(
        appeared.ok && appeared.probed,
        "a directory that appeared makes fcc probe again:\n{}",
        appeared.stderr
    );
    assert!(appeared.hfir.contains("9"), "{}", appeared.hfir);

    // A damaged entry is ignored and replaced.
    for e in entries(&cache) {
        std::fs::write(&e, "key 3\nxyz\ndir /nonexistent\nend\n").unwrap();
    }
    let damaged = run(&fcc, &plain, &cache, &[]);
    assert!(damaged.ok && damaged.probed, "{}", damaged.stderr);
    assert_eq!(damaged.hfir, first.hfir);
    let repaired = run(&fcc, &plain, &cache, &[]);
    assert!(
        repaired.ok && repaired.cached && !repaired.probed,
        "{}",
        repaired.stderr
    );
    let _ = std::fs::remove_dir_all(&dir);
}
