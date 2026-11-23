#!/usr/bin/env -S uv run --script
"""projbench: fcc against GCC, Clang, and arocc on whole C projects and on C23.

cbench (benchmarks/c) measures 12 small kernels and compilebench (benchmarks/compile) measures
compile latency. This measures what neither does: two real projects end to end, Lua 5.4.7 (33
files) and SQLite 3.53.3 (the 9 MB amalgamation and speedtest1), and which C23 programs each
compiler accepts. Run from the repository root in the dev shell, on Linux:

  benchmarks/projects/projbench.py prepare   the sources: Lua and SQLite from the flake's
                                             nixpkgs, Lua's test suite from lua.org (SHA-256
                                             pinned); generates sqlite3.c
  benchmarks/projects/projbench.py build     every file of each project by every configuration:
                                             wall and CPU time, peak RSS (minimum of --reps),
                                             code size, fcc's phases (FIR_TIME=1); links static
                                             AArch64 binaries
  benchmarks/projects/projbench.py frontend  parse and check only (-fsyntax-only): GCC, Clang,
                                             and arocc on the projects, cbench's 12 programs,
                                             and generated C
  benchmarks/projects/projbench.py check     under qemu-aarch64: Lua's own test suite and the
                                             Lua scripts, and speedtest1 --verify, per build,
                                             against GCC -O2's
  benchmarks/projects/projbench.py count     under qemu-aarch64 with cbench's plugin: executed
                                             instructions (own code and libc), their mix, and
                                             memory accesses, per workload and build
  benchmarks/projects/projbench.py c23       the C23 corpus programs: GCC, Clang, and fcc
                                             compile, link, and run each (qemu); arocc checks it
  benchmarks/projects/projbench.py time [--ssh HOST [--docker IMAGE]]
                                             native wall time (cbench's benchrun), as cbench
  benchmarks/projects/projbench.py report    OUT/report.md
  benchmarks/projects/projbench.py all [time options]

arocc (https://github.com/Vexu/arocc) has no code generator yet (its README: "under
construction"; any function fails with "TODO implement lowering functions"), so it is measured as
a frontend only, next to `gcc -fsyntax-only`, `clang -fsyntax-only`, and fcc's own Clang phase.
`--arocc PATH` (or AROCC) names it; without it, arocc's rows are skipped.

Every compiler gets the same target (AArch64 Linux), the same headers (the cross GCC's glibc; Clang
and arocc with exactly cbench's Clang setup), and the same defines. The reference compilers get
cbench's flags (-ffp-contract=off, no Nix hardening). Output: OUT (target/projbench) holds a JSON
file per step and report.md.
"""

import argparse
import fcntl
import hashlib
import importlib
import json
import math
import os
import random
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import zipfile
from pathlib import Path
from typing import Any

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parents[1]
sys.path.insert(0, str(ROOT / "benchmarks/c"))
cbench = importlib.import_module("cbench")

# The sources, pinned by SHA-256 (the same files nixpkgs fetches for lua5_4 5.4.7 and sqlite 3.53.3).
SOURCES = {
    "lua-5.4.7.tar.gz": (
        "https://www.lua.org/ftp/lua-5.4.7.tar.gz",
        "9fbf5e28ef86c69858f6d3d34eccc32e911c1a28b4120ff3e84aaa70cfbf1e30",
    ),
    "lua-5.4.7-tests.tar.gz": (
        "https://www.lua.org/tests/lua-5.4.7-tests.tar.gz",
        "8a4898ffe4c7613c8009327a0722db7a41ef861d526c77c5b46114e59ebf811e",
    ),
    "sqlite-src-3530300.zip": (
        "https://sqlite.org/2026/sqlite-src-3530300.zip",
        "bb80bf8a3bffc19241ce8aba5a4bc74e9c3980013cb0b5f0f0976a99516942af",
    ),
}
LUA_TUS = [
    "lapi",
    "lcode",
    "lctype",
    "ldebug",
    "ldo",
    "ldump",
    "lfunc",
    "lgc",
    "llex",
    "lmem",
    "lobject",
    "lopcodes",
    "lparser",
    "lstate",
    "lstring",
    "ltable",
    "ltm",
    "lundump",
    "lvm",
    "lzio",
    "lauxlib",
    "lbaselib",
    "lcorolib",
    "ldblib",
    "liolib",
    "lmathlib",
    "loadlib",
    "loslib",
    "lstrlib",
    "ltablib",
    "lutf8lib",
    "linit",
    "lua",
]
# The seed of Lua's string hashes is fixed: Lua makes it from the time and from addresses, and
# with that every workload's instruction count differed from run to run (by 0.005% to 0.3%, and
# lua-nbody's by 5%), for every compiler. With it fixed they repeat to a few dozen instructions.
LUA_FLAGS = ["-std=c23", "-DLUA_COMPAT_5_3", "-DLUA_USE_POSIX", "-Dluai_makeseed(L)=0u"]
# Lua's own tests that run alone (portable, soft mode), as luascore ran them.
LUA_SUITE = [
    "attrib",
    "bitwise",
    "calls",
    "closure",
    "code",
    "constructs",
    "coroutine",
    "cstack",
    "db",
    "errors",
    "events",
    "files",
    "gc",
    "gengc",
    "goto",
    "literals",
    "locals",
    "math",
    "nextvar",
    "pm",
    "sort",
    "strings",
    "tpack",
    "utf8",
    "vararg",
    "main",
    "bwcoercion",
    "tracegc",
]
SQLITE_FLAGS = [
    "-std=gnu23",
    "-DNDEBUG",
    "-DSQLITE_THREADSAFE=0",
    "-DSQLITE_OMIT_LOAD_EXTENSION",
]
# Lua scripts (BENCH/lua): (argument under qemu, argument timed natively).
LUA_SCRIPTS = {
    "fib": (20, 35),
    "trees": (8, 15),
    "nbody": (2000, 400000),
    "spectral": (40, 400),
    "strings": (2000, 300000),
    "sort": (5000, 400000),
    "fannkuch": (7, 10),
}
SPEEDTEST_SIZE = (5, 60)  # speedtest1 --size: under qemu, natively
# speedtest1's default mix ("mix1") without rtree/10, which needs SQLITE_ENABLE_RTREE.
SPEEDTEST_SET = "main,orm/25,cte/20,json,fp/3,parsenumber/25,star,app"

BUILD_CONFIGS = ["fcc", "fcc-O", "gcc-O0", "gcc-O2", "clang-O0", "clang-O2"]
FRONTENDS = ["gcc", "clang", "arocc"]
REFERENCE = "gcc-O2"


# Why the last `die` stopped the run, for the gate's report.
STOPPED: list[str] = []


def die(msg):
    STOPPED.append(msg)
    print(f"projbench: {msg}", file=sys.stderr)
    sys.exit(1)


def run(cmd, **kw):
    return cbench.run([str(c) for c in cmd], **kw)


def measure(cmd, env, cwd=None, timeout=None):
    """Run cmd: wall seconds, CPU seconds (with waited-for children), peak RSS in KiB, exit code,
    and stderr. After `timeout` seconds it is killed, and `timed_out` says so."""
    t0 = time.perf_counter()
    p = subprocess.Popen(
        [str(c) for c in cmd],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        env=env,
        cwd=cwd,
    )
    assert p.stderr is not None
    killed = []

    def kill():
        killed.append(True)
        p.kill()

    timer = threading.Timer(timeout, kill) if timeout else None
    if timer:
        timer.start()
    err = p.stderr.read().decode(errors="replace")
    _, status, ru = os.wait4(p.pid, 0)
    if timer:
        timer.cancel()
    wall = time.perf_counter() - t0
    p.stderr.close()
    return {
        "wall": wall,
        "cpu": ru.ru_utime + ru.ru_stime,
        "rss_kib": ru.ru_maxrss,
        "exit": os.waitstatus_to_exitcode(status),
        "stderr": err,
        "timed_out": bool(killed),
    }


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(out, name, data):
    (out / f"{name}.json").write_text(json.dumps(data, indent=1, sort_keys=True))


def load(out, name):
    p = out / f"{name}.json"
    return json.loads(p.read_text()) if p.exists() else None


class Setup:
    """The compilers (cbench.Tools for fcc, GCC, and Clang), arocc, and the projects' files."""

    def __init__(self, args):
        self.args = args
        self.tools = cbench.Tools()
        self.out = Path(args.out).resolve()
        self.src = self.out / "src"
        self.arocc = args.arocc or os.environ.get("AROCC")
        self.plain = set(args.plain.split(",")) if args.plain else set()
        self.env = self.tools.env

    def lua_dir(self):
        return self.src / "lua-5.4.7/src"

    def sqlite_dir(self):
        return self.src / "sqlite-src-3530300"

    def projects(self):
        """{project: [(tu name, source path, flags)]}"""
        lua = [(t, self.lua_dir() / f"{t}.c", LUA_FLAGS) for t in LUA_TUS]
        sq = self.sqlite_dir()
        inc = ["-I", str(sq)]
        sqlite = [
            ("sqlite3", sq / "sqlite3.c", SQLITE_FLAGS + inc),
            ("speedtest1", sq / "test/speedtest1.c", SQLITE_FLAGS + inc),
        ]
        return {"lua": lua, "sqlite": sqlite}

    def compile_cmd(self, config, src, flags, obj):
        """cbench's command for config, with the project's flags. A file named in --plain is
        compiled with `fcc -O` under every experimental fcc configuration."""
        if config in cbench.FCC_EXPERIMENTAL and Path(src).stem in self.plain:
            config = "fcc-O"
        cmd = [str(c) for c in self.tools.compile_cmd(config, src, obj)]
        at = 2 if config.startswith("fcc") else 1
        return cmd[:at] + list(flags) + cmd[at:]

    def syntax_cmd(self, frontend, src, flags):
        if frontend == "gcc":
            return [self.tools.cc, "-fsyntax-only", "-w", *flags, src]
        if frontend == "clang":
            return [self.tools.clang, *self.tools.clang_flags, "-fsyntax-only", "-w", *flags, src]
        # arocc with Clang's setup: the target, no system directories (its own builtin headers
        # stay), and the cross GCC's include directories after them.
        inc = [f for f in self.tools.clang_flags if not f.startswith("-resource-dir")]
        inc = [("--target=aarch64-linux-gnu" if f.startswith("--target") else f) for f in inc]
        return [self.arocc, *inc, "-fsyntax-only", "-w", *flags, src]

    def frontends(self):
        return [f for f in FRONTENDS if f != "arocc" or self.arocc]


# ---------------------------------------------------------------------------------------------
# prepare


def source_digest(d):
    """One hash of the C, header, and Lua files under `d`, with their paths: what the builds
    and the workloads read of a fetched source."""
    h = hashlib.sha256()
    for f in sorted(d.rglob("*")):
        if f.suffix in (".c", ".h", ".lua") and f.is_file():
            h.update(str(f.relative_to(d)).encode() + b"\0" + bytes.fromhex(sha256(f)))
    return h.hexdigest()


def cmd_prepare(s):
    """Fetch the sources, check each archive against its pinned hash, and unpack them. An
    unpacked source is ignored by git, so nothing else would notice a change to it: its digest
    (`source_digest`) is written beside it once it is prepared (`NAME.digest`) and checked on
    every later run. A directory without one, unpacked before this check existed, is unpacked
    again from the checked archive."""
    s.src.mkdir(parents=True, exist_ok=True)
    unpacked_dirs = []
    for name, (url, digest) in SOURCES.items():
        f = s.src / name
        if not f.exists():
            run(["curl", "-sfL", url, "-o", f])
        if sha256(f) != digest:
            die(f"{f}: SHA-256 is not {digest}")
        unpacked = s.src / name.removesuffix(".tar.gz").removesuffix(".zip")
        unpacked_dirs.append(unpacked)
        mark = s.src / f"{unpacked.name}.digest"
        if unpacked.exists() and not mark.exists():
            shutil.rmtree(unpacked)
        if unpacked.exists():
            continue
        if name.endswith(".zip"):
            with zipfile.ZipFile(f) as z:
                z.extractall(s.src)
                for info in z.infolist():  # zipfile drops the modes (configure's scripts)
                    if mode := (info.external_attr >> 16) & 0o777:
                        (s.src / info.filename).chmod(mode)
        else:
            with tarfile.open(f) as tf:
                tf.extractall(s.src, filter="data")
    sq = s.sqlite_dir()
    if not (sq / "sqlite3.c").exists():
        # The amalgamation, as SQLite's own build makes it (its bundled jimsh runs the scripts).
        sh = "./configure --disable-tcl >/dev/null && make sqlite3.c >/dev/null"
        run(
            [
                "nix",
                "shell",
                "--inputs-from",
                ROOT,
                "nixpkgs#gnumake",
                "nixpkgs#gcc",
                "-c",
                "sh",
                "-c",
                sh,
            ],
            cwd=sq,
        )
    digests = {}
    for unpacked in unpacked_dirs:
        mark = s.src / f"{unpacked.name}.digest"
        digests[unpacked.name] = now = source_digest(unpacked)
        if not mark.exists():
            mark.write_text(now + "\n")
        elif mark.read_text().strip() != now:
            die(
                f"{unpacked} is not as it was unpacked (its C, header, and Lua files changed): "
                f"remove it and {mark.name} to unpack it again"
            )
    info = {
        "sources": {n: {"url": u, "sha256": d} for n, (u, d) in SOURCES.items()},
        "unpacked": digests,
        "sqlite3_c_sha256": sha256(sq / "sqlite3.c"),
        "sqlite3_c_lines": len((sq / "sqlite3.c").read_bytes().splitlines()),
    }
    save(s.out, "prepare", info)
    print(f"sources in {s.src}", file=sys.stderr)


# ---------------------------------------------------------------------------------------------
# build


def cmd_build(s):
    s.tools.build_fcc()
    obj = s.out / "obj"
    bins = s.out / "bin"
    obj.mkdir(parents=True, exist_ok=True)
    bins.mkdir(parents=True, exist_ok=True)
    projects = s.projects()
    jobs = [
        (p, tu, src, fl, c)
        for p, tus in projects.items()
        for tu, src, fl in tus
        for c in BUILD_CONFIGS
    ]
    runs: dict[str, list] = {}
    for rep in range(s.args.reps):
        random.shuffle(jobs)
        for p, tu, src, fl, c in jobs:
            o = obj / f"{p}.{tu}.{c}.o"
            m = measure(s.compile_cmd(c, src, fl, o), s.env, timeout=s.args.timeout)
            if m["timed_out"]:
                die(f"{c} did not compile {src} in {s.args.timeout} s")
            if m["exit"] != 0:
                die(f"{c} failed on {src}:\n{m['stderr'][-3000:]}")
            runs.setdefault(f"{p}/{tu}/{c}", []).append(
                {k: m[k] for k in ("wall", "cpu", "rss_kib")}
            )
        print(f"build: round {rep + 1} of {s.args.reps}", file=sys.stderr)
    result: dict[str, Any] = {"identity": s.tools.identity(), "reps": s.args.reps, "tus": {}}
    for key, rs in runs.items():
        p, tu, c = key.split("/")
        o = obj / f"{p}.{tu}.{c}.o"
        result["tus"][key] = {
            "wall_min": min(r["wall"] for r in rs),
            "wall_median": statistics.median(r["wall"] for r in rs),
            "cpu_min": min(r["cpu"] for r in rs),
            "rss_kib_max": max(r["rss_kib"] for r in rs),
            "text": s.tools.text_size(o),
            "object_bytes": o.stat().st_size,
        }
    # The binaries: static, linked by the reference GCC as cbench links its programs.
    result["binaries"] = {}
    for c in BUILD_CONFIGS:
        for p, exe, tus in (
            ("lua", "lua", LUA_TUS),
            ("sqlite", "speedtest1", ["sqlite3", "speedtest1"]),
        ):
            out = bins / f"{exe}.{c}"
            objs = [obj / f"{p}.{tu}.{c}.o" for tu in tus]
            run([s.tools.cc, "-static", *objs, "-o", out, f"-L{s.tools.libc}", "-lm"], env=s.env)
            result["binaries"][f"{exe}.{c}"] = {
                "sha256": sha256(out),
                "bytes": out.stat().st_size,
                "text": s.tools.text_size(out),
            }
    # Where fcc's time goes, from separate FIR_TIME=1 runs (one per file, -O and not).
    phases: dict[str, dict] = {}
    env = dict(s.env, FIR_TIME="1")
    for p, tus in projects.items():
        for c in ("fcc", "fcc-O"):
            total: dict[str, float] = {}
            for _tu, src, fl in tus:
                m = measure(s.compile_cmd(c, src, fl, obj / "phase.o"), env)
                for name, ms in phases_of(m["stderr"]).items():
                    total[name] = total.get(name, 0.0) + ms
            phases[f"{p}/{c}"] = total
    result["phases"] = phases
    result["loadavg_end"] = Path("/proc/loadavg").read_text().split()[:3]
    save(s.out, "build", result)


def phases_of(stderr):
    """fir::timing's report: {phase: self ms} ('*' marks phases summed over worker threads)."""
    out: dict[str, float] = {}
    for line in stderr.splitlines():
        if not line.startswith("fir: time:") or "self ms" in line or "summed over" in line:
            continue
        parts = line[len("fir: time:") :].split()
        if not parts:
            continue
        ms = float(parts[0])
        rest = parts[1:]
        if rest and rest[0].endswith("%"):
            rest = rest[1:]
        if rest and rest[0].isdigit():
            rest = rest[1:]
        name = " ".join(rest)
        out[name] = out.get(name, 0.0) + ms
    return out


# ---------------------------------------------------------------------------------------------
# frontend: parse and check only


def cmd_frontend(s):
    gen = s.out / "gen"
    gen.mkdir(parents=True, exist_ok=True)
    inputs: list[tuple[str, str, Path, list]] = []
    for p, tus in s.projects().items():
        inputs += [(p, tu, src, fl) for tu, src, fl in tus]
    for prog in sorted((ROOT / "benchmarks/c/programs").glob("*.c")):
        inputs.append(("programs", prog.stem, prog, []))
    for nf, ns in ((1600, 10), (1, 6400)):
        f = gen / f"gen-{nf}x{ns}.c"
        f.write_text(cbench.synth(nf, ns))
        inputs.append(("generated", f.stem, f, []))
    fes = s.frontends()
    jobs = [(g, n, src, fl, fe) for g, n, src, fl in inputs for fe in fes]
    runs: dict[str, list] = {}
    errors: dict[str, str] = {}
    for rep in range(s.args.reps):
        random.shuffle(jobs)
        for g, n, src, fl, fe in jobs:
            m = measure(s.syntax_cmd(fe, src, fl), s.env)
            key = f"{g}/{n}/{fe}"
            if m["exit"] != 0:
                errors[key] = m["stderr"][-2000:]
                continue
            runs.setdefault(key, []).append(m)
        print(f"frontend: round {rep + 1} of {s.args.reps}", file=sys.stderr)
    result: dict[str, Any] = {"runs": {}, "errors": errors, "reps": s.args.reps}
    for key, rs in runs.items():
        result["runs"][key] = {
            "wall_min": min(r["wall"] for r in rs),
            "cpu_min": min(r["cpu"] for r in rs),
            "rss_kib_max": max(r["rss_kib"] for r in rs),
        }
    # fcc's frontend (Clang's parse and analysis, then lowering the AST to HFIR) from its phases.
    env = dict(s.env, FIR_TIME="1")
    fcc_fe = {}
    for g, n, src, fl in inputs:
        best = None
        for _ in range(s.args.reps):
            m = measure(s.compile_cmd("fcc", src, fl, s.out / "phase.o"), env)
            ph = phases_of(m["stderr"])
            clang = sum(v for k, v in ph.items() if k.lower().startswith("fcc: clang"))
            lower = sum(v for k, v in ph.items() if k.lower().startswith("fcc: lower ast"))
            if best is None or clang + lower < best["clang_ms"] + best["lower_ms"]:
                best = {"clang_ms": clang, "lower_ms": lower}
        fcc_fe[f"{g}/{n}"] = best
    result["fcc"] = fcc_fe
    if s.arocc:
        result["arocc_version"] = cbench.first_line([s.arocc, "--version"])
        result["arocc_revision"] = arocc_revision(s.arocc)
    result["lines"] = {
        f"{g}/{n}": len(Path(src).read_bytes().splitlines()) for g, n, src, _ in inputs
    }
    # Preprocessed size: what the parsers actually read.
    result["preprocessed_lines"] = {}
    for g, n, src, fl in inputs:
        if g in ("lua", "sqlite"):
            e = run([s.tools.cc, "-E", "-P", "-w", *fl, src], env=s.env).stdout
            result["preprocessed_lines"][f"{g}/{n}"] = e.count("\n")
    save(s.out, "frontend", result)


def arocc_revision(path):
    """The arocc checkout's commit, if `path` sits in one (zig-out/bin/arocc)."""
    repo = Path(path).resolve().parents[2]
    p = subprocess.run(
        ["git", "-C", str(repo), "log", "-1", "--format=%h %cs"], capture_output=True, text=True
    )
    return p.stdout.strip() if p.returncode == 0 else None


# ---------------------------------------------------------------------------------------------
# check: behavior under qemu


def guest_env():
    """The environment the behavior checks run in: the host's, without what changes what Lua
    or QEMU does (`LUA_INIT` runs code before every script; `QEMU_*` sets QEMU's options)."""
    return {k: v for k, v in os.environ.items() if not k.startswith(("LUA_", "QEMU_"))}


def qemu(exe, args, cwd=None, timeout=900):
    cmd = ([] if s_native() else ["qemu-aarch64"]) + [str(exe), *map(str, args)]
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout, env=guest_env())
    return p.returncode, p.stdout


def s_native():
    return os.uname().machine == "aarch64"


def cmd_check(s):
    bins = s.out / "bin"
    result: dict[str, Any] = {"lua_scripts": {}, "lua_suite": {}, "speedtest": {}}
    for name, (small, _) in LUA_SCRIPTS.items():
        ref = qemu(bins / f"lua.{REFERENCE}", [BENCH / "lua" / f"{name}.lua", small])
        for c in BUILD_CONFIGS:
            got = qemu(bins / f"lua.{c}", [BENCH / "lua" / f"{name}.lua", small])
            result["lua_scripts"][f"{name}/{c}"] = got == ref and ref[0] == 0
    tests = s.src / "lua-5.4.7-tests"
    for c in BUILD_CONFIGS:
        passed = []
        for t in LUA_SUITE:
            try:
                code, _ = qemu(
                    bins / f"lua.{c}", ["-e", "_port=true; _soft=true", f"{t}.lua"], cwd=tests
                )
            except subprocess.TimeoutExpired:
                code = -1
            if code == 0:
                passed.append(t)
        result["lua_suite"][c] = passed
        print(f"check: Lua suite, {c}: {len(passed)} of {len(LUA_SUITE)}", file=sys.stderr)
    for c in BUILD_CONFIGS:
        code, out = qemu(
            bins / f"speedtest1.{c}",
            ["--size", SPEEDTEST_SIZE[0], "--memdb", "--verify", "--testset", SPEEDTEST_SET],
        )
        m = re.search(rb"Verification Hash: (.*)", out)
        result["speedtest"][c] = {"exit": code, "hash": m.group(1).decode() if m else None}
    save(s.out, "check", result)


# ---------------------------------------------------------------------------------------------
# count: executed instructions under qemu (exact), as cbench counts the kernels


def merged(ranges):
    out: list[tuple[int, int]] = []
    for lo, hi in sorted(ranges):
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def code_ranges(mapfile, obj):
    """cbench.program_ranges, but empty for an object with no code (GCC's lctype.o is a table)."""
    try:
        return cbench.program_ranges(mapfile, obj)
    except SystemExit:
        return []


def counted_workloads(work):
    """The workloads `count` and `forms` run under the plugin: (program, name, arguments), each to
    be run in `work` as `./PROGRAM.CONFIG ARGUMENTS`, with Lua's scripts copied there.

    A counted run names its program and its script without a directory, because what a program
    is told is part of what it does: Lua keeps the script's path in every function it loads, so
    a longer path is more memory, and its collector, which is paced by memory, then runs at
    other points. With the paths as they were (absolute), lua-trees executed 2.3% fewer
    instructions in an output directory five letters shorter. A count must not depend on where
    the tree or the output directory is."""
    for n in LUA_SCRIPTS:
        shutil.copyfile(BENCH / "lua" / f"{n}.lua", work / f"{n}.lua")
    workloads: list[tuple[str, str, list[Any]]] = [
        ("lua", f"lua-{n}", [f"{n}.lua", a[0]]) for n, a in LUA_SCRIPTS.items()
    ]
    workloads.append(
        (
            "speedtest1",
            "speedtest1",
            ["--size", SPEEDTEST_SIZE[0], "--memdb", "--testset", SPEEDTEST_SET],
        )
    )
    return workloads


def cmd_count(s):
    """Every workload of every build under cbench's QEMU plugin: executed instructions in the
    project's own code and in libc, their mix, and the own code's memory accesses. The binaries
    are linked again with a linker map (the same bytes as `build`'s, which this checks)."""
    if s_native():
        die("count needs qemu-aarch64's plugin: run it off AArch64")
    build = load(s.out, "build")
    if not build:
        die("run `projbench.py build` first")
    tools = s.tools
    so = cbench.plugin(tools, s.out)
    work = s.out / "count"
    work.mkdir(exist_ok=True)
    obj = s.out / "obj"
    workloads = counted_workloads(work)
    tus = {
        "lua": [("lua", t) for t in LUA_TUS],
        "speedtest1": [("sqlite", "sqlite3"), ("sqlite", "speedtest1")],
    }
    result: dict[str, Any] = {"programs": {}, "failures": []}
    for exe_name, files in tus.items():
        for c in BUILD_CONFIGS:
            exe = work / f"{exe_name}.{c}"
            mapfile = work / f"{exe_name}.{c}.map"
            objs = [obj / f"{p}.{tu}.{c}.o" for p, tu in files]
            run(
                [
                    tools.cc,
                    "-static",
                    *objs,
                    "-o",
                    exe,
                    f"-L{tools.libc}",
                    "-lm",
                    f"-Wl,-Map={mapfile}",
                ],
                env=s.env,
            )
            if sha256(exe) != build["binaries"][f"{exe_name}.{c}"]["sha256"]:
                die(f"{exe}: linking again made other bytes than `build`")
            ranges = merged(r for o in objs for r in code_ranges(mapfile, o))
            if not ranges:
                die(f"{exe.name}: none of its objects' code is in the linker map {mapfile}")
            for prog, name, args in workloads:
                if prog != exe_name:
                    continue
                trace = work / f"{name}.{c}.trace"
                # A trace left by an earlier run must not be read as this run's.
                trace.unlink(missing_ok=True)
                plug = (
                    f"{so},outfile={trace},below={cbench.STACK_BELOW},"
                    f"above={cbench.STACK_ABOVE},deep={cbench.STACK_DEEP}"
                )
                cmd = [
                    "env",
                    "-i",
                    shutil.which("qemu-aarch64"),
                    "-s",
                    cbench.QEMU_STACK,
                    "-strace",
                    "-plugin",
                    plug,
                    f"./{exe.name}",
                    *args,
                ]
                p = run(cmd, check=False, timeout=3600, cwd=work)
                if not trace.exists():
                    die(f"{name} {c}: the plugin wrote no trace (exit {p.returncode})")
                a = cbench.analyze_ranges(tools, exe, ranges, trace)
                lo, hi = a.pop("window")
                if any(x < hi and lo < y for x, y in cbench.mappings(p.stderr)):
                    result["failures"].append(f"{name} {c}: a mapping meets the stack window")
                if a["deep_accesses"]:
                    result["failures"].append(f"{name} {c}: stack deeper than the window")
                a["exit"] = p.returncode
                a["stdout_sha256"] = hashlib.sha256(p.stdout.encode()).hexdigest()
                result["programs"].setdefault(name, {})[c] = a
                trace.unlink()
                print(
                    f"count: {name} {c}: {a['program'] / 1e6:,.1f}M own, "
                    f"{a['library'] / 1e6:,.1f}M libc",
                    file=sys.stderr,
                )
    # speedtest1 prints its timings: only Lua's outputs must be the same bytes.
    for name, cfgs in result["programs"].items():
        ref = cfgs[REFERENCE]
        for c, a in cfgs.items():
            same = a["exit"] == 0 and (
                name == "speedtest1" or a["stdout_sha256"] == ref["stdout_sha256"]
            )
            if not same:
                result["failures"].append(f"{name} {c}: exit {a['exit']} or output differs")
    save(s.out, "count", result)
    if result["failures"]:
        die("count failed:\n  " + "\n  ".join(result["failures"]))


# ---------------------------------------------------------------------------------------------
# forms: executed instructions by form, and the stack's accesses by kind


# The registers fai's allocator loads spilled values into and stores them from (regalloc.rs).
SPILL_REGS = {"x15", "x17", "w15", "w17", "d29", "d30", "d31", "s29", "s30", "s31"}
SAVED_REGS = {f"x{i}" for i in range(19, 31)} | {f"d{i}" for i in range(8, 16)}
EXTENDS = {"sxtw", "sxtb", "sxth", "uxtb", "uxth", "ubfx", "sbfx", "ubfiz", "sbfiz"}
FLAG_TO_REG = {"cset", "csetm", "csel", "csinc", "csinv", "csneg", "cinc", "cneg"}
COMPARES = {"cmp", "cmn", "ccmp", "ccmn", "fcmp", "fcmpe"}
MULTIPLIES = {"mul", "madd", "msub", "mneg", "smull", "umull", "smulh", "umulh", "smaddl", "umaddl"}
LOGIC = {"and", "ands", "orr", "eor", "bic", "bics", "orn", "eon", "mvn", "neg", "negs"}
# The interpreter loops, counted apart from the rest of each project.
HOT = ("luaV_execute", "sqlite3VdbeExec")
FORMS_DEFAULT = ["fcc-O", "gcc-O0", "clang-O0"]


def split_ops(ops):
    """An instruction's operands, a memory operand `[…]` kept whole."""
    out, depth, cur = [], 0, ""
    for ch in ops:
        depth += (ch == "[") - (ch == "]")
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def mem_base(o):
    """The base register of the instruction's memory operand, if it has one."""
    for x in o:
        if x.startswith("["):
            return x[1:].split("]")[0].split(",")[0].strip()
    return None


def insn_form(mn, o):
    """The form of an instruction that isn't a load or a store, by mnemonic and operands as
    objdump prints them (aliases included: `sbfx x, x, #0, #32` is `sxtw`, a `movz` is `mov`)."""
    if mn in ("mov", "movz", "movn", "movk", "fmov"):
        if mn == "movk" or (len(o) > 1 and o[1].startswith("#")):
            return "constant into a register"
        if len(o) > 1 and o[1] == "sp":
            return "frame address"
        if o and o[0] == "sp":
            return "stack pointer adjustment"
        return "register copy"
    if mn in EXTENDS:
        return "extension"
    if mn == "asr" and len(o) == 3 and o[2] == "#0":
        return "shift by zero"
    if mn in FLAG_TO_REG:
        return "flags into a register"
    if mn == "tst":
        return "test of a register"
    if mn in COMPARES:
        return "compare"
    if mn in MULTIPLIES:
        return "multiply"
    if mn in ("add", "sub", "adds", "subs"):
        if o and o[0] == "sp":
            return "stack pointer adjustment"
        if len(o) > 1 and o[1] == "sp":
            return "frame address"
        if any(x.startswith("#") for x in o[2:]):
            return "add or subtract an immediate"
        return "add or subtract registers"
    if mn in ("lsl", "lsr", "asr", "ror"):
        return "shift"
    if mn in LOGIC:
        return "logic"
    if mn == "b":
        return "jump"
    if mn.startswith("b.") or mn in ("cbz", "cbnz", "tbz", "tbnz"):
        return "conditional branch"
    if mn == "br":
        return "indirect jump"
    if mn in ("bl", "blr", "ret"):
        return "call or return"
    if mn in ("adrp", "adr"):
        return "address of a global"
    if cbench.FP.match(mn):
        return "float"
    return "other"


def mem_form(mn, o):
    """A load's or store's form when its registers alone decide it: spill code (a scratch
    register to or from the frame), or a save or restore of a callee-saved register."""
    load = bool(cbench.LOAD.match(mn))
    data = [x for x in o if not x.startswith(("[", "#"))]
    base = mem_base(o)
    if data and all(d in SPILL_REGS for d in data) and base in ("sp", "x16"):
        return "spill reload" if load else "spill store"
    if data and all(d in SAVED_REGS for d in data) and base in ("sp", "x29"):
        return "register restore" if load else "register save"
    return None


def forms_of_run(tools, exe, ranges, trace):
    """One run's executed instructions by form, in all of the program's code and in its
    interpreter loop; what follows each constant; what each spill reload is for; and the
    stack's accesses by the form of the instruction making them."""
    import bisect

    insns, syms = cbench.disassemble(tools, exe, ranges)
    starts = [a for a, _ in syms]

    def inside(a):
        return any(lo <= a < hi for lo, hi in ranges)

    execs: dict[int, int] = {}
    mem: dict[int, list[int]] = {}
    for line in trace.read_text().splitlines():
        kind, *f = line.split()
        if kind == "B":
            vaddr, n, count = int(f[0], 16), int(f[1]), int(f[2])
            for i in range(n):
                a = vaddr + 4 * i
                if inside(a):
                    execs[a] = execs.get(a, 0) + count
        elif kind == "M":
            a = int(f[0], 16)
            if inside(a):
                m = mem.setdefault(a, [0, 0, 0, 0])
                for i, v in enumerate(f[1:5]):
                    m[i] += int(v)
    out: dict[str, dict[str, float]] = {
        "all": {},
        "hot": {},
        "after_constant": {},
        "reload_for": {},
        "stack_accesses": {},
    }

    def add(table, key, n):
        out[table][key] = out[table].get(key, 0) + n

    for a, count in execs.items():
        mn, ops = insns.get(a, ("?", ""))
        o = split_ops(ops)
        k = bisect.bisect_right(starts, a) - 1
        hot = k >= 0 and syms[k][1].startswith(HOT)
        is_mem = "[" in ops and (cbench.LOAD.match(mn) or cbench.STORE.match(mn))
        if not is_mem:
            parts = {insn_form(mn, o): 1.0}
        else:
            load = bool(cbench.LOAD.match(mn))
            sl, ss, ol, os_ = mem.get(a, [0, 0, 0, 0])
            total = sl + ss + ol + os_
            share = (sl + ss) / total if total else 0.0
            fixed = mem_form(mn, o)
            if fixed:
                parts = {fixed: 1.0}
                add("stack_accesses", fixed, sl + ss)
            else:
                word = "load" if load else "store"
                parts = {f"stack {word}": share, f"other {word}": 1.0 - share}
                add("stack_accesses", f"stack {word}", sl + ss)
        for form, w in parts.items():
            if w:
                add("all", form, count * w)
                if hot:
                    add("hot", form, count * w)
        nxt = insns.get(a + 4)
        if nxt and "constant into a register" in parts:
            no = split_ops(nxt[1])
            reg = o[0].lstrip("wx") if o else ""
            reads = any(x.lstrip("wx") == reg for x in no[1:]) or (
                nxt[0] in COMPARES | {"tst"} and no and no[0].lstrip("wx") == reg
            )
            add("after_constant", nxt[0] if reads else "(not read next)", count)
        if nxt and "spill reload" in parts:
            reg = next((x for x in o if x in SPILL_REGS), "")
            base = mem_base(split_ops(nxt[1]))
            as_address = base is not None and base.lstrip("wx") == reg.lstrip("wx")
            add("reload_for", "an address" if as_address else "a value", count)
    return out


def cmd_forms(s):
    """Every workload of some builds (`--configs`, or fcc -O and GCC and Clang at -O0) under
    cbench's QEMU plugin, as `count` runs them, with each executed instruction named by form:
    what instruction selection, the allocator, and the frontend each cost. Writes forms.json
    and forms.md."""
    if s_native():
        die("forms needs qemu-aarch64's plugin: run it off AArch64")
    if not load(s.out, "build"):
        die("run `projbench.py build` first")
    configs = BUILD_CONFIGS if s.args.configs else FORMS_DEFAULT
    tools = s.tools
    so = cbench.plugin(tools, s.out)
    work = s.out / "forms"
    work.mkdir(exist_ok=True)
    obj = s.out / "obj"
    workloads = counted_workloads(work)
    tus = {
        "lua": [("lua", t) for t in LUA_TUS],
        "speedtest1": [("sqlite", "sqlite3"), ("sqlite", "speedtest1")],
    }
    result: dict[str, Any] = {"configs": configs, "programs": {}}
    for exe_name, files in tus.items():
        for c in configs:
            exe = work / f"{exe_name}.{c}"
            mapfile = work / f"{exe_name}.{c}.map"
            objs = [obj / f"{p}.{tu}.{c}.o" for p, tu in files]
            link = [tools.cc, "-static", *objs, "-o", exe, f"-L{tools.libc}", "-lm"]
            run([*link, f"-Wl,-Map={mapfile}"], env=s.env)
            ranges = merged(r for o in objs for r in code_ranges(mapfile, o))
            if not ranges:
                die(f"{exe.name}: none of its objects' code is in the linker map {mapfile}")
            for prog, name, args in workloads:
                if prog != exe_name:
                    continue
                trace = work / f"{name}.{c}.trace"
                # A trace left by an earlier run must not be read as this run's.
                trace.unlink(missing_ok=True)
                plug = (
                    f"{so},outfile={trace},below={cbench.STACK_BELOW},"
                    f"above={cbench.STACK_ABOVE},deep={cbench.STACK_DEEP}"
                )
                qemu_cmd = ["env", "-i", shutil.which("qemu-aarch64"), "-s", cbench.QEMU_STACK]
                p = run(
                    [*qemu_cmd, "-plugin", plug, f"./{exe.name}", *args],
                    check=False,
                    timeout=3600,
                    cwd=work,
                )
                if p.returncode != 0:
                    die(f"forms: {name} {c} exited with {p.returncode}")
                if not trace.exists():
                    die(f"forms: {name} {c}: the plugin wrote no trace")
                result["programs"].setdefault(name, {})[c] = forms_of_run(tools, exe, ranges, trace)
                trace.unlink()
                print(f"forms: {name} {c}", file=sys.stderr)
    save(s.out, "forms", result)
    (s.out / "forms.md").write_text(forms_report(result))
    print(f"wrote {s.out / 'forms.md'}", file=sys.stderr)


def forms_report(result):
    """forms.json as tables: Lua's workloads summed, then speedtest1."""
    configs = result["configs"]
    groups = {
        "Lua (7 workloads)": [p for p in result["programs"] if p.startswith("lua-")],
        "speedtest1": [p for p in result["programs"] if p == "speedtest1"],
    }

    def total(progs, c, which):
        acc: dict[str, float] = {}
        for p in progs:
            for k, v in result["programs"][p][c][which].items():
                acc[k] = acc.get(k, 0) + v
        return acc

    def mil(x):
        return f"{x / 1e6:,.1f}"

    lines = ["# Executed instructions by form", ""]
    for title, progs in groups.items():
        if not progs:
            continue
        for which, what in (("all", "the project's own code"), ("hot", "the interpreter loop")):
            data = {c: total(progs, c, which) for c in configs}
            forms = sorted(
                {k for d in data.values() for k in d}, key=lambda k: -data[configs[0]].get(k, 0)
            )
            lines += [f"## {title}: {what} (millions)", ""]
            rows = [[f, *[mil(data[c].get(f, 0)) for c in configs]] for f in forms]
            rows.append(["**all**", *[f"**{mil(sum(data[c].values()))}**" for c in configs]])
            lines += [table(["form", *configs], rows), ""]
        for which, what in (
            ("after_constant", "the instruction after each constant, when it reads it"),
            ("reload_for", "what a spill reload is for, by the next instruction"),
            ("stack_accesses", "accesses to the stack, by the form of the instruction"),
        ):
            data = {c: total(progs, c, which) for c in configs}
            keys = sorted(
                {k for d in data.values() for k in d}, key=lambda k: -data[configs[0]].get(k, 0)
            )[:12]
            if not keys:
                continue
            lines += [f"## {title}: {what} (millions)", ""]
            rows = [[k, *[mil(data[c].get(k, 0)) for c in configs]] for k in keys]
            lines += [table(["", *configs], rows), ""]
    return "\n".join(lines)


# ---------------------------------------------------------------------------------------------
# gate: does this tree build both projects correctly, and no worse than the accepted baseline?


GATE = Path(__file__).resolve().parent / "gate.json"
# A build may take this many times the baseline's compile time and memory, plus a second: they
# are measured once, on whatever else the host is doing.
GATE_SLACK = 2.0
# The gate's exit statuses: the tree passed, the tree failed, or the gate could not judge it.
GATE_PASS, GATE_FAIL, GATE_NOT_RUN = 0, 1, 2
# How far a workload's instruction count may sit from the baseline's and still be the same:
# one part in 100,000. With Lua's hash seed fixed (LUA_FLAGS), every workload's count repeats to
# within a few dozen instructions, in tens of millions to billions.
GATE_SAME = 1e-5


def gate_measure(s, configs):
    """What the gate compares, from build.json, check.json, and count.json: per configuration,
    whether both projects behave as the reference build does, the instructions each workload
    executes, each project's code size, and its compile time and peak memory."""
    build, check, count = load(s.out, "build"), load(s.out, "check"), load(s.out, "count")
    out: dict[str, Any] = {}
    for c in configs:
        tus = {k: v for k, v in build["tus"].items() if k.endswith(f"/{c}")}
        projects = sorted({k.split("/")[0] for k in tus})
        ref = check["speedtest"][REFERENCE]
        st = check["speedtest"][c]
        out[c] = {
            "behavior": {
                "lua workloads match": all(check["lua_scripts"][f"{n}/{c}"] for n in LUA_SCRIPTS),
                "lua suite files passed": len(check["lua_suite"][c]),
                # Against a reference that verified itself: its hash alone is no witness.
                "speedtest1 verifies": st["exit"] == 0
                and ref["exit"] == 0
                and bool(ref["hash"])
                and st["hash"] == ref["hash"],
            },
            # The project's own code, where a compiler change shows undiluted, and the whole
            # run with libc: work moved into libc (a call where a loop was) is still work.
            "instructions": {w: count["programs"][w][c]["program"] for w in count["programs"]},
            "total_instructions": {w: count["programs"][w][c]["total"] for w in count["programs"]},
            # The ten functions that execute most, per workload: they explain a failure
            # (gate_slower_functions) and decide nothing.
            "functions": {
                w: count["programs"][w][c].get("functions", {}) for w in count["programs"]
            },
            "text": {
                p: sum(v["text"] for k, v in tus.items() if k.startswith(f"{p}/")) for p in projects
            },
            # CPU time, the compiler's and its children's: wall time doubles on a busy host.
            "compile_cpu_seconds": {
                p: round(sum(v["cpu_min"] for k, v in tus.items() if k.startswith(f"{p}/")), 2)
                for p in projects
            },
            "compile_rss_kib": {
                p: max(v["rss_kib_max"] for k, v in tus.items() if k.startswith(f"{p}/"))
                for p in projects
            },
        }
    return out


def gate_expected():
    """What every measurement must cover, on both sides: each workload (`count`) and each
    project (`build`). A side that lacks one wasn't measured, whatever the other side lacks."""
    workloads = {f"lua-{n}" for n in LUA_SCRIPTS} | {"speedtest1"}
    projects = {"lua", "sqlite"}
    return {
        "instructions": workloads,
        "total_instructions": workloads,
        "text": projects,
        "compile_cpu_seconds": projects,
        "compile_rss_kib": projects,
    }


def gate_number(x):
    """Whether `x` is a measurement: a finite number above zero."""
    return isinstance(x, (int, float)) and not isinstance(x, bool) and math.isfinite(x) and x > 0


# What a baseline holds per configuration besides behavior, each by workload or by project.
GATE_DIMENSIONS = (
    "instructions",
    "total_instructions",
    "text",
    "compile_cpu_seconds",
    "compile_rss_kib",
)


def gate_compare(now, base, first=False):
    """What got worse and what got better, as sentences. Behavior, instruction counts (to within
    GATE_SAME, in the project's own code and in all), and code size may not get worse at all;
    compile time and memory may reach GATE_SLACK times the baseline's (plus a second, or 64
    MiB). Both sides must have every measurement: one that is missing, new, or not above zero
    is worse, not skipped. `first` is the first baseline of all, where there is nothing to
    compare with and only behavior and the measurements' presence count."""
    worse, better = [], []
    want = {
        "lua workloads match": True,
        "lua suite files passed": len(LUA_SUITE),
        "speedtest1 verifies": True,
    }
    for k, v in want.items():
        if now["behavior"][k] != v:
            worse.append(f"behavior: {k}: {now['behavior'][k]}, not {v}")
    counted = ("instructions", "total_instructions")
    expected = gate_expected()
    for dim in GATE_DIMENSIONS:
        have = now.get(dim)
        have = have if isinstance(have, dict) else {}
        for k in sorted(expected[dim] - have.keys()):
            worse.append(f"{dim}: {k} was not " + ("run" if dim in counted else "measured"))
        for k, n in have.items():
            if not gate_number(n):
                worse.append(f"{dim}: {k} measured {n}: the measurement is broken")
        if first:
            continue
        b = base.get(dim)
        if not isinstance(b, dict):
            worse.append(f"{dim}: the baseline has none: make the baseline again")
            continue
        for k in sorted(expected[dim] - b.keys()):
            worse.append(f"{dim}: {k} has no baseline: add it to gate.json")
        for k in sorted(have.keys() - b.keys() - expected[dim]):
            worse.append(f"{dim}: {k} has no baseline: add it to gate.json")
        for k, n in b.items():
            if not gate_number(n):
                worse.append(f"{dim}: the baseline's {k} is {n}: make the baseline again")
    if first:
        return worse, better

    def both(dim):
        have, b = now.get(dim), base.get(dim)
        if not isinstance(have, dict) or not isinstance(b, dict):
            return []
        return [
            (k, have[k], v) for k, v in b.items() if gate_number(v) and gate_number(have.get(k))
        ]

    def by(n, b):
        return f"{n / b - 1:+.2%}" if b else "from nothing"

    for w, n, b in both("instructions"):
        if n > b * (1 + GATE_SAME):
            worse.append(f"instructions: {w} executes {n:,}, more than {b:,} ({by(n, b)})")
            for f, after, before in gate_slower_functions(now, base, w):
                worse.append(
                    f"    in {f}: {after:,}, "
                    + (
                        f"{after - before:+,} ({by(after, before)})"
                        if before
                        else "new among the ten busiest"
                    )
                )
        elif n < b * (1 - GATE_SAME):
            better.append(f"instructions: {w} executes {n:,}, fewer than {b:,} ({by(n, b)})")
    for w, n, b in both("total_instructions"):
        if n > b * (1 + GATE_SAME):
            worse.append(
                f"instructions in all: {w} executes {n:,} with libc, more than {b:,} ({by(n, b)})"
            )
            for f, after, before in gate_slower_functions(now, base, w):
                worse.append(
                    f"    in {f}: {after:,}, "
                    + (
                        f"{after - before:+,} ({by(after, before)})"
                        if before
                        else "new among the ten busiest"
                    )
                )
        elif n < b * (1 - GATE_SAME):
            better.append(
                f"instructions in all: {w} executes {n:,} with libc, fewer than {b:,} ({by(n, b)})"
            )
    for p, n, b in both("text"):
        if n > b:
            worse.append(f"code size: {p}'s .text is {n:,} bytes, more than {b:,} ({by(n, b)})")
        elif n < b:
            better.append(f"code size: {p}'s .text is {n:,} bytes, less than {b:,} ({by(n, b)})")
    for p, n, b in both("compile_cpu_seconds"):
        if n > GATE_SLACK * b + 1.0:
            worse.append(
                f"compile time: {p} takes {n:.2f} s of CPU, over {GATE_SLACK:g} times {b:.2f} s"
            )
    for p, n, b in both("compile_rss_kib"):
        if n > GATE_SLACK * b + (64 << 10):
            worse.append(
                f"compile memory: {p} peaks at {n >> 10} MiB, over {GATE_SLACK:g} times {b >> 10} MiB"
            )
    return worse, better


def gate_slower_functions(now, base, workload, most=5):
    """Where a workload's extra instructions are: the functions among its ten busiest that
    execute more than in the baseline, most first, as (name, now, before), and after them those
    that weren't among the baseline's ten (`before` is None: how much they rose isn't known). A
    local function's name ends in a hash of its file (`f.l8bbbcbfa`), which is dropped, since it
    differs between trees; functions that then share a name are counted together. This explains
    a failure and never decides one: the verdict is on the workload's total."""

    def plain(side):
        out: dict[str, int] = {}
        for f, n in ((side.get("functions") or {}).get(workload) or {}).items():
            name = re.sub(r"\.l[0-9a-f]{8}$", "", f)
            out[name] = out.get(name, 0) + n
        return out

    after, before = plain(now), plain(base)
    if not after or not before:
        return []
    rose = [(f, n, before[f]) for f, n in after.items() if f in before and n > before[f]]
    rose.sort(key=lambda r: -(r[1] - r[2]))
    new = sorted(((f, n, None) for f, n in after.items() if f not in before), key=lambda r: -r[1])
    return (rose + new)[:most]


def gate_verdict(now, baseline, gated, plain):
    """The verdict and its reasons, from the measurements alone: per gated configuration, what
    is worse and what is better than the baseline it is held to (its own, or `fcc -O`'s when it
    has none: a pipeline proposed for `-O` must not be worse than `-O`). FAIL if anything is
    worse, or if the baseline has neither. With no baseline at all (`baseline` is None: the
    first one is being made) only behavior and the measurements themselves are judged. With
    `plain` (files compiled another way, which were therefore not judged) the best verdict is
    PARTIAL, which is not a pass."""
    report: dict[str, Any] = {"verdict": "PASS", "configs": {}}
    for c in gated:
        if baseline is None:
            base_of, base = c, {}
        else:
            base_of = c if c in baseline["configs"] else "fcc-O"
            base = baseline["configs"].get(base_of)
            if base is None:
                why = f"the baseline has neither {c} nor fcc-O to hold it to"
                report["configs"][c] = {"against": None, "worse": [why], "better": []}
                report["verdict"] = "FAIL"
                continue
        worse, better = gate_compare(now[c], base, first=baseline is None)
        report["configs"][c] = {"against": base_of, "worse": worse, "better": better}
        if worse:
            report["verdict"] = "FAIL"
    if report["verdict"] == "PASS" and plain:
        report["verdict"] = "PARTIAL"
        report["plain"] = sorted(plain)
    return report


def gate_updated(configs, now, gated):
    """The baseline's configurations after `--update` (which runs only on a PASS): the gated
    ones take the new measurements, except that a baseline only ever gets better than what the
    configuration was held to, its own or `fcc -O`'s. A count that is the same (within
    GATE_SAME) keeps the old value, and code size, time, and memory keep the lower one."""
    configs = dict(configs)
    for c in gated:
        own = configs.get(c)
        held = own or configs.get("fcc-O")
        new = json.loads(json.dumps(now[c]))
        if held:
            for dim in ("instructions", "total_instructions"):
                for w, n in new[dim].items():
                    b = held.get(dim, {}).get(w, n)
                    new[dim][w] = n if n < b * (1 - GATE_SAME) else b
            for dim in ("text", "compile_cpu_seconds", "compile_rss_kib"):
                for p, n in new[dim].items():
                    new[dim][p] = min(n, held.get(dim, {}).get(p, n))
        if held:
            # The per-function counts explain and don't gate: they go with the count kept,
            # whichever baseline it was kept from.
            for w, n in new["instructions"].items():
                if n == held["instructions"].get(w) and w in (held.get("functions") or {}):
                    new["functions"][w] = held["functions"][w]
        configs[c] = new
    return configs


def gate_check_baseline(baseline):
    """Raise if `baseline` isn't shaped as `--update` writes it: configurations of
    dimensions of numbers (each number is judged in `gate_compare`)."""
    configs = baseline["configs"]
    if not isinstance(configs, dict):
        raise TypeError("configs is not an object")
    for c, v in configs.items():
        if not isinstance(v, dict):
            raise TypeError(f"{c} is not an object")
        for dim in GATE_DIMENSIONS:
            if dim in v and not isinstance(v[dim], dict):
                raise TypeError(f"{c}'s {dim} is not an object")


def gate_lua_sources(unpacked):
    """The digests of Lua's sources and tests, which are unpacked from pinned archives and so
    the same everywhere. (SQLite's tree also holds the amalgamation its build generates, whose
    bytes needn't be the same on every host: it is checked against its own record only.)"""
    return {k: v for k, v in unpacked.items() if k.startswith("lua-")}


def gate_check_sources(s, before, baseline):
    """Stop the gate if the sources changed during the run, or aren't those the baseline was
    measured on."""
    for name, digest in (before or {}).items():
        if source_digest(s.src / name) != digest:
            die(f"{s.src / name} changed while the gate ran")
    want = (baseline or {}).get("sources") or {}
    for name, digest in want.items():
        if (before or {}).get(name) != digest:
            die(
                f"{s.src / name} is not what the baseline was measured on: remove it and its "
                ".digest to unpack it again"
            )


def gate_self_test():
    """`gate --self-test`: the gate's verdict on made-up measurements, where the right verdict
    is known. It runs no compiler and takes no time, so `fai verify` runs it every time, and
    `fai mutate` weakens the gate and requires this to notice. Returns the exit status."""
    good = {
        "behavior": {
            "lua workloads match": True,
            "lua suite files passed": len(LUA_SUITE),
            "speedtest1 verifies": True,
        },
        # Every workload the gate expects; lua-fib and speedtest1 are the ones the cases use.
        "instructions": {
            **{w: 50_000_000 for w in gate_expected()["instructions"]},
            "lua-fib": 14_000_000,
            "speedtest1": 2_800_000_000,
        },
        "total_instructions": {
            **{w: 51_000_000 for w in gate_expected()["total_instructions"]},
            "lua-fib": 14_250_000,
            "speedtest1": 2_900_000_000,
        },
        "functions": {
            "lua-fib": {"luaV_execute.l8bbbcbfa": 9_000_000, "luaD_precall": 2_000_000},
            "speedtest1": {"sqlite3VdbeExec": 900_000_000},
        },
        "text": {"lua": 377_000, "sqlite": 1_216_000},
        "compile_cpu_seconds": {"lua": 2.0, "sqlite": 3.0},
        "compile_rss_kib": {"lua": 100 << 10, "sqlite": 900 << 10},
    }

    def changed(path, value, src=good):
        new = json.loads(json.dumps(src))
        at = new
        for k in path[:-1]:
            at = at[k]
        if value is None:
            del at[path[-1]]
        else:
            at[path[-1]] = value
        return new

    def verdict(now, base=good, config="fcc-O", plain=()):
        baseline = {"configs": {"fcc-O": base}} if base else None
        return gate_verdict({config: now}, baseline, [config], set(plain))

    fib = ("instructions", "lua-fib")
    cases = [
        ("the baseline's own measurements pass", verdict(good), "PASS", None),
        (
            "a count one and a half parts in 100,000 higher fails",
            verdict(changed(fib, 14_000_210)),
            "FAIL",
            "lua-fib executes 14,000,210",
        ),
        (
            "more instructions in all fails, with the project's own code the same",
            verdict(changed(("total_instructions", "lua-fib"), 14_500_000)),
            "FAIL",
            "instructions in all: lua-fib executes 14,500,000 with libc",
        ),
        (
            "a count of zero is a broken measurement, not an improvement",
            verdict(changed(fib, 0)),
            "FAIL",
            "instructions: lua-fib measured 0: the measurement is broken",
        ),
        (
            "a workload the baseline doesn't have fails",
            verdict(changed(("instructions", "lua-new"), 5_000_000)),
            "FAIL",
            "instructions: lua-new has no baseline",
        ),
        (
            "a project that was not measured fails",
            verdict(changed(("text", "sqlite"), None)),
            "FAIL",
            "text: sqlite was not measured",
        ),
        (
            "a workload neither side has fails",
            verdict(
                changed(
                    ("total_instructions", "speedtest1"),
                    None,
                    changed(("instructions", "speedtest1"), None),
                ),
                base=changed(
                    ("total_instructions", "speedtest1"),
                    None,
                    changed(("instructions", "speedtest1"), None),
                ),
            ),
            "FAIL",
            "instructions: speedtest1 was not run",
        ),
        (
            "a first baseline of a partial run fails",
            verdict(changed(("text", "sqlite"), None), base=None),
            "FAIL",
            "text: sqlite was not measured",
        ),
        (
            "a baseline number that isn't finite fails",
            verdict(changed(fib, 40_000_000), base=changed(fib, float("inf"))),
            "FAIL",
            "the baseline's lua-fib is inf",
        ),
        (
            "more instructions in all names the function that rose",
            verdict(
                changed(
                    ("functions", "lua-fib"),
                    {"luaV_execute.l8bbbcbfa": 9_400_000, "luaD_precall": 2_000_000},
                    changed(("total_instructions", "lua-fib"), 14_700_000),
                )
            ),
            "FAIL",
            "in luaV_execute: 9,400,000",
        ),
        (
            "a baseline without one of the measurements fails",
            verdict(good, base=changed(("text",), None)),
            "FAIL",
            "text: the baseline has none",
        ),
        (
            "a baseline with neither the configuration nor fcc -O fails",
            gate_verdict({"fcc-m2r": good}, {"configs": {"fcc-promo": good}}, ["fcc-m2r"], set()),
            "FAIL",
            "the baseline has neither fcc-m2r nor fcc-O",
        ),
        (
            "compile time at exactly twice the baseline's and a second passes",
            verdict(changed(("compile_cpu_seconds", "sqlite"), 7.0)),
            "PASS",
            None,
        ),
        (
            "compile time a hundredth over that fails",
            verdict(changed(("compile_cpu_seconds", "sqlite"), 7.01)),
            "FAIL",
            "compile time: sqlite",
        ),
        (
            "compile memory at exactly twice the baseline's and 64 MiB passes",
            verdict(changed(("compile_rss_kib", "sqlite"), 1864 << 10)),
            "PASS",
            None,
        ),
        (
            "compile memory one KiB over that fails",
            verdict(changed(("compile_rss_kib", "sqlite"), (1864 << 10) + 1)),
            "FAIL",
            "compile memory: sqlite",
        ),
        (
            "a count within one part in 100,000 is the same",
            verdict(changed(fib, 14_000_100)),
            "PASS",
            None,
        ),
        (
            "1% more instructions on one workload fails, and names it",
            verdict(changed(fib, 14_140_000)),
            "FAIL",
            "lua-fib executes 14,140,000, more than 14,000,000",
        ),
        (
            "one part in 10,000 more instructions fails",
            verdict(changed(fib, 14_001_400)),
            "FAIL",
            "lua-fib",
        ),
        ("fewer instructions pass", verdict(changed(fib, 13_000_000)), "PASS", None),
        (
            "a workload that was not run fails",
            verdict(changed(fib, None)),
            "FAIL",
            "lua-fib was not run",
        ),
        (
            "a Lua workload whose output differs fails",
            verdict(changed(("behavior", "lua workloads match"), False)),
            "FAIL",
            "behavior: lua workloads match",
        ),
        (
            "one file of Lua's suite failing fails",
            verdict(changed(("behavior", "lua suite files passed"), len(LUA_SUITE) - 1)),
            "FAIL",
            "behavior: lua suite files passed",
        ),
        (
            "speedtest1 not verifying fails",
            verdict(changed(("behavior", "speedtest1 verifies"), False)),
            "FAIL",
            "behavior: speedtest1 verifies",
        ),
        (
            "one more byte of code fails",
            verdict(changed(("text", "lua"), 377_001)),
            "FAIL",
            "code size: lua",
        ),
        (
            "compile time within twice the baseline's passes",
            verdict(changed(("compile_cpu_seconds", "sqlite"), 5.9)),
            "PASS",
            None,
        ),
        (
            "compile time over twice the baseline's fails",
            verdict(changed(("compile_cpu_seconds", "sqlite"), 7.5)),
            "FAIL",
            "compile time: sqlite",
        ),
        (
            "compile memory over twice the baseline's fails",
            verdict(changed(("compile_rss_kib", "sqlite"), 2000 << 10)),
            "FAIL",
            "compile memory: sqlite",
        ),
        (
            "a partial build that is otherwise fine is PARTIAL, not a pass",
            verdict(good, plain=["lvm"]),
            "PARTIAL",
            None,
        ),
        (
            "a partial build that is worse fails",
            verdict(changed(fib, 15_000_000), plain=["lvm"]),
            "FAIL",
            "lua-fib",
        ),
        (
            "a configuration without a baseline is held to fcc -O's",
            verdict(changed(fib, 15_000_000), config="fcc-promo"),
            "FAIL",
            "lua-fib",
        ),
        ("with no baseline at all, right behavior passes", verdict(good, base=None), "PASS", None),
        (
            "with no baseline at all, wrong behavior fails",
            verdict(changed(("behavior", "speedtest1 verifies"), False), base=None),
            "FAIL",
            "behavior: speedtest1 verifies",
        ),
    ]
    failed = []
    for what, report, want, reason in cases:
        reasons = [line for r in report["configs"].values() for line in r["worse"]]
        if report["verdict"] != want:
            failed.append(f"{what}: the verdict is {report['verdict']}, not {want}")
        elif reason and not any(reason in line for line in reasons):
            failed.append(f"{what}: no reason mentions '{reason}' (reasons: {reasons})")
        elif want != "FAIL" and reasons:
            failed.append(f"{what}: {want}, with reasons to fail: {reasons}")
    extra = [0]

    def check(ok, what):
        extra[0] += 1
        if not ok:
            failed.append(what)

    # A failure says where: the function that executes more, by its name without the hash.
    slower = changed(
        ("functions", "lua-fib"),
        {"luaV_execute.l00000000": 9_140_000, "luaD_precall": 2_000_000},
        changed(fib, 14_140_000),
    )
    reasons = verdict(slower)["configs"]["fcc-O"]["worse"]
    check(
        any("in luaV_execute: 9,140,000, +140,000 (+1.56%)" in r for r in reasons),
        f"a failure names the function that got slower (reasons: {reasons})",
    )
    check(
        not any("luaD_precall" in r for r in reasons),
        "a failure names only functions that execute more",
    )
    # Two local functions of one name are counted together, and one that is new among the ten
    # busiest comes after those known to have risen.
    twins = {"functions": {"w": {"f.l11111111": 5, "f.l22222222": 7, "g": 100, "h": 1}}}
    before = {"functions": {"w": {"f.l33333333": 4, "f.l44444444": 6, "h": 1}}}
    check(
        gate_slower_functions(twins, before, "w") == [("f", 12, 10), ("g", 100, None)],
        f"functions of one name count together: {gate_slower_functions(twins, before, 'w')}",
    )
    # A run without the breakdown still fails for its count.
    bare = changed(("functions",), None, changed(fib, 14_140_000))
    check(
        verdict(bare)["verdict"] == "FAIL",
        "a failure doesn't need the functions' breakdown",
    )
    # The baseline moves one way.
    old = {"fcc-O": good}
    worse_now = changed(
        ("functions", "lua-fib"),
        {"luaV_execute.l8bbbcbfa": 9_000_050, "luaD_precall": 2_000_000},
        changed(("compile_cpu_seconds", "lua"), 3.5, changed(fib, 14_000_050)),
    )
    kept = gate_updated(old, {"fcc-O": worse_now}, ["fcc-O"])["fcc-O"]
    check(
        kept["instructions"]["lua-fib"] == 14_000_000,
        "the baseline only moves down: --update raised an instruction count",
    )
    check(
        kept["compile_cpu_seconds"]["lua"] == 2.0,
        "the baseline only moves down: --update raised a compile time",
    )
    check(
        kept["functions"]["lua-fib"] == good["functions"]["lua-fib"],
        "a count that is kept keeps the functions it was counted with",
    )
    better_now = changed(("compile_cpu_seconds", "lua"), 1.5, changed(fib, 13_000_000))
    moved = gate_updated(old, {"fcc-O": better_now}, ["fcc-O"])["fcc-O"]
    check(
        moved["instructions"]["lua-fib"] == 13_000_000
        and moved["compile_cpu_seconds"]["lua"] == 1.5,
        "the baseline moves down: --update didn't take a better number",
    )
    # A baseline that isn't what --update writes is refused before the run.
    for bad in ({"configs": None}, {"configs": {"fcc-O": {"text": None}}}, {}):
        try:
            gate_check_baseline(bad)
            ok = False
        except TypeError, KeyError:
            ok = True
        check(ok, f"a malformed baseline is refused: {bad}")
    # A count kept from the baseline it was held to keeps that baseline's functions.
    inherited = gate_updated(old, {"fcc-promo": changed(fib, 14_000_090)}, ["fcc-promo"])[
        "fcc-promo"
    ]
    check(
        inherited["instructions"]["lua-fib"] == 14_000_000
        and inherited["functions"]["lua-fib"] == good["functions"]["lua-fib"],
        "an inherited count keeps the functions it was counted with",
    )
    # A configuration's first baseline is no looser than fcc -O's, which it passed against
    # with slack.
    slow = changed(("compile_cpu_seconds", "lua"), 3.2)
    first = gate_updated(old, {"fcc-promo": slow}, ["fcc-promo"])["fcc-promo"]
    check(
        first["compile_cpu_seconds"]["lua"] == 2.0,
        "a new configuration's baseline is no looser than the one it was held to",
    )
    checks = len(cases) + extra[0]
    if failed:
        print(f"gate self-test: FAILED ({len(failed)} of {checks} checks)")
        for f in failed:
            print(f"  {f}")
        return 1
    print(f"gate self-test: passed ({checks} checks)")
    return 0


def cmd_gate(s):
    """One verdict for a change to the compiler, on Lua and SQLite: build both with fcc (`-O`, or
    the fcc configurations of --configs), check that they behave as GCC -O2's builds do, count
    the instructions every workload executes, and compare with the accepted baseline
    (benchmarks/projects/gate.json). FAIL, and exit 1, if a file doesn't compile (in --timeout
    seconds), behavior differs, or anything is worse than the baseline: a workload's
    instructions, a project's code size, or (beyond twice) its compile time or memory. A
    configuration with no baseline of its own is held to `fcc -O`'s: a pipeline proposed for
    `-O` must not be worse than `-O`. With --plain the best verdict is PARTIAL, which is not a
    pass. NOT RUN, and exit 2, when the gate can't judge the tree at all (no baseline, or an
    AArch64 host, where the instruction-counting plugin doesn't run). The verdict and its
    reasons are also in gate-report.json, in --out.

    --update writes the baseline, and only when the verdict is PASS: the baseline moves one way.
    To accept a trade, edit gate.json by hand, where the diff shows it."""
    global BUILD_CONFIGS

    # From `fai gate`: which tests, baselines, and checkers the change touches (tools/fai's
    # judging.rs). It is said above every verdict, and decides none here.
    judging = os.environ.get("FAI_JUDGING")

    def not_run(why):
        if judging:
            print(judging)
        print(f"gate: NOT RUN: {why}")
        sys.exit(GATE_NOT_RUN)

    gated = [c for c in BUILD_CONFIGS if c.startswith("fcc")] if s.args.configs else ["fcc-O"]
    if not gated:
        not_run("--configs names no fcc configuration")
    if s_native():
        not_run("counting instructions needs qemu-aarch64's plugin: run it off AArch64")
    # The linker map and QEMU's plugin options carry these paths, and neither can carry a
    # space or a comma: the program's code would not be found, and nothing would be counted.
    for where in (ROOT, s.out):
        if any(ch.isspace() or ch == "," for ch in str(where)):
            not_run(f"{where}: a path with a space or a comma can't be measured")
    # One gate at a time in a checkout: two would share the measurement files under --out,
    # the sources, and the baseline an update writes. Held until the process ends.
    lock_dir = ROOT / "target/fai"
    lock_dir.mkdir(parents=True, exist_ok=True)
    lock = open(lock_dir / "gate.lock", "w")  # noqa: SIM115 (held for the whole run)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        not_run("another gate is running in this checkout")
    baseline_text = GATE.read_bytes() if GATE.exists() else None
    if baseline_text is None and not s.args.update:
        not_run(f"no baseline at {GATE}; make one with `gate --update`")
    if s.plain and s.args.update:
        not_run("--update with --plain: a baseline is of whole builds")
    BUILD_CONFIGS = [*gated, REFERENCE]
    s.args.reps = 1
    if s.args.timeout is None:
        s.args.timeout = 300
    report: dict[str, Any] = {"verdict": "PASS", "configs": {}}
    if judging:
        try:
            report["judging"] = json.loads(os.environ.get("FAI_JUDGING_JSON", "null"))
        except ValueError:
            report["judging"] = None
    # What this verdict is of: the tree (`fai gate` gives its hash, and `fai status` compares it
    # with the tree later), the run that wrote it, the baseline, and how the gate was run.
    report["tree"] = os.environ.get("FAI_TREE")
    report["run"] = os.environ.get("FAI_RUN")
    report["baseline_sha256"] = (
        hashlib.sha256(baseline_text).hexdigest() if baseline_text is not None else None
    )
    report["update"] = bool(s.args.update)
    # The harness stops (`die`) when a file doesn't compile, takes too long, or a counted run
    # goes wrong, and a run can also end in an error of its own (a workload over its time, a
    # trace that was never written): each is the tree failing, and still gets a verdict and a
    # report.
    # The baseline, read once, is checked first: one that isn't what the gate wrote fails here,
    # with a report, and not with a crash later.
    stopped = None
    baseline = None
    if baseline_text is not None:
        try:
            baseline = json.loads(baseline_text)
            gate_check_baseline(baseline)
        except (ValueError, TypeError, KeyError) as e:
            stopped = f"{GATE} is not a baseline the gate can read ({e}): make it again"
    now = None
    if stopped is None:
        try:
            cmd_prepare(s)
            before = load(s.out, "prepare").get("unpacked")
            cmd_build(s)
            cmd_check(s)
            cmd_count(s)
            # The sources are ignored by git: they must be as they were before the run, and
            # those the baseline was measured on.
            gate_check_sources(s, before, baseline)
            now = gate_measure(s, gated)
            verdict = gate_verdict(now, baseline, gated, s.plain)
        except SystemExit:
            stopped = STOPPED[-1] if STOPPED else "the harness stopped (see above)"
        except Exception as e:
            stopped = f"{type(e).__name__}: {e}"
    if stopped is not None:
        report["verdict"] = "FAIL"
        report["stopped"] = stopped
        save(s.out, "gate-report", report)
        print(f"gate: stopped: {stopped}")
        if judging:
            print(judging)
        print("gate: FAIL")
        sys.exit(GATE_FAIL)
    report["sources"] = load(s.out, "prepare").get("unpacked")
    report.update(verdict)
    save(s.out, "gate-report", report)
    for c, r in report["configs"].items():
        if r["against"] is None:
            print(f"gate: {c}:")
        else:
            print(f"gate: {c}, against the baseline of {r['against']}:")
        for line in r["worse"]:
            print(f"  WORSE   {line}")
        for line in r["better"]:
            print(f"  better  {line}")
        if not r["worse"] and not r["better"]:
            print("  the same as the baseline")
    if judging:
        print(judging)
    if report["verdict"] == "PARTIAL":
        files = ", ".join(report["plain"])
        print(f"gate: PARTIAL, not a pass: {files} compiled with fcc -O (--plain)")
        sys.exit(GATE_FAIL)
    print(f"gate: {report['verdict']}")
    if report["verdict"] != "PASS":
        sys.exit(GATE_FAIL)
    if s.args.update:
        # The verdict was against the baseline as it was when the gate started.
        if (sha256(GATE) if GATE.exists() else None) != report["baseline_sha256"]:
            report["verdict"] = "FAIL"
            report["stopped"] = f"{GATE} changed while the gate ran"
            save(s.out, "gate-report", report)
            print(f"gate: {GATE} changed while the gate ran: it was not written")
            print("gate: FAIL")
            sys.exit(GATE_FAIL)
        configs = gate_updated(baseline["configs"] if baseline else {}, now, gated)
        text = json.dumps(
            {
                "about": "The accepted results of `fai gate` (benchmarks/projects/README.md): "
                "what a change may not make worse. Written by `fai gate --update`, which "
                "refuses unless the gate passes, and then only moves a number down.",
                "configs": configs,
                # The Lua sources the baseline was measured on (`source_digest`): a later run
                # on other sources measures something else.
                "sources": gate_lua_sources(load(s.out, "prepare").get("unpacked") or {}),
            },
            indent=1,
            sort_keys=True,
        )
        GATE.write_text(text + "\n")
        print(f"gate: wrote {GATE}")


# ---------------------------------------------------------------------------------------------
# c23: which compiler accepts and correctly runs each C23 program


def cmd_c23(s):
    tests = ROOT / "frontends/c/tests"
    inc = ["-I", str(tests / "runtime")]
    work = s.out / "c23"
    work.mkdir(parents=True, exist_ok=True)
    # The output helpers, by GCC, linked into every build (as the corpus test links them).
    rt = work / "fai_runtime.o"
    run(
        s.compile_cmd("gcc-O1", tests / "runtime/fai_runtime.c", ["-std=gnu17", *inc], rt),
        env=s.env,
    )
    progs = sorted(tests.glob("c23_*.c")) + sorted((tests / "errors").glob("c23_*.c"))
    result: dict[str, Any] = {}
    for prog in progs:
        name = ("errors/" if prog.parent.name == "errors" else "") + prog.stem
        row: dict[str, Any] = {}
        outs = {}
        for c, cfg in (("gcc", "gcc-O1"), ("clang", "clang-O0"), ("fcc", "fcc")):
            o = work / f"{prog.stem}.{c}.o"
            m = measure(s.compile_cmd(cfg, prog, ["-std=c23", *inc], o), s.env)
            if m["exit"] != 0:
                row[c] = {"compiles": False, "error": first_error(m["stderr"])}
                continue
            if prog.parent.name == "errors":  # fcc's error tests: no main, only accepted or not
                row[c] = {"compiles": True}
                continue
            exe = work / f"{prog.stem}.{c}"
            run([s.tools.cc, "-static", o, rt, "-o", exe, f"-L{s.tools.libc}", "-lm"], env=s.env)
            code, out = qemu(exe, [])
            outs[c] = (code, out)
            row[c] = {"compiles": True, "exit": code}
        for c in ("clang", "fcc"):
            if c in outs and "gcc" in outs:
                row[c]["same_as_gcc"] = outs[c] == outs["gcc"]
        if s.arocc:
            m = measure(s.syntax_cmd("arocc", prog, ["-std=c23", *inc]), s.env)
            row["arocc"] = {"accepts": m["exit"] == 0, "error": first_error(m["stderr"])}
        result[name] = row
    save(s.out, "c23", result)


def first_error(stderr):
    for line in stderr.splitlines():
        if "error" in line:
            return re.sub(r"^\S*/", "", line.strip())[:200]
    return stderr.strip().splitlines()[0][:200] if stderr.strip() else ""


# ---------------------------------------------------------------------------------------------
# time: natively


RUN_SH = r"""#!/bin/sh
# Generated by projbench.py: times the Lua and speedtest1 builds with benchrun, which refuses to
# run unless the CPU is AArch64 hardware. Usage: ./run.sh ROUNDS
set -eu
cd "$(dirname "$0")"
ROUNDS=${1:-5}
mkdir -p expected results
{
  echo "uname: $(uname -a)"
  echo "nproc: $(nproc 2>/dev/null || echo ?)"
  grep -m1 -i "MemTotal" /proc/meminfo || true
  grep -E "^(CPU implementer|CPU part|CPU variant|CPU revision)" /proc/cpuinfo | sort | uniq -c
} > results/env.txt
: > results/times.jsonl
for p in $SCRIPTS; do
  eval "arg=\$ARG_$p"
  ./bin/lua.REFERENCE lua/$p.lua "$arg" > expected/$p.out
done
# speedtest1 prints its own timings, so its output is not compared here: `check` compares its
# --verify hash under qemu, and every build's hash is checked here first.
for c in $CONFIGS; do
  ./bin/speedtest1.$c --size $SPEEDTEST_SIZE --memdb --verify --testset $SPEEDTEST_SET | grep "Verification Hash" > results/hash.$c
done
: > expected/none
round=0
while [ $round -le "$ROUNDS" ]; do
  for p in $SCRIPTS; do
    eval "arg=\$ARG_$p"
    for c in $CONFIGS; do
      json=$(./benchrun 1 0 expected/$p.out ./bin/lua.$c lua/$p.lua "$arg")
      echo "{\"round\": $round, \"program\": \"lua-$p\", \"config\": \"$c\", \"result\": $json}" >> results/times.jsonl
    done
  done
  for c in $CONFIGS; do
    json=$(./benchrun 1 0 - ./bin/speedtest1.$c --size $SPEEDTEST_SIZE --memdb --testset $SPEEDTEST_SET)
    echo "{\"round\": $round, \"program\": \"speedtest1\", \"config\": \"$c\", \"result\": $json}" >> results/times.jsonl
  done
  echo "round $round done" >&2
  round=$((round + 1))
done
"""


def cmd_time(s):
    args = s.args
    if not load(s.out, "build"):
        die("run `projbench.py build` first")
    if not args.ssh and not s_native():
        die("refusing to time under emulation: run on AArch64 Linux, or pass --ssh HOST")
    bundle = Path(tempfile.mkdtemp(prefix="projbench-bundle-", dir=s.out))
    (bundle / "bin").mkdir()
    for c in BUILD_CONFIGS:
        for exe in ("lua", "speedtest1"):
            shutil.copy2(s.out / "bin" / f"{exe}.{c}", bundle / "bin")
    shutil.copytree(BENCH / "lua", bundle / "lua")
    run(
        [
            s.tools.cc,
            "-static",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            ROOT / "benchmarks/c/benchrun.c",
            "-o",
            bundle / "benchrun",
            f"-L{s.tools.libc}",
        ],
        env=s.env,
    )
    header = (
        f"SCRIPTS='{' '.join(LUA_SCRIPTS)}'\nCONFIGS='{' '.join(BUILD_CONFIGS)}'\n"
        f"SPEEDTEST_SIZE={SPEEDTEST_SIZE[1]}\nSPEEDTEST_SET='{SPEEDTEST_SET}'\n"
        + "".join(f"ARG_{n}={v[1]}\n" for n, v in LUA_SCRIPTS.items())
    )
    script = RUN_SH.replace("set -eu\n", "set -eu\n" + header, 1).replace("REFERENCE", REFERENCE)
    (bundle / "run.sh").write_text(script)
    (bundle / "run.sh").chmod(0o755)
    info: dict[str, Any] = {"rounds": args.rounds}
    if not args.ssh:
        run([bundle / "run.sh", args.rounds], capture=False)
        info["where"] = "local"
    else:
        remote = run(["ssh", args.ssh, "mktemp -d /tmp/projbench.XXXXXX"]).stdout.strip()
        try:
            run(["scp", "-q", "-r", f"{bundle}/.", f"{args.ssh}:{remote}/"])
            if args.docker:
                d = args.docker_bin
                q = shlex.quote(args.docker)
                info["image"] = run(
                    [
                        "ssh",
                        args.ssh,
                        f"{d} pull -q {q} >/dev/null && "
                        f"{d} image inspect --format '{{{{index .RepoDigests 0}}}}' {q}",
                    ]
                ).stdout.strip()
                inner = (
                    f"{d} run --rm --platform linux/arm64 -v {remote}:/b {q} "
                    f"/b/run.sh {args.rounds}"
                )
                info["where"] = f"ssh {args.ssh}, docker"
            else:
                inner = f"{remote}/run.sh {args.rounds}"
                info["where"] = f"ssh {args.ssh}"
            info["remote_host"] = run(
                [
                    "ssh",
                    args.ssh,
                    "uname -a; (sysctl -n machdep.cpu.brand_string hw.ncpu hw.memsize 2>/dev/null "
                    "|| true)",
                ]
            ).stdout.strip()
            run(["ssh", args.ssh, inner], capture=False)
            run(["scp", "-q", "-r", f"{args.ssh}:{remote}/results/.", f"{bundle}/results/"])
        finally:
            run(["ssh", args.ssh, f"rm -rf {shlex.quote(remote)}"], check=False)
    res = bundle / "results"
    info["env"] = (res / "env.txt").read_text()
    info["speedtest_hash"] = {c: (res / f"hash.{c}").read_text().strip() for c in BUILD_CONFIGS}
    times: dict[str, dict] = {}
    for ln in (res / "times.jsonl").read_text().splitlines():
        r = json.loads(ln)
        if r["round"] == 0:
            continue
        t = times.setdefault(r["program"], {}).setdefault(
            r["config"], {"wall": [], "user": [], "maxrss_kib": 0}
        )
        t["wall"] += r["result"]["wall"]
        t["user"] += r["result"]["user"]
        t["maxrss_kib"] = max(t["maxrss_kib"], r["result"]["maxrss_kib"])
        info["cpu_implementer"] = r["result"]["cpu_implementer"]
        info["cpu_part"] = r["result"]["cpu_part"]
    for prog in times.values():
        for t in prog.values():
            if len(t["wall"]) != args.rounds:
                die(f"incomplete timing in {bundle}")
            t["median"] = statistics.median(t["wall"])
            t["min"], t["max"] = min(t["wall"]), max(t["wall"])
    info["programs"] = times
    info["sizes"] = {n: v[1] for n, v in LUA_SCRIPTS.items()} | {"speedtest1": SPEEDTEST_SIZE[1]}
    save(s.out, "time", info)
    shutil.rmtree(bundle)


# ---------------------------------------------------------------------------------------------
# report


def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    return statistics.geometric_mean(xs) if xs else float("nan")


def table(header, rows):
    out = [
        "| " + " | ".join(header) + " |",
        "|" + "|".join(["---"] + ["---:"] * (len(header) - 1)) + "|",
    ]
    out += ["| " + " | ".join(str(c) for c in r) + " |" for r in rows]
    return "\n".join(out)


def ms(x):
    return "-" if x is None else (f"{x * 1000:,.0f}" if x >= 0.1 else f"{x * 1000:.1f}")


def cmd_report(s):
    out = s.out
    lines = ["# projbench report", ""]
    build, fe, chk, c23, tm = (load(out, n) for n in ("build", "frontend", "check", "c23", "time"))
    cnt = load(out, "count")
    if build:
        ident = build["identity"]
        lines += [
            f"fai `{ident['revision'][:10]}`{' (dirty)' if ident['dirty'] else ''}; "
            f"{ident['gcc']}; {ident['clang']}; host {ident['host_cpu']}, "
            f"load {ident['loadavg']} to {build['loadavg_end']}",
            "",
        ]
        for proj, tus, label in (
            ("lua", LUA_TUS, "Lua 5.4.7, 33 files"),
            ("sqlite", ["sqlite3", "speedtest1"], "SQLite: sqlite3.c + speedtest1.c"),
        ):
            rows = []
            for c in BUILD_CONFIGS:
                ts = [build["tus"][f"{proj}/{tu}/{c}"] for tu in tus]
                rows.append(
                    [
                        c,
                        ms(sum(t["wall_min"] for t in ts)),
                        ms(sum(t["cpu_min"] for t in ts)),
                        f"{max(t['rss_kib_max'] for t in ts) / 1024:,.0f}",
                        f"{sum(t['text'] for t in ts):,}",
                    ]
                )
            lines += [
                f"## Build: {label} (serial, minimum of {build['reps']})",
                "",
                table(["config", "wall ms", "CPU ms", "peak RSS MiB", ".text bytes"], rows),
                "",
            ]
            if proj == "sqlite":
                rows = [
                    [c] + [ms(build["tus"][f"sqlite/{tu}/{c}"]["wall_min"]) for tu in tus]
                    for c in BUILD_CONFIGS
                ]
                lines += [table(["config", *tus], rows), ""]
        rows = []
        for key, ph in sorted(build["phases"].items()):
            top = sorted(ph.items(), key=lambda kv: -kv[1])[:8]
            rows.append([key, ", ".join(f"{k} {v:,.0f}" for k, v in top)])
        lines += [
            "## fcc phases (self ms, summed over files; * = summed over threads)",
            "",
            table(["build", "largest phases"], rows),
            "",
        ]
        rows = [
            [k, f"{v['bytes']:,}", f"{v['text']:,}"] for k, v in sorted(build["binaries"].items())
        ]
        lines += ["## Binaries (static)", "", table(["binary", "bytes", ".text"], rows), ""]
    if fe:
        fes = [f for f in FRONTENDS if any(k.endswith("/" + f) for k in fe["runs"])]
        groups: dict[str, list] = {}
        for key in fe["lines"]:
            groups.setdefault(key.split("/")[0], []).append(key)
        rows = []
        for g, keys in groups.items():
            row = [g, len(keys)]
            for f in fes:
                vals = [fe["runs"].get(f"{k}/{f}") for k in keys]
                ok = [v for v in vals if v]
                row.append(
                    ms(sum(v["wall_min"] for v in ok))
                    + ("" if len(ok) == len(keys) else f" ({len(ok)} of {len(keys)})")
                )
            row.append(ms(sum((fe["fcc"][k]["clang_ms"]) / 1000 for k in keys)))
            row.append(ms(sum((fe["fcc"][k]["lower_ms"]) / 1000 for k in keys)))
            rows.append(row)
        lines += [
            "## Frontends: parse and check only (wall ms, minimum, summed over files)",
            "",
            table(
                [
                    "inputs",
                    "files",
                    *[f"{f} -fsyntax-only" for f in fes],
                    "fcc: Clang phase",
                    "fcc: AST to HFIR",
                ],
                rows,
            ),
            "",
        ]
        rows = []
        for key in fe["lines"]:
            r = [key, f"{fe['lines'][key]:,}"]
            for f in fes:
                v = fe["runs"].get(f"{key}/{f}")
                r.append(f"{ms(v['wall_min'])} / {v['rss_kib_max'] / 1024:,.0f}" if v else "error")
            rows.append(r)
        lines += ["Per file: wall ms / peak RSS MiB", "", table(["file", "lines", *fes], rows), ""]
        if fe["errors"]:
            lines += (
                ["Errors:", ""]
                + [f"- `{k}`: {first_error(v)}" for k, v in sorted(fe["errors"].items())]
                + [""]
            )
    if chk:
        rows = [
            [
                c,
                f"{len(chk['lua_suite'][c])} of {len(LUA_SUITE)}",
                sum(1 for n in LUA_SCRIPTS if chk["lua_scripts"][f"{n}/{c}"]),
                chk["speedtest"][c]["exit"] == 0
                and chk["speedtest"][c]["hash"] is not None
                and chk["speedtest"][c]["hash"] == chk["speedtest"][REFERENCE]["hash"],
            ]
            for c in BUILD_CONFIGS
        ]
        lines += [
            "## Behavior (qemu)",
            "",
            table(
                ["config", "Lua suite", "Lua scripts = GCC -O2", "speedtest1 hash = GCC -O2"], rows
            ),
            "",
        ]
    if c23:
        rows = []
        for name, row in c23.items():

            def cell(c, row=row):
                r = row.get(c)
                if not r:
                    return "-"
                if not r["compiles"]:
                    return "rejected"
                if "exit" not in r:
                    return "accepts"
                if c == "gcc":
                    return "runs" if r["exit"] == 0 else f"exit {r['exit']}"
                return "same" if r.get("same_as_gcc") else "differs"

            ar = row.get("arocc")
            rows.append(
                [
                    name,
                    cell("gcc"),
                    cell("clang"),
                    cell("fcc"),
                    "-" if not ar else ("accepts" if ar["accepts"] else f"rejects: {ar['error']}"),
                ]
            )
        lines += [
            "## C23 programs",
            "",
            table(["program", "GCC", "Clang", "fcc", "arocc"], rows),
            "",
        ]
    if tm:
        progs = list(tm["programs"])
        rows = []
        for p in progs:
            ref = tm["programs"][p][REFERENCE]["median"]
            rows.append(
                [p]
                + [
                    f"{tm['programs'][p][c]['median']:.3f} ({tm['programs'][p][c]['median'] / ref:.2f}×)"
                    for c in BUILD_CONFIGS
                ]
            )
        rows.append(
            ["**geomean vs gcc-O2**"]
            + [
                f"**{geomean([tm['programs'][p][c]['median'] / tm['programs'][p][REFERENCE]['median'] for p in progs]):.2f}×**"
                for c in BUILD_CONFIGS
            ]
        )
        lines += [
            f"## Native run time, seconds (median of {tm['rounds']}; {tm['where']})",
            "",
            table(["program", *BUILD_CONFIGS], rows),
            "",
        ]
    if cnt:
        progs = list(cnt["programs"])
        rows = []
        for p in progs:
            ref = cnt["programs"][p][REFERENCE]["program"]
            rows.append(
                [p]
                + [
                    f"{cnt['programs'][p][c]['program'] / 1e6:,.1f} "
                    f"({cnt['programs'][p][c]['program'] / ref:.2f}×)"
                    for c in BUILD_CONFIGS
                ]
            )
        rows.append(
            ["**geomean vs gcc-O2**"]
            + [
                f"**{geomean([cnt['programs'][p][c]['program'] / cnt['programs'][p][REFERENCE]['program'] for p in progs]):.2f}×**"
                for c in BUILD_CONFIGS
            ]
        )
        lines += [
            "## Executed instructions in the project's own code (qemu, exact, millions)",
            "",
            table(["workload", *BUILD_CONFIGS], rows),
            "",
        ]
        rows = [
            [p] + [f"{cnt['programs'][p][c]['library'] / 1e6:,.1f}" for c in BUILD_CONFIGS]
            for p in progs
        ]
        lines += ["Executed in libc (millions):", "", table(["workload", *BUILD_CONFIGS], rows), ""]
        classes = ["load", "store", "move", "alu", "compare", "branch", "call", "muldiv", "fp"]
        rows = []
        for c in BUILD_CONFIGS:
            tot = sum(cnt["programs"][p][c]["program"] for p in progs)
            mix = {k: sum(cnt["programs"][p][c]["mix"].get(k, 0) for p in progs) for k in classes}
            mem = {
                k: sum(cnt["programs"][p][c]["memory_accesses"][k] for p in progs)
                for k in ("stack_loads", "stack_stores", "other_loads", "other_stores")
            }
            acc = sum(mem.values())
            rows.append(
                [c, f"{tot / 1e6:,.0f}M"]
                + [f"{100 * mix[k] / tot:.1f}%" for k in classes]
                + [
                    f"{acc / 1e6:,.0f}M",
                    f"{100 * (mem['stack_loads'] + mem['stack_stores']) / acc:.0f}%",
                ]
            )
        lines += [
            "Instruction mix in the own code, all workloads:",
            "",
            table(["config", "executed", *classes, "memory accesses", "to the stack"], rows),
            "",
        ]
    if tm:
        rows = []
        for p in tm["programs"]:
            rows.append(
                [p] + [f"{tm['programs'][p][c]['maxrss_kib'] / 1024:,.1f}" for c in BUILD_CONFIGS]
            )
        lines += ["Peak RSS while running, MiB:", "", table(["program", *BUILD_CONFIGS], rows), ""]
        rows = []
        for p in tm["programs"]:
            rows.append(
                [p]
                + [
                    f"{100 * (max(tm['programs'][p][c]['wall']) - min(tm['programs'][p][c]['wall'])) / tm['programs'][p][c]['median']:.1f}%"
                    for c in BUILD_CONFIGS
                ]
            )
        lines += [
            "Spread of the runs, (max − min) / median:",
            "",
            table(["program", *BUILD_CONFIGS], rows),
            "",
        ]
    (out / "report.md").write_text("\n".join(lines))
    print(out / "report.md")


def main():
    global BUILD_CONFIGS
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "step",
        choices=[
            "prepare",
            "build",
            "frontend",
            "check",
            "count",
            "forms",
            "gate",
            "c23",
            "time",
            "report",
            "all",
        ],
    )
    ap.add_argument("--out", default=str(ROOT / "target/projbench"))
    ap.add_argument("--arocc", help="arocc's path (or AROCC)")
    ap.add_argument("--reps", type=int, default=3, help="compile-time repetitions (minimum)")
    ap.add_argument("--rounds", type=int, default=5, help="native timing rounds after a warmup")
    ap.add_argument("--ssh")
    ap.add_argument("--docker")
    ap.add_argument("--docker-bin", default="docker")
    ap.add_argument(
        "--configs",
        help="comma-separated configurations for build, check, and count, in place of the "
        f"default {','.join(BUILD_CONFIGS)}; must include {REFERENCE}, and may name "
        f"{', '.join(cbench.FCC_EXPERIMENTAL)} (fcc with an experimental pipeline). "
        "`report` and `time` are for the default set",
    )
    ap.add_argument(
        "--timeout",
        type=float,
        help="seconds a compiler may take on one file before `build` (and `gate`, where it "
        "defaults to 300) gives up on it",
    )
    ap.add_argument(
        "--update",
        action="store_true",
        help="gate: write the baseline (benchmarks/projects/gate.json), if the gate passes",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="gate: check the gate's verdict on made-up measurements (no compiler runs)",
    )
    ap.add_argument(
        "--plain",
        help="comma-separated source files (by stem: lvm) that the experimental fcc "
        "configurations compile with `fcc -O` instead, for files the backend can't compile "
        "under an experimental pipeline in practical time",
    )
    args = ap.parse_args()
    if args.self_test:
        if args.step != "gate":
            die("--self-test is the gate's")
        sys.exit(gate_self_test())
    if args.configs:
        BUILD_CONFIGS = args.configs.split(",")
        known = [*cbench.CONFIGS, *cbench.FCC_EXPERIMENTAL]
        if bad := [c for c in BUILD_CONFIGS if c not in known]:
            die(f"--configs: unknown {', '.join(bad)} (known: {', '.join(known)})")
        if REFERENCE not in BUILD_CONFIGS and args.step != "gate":
            die(f"--configs must include {REFERENCE}, which the others are checked against")
        if args.step in ("report", "time", "all"):
            die(
                f"--configs is for build, check, count, forms, and gate; `{args.step}` uses the default set"
            )
    s = Setup(args)
    s.out.mkdir(parents=True, exist_ok=True)
    steps = {
        "count": cmd_count,
        "forms": cmd_forms,
        "gate": cmd_gate,
        "prepare": cmd_prepare,
        "build": cmd_build,
        "frontend": cmd_frontend,
        "check": cmd_check,
        "c23": cmd_c23,
        "time": cmd_time,
        "report": cmd_report,
    }
    if args.step == "all":
        for name in ("prepare", "build", "frontend", "check", "count", "c23", "time", "report"):
            steps[name](s)
    else:
        steps[args.step](s)


if __name__ == "__main__":
    main()
