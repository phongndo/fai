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
import hashlib
import importlib
import json
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


def die(msg):
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


def cmd_prepare(s):
    s.src.mkdir(parents=True, exist_ok=True)
    for name, (url, digest) in SOURCES.items():
        f = s.src / name
        if not f.exists():
            run(["curl", "-sfL", url, "-o", f])
        if sha256(f) != digest:
            die(f"{f}: SHA-256 is not {digest}")
        unpacked = s.src / name.removesuffix(".tar.gz").removesuffix(".zip")
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
    info = {
        "sources": {n: {"url": u, "sha256": d} for n, (u, d) in SOURCES.items()},
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


def qemu(exe, args, cwd=None, timeout=900):
    cmd = ([] if s_native() else ["qemu-aarch64"]) + [str(exe), *map(str, args)]
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout)
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
    workloads: list[tuple[str, str, list[Any]]] = [
        ("lua", f"lua-{n}", [BENCH / "lua" / f"{n}.lua", a[0]]) for n, a in LUA_SCRIPTS.items()
    ]
    workloads.append(
        (
            "speedtest1",
            "speedtest1",
            ["--size", SPEEDTEST_SIZE[0], "--memdb", "--testset", SPEEDTEST_SET],
        )
    )
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
            for prog, name, args in workloads:
                if prog != exe_name:
                    continue
                trace = work / f"{name}.{c}.trace"
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
                    exe,
                    *args,
                ]
                p = run(cmd, check=False, timeout=3600)
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
    workloads: list[tuple[str, str, list[Any]]] = [
        ("lua", f"lua-{n}", [BENCH / "lua" / f"{n}.lua", a[0]]) for n, a in LUA_SCRIPTS.items()
    ]
    workloads.append(
        (
            "speedtest1",
            "speedtest1",
            ["--size", SPEEDTEST_SIZE[0], "--memdb", "--testset", SPEEDTEST_SET],
        )
    )
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
            for prog, name, args in workloads:
                if prog != exe_name:
                    continue
                trace = work / f"{name}.{c}.trace"
                plug = (
                    f"{so},outfile={trace},below={cbench.STACK_BELOW},"
                    f"above={cbench.STACK_ABOVE},deep={cbench.STACK_DEEP}"
                )
                qemu_cmd = ["env", "-i", shutil.which("qemu-aarch64"), "-s", cbench.QEMU_STACK]
                p = run([*qemu_cmd, "-plugin", plug, exe, *args], check=False, timeout=3600)
                if p.returncode != 0:
                    die(f"forms: {name} {c} exited with {p.returncode}")
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
        ref_hash = check["speedtest"][REFERENCE]["hash"]
        st = check["speedtest"][c]
        out[c] = {
            "behavior": {
                "lua workloads match": all(check["lua_scripts"][f"{n}/{c}"] for n in LUA_SCRIPTS),
                "lua suite files passed": len(check["lua_suite"][c]),
                "speedtest1 verifies": st["exit"] == 0
                and st["hash"] == ref_hash
                and bool(ref_hash),
            },
            "instructions": {w: count["programs"][w][c]["program"] for w in count["programs"]},
            "text": {
                p: sum(v["text"] for k, v in tus.items() if k.startswith(f"{p}/")) for p in projects
            },
            "compile_seconds": {
                p: round(sum(v["wall_min"] for k, v in tus.items() if k.startswith(f"{p}/")), 2)
                for p in projects
            },
            "compile_rss_kib": {
                p: max(v["rss_kib_max"] for k, v in tus.items() if k.startswith(f"{p}/"))
                for p in projects
            },
        }
    return out


def gate_compare(now, base):
    """What got worse and what got better, as sentences. Behavior, instruction counts (to within
    GATE_SAME), and code size may not get worse at all; compile time and memory may reach
    GATE_SLACK times the baseline's (plus a second, or 64 MiB)."""
    worse, better = [], []
    want = {
        "lua workloads match": True,
        "lua suite files passed": len(LUA_SUITE),
        "speedtest1 verifies": True,
    }
    for k, v in want.items():
        if now["behavior"][k] != v:
            worse.append(f"behavior: {k}: {now['behavior'][k]}, not {v}")
    for w, b in base["instructions"].items():
        n = now["instructions"].get(w)
        tol = GATE_SAME
        if n is None:
            worse.append(f"instructions: {w} was not run")
        elif n > b * (1 + tol):
            worse.append(f"instructions: {w} executes {n:,}, more than {b:,} ({n / b - 1:+.2%})")
        elif n < b * (1 - tol):
            better.append(f"instructions: {w} executes {n:,}, fewer than {b:,} ({n / b - 1:+.2%})")
    for p, b in base["text"].items():
        n = now["text"][p]
        if n > b:
            worse.append(
                f"code size: {p}'s .text is {n:,} bytes, more than {b:,} ({n / b - 1:+.2%})"
            )
        elif n < b:
            better.append(
                f"code size: {p}'s .text is {n:,} bytes, less than {b:,} ({n / b - 1:+.2%})"
            )
    for p, b in base["compile_seconds"].items():
        n = now["compile_seconds"][p]
        if n > GATE_SLACK * b + 1.0:
            worse.append(f"compile time: {p} takes {n:.2f} s, over {GATE_SLACK:g} times {b:.2f} s")
    for p, b in base["compile_rss_kib"].items():
        n = now["compile_rss_kib"][p]
        if n > GATE_SLACK * b + (64 << 10):
            worse.append(
                f"compile memory: {p} peaks at {n >> 10} MiB, over {GATE_SLACK:g} times {b >> 10} MiB"
            )
    return worse, better


def cmd_gate(s):
    """One verdict for a change to the compiler, on Lua and SQLite: build both with fcc (`-O`, or
    the fcc configurations of --configs), check that they behave as GCC -O2's builds do, count
    the instructions every workload executes, and compare with the accepted baseline
    (benchmarks/projects/gate.json). FAIL, and exit 1, if a file doesn't compile (in --timeout
    seconds), behavior differs, or anything is worse than the baseline: a workload's
    instructions, a project's code size, or (beyond twice) its compile time or memory. A
    configuration with no baseline of its own is held to `fcc -O`'s: a pipeline proposed for
    `-O` must not be worse than `-O`.

    --update writes the baseline, and only when the verdict is PASS: the baseline moves one way.
    To accept a trade, edit gate.json by hand, where the diff shows it."""
    global BUILD_CONFIGS
    gated = [c for c in BUILD_CONFIGS if c.startswith("fcc")] if s.args.configs else ["fcc-O"]
    if not gated:
        die("gate: --configs names no fcc configuration")
    BUILD_CONFIGS = [*gated, REFERENCE]
    s.args.reps = 1
    if s.args.timeout is None:
        s.args.timeout = 300
    baseline = json.loads(GATE.read_text()) if GATE.exists() else None
    if baseline is None and not s.args.update:
        die(f"gate: no baseline at {GATE}; make one with `gate --update`")
    cmd_prepare(s)
    cmd_build(s)
    cmd_check(s)
    cmd_count(s)
    now = gate_measure(s, gated)
    report: dict[str, Any] = {"verdict": "PASS", "configs": {}}
    for c in gated:
        base_of = c if baseline and c in baseline["configs"] else "fcc-O"
        base = baseline["configs"].get(base_of) if baseline else None
        if base is None:
            # The first baseline: behavior must still be right.
            base = {k: {} for k in ("instructions", "text", "compile_seconds", "compile_rss_kib")}
        worse, better = gate_compare(now[c], base)
        report["configs"][c] = {"against": base_of, "worse": worse, "better": better}
        if worse:
            report["verdict"] = "FAIL"
    save(s.out, "gate", report)
    for c, r in report["configs"].items():
        print(f"gate: {c}, against the baseline of {r['against']}:")
        for line in r["worse"]:
            print(f"  WORSE   {line}")
        for line in r["better"]:
            print(f"  better  {line}")
        if not r["worse"] and not r["better"]:
            print("  the same as the baseline")
    print(f"gate: {report['verdict']}")
    if report["verdict"] != "PASS":
        sys.exit(1)
    if s.args.update:
        configs = dict(baseline["configs"]) if baseline else {}
        for c in gated:
            old = configs.get(c)
            new = now[c]
            if old:
                # The baseline only ever gets better: a count that is the same (within
                # GATE_SAME) keeps its old value, and the time and memory keep the lower one.
                for w, n in new["instructions"].items():
                    b = old["instructions"].get(w, n)
                    new["instructions"][w] = n if n < b * (1 - GATE_SAME) else b
                for key in ("compile_seconds", "compile_rss_kib"):
                    for p, n in new[key].items():
                        new[key][p] = min(n, old[key].get(p, n))
            configs[c] = new
        text = json.dumps(
            {
                "about": "The accepted results of `fai gate` (benchmarks/projects/README.md): "
                "what a change may not make worse. Written by `fai gate --update`, which "
                "refuses unless the gate passes, and then only moves a number down.",
                "configs": configs,
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
        "--plain",
        help="comma-separated source files (by stem: lvm) that the experimental fcc "
        "configurations compile with `fcc -O` instead, for files the backend can't compile "
        "under an experimental pipeline in practical time",
    )
    args = ap.parse_args()
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
