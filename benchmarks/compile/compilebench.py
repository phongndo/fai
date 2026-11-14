#!/usr/bin/env python3
"""compilebench: how long fai takes to compile programs, against Clang and GCC.

This measures the compiler's latency on one input (what an edit/compile/test loop waits for), not
the speed of the code it generates (benchmarks/c/cbench.py, benchmarks/inference/) and not the
time to rebuild the compiler itself (see docs/performance/compile-speed.md). Run from the
repository root in the dev shell, on Linux:

  python3 -B benchmarks/compile/compilebench.py run [--rounds N] [--only W,...] [--out DIR]
      [--fcc NAME=PATH ...] [--fir NAME=PATH ...] [--configs C,...]

Each workload is compiled by each configuration once per round, after one warmup round, with the
configurations in a different order each round, so drift and other load spread over all of them.
Every run records wall time, CPU time (user + system, the process and the children it waited for:
the assembler, the include probe), and peak resident memory (`wait4`). A separate set of rounds
runs fai's configurations with FIR_TIME=1 and keeps the phase reports (fir::timing), so the
timing never perturbs the measured runs. fcc's outputs are hashed (SHA-256), so two fcc builds
can be checked to produce the same bytes.

Workloads (`WORKLOADS`): `small` are the 12 programs of benchmarks/c/programs (20-65 lines),
`medium` and `large` are generated C (cbench.synth: loops, branches, switches, arrays, calls):
many functions of 10 statements, or one function of many statements.

Configurations (`--configs`, default all that apply):
  fcc-O0.o, fcc-O.o       fcc to an AArch64 object (Clang's frontend, fai, GNU as)
  fcc-O.s                 fcc -O to assembly: no assembler
  fcc-x86-O.o             fcc --target x86_64 -O to an object (the integer subset; others skip)
  fir-O.s                 `fir compile -O` from MFIR: fai's own pipeline in process, no C frontend
  clang-O0.o, clang-O2.o  Clang with fcc's exact Clang setup (cbench.Tools), AArch64
  gcc-O0.o, gcc-O2.o      the AArch64 cross GCC
  clang-x86-O0.o, gcc-x86-O0.o   the host's Clang and GCC for x86-64, for fcc-x86-O.o
The reference compilers get -ffp-contract=off and no Nix hardening, as in cbench. These are
compile-time comparisons only: the configurations don't make code of the same quality.

`--fcc NAME=PATH` and `--fir NAME=PATH` measure other builds of fcc or fir (a baseline) too, as
configurations fcc@NAME-O.o, fcc@NAME-O0.o, fcc@NAME-O.s, fcc@NAME-x86-O.o, and fir@NAME-O.s.
FCC_CACHE_DIR is set to a fresh directory per fcc build, and its first run is the warmup, so
"cached" runs measure a warm include-probe cache; `--fcc-cold` empties it before every run.

Output: DIR/results.json (every run) and DIR/report.md (medians, quartiles, ranges, phases).
"""

import argparse
import hashlib
import json
import os
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parents[1]
sys.path.insert(0, str(ROOT / "benchmarks/c"))
import cbench  # noqa: E402  (the reference compilers' setup, and the C generator)

SMALL = sorted(p.stem for p in (ROOT / "benchmarks/c/programs").glob("*.c"))
# name: (functions, statements per function)
GENERATED = {
    "gen-100x10": (100, 10),
    "gen-400x10": (400, 10),
    "gen-1600x10": (1600, 10),
    "gen-1x400": (1, 400),
    "gen-1x1600": (1, 1600),
    "gen-1x6400": (1, 6400),
}
SIZE = {"gen-100x10": "medium", "gen-400x10": "medium", "gen-1x400": "medium",
        "gen-1600x10": "large", "gen-1x1600": "large", "gen-1x6400": "large"}


def die(msg):
    print(f"compilebench: {msg}", file=sys.stderr)
    sys.exit(1)


def measure(cmd, env, out_file=None):
    """Run cmd; wall seconds, CPU seconds (with waited-for children), peak RSS in KiB, stderr."""
    t0 = time.perf_counter()
    p = subprocess.Popen([str(c) for c in cmd], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                         env=env)
    _, status, ru = os.wait4(p.pid, 0)
    wall = time.perf_counter() - t0
    err = p.stderr.read().decode(errors="replace")
    p.stderr.close()
    code = os.waitstatus_to_exitcode(status)
    return {"wall": wall, "cpu": ru.ru_utime + ru.ru_stime, "rss_kib": ru.ru_maxrss,
            "exit": code, "stderr": err if code != 0 or "fir: time:" in err else ""}


def sha256(path):
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def phases(stderr):
    """fir::timing's report: {phase: self ms} (summed-over-threads phases end in ' *')."""
    out = {}
    for line in stderr.splitlines():
        if not line.startswith("fir: time:") or "self ms" in line or "summed over" in line:
            continue
        parts = line[len("fir: time:"):].split()
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


class Bench:
    def __init__(self, args):
        self.args = args
        self.tools = cbench.Tools()
        self.out = Path(args.out).resolve()
        self.work = self.out / "work"
        if self.work.exists():
            shutil.rmtree(self.work)
        self.work.mkdir(parents=True)
        self.env = dict(self.tools.env, FIR_TIME="0", PYTHONDONTWRITEBYTECODE="1")
        self.fccs = {"fcc": self.tools.fcc}
        self.firs = {"fir": self.tools.fir}
        for spec, table in ((args.fcc, self.fccs), (args.fir, self.firs)):
            for s in spec or []:
                name, _, path = s.partition("=")
                if not name or not path or not Path(path).is_file():
                    die(f"bad build '{s}': want NAME=PATH to an executable")
                table[name] = Path(path).resolve()
        self.cache_dirs = {n: self.work / f"cache-{n}" for n in self.fccs}
        self.work_src = {}
        self.x86_cc = {"clang": shutil.which("clang"), "gcc": shutil.which("gcc")}

    # -- workloads ---------------------------------------------------------------------------

    def workloads(self):
        names = SMALL + list(GENERATED)
        if self.args.only:
            want = self.args.only.split(",")
            names = [n for n in names if any(w == n or w == SIZE.get(n, "small") for w in want)]
        out = {}
        for n in names:
            if n in GENERATED:
                src = self.work / f"{n}.c"
                src.write_text(cbench.synth(*GENERATED[n]))
            else:
                src = ROOT / "benchmarks/c/programs" / f"{n}.c"
            self.work_src[n] = src
            out[n] = {"src": src, "size": SIZE.get(n, "small"),
                      "lines": len(src.read_text().splitlines())}
        return out

    def mfir(self, name):
        """The workload's MFIR (unoptimized), from the default fcc: `fir compile`'s input."""
        path = self.work / f"{name}.mfir"
        if not path.exists():
            r = subprocess.run([self.tools.fcc, self.work_src[name], "--emit", "mfir", "-o", path], env=self.env,
                               capture_output=True, text=True)
            if r.returncode != 0:
                return None
        return path

    # -- configurations ----------------------------------------------------------------------

    def configs(self):
        """name: (kind, command maker, environment, output file, output group). Outputs in one
        group must be identical across builds (fcc's, and fir's, separately)."""
        c = {}
        o = self.work / "o"
        o.mkdir(exist_ok=True)
        for n, fcc in self.fccs.items():
            env = dict(self.env, FCC_CACHE_DIR=str(self.cache_dirs[n]))
            label = "fcc" if n == "fcc" else f"fcc@{n}"
            for suffix, flags in (("O0.o", []), ("O.o", ["-O"]), ("O.s", ["-O", "--emit", "asm"]),
                                  ("x86-O.o", ["--target", "x86_64", "-O"])):
                out = o / f"{label}-{suffix}"
                c[f"{label}-{suffix}"] = ("fai", lambda s, w, fcc=fcc, flags=flags, out=out:
                                      [fcc, s, *flags, "-o", out], env, out, f"fcc {suffix}")
        for n, fir in self.firs.items():
            label = "fir" if n == "fir" else f"fir@{n}"
            out = o / f"{label}.fir-O.s"
            c[f"{label}-O.s"] = ("fai", lambda s, w, fir=fir, out=out:
                             (lambda m: m and [fir, "compile", m, "-O", "--emit", "asm", "-o", out])(self.mfir(w)),
                             self.env, out, "fir O.s")
        for cfg in ("clang-O0", "clang-O2", "gcc-O0", "gcc-O2"):
            c[f"{cfg}.o"] = ("ref", lambda s, w, cfg=cfg: self.tools.compile_cmd(cfg, s, o / f"{cfg}.o"),
                             self.env, None, None)
        for cc in ("clang", "gcc"):
            if self.x86_cc[cc]:
                c[f"{cc}-x86-O0.o"] = ("ref", lambda s, w, cc=cc: [self.x86_cc[cc], "-c", "-O0", "-ffp-contract=off",
                                                                  s, "-o", o / f"{cc}-x86.o"], self.env, None, None)
        if self.args.configs:
            want = self.args.configs.split(",")
            c = {k: v for k, v in c.items() if k in want}
        return c

    # -- running -----------------------------------------------------------------------------

    def run(self):
        identity = self.tools.identity()
        identity["loadavg_start"] = Path("/proc/loadavg").read_text().split()[:3]
        identity["builds"] = {**{("fcc" if k == "fcc" else f"fcc@{k}"): str(v) for k, v in self.fccs.items()},
                              **{("fir" if k == "fir" else f"fir@{k}"): str(v) for k, v in self.firs.items()}}
        identity["build_sha256"] = {k: sha256(v) for k, v in identity["builds"].items()}
        work = self.workloads()
        configs = self.configs()
        rounds = self.args.rounds
        results = {"identity": identity, "rounds": rounds, "workloads": {}, "configs": list(configs)}
        rng = random.Random(1)
        for name, w in work.items():
            src = w["src"]
            entry = {"size": w["size"], "lines": w["lines"], "runs": {}, "first": {}, "phases": {},
                     "outputs": {}, "skipped": {}}
            # A configuration that fails on its first try (fcc refusing what it doesn't support,
            # such as floats on x86-64) is skipped for this workload, with its message.
            live = {}
            for cname, (kind, mk, env, outp, group) in configs.items():
                cmd = mk(src, name)
                if not cmd:
                    entry["skipped"][cname] = "no MFIR"
                    continue
                r = measure(cmd, env)  # warmup (and the include-probe cache's first fill)
                if r["exit"] != 0:
                    last = (r["stderr"].strip().splitlines() or ["failed"])[-1]
                    entry["skipped"][cname] = last.replace(str(src) + ": ", "")
                    continue
                live[cname] = (kind, cmd, env, outp)
                entry["first"][cname] = {k: r[k] for k in ("wall", "cpu", "rss_kib")}
                if outp is not None:
                    entry["outputs"][cname] = [group, sha256(outp)]
            for r_i in range(rounds):
                order = list(live)
                rng.shuffle(order)
                for cname in order:
                    kind, cmd, env, outp = live[cname]
                    if self.args.fcc_cold and kind == "fai":
                        for d in self.cache_dirs.values():
                            shutil.rmtree(d, ignore_errors=True)
                    r = measure(cmd, env)
                    if r["exit"] != 0:
                        die(f"{cname} on {name} failed in round {r_i}: {r['stderr'][-2000:]}")
                    entry["runs"].setdefault(cname, []).append(
                        {k: r[k] for k in ("wall", "cpu", "rss_kib")})
            # Phase reports, in their own runs.
            for cname, (kind, cmd, env, outp) in live.items():
                if kind != "fai":
                    continue
                reps = []
                for _ in range(max(1, min(5, rounds))):
                    r = measure(cmd, dict(env, FIR_TIME="1"))
                    reps.append(phases(r["stderr"]))
                keys = sorted({k for rep in reps for k in rep})
                if not keys:
                    continue  # a build without FIR_TIME
                entry["phases"][cname] = {k: statistics.median(rep.get(k, 0.0) for rep in reps)
                                          for k in keys}
            results["workloads"][name] = entry
            print(f"compilebench: {name} done", file=sys.stderr, flush=True)
        identity["loadavg_end"] = Path("/proc/loadavg").read_text().split()[:3]
        self.out.mkdir(parents=True, exist_ok=True)
        (self.out / "results.json").write_text(json.dumps(results, indent=1) + "\n")
        (self.out / "report.md").write_text(report(results))
        print(f"compilebench: wrote {self.out / 'report.md'}", file=sys.stderr)


def q(xs, f):
    xs = sorted(xs)
    if len(xs) == 1:
        return xs[0]
    return statistics.quantiles(xs, n=4, method="inclusive")[{0.25: 0, 0.75: 2}[f]]


def report(res):
    idn = res["identity"]
    lines = ["# compilebench report", "",
             f"- revision `{idn['revision'][:12]}`{' (dirty)' if idn['dirty'] else ''}; builds: "
             + ", ".join(f"`{k}` = {v} (sha256 {idn['build_sha256'][k][:12] if idn['build_sha256'][k] else '?'})" for k, v in idn["builds"].items()),
             f"- host: {idn['host']}, {idn['host_cpu']}, {idn['host_cpus']} CPUs; load average "
             f"{' '.join(idn['loadavg_start'])} at the start, {' '.join(idn['loadavg_end'])} at the end",
             f"- {idn['gcc']}; {idn['clang']}; {idn['rustc']}",
             f"- {res['rounds']} rounds after a warmup, configurations shuffled per round. Wall and CPU "
             "in ms: median [quartiles] (min-max); peak RSS in MiB (max). \"first run\" is the warmup: "
             "fcc's include-probe cache is empty then (a cold cache), and warm after.", ""]
    # The overview: median wall time of every configuration on every workload.
    cfgs = []
    for w in res["workloads"].values():
        for c in sorted(w["runs"], key=lambda c: (not c.startswith("f"), c)):
            if c not in cfgs:
                cfgs.append(c)
    for metric, title, scale, agg in (
            ("wall", "Median wall time, ms", 1e3, statistics.median),
            ("cpu", "Median CPU time (user + system, with waited-for children), ms", 1e3, statistics.median),
            ("rss_kib", "Peak resident memory, MiB", 1 / 1024, max)):
        lines += [f"## Overview: {title}", "", "| workload | " + " | ".join(cfgs) + " |",
                  "|---|" + "---:|" * len(cfgs)]
        for name, w in res["workloads"].items():
            cells = []
            for c in cfgs:
                runs = w["runs"].get(c)
                cells.append(f"{agg(r[metric] for r in runs) * scale:.1f}" if runs else "-")
            lines.append(f"| {name} | " + " | ".join(cells) + " |")
        lines.append("")
    for name, w in res["workloads"].items():
        lines += [f"## {name} ({w['size']}, {w['lines']} lines)", "",
                  "| config | wall ms | CPU ms | RSS MiB | first run ms |", "|---|---:|---:|---:|---:|"]
        for cname, runs in sorted(w["runs"].items(), key=lambda kv: (not kv[0].startswith("f"), kv[0])):
            wall = [r["wall"] * 1e3 for r in runs]
            cpu = [r["cpu"] * 1e3 for r in runs]
            rss = max(r["rss_kib"] for r in runs) / 1024
            lines.append(f"| {cname} | {statistics.median(wall):.1f} [{q(wall, 0.25):.1f}, {q(wall, 0.75):.1f}] "
                         f"({min(wall):.1f}-{max(wall):.1f}) | {statistics.median(cpu):.1f} | {rss:.0f} | "
                         f"{w['first'][cname]['wall'] * 1e3:.1f} |")
        for cname, why in w["skipped"].items():
            lines.append(f"| {cname} | skipped: {why} | | | |")
        groups = {}
        for cname, (group, h) in w["outputs"].items():
            groups.setdefault(group, {})[cname] = h
        same = [g for g, hs in groups.items() if len(hs) > 1 and len(set(hs.values())) == 1]
        differ = [g for g, hs in groups.items() if len(set(hs.values())) > 1]
        lines.append("")
        if same or differ:
            lines.append("Outputs across builds: " + "; ".join(
                [f"{g}: identical" for g in same] + [f"{g}: **differ** ({', '.join(groups[g])})" for g in differ]))
            lines.append("")
        if w["phases"]:
            names = list(w["phases"])
            keys = []
            for c in names:
                for k in w["phases"][c]:
                    if k not in keys:
                        keys.append(k)
            lines += ["Phases (FIR_TIME=1, self ms, median of up to 5 runs; `*` summed over threads):", "",
                      "| phase | " + " | ".join(names) + " |", "|---|" + "---:|" * len(names)]
            for k in keys:
                lines.append(f"| {k} | " + " | ".join(
                    f"{w['phases'][c].get(k, 0):.2f}" if k in w["phases"][c] else "" for c in names) + " |")
            # What no phase covers: process start (loading Clang's and LLVM's libraries),
            # Clang's setup, exit.
            outside = []
            for c in names:
                t = w["phases"][c].get("total (main thread)")
                outside.append(f"{statistics.median(r['wall'] for r in w['runs'][c]) * 1e3 - t:.2f}"
                               if t is not None and c in w["runs"] else "")
            lines.append("| outside the phases (median wall - total) | " + " | ".join(outside) + " |")
            lines.append("")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--rounds", type=int, default=10)
    r.add_argument("--only", help="workloads or sizes (small, medium, large), comma-separated")
    r.add_argument("--configs", help="configurations, comma-separated")
    r.add_argument("--out", default=str(ROOT / "target/compilebench"))
    r.add_argument("--fcc", action="append", help="NAME=PATH: another fcc build to measure")
    r.add_argument("--fir", action="append", help="NAME=PATH: another fir build to measure")
    r.add_argument("--fcc-cold", action="store_true", help="empty the include-probe cache before every fcc run")
    rp = sub.add_parser("report")
    rp.add_argument("--out", default=str(ROOT / "target/compilebench"))
    a = ap.parse_args()
    if platform.system() != "Linux":
        die("Linux only (the reference compilers and glibc are the dev shell's Linux ones)")
    if a.cmd == "run":
        Bench(a).run()
    else:
        res = json.loads((Path(a.out) / "results.json").read_text())
        (Path(a.out) / "report.md").write_text(report(res))


if __name__ == "__main__":
    main()
