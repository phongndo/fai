#!/usr/bin/env python3
"""Dynamic and static costs of the C corpus under several fai-cc pipelines (see README.md).

For each program of frontends/c/tests: build it with the reference compiler (GCC -O1), fai-cc,
fai-cc -O, and fai-cc with the experimental pipeline ($BENCH_PASSES, and each of $BENCH_MORE,
separated by `;`); link non-PIE; run under qemu-aarch64 with the counting plugin restricted to
the program's own object's .text (not libc's, the runtime's, or the C helpers'); and check that
every build prints the same and exits the same as the reference. With BENCH_HIST=1, also count
executed instructions by mnemonic. Writes OUTDIR/results.json; summarize.py prints it.

Usage, in the dev shell, after build-plugins.sh OUTDIR:
  python3 -I bench.py REPO OUTDIR [NAME-FILTER]
$BENCH_FAI picks the fai-cc binary (default REPO/build/fai-cc/fai-cc).
"""
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys

REPO, OUT = sys.argv[1], sys.argv[2]
ONLY = sys.argv[3] if len(sys.argv) > 3 else ""
PLUGIN = os.path.join(OUT, "libcount.so")
HIST = os.path.join(OUT, "libhist.so") if os.environ.get("BENCH_HIST") else None
CC = "aarch64-unknown-linux-gnu-cc"
TESTS = os.path.join(REPO, "frontends/c/tests")
INC = os.path.join(TESTS, "runtime")
FAI = os.environ.get("BENCH_FAI") or os.path.join(REPO, "build/fai-cc/fai-cc")
EXP = os.environ.get("BENCH_PASSES", "mem2reg,stackdce,fwd,copyprop,dse,dce")
CONFIGS = [
    ("gcc-O1", None),
    ("fai", []),
    ("fai-O", ["-O"]),
    ("fai-exp", ["--passes", EXP, "--experimental"]),
] + [
    (f"fai-exp{i}", ["--passes", p, "--experimental"])
    for i, p in enumerate(filter(None, os.environ.get("BENCH_MORE", "").split(";")), 2)
]
os.makedirs(OUT, exist_ok=True)


def sh(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, **kw)


def build_common():
    rt = os.path.join(OUT, "fai_runtime.o")
    sh([CC, "-O1", "-c", os.path.join(INC, "fai_runtime.c"), "-o", rt]).check_returncode()
    return rt


def text_range(exe, obj):
    syms = sh(["aarch64-unknown-linux-gnu-nm", "--defined-only", obj]).stdout
    names = {l.split()[2] for l in syms.splitlines() if len(l.split()) == 3 and l.split()[1] in "Tt"}
    size = 0
    for l in sh(["aarch64-unknown-linux-gnu-readelf", "-SW", obj]).stdout.splitlines():
        m = re.search(r"\]\s+\.text\s+\S+\s+\S+\s+\S+\s+([0-9a-f]+)", l)
        if m:
            size = int(m.group(1), 16)
    addrs = []
    for l in sh(["aarch64-unknown-linux-gnu-nm", exe]).stdout.splitlines():
        p = l.split()
        if len(p) == 3 and p[2] in names:
            addrs.append(int(p[0], 16))
    lo = min(addrs)
    return lo, lo + size, size


def one(file):
    name = os.path.basename(file)[:-2]
    helper = os.path.join(TESTS, "extern", name + ".c")
    objs = [os.path.join(OUT, "fai_runtime.o")]
    if os.path.exists(helper):
        h = os.path.join(OUT, name + ".extern.o")
        sh([CC, "-O1", "-w", "-std=gnu17", "-ffp-contract=off", "-c", "-I", INC, helper, "-o", h]).check_returncode()
        objs.append(h)
    res = {}
    for cfg, flags in CONFIGS:
        obj = os.path.join(OUT, f"{name}.{cfg}.o")
        exe = os.path.join(OUT, f"{name}.{cfg}")
        if flags is None:
            r = sh([CC, "-O1", "-w", "-std=gnu17", "-ffp-contract=off", "-c", "-I", INC, file, "-o", obj])
        else:
            r = sh([FAI, file, "-I", INC, "-o", obj] + flags)
        if r.returncode:
            res[cfg] = {"error": r.stderr[-400:]}
            continue
        sh([CC, "-no-pie", obj] + objs + ["-lm", "-o", exe]).check_returncode()
        lo, hi, size = text_range(exe, obj)
        run = sh(["qemu-aarch64", "-plugin", f"{PLUGIN},lo={lo},hi={hi}", exe], timeout=600)
        m = re.search(r"COUNT (\d+) (\d+) (\d+)", run.stderr)
        res[cfg] = {
            "insns": int(m.group(1)), "loads": int(m.group(2)), "stores": int(m.group(3)),
            "text": size, "out": (run.stdout, run.returncode),
        }
        if HIST:
            h = sh(["qemu-aarch64", "-plugin", f"{HIST},lo={lo},hi={hi}", exe], timeout=1200)
            mn = {}
            for l in sh(["aarch64-unknown-linux-gnu-objdump", "-d", "--no-show-raw-insn", exe]).stdout.splitlines():
                m2 = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*([^/<]*)", l)
                if m2:
                    # objdump spells `movz`/`movn`/`orr` of an immediate as `mov x0, #42`, and
                    # `fmov d0, #1.0` takes one too: those make constants, not copies.
                    op = m2.group(2)
                    if op in ("mov", "fmov") and "#" in m2.group(3):
                        op += "#"
                    mn[int(m2.group(1), 16)] = op
            hist = {}
            for l in h.stderr.splitlines():
                if l.startswith("HIST "):
                    _, pc, n = l.split()
                    k = mn.get(int(pc, 16), "?")
                    hist[k] = hist.get(k, 0) + int(n)
            res[cfg]["hist"] = hist
    for cfg, flags in CONFIGS:
        if flags and "error" not in res[cfg]:
            m = sh([FAI, file, "-I", INC, "--emit", "mfir"] + flags).stdout
            res[cfg]["mfir_loads"] = m.count("mem.load")
            res[cfg]["mfir_stores"] = m.count("mem.store")
            res[cfg]["mfir_slots"] = m.count("mem.stack")
    ref = res["gcc-O1"].get("out")
    for cfg, _ in CONFIGS:
        if "out" in res[cfg]:
            res[cfg]["same"] = res[cfg]["out"] == ref
            del res[cfg]["out"]
    return name, res


def main():
    build_common()
    files = sorted(
        os.path.join(TESTS, f) for f in os.listdir(TESTS) if f.endswith(".c") and ONLY in f
    )
    with cf.ThreadPoolExecutor(os.cpu_count()) as ex:
        results = dict(ex.map(one, files))
    json.dump(results, open(os.path.join(OUT, "results.json"), "w"), indent=1)
    print(f"{len(results)} programs; summarize with summarize.py {OUT}/results.json")


main()
