#!/usr/bin/env python3
"""Summarize bench.py's results: totals and geometric-mean ratios to fcc -O, the programs
that run longest, and (with BENCH_HIST=1 results) the executed instructions by category.
Usage: summarize.py OUTDIR/results.json [N-PROGRAMS]"""
import json, sys, math
r = json.load(open(sys.argv[1]))
cfgs = [c for c in next(iter(r.values())).keys()]
bad = [(n, c) for n, v in r.items() for c in cfgs if not v[c].get("same", False)]
print("mismatches or errors:", bad)
def geo(xs): return math.exp(sum(map(math.log, xs)) / len(xs))
base = "fcc-O"
rows = []
for n, v in sorted(r.items()):
    if any("error" in v[c] for c in cfgs): continue
    rows.append((n, v))
print(f"{len(rows)} programs")
for metric in ["insns", "loads", "stores", "text"]:
    line = f"{metric:7}"
    for c in cfgs:
        tot = sum(v[c][metric] for _, v in rows)
        ratios = [max(v[c][metric],1) / max(v[base][metric],1) for _, v in rows]
        line += f" | {c}: total {tot:>11,} geo x{geo(ratios):.3f}"
    print(line)
for metric in ["mfir_loads", "mfir_stores", "mfir_slots"]:
    line = f"{metric:11}"
    for c in cfgs:
        if metric in rows[0][1][c]:
            line += f" | {c}: {sum(v[c][metric] for _, v in rows):>6}"
    print(line)
# Per-program top table
print("\nprogram            gccO1-insns   fcc-O-insns   exp-insns  exp/O  | loads O -> exp (gcc)")
for n, v in sorted(rows, key=lambda x: -x[1][base]["insns"])[: int(sys.argv[2]) if len(sys.argv) > 2 else 25]:
    e = cfgs[-1]
    print(f"{n:18} {v['gcc-O1']['insns']:>12,} {v[base]['insns']:>12,} {v[e]['insns']:>11,}  {v[e]['insns']/v[base]['insns']:.2f}  | {v[base]['loads']:>9,} -> {v[e]['loads']:>9,} ({v['gcc-O1']['loads']:,})")


def category(m):
    if m.startswith(("ldr", "ldur", "ldp")):
        return "load"
    if m.startswith(("str", "stur", "stp")):
        return "store"
    if m in ("mov", "fmov"):
        return m
    if m in ("movz", "movk", "movn", "adrp", "mov#", "fmov#"):
        return "constant/address"
    if m in ("sxtw", "sxth", "sxtb", "uxtb", "uxth", "sbfx", "ubfx"):
        return "extension"
    if m in ("cset", "csinc", "tst", "ands", "cmp", "subs", "fcmp", "fcmpe", "csel", "cmn"):
        return "compare/flags"
    if m in ("b", "bl", "blr", "br", "ret", "cbz", "cbnz", "tbz", "tbnz") or m.startswith("b."):
        return "branch"
    return "other"

if any("hist" in v[c] for _, v in rows for c in cfgs):
    print("\nexecuted instructions by category:")
    for c in cfgs:
        tot = {}
        for _, v in rows:
            for k, n in v[c].get("hist", {}).items():
                tot[category(k)] = tot.get(category(k), 0) + n
        s = sum(tot.values()) or 1
        print(f"{c:8} " + "  ".join(f"{k} {n / s:.0%}" for k, n in sorted(tot.items(), key=lambda x: -x[1])))
