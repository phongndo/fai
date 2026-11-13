#!/usr/bin/env python3
"""cbench: fcc's end-to-end C baseline against GCC and Clang.

Run from the repository root in the dev shell (Linux; `nix develop -c python3 ...`):

  benchmarks/c/cbench.py build           compile every program with every configuration
                                          (compile time, fcc's phases, code size), link
                                          statically against the target's glibc
  benchmarks/c/cbench.py count           run each binary at its small size (under qemu-user off
                                          AArch64): output and exit code against the reference,
                                          executed instructions and their mix (a QEMU plugin)
  benchmarks/c/cbench.py scaling         fcc's compile time on generated inputs of growing size
  benchmarks/c/cbench.py time [--ssh HOST [--docker IMAGE]]
                                          wall time at the large size, on native AArch64 only:
                                          here if this machine is AArch64 Linux, else on HOST
                                          (directly, or in a Docker container there)
  benchmarks/c/cbench.py report          target/cbench/report.md from what was measured
  benchmarks/c/cbench.py all [time options]

Every step writes JSON to target/cbench/ (`--out DIR` elsewhere). Nothing is timed under
emulation: `benchrun`, the native driver, refuses to run unless the CPU reports a hardware
implementer (QEMU's CPU reports 0x00, which Arm reserves for software).
"""

import argparse
import json
import os
import platform
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parents[1]
PROGRAMS = BENCH / "programs"

# Each program's argument: (count size, run under qemu for behavior and instruction counts;
# time size, run natively for wall time). Time sizes take GCC -O2 about 0.15-0.4 s on an Apple M4 Max.
SIZES = {
    "bintree": (1, 150),
    "bytecode": (200000, 15000000),
    "crc32": (20, 2000),
    "fannkuch": (8, 10),
    "hashtab": (1, 100),
    "mandel": (100, 2400),
    "matmul": (1, 400),
    "nbody": (20000, 8000000),
    "nqueens": (8, 14),
    "quicksort": (1, 75),
    "sieve": (2, 150),
    "strings": (5, 3000),
}

CONFIGS = ["fcc", "fcc-O", "gcc-O0", "gcc-O1", "gcc-O2", "clang-O0", "clang-O2"]
REFERENCE = "gcc-O2"
SCALING_SIZES = [25, 100, 400, 1600]


def die(msg):
    print(f"cbench: {msg}", file=sys.stderr)
    sys.exit(1)


def run(cmd, env=None, cwd=None, check=True, capture=True, timeout=None):
    p = subprocess.run(
        cmd,
        env=env,
        cwd=cwd,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
        text=True,
        timeout=timeout,
    )
    if check and p.returncode != 0:
        die(f"failed ({p.returncode}): {shlex.join(map(str, cmd))}\n{p.stdout or ''}{p.stderr or ''}")
    return p


def timed(cmd, env, reps):
    """Median and minimum wall seconds of `reps` runs of cmd (which must succeed). Compile times
    are reported as the minimum: other load on a shared host only ever adds time."""
    times = []
    for _ in range(reps):
        t0 = time.perf_counter()
        run(cmd, env=env)
        times.append(time.perf_counter() - t0)
    return {"median": statistics.median(times), "min": min(times), "runs": times}


def first_line(cmd):
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        return next((l.strip() for l in p.stdout.splitlines() if l.strip()), "?")
    except OSError:
        return None


class Tools:
    """The compilers and binutils, resolved once, as the dev shell provides them."""

    def __init__(self):
        if platform.system() != "Linux":
            die("Linux only: the benchmarks link against the AArch64 target's static glibc")
        self.native = platform.machine() == "aarch64"
        # The reference GCC, which also links every binary. Not `cc`: on AArch64 the dev shell's
        # `cc` is Clang.
        self.cc = os.environ.get("FCC_BENCH_GCC") or "aarch64-unknown-linux-gnu-cc"
        prefix = "" if self.native else "aarch64-unknown-linux-gnu-"
        self.objdump, self.size, self.nm = (prefix + t for t in ("objdump", "size", "nm"))
        self.libc = os.environ.get("FCC_BENCH_LIBC_STATIC")
        if not self.libc or not Path(self.libc, "libc.a").exists():
            die("FCC_BENCH_LIBC_STATIC must name the target's static glibc (the dev shell sets it)")
        for t in (self.cc, self.objdump, self.size, self.nm, "cmake", "ninja", "clang"):
            if not shutil.which(t):
                die(f"{t} is not on PATH: run in the dev shell (nix develop)")
        if "(GCC)" not in (first_line([self.cc, "--version"]) or ""):
            die(f"{self.cc} is not GCC ({first_line([self.cc, '--version'])}): set FCC_BENCH_GCC "
                "to an AArch64 GCC (the dev shell sets it)")
        # The reference compilers' flags must be only what is written here: Nix's compiler
        # wrapper otherwise adds hardening (-fstack-protector-strong, -fzero-call-used-regs, ...)
        # to GCC's code and not to fcc's.
        self.env = dict(os.environ, NIX_HARDENING_ENABLE="")
        self.fcc = ROOT / "build/fcc/fcc"
        self.fir = ROOT / "target/release/fir"
        self.clang, self.clang_flags = self._clang()

    def _clang(self):
        """The reference Clang with exactly fcc's Clang setup (main.cpp): the target, no
        host includes, Clang's resource directory, and the AArch64 compiler's system include
        directories after it. Nix's x86 wrapper would add the host's glibc headers, so its
        unwrapped compiler is used."""
        wrapper = Path(shutil.which("clang")).resolve().parent.parent
        clang, resource = "clang", None
        orig = wrapper / "nix-support/orig-cc"
        if orig.exists():
            clang = str(Path(orig.read_text().strip()) / "bin/clang")
            m = re.search(r"-resource-dir=(\S+)", (wrapper / "nix-support/cc-cflags").read_text())
            resource = m.group(1) if m else None
        flags = ["--target=aarch64-unknown-linux-gnu", "-nostdlibinc"]
        if resource:
            flags.append(f"-resource-dir={resource}")
        out = run([self.cc, "-E", "-Wp,-v", "-x", "c", "/dev/null"], env=self.env).stderr
        inside = False
        for line in out.splitlines():
            l = line.strip()
            if l.startswith("#include <...>"):
                inside = True
            elif l.startswith("End of search list"):
                inside = False
            elif inside and not any(s in l for s in ("/lib/gcc/", "/lib/clang/", "/include-fixed")):
                flags += ["-idirafter", l]
        return clang, flags

    def build_fcc(self):
        build = ROOT / "build/fcc"
        if not (build / "build.ninja").exists():
            run(["cmake", "-S", ROOT / "frontends/c", "-B", build, "-G", "Ninja",
                 "-DCMAKE_BUILD_TYPE=Release"], capture=False)
        run(["cmake", "--build", build], capture=False)
        run(["cargo", "build", "--release", "-q", "-p", "fir"], cwd=ROOT, capture=False)

    def compile_cmd(self, config, src, obj):
        if config.startswith("fcc"):
            return [self.fcc, src] + (["-O"] if config == "fcc-O" else []) + ["-o", obj]
        compiler, level = config.split("-")
        fp = ["-ffp-contract=off"]  # fcc never contracts a * b + c into an fma
        if compiler == "gcc":
            return [self.cc, "-c", f"-{level}", *fp, src, "-o", obj]
        return [self.clang, *self.clang_flags, "-c", f"-{level}", *fp, src, "-o", obj]

    def link_cmd(self, obj, exe, mapfile):
        return [self.cc, "-static", obj, "-o", exe, f"-L{self.libc}", "-lm", f"-Wl,-Map={mapfile}"]

    def text_size(self, obj):
        out = run([self.size, "-A", obj]).stdout
        return sum(int(l.split()[1]) for l in out.splitlines() if l.startswith(".text"))

    def identity(self):
        rev = run(["git", "rev-parse", "HEAD"], cwd=ROOT).stdout.strip()
        dirty = run(["git", "status", "--porcelain"], cwd=ROOT).stdout.strip() != ""
        cpu = "?"
        try:
            for l in Path("/proc/cpuinfo").read_text().splitlines():
                if l.startswith("model name"):
                    cpu = l.split(":", 1)[1].strip()
                    break
        except OSError:
            pass
        return {
            "revision": rev,
            "dirty": dirty,
            "host": f"{platform.system()} {platform.release()} {platform.machine()}",
            "host_cpu": cpu,
            "host_cpus": os.cpu_count(),
            "loadavg": Path("/proc/loadavg").read_text().split()[:3],
            "gcc": first_line([self.cc, "--version"]),
            "clang": first_line([self.clang, "--version"]),
            "rustc": first_line(["rustc", "--version"]),
            "qemu": first_line(["qemu-aarch64", "--version"]) if not self.native else None,
            "libc_static": self.libc,
            "reference_flags": "-ffp-contract=off, NIX_HARDENING_ENABLE=''",
            "clang_flags": self.clang_flags,
        }


def programs(only):
    names = sorted(p.stem for p in PROGRAMS.glob("*.c"))
    if set(names) != set(SIZES):
        die(f"programs/ and SIZES disagree: {sorted(set(names) ^ set(SIZES))}")
    chosen = [n for n in names if not only or any(o in n for o in only)]
    if not chosen:
        die(f"--only {' '.join(only)} matches no program (programs: {' '.join(names)})")
    return chosen


def save(out, name, data):
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{name}.json").write_text(json.dumps(data, indent=1) + "\n")


def load(out, name):
    p = out / f"{name}.json"
    return json.loads(p.read_text()) if p.exists() else None


# ---------------------------------------------------------------------------------------------
# build: compile, time the compilers, size the code, link


def cmd_build(args, tools):
    tools.build_fcc()
    out = args.out
    objs, bins = out / "obj", out / "bin"
    objs.mkdir(parents=True, exist_ok=True)
    bins.mkdir(parents=True, exist_ok=True)
    env = tools.env
    result = {"identity": tools.identity(), "reps": args.reps, "programs": {}}

    # fcc's fixed cost: an empty file through the frontend, and the system include probe
    # (`cc -E -Wp,-v`) it runs on every invocation.
    empty = out / "empty.c"
    empty.write_text("")
    result["fcc_startup"] = timed([tools.fcc, empty, "--emit", "hfir", "-o", "/dev/null"], env, args.reps)
    result["include_probe"] = timed([tools.cc, "-E", "-Wp,-v", "-x", "c", "/dev/null"], env, args.reps)

    for name in programs(args.only):
        src = PROGRAMS / f"{name}.c"
        entry = {"configs": {}, "fcc_phases": {}}
        for config in CONFIGS:
            obj = objs / f"{name}.{config}.o"
            exe = bins / f"{name}.{config}"
            t = timed(tools.compile_cmd(config, src, obj), env, args.reps)
            run(tools.link_cmd(obj, exe, objs / f"{name}.{config}.map"), env=env)
            entry["configs"][config] = {"compile": t, "text_bytes": tools.text_size(obj),
                                        "binary": fingerprint(exe)}
        # Where fcc's time goes: each stage is the one before plus one more step.
        for opt in ([], ["-O"]):
            key = "O" if opt else "O0"
            phases = {}
            for stage, emit in (("hfir", ["--emit", "hfir", "-o", "/dev/null"]),
                                ("mfir", ["--emit", "mfir", "-o", "/dev/null"]),
                                ("asm", ["--emit", "asm", "-o", "/dev/null"]),
                                ("obj", ["-o", str(out / "phase.o")])):
                phases[stage] = timed([tools.fcc, src, *opt, *emit], env, args.reps)["min"]
            entry["fcc_phases"][key] = phases
        # FIR's own steps on the same module, in process (`fir` CLI): lower, -O, backend.
        hfir = out / "phase.hfir"
        run([tools.fcc, src, "--emit", "hfir", "-o", hfir], env=env)
        mfir, mfir_o = out / "phase.mfir", out / "phase.mfir-O"
        mfir.write_text(run([tools.fir, "lower", hfir]).stdout)
        mfir_o.write_text(run([tools.fir, "opt", mfir, "-O"]).stdout)
        entry["fir_steps"] = {
            "lower": timed([tools.fir, "lower", hfir], env, args.reps)["min"],
            "opt": timed([tools.fir, "opt", mfir, "-O"], env, args.reps)["min"],
            "compile": timed([tools.fir, "compile", mfir_o, "--emit", "asm", "-o", "/dev/null"], env, args.reps)["min"],
            "hfir_lines": len(hfir.read_text().splitlines()),
            "mfir_lines": len(mfir.read_text().splitlines()),
        }
        result["programs"][name] = entry
        print(f"built {name}", file=sys.stderr)

    # The existing differential corpus, as a larger and more varied compile-time input.
    corpus = sorted((ROOT / "frontends/c/tests").glob("*.c"))
    inc = ["-I", str(ROOT / "frontends/c/tests/runtime")]
    totals = {}
    for config in CONFIGS:
        total = 0.0
        for src in corpus:
            cmd = tools.compile_cmd(config, src, out / "corpus.o")
            cmd = cmd[:2] + inc + cmd[2:] if config.startswith("fcc") else cmd[:1] + inc + cmd[1:]
            total += timed(cmd, env, max(1, args.reps // 2))["min"]
        totals[config] = total
    result["corpus_compile"] = {"programs": len(corpus), "seconds": totals}
    result["loadavg_end"] = Path("/proc/loadavg").read_text().split()[:3]
    save(out, "build", result)


# ---------------------------------------------------------------------------------------------
# count: behavior at the small size and executed instructions, under qemu-user (exact counts)


def plugin(tools, out):
    """Builds the instruction-counting QEMU plugin against this qemu's header."""
    qemu = shutil.which("qemu-aarch64")
    if not qemu:
        die("qemu-aarch64 is not on PATH (the dev shell has it off AArch64)")
    include = Path(qemu).resolve().parent.parent / "include"
    so = out / "insn_count.so"
    glib = shlex.split(os.environ.get("FCC_BENCH_GLIB_CFLAGS", ""))
    if not glib:
        die("FCC_BENCH_GLIB_CFLAGS must give glib's include flags (the dev shell sets it)")
    run(["cc", "-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror", *glib, f"-I{include}",
         BENCH / "insn_count.c", "-o", so], env=tools.env)
    return so


def program_ranges(mapfile, obj):
    """The address ranges of obj's code in the linked binary, from the linker map."""
    ranges, pending = [], None
    lines = mapfile.read_text().splitlines()
    for line in lines:
        m = re.match(r"^ (\.text[\w.$]*)\s+0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+(\S+)$", line)
        if m:
            sec, addr, size, path = m.groups()
        elif pending:
            m = re.match(r"^\s+0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+(\S+)$", line)
            pending, prev = None, pending
            if not m:
                continue
            sec, (addr, size, path) = prev, m.groups()
        else:
            m = re.match(r"^ (\.text[\w.$]*)$", line)
            if m:
                pending = m.group(1)
            continue
        if Path(path).resolve() == Path(obj).resolve() and int(size, 16):
            ranges.append((int(addr, 16), int(addr, 16) + int(size, 16)))
    if not ranges:
        die(f"no code of {obj} in {mapfile}")
    return ranges


def disassemble(tools, exe, ranges):
    """addr -> (mnemonic, operands), and function symbols, for the given ranges."""
    insns = {}
    for lo, hi in ranges:
        out = run([tools.objdump, "-d", "--no-show-raw-insn", f"--start-address={lo:#x}",
                   f"--stop-address={hi:#x}", exe]).stdout
        for line in out.splitlines():
            m = re.match(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
            if m:
                ops = m.group(3).split("//")[0].strip()
                insns[int(m.group(1), 16)] = (m.group(2), ops)
    syms = []
    for line in run([tools.nm, "-n", "--defined-only", exe]).stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] in "TtWw":
            syms.append((int(parts[0], 16), parts[2]))
    return insns, syms


LOAD = re.compile(r"^ld[a-z0-9]*$")
STORE = re.compile(r"^st[a-z0-9]*$")
BRANCH = re.compile(r"^(b|b\..*|bc\..*|cbz|cbnz|tbz|tbnz|br|ret)$")
CALL = re.compile(r"^(bl|blr)$")
MOVE = re.compile(r"^(mov|movz|movk|movn|fmov)$")
MULDIV = re.compile(r"^(mul|madd|msub|smull|umull|smulh|umulh|sdiv|udiv|mneg|smaddl|umaddl)$")
COMPARE = re.compile(r"^(cmp|cmn|tst|ccmp|ccmn|fcmp|fcmpe|cset|csetm|csel|csinc|csinv|csneg|cinc|cneg)$")
FP = re.compile(r"^f[a-z0-9]+$|^(scvtf|ucvtf)$")


def classify(mnemonic, ops):
    if LOAD.match(mnemonic) and "[" in ops:
        return "load"
    if STORE.match(mnemonic) and "[" in ops:
        return "store"
    for name, pat in (("call", CALL), ("branch", BRANCH), ("move", MOVE), ("muldiv", MULDIV),
                      ("compare", COMPARE), ("fp", FP)):
        if pat.match(mnemonic):
            return name
    return "alu"


def analyze(tools, exe, mapfile, obj, trace):
    """Executed instructions in all and in the program's own code (by class, mnemonic, and
    function), and the program code's memory accesses to the stack and elsewhere."""
    import bisect

    ranges = program_ranges(mapfile, obj)
    insns, syms = disassemble(tools, exe, ranges)
    inside = lambda a: any(lo <= a < hi for lo, hi in ranges)
    starts = [s[0] for s in syms]
    total = program = 0
    mix, mnem, funcs = {}, {}, {}
    mem = {"stack_loads": 0, "stack_stores": 0, "other_loads": 0, "other_stores": 0}
    sp0 = lo = hi = deep = None
    for line in trace.read_text().splitlines():
        kind, *f = line.split()
        if kind == "S":
            sp0, lo, hi, deep = int(f[0], 16), int(f[1], 16), int(f[2], 16), int(f[3])
            continue
        if kind == "M":
            a = int(f[0], 16)
            if inside(a):
                for key, v in zip(mem, f[1:]):
                    mem[key] += int(v)
            continue
        if kind != "B":
            continue
        vaddr, n, count = int(f[0], 16), int(f[1]), int(f[2])
        total += n * count
        for i in range(n):
            a = vaddr + 4 * i
            if not inside(a):
                continue
            program += count
            mn, ops = insns.get(a, ("?", ""))
            cls = classify(mn, ops)
            mix[cls] = mix.get(cls, 0) + count
            mnem[mn] = mnem.get(mn, 0) + count
            k = bisect.bisect_right(starts, a) - 1
            fn = syms[k][1] if k >= 0 else "?"
            funcs[fn] = funcs.get(fn, 0) + count
    if not sp0:
        die(f"{trace}: the plugin never read the stack pointer")
    top = lambda d, k: dict(sorted(d.items(), key=lambda kv: -kv[1])[:k])
    return {
        "window": (lo, hi),
        "deep_accesses": deep,
        "total": total,
        "program": program,
        "library": total - program,
        "mix": mix,
        "memory_accesses": mem,
        "mnemonics": top(mnem, 25),
        "functions": top(funcs, 10),
    }


# The stack window of the plugin (insn_count.c): QEMU gets an 8 MiB stack (-s) and an empty
# environment, so the stack mapping is [top - 8 MiB, top) with the initial sp within a few KiB of
# top; the window [sp0 - 7 MiB, sp0 + 64 KiB) then lies inside it, and accesses in the 512 KiB
# below the window (still stack) are "deep": stack the window would miss.
QEMU_STACK = "8M"
STACK_BELOW, STACK_ABOVE, STACK_DEEP = 7 << 20, 64 << 10, 512 << 10


def fingerprint(path):
    import hashlib

    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def mappings(strace):
    """The guest memory qemu-user's -strace shows the program mapping: (start, end) ranges from
    successful mmap/mremap calls, and the brk heap."""
    ranges, brks = [], []
    for line in strace.splitlines():
        m = re.search(r"\bmmap\(\w+,(\d+),.*\) = (0x[0-9a-f]+)$", line)
        if m:
            ranges.append((int(m.group(2), 16), int(m.group(2), 16) + int(m.group(1))))
            continue
        m = re.search(r"\bmremap\(0x[0-9a-f]+,\d+,(\d+),.*\) = (0x[0-9a-f]+)$", line)
        if m:
            ranges.append((int(m.group(2), 16), int(m.group(2), 16) + int(m.group(1))))
            continue
        m = re.search(r"\bbrk\(.*\) = (0x[0-9a-f]+)$", line)
        if m:
            brks.append(int(m.group(1), 16))
    if brks:
        ranges.append((min(brks), max(brks)))
    return ranges


def cmd_count(args, tools):
    out = args.out
    build = load(out, "build")
    if not build:
        die("run `cbench.py build` first")
    so = None if tools.native else plugin(tools, out)
    result = {"identity": tools.identity(), "emulated": not tools.native, "programs": {}}
    traces = out / "traces"
    traces.mkdir(exist_ok=True)
    failures = []
    for name in programs(args.only):
        arg = str(SIZES[name][0])
        entry = {"arg": arg, "configs": {}}
        outputs = {}
        for config in CONFIGS:
            exe = out / "bin" / f"{name}.{config}"
            obj = out / "obj" / f"{name}.{config}.o"
            trace = traces / f"{name}.{config}.trace"
            if tools.native:  # natively there is no plugin: behavior only
                cmd = [exe, arg]
            else:
                plug = f"{so},outfile={trace},below={STACK_BELOW},above={STACK_ABOVE},deep={STACK_DEEP}"
                cmd = ["env", "-i", shutil.which("qemu-aarch64"), "-s", QEMU_STACK, "-strace",
                       "-plugin", plug, exe, arg]
            p = run(cmd, check=False, timeout=3600)
            outputs[config] = (p.stdout, p.returncode)
            c = {"exit": p.returncode, "stdout": p.stdout, "binary": fingerprint(exe)}
            if not tools.native:
                c.update(analyze(tools, exe, out / "obj" / f"{name}.{config}.map", obj, trace))
                lo, hi = c.pop("window")
                meets = [f"{a:#x}-{b:#x}" for a, b in mappings(p.stderr) if a < hi and lo < b]
                if meets:
                    failures.append(f"{name} {config}: mappings {meets} meet the stack window "
                                    f"{lo:#x}-{hi:#x}, so heap would count as stack")
                if c["deep_accesses"]:
                    failures.append(f"{name} {config}: {c['deep_accesses']} stack accesses below "
                                    "the window (more than 7 MiB of stack)")
            entry["configs"][config] = c
        ref = outputs[REFERENCE]
        if ref[1] != 0:
            failures.append(f"{name}: the reference {REFERENCE} exited with {ref[1]}")
        for config in CONFIGS:
            entry["configs"][config]["matches_reference"] = ref[1] == 0 and outputs[config] == ref
        bad = [c for c in CONFIGS if not entry["configs"][c]["matches_reference"]]
        if bad:
            failures.append(f"{name}: output or exit code differs from {REFERENCE}'s: {bad}")
        print(f"counted {name}" + (f": DIFFERS from {REFERENCE}: {bad}" if bad else ""), file=sys.stderr)
        result["programs"][name] = entry
    result["failures"] = failures
    save(out, "count", result)
    if failures:
        die("count failed:\n  " + "\n  ".join(failures))


# ---------------------------------------------------------------------------------------------
# scaling: fcc's compile time against input size


def synth(n_funcs, stmts_per_func):
    """A C file of n_funcs functions of about stmts_per_func statements each: loops, branches,
    arrays, calls, a switch."""
    lines = ["int sink[64];"]
    for f in range(n_funcs):
        lines.append(f"int f{f}(int a, int b) {{")
        lines.append("  int x = a, y = b, t[8] = {0};")
        for s in range(stmts_per_func):
            k = (f * 31 + s * 17) % 6
            if k == 0:
                lines.append(f"  for (int i = 0; i < 8; i++) t[i] += x * {s + 1} + i;")
            elif k == 1:
                lines.append(f"  if (x > y) x -= y + {s}; else y -= x - {s};")
            elif k == 2:
                lines.append(f"  switch ((x + {s}) & 3) {{ case 0: y++; break; case 1: x ^= y; break; default: x += {s}; }}")
            elif k == 3:
                lines.append(f"  sink[{s % 64}] = x + y + t[{s % 8}];")
            elif k == 4 and f > 0:
                lines.append(f"  x += f{(f * 7 + s) % f}(y, {s});")
            else:
                lines.append(f"  y = (y << 1) ^ (x >> 2) ^ {s};")
        lines.append("  return x + y + t[0] + t[7];")
        lines.append("}")
    return "\n".join(lines) + "\n"


def cmd_scaling(args, tools):
    out = args.out / "scaling"
    out.mkdir(parents=True, exist_ok=True)
    env = tools.env
    result = {"identity": tools.identity(), "many_functions": [], "one_function": []}
    for kind, shapes in (("many_functions", [(n, 10) for n in SCALING_SIZES]),
                         ("one_function", [(1, n) for n in SCALING_SIZES])):
        for funcs, stmts in shapes:
            src = out / f"{kind}-{funcs}x{stmts}.c"
            src.write_text(synth(funcs, stmts))
            row = {"functions": funcs, "statements": stmts, "lines": len(src.read_text().splitlines())}
            for config in ("fcc", "fcc-O", "gcc-O0", "gcc-O2", "clang-O0"):
                row[config] = timed(tools.compile_cmd(config, src, out / "s.o"), env, args.reps)["min"]
            hfir = out / "s.hfir"
            run([tools.fcc, src, "--emit", "hfir", "-o", hfir], env=env)
            row["fcc_hfir"] = timed([tools.fcc, src, "--emit", "hfir", "-o", "/dev/null"], env, args.reps)["min"]
            row["fcc_asm"] = timed([tools.fcc, src, "--emit", "asm", "-o", "/dev/null"], env, args.reps)["min"]
            row["fcc_O_asm"] = timed([tools.fcc, src, "-O", "--emit", "asm", "-o", "/dev/null"], env, args.reps)["min"]
            row["hfir_lines"] = len(hfir.read_text().splitlines())
            result[kind].append(row)
            print(f"scaling {kind} {funcs}x{stmts}: fcc-O {row['fcc-O']:.3f}s gcc-O2 {row['gcc-O2']:.3f}s",
                  file=sys.stderr)
    result["loadavg_end"] = Path("/proc/loadavg").read_text().split()[:3]
    save(args.out, "scaling", result)


# ---------------------------------------------------------------------------------------------
# time: native wall time, on AArch64 hardware only


RUN_SH = r"""#!/bin/sh
# Generated by cbench.py: times every benchmark binary here with benchrun, which refuses to run
# unless the CPU is AArch64 hardware. Usage: ./run.sh ROUNDS
set -eu
cd "$(dirname "$0")"
ROUNDS=${1:-5}
mkdir -p expected results
{
  echo "uname: $(uname -a)"
  echo "nproc: $(nproc 2>/dev/null || echo ?)"
  grep -m1 -i "MemTotal" /proc/meminfo || true
  grep -E "^(CPU implementer|CPU part|CPU variant|CPU revision|Features)" /proc/cpuinfo | sort | uniq -c
} > results/env.txt
: > results/times.jsonl
for p in $PROGRAMS; do
  eval "arg=\$ARG_$p"
  ./bin/$p.REFERENCE "$arg" > expected/$p.out
done
# A warmup round, then ROUNDS rounds, each running every program under every configuration once,
# so drift (thermal, other load) spreads across configurations instead of biasing one.
round=0
while [ $round -le "$ROUNDS" ]; do
  for p in $PROGRAMS; do
    eval "arg=\$ARG_$p"
    for c in $CONFIGS; do
      json=$(./benchrun 1 0 expected/$p.out ./bin/$p.$c "$arg")
      echo "{\"round\": $round, \"program\": \"$p\", \"config\": \"$c\", \"result\": $json}" >> results/times.jsonl
    done
  done
  echo "round $round done" >&2
  round=$((round + 1))
done
"""


def make_bundle(args, tools, names):
    bundle = Path(tempfile.mkdtemp(prefix="cbench-bundle-", dir=args.out))
    (bundle / "bin").mkdir()
    for name in names:
        for config in CONFIGS:
            shutil.copy2(args.out / "bin" / f"{name}.{config}", bundle / "bin")
    run([tools.cc, "-static", "-O2", "-Wall", "-Wextra", "-Werror", BENCH / "benchrun.c", "-o",
         bundle / "benchrun", f"-L{tools.libc}"], env=tools.env)
    header = f"PROGRAMS='{' '.join(names)}'\nCONFIGS='{' '.join(CONFIGS)}'\n"
    header += "".join(f"ARG_{n}={SIZES[n][1]}\n" for n in names)
    script = RUN_SH.replace("set -eu\n", "set -eu\n" + header, 1).replace("REFERENCE", REFERENCE)
    (bundle / "run.sh").write_text(script)
    (bundle / "run.sh").chmod(0o755)
    return bundle


def cmd_time(args, tools):
    names = programs(args.only)
    if not load(args.out, "build"):
        die("run `cbench.py build` first")
    if not args.ssh and not tools.native:
        die("refusing to time under emulation: run on AArch64 Linux, or pass --ssh HOST "
            "(with --docker IMAGE for a Linux container on, say, an Apple silicon Mac)")
    bundle = make_bundle(args, tools, names)
    info = {"rounds": args.rounds, "sizes": {n: SIZES[n][1] for n in names}}
    if not args.ssh:
        run([bundle / "run.sh", str(args.rounds)], capture=False)
        info["where"] = "local"
    else:
        remote = run(["ssh", args.ssh, "mktemp -d /tmp/cbench.XXXXXX"]).stdout.strip()
        try:
            run(["scp", "-q", "-r", f"{bundle}/.", f"{args.ssh}:{remote}/"])
            if args.docker:
                docker = args.docker_bin
                digest = run(["ssh", args.ssh, f"{docker} pull -q {shlex.quote(args.docker)} >/dev/null && "
                              f"{docker} image inspect --format '{{{{index .RepoDigests 0}}}}' {shlex.quote(args.docker)}"]).stdout.strip()
                server = run(["ssh", args.ssh, f"{docker} version --format '{{{{.Server.Version}}}} {{{{.Server.Os}}}}/{{{{.Server.Arch}}}}'"]).stdout.strip()
                inner = f"{docker} run --rm --platform linux/arm64 -v {remote}:/b {shlex.quote(args.docker)} /b/run.sh {args.rounds}"
                info.update(where=f"ssh {args.ssh}, docker", image=digest, docker_server=server)
            else:
                inner = f"{remote}/run.sh {args.rounds}"
                info["where"] = f"ssh {args.ssh}"
            info["remote_host"] = run(["ssh", args.ssh, "uname -a; (sysctl -n machdep.cpu.brand_string hw.ncpu hw.memsize 2>/dev/null || true)"]).stdout.strip()
            run(["ssh", args.ssh, inner], capture=False)
            run(["scp", "-q", "-r", f"{args.ssh}:{remote}/results/.", f"{bundle}/results/"])
        finally:
            run(["ssh", args.ssh, f"rm -rf {shlex.quote(remote)}"], check=False)
    rows = [json.loads(l) for l in (bundle / "results/times.jsonl").read_text().splitlines() if l.strip()]
    info["env"] = (bundle / "results/env.txt").read_text()
    times = {}
    for r in rows:
        if r["round"] == 0:  # warmup
            continue
        t = times.setdefault(r["program"], {}).setdefault(r["config"], {"wall": [], "user": [], "maxrss_kib": 0})
        t["wall"] += r["result"]["wall"]
        t["user"] += r["result"]["user"]
        t["maxrss_kib"] = max(t["maxrss_kib"], r["result"]["maxrss_kib"])
        info["cpu_implementer"] = r["result"]["cpu_implementer"]
        info["cpu_part"] = r["result"]["cpu_part"]
    # Every program under every configuration, once per round: anything less is not saved.
    missing = [f"{n} {c}: {len(times.get(n, {}).get(c, {}).get('wall', []))} of {args.rounds} runs"
               for n in names for c in CONFIGS
               if len(times.get(n, {}).get(c, {}).get("wall", [])) != args.rounds]
    if missing:
        die(f"incomplete timing in {bundle}:\n  " + "\n  ".join(missing))
    for n in names:
        for c in CONFIGS:
            t = times[n][c]
            t["median"] = statistics.median(t["wall"])
            t["min"] = min(t["wall"])
            t["max"] = max(t["wall"])
            t["binary"] = fingerprint(bundle / "bin" / f"{n}.{c}")
    info["programs"] = times
    info["identity"] = tools.identity()
    save(args.out, "time", info)
    shutil.rmtree(bundle)


# ---------------------------------------------------------------------------------------------
# report


def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    if not xs:
        return float("nan")
    import math

    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def table(header, rows):
    out = ["| " + " | ".join(header) + " |", "|" + "|".join("---" if i == 0 else "---:" for i in range(len(header))) + "|"]
    out += ["| " + " | ".join(str(c) for c in r) + " |" for r in rows]
    return "\n".join(out)


def ratio_table(metric_of, names, fmt, ref=REFERENCE):
    rows, ratios = [], {c: [] for c in CONFIGS}
    for n in names:
        row = [n]
        for c in CONFIGS:
            v, r = metric_of(n, c), metric_of(n, ref)
            row.append(fmt(v))
            if v and r:
                ratios[c].append(v / r)
        rows.append(row)
    rows.append([f"**geomean vs {ref}**"] + [f"**{geomean(ratios[c]):.2f}×**" for c in CONFIGS])
    return table(["program"] + CONFIGS, rows)


def cmd_report(args, tools=None):
    out = args.out
    build, count, timing, scaling = (load(out, n) for n in ("build", "count", "time", "scaling"))
    if not build:
        die("nothing measured yet")
    names = sorted(build["programs"])
    # Every count and time must be of the binaries this build made: a stale step is refused, not
    # mixed in.
    for step, data in (("count", count), ("time", timing)):
        if not data:
            continue
        stale = []
        for n in names:
            for c in CONFIGS:
                cell = data["programs"].get(n, {})
                cell = cell.get("configs", cell).get(c)
                if cell is None:
                    stale.append(f"{n} {c}: not measured")
                elif not cell.get("binary"):
                    stale.append(f"{n} {c}: no fingerprint (measured by an older harness)")
                elif cell["binary"] != build["programs"][n]["configs"][c]["binary"]:
                    stale.append(f"{n} {c}: another binary")
        if stale:
            die(f"{step}.json doesn't match build.json (rerun `cbench.py {step}`):\n  "
                + "\n  ".join(stale[:10]))
    if count and count.get("failures"):
        die("count.json records failures:\n  " + "\n  ".join(count["failures"]))
    md = ["# fcc C baseline: measured results", ""]
    ident = build["identity"]
    md += [f"Revision `{ident['revision'][:12]}`{' (with uncommitted changes)' if ident['dirty'] else ''}; "
           f"host {ident['host']}, {ident['host_cpu']} ({ident['host_cpus']} CPUs). "
           f"{ident['gcc']}; {ident['clang']}; {ident['qemu'] or 'native'}.", ""]
    if count:
        md += ["## Behavior (small size, " + ("qemu-user" if count["emulated"] else "native") + f"): output and exit code equal to {REFERENCE}'s", ""]
        rows = [[n] + ["✓" if count["programs"][n]["configs"][c]["matches_reference"] else "✗" for c in CONFIGS]
                for n in names if n in count["programs"]]
        md += [table(["program"] + CONFIGS, rows), ""]
    if timing:
        md += [f"## Native wall time (median of {timing['rounds']} interleaved rounds, seconds)", "",
               f"Where: {timing['where']}; CPU implementer {timing.get('cpu_implementer', 0):#x}, "
               f"part {timing.get('cpu_part', 0):#x}"
               + (f"; Docker server {timing['docker_server']}, image `{timing['image']}`" if timing.get("image") else "")
               + ".", ""]
        if timing.get("remote_host"):
            md += ["The SSH host: " + "; ".join(timing["remote_host"].splitlines()) + ".", ""]
        md += ["The machine as Linux saw it:", "", "```", timing["env"].strip(), "```", ""]
        md += [ratio_table(lambda n, c: timing["programs"].get(n, {}).get(c, {}).get("median"), names,
                           lambda v: f"{v:.3f}" if v else "—"), ""]
        spread = []
        for n in names:
            for c in CONFIGS:
                t = timing["programs"].get(n, {}).get(c)
                if t:
                    spread.append((t["max"] - t["min"]) / t["median"])
        if spread:
            md += [f"Spread (max − min) / median across rounds: median {statistics.median(spread) * 100:.1f}%, "
                   f"worst {max(spread) * 100:.1f}%.", ""]
            noisy = [f"{n} {c} ({', '.join(f'{w:.3f}' for w in t['wall'])})"
                     for n in names for c, t in timing["programs"].get(n, {}).items()
                     if (t["max"] - t["min"]) / t["median"] > 0.15]
            if noisy:
                md += ["Cells whose runs spread by more than 15% (all runs, seconds): " + "; ".join(noisy) + ".", ""]
    if count and count["emulated"]:
        md += [f"## Executed instructions in the program's own code (small size, millions; exact, counted under qemu)", ""]
        md += [ratio_table(lambda n, c: count["programs"][n]["configs"][c].get("program", 0) / 1e6, names,
                           lambda v: f"{v:.1f}"), ""]
        md += ["## Executed instructions including libc (millions)", ""]
        md += [ratio_table(lambda n, c: count["programs"][n]["configs"][c].get("total", 0) / 1e6, names,
                           lambda v: f"{v:.1f}"), ""]
        md += ["## Instruction mix in the program's own code (all programs, share of executed instructions)", ""]
        classes = ["load", "store", "move", "alu", "compare", "branch", "call", "muldiv", "fp"]
        rows = []
        for c in CONFIGS:
            agg, acc, tot = {}, {}, 0
            for n in names:
                e = count["programs"][n]["configs"][c]
                tot += e["program"]
                for k, v in e["mix"].items():
                    agg[k] = agg.get(k, 0) + v
                for k, v in e["memory_accesses"].items():
                    acc[k] = acc.get(k, 0) + v
            accesses = sum(acc.values())
            stack = acc["stack_loads"] + acc["stack_stores"]
            rows.append([c, f"{tot / 1e6:.0f}M"] + [f"{100 * agg.get(k, 0) / tot:.1f}%" for k in classes]
                        + [f"{accesses / 1e6:.0f}M", f"{100 * stack / max(accesses, 1):.0f}%"])
        md += [table(["config", "executed"] + classes + ["memory accesses", "to the stack"], rows), "",
               "Memory accesses are counted by address (an `ldp` may be two); an access is to the stack if its "
               "address is in [sp - 7 MiB, sp + 64 KiB) of the initial stack pointer sp, inside QEMU's 8 MiB "
               "stack; `count` checks that no mapping meets that window.", ""]
    md += ["## Code size (.text bytes of the program's object)", ""]
    md += [ratio_table(lambda n, c: build["programs"][n]["configs"][c]["text_bytes"], names, str), ""]
    md += [f"## Compile time to an object file (host, minimum of {build['reps']} runs, ms)", ""]
    md += [ratio_table(lambda n, c: build["programs"][n]["configs"][c]["compile"]["min"] * 1e3, names,
                       lambda v: f"{v:.0f}"), ""]
    cc = build["corpus_compile"]
    md += [f"The {cc['programs']} programs of `frontends/c/tests`, one compile each, total seconds: "
           + ", ".join(f"{c} {cc['seconds'][c]:.2f}" for c in CONFIGS) + ".", ""]
    md += ["### Where fcc's time goes (ms, minimum of the runs; each stage includes the ones before)", "",
           f"Startup (an empty file to HFIR): {build['fcc_startup']['min'] * 1e3:.0f} ms, of which the "
           f"system include probe (`cc -E -Wp,-v`) is {build['include_probe']['min'] * 1e3:.0f} ms.", ""]
    rows = []
    for n in names:
        p = build["programs"][n]["fcc_phases"]
        f = build["programs"][n]["fir_steps"]
        rows.append([n, f"{p['O0']['hfir'] * 1e3:.0f}", f"{p['O']['mfir'] * 1e3:.0f}", f"{p['O']['asm'] * 1e3:.0f}",
                     f"{p['O']['obj'] * 1e3:.0f}", f"{f['lower'] * 1e3:.1f}", f"{f['opt'] * 1e3:.1f}",
                     f"{f['compile'] * 1e3:.1f}", f["hfir_lines"]])
    md += [table(["program", "→HFIR", "→MFIR -O", "→asm -O", "→.o -O", "fir lower", "fir opt -O", "fir compile",
                  "HFIR lines"], rows), "",
           "The `fir` columns are the same module through the `fir` CLI, each step a separate process.", ""]
    if scaling:
        md += ["## Compile-time scaling (seconds, minimum of the runs)", ""]
        for kind in ("many_functions", "one_function"):
            rows = [[r["functions"], r["statements"], r["lines"], r["hfir_lines"], f"{r['fcc_hfir']:.3f}",
                     f"{r['fcc_asm']:.3f}", f"{r['fcc_O_asm']:.3f}", f"{r['fcc-O']:.3f}", f"{r['gcc-O0']:.3f}",
                     f"{r['gcc-O2']:.3f}", f"{r['clang-O0']:.3f}"] for r in scaling[kind]]
            md += [f"**{kind.replace('_', ' ')}**", "",
                   table(["funcs", "stmts each", "C lines", "HFIR lines", "fcc →HFIR", "fcc →asm", "fcc -O →asm",
                          "fcc -O →.o", "gcc -O0", "gcc -O2", "clang -O0"], rows), ""]
    (out / "report.md").write_text("\n".join(md))
    print(out / "report.md")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("step", choices=["build", "count", "scaling", "time", "report", "all"])
    ap.add_argument("--out", type=Path, default=ROOT / "target/cbench")
    ap.add_argument("--only", nargs="*", default=[], help="programs whose names contain one of these")
    ap.add_argument("--reps", type=int, default=5, help="compile-time repetitions (minimum)")
    ap.add_argument("--rounds", type=int, default=7, help="native timing rounds after one warmup")
    ap.add_argument("--ssh", help="time on this AArch64 host (or the Docker host with --docker)")
    ap.add_argument("--docker", help="run the timing in this image (an arm64 Linux image) on --ssh's host")
    ap.add_argument("--docker-bin", default="docker", help="docker's path on the --ssh host")
    args = ap.parse_args()
    if args.reps < 1 or args.rounds < 1:
        die("--reps and --rounds must be at least 1")
    args.out = args.out.resolve()
    tools = Tools()
    steps = {"build": cmd_build, "count": cmd_count, "scaling": cmd_scaling, "time": cmd_time, "report": cmd_report}
    if args.step == "all":
        for s in ("build", "count", "scaling"):
            steps[s](args, tools)
        if args.ssh or tools.native:
            cmd_time(args, tools)
        else:
            print("cbench: not timing (no native AArch64: pass --ssh HOST)", file=sys.stderr)
        cmd_report(args, tools)
    else:
        steps[args.step](args, tools)


if __name__ == "__main__":
    main()
