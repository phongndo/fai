// fcc: a C compiler on FIR. Clang parses and type-checks the C (preprocessor and headers
// included) for AArch64 Linux, or x86-64 Linux with `--target x86_64`; the AST is lowered to HFIR
// through FIR's C API (Lower.cpp), which verifies it and compiles it to the target's assembly; the
// system's C compiler for the target assembles and links it, as `fir compile` does.
//
//   fcc FILE.c [-O [--check-dce FIR-REF] | --passes P,... [--experimental]] [-o OUT]
//          [--emit hfir|mfir|asm] [--target aarch64|x86_64] [INPUT...] [-I DIR] [-D NAME[=V]]
//          [-l LIB] [-L DIR] [-- CLANG-FLAG...]
//
// Without --emit, OUT (default a.out) is an executable, or an object file when it ends in `.o`
// (or assembly when it ends in `.s`); further INPUTs (objects, archives, C or assembly files)
// and -l/-L are passed to the linker. --emit prints HFIR (as lowered), MFIR (lowered, and
// optimized with -O or --passes), or assembly, to OUT or standard output. Flags after `--` go to
// Clang. --passes runs the named passes to a fixed point instead of -O's; experimental
// (unproved) ones, such as mem2reg, only with --experimental.
//
// --check-dce FIR-REF checks every step of dead code elimination in -O with the proved Lean
// checker (`fir-ref check-dce`, run by the library: FIR_CHECK_DCE), fails if it refuses one, and
// prints one summary line on stderr.
//
// The linker is $FIR_CC, or `cc` when the host is the target (its CPU, on Linux), else the
// target's cross compiler (`aarch64-unknown-linux-gnu-cc`, which the dev shell has on x86-64
// Linux, or `x86_64-unknown-linux-gnu-cc`). Its system include directories are given to Clang
// (after Clang's own headers), so <stdint.h> and friends are the target's.
//
// FIR_TIME=1 prints where the time went on stderr: fcc's own steps (the include probe, Clang,
// the lowering to HFIR, the external assembler and linker) and the library's phases, in one
// report (fir_time_record, fir_time_report).

#include "Lower.h"
#include "fir.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/xxhash.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <vector>

extern char **environ;

#ifndef FCC_RESOURCE_DIR
#define FCC_RESOURCE_DIR ""
#endif

namespace {

// One of fcc's steps, timed into the library's report when FIR_TIME is set (fir_time_record
// does nothing otherwise).
class Step {
public:
  explicit Step(const char *name) : name(name), start(std::chrono::steady_clock::now()) {}
  ~Step() { fir_time_record(name, seconds()); }
  Step(const Step &) = delete;
  Step &operator=(const Step &) = delete;
  double seconds() const {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  }

private:
  const char *name;
  std::chrono::steady_clock::time_point start;
};

const char *kUsage =
    "usage: fcc FILE.c [-O [--check-dce FIR-REF] | --passes P,... [--experimental]] [-o OUT]\n"
    "              [--emit hfir|mfir|asm] [--target aarch64|x86_64] [INPUT...] [-I DIR]\n"
    "              [-D NAME[=V]] [-l LIB] [-L DIR] [-- CLANG-FLAG...]\n";

struct Options {
  std::string file;
  std::string out;
  std::string emit;
  std::string checkDce;
  // FIR's name for the target: `aarch64` or `x86_64`.
  std::string target = "aarch64";
  bool optimize = false;
  // --passes: run these instead of -O's pipeline; `experimental` allows unproved ones.
  bool hasPasses = false;
  std::string passes;
  bool experimental = false;
  std::vector<std::string> clangArgs;
  std::vector<std::string> linkArgs;
};

bool parseArgs(int argc, char **argv, Options &o) {
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto value = [&](std::string &dst) {
      if (i + 1 >= argc)
        return false;
      dst = argv[++i];
      return true;
    };
    if (a == "--") {
      for (i++; i < argc; i++)
        o.clangArgs.push_back(argv[i]);
      break;
    }
    if (a == "-O") {
      o.optimize = true;
    } else if (a == "--passes") {
      if (!value(o.passes))
        return false;
      o.hasPasses = true;
    } else if (a == "--experimental") {
      o.experimental = true;
    } else if (a == "-o") {
      if (!value(o.out))
        return false;
    } else if (a == "--check-dce") {
      if (!value(o.checkDce) || o.checkDce.empty())
        return false;
    } else if (a == "--emit") {
      if (!value(o.emit))
        return false;
      if (o.emit != "hfir" && o.emit != "mfir" && o.emit != "asm")
        return false;
    } else if (a == "--target") {
      if (!value(o.target))
        return false;
      if (o.target != "aarch64" && o.target != "x86_64")
        return false;
    } else if (a == "-I" || a == "-D" || a == "-U") {
      std::string v;
      if (!value(v))
        return false;
      o.clangArgs.push_back(a + v);
    } else if (a.rfind("-I", 0) == 0 || a.rfind("-D", 0) == 0 || a.rfind("-U", 0) == 0 ||
               a.rfind("-std=", 0) == 0) {
      o.clangArgs.push_back(a);
    } else if (a == "-l" || a == "-L") {
      std::string v;
      if (!value(v))
        return false;
      o.linkArgs.push_back(a + v);
    } else if (a.rfind("-l", 0) == 0 || a.rfind("-L", 0) == 0) {
      o.linkArgs.push_back(a);
    } else if (a == "-h" || a == "--help") {
      return false;
    } else if (!a.empty() && a[0] == '-') {
      llvm::errs() << "fcc: unknown option '" << a << "'\n";
      return false;
    } else if (o.file.empty() && llvm::StringRef(a).ends_with(".c")) {
      o.file = a;
    } else {
      o.linkArgs.push_back(a);
    }
  }
  if (!o.checkDce.empty() && !o.optimize && !o.hasPasses) {
    llvm::errs()
        << "fcc: --check-dce checks the dead code elimination of -O or --passes; add one\n";
    return false;
  }
  return !o.file.empty();
}

bool x86(const Options &o) { return o.target == "x86_64"; }

// The target's name in messages, and Clang's triple for it.
const char *targetName(const Options &o) { return x86(o) ? "x86-64" : "AArch64"; }
const char *triple(const Options &o) {
  return x86(o) ? "x86_64-unknown-linux-gnu" : "aarch64-unknown-linux-gnu";
}

std::string linker(const Options &o) {
  if (const char *cc = std::getenv("FIR_CC"); cc && *cc)
    return cc;
  // The host's `cc` only when it makes binaries for the target: the same CPU, and Linux (fcc's
  // output is Linux ELF, which macOS's `cc` would hand to Apple's assembler).
#if defined(__linux__) && defined(__aarch64__)
  bool native = !x86(o);
#elif defined(__linux__) && defined(__x86_64__)
  bool native = x86(o);
#else
  bool native = false;
#endif
  if (native)
    return "cc";
  return std::string(triple(o)) + "-cc";
}

// What the target C compiler's include probe found: its system include directories, without its
// compiler-specific ones (Clang brings its own), and the directories it would search but left out
// because they don't exist (GCC's "ignoring nonexistent directory").
struct Probe {
  std::vector<std::string> dirs;
  std::vector<std::string> absent;
  bool complete = false; // the search list was printed in full
};

Probe runProbe(const std::string &cc) {
  Step step("fcc: include probe (cc -E -v)");
  Probe r;
  std::string cmd = cc + " -E -Wp,-v -x c /dev/null 2>&1";
  FILE *p = popen(cmd.c_str(), "r");
  if (!p)
    return r;
  char line[4096];
  bool in = false;
  while (fgets(line, sizeof line, p)) {
    llvm::StringRef l = llvm::StringRef(line).trim();
    if (l.consume_front("ignoring nonexistent directory \"") && l.consume_back("\"")) {
      r.absent.push_back(l.str());
    } else if (l.starts_with("#include <...>")) {
      in = true;
    } else if (l.starts_with("End of search list")) {
      in = false;
      r.complete = true;
    } else if (in && !l.contains("/lib/gcc/") && !l.contains("/lib/clang/") &&
               !l.contains("/include-fixed")) {
      r.dirs.push_back(l.str());
    }
  }
  pclose(p);
  return r;
}

// The probe's result is cached (in $FCC_CACHE_DIR, else the user's cache directory's fcc/; off
// with FCC_CACHE=0): it costs a process of the target C compiler (7 ms or more) on every
// compilation, and its answer rarely changes. An entry is used only when everything that could
// change the answer is as it was: the compiler named, the file it resolves to (its real path,
// size, and modification time), the target, and the whole environment except variables no
// compiler reads for its search path (a C compiler's search path depends on the environment:
// CPATH, GCC_EXEC_PREFIX, Nix's NIX_CFLAGS_COMPILE, ...); and when every directory found still
// exists and every one left out still doesn't. The key is stored in the entry and compared in
// full, so a hash collision can't select another entry. Anything unexpected falls back to probing.
const char *kProbeMagic = "fcc include probe 1";

// The cache key, or nothing when the compiler can't be resolved (then fcc probes, uncached).
std::optional<std::string> probeKey(const Options &o, const std::string &cc) {
  llvm::ErrorOr<std::string> prog = llvm::sys::findProgramByName(cc);
  if (!prog)
    return std::nullopt;
  llvm::SmallString<256> real;
  if (llvm::sys::fs::real_path(*prog, real))
    return std::nullopt;
  llvm::sys::fs::file_status st;
  if (llvm::sys::fs::status(real, st))
    return std::nullopt;
  std::string key;
  llvm::raw_string_ostream k(key);
  k << kProbeMagic << "\ntarget " << triple(o) << "\ncc " << cc << "\nfile " << real << " "
    << st.getSize() << " " << st.getLastModificationTime().time_since_epoch().count() << "\n";
  // Variables that say where a shell is, not what a compiler does.
  static const char *const ignored[] = {"PWD",      "OLDPWD", "SHLVL",   "_",
                                        "FIR_TIME", "TERM",   "COLUMNS", "LINES"};
  std::vector<llvm::StringRef> env;
  for (char **e = environ; *e; e++) {
    llvm::StringRef var(*e);
    llvm::StringRef name = var.split('=').first;
    if (std::find(std::begin(ignored), std::end(ignored), name) == std::end(ignored))
      env.push_back(var);
  }
  std::sort(env.begin(), env.end());
  for (llvm::StringRef var : env)
    k << "env " << var.size() << " " << var << "\n";
  return key;
}

std::optional<std::string> probeCacheDir() {
  const char *off = std::getenv("FCC_CACHE");
  if (off && llvm::StringRef(off) == "0")
    return std::nullopt;
  if (const char *d = std::getenv("FCC_CACHE_DIR"); d && *d)
    return std::string(d);
  llvm::SmallString<256> dir;
  if (!llvm::sys::path::cache_directory(dir))
    return std::nullopt;
  llvm::sys::path::append(dir, "fcc");
  return dir.str().str();
}

std::string probeCachePath(const std::string &dir, const std::string &key) {
  llvm::SmallString<256> p(dir);
  llvm::sys::path::append(p, "include-probe-" + llvm::utohexstr(llvm::xxh3_64bits(key)));
  return p.str().str();
}

// The cached probe for `key`, if there is one and it still holds.
std::optional<Probe> readProbe(const std::string &path, const std::string &key) {
  llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> buf = llvm::MemoryBuffer::getFile(path);
  if (!buf)
    return std::nullopt;
  llvm::StringRef text = (*buf)->getBuffer();
  // The key, length-prefixed (environment values may hold newlines), then one path per line.
  size_t n = 0;
  if (!text.consume_front("key ") || text.consumeInteger(10, n) || !text.consume_front("\n") ||
      text.size() < n || text.take_front(n) != key)
    return std::nullopt;
  text = text.drop_front(n);
  Probe r;
  while (!text.empty()) {
    auto [line, rest] = text.split('\n');
    text = rest;
    if (line == "end") {
      r.complete = true;
      break;
    }
    if (line.consume_front("dir ")) {
      if (!llvm::sys::fs::is_directory(line))
        return std::nullopt;
      r.dirs.push_back(line.str());
    } else if (line.consume_front("absent ")) {
      if (llvm::sys::fs::exists(line))
        return std::nullopt;
      r.absent.push_back(line.str());
    } else {
      return std::nullopt;
    }
  }
  if (!r.complete)
    return std::nullopt;
  return r;
}

// Store `r` for `key`, atomically (a temporary file renamed into place); failures are ignored.
void writeProbe(const std::string &dir, const std::string &path, const std::string &key,
                const Probe &r) {
  for (const std::vector<std::string> *v : {&r.dirs, &r.absent})
    for (const std::string &d : *v)
      if (d.find('\n') != std::string::npos)
        return;
  if (llvm::sys::fs::create_directories(dir))
    return;
  llvm::SmallString<256> tmp;
  int fd;
  if (llvm::sys::fs::createUniqueFile(path + ".%%%%%%%%.tmp", fd, tmp))
    return;
  {
    llvm::raw_fd_ostream os(fd, /*shouldClose=*/true);
    os << "key " << key.size() << "\n" << key;
    for (const std::string &d : r.dirs)
      os << "dir " << d << "\n";
    for (const std::string &d : r.absent)
      os << "absent " << d << "\n";
    os << "end\n";
    if (os.has_error()) {
      os.clear_error();
      llvm::sys::fs::remove(tmp);
      return;
    }
  }
  if (llvm::sys::fs::rename(tmp, path))
    llvm::sys::fs::remove(tmp);
}

// The target C compiler's system include directories (see Probe), from the cache when it holds.
std::vector<std::string> systemIncludes(const Options &o) {
  std::string cc = linker(o);
  std::optional<std::string> dir = probeCacheDir();
  std::optional<std::string> key = dir ? probeKey(o, cc) : std::nullopt;
  if (!key)
    return runProbe(cc).dirs;
  std::string path = probeCachePath(*dir, *key);
  {
    Step step("fcc: include probe (cached)");
    if (std::optional<Probe> cached = readProbe(path, *key))
      return cached->dirs;
  }
  Probe r = runProbe(cc);
  if (r.complete)
    writeProbe(*dir, path, *key, r);
  return r.dirs;
}

// How long the lowering to HFIR took, to tell it apart from Clang's own time.
double lowerSeconds = 0;

// The command line, which the names of a file's internal symbols hash with its path.
std::string commandLine;

class Consumer : public clang::ASTConsumer {
public:
  Consumer(FirModule *m, bool &lowered) : m(m), lowered(lowered) {}
  void HandleTranslationUnit(clang::ASTContext &ctx) override {
    if (ctx.getDiagnostics().hasErrorOccurred())
      return;
    Step step("fcc: lower AST to HFIR");
    lowered = fai::lowerTranslationUnit(ctx, m, commandLine);
    lowerSeconds = step.seconds();
  }

private:
  FirModule *m;
  bool &lowered;
};

class Action : public clang::ASTFrontendAction {
public:
  Action(FirModule *m, bool &lowered) : m(m), lowered(lowered) {}
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &,
                                                        llvm::StringRef) override {
    return std::make_unique<Consumer>(m, lowered);
  }

private:
  FirModule *m;
  bool &lowered;
};

class Factory : public clang::tooling::FrontendActionFactory {
public:
  Factory(FirModule *m, bool &lowered) : m(m), lowered(lowered) {}
  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<Action>(m, lowered);
  }

private:
  FirModule *m;
  bool &lowered;
};

bool writeOut(const std::string &path, const std::string &text) {
  if (path.empty() || path == "-") {
    llvm::outs() << text;
    return true;
  }
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec);
  if (ec) {
    llvm::errs() << "fcc: " << path << ": " << ec.message() << "\n";
    return false;
  }
  os << text;
  return true;
}

// A string FIR returned, freed when done.
struct FirString {
  char *s = nullptr;
  ~FirString() { fir_string_free(s); }
  std::string str() const { return s ? s : ""; }
};

struct ModuleHandle {
  FirModule *m;
  explicit ModuleHandle(FirModule *m) : m(m) {}
  ~ModuleHandle() {
    if (m)
      fir_module_free(m);
  }
};

// The external functions that do C's volatile accesses for `fcc`'s code (`Lower.cpp`): one
// load or store each, of 8, 16, 32, or 64 bits (integers zero-extended to 64 bits) or of a
// pointer, appended to each object that calls them, weak and in one COMDAT group, so the copies in
// objects linked together are one.
std::string volatileHelpers(const Options &o) {
  struct Fn {
    const char *name, *a64, *x64;
  };
  static const Fn fns[] = {
      {"__fcc_vload8", "ldrb w0, [x0]", "movzbl (%rdi), %eax"},
      {"__fcc_vload16", "ldrh w0, [x0]", "movzwl (%rdi), %eax"},
      {"__fcc_vload32", "ldr w0, [x0]", "movl (%rdi), %eax"},
      {"__fcc_vload64", "ldr x0, [x0]", "movq (%rdi), %rax"},
      {"__fcc_vloadp", "ldr x0, [x0]", "movq (%rdi), %rax"},
      {"__fcc_vstore8", "strb w1, [x0]", "movb %sil, (%rdi)"},
      {"__fcc_vstore16", "strh w1, [x0]", "movw %si, (%rdi)"},
      {"__fcc_vstore32", "str w1, [x0]", "movl %esi, (%rdi)"},
      {"__fcc_vstore64", "str x1, [x0]", "movq %rsi, (%rdi)"},
      {"__fcc_vstorep", "str x1, [x0]", "movq %rsi, (%rdi)"},
  };
  bool x86 = o.target == "x86_64";
  std::string s = "\n// fcc's volatile accesses\n";
  if (x86)
    s += "\t.att_syntax prefix\n";
  s += "\t.section .text.__fcc_volatile,\"axG\",@progbits,__fcc_volatile,comdat\n";
  for (const Fn &f : fns) {
    s += std::string("\t.p2align 2\n\t.weak ") + f.name + "\n\t.type " + f.name + ",@function\n" +
         f.name + ":\n\t" + (x86 ? f.x64 : f.a64) + "\n\tret\n\t.size " + f.name + ", .-" + f.name +
         "\n";
  }
  return s;
}

// The external functions that give the addresses of variables defined in another file
// (`Lower.cpp`), `__fcc_addr.NAME`, read from the GOT, for each one the assembly calls: weak, each
// in its own COMDAT group.
std::string externAddrHelpers(const Options &o, const std::string &text) {
  static const std::string prefix = "__fcc_addr.";
  std::set<std::string> names;
  for (size_t i = text.find(prefix); i != std::string::npos; i = text.find(prefix, i + 1)) {
    size_t j = i + prefix.size();
    while (j < text.size() && (isalnum((unsigned char)text[j]) || text[j] == '_'))
      j++;
    if (j > i + prefix.size())
      names.insert(text.substr(i + prefix.size(), j - i - prefix.size()));
  }
  bool x86 = o.target == "x86_64";
  std::string s;
  if (!names.empty())
    s += x86 ? "\n// fcc's external variables\n\t.att_syntax prefix\n"
             : "\n// fcc's external variables\n";
  for (const std::string &n : names) {
    std::string f = prefix + n;
    s += "\t.section .text." + f + ",\"axG\",@progbits," + f + ",comdat\n\t.p2align 2\n\t.weak " +
         f + "\n\t.type " + f + ",@function\n" + f + ":\n";
    s += x86 ? "\tmovq " + n + "@GOTPCREL(%rip), %rax\n"
             : "\tadrp x0, :got:" + n + "\n\tldr x0, [x0, :got_lo12:" + n + "]\n";
    s += "\tret\n\t.size " + f + ", .-" + f + "\n";
  }
  return s;
}

// The external functions that do the atomic operations for `fcc`'s code (`Lower.cpp`),
// `__fcc_atomic_OPN` (OP one of load, store, xchg, cas, add, sub, and, or, xor, nand, fence;
// N the bits, 8 to 64, or `p` for a pointer), sequentially consistent: AArch64's acquire and
// release loads and stores and exclusive pairs, x86-64's `xchg` and `lock` instructions. Each
// one the assembly calls is appended, weak, in its own COMDAT group. Values arrive and leave
// zero-extended to 64 bits.
std::string atomicBody(const Options &o, const std::string &op, unsigned n) {
  bool x86 = o.target == "x86_64";
  std::string s;
  auto L = [&](const std::string &l) { s += "\t" + l + "\n"; };
  if (op == "fence") {
    L(x86 ? "mfence" : "dmb ish");
    L("ret");
    return s;
  }
  if (!x86) {
    std::string sz = n == 8 ? "b" : n == 16 ? "h" : "";
    std::string r = n == 64 ? "x" : "w";
    if (op == "load") {
      L("ldar" + sz + " " + r + "0, [x0]");
    } else if (op == "store") {
      L("stlr" + sz + " " + r + "1, [x0]");
    } else if (op == "cas") {
      L("ldr" + sz + " " + r + "4, [x1]");
      s += "1:\n";
      L("ldaxr" + sz + " " + r + "3, [x0]");
      L("cmp " + r + "3, " + r + "4");
      L("b.ne 2f");
      L("stlxr" + sz + " w5, " + r + "2, [x0]");
      L("cbnz w5, 1b");
      L("mov w0, #1");
      L("ret");
      s += "2:\n";
      L("clrex");
      L("str" + sz + " " + r + "3, [x1]");
      L("mov w0, #0");
    } else {
      s += "1:\n";
      L("ldaxr" + sz + " " + r + "2, [x0]");
      if (op == "xchg") {
        L("stlxr" + sz + " w3, " + r + "1, [x0]");
      } else {
        std::string i = op == "add"                   ? "add"
                        : op == "sub"                 ? "sub"
                        : op == "and" || op == "nand" ? "and"
                        : op == "or"                  ? "orr"
                                                      : "eor";
        L(i + " " + r + "4, " + r + "2, " + r + "1");
        if (op == "nand")
          L("mvn " + r + "4, " + r + "4");
        L("stlxr" + sz + " w3, " + r + "4, [x0]");
      }
      L("cbnz w3, 1b");
      if (n == 8)
        L("and w0, w2, #0xff");
      else if (n == 16)
        L("and w0, w2, #0xffff");
      else
        L("mov " + r + "0, " + r + "2");
    }
    L("ret");
    return s;
  }
  std::string sfx = n == 8 ? "b" : n == 16 ? "w" : n == 32 ? "l" : "q";
  auto reg = [&](const char *q, const char *d, const char *w, const char *b8) {
    return std::string("%") + (n == 64 ? q : n == 32 ? d : n == 16 ? w : b8);
  };
  std::string ax = reg("rax", "eax", "ax", "al"), si = reg("rsi", "esi", "si", "sil"),
              cx = reg("rcx", "ecx", "cx", "cl"), dx = reg("rdx", "edx", "dx", "dl");
  std::string zload = n == 8 ? "movzbl" : n == 16 ? "movzwl" : n == 32 ? "movl" : "movq";
  std::string zdst = n == 64 ? "%rax" : "%eax";
  std::string zext = n == 8 ? "movzbl %al, %eax" : n == 16 ? "movzwl %ax, %eax" : "";
  if (op == "load") {
    L(zload + " (%rdi), " + zdst);
  } else if (op == "store") {
    L("xchg" + sfx + " " + si + ", (%rdi)");
  } else if (op == "xchg") {
    L("movq %rsi, %rax");
    L("xchg" + sfx + " " + ax + ", (%rdi)");
    if (!zext.empty())
      L(zext);
  } else if (op == "add" || op == "sub") {
    L("movq %rsi, %rax");
    if (op == "sub")
      L("negq %rax");
    L("lock xadd" + sfx + " " + ax + ", (%rdi)");
    if (!zext.empty())
      L(zext);
  } else if (op == "cas") {
    L(zload + " (%rsi), " + zdst);
    L("lock cmpxchg" + sfx + " " + dx + ", (%rdi)");
    L("je 1f");
    L("mov" + sfx + " " + ax + ", (%rsi)");
    L("xorl %eax, %eax");
    L("ret");
    s += "1:\n";
    L("movl $1, %eax");
  } else {
    L(zload + " (%rdi), " + zdst);
    s += "1:\n";
    L("movq %rax, %rcx");
    std::string i = op == "or" ? "orq" : op == "xor" ? "xorq" : "andq";
    L(i + " %rsi, %rcx");
    if (op == "nand")
      L("notq %rcx");
    L("lock cmpxchg" + sfx + " " + cx + ", (%rdi)");
    L("jne 1b");
    if (!zext.empty())
      L(zext);
  }
  L("ret");
  return s;
}

std::string atomicHelpers(const Options &o, const std::string &text) {
  static const std::string prefix = "__fcc_atomic_";
  std::set<std::string> names;
  for (size_t i = text.find(prefix); i != std::string::npos; i = text.find(prefix, i + 1)) {
    size_t j = i + prefix.size();
    while (j < text.size() && (isalnum((unsigned char)text[j]) || text[j] == '_'))
      j++;
    names.insert(text.substr(i, j - i));
  }
  bool x86 = o.target == "x86_64";
  std::string s;
  if (!names.empty())
    s += x86 ? "\n// fcc's atomic operations\n\t.att_syntax prefix\n"
             : "\n// fcc's atomic operations\n";
  for (const std::string &f : names) {
    std::string rest = f.substr(prefix.size());
    std::string op = rest, size;
    // OP is letters; N digits or a final `p`.
    size_t d = rest.size();
    while (d > 0 && isdigit((unsigned char)rest[d - 1]))
      d--;
    if (d == rest.size() && !rest.empty() && rest.back() == 'p')
      d = rest.size() - 1;
    op = rest.substr(0, d);
    size = rest.substr(d);
    unsigned n = size == "p" || size.empty() ? 64 : (unsigned)std::stoul(size);
    s += "\t.section .text." + f + ",\"axG\",@progbits," + f + ",comdat\n\t.p2align 2\n\t.weak " +
         f + "\n\t.type " + f + ",@function\n" + f + ":\n" + atomicBody(o, op, n) + "\t.size " + f +
         ", .-" + f + "\n";
  }
  return s;
}

int compileAndLink(FirModule *m, const Options &o) {
  FirString as;
  FirStatus st = o.hasPasses
                     ? fir_module_compile_passes(m, o.target.c_str(), o.passes.c_str(),
                                                 o.experimental, FIR_OS_LINUX, &as.s)
                     : fir_module_compile(m, o.target.c_str(), o.optimize, FIR_OS_LINUX, &as.s);
  if (st != FIR_OK) {
    std::string err = fir_module_error(m);
    if (!o.checkDce.empty() && err.find("check-dce") != std::string::npos)
      llvm::errs() << o.file << ": the proved DCE checker refused the optimized output: " << err
                   << "\n";
    else
      llvm::errs() << o.file << ": the " << targetName(o)
                   << " backend can't compile this program: " << err << "\n";
    return 1;
  }
  std::string text = as.str();
  if (text.find("__fcc_vload") != std::string::npos ||
      text.find("__fcc_vstore") != std::string::npos)
    text += volatileHelpers(o);
  text += externAddrHelpers(o, text);
  text += atomicHelpers(o, text);
  // The function that fills initializers' addresses of other files' variables (`Lower.cpp`),
  // run before `main` from the ELF `.init_array`, at priority 0 (`.init_array.00000`, one of
  // the priorities C implementations keep for themselves), so before every constructor a
  // program declares, which may read those slots.
  if (size_t i = text.find("\n__fcc_init."); i != std::string::npos) {
    size_t j = text.find(':', i + 1);
    text += "\n\t.section .init_array.00000,\"aw\"\n\t.p2align 3\n\t.quad " +
            text.substr(i + 1, j - i - 1) + "\n";
  }
  if (o.emit == "asm")
    return writeOut(o.out, text) ? 0 : 1;
  std::string out = o.out.empty() ? "a.out" : o.out;
  if (llvm::StringRef(out).ends_with(".s"))
    return writeOut(out, text) ? 0 : 1;
  llvm::SmallString<128> tmp;
  if (std::error_code ec = llvm::sys::fs::createTemporaryFile("fcc", "s", tmp)) {
    llvm::errs() << "fcc: a temporary file: " << ec.message() << "\n";
    return 1;
  }
  std::string s = tmp.str().str();
  int rc = 1;
  bool written;
  {
    Step step("fcc: write assembly");
    written = writeOut(s, text);
  }
  if (written) {
    std::string cc = linker(o);
    auto prog = llvm::sys::findProgramByName(cc);
    if (!prog) {
      llvm::errs() << "fcc: no " << targetName(o) << " C compiler to link with: '" << cc
                   << "' (set FIR_CC, or use the dev shell)\n";
    } else {
      std::vector<std::string> args = {cc, s};
      for (const std::string &a : o.linkArgs)
        args.push_back(a);
      args.push_back("-o");
      args.push_back(out);
      if (llvm::StringRef(out).ends_with(".o"))
        args.push_back("-c");
      std::vector<llvm::StringRef> refs(args.begin(), args.end());
      std::string err;
      Step step("fcc: assemble, link (cc)");
      int status = llvm::sys::ExecuteAndWait(*prog, refs, std::nullopt, {}, 0, 0, &err);
      if (status == 0) {
        rc = 0;
      } else {
        llvm::errs() << "fcc: " << cc << " failed" << (err.empty() ? "" : ": " + err) << "\n";
      }
    }
  }
  llvm::sys::fs::remove(s);
  return rc;
}

int run(int argc, char **argv) {
  for (int i = 1; i < argc; i++)
    commandLine += std::string(argv[i]) + '\0';
  Options o;
  if (!parseArgs(argc, argv, o)) {
    llvm::errs() << kUsage;
    return 2;
  }
  // The library's -O pipeline runs the proved checker when this names a fir-ref.
  if (!o.checkDce.empty())
    setenv("FIR_CHECK_DCE", o.checkDce.c_str(), 1);
  if (o.experimental && o.hasPasses)
    llvm::errs() << "fcc: warning: --experimental: passes that are not proved may run\n";
  std::vector<std::string> args = {"-target", triple(o), "-nostdlibinc"};
  std::string res = FCC_RESOURCE_DIR;
  if (const char *r = std::getenv("FCC_RESOURCE_DIR"); r && *r)
    res = r;
  if (!res.empty()) {
    args.push_back("-resource-dir");
    args.push_back(res);
  }
  for (const std::string &d : systemIncludes(o)) {
    args.push_back("-idirafter");
    args.push_back(d);
  }
  for (const std::string &a : o.clangArgs)
    args.push_back(a);

  ModuleHandle mh(fir_module_new());
  bool lowered = false;
  int rc;
  {
    std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();
    clang::tooling::FixedCompilationDatabase db(".", args);
    clang::tooling::ClangTool tool(db, {o.file});
    Factory factory(mh.m, lowered);
    rc = tool.run(&factory);
    double all = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    fir_time_record("fcc: clang (preprocess, parse, sema)", all - lowerSeconds);
  }
  if (rc != 0 || !lowered)
    return 1;

  if (fir_module_verify(mh.m) != FIR_OK) {
    llvm::errs() << o.file
                 << ": internal error: the HFIR doesn't verify: " << fir_module_error(mh.m) << "\n";
    FirString text;
    text.s = fir_module_print(mh.m, true);
    if (std::getenv("FCC_DUMP"))
      llvm::errs() << text.str();
    return 1;
  }
  if (o.emit == "hfir") {
    FirString text;
    text.s = fir_module_print(mh.m, true);
    return writeOut(o.out, text.str()) ? 0 : 1;
  }
  if (o.emit == "mfir") {
    FirModule *l = nullptr, *opt = nullptr;
    if (fir_module_lower(mh.m, &l) != FIR_OK) {
      llvm::errs() << o.file << ": lowering to MFIR failed: " << fir_module_error(mh.m) << "\n";
      return 1;
    }
    ModuleHandle lh(l);
    if (o.optimize || o.hasPasses) {
      FirStatus st = o.hasPasses
                         ? fir_module_optimize_passes(l, o.passes.c_str(), o.experimental, &opt)
                         : fir_module_optimize(l, &opt);
      if (st != FIR_OK) {
        llvm::errs() << o.file << ": optimizing failed: " << fir_module_error(l) << "\n";
        return 1;
      }
    }
    ModuleHandle oh(opt);
    FirString text;
    text.s = fir_module_print(opt ? opt : l, true);
    return writeOut(o.out, text.str()) ? 0 : 1;
  }
  return compileAndLink(mh.m, o);
}

} // namespace

int main(int argc, char **argv) {
  int rc = run(argc, argv);
  if (char *report = fir_time_report()) {
    llvm::errs() << report;
    fir_string_free(report);
  }
  return rc;
}
