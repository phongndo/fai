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
// The linker is $FIR_CC, or `cc` when the host is the target, else the target's cross compiler
// (`aarch64-unknown-linux-gnu-cc`, which the dev shell has on x86-64 Linux, or
// `x86_64-unknown-linux-gnu-cc`). Its system include directories are given to Clang (after
// Clang's own headers), so <stdint.h> and friends are the target's.

#include "Lower.h"
#include "fir.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdio>
#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#ifndef FCC_RESOURCE_DIR
#define FCC_RESOURCE_DIR ""
#endif

namespace {

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
#if defined(__aarch64__)
  bool native = !x86(o);
#elif defined(__x86_64__)
  bool native = x86(o);
#else
  bool native = false;
#endif
  if (native)
    return "cc";
  return std::string(triple(o)) + "-cc";
}

// The target C compiler's system include directories, without its compiler-specific ones
// (Clang brings its own).
std::vector<std::string> systemIncludes(const Options &o) {
  std::vector<std::string> dirs;
  std::string cmd = linker(o) + " -E -Wp,-v -x c /dev/null 2>&1";
  FILE *p = popen(cmd.c_str(), "r");
  if (!p)
    return dirs;
  char line[4096];
  bool in = false;
  while (fgets(line, sizeof line, p)) {
    llvm::StringRef l = llvm::StringRef(line).trim();
    if (l.starts_with("#include <...>")) {
      in = true;
    } else if (l.starts_with("End of search list")) {
      in = false;
    } else if (in && !l.contains("/lib/gcc/") && !l.contains("/lib/clang/") &&
               !l.contains("/include-fixed")) {
      dirs.push_back(l.str());
    }
  }
  pclose(p);
  return dirs;
}

class Consumer : public clang::ASTConsumer {
public:
  Consumer(FirModule *m, bool &lowered) : m(m), lowered(lowered) {}
  void HandleTranslationUnit(clang::ASTContext &ctx) override {
    if (ctx.getDiagnostics().hasErrorOccurred())
      return;
    lowered = fai::lowerTranslationUnit(ctx, m);
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
  if (o.emit == "asm")
    return writeOut(o.out, as.str()) ? 0 : 1;
  std::string out = o.out.empty() ? "a.out" : o.out;
  if (llvm::StringRef(out).ends_with(".s"))
    return writeOut(out, as.str()) ? 0 : 1;
  llvm::SmallString<128> tmp;
  if (std::error_code ec = llvm::sys::fs::createTemporaryFile("fcc", "s", tmp)) {
    llvm::errs() << "fcc: a temporary file: " << ec.message() << "\n";
    return 1;
  }
  std::string s = tmp.str().str();
  int rc = 1;
  if (writeOut(s, as.str())) {
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

} // namespace

int main(int argc, char **argv) {
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
  clang::tooling::FixedCompilationDatabase db(".", args);
  clang::tooling::ClangTool tool(db, {o.file});
  Factory factory(mh.m, lowered);
  int rc = tool.run(&factory);
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
