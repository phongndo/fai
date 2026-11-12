// fai-cc's lowering: Clang's AST of a C translation unit to HFIR, built through `fir.h` only.
//
// The mapping (decisions.md, row C frontend):
//
// * Types. `_Bool` is `i8` (0 or 1), the other integer types and enums `iN` of their size,
//   pointers `ptr`, arrays `array<N x T>`, structs `struct<C>{…}` built from Clang's record
//   layout (bitfield storage and gaps as `array<k x i8>` padding, extra alignment as a leading
//   `array<0 x iA>`) and checked against it field by field, and unions a struct of their size
//   and alignment that members are read through by pointer.
// * Every C rule is an explicit modifier: signed `+ - *` are `.nsw`, unsigned ones `.wrap`;
//   `/` and `%` are `int.div.s.ub`/`.u.ub`; shifts are `.ub` (a shift by at least the width or
//   by a negative amount is UB in C; signed left shifts that overflow wrap, which refines C's
//   UB); integer conversions truncate with `.wrap` (C's implementation-defined conversion is
//   modular on every target Clang supports).
// * Objects live in memory: every local and parameter is a `mem.stack.of` slot made at the
//   function's entry, and every access a load or store (mem2reg comes later). Globals, static
//   locals, string literals, and file-scope compound literals are FIR globals; aggregate copies
//   are `mem.copy`. `char` accesses are `i8` loads and stores, which stay defined on pointer
//   bytes (decision: Pointer bytes as integers); copies of whole objects are exact.
// * Control flow is structured (`cf.if`, `cf.loop`) where C's is; a `switch` is a `cf.blocks`
//   with `cf.switch`, and a function with `goto` (or a `switch` whose cases sit inside other
//   statements) becomes one `cf.blocks` of basic blocks. `&&`, `||`, and `?:` are `cf.if`.
// * Calls to functions without a body here are `extern func`s that may do anything
//   (`effects[read(args), read(exposed), read(globals), write(…), alloc, free, trap, diverge]`);
//   `malloc` and `free` are FIR's `mem.alloc.null c.malloc` and `mem.free c.malloc`.
//
// What isn't supported yet is reported with its source location and nothing is emitted.

#include "Lower.h"

#include "clang/AST/APValue.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

#include <functional>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace clang;

namespace fai {
namespace {

// Thrown after a diagnostic, to stop lowering the current function or global.
struct Abort {};

constexpr FirEffect kAllEffects[] = {
    FIR_EFFECT_READ_ARGS,  FIR_EFFECT_READ_EXPOSED,  FIR_EFFECT_READ_GLOBALS,
    FIR_EFFECT_WRITE_ARGS, FIR_EFFECT_WRITE_EXPOSED, FIR_EFFECT_WRITE_GLOBALS,
    FIR_EFFECT_ALLOC,      FIR_EFFECT_FREE,          FIR_EFFECT_TRAP,
    FIR_EFFECT_DIVERGE,
};

uint64_t alignUp(uint64_t x, uint64_t a) { return a <= 1 ? x : (x + a - 1) / a * a; }

// The `n`-bit pattern `v` as the signed 64-bit number `fir_int_const` takes.
int64_t pattern(uint64_t v, unsigned bits) {
  if (bits >= 64)
    return (int64_t)v;
  uint64_t m = (uint64_t(1) << bits) - 1;
  v &= m;
  if (v >> (bits - 1))
    v |= ~m;
  return (int64_t)v;
}

// A struct's FIR field: a C member, padding (bytes that hold bitfields or nothing), or the
// zero-length array that gives the struct Clang's alignment.
struct Slot {
  enum Kind { Member, Pad, Align } kind;
  const FieldDecl *field;
  uint64_t offset, len;
  FirType ty;
};

struct BitField {
  uint64_t bitOffset; // from the record's start
  unsigned width;
};

struct RecordInfo {
  FirType ty;
  bool isUnion;
  uint64_t size;
  unsigned align;
  std::vector<Slot> slots;
  llvm::DenseMap<const FieldDecl *, uint32_t> index; // members: their FIR field
  llvm::DenseMap<const FieldDecl *, BitField> bits;  // bitfields
};

// An lvalue: an address, or a bitfield of the record at `addr`.
struct LValue {
  FirValue addr;
  const FieldDecl *bitfield = nullptr;
};

// What `break` and `continue` do inside a loop or a switch.
struct Jump {
  bool isLoop;
  std::function<void()> onContinue;      // structured loops
  FirRegion breakBlock = FIR_INVALID;    // switches (structured), loops and switches (CFG)
  FirRegion continueBlock = FIR_INVALID; // loops (CFG)
};

class Lowerer {
public:
  Lowerer(ASTContext &ctx, FirModule *m)
      : ctx(ctx), diags(ctx.getDiagnostics()), sm(ctx.getSourceManager()), m(m) {}

  bool run();

private:
  ASTContext &ctx;
  DiagnosticsEngine &diags;
  SourceManager &sm;
  FirModule *m;
  bool failed = false;
  SourceLocation curLoc;

  // Module state.
  std::map<const RecordDecl *, RecordInfo> records;
  llvm::DenseMap<const FunctionDecl *, FirFunc> funcs;
  llvm::DenseMap<const VarDecl *, FirGlobal> globals;
  llvm::DenseMap<const Expr *, FirGlobal> exprGlobals; // string and compound literals
  std::map<FirType, FirGlobal> zeros;
  std::vector<const VarDecl *> pendingVars;
  std::vector<const CompoundLiteralExpr *> pendingLits;
  std::set<std::string> usedNames;
  unsigned counter = 0;

  // Function state.
  FirBuilder *b = nullptr;
  const FunctionDecl *curFn = nullptr;
  bool cfg = false; // the function is one cf.blocks
  FirOp blocksOp = FIR_INVALID;
  FirRegion region = FIR_INVALID; // where ops go
  bool term = false;              // the region (or block) already ended
  llvm::DenseMap<const Decl *, FirValue> slots;
  llvm::DenseMap<const CompoundLiteralExpr *, FirValue> litSlots;
  llvm::DenseMap<const LabelDecl *, FirRegion> labels;
  llvm::DenseMap<const SwitchCase *, FirRegion> caseBlocks;
  std::vector<Jump> jumps;
  std::set<std::string> valueNames;

  // Diagnostics.

  void report(SourceLocation loc, const std::string &msg) {
    unsigned id = diags.getCustomDiagID(DiagnosticsEngine::Error, "%0");
    diags.Report(loc, id) << msg;
    failed = true;
  }
  [[noreturn]] void unsupported(SourceLocation loc, const std::string &what) {
    report(loc, "fai-cc does not support " + what + " yet");
    throw Abort{};
  }
  [[noreturn]] void internal(const std::string &what) {
    report(curLoc, "internal error: " + what + ": " + fir_module_error(m));
    throw Abort{};
  }
  uint32_t ck(uint32_t id, const char *what) {
    if (id == FIR_INVALID)
      internal(what);
    return id;
  }
  void ok(FirStatus s, const char *what) {
    if (s != FIR_OK)
      internal(what);
  }

  // Locations: every op gets its C construct's line and column.

  struct LocScope {
    Lowerer &l;
    SourceLocation saved;
    LocScope(Lowerer &l, SourceLocation loc) : l(l), saved(l.curLoc) {
      if (loc.isValid())
        l.setLoc(loc);
    }
    ~LocScope() {
      if (saved.isValid())
        l.setLoc(saved);
    }
  };
  void setLoc(SourceLocation loc) {
    curLoc = loc;
    if (!b)
      return;
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    if (p.isValid())
      fir_set_loc(b, p.getLine(), p.getColumn());
  }

  // Names.

  std::string uniqueName(const std::string &want) {
    std::string n = want;
    for (unsigned i = 1; usedNames.count(n) || fir_func_find(m, n.c_str()) != FIR_INVALID; i++)
      n = want + "." + std::to_string(i);
    usedNames.insert(n);
    return n;
  }
  bool validName(StringRef n) {
    if (n.empty() || isdigit((unsigned char)n[0]))
      return false;
    for (char c : n)
      if (!isalnum((unsigned char)c) && c != '_')
        return false;
    return true;
  }
  void nameValue(FirValue v, StringRef want) {
    if (!validName(want.split('.').first))
      return;
    std::string n = want.str();
    for (unsigned i = 1; valueNames.count(n); i++)
      n = want.str() + "." + std::to_string(i);
    valueNames.insert(n);
    fir_value_set_name(b, v, n.c_str());
  }

  // Types.

  unsigned bits(QualType t) { return (unsigned)ctx.getTypeSize(t); }
  unsigned alignOf(QualType t) { return (unsigned)ctx.getTypeAlignInChars(t).getQuantity(); }
  bool isSigned(QualType t) { return t->isSignedIntegerOrEnumerationType(); }

  bool isScalar(QualType t) {
    t = t.getCanonicalType();
    return t->isIntegerType() || t->isPointerType() || t->isBooleanType();
  }

  FirType scalarTy(QualType t, SourceLocation loc) {
    QualType c = t.getCanonicalType();
    if (c.isVolatileQualified())
      unsupported(loc, "'volatile'");
    if (c->isBooleanType())
      return fir_type_int(8);
    if (c->isPointerType())
      return FIR_TYPE_PTR;
    if (c->isIntegerType()) {
      if (c->isBitIntType())
        unsupported(loc, "'_BitInt'");
      unsigned n = bits(c);
      if (n > 64)
        unsupported(loc, "128-bit integers ('" + t.getAsString() + "')");
      return fir_type_int(n);
    }
    if (c->isRealFloatingType())
      unsupported(loc, "floating-point types ('" + t.getAsString() + "', track F2)");
    if (c->isAnyComplexType())
      unsupported(loc, "'_Complex'");
    if (c->isAtomicType())
      unsupported(loc, "'_Atomic'");
    if (c->isVectorType())
      unsupported(loc, "vector types");
    unsupported(loc, "values of type '" + t.getAsString() + "' here");
  }

  FirType memTy(QualType t, SourceLocation loc) {
    QualType c = t.getCanonicalType();
    if (c.isVolatileQualified())
      unsupported(loc, "'volatile'");
    if (isScalar(c) || c->isRealFloatingType() || c->isAnyComplexType())
      return scalarTy(c, loc);
    if (const auto *a = ctx.getAsConstantArrayType(c))
      return ck(fir_type_array(m, a->getSize().getZExtValue(), memTy(a->getElementType(), loc)),
                "fir_type_array");
    if (const auto *a = ctx.getAsIncompleteArrayType(c))
      return ck(fir_type_array(m, 0, memTy(a->getElementType(), loc)), "fir_type_array");
    if (ctx.getAsVariableArrayType(c))
      unsupported(loc, "variable-length arrays");
    if (const RecordDecl *rd = c->getAsRecordDecl())
      return record(rd, loc).ty;
    unsupported(loc, "objects of type '" + t.getAsString() + "'");
  }

  void layoutOf(FirType t, uint64_t &size, uint32_t &align) {
    ok(fir_type_layout(m, t, &size, &align), "fir_type_layout");
  }

  // A record's FIR type, made from Clang's layout and checked against it.
  RecordInfo &record(const RecordDecl *rd, SourceLocation loc) {
    const RecordDecl *def = rd->getDefinition();
    if (!def)
      unsupported(loc, "incomplete struct or union types");
    auto found = records.find(def);
    if (found != records.end())
      return found->second;
    if (def->hasAttr<PackedAttr>() || def->hasAttr<MaxFieldAlignmentAttr>())
      unsupported(def->getLocation(), "packed structs");
    const ASTRecordLayout &L = ctx.getASTRecordLayout(def);
    RecordInfo info;
    info.isUnion = def->isUnion();
    info.size = (uint64_t)L.getSize().getQuantity();
    info.align = (unsigned)L.getAlignment().getQuantity();
    if (info.size == 0)
      unsupported(def->getLocation(), "empty structs and unions");
    if (info.align > 16)
      unsupported(def->getLocation(), "alignments above 16");
    unsigned firAlign = 1;
    uint64_t cur = 0;
    // Whether bitfields lie between `cur` and the next member (or the end): their bytes get an
    // explicit padding slot even where FIR's layout would leave them implicit, since a global's
    // initializer only sets the bytes of its fields (FIR zeroes the rest).
    bool bitsPending = false;
    auto pad = [&](uint64_t from, uint64_t len) {
      FirType t = ck(fir_type_array(m, len, fir_type_int(8)), "fir_type_array");
      info.slots.push_back({Slot::Pad, nullptr, from, len, t});
    };
    for (const FieldDecl *fd : def->fields()) {
      uint64_t bitOff = L.getFieldOffset(fd->getFieldIndex());
      if (fd->isBitField()) {
        unsigned w = fd->getBitWidthValue();
        if (w == 0)
          continue;
        if (bits(fd->getType()) > 64)
          unsupported(fd->getLocation(), "bitfields wider than 64 bits");
        info.bits[fd] = {bitOff, w};
        bitsPending = true;
        continue;
      }
      if (info.isUnion) {
        memTy(fd->getType(), fd->getLocation()); // diagnose unsupported member types
        continue;
      }
      FirType ft = memTy(fd->getType(), fd->getLocation());
      uint64_t fsize;
      uint32_t falign;
      layoutOf(ft, fsize, falign);
      uint64_t off = bitOff / 8;
      if (off < cur || off % falign != 0)
        layoutMismatch(def, "field '" + fd->getName().str() + "'");
      if (bitsPending || alignUp(cur, falign) != off)
        pad(cur, off - cur);
      bitsPending = false;
      info.index[fd] = (uint32_t)info.slots.size();
      info.slots.push_back({Slot::Member, fd, off, fsize, ft});
      cur = off + fsize;
      firAlign = std::max(firAlign, (unsigned)falign);
    }
    if (info.isUnion)
      cur = 0;
    if (firAlign > info.align)
      layoutMismatch(def, "its alignment");
    if (firAlign < info.align) {
      FirType a = ck(fir_type_array(m, 0, fir_type_int(8 * info.align)), "fir_type_array");
      info.slots.insert(info.slots.begin(), {Slot::Align, nullptr, 0, 0, a});
      for (auto &e : info.index)
        e.second++;
    }
    if (bitsPending || alignUp(cur, info.align) != info.size)
      pad(cur, info.size - cur);
    std::vector<FirType> tys;
    for (const Slot &s : info.slots)
      tys.push_back(s.ty);
    info.ty = ck(fir_type_struct(m, FIR_POLICY_C, tys.data(), tys.size()), "fir_type_struct");
    // FIR's layout must be Clang's: every member's offset, the size, and the alignment.
    uint64_t size;
    uint32_t align;
    layoutOf(info.ty, size, align);
    if (size != info.size || align != info.align)
      layoutMismatch(def, "its size or alignment");
    for (uint32_t i = 0; i < info.slots.size(); i++) {
      uint64_t off;
      ok(fir_type_field_offset(m, info.ty, i, &off), "fir_type_field_offset");
      if (off != info.slots[i].offset)
        layoutMismatch(def, "FIR field " + std::to_string(i));
    }
    return records.emplace(def, std::move(info)).first->second;
  }

  [[noreturn]] void layoutMismatch(const RecordDecl *rd, const std::string &what) {
    report(rd->getLocation(), "internal error: FIR's struct<C> layout of '" +
                                  rd->getNameAsString() + "' differs from Clang's at " + what);
    throw Abort{};
  }

  // Signatures.

  struct Sig {
    std::vector<FirType> params, rets;
  };

  // A function type's FIR signature. One without a prototype (`int f();`) takes no
  // parameters: calls with arguments to it are rejected (C23's meaning).
  Sig sigOf(const FunctionType *ft, SourceLocation loc) {
    Sig s;
    QualType ret = ft->getReturnType();
    if (ret->isRecordType())
      unsupported(loc, "structs and unions returned by value (track A)");
    if (!ret->isVoidType())
      s.rets.push_back(scalarTy(ret, loc));
    if (const auto *p = dyn_cast<FunctionProtoType>(ft)) {
      if (p->isVariadic())
        unsupported(loc, "variadic functions (track V)");
      for (QualType pt : p->param_types()) {
        if (pt->isRecordType())
          unsupported(loc, "structs and unions passed by value (track A)");
        s.params.push_back(scalarTy(pt, loc));
      }
    }
    return s;
  }

  FirType funcTy(const FunctionType *ft, SourceLocation loc) {
    Sig s = sigOf(ft, loc);
    return ck(fir_type_func(m, s.params.data(), s.params.size(), s.rets.data(), s.rets.size()),
              "fir_type_func");
  }

  const FunctionType *fnType(QualType t) { return t->castAs<FunctionType>(); }

  // A function: declared when first needed; one without a body here is external.
  FirFunc funcFor(const FunctionDecl *fd, SourceLocation loc) {
    fd = fd->getCanonicalDecl();
    auto it = funcs.find(fd);
    if (it != funcs.end())
      return it->second;
    const FunctionDecl *def = nullptr;
    fd->hasBody(def);
    const FunctionDecl *typed = def ? def : fd->getMostRecentDecl();
    std::string name = fd->getName().str();
    if (!validName(name))
      unsupported(loc, "the function name '" + name + "'");
    Sig s = sigOf(fnType(typed->getType()), loc);
    FirFunc f;
    if (def) {
      f = ck(fir_func_declare(m, name.c_str(), s.params.data(), s.params.size(), s.rets.data(),
                              s.rets.size()),
             "fir_func_declare");
    } else {
      f = ck(fir_extern_declare(m, name.c_str(), s.params.data(), s.params.size(), s.rets.data(),
                                s.rets.size(), kAllEffects, std::size(kAllEffects),
                                FIR_TRUST_ASSUME),
             "fir_extern_declare");
    }
    usedNames.insert(name);
    funcs[fd] = f;
    return f;
  }

  // Globals.

  bool isConstObject(QualType t) {
    return t.isConstQualified() || ctx.getBaseElementType(t).isConstQualified();
  }

  FirGlobal globalFor(const VarDecl *vd, SourceLocation loc) {
    vd = vd->getCanonicalDecl();
    auto it = globals.find(vd);
    if (it != globals.end())
      return it->second;
    const VarDecl *def = vd->getDefinition();
    if (!def)
      def = vd->getActingDefinition();
    if (!def)
      unsupported(loc, "external variables ('" + vd->getNameAsString() +
                           "' is defined in another file; FIR has no external globals)");
    if (def->getTLSKind() != VarDecl::TLS_None)
      unsupported(loc, "thread-local variables");
    std::string name = vd->getName().str();
    if (vd->isStaticLocal()) {
      const auto *fn = dyn_cast<FunctionDecl>(vd->getDeclContext());
      name = (fn ? fn->getName().str() : std::string("local")) + "." + name;
    }
    if (!validName(vd->getName()))
      unsupported(loc, "the variable name '" + name + "'");
    name = vd->isStaticLocal() ? uniqueName(name) : name;
    usedNames.insert(name);
    FirType t = memTy(def->getType(), def->getLocation());
    unsigned align = (unsigned)ctx.getDeclAlign(def).getQuantity();
    FirGlobal g = ck(fir_global_declare(m, name.c_str(), t, isConstObject(def->getType()), align,
                                        ck(fir_init_zero(m), "fir_init_zero")),
                     "fir_global_declare");
    globals[vd] = g;
    pendingVars.push_back(def);
    return g;
  }

  FirGlobal stringGlobal(const StringLiteral *sl) {
    auto it = exprGlobals.find(sl);
    if (it != exprGlobals.end())
      return it->second;
    const auto *at = ctx.getAsConstantArrayType(sl->getType());
    FirGlobal g = bytesGlobal("str", at->getSize().getZExtValue(), sl, sl->getBeginLoc(), true);
    exprGlobals[sl] = g;
    return g;
  }

  // A constant global of `n` bytes holding a string literal's bytes, then zeros.
  FirGlobal bytesGlobal(const char *prefix, uint64_t n, const StringLiteral *sl, SourceLocation loc,
                        bool constant) {
    if (sl->getCharByteWidth() != 1)
      unsupported(loc, "wide string literals");
    std::vector<uint8_t> bytes(n, 0);
    StringRef s = sl->getBytes();
    for (uint64_t i = 0; i < n && i < s.size(); i++)
      bytes[i] = (uint8_t)s[i];
    FirType t = ck(fir_type_array(m, n, fir_type_int(8)), "fir_type_array");
    FirInit init = ck(fir_init_bytes(m, bytes.data(), bytes.size()), "fir_init_bytes");
    std::string name = uniqueName(std::string(prefix) + "." + std::to_string(counter++));
    return ck(fir_global_declare(m, name.c_str(), t, constant, 1, init), "fir_global_declare");
  }

  FirGlobal zeroGlobal(FirType t) {
    auto it = zeros.find(t);
    if (it != zeros.end())
      return it->second;
    std::string name = uniqueName("zero." + std::to_string(counter++));
    FirGlobal g = ck(fir_global_declare(m, name.c_str(), t, true, 1, ck(fir_init_zero(m), "zero")),
                     "fir_global_declare");
    zeros[t] = g;
    return g;
  }

  FirGlobal litGlobal(const CompoundLiteralExpr *cle) {
    auto it = exprGlobals.find(cle);
    if (it != exprGlobals.end())
      return it->second;
    FirType t = memTy(cle->getType(), cle->getBeginLoc());
    std::string name = uniqueName("lit." + std::to_string(counter++));
    FirGlobal g = ck(fir_global_declare(m, name.c_str(), t, isConstObject(cle->getType()),
                                        alignOf(cle->getType()), ck(fir_init_zero(m), "zero")),
                     "fir_global_declare");
    exprGlobals[cle] = g;
    pendingLits.push_back(cle);
    return g;
  }

  // Initializers of globals, from Clang's evaluation of them.

  FirInit izero() { return ck(fir_init_zero(m), "fir_init_zero"); }
  FirInit iint(int64_t v) { return ck(fir_init_int(m, v), "fir_init_int"); }

  bool isZero(const APValue &v) {
    switch (v.getKind()) {
    case APValue::None:
    case APValue::Indeterminate:
      return true;
    case APValue::Int:
      return v.getInt().isZero();
    case APValue::LValue:
      return v.isNullPointer();
    case APValue::Array:
      for (unsigned i = 0; i < v.getArrayInitializedElts(); i++)
        if (!isZero(v.getArrayInitializedElt(i)))
          return false;
      return !v.hasArrayFiller() || isZero(v.getArrayFiller());
    case APValue::Struct:
      for (unsigned i = 0; i < v.getStructNumFields(); i++)
        if (!isZero(v.getStructField(i)))
          return false;
      return true;
    case APValue::Union:
      return !v.getUnionField() || isZero(v.getUnionValue());
    default:
      return false;
    }
  }

  FirInit initFrom(const APValue &v, QualType t, SourceLocation loc) {
    if (isZero(v))
      return izero();
    QualType c = t.getCanonicalType();
    if (c->isIntegerType() || c->isBooleanType()) {
      if (!v.isInt())
        unsupported(loc, "addresses used as integers in a global's initializer");
      const llvm::APSInt &n = v.getInt();
      return iint(pattern(n.isSigned() ? (uint64_t)n.getExtValue() : n.getZExtValue(), bits(c)));
    }
    if (c->isPointerType()) {
      if (!v.isLValue() || !v.getLValueBase())
        unsupported(loc, "integers used as pointers in a global's initializer");
      if (!v.getLValueOffset().isZero())
        unsupported(loc, "a global's initializer pointing inside another object (FIR's "
                         "initializers name only the start of a global)");
      APValue::LValueBase base = v.getLValueBase();
      if (const ValueDecl *d = base.dyn_cast<const ValueDecl *>()) {
        if (const auto *fd = dyn_cast<FunctionDecl>(d))
          return ck(fir_init_func(m, funcFor(fd, loc)), "fir_init_func");
        if (const auto *vd = dyn_cast<VarDecl>(d))
          return ck(fir_init_global(m, globalFor(vd, loc)), "fir_init_global");
      } else if (const Expr *e = base.dyn_cast<const Expr *>()) {
        if (const auto *sl = dyn_cast<StringLiteral>(e))
          return ck(fir_init_global(m, stringGlobal(sl)), "fir_init_global");
        if (const auto *pe = dyn_cast<PredefinedExpr>(e))
          return ck(fir_init_global(m, stringGlobal(pe->getFunctionName())), "fir_init_global");
        if (const auto *cle = dyn_cast<CompoundLiteralExpr>(e))
          return ck(fir_init_global(m, litGlobal(cle)), "fir_init_global");
      }
      unsupported(loc, "this address in a global's initializer");
    }
    if (const auto *at = ctx.getAsConstantArrayType(c)) {
      if (!v.isArray())
        unsupported(loc, "this array initializer");
      uint64_t n = at->getSize().getZExtValue();
      std::vector<FirInit> items;
      FirInit filler = FIR_INVALID;
      for (uint64_t i = 0; i < n; i++) {
        if (i < v.getArrayInitializedElts()) {
          items.push_back(initFrom(v.getArrayInitializedElt(i), at->getElementType(), loc));
        } else {
          if (filler == FIR_INVALID)
            filler = v.hasArrayFiller() ? initFrom(v.getArrayFiller(), at->getElementType(), loc)
                                        : izero();
          items.push_back(filler);
        }
      }
      return ck(fir_init_list(m, items.data(), items.size()), "fir_init_list");
    }
    if (const RecordDecl *rd = c->getAsRecordDecl()) {
      RecordInfo &info = record(rd, loc);
      std::vector<uint8_t> image(info.size, 0);
      if (info.isUnion) {
        if (!v.isUnion())
          unsupported(loc, "this union initializer");
        if (const FieldDecl *f = v.getUnionField())
          storeBytes(v.getUnionValue(), f, info, image, 0, loc);
      } else {
        if (!v.isStruct())
          unsupported(loc, "this struct initializer");
        for (const FieldDecl *fd : rd->getDefinition()->fields())
          if (info.bits.count(fd))
            storeBytes(v.getStructField(fd->getFieldIndex()), fd, info, image, 0, loc);
      }
      std::vector<FirInit> items;
      for (const Slot &s : info.slots) {
        if (s.kind == Slot::Member) {
          items.push_back(
              initFrom(v.getStructField(s.field->getFieldIndex()), s.field->getType(), loc));
        } else if (s.kind == Slot::Pad) {
          items.push_back(bytesInit(image, s.offset, s.len));
        } else {
          items.push_back(izero());
        }
      }
      return ck(fir_init_list(m, items.data(), items.size()), "fir_init_list");
    }
    unsupported(loc, "initializers of type '" + t.getAsString() + "'");
  }

  FirInit bytesInit(const std::vector<uint8_t> &image, uint64_t off, uint64_t len) {
    bool any = false;
    for (uint64_t i = 0; i < len; i++)
      any |= image[off + i] != 0;
    if (!any)
      return izero();
    std::vector<FirInit> items;
    for (uint64_t i = 0; i < len; i++)
      items.push_back(iint(pattern(image[off + i], 8)));
    return ck(fir_init_list(m, items.data(), items.size()), "fir_init_list");
  }

  // A member's value into a record's byte image (`base` is the record's offset in it).
  void storeBytes(const APValue &v, const FieldDecl *fd, RecordInfo &info,
                  std::vector<uint8_t> &image, uint64_t base, SourceLocation loc) {
    auto bf = info.bits.find(fd);
    if (bf == info.bits.end()) {
      serialize(v, fd->getType(), image, base, loc);
      return;
    }
    if (!v.isInt())
      unsupported(loc, "this bitfield initializer");
    uint64_t x = v.getInt().getZExtValue();
    for (unsigned i = 0; i < bf->second.width; i++) {
      uint64_t bit = bf->second.bitOffset + i;
      if ((x >> i) & 1)
        image[base + bit / 8] |= (uint8_t)(1u << (bit % 8));
    }
  }

  // A constant's bytes, little-endian, at `off` in `image`: integers and null pointers only.
  void serialize(const APValue &v, QualType t, std::vector<uint8_t> &image, uint64_t off,
                 SourceLocation loc) {
    if (isZero(v))
      return;
    QualType c = t.getCanonicalType();
    if (c->isIntegerType() || c->isBooleanType()) {
      if (!v.isInt())
        unsupported(loc, "addresses used as integers in a global's initializer");
      uint64_t x = v.getInt().getZExtValue();
      for (unsigned i = 0; i < bits(c) / 8; i++)
        image[off + i] = (uint8_t)(x >> (8 * i));
      return;
    }
    if (const auto *at = ctx.getAsConstantArrayType(c)) {
      uint64_t stride = ctx.getTypeSizeInChars(at->getElementType()).getQuantity();
      for (uint64_t i = 0; i < at->getSize().getZExtValue(); i++) {
        const APValue &e =
            i < v.getArrayInitializedElts() ? v.getArrayInitializedElt(i) : v.getArrayFiller();
        serialize(e, at->getElementType(), image, off + i * stride, loc);
      }
      return;
    }
    if (const RecordDecl *rd = c->getAsRecordDecl()) {
      RecordInfo &info = record(rd, loc);
      if (info.isUnion) {
        if (const FieldDecl *f = v.getUnionField())
          storeBytes(v.getUnionValue(), f, info, image, off, loc);
        return;
      }
      const ASTRecordLayout &L = ctx.getASTRecordLayout(rd->getDefinition());
      for (const FieldDecl *fd : rd->getDefinition()->fields()) {
        if (info.bits.count(fd)) {
          storeBytes(v.getStructField(fd->getFieldIndex()), fd, info, image, off, loc);
        } else if (!fd->isBitField()) {
          serialize(v.getStructField(fd->getFieldIndex()), fd->getType(), image,
                    off + L.getFieldOffset(fd->getFieldIndex()) / 8, loc);
        }
      }
      return;
    }
    unsupported(loc, "pointers in a union's initializer");
  }

  void emitPendingInits() {
    while (!pendingVars.empty() || !pendingLits.empty()) {
      if (!pendingVars.empty()) {
        const VarDecl *vd = pendingVars.back();
        pendingVars.pop_back();
        try {
          FirGlobal g = globals.find(vd->getCanonicalDecl())->second; // made by globalFor
          if (const Expr *init = vd->getInit()) {
            const APValue *v = vd->evaluateValue();
            if (!v)
              unsupported(init->getBeginLoc(), "this global initializer (not a constant)");
            ok(fir_global_set_init(m, g, initFrom(*v, vd->getType(), init->getBeginLoc())),
               "fir_global_set_init");
          }
        } catch (Abort &) {
        }
        continue;
      }
      const CompoundLiteralExpr *cle = pendingLits.back();
      pendingLits.pop_back();
      try {
        Expr::EvalResult r;
        if (!cle->getInitializer()->EvaluateAsRValue(r, ctx, true))
          unsupported(cle->getBeginLoc(), "this compound literal's initializer (not a constant)");
        ok(fir_global_set_init(m, exprGlobals.find(cle)->second, // made by litGlobal
                               initFrom(r.Val, cle->getType(), cle->getBeginLoc())),
           "fir_global_set_init");
      } catch (Abort &) {
      }
    }
  }

  // Values.

  FirValue cint(FirType t, int64_t v) { return ck(fir_int_const(b, t, v), "fir_int_const"); }
  FirValue cbits(unsigned n, uint64_t v) { return cint(fir_type_int(n), pattern(v, n)); }
  FirValue i1(bool v) { return cint(fir_type_int(1), v ? 1 : 0); }

  // An integer of `from` bits converted to `to` bits.
  FirValue resize(FirValue v, unsigned from, unsigned to, bool sign) {
    if (from == to)
      return v;
    if (to < from)
      return ck(fir_int_trunc(b, fir_type_int(to), FIR_TRUNC_MODE_WRAP, v), "trunc");
    if (sign)
      return ck(fir_int_sext(b, fir_type_int(to), v), "sext");
    return ck(fir_int_zext(b, fir_type_int(to), v), "zext");
  }

  FirValue boolToInt(FirValue c, QualType to) { return resize(c, 1, bits(to), false); }

  // An integer or pointer value converted to another C scalar type, as C converts it.
  FirValue convert(FirValue v, QualType from, QualType to, SourceLocation loc) {
    from = from.getCanonicalType();
    to = to.getCanonicalType();
    if (to->isBooleanType()) {
      if (from->isBooleanType())
        return v;
      return boolToInt(truth(v, from), to);
    }
    if (to->isPointerType()) {
      if (from->isPointerType())
        return v;
      FirValue a = resize(v, bits(from), 64, isSigned(from));
      return ck(fir_ptr_from_exposed(b, a), "ptr.from_exposed");
    }
    if (to->isIntegerType()) {
      if (from->isPointerType()) {
        FirValue a = ck(fir_ptr_expose(b, v), "ptr.expose");
        return resize(a, 64, bits(to), false);
      }
      if (from->isIntegerType() || from->isBooleanType())
        return resize(v, bits(from), bits(to), isSigned(from));
    }
    unsupported(loc, "conversions from '" + from.getAsString() + "' to '" + to.getAsString() + "'");
  }

  // Whether a scalar is nonzero, as an `i1`.
  FirValue truth(FirValue v, QualType t) {
    if (t->isPointerType())
      return ck(fir_ptr_cmp(b, FIR_PRED_NE, v, ck(fir_ptr_null(b), "ptr.null")), "ptr.cmp");
    return ck(fir_int_cmp(b, FIR_PRED_NE, v, cbits(bits(t), 0)), "int.cmp");
  }

  FirValue load(QualType t, FirValue addr, SourceLocation loc) {
    return ck(fir_mem_load(b, scalarTy(t, loc), addr, alignOf(t)), "mem.load");
  }
  void store(QualType t, FirValue v, FirValue addr, SourceLocation loc) {
    ck(fir_mem_store(b, scalarTy(t, loc), v, addr, alignOf(t)), "mem.store");
  }

  FirValue offsetPtr(FirValue p, uint64_t off) {
    if (off == 0)
      return p;
    return ck(fir_ptr_offset(b, true, p, cbits(64, off)), "ptr.offset");
  }

  // Bitfields: the bytes they span, read and written one at a time (a byte that also holds
  // another member is written back unchanged; uninitialized bytes are frozen first).
  FirValue bitRead(FirValue base, const FieldDecl *fd) {
    const RecordInfo &info = record(fd->getParent(), fd->getLocation());
    BitField bf = info.bits.lookup(fd);
    uint64_t start = bf.bitOffset / 8;
    unsigned sh = bf.bitOffset % 8, n = (sh + bf.width + 7) / 8;
    FirType i64 = fir_type_int(64);
    FirValue acc = FIR_INVALID;
    for (unsigned k = 0; k < n; k++) {
      FirValue byte = ck(fir_mem_load(b, fir_type_int(8), offsetPtr(base, start + k), 1), "load");
      FirValue w = resize(byte, 8, 64, false);
      if (k)
        w = ck(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_UB, w, cint(i64, 8 * k)), "shl");
      acc = acc == FIR_INVALID ? w : ck(fir_int_bit(b, FIR_BIT_OP_OR, acc, w), "or");
    }
    QualType ft = fd->getType();
    if (isSigned(ft) && bf.width < 64) {
      unsigned up = 64 - bf.width - sh;
      if (up)
        acc = ck(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_UB, acc, cint(i64, up)), "shl");
      acc =
          ck(fir_int_shift(b, FIR_SHIFT_OP_SHR_S, FIR_SHIFT_EDGE_UB, acc, cint(i64, 64 - bf.width)),
             "shr");
    } else {
      if (sh)
        acc =
            ck(fir_int_shift(b, FIR_SHIFT_OP_SHR_U, FIR_SHIFT_EDGE_UB, acc, cint(i64, sh)), "shr");
      if (bf.width < 64)
        acc = ck(fir_int_bit(b, FIR_BIT_OP_AND, acc, cbits(64, (uint64_t(1) << bf.width) - 1)),
                 "and");
    }
    if (ft->isBooleanType())
      return resize(acc, 64, 8, false);
    return resize(acc, 64, bits(ft), false);
  }

  // Store `v` (of the field's declared type) into a bitfield; gives the value it now holds.
  FirValue bitWrite(FirValue base, const FieldDecl *fd, FirValue v) {
    const RecordInfo &info = record(fd->getParent(), fd->getLocation());
    BitField bf = info.bits.lookup(fd);
    uint64_t start = bf.bitOffset / 8;
    unsigned sh = bf.bitOffset % 8, n = (sh + bf.width + 7) / 8;
    FirType i64 = fir_type_int(64);
    QualType ft = fd->getType();
    unsigned fw = ft->isBooleanType() ? 8 : bits(ft);
    uint64_t mask = bf.width >= 64 ? ~uint64_t(0) : (uint64_t(1) << bf.width) - 1;
    FirValue acc = FIR_INVALID;
    std::vector<FirValue> ptrs;
    for (unsigned k = 0; k < n; k++) {
      ptrs.push_back(offsetPtr(base, start + k));
      FirValue byte =
          ck(fir_freeze(b, ck(fir_mem_load(b, fir_type_int(8), ptrs.back(), 1), "load")), "freeze");
      FirValue w = resize(byte, 8, 64, false);
      if (k)
        w = ck(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_UB, w, cint(i64, 8 * k)), "shl");
      acc = acc == FIR_INVALID ? w : ck(fir_int_bit(b, FIR_BIT_OP_OR, acc, w), "or");
    }
    FirValue x =
        ck(fir_int_bit(b, FIR_BIT_OP_AND, resize(v, fw, 64, false), cbits(64, mask)), "and");
    FirValue keep = cbits(64, ~(mask << sh));
    acc = ck(fir_int_bit(b, FIR_BIT_OP_AND, acc, keep), "and");
    FirValue placed =
        sh ? ck(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_UB, x, cint(i64, sh)), "shl") : x;
    acc = ck(fir_int_bit(b, FIR_BIT_OP_OR, acc, placed), "or");
    for (unsigned k = 0; k < n; k++) {
      FirValue w =
          k ? ck(fir_int_shift(b, FIR_SHIFT_OP_SHR_U, FIR_SHIFT_EDGE_UB, acc, cint(i64, 8 * k)),
                 "shr")
            : acc;
      ck(fir_mem_store(b, fir_type_int(8), resize(w, 64, 8, false), ptrs[k], 1), "store");
    }
    // The value the bitfield now holds.
    if (isSigned(ft) && bf.width < 64) {
      FirValue up =
          ck(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_UB, x, cint(i64, 64 - bf.width)),
             "shl");
      x = ck(fir_int_shift(b, FIR_SHIFT_OP_SHR_S, FIR_SHIFT_EDGE_UB, up, cint(i64, 64 - bf.width)),
             "shr");
    }
    return resize(x, 64, fw, false);
  }

  FirValue loadLV(const LValue &lv, QualType t, SourceLocation loc) {
    if (lv.bitfield)
      return bitRead(lv.addr, lv.bitfield);
    return load(t, lv.addr, loc);
  }
  FirValue storeLV(const LValue &lv, QualType t, FirValue v, SourceLocation loc) {
    if (lv.bitfield)
      return bitWrite(lv.addr, lv.bitfield, v);
    store(t, v, lv.addr, loc);
    return v;
  }

  // Expressions.

  bool foldInt(const Expr *e, uint64_t &out) {
    QualType t = e->getType();
    if (!(t->isIntegerType() || t->isBooleanType()))
      return false;
    if (e->isValueDependent())
      return false;
    Expr::EvalResult r;
    if (!e->EvaluateAsInt(r, ctx, Expr::SE_NoSideEffects) || r.HasUndefinedBehavior)
      return false;
    const llvm::APSInt &n = r.Val.getInt();
    out = n.isSigned() ? (uint64_t)n.getExtValue() : n.getZExtValue();
    return true;
  }

  // The value of a scalar expression (`FIR_INVALID` for a void one).
  FirValue rvalue(const Expr *e) {
    LocScope ls(*this, e->getExprLoc());
    uint64_t k;
    if (foldInt(e, k)) {
      if (e->getType()->isBooleanType())
        return cbits(8, k != 0);
      return cbits(bits(e->getType()), k);
    }
    e = e->IgnoreParens();
    if (const auto *ce = dyn_cast<ConstantExpr>(e))
      return rvalue(ce->getSubExpr());
    if (const auto *c = dyn_cast<CastExpr>(e))
      return castExpr(c);
    if (const auto *u = dyn_cast<UnaryOperator>(e))
      return unary(u);
    if (const auto *ca = dyn_cast<CompoundAssignOperator>(e))
      return compoundAssign(ca);
    if (const auto *bo = dyn_cast<BinaryOperator>(e))
      return binary(bo);
    if (const auto *co = dyn_cast<ConditionalOperator>(e))
      return conditional(co);
    if (const auto *call = dyn_cast<CallExpr>(e))
      return callExpr(call);
    if (const auto *g = dyn_cast<GenericSelectionExpr>(e))
      return rvalue(g->getResultExpr());
    if (const auto *ch = dyn_cast<ChooseExpr>(e))
      return rvalue(ch->getChosenSubExpr());
    if (const auto *ile = dyn_cast<InitListExpr>(e)) {
      if (ile->getNumInits() == 1 && isScalar(e->getType()))
        return rvalue(ile->getInit(0));
    }
    if (isa<ImplicitValueInitExpr>(e))
      return zeroOf(e->getType(), e->getExprLoc());
    if (isa<StmtExpr>(e))
      unsupported(e->getExprLoc(), "statement expressions");
    if (isa<AddrLabelExpr>(e))
      unsupported(e->getExprLoc(), "labels as values (computed 'goto')");
    if (isa<BinaryConditionalOperator>(e))
      unsupported(e->getExprLoc(), "'?:' without a middle operand");
    if (isa<VAArgExpr>(e))
      unsupported(e->getExprLoc(), "'va_arg' (track V)");
    if (isa<FloatingLiteral>(e))
      unsupported(e->getExprLoc(), "floating-point constants (track F2)");
    if (const auto *dre = dyn_cast<DeclRefExpr>(e)) {
      if (isa<FunctionDecl>(dre->getDecl()))
        return lvalue(e);
    }
    unsupported(e->getExprLoc(), std::string("the expression '") + e->getStmtClassName() + "'");
  }

  FirValue zeroOf(QualType t, SourceLocation loc) {
    if (t->isPointerType())
      return ck(fir_ptr_null(b), "ptr.null");
    return cint(scalarTy(t, loc), 0);
  }

  // Evaluate an expression for its effects.
  void discard(const Expr *e) {
    if (!e->HasSideEffects(ctx))
      return;
    LocScope ls(*this, e->getExprLoc());
    QualType t = e->getType();
    if (t->isVoidType() || isScalar(t)) {
      rvalue(e);
      return;
    }
    if (t->isRecordType() || t->isArrayType()) {
      aggAddr(e);
      return;
    }
    unsupported(e->getExprLoc(), "expressions of type '" + t.getAsString() + "'");
  }

  FirValue castExpr(const CastExpr *c) {
    const Expr *sub = c->getSubExpr();
    QualType to = c->getType(), from = sub->getType();
    SourceLocation loc = c->getExprLoc();
    switch (c->getCastKind()) {
    case CK_LValueToRValue: {
      if (!isScalar(to))
        unsupported(loc, "values of type '" + to.getAsString() + "' here");
      if (to.isVolatileQualified() || from.isVolatileQualified())
        unsupported(loc, "'volatile'");
      LValue lv = lvalueFull(sub);
      return loadLV(lv, to, loc);
    }
    case CK_NoOp:
    case CK_BitCast:
      if (isScalar(to) && isScalar(from))
        return rvalue(sub);
      break;
    case CK_IntegralCast:
    case CK_IntegralToBoolean:
    case CK_PointerToBoolean:
    case CK_PointerToIntegral:
    case CK_IntegralToPointer:
      return convert(rvalue(sub), from, to, loc);
    case CK_NullToPointer:
      discard(sub);
      return ck(fir_ptr_null(b), "ptr.null");
    case CK_ArrayToPointerDecay:
      return aggAddr(sub);
    case CK_FunctionToPointerDecay:
      return lvalue(sub);
    case CK_ToVoid:
      discard(sub);
      return FIR_INVALID;
    case CK_FloatingToIntegral:
    case CK_IntegralToFloating:
    case CK_FloatingCast:
    case CK_FloatingToBoolean:
      unsupported(loc, "floating-point conversions (track F2)");
    default:
      break;
    }
    unsupported(loc, std::string("the conversion '") + c->getCastKindName() + "'");
  }

  FirValue unary(const UnaryOperator *u) {
    const Expr *sub = u->getSubExpr();
    QualType t = u->getType();
    SourceLocation loc = u->getExprLoc();
    switch (u->getOpcode()) {
    case UO_Plus:
    case UO_Extension:
      return rvalue(sub);
    case UO_Minus: {
      FirValue x = rvalue(sub);
      return ck(fir_int_arith(b, FIR_ARITH_OP_SUB, isSigned(t) ? FIR_OVF_NSW : FIR_OVF_WRAP,
                              cbits(bits(t), 0), x),
                "int.sub");
    }
    case UO_Not:
      return ck(fir_int_bit(b, FIR_BIT_OP_XOR, rvalue(sub), cbits(bits(t), ~uint64_t(0))), "xor");
    case UO_LNot:
      return boolToInt(cond(u), t);
    case UO_AddrOf:
      return lvalue(sub);
    case UO_Deref:
      return loadLV(lvalueFull(u), t, loc);
    case UO_PreInc:
    case UO_PreDec:
    case UO_PostInc:
    case UO_PostDec: {
      QualType st = sub->getType();
      if (st->isBooleanType())
        unsupported(loc, "'++' and '--' on '_Bool'");
      LValue lv = lvalueFull(sub);
      FirValue old = loadLV(lv, st, loc);
      bool inc = u->isIncrementOp();
      FirValue nv;
      if (st->isPointerType()) {
        nv = ptrIndex(old, st->getPointeeType(), cbits(64, inc ? 1 : ~uint64_t(0)), loc);
      } else {
        // A type narrower than int is promoted, so the step can't overflow; it wraps when
        // converted back.
        bool nsw = isSigned(st) && bits(st) >= bits(ctx.IntTy);
        nv = ck(fir_int_arith(b, inc ? FIR_ARITH_OP_ADD : FIR_ARITH_OP_SUB,
                              nsw ? FIR_OVF_NSW : FIR_OVF_WRAP, old, cbits(bits(st), 1)),
                "int.add");
      }
      FirValue stored = storeLV(lv, st, nv, loc);
      return u->isPrefix() ? stored : old;
    }
    case UO_Real:
    case UO_Imag:
      unsupported(loc, "'__real__' and '__imag__'");
    default:
      break;
    }
    unsupported(loc, "this unary operator");
  }

  FirValue ptrIndex(FirValue p, QualType elem, FirValue idx64, SourceLocation loc) {
    if (elem->isVoidType() || elem->isFunctionType())
      unsupported(loc, "arithmetic on 'void *' or function pointers");
    return ck(fir_ptr_index(b, true, memTy(elem, loc), p, idx64), "ptr.index");
  }

  FirValue toIndex(FirValue v, QualType t) { return resize(v, bits(t), 64, isSigned(t)); }

  static bool isComparison(BinaryOperatorKind op) {
    return op == BO_LT || op == BO_GT || op == BO_LE || op == BO_GE || op == BO_EQ || op == BO_NE;
  }

  FirValue binary(const BinaryOperator *bo) {
    BinaryOperatorKind op = bo->getOpcode();
    const Expr *l = bo->getLHS(), *r = bo->getRHS();
    QualType t = bo->getType();
    SourceLocation loc = bo->getExprLoc();
    if (op == BO_Comma) {
      discard(l);
      if (t->isVoidType()) {
        discard(r);
        return FIR_INVALID;
      }
      return rvalue(r);
    }
    if (op == BO_Assign) {
      if (!isScalar(t)) {
        aggAddr(bo);
        return FIR_INVALID;
      }
      if (t.isVolatileQualified())
        unsupported(loc, "'volatile'");
      LValue lv = lvalueFull(l);
      FirValue v = rvalue(r);
      return storeLV(lv, l->getType(), v, loc);
    }
    if (op == BO_LAnd || op == BO_LOr || isComparison(op))
      return boolToInt(cond(bo), t);
    QualType lt = l->getType(), rt = r->getType();
    if (lt->isPointerType() && rt->isPointerType() && op == BO_Sub) {
      FirValue a = ck(fir_ptr_addr(b, rvalue(l)), "ptr.addr");
      FirValue c = ck(fir_ptr_addr(b, rvalue(r)), "ptr.addr");
      FirValue d = ck(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_WRAP, a, c), "int.sub");
      QualType elem = lt->getPointeeType();
      if (elem->isVoidType() || elem->isFunctionType())
        unsupported(loc, "arithmetic on 'void *' or function pointers");
      uint64_t size = ctx.getTypeSizeInChars(elem).getQuantity();
      FirValue q =
          size == 1
              ? d
              : ck(fir_int_div(b, FIR_DIV_OP_DIV_S, FIR_EDGE_UB, FIR_EDGE_UB, d, cbits(64, size)),
                   "int.div");
      return resize(q, 64, bits(t), true);
    }
    if (lt->isPointerType() || rt->isPointerType()) {
      bool lp = lt->isPointerType();
      FirValue p = rvalue(lp ? l : r);
      const Expr *ie = lp ? r : l;
      FirValue idx = toIndex(rvalue(ie), ie->getType());
      if (op == BO_Sub)
        idx = ck(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_NSW, cbits(64, 0), idx), "int.sub");
      else if (op != BO_Add)
        unsupported(loc, "this operator on pointers");
      return ptrIndex(p, (lp ? lt : rt)->getPointeeType(), idx, loc);
    }
    FirValue a = rvalue(l);
    FirValue c = rvalue(r);
    return arith(op, a, c, t, rt, loc);
  }

  // An integer operator, at the width of `t` (C's promotions and conversions are already in
  // the AST); `rt` is the right operand's type (shifts don't convert it).
  FirValue arith(BinaryOperatorKind op, FirValue a, FirValue c, QualType t, QualType rt,
                 SourceLocation loc) {
    if (!t->isIntegerType())
      unsupported(loc, "arithmetic on '" + t.getAsString() + "'");
    bool sgn = isSigned(t);
    switch (op) {
    case BO_Add:
    case BO_AddAssign:
      return ck(fir_int_arith(b, FIR_ARITH_OP_ADD, sgn ? FIR_OVF_NSW : FIR_OVF_WRAP, a, c), "add");
    case BO_Sub:
    case BO_SubAssign:
      return ck(fir_int_arith(b, FIR_ARITH_OP_SUB, sgn ? FIR_OVF_NSW : FIR_OVF_WRAP, a, c), "sub");
    case BO_Mul:
    case BO_MulAssign:
      return ck(fir_int_arith(b, FIR_ARITH_OP_MUL, sgn ? FIR_OVF_NSW : FIR_OVF_WRAP, a, c), "mul");
    case BO_Div:
    case BO_DivAssign:
      return ck(
          fir_int_div(b, sgn ? FIR_DIV_OP_DIV_S : FIR_DIV_OP_DIV_U, FIR_EDGE_UB, FIR_EDGE_UB, a, c),
          "div");
    case BO_Rem:
    case BO_RemAssign:
      return ck(
          fir_int_div(b, sgn ? FIR_DIV_OP_REM_S : FIR_DIV_OP_REM_U, FIR_EDGE_UB, FIR_EDGE_UB, a, c),
          "rem");
    case BO_And:
    case BO_AndAssign:
      return ck(fir_int_bit(b, FIR_BIT_OP_AND, a, c), "and");
    case BO_Or:
    case BO_OrAssign:
      return ck(fir_int_bit(b, FIR_BIT_OP_OR, a, c), "or");
    case BO_Xor:
    case BO_XorAssign:
      return ck(fir_int_bit(b, FIR_BIT_OP_XOR, a, c), "xor");
    case BO_Shl:
    case BO_ShlAssign:
    case BO_Shr:
    case BO_ShrAssign: {
      FirValue n = resize(c, bits(rt), bits(t), isSigned(rt));
      FirShiftOp so = (op == BO_Shl || op == BO_ShlAssign) ? FIR_SHIFT_OP_SHL
                      : sgn                                ? FIR_SHIFT_OP_SHR_S
                                                           : FIR_SHIFT_OP_SHR_U;
      return ck(fir_int_shift(b, so, FIR_SHIFT_EDGE_UB, a, n), "shift");
    }
    default:
      break;
    }
    unsupported(loc, "this operator");
  }

  FirValue compoundAssign(const CompoundAssignOperator *ca) {
    SourceLocation loc = ca->getExprLoc();
    const Expr *l = ca->getLHS(), *r = ca->getRHS();
    QualType lt = l->getType();
    if (lt.isVolatileQualified())
      unsupported(loc, "'volatile'");
    LValue lv = lvalueFull(l);
    FirValue old = loadLV(lv, lt, loc);
    FirValue nv;
    if (lt->isPointerType()) {
      FirValue idx = toIndex(rvalue(r), r->getType());
      if (ca->getOpcode() == BO_SubAssign)
        idx = ck(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_NSW, cbits(64, 0), idx), "int.sub");
      nv = ptrIndex(old, lt->getPointeeType(), idx, loc);
    } else {
      QualType ct = ca->getComputationLHSType(), rt = ca->getComputationResultType();
      FirValue a = convert(old, lt, ct, loc);
      FirValue c = rvalue(r);
      FirValue res = arith(ca->getOpcode(), a, c, rt, r->getType(), loc);
      nv = convert(res, rt, lt, loc);
    }
    return storeLV(lv, lt, nv, loc);
  }

  // `c ? a : b` on scalars, or void.
  FirValue conditional(const ConditionalOperator *co) {
    QualType t = co->getType();
    uint64_t k;
    if (foldInt(co->getCond(), k)) {
      const Expr *chosen = k ? co->getTrueExpr() : co->getFalseExpr();
      if (t->isVoidType()) {
        discard(chosen);
        return FIR_INVALID;
      }
      return rvalue(chosen);
    }
    FirValue c = cond(co->getCond());
    bool isVoid = t->isVoidType();
    FirType rt = isVoid ? FIR_INVALID : scalarTy(t, co->getExprLoc());
    FirOp op = ck(fir_cf_if_begin(b, &rt, isVoid ? 0 : 1, c), "cf.if");
    FirRegion saved = region;
    for (int i = 0; i < 2; i++) {
      enter(ck(fir_op_region(b, op, i), "region"));
      const Expr *arm = i == 0 ? co->getTrueExpr() : co->getFalseExpr();
      if (isVoid) {
        discard(arm);
        yield(nullptr, 0);
      } else {
        FirValue v = rvalue(arm);
        yield(&v, 1);
      }
    }
    enter(saved);
    return isVoid ? FIR_INVALID : ck(fir_op_result(b, op, 0), "result");
  }

  // A condition, as an `i1`.
  FirValue cond(const Expr *e) {
    LocScope ls(*this, e->getExprLoc());
    uint64_t k;
    if (foldInt(e, k))
      return i1(k != 0);
    e = e->IgnoreParens();
    if (const auto *u = dyn_cast<UnaryOperator>(e); u && u->getOpcode() == UO_LNot)
      return ck(fir_int_bit(b, FIR_BIT_OP_XOR, cond(u->getSubExpr()), i1(true)), "xor");
    if (const auto *bo = dyn_cast<BinaryOperator>(e)) {
      BinaryOperatorKind op = bo->getOpcode();
      if (op == BO_LAnd || op == BO_LOr) {
        FirValue c = cond(bo->getLHS());
        FirType i1t = fir_type_int(1);
        FirOp ifop = ck(fir_cf_if_begin(b, &i1t, 1, c), "cf.if");
        FirRegion saved = region;
        enter(ck(fir_op_region(b, ifop, 0), "region"));
        FirValue v = op == BO_LAnd ? cond(bo->getRHS()) : i1(true);
        yield(&v, 1);
        enter(ck(fir_op_region(b, ifop, 1), "region"));
        v = op == BO_LAnd ? i1(false) : cond(bo->getRHS());
        yield(&v, 1);
        enter(saved);
        return ck(fir_op_result(b, ifop, 0), "result");
      }
      if (isComparison(op)) {
        QualType lt = bo->getLHS()->getType();
        FirValue a = rvalue(bo->getLHS()), c = rvalue(bo->getRHS());
        bool sgn = !lt->isPointerType() && isSigned(lt);
        FirPred p;
        switch (op) {
        case BO_EQ:
          p = FIR_PRED_EQ;
          break;
        case BO_NE:
          p = FIR_PRED_NE;
          break;
        case BO_LT:
          p = sgn ? FIR_PRED_SLT : FIR_PRED_ULT;
          break;
        case BO_LE:
          p = sgn ? FIR_PRED_SLE : FIR_PRED_ULE;
          break;
        case BO_GT:
          p = sgn ? FIR_PRED_SGT : FIR_PRED_UGT;
          break;
        default:
          p = sgn ? FIR_PRED_SGE : FIR_PRED_UGE;
          break;
        }
        if (lt->isPointerType())
          return ck(fir_ptr_cmp(b, p, a, c), "ptr.cmp");
        return ck(fir_int_cmp(b, p, a, c), "int.cmp");
      }
    }
    QualType t = e->getType();
    if (!isScalar(t))
      unsupported(e->getExprLoc(), "conditions of type '" + t.getAsString() + "'");
    return truth(rvalue(e), t);
  }

  FirValue callExpr(const CallExpr *ce) {
    SourceLocation loc = ce->getExprLoc();
    QualType rt = ce->getType();
    if (rt->isRecordType())
      unsupported(loc, "structs and unions returned by value (track A)");
    const FunctionDecl *fd = ce->getDirectCallee();
    if (fd) {
      if (unsigned id = fd->getBuiltinID()) {
        if (id == Builtin::BI__builtin_expect ||
            id == Builtin::BI__builtin_expect_with_probability) {
          FirValue v = rvalue(ce->getArg(0));
          for (unsigned i = 1; i < ce->getNumArgs(); i++)
            discard(ce->getArg(i));
          return v;
        }
        if (id == Builtin::BImalloc && ce->getNumArgs() == 1) {
          FirValue n = rvalue(ce->getArg(0));
          return ck(fir_mem_alloc(b, FIR_ALLOC_FAIL_NULL, "c.malloc", n, 16), "mem.alloc");
        }
        if (id == Builtin::BIfree && ce->getNumArgs() == 1) {
          ck(fir_mem_free(b, "c.malloc", rvalue(ce->getArg(0))), "mem.free");
          return FIR_INVALID;
        }
        if (!ctx.BuiltinInfo.isPredefinedLibFunction(id))
          unsupported(loc, "the builtin '" + fd->getName().str() + "'");
      }
    }
    const FunctionType *ft = nullptr;
    QualType calleeTy = ce->getCallee()->getType();
    if (const auto *pt = calleeTy->getAs<PointerType>())
      ft = pt->getPointeeType()->getAs<FunctionType>();
    if (!ft)
      unsupported(loc, "this call");
    // C's default argument promotions don't match a definition's parameter types in general.
    if (isa<FunctionNoProtoType>(ft) && ce->getNumArgs() > 0)
      unsupported(loc, "calls with arguments to a function declared without a prototype");
    if (const auto *p = dyn_cast<FunctionProtoType>(ft); p && p->isVariadic())
      unsupported(loc, "calls to variadic functions (track V)");
    std::vector<FirValue> args;
    for (const Expr *a : ce->arguments()) {
      if (a->getType()->isRecordType())
        unsupported(a->getExprLoc(), "structs and unions passed by value (track A)");
      args.push_back(rvalue(a));
    }
    LocScope ls(*this, loc);
    FirOp op;
    if (fd) {
      op = ck(fir_func_call(b, funcFor(fd, loc), args.data(), args.size()), "func.call");
    } else {
      FirValue p = rvalue(ce->getCallee());
      op = ck(fir_func_call_indirect(b, funcTy(ft, loc), p, args.data(), args.size()),
              "func.call.indirect");
    }
    if (rt->isVoidType())
      return FIR_INVALID;
    return ck(fir_op_result(b, op, 0), "result");
  }

  // Lvalues: addresses.

  FirValue lvalue(const Expr *e) {
    LValue lv = lvalueFull(e);
    if (lv.bitfield)
      unsupported(e->getExprLoc(), "the address of a bitfield");
    return lv.addr;
  }

  LValue lvalueFull(const Expr *e) {
    LocScope ls(*this, e->getExprLoc());
    e = e->IgnoreParens();
    SourceLocation loc = e->getExprLoc();
    if (const auto *dre = dyn_cast<DeclRefExpr>(e)) {
      const ValueDecl *d = dre->getDecl();
      if (const auto *fd = dyn_cast<FunctionDecl>(d))
        return {ck(fir_func_addr(b, funcFor(fd, loc)), "func.addr")};
      if (const auto *vd = dyn_cast<VarDecl>(d)) {
        auto it = slots.find(vd);
        if (it != slots.end())
          return {it->second};
        if (vd->hasLocalStorage())
          unsupported(loc, "this local variable");
        return {ck(fir_mem_global(b, globalFor(vd, loc)), "mem.global")};
      }
      unsupported(loc, "this reference");
    }
    if (const auto *u = dyn_cast<UnaryOperator>(e)) {
      if (u->getOpcode() == UO_Deref)
        return {rvalue(u->getSubExpr())};
      if (u->getOpcode() == UO_Extension)
        return lvalueFull(u->getSubExpr());
    }
    if (const auto *me = dyn_cast<MemberExpr>(e)) {
      const auto *fd = dyn_cast<FieldDecl>(me->getMemberDecl());
      if (!fd)
        unsupported(loc, "this member");
      FirValue base = me->isArrow() ? rvalue(me->getBase()) : aggAddr(me->getBase());
      RecordInfo &info = record(fd->getParent(), loc);
      if (fd->isBitField())
        return {base, fd};
      if (info.isUnion)
        return {base};
      return {ck(fir_ptr_field(b, true, info.ty, base, info.index.lookup(fd)), "ptr.field")};
    }
    if (const auto *as = dyn_cast<ArraySubscriptExpr>(e)) {
      FirValue base = rvalue(as->getBase());
      const Expr *ie = as->getIdx();
      FirValue idx = toIndex(rvalue(ie), ie->getType());
      return {ptrIndex(base, as->getType(), idx, loc)};
    }
    if (const auto *sl = dyn_cast<StringLiteral>(e))
      return {ck(fir_mem_global(b, stringGlobal(sl)), "mem.global")};
    if (const auto *pe = dyn_cast<PredefinedExpr>(e))
      return {ck(fir_mem_global(b, stringGlobal(pe->getFunctionName())), "mem.global")};
    if (const auto *cle = dyn_cast<CompoundLiteralExpr>(e)) {
      if (cle->isFileScope())
        return {ck(fir_mem_global(b, litGlobal(cle)), "mem.global")};
      // FIR ids start at 0, so a missing entry can't be told from `lookup`'s default.
      auto it = litSlots.find(cle);
      if (it == litSlots.end())
        unsupported(loc, "this compound literal");
      initObject(it->second, cle->getType(), cle->getInitializer());
      return {it->second};
    }
    if (const auto *ce = dyn_cast<CastExpr>(e)) {
      if (ce->getCastKind() == CK_NoOp || ce->getCastKind() == CK_LValueBitCast)
        return lvalueFull(ce->getSubExpr());
    }
    if (const auto *g = dyn_cast<GenericSelectionExpr>(e))
      return lvalueFull(g->getResultExpr());
    if (const auto *ch = dyn_cast<ChooseExpr>(e))
      return lvalueFull(ch->getChosenSubExpr());
    if (e->getType()->isRecordType() || e->getType()->isArrayType())
      return {aggAddr(e)};
    unsupported(loc, std::string("this lvalue ('") + e->getStmtClassName() + "')");
  }

  // The address of an aggregate-valued expression (a struct, union, or array).
  FirValue aggAddr(const Expr *e) {
    LocScope ls(*this, e->getExprLoc());
    e = e->IgnoreParens();
    SourceLocation loc = e->getExprLoc();
    if (const auto *bo = dyn_cast<BinaryOperator>(e)) {
      if (bo->getOpcode() == BO_Assign) {
        FirValue dst = lvalue(bo->getLHS());
        FirValue src = aggAddr(bo->getRHS());
        copy(bo->getType(), dst, src, loc);
        return dst;
      }
      if (bo->getOpcode() == BO_Comma) {
        discard(bo->getLHS());
        return aggAddr(bo->getRHS());
      }
    }
    if (const auto *co = dyn_cast<ConditionalOperator>(e)) {
      FirValue c = cond(co->getCond());
      FirType pt = FIR_TYPE_PTR;
      FirOp op = ck(fir_cf_if_begin(b, &pt, 1, c), "cf.if");
      FirRegion saved = region;
      for (int i = 0; i < 2; i++) {
        enter(ck(fir_op_region(b, op, i), "region"));
        FirValue v = aggAddr(i == 0 ? co->getTrueExpr() : co->getFalseExpr());
        yield(&v, 1);
      }
      enter(saved);
      return ck(fir_op_result(b, op, 0), "result");
    }
    if (const auto *ce = dyn_cast<CastExpr>(e)) {
      if (ce->getCastKind() == CK_LValueToRValue || ce->getCastKind() == CK_NoOp)
        return aggAddr(ce->getSubExpr());
    }
    if (isa<CallExpr>(e))
      unsupported(loc, "structs and unions returned by value (track A)");
    if (isa<StmtExpr>(e))
      unsupported(loc, "statement expressions");
    if (isa<DeclRefExpr, MemberExpr, ArraySubscriptExpr, UnaryOperator, StringLiteral,
            CompoundLiteralExpr, PredefinedExpr, GenericSelectionExpr, ChooseExpr>(e))
      return lvalue(e);
    unsupported(loc, std::string("this aggregate expression ('") + e->getStmtClassName() + "')");
  }

  void copy(QualType t, FirValue dst, FirValue src, SourceLocation loc) {
    if (t.isVolatileQualified())
      unsupported(loc, "'volatile'");
    ck(fir_mem_copy(b, memTy(t, loc), dst, src, alignOf(t)), "mem.copy");
  }

  // Initialize the object of type `t` at `addr` from `init` (a declaration's initializer or a
  // compound literal's): members not named are zero.
  void initObject(FirValue addr, QualType t, const Expr *init) {
    LocScope ls(*this, init->getExprLoc());
    init = init->IgnoreParens();
    SourceLocation loc = init->getExprLoc();
    if (isScalar(t)) {
      const Expr *e = init;
      if (const auto *ile = dyn_cast<InitListExpr>(e)) {
        if (ile->getNumInits() == 0) {
          store(t, zeroOf(t, loc), addr, loc);
          return;
        }
        e = ile->getInit(0);
      }
      store(t, rvalue(e), addr, loc);
      return;
    }
    if (const auto *sl = dyn_cast<StringLiteral>(init)) {
      const auto *at = ctx.getAsConstantArrayType(t);
      if (!at)
        unsupported(loc, "this string initializer");
      FirGlobal g = bytesGlobal("init", at->getSize().getZExtValue(), sl, loc, true);
      copy(t, addr, ck(fir_mem_global(b, g), "mem.global"), loc);
      return;
    }
    if (const auto *ile = dyn_cast<InitListExpr>(init)) {
      if (ile->isStringLiteralInit()) {
        initObject(addr, t, ile->getInit(0));
        return;
      }
      if (needsZero(ile))
        copy(t, addr, ck(fir_mem_global(b, zeroGlobal(memTy(t, loc))), "mem.global"), loc);
      initList(addr, t, ile);
      return;
    }
    if (isa<ImplicitValueInitExpr>(init)) {
      copy(t, addr, ck(fir_mem_global(b, zeroGlobal(memTy(t, loc))), "mem.global"), loc);
      return;
    }
    // A whole struct or union from another one.
    copy(t, addr, aggAddr(init), loc);
  }

  // Whether an initializer list leaves something to zero.
  bool needsZero(const InitListExpr *ile) {
    if (ile->hasArrayFiller())
      return true;
    QualType t = ile->getType();
    if (t->isUnionType())
      return true;
    if (const auto *at = ctx.getAsConstantArrayType(t))
      if (ile->getNumInits() < at->getSize().getZExtValue())
        return true;
    if (const RecordDecl *rd = t->getAsRecordDecl()) {
      unsigned n = 0;
      for (const FieldDecl *fd : rd->getDefinition()->fields())
        if (!fd->isUnnamedBitField())
          n++;
      if (ile->getNumInits() < n)
        return true;
    }
    for (const Expr *e : ile->inits()) {
      e = e->IgnoreParens();
      if (isa<ImplicitValueInitExpr>(e))
        return true;
      if (const auto *sub = dyn_cast<InitListExpr>(e);
          sub && !sub->isStringLiteralInit() && needsZero(sub))
        return true;
      if (isa<StringLiteral>(e))
        return true;
    }
    return false;
  }

  // Store the named members (the object is already zero where needed).
  void initList(FirValue addr, QualType t, const InitListExpr *ile) {
    SourceLocation loc = ile->getExprLoc();
    auto member = [&](FirValue p, QualType mt, const Expr *e) {
      e = e->IgnoreParens();
      if (isa<ImplicitValueInitExpr>(e))
        return;
      if (const auto *sub = dyn_cast<InitListExpr>(e);
          sub && !isScalar(mt) && !sub->isStringLiteralInit()) {
        initList(p, mt, sub);
        return;
      }
      initObjectNoZero(p, mt, e);
    };
    if (const auto *at = ctx.getAsConstantArrayType(t)) {
      QualType et = at->getElementType();
      if (ile->hasArrayFiller() &&
          !isa<ImplicitValueInitExpr>(ile->getArrayFiller()->IgnoreParens()))
        unsupported(loc, "array fillers other than zero");
      for (unsigned i = 0; i < ile->getNumInits(); i++) {
        FirValue p = ptrIndex(addr, et, cbits(64, i), loc);
        member(p, et, ile->getInit(i));
      }
      return;
    }
    if (const RecordDecl *rd = t->getAsRecordDecl()) {
      RecordInfo &info = record(rd, loc);
      if (info.isUnion) {
        const FieldDecl *fd = ile->getInitializedFieldInUnion();
        if (!fd || ile->getNumInits() == 0)
          return;
        if (fd->isBitField()) {
          bitWrite(addr, fd, rvalue(ile->getInit(0)));
          return;
        }
        member(addr, fd->getType(), ile->getInit(0));
        return;
      }
      unsigned i = 0;
      for (const FieldDecl *fd : rd->getDefinition()->fields()) {
        if (fd->isUnnamedBitField())
          continue;
        if (i >= ile->getNumInits())
          break;
        const Expr *e = ile->getInit(i++);
        if (fd->isBitField()) {
          if (!isa<ImplicitValueInitExpr>(e->IgnoreParens()))
            bitWrite(addr, fd, rvalue(e));
          continue;
        }
        FirValue p = ck(fir_ptr_field(b, true, info.ty, addr, info.index.lookup(fd)), "ptr.field");
        member(p, fd->getType(), e);
      }
      return;
    }
    unsupported(loc, "this initializer list");
  }

  // `initObject` for a member, whose surrounding object was zeroed if needed.
  void initObjectNoZero(FirValue addr, QualType t, const Expr *e) {
    if (const auto *sl = dyn_cast<StringLiteral>(e->IgnoreParens())) {
      initObject(addr, t, sl);
      return;
    }
    if (const auto *ile = dyn_cast<InitListExpr>(e->IgnoreParens());
        ile && ile->isStringLiteralInit()) {
      initObject(addr, t, ile->getInit(0));
      return;
    }
    initObject(addr, t, e);
  }

  // Regions and terminators.

  void enter(FirRegion r) {
    ok(fir_position_at_end(b, r), "fir_position_at_end");
    region = r;
    term = false;
  }
  void yield(const FirValue *vs, size_t n) {
    ck(fir_cf_yield(b, vs, n), "cf.yield");
    term = true;
  }
  void br(FirRegion to) {
    FirTarget t = {to, nullptr, 0};
    ck(fir_cf_br(b, t), "cf.br");
    term = true;
  }
  FirRegion newBlock() {
    return ck(fir_block_new(b, blocksOp, nullptr, nullptr, 0), "fir_block_new");
  }
  // In CFG mode, code after a terminator goes into a block nothing jumps to (yet).
  void ensureOpen() {
    if (term && cfg)
      enter(newBlock());
  }

  void retFallOff() {
    QualType rt = curFn->getReturnType();
    if (rt->isVoidType()) {
      ck(fir_func_ret(b, nullptr, 0), "func.ret");
    } else {
      FirType t = scalarTy(rt, curFn->getLocation());
      FirValue v = curFn->isMain() ? cint(t, 0) : ck(fir_poison(b, t), "poison");
      ck(fir_func_ret(b, &v, 1), "func.ret");
    }
    term = true;
  }

  // Statements.

  void stmt(const Stmt *s) {
    if (!s)
      return;
    if (term && !cfg)
      return; // unreachable, and no label can reach it
    ensureOpen();
    LocScope ls(*this, s->getBeginLoc());
    SourceLocation loc = s->getBeginLoc();
    if (const auto *e = dyn_cast<Expr>(s)) {
      discard(e);
      return;
    }
    switch (s->getStmtClass()) {
    case Stmt::NullStmtClass:
      return;
    case Stmt::CompoundStmtClass:
      for (const Stmt *c : cast<CompoundStmt>(s)->body())
        stmt(c);
      return;
    case Stmt::DeclStmtClass:
      for (const Decl *d : cast<DeclStmt>(s)->decls())
        decl(d);
      return;
    case Stmt::ReturnStmtClass: {
      const Expr *e = cast<ReturnStmt>(s)->getRetValue();
      if (e && e->getType()->isRecordType())
        unsupported(loc, "structs and unions returned by value (track A)");
      if (e && !curFn->getReturnType()->isVoidType()) {
        FirValue v = rvalue(e);
        ck(fir_func_ret(b, &v, 1), "func.ret");
      } else {
        if (e)
          discard(e);
        ck(fir_func_ret(b, nullptr, 0), "func.ret");
      }
      term = true;
      return;
    }
    case Stmt::IfStmtClass:
      return ifStmt(cast<IfStmt>(s));
    case Stmt::WhileStmtClass: {
      const auto *w = cast<WhileStmt>(s);
      return loop(nullptr, w->getCond(), nullptr, w->getBody(), false);
    }
    case Stmt::DoStmtClass: {
      const auto *d = cast<DoStmt>(s);
      return loop(nullptr, d->getCond(), nullptr, d->getBody(), true);
    }
    case Stmt::ForStmtClass: {
      const auto *f = cast<ForStmt>(s);
      return loop(f->getInit(), f->getCond(), f->getInc(), f->getBody(), false);
    }
    case Stmt::BreakStmtClass: {
      if (jumps.empty())
        unsupported(loc, "'break' here");
      const Jump &j = jumps.back();
      if (cfg || !j.isLoop) {
        br(j.breakBlock);
      } else {
        ck(fir_cf_break(b, nullptr, 0), "cf.break");
        term = true;
      }
      return;
    }
    case Stmt::ContinueStmtClass: {
      for (auto it = jumps.rbegin(); it != jumps.rend(); ++it) {
        if (!it->isLoop)
          continue;
        if (cfg)
          br(it->continueBlock);
        else
          it->onContinue();
        return;
      }
      unsupported(loc, "'continue' here");
    }
    case Stmt::SwitchStmtClass:
      return switchStmt(cast<SwitchStmt>(s));
    case Stmt::CaseStmtClass:
    case Stmt::DefaultStmtClass: {
      const auto *sc = cast<SwitchCase>(s);
      auto it = caseBlocks.find(sc);
      if (!cfg || it == caseBlocks.end())
        unsupported(loc, "this case label");
      if (!term)
        br(it->second);
      enter(it->second);
      return stmt(sc->getSubStmt());
    }
    case Stmt::LabelStmtClass: {
      const auto *ls2 = cast<LabelStmt>(s);
      FirRegion blk = labelBlock(ls2->getDecl());
      if (!term)
        br(blk);
      enter(blk);
      return stmt(ls2->getSubStmt());
    }
    case Stmt::GotoStmtClass:
      br(labelBlock(cast<GotoStmt>(s)->getLabel()));
      return;
    case Stmt::IndirectGotoStmtClass:
      unsupported(loc, "computed 'goto'");
    case Stmt::AttributedStmtClass:
      return stmt(cast<AttributedStmt>(s)->getSubStmt());
    case Stmt::GCCAsmStmtClass:
    case Stmt::MSAsmStmtClass:
      unsupported(loc, "inline assembly");
    default:
      unsupported(loc, std::string("the statement '") + s->getStmtClassName() + "'");
    }
  }

  FirRegion labelBlock(const LabelDecl *ld) {
    auto it = labels.find(ld);
    if (it != labels.end())
      return it->second;
    FirRegion r = newBlock();
    labels[ld] = r;
    return r;
  }

  void decl(const Decl *d) {
    const auto *vd = dyn_cast<VarDecl>(d);
    if (!vd) {
      if (isa<TypedefNameDecl, RecordDecl, EnumDecl, FunctionDecl, StaticAssertDecl,
              EnumConstantDecl>(d))
        return;
      unsupported(d->getLocation(), "this declaration");
    }
    LocScope ls(*this, vd->getLocation());
    if (vd->getType()->isVariablyModifiedType())
      unsupported(vd->getLocation(), "variable-length arrays");
    if (!vd->hasLocalStorage()) {
      if (vd->isStaticLocal())
        globalFor(vd, vd->getLocation());
      return;
    }
    if (const Expr *init = vd->getInit()) {
      auto it = slots.find(vd);
      if (it == slots.end())
        unsupported(vd->getLocation(), "this local variable");
      initObject(it->second, vd->getType(), init);
    }
  }

  void ifStmt(const IfStmt *s) {
    if (s->getInit() || s->getConditionVariable())
      unsupported(s->getBeginLoc(), "this 'if'");
    if (cfg) {
      FirValue c = cond(s->getCond());
      FirRegion t = newBlock(), join = newBlock();
      FirRegion f = s->getElse() ? newBlock() : join;
      FirTarget tt = {t, nullptr, 0}, ft = {f, nullptr, 0};
      ck(fir_cf_cond_br(b, c, tt, ft), "cf.cond_br");
      term = true;
      enter(t);
      stmt(s->getThen());
      if (!term)
        br(join);
      if (s->getElse()) {
        enter(f);
        stmt(s->getElse());
        if (!term)
          br(join);
      }
      enter(join);
      return;
    }
    FirValue c = cond(s->getCond());
    FirOp op = ck(fir_cf_if_begin(b, nullptr, 0, c), "cf.if");
    FirRegion saved = region;
    enter(ck(fir_op_region(b, op, 0), "region"));
    stmt(s->getThen());
    if (!term)
      yield(nullptr, 0);
    enter(ck(fir_op_region(b, op, 1), "region"));
    stmt(s->getElse());
    if (!term)
      yield(nullptr, 0);
    enter(saved);
  }

  // `while`, `do`, and `for`.
  void loop(const Stmt *init, const Expr *c, const Expr *inc, const Stmt *body, bool isDo) {
    stmt(init);
    ensureOpen();
    uint64_t k;
    bool always = !c || (foldInt(c, k) && k != 0);
    if (cfg) {
      FirRegion head = newBlock(), bodyB = newBlock(), next = newBlock(), exit = newBlock();
      // head: test; body; next: the step (for) or test (do); exit.
      br(isDo ? bodyB : head);
      enter(head);
      condJump(c, always, bodyB, exit);
      enter(bodyB);
      jumps.push_back({true, nullptr, exit, next});
      stmt(body);
      jumps.pop_back();
      if (!term)
        br(next);
      enter(next);
      if (inc)
        discard(inc);
      if (isDo)
        condJump(c, always, bodyB, exit);
      else
        br(head);
      enter(exit);
      return;
    }
    FirOp op = ck(fir_cf_loop_begin(b, nullptr, 0, false, nullptr, 0), "cf.loop");
    FirRegion saved = region;
    FirRegion r = ck(fir_op_region(b, op, 0), "region");
    enter(r);
    // Leave the loop unless `c` holds.
    auto test = [&]() {
      if (always)
        return;
      FirValue v = cond(c);
      FirOp ifop = ck(fir_cf_if_begin(b, nullptr, 0, v), "cf.if");
      FirRegion here = region;
      enter(ck(fir_op_region(b, ifop, 0), "region"));
      yield(nullptr, 0);
      enter(ck(fir_op_region(b, ifop, 1), "region"));
      ck(fir_cf_break(b, nullptr, 0), "cf.break");
      enter(here);
    };
    auto cont = [&, this]() {
      if (inc)
        discard(inc);
      if (isDo)
        test();
      ck(fir_cf_continue(b, nullptr, 0), "cf.continue");
      term = true;
    };
    if (!isDo)
      test();
    jumps.push_back({true, cont, FIR_INVALID, FIR_INVALID});
    stmt(body);
    jumps.pop_back();
    if (!term)
      cont();
    enter(saved);
  }

  void condJump(const Expr *c, bool always, FirRegion t, FirRegion f) {
    if (always) {
      br(t);
      return;
    }
    FirValue v = cond(c);
    FirTarget tt = {t, nullptr, 0}, ft = {f, nullptr, 0};
    ck(fir_cf_cond_br(b, v, tt, ft), "cf.cond_br");
    term = true;
  }

  // The statements of a switch body at its top level, with their case labels peeled.
  struct Segment {
    std::vector<const SwitchCase *> cases;
    std::vector<const Stmt *> stmts;
  };

  static std::vector<Segment> segments(const Stmt *body) {
    std::vector<Segment> segs(1);
    auto add = [&](const Stmt *s) {
      bool labelled = false;
      while (const auto *sc = dyn_cast<SwitchCase>(s)) {
        if (!labelled)
          segs.push_back({});
        labelled = true;
        segs.back().cases.push_back(sc);
        s = sc->getSubStmt();
      }
      segs.back().stmts.push_back(s);
    };
    if (const auto *cs = dyn_cast<CompoundStmt>(body)) {
      for (const Stmt *s : cs->body())
        add(s);
    } else {
      add(body);
    }
    return segs;
  }

  // A switch's case labels are all at the top level of its body.
  static bool structuredSwitch(const SwitchStmt *s) {
    std::set<const SwitchCase *> top;
    for (const Segment &seg : segments(s->getBody()))
      for (const SwitchCase *c : seg.cases)
        top.insert(c);
    for (const SwitchCase *c = s->getSwitchCaseList(); c; c = c->getNextSwitchCase())
      if (!top.count(c))
        return false;
    return true;
  }

  void caseKeys(const SwitchCase *sc, FirRegion to, std::vector<FirCase> &cases, FirRegion &dflt) {
    if (isa<DefaultStmt>(sc)) {
      dflt = to;
      return;
    }
    const auto *cs = cast<CaseStmt>(sc);
    llvm::APSInt lo = cs->getLHS()->EvaluateKnownConstInt(ctx);
    llvm::APSInt hi = cs->getRHS() ? cs->getRHS()->EvaluateKnownConstInt(ctx) : lo;
    if ((hi - lo).getZExtValue() > 1024)
      unsupported(cs->getBeginLoc(), "case ranges over 1024 values");
    for (llvm::APSInt v = lo;; ++v) {
      cases.push_back({v.getExtValue(), {to, nullptr, 0}});
      if (v == hi)
        break;
    }
  }

  void switchStmt(const SwitchStmt *s) {
    SourceLocation loc = s->getBeginLoc();
    if (s->getInit() || s->getConditionVariable())
      unsupported(loc, "this 'switch'");
    FirValue x = rvalue(s->getCond());
    std::vector<FirCase> cases;
    FirRegion dflt = FIR_INVALID;
    if (cfg) {
      FirRegion exit = newBlock();
      for (const SwitchCase *c = s->getSwitchCaseList(); c; c = c->getNextSwitchCase()) {
        FirRegion blk = newBlock();
        caseBlocks[c] = blk;
        caseKeys(c, blk, cases, dflt);
      }
      FirTarget d = {dflt == FIR_INVALID ? exit : dflt, nullptr, 0};
      ck(fir_cf_switch(b, x, d, cases.data(), cases.size()), "cf.switch");
      term = true;
      jumps.push_back({false, nullptr, exit, FIR_INVALID});
      stmt(s->getBody());
      jumps.pop_back();
      if (!term)
        br(exit);
      enter(exit);
      return;
    }
    std::vector<Segment> segs = segments(s->getBody());
    FirOp op = ck(fir_cf_blocks_begin(b, nullptr, 0, false), "cf.blocks");
    FirOp savedOp = blocksOp;
    blocksOp = op;
    FirRegion saved = region;
    FirRegion entry = newBlock();
    std::vector<FirRegion> blocks;
    for (size_t i = 0; i < segs.size(); i++)
      blocks.push_back(newBlock());
    FirRegion exit = newBlock();
    for (size_t i = 1; i < segs.size(); i++)
      for (const SwitchCase *c : segs[i].cases)
        caseKeys(c, blocks[i], cases, dflt);
    enter(entry);
    FirTarget d = {dflt == FIR_INVALID ? exit : dflt, nullptr, 0};
    ck(fir_cf_switch(b, x, d, cases.data(), cases.size()), "cf.switch");
    term = true;
    jumps.push_back({false, nullptr, exit, FIR_INVALID});
    for (size_t i = 0; i < segs.size(); i++) {
      enter(blocks[i]);
      for (const Stmt *st : segs[i].stmts)
        stmt(st);
      if (!term)
        br(i + 1 < segs.size() ? blocks[i + 1] : exit);
    }
    jumps.pop_back();
    enter(exit);
    yield(nullptr, 0);
    ok(fir_blocks_end(b, op), "fir_blocks_end");
    blocksOp = savedOp;
    enter(saved);
  }

  // Whether a function needs basic blocks: `goto`, labels, or a switch with nested cases.
  static bool needsCFG(const Stmt *s) {
    if (!s)
      return false;
    if (isa<LabelStmt, GotoStmt, IndirectGotoStmt>(s))
      return true;
    if (const auto *sw = dyn_cast<SwitchStmt>(s); sw && !structuredSwitch(sw))
      return true;
    for (const Stmt *c : s->children())
      if (needsCFG(c))
        return true;
    return false;
  }

  // The automatic objects of a body: locals and compound literals.
  void collectSlots(const Stmt *s) {
    if (!s)
      return;
    if (const auto *ds = dyn_cast<DeclStmt>(s)) {
      for (const Decl *d : ds->decls()) {
        const auto *vd = dyn_cast<VarDecl>(d);
        if (!vd || !vd->hasLocalStorage())
          continue;
        if (vd->getType()->isVariablyModifiedType())
          unsupported(vd->getLocation(), "variable-length arrays");
        LocScope ls(*this, vd->getLocation());
        FirValue slot = ck(fir_mem_stack_of(b, memTy(vd->getType(), vd->getLocation()),
                                            (uint32_t)ctx.getDeclAlign(vd).getQuantity()),
                           "mem.stack.of");
        nameValue(slot, vd->getName());
        slots[vd] = slot;
      }
    }
    if (const auto *cle = dyn_cast<CompoundLiteralExpr>(s); cle && !cle->isFileScope()) {
      LocScope ls(*this, cle->getBeginLoc());
      litSlots[cle] = ck(
          fir_mem_stack_of(b, memTy(cle->getType(), cle->getBeginLoc()), alignOf(cle->getType())),
          "mem.stack.of");
    }
    for (const Stmt *c : s->children())
      collectSlots(c);
  }

  void function(const FunctionDecl *fd) {
    if (!fd->hasWrittenPrototype() && fd->getNumParams() > 0) {
      report(fd->getLocation(), "fai-cc does not support old-style (K&R) function definitions yet");
      return;
    }
    FirFunc f = funcFor(fd, fd->getLocation());
    b = fir_func_begin(m, f);
    if (!b) {
      report(fd->getLocation(),
             std::string("internal error: fir_func_begin: ") + fir_module_error(m));
      return;
    }
    curFn = fd;
    slots.clear();
    litSlots.clear();
    labels.clear();
    caseBlocks.clear();
    jumps.clear();
    valueNames.clear();
    blocksOp = FIR_INVALID;
    term = false;
    try {
      lowerBody(fd);
      FirBuilder *done = b;
      b = nullptr;
      if (fir_func_end(done) != FIR_OK)
        internal("fir_func_end");
    } catch (Abort &) {
      if (b)
        fir_func_abandon(b);
    }
    b = nullptr;
    curFn = nullptr;
    curLoc = SourceLocation();
  }

  void lowerBody(const FunctionDecl *fd) {
    {
      PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(fd->getLocation()));
      if (p.isValid())
        ok(fir_set_file(b, p.getFilename()), "fir_set_file");
      LocScope ls(*this, fd->getLocation());
      region = fir_builder_entry(b);
      for (unsigned i = 0; i < fd->getNumParams(); i++) {
        const ParmVarDecl *pd = fd->getParamDecl(i);
        LocScope pl(*this, pd->getLocation());
        FirValue v = ck(fir_builder_param(b, i), "param");
        nameValue(v, pd->getName());
        FirValue slot = ck(fir_mem_stack_of(b, memTy(pd->getType(), pd->getLocation()),
                                            (uint32_t)ctx.getDeclAlign(pd).getQuantity()),
                           "mem.stack.of");
        nameValue(slot, (pd->getName() + ".addr").str());
        store(pd->getType(), v, slot, pd->getLocation());
        slots[pd] = slot;
      }
      const Stmt *body = fd->getBody();
      collectSlots(body);
      cfg = needsCFG(body);
      if (cfg) {
        blocksOp = ck(fir_cf_blocks_begin(b, nullptr, 0, false), "cf.blocks");
        FirRegion entry = fir_builder_entry(b);
        enter(newBlock());
        stmt(body);
        if (!term)
          retFallOff();
        ok(fir_blocks_end(b, blocksOp), "fir_blocks_end");
        enter(entry);
        retFallOff(); // unreachable: every block returns or jumps
      } else {
        stmt(body);
        if (!term) {
          LocScope el(*this, cast<CompoundStmt>(body)->getRBracLoc());
          retFallOff();
        }
      }
    }
  }
};

bool Lowerer::run() {
  // AArch64's data layout is FIR's default one (64-bit pointers, naturally aligned integers).
  const TranslationUnitDecl *tu = ctx.getTranslationUnitDecl();
  std::vector<const FunctionDecl *> bodies;
  // Declare every function defined here first, so calls and addresses find them.
  for (const Decl *d : tu->decls()) {
    if (const auto *fd = dyn_cast<FunctionDecl>(d)) {
      if (fd->doesThisDeclarationHaveABody()) {
        bodies.push_back(fd);
        try {
          funcFor(fd, fd->getLocation());
        } catch (Abort &) {
        }
      }
    } else if (const auto *vd = dyn_cast<VarDecl>(d)) {
      if (vd->isThisDeclarationADefinition() != VarDecl::DeclarationOnly) {
        try {
          globalFor(vd, vd->getLocation());
        } catch (Abort &) {
        }
      }
    }
  }
  for (const FunctionDecl *fd : bodies) {
    if (!funcs.count(fd->getCanonicalDecl()))
      continue;
    function(fd);
  }
  emitPendingInits();
  return !failed;
}

} // namespace

bool lowerTranslationUnit(ASTContext &ctx, FirModule *m) {
  Lowerer l(ctx, m);
  return l.run();
}

} // namespace fai
