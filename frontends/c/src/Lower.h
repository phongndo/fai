// fai-cc: lowering Clang's AST of a C translation unit to HFIR, through FIR's C API only.
#pragma once

#include "fir.h"

namespace clang {
class ASTContext;
}

namespace fai {

// Lower the translation unit into `m` (an empty module). Unsupported C is reported through the
// context's diagnostics, with its source location; returns whether everything was lowered.
bool lowerTranslationUnit(clang::ASTContext &ctx, FirModule *m);

} // namespace fai
