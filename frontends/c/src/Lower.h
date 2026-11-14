// fcc: lowering Clang's AST of a C translation unit to HFIR, through FIR's C API only.
#pragma once

#include "fir.h"

#include <string>

namespace clang {
class ASTContext;
}

namespace fai {

// Lower the translation unit into `m` (an empty module). Unsupported C is reported through the
// context's diagnostics, with its source location; returns whether everything was lowered.
// `salt` (the command line) goes into the names of the file's internal symbols, with its path.
bool lowerTranslationUnit(clang::ASTContext &ctx, FirModule *m, const std::string &salt);

} // namespace fai
