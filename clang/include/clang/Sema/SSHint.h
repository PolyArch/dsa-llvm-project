//===--- SSHint.h - Types for LoopHint ------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_SEMA_SSHINT_H
#define LLVM_CLANG_SEMA_SSHINT_H

#include "clang/Basic/IdentifierTable.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Lex/Token.h"
#include "clang/Sema/Ownership.h"
#include "clang/Sema/ParsedAttr.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

namespace clang {


/// Loop optimization hint for loop and unroll pragmas.
struct SSHint {
  // Source range of the directive.
  SourceRange Range;
  // Identifier corresponding to the name of the pragma.
  // Either "stream" or "dfg"
  IdentifierLoc *PragmaNameLoc;
  // Dependence and unroll clauses.
  SmallVector<std::pair<Token, Expr*>, 0> Clauses;

  SSHint() : Range(), PragmaNameLoc(nullptr), Clauses() {}
};

} // end namespace clang

#endif // LLVM_CLANG_SEMA_SSHINT_H
