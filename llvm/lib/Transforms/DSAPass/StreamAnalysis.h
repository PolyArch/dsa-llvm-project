#pragma once

#include <map>
#include <memory>
#include <set>
#include <vector>
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/Casting.h"
#include "Util.h"
#include "DfgEntry.h"
#include "Pass.h"

namespace dsa {
namespace analysis {

struct Dimension {
  enum Type {
    Invariant,
    Affined,
    Unknown
  };
  Type Ty;
  ScalarEvolution *Stride;
  ScalarEvolution *TripCount;
};

void AnalyzeIndexExpr(ScalarEvolution *SE, Value *Index, std::vector<Loop*> LoopNest);

}
}