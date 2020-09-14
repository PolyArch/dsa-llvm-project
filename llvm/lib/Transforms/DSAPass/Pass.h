#ifndef STREAM_SPECIALIZE_H_
#define STREAM_SPECIALIZE_H_

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/DDG.h"
#include "llvm/Analysis/MemorySSA.h"

using namespace llvm;

#define DEFINE_FLAG(x, default_) \
  int64_t x{default_};           \
  void getFlag##x() {            \
    char *env = getenv(#x);      \
    if (env)                     \
      x = std::stol(env);        \
  }

struct ModuleFlags {

  DEFINE_FLAG(IND, 1)
  DEFINE_FLAG(REC, 1)
  DEFINE_FLAG(PRED, 1)
  DEFINE_FLAG(TEMPORAL, 1)
  DEFINE_FLAG(TRIGGER, 0)
  DEFINE_FLAG(EXTRACT, 0)

  void InitFlags() {
    getFlagIND();
    getFlagREC();
    getFlagPRED();
    getFlagTEMPORAL();
    getFlagTRIGGER();
    getFlagEXTRACT();
  }

};

#undef DEFINE_FLAG

struct StreamSpecialize : public FunctionPass {

  ModuleFlags MF;

  AssumptionCache *ACT;
  LoopInfo *LI;
  ScalarEvolution *SE;
  TargetLibraryInfo *TLI;
  DominatorTree *DT;
  AAResults *AAR;
  DDGInfo *DI;
  BlockFrequencyInfo *BFI;
  MemorySSA *MSSA;

  IRBuilder<> *IBPtr{nullptr};

  static char ID;

  StreamSpecialize() : FunctionPass(ID) {
    MF.InitFlags();
  }

  // {
  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  // }

  void HandleMemIntrin(Function &F);

};

#endif
