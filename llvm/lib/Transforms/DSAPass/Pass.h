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

#include "Util.h"

using namespace llvm;


struct StreamSpecialize : public ModulePass {

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
  dsa::RegisterFile DSARegs;

  static char ID;

  StreamSpecialize() : ModulePass(ID) {}

  bool runOnFunction(Function &F);

  // {
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  // }

  void HandleMemIntrin(Function &F);

};

#endif
