#include <cstdlib>
#include <sstream>
#include <fstream>
#include <queue>
#include <map>

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Support/Format.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

#include "DfgEntry.h"
#include "Transformation.h"
#include "Util.h"
#include "Pass.h"

using namespace llvm;

#define DEBUG_TYPE "stream-specialize"

void EliminateTemporal(Function &F) {
  std::vector<Instruction*> ToRemove;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto Intrin = dyn_cast<IntrinsicInst>(&I);
      if (!Intrin)
        continue;
      switch (Intrin->getIntrinsicID()) {
      case Intrinsic::ss_temporal_region_start:
      case Intrinsic::ss_temporal_region_end:
        ToRemove.push_back(Intrin);
        break;
      default:
        break;
      }
    }
  }

  for (auto I : ToRemove) {
    I->replaceAllUsesWith(UndefValue::get(I->getType()));
    I->eraseFromParent();
  }
}

std::vector<std::pair<IntrinsicInst*, IntrinsicInst*>>
GatherIntrinPairs(Function &F, llvm::Intrinsic::ID Kind) {
  std::vector<std::pair<IntrinsicInst*, IntrinsicInst*>> Res;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto Start = dyn_cast<IntrinsicInst>(&I);
      if (!Start || Start->getIntrinsicID() != Kind)
        continue;
      for (auto &AnotherBB : F) {
        for (auto &AntherI : AnotherBB) {
          auto End = dyn_cast<IntrinsicInst>(&AntherI);
          if (!End || End->getOperand(0) != Start)
            continue;
          Res.emplace_back(Start, End);
        }
      }
    }
  }
  return Res;
}

bool StreamSpecialize::runOnFunction(Function &F) {

  if (!MF.TEMPORAL) {
    EliminateTemporal(F);
  }

  LLVM_DEBUG(dbgs() << "Working on " << F.getName() << "\n");
  ACT = &getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
  LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  AAR = &getAnalysis<AAResultsWrapperPass>().getAAResults();
  BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
  MSSA = &getAnalysis<MemorySSAWrapperPass>().getMSSA();

  IRBuilder<> IB(F.getContext());
  IBPtr = &IB;

  {
    int Cnt = 0;
    auto ScopePairs = GatherIntrinPairs(F, Intrinsic::ss_config_start);
    for (auto &Pair : ScopePairs) {
      std::ostringstream OSS;
      OSS << F.getName().bytes_begin() << "_dfg_" << Cnt++ << ".dfg";
      DfgFile DFG(OSS.str(), F, Pair.first, Pair.second, this);
      DFG.InspectSPADs();
      DFG.InitAllDfgs();
      DFG.EmitAndScheduleDfg();
      DFG.InjectStreamIntrinsics();
      if (MF.EXTRACT) {
        DFG.EmitAndScheduleDfg();
        continue;
      }
      DFG.EraseOffloadedInstructions();
    }
    for (auto &Pair : ScopePairs) {
      Pair.second->eraseFromParent();
      Pair.first->eraseFromParent();
    }
  }

  HandleMemIntrin(F);

  LLVM_DEBUG(
    llvm::errs() << "After transformation:\n";
    F.dump()
  );

  return false;
}

void StreamSpecialize::HandleMemIntrin(Function &F) {
  DfgFile Dummy("dummy", F, nullptr, nullptr, this);
  std::vector<IntrinsicInst*> ToInject;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto Intrin = dyn_cast<IntrinsicInst>(&I);
      if (!Intrin)
        continue;
      if (Intrin->getIntrinsicID() == Intrinsic::memcpy) {
        ToInject.push_back(Intrin);
      }
    }
  }

  for (auto Intrin : ToInject) {
    Value *Dst = Intrin->getOperand(0);
    Value *Src = Intrin->getOperand(1);
    Value *Size = Intrin->getOperand(2);

    AnalyzedStream AS0;
    AnalyzedStream AS1;

    AS0.Dimensions.emplace_back(Dst, Size, 0);
    AS1.Dimensions.emplace_back(Src, Size, 0);

    IntrinDfg Dfg(Dummy, Intrin);

    Dfg.InjectStreamIntrin(MemScrPort, "ss_dma_rd $0, $1, $2", AS1);
    Dfg.InjectStreamIntrin(MemScrPort, "ss_wr_dma $0, $1, $2", AS0);
    createAssembleCall(IBPtr->getVoidTy(), "ss_wait t0, t0, 0", "~{memory}", {}, Dfg.DefaultIP());
    //Intrin->replaceAllUsesWith(UndefValue::get(Intrin->getType()));
    Intrin->eraseFromParent();
  }

}

void StreamSpecialize::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<AssumptionCacheTracker>();
  AU.addRequired<BlockFrequencyInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<DependenceAnalysisWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<TargetTransformInfoWrapperPass>();
  AU.addRequired<AAResultsWrapperPass>();
  AU.addRequired<LoopAccessLegacyAnalysis>();
  //AU.addRequired<DemandedBitsWrapperPass>();
  AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
  AU.addRequired<MemorySSAWrapperPass>();
  AU.addPreserved<LoopInfoWrapperPass>();
  //AU.addPreserved<BasicAAWrapperPass>();
  //AU.addPreserved<GlobalsAAWrapperPass>();
  AU.addPreserved<DependenceAnalysisWrapperPass>();
}

char StreamSpecialize::ID = 0;

static RegisterPass<StreamSpecialize> X("stream-specialize", "Stream specialize the program...");
