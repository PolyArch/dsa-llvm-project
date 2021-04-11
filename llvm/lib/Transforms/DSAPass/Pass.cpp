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
#include "dsa/rf.h"

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

std::vector<StreamSpecialize::StickyRegister>
InjectRegisterFile(IRBuilder<> *IB) {
  std::vector<StreamSpecialize::StickyRegister> Res;
  std::string TyName("reg.type");
  auto RegType = StructType::create(TyName, IB->getInt64Ty(), IB->getInt8Ty());
  for (int i = 0; i < DSARF::TOTAL_REG; ++i) {
    auto A = IB->CreateAlloca(RegType, nullptr, REG_NAMES[i]);
    auto R = IB->CreateInBoundsGEP(A, {IB->getInt32(0), IB->getInt32(0)});
    auto S = IB->CreateInBoundsGEP(A, {IB->getInt32(0), IB->getInt32(1)});
    IB->CreateStore(IB->getInt64(REG_STICKY[i]), R);
    IB->CreateStore(IB->getInt8(i == DSARF::TBC), S);
    Res.emplace_back(A, R, S);
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
    if (!ScopePairs.empty()) {
      IB.SetInsertPoint(&F.getEntryBlock().back());
      DSARegs = InjectRegisterFile(&IB);
    }
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
    IBPtr->SetInsertPoint(Dfg.DefaultIP());
    dsa::inject::InjectLinearStream(IBPtr, DSARegs, MemScrPort, AS1, DMO_Read, DP_NoPadding, DMT_DMA, 1);
    dsa::inject::InjectLinearStream(IBPtr, DSARegs, MemScrPort, AS1, DMO_Read, DP_NoPadding, DMT_SPAD, 1);
    dsa::inject::DSAIntrinsicEmitter(IBPtr, DSARegs).SS_WAIT(~0ull);
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
