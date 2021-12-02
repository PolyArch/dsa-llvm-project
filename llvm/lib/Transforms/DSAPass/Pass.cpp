
#include <cstdlib>
#include <fstream>
#include <map>
#include <queue>
#include <sstream>

#include "./llvm_common.h"

#include "CodeXform.h"
#include "DFGAnalysis.h"
#include "DFGEntry.h"
#include "DFGIR.h"
#include "Pass.h"
#include "StreamAnalysis.h"
#include "Util.h"
#include "dsa-ext/rf.h"

using namespace llvm;

#define DEBUG_TYPE "stream-specialize"

bool StreamSpecialize::runOnModule(Module &M) {

  for (auto &F : M) {
    if (F.isDeclaration()) {
      continue;
    }
    ACT = &getAnalysis<AssumptionCacheTracker>(F).getAssumptionCache(F);
    LI = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    SE = &getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
    DT = &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    AAR = &getAnalysis<AAResultsWrapperPass>(F).getAAResults();
    BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    MSSA = &getAnalysis<MemorySSAWrapperPass>(F).getMSSA();
    runOnFunction(F);
  }

  // If we are not extracting DFG's, do not clean up the code with O3.
  if (!dsa::utils::ModuleContext().EXTRACT) {
    llvm::PassManagerBuilder PMB;
    PMB.OptLevel = 3;
    llvm::legacy::FunctionPassManager Fpass(&M);
    llvm::legacy::PassManager Mpass;
    PMB.populateFunctionPassManager(Fpass);
    PMB.populateModulePassManager(Mpass);
    PMB.Inliner = llvm::createFunctionInliningPass(3, 0, false);
    for (auto &F : M) {
      runOnFunction(F);
    }
    Fpass.doFinalization();
    Mpass.run(M);
  }

  return false;
}

bool StreamSpecialize::runOnFunction(Function &F) {
  DSA_LOG(PASS) << "Processing Function: " << F.getName();

  if (!dsa::utils::ModuleContext().TEMPORAL) {
    dsa::xform::eliminateTemporal(F);
  }

  IRBuilder<> IB(F.getContext());
  IBPtr = &IB;

  auto ScopePairs = dsa::analysis::gatherConfigScope(F);
  if (!ScopePairs.empty()) {
    if (!dsa::utils::ModuleContext().EXTRACT) {
      DSARegs = dsa::xform::injectDSARegisterFile(F);
    }
  } else {
    DSA_LOG(PASS) << "No need to transform " << F.getName();
    return false;
  }
  DSA_LOG(PASS) << "Transforming " << F.getName();
  SCEVExpander SEE(*SE, F.getParent()->getDataLayout(), "");
  dsa::xform::CodeGenContext CGC(&IB, DSARegs, *SE, SEE, DT, LI, BFI);
  bool GlobalSuccessSchedule = true;
  for (int i = 0, N = ScopePairs.size(); i < N; ++i) { // NOLINT
    auto *Start = ScopePairs[i].first;
    auto *End = ScopePairs[i].second;
    auto LinearOverride = dsa::analysis::gatherLinearOverride(Start, End, CGC);

    DFGFile DF(Start, End, this);
    DF.ID = i;
    DSA_LOG(PASS) << i << ": Extracting DFG IR...";
    dsa::analysis::extractDFGFromScope(DF, CGC);
    dsa::analysis::DFGUnroll DU(DF, CGC);
    bool LocalSuccessSchedule = false;
    while (DU.hasNext()) {
      DU.next(true);
      dsa::analysis::DFGAnalysisResult &DAR = DU.DAR.back();
      DAR.LinearOverride = LinearOverride;
      DSA_LOG(PASS) << i << ": Analyzing loop trip counts...";
      dsa::analysis::analyzeDFGLoops(DF, CGC, DAR);
      DSA_LOG(PASS) << i << ": Analyzing affine memory access...";
      DAR.initAffineCache(DF, CGC.SE);
      DSA_LOG(PASS) << i << ": Coalescing SLP memories...";
      dsa::analysis::gatherMemoryCoalescing(DF, *SE, DAR);
      DSA_LOG(PASS) << i << ": Analyzing accumulators...";
      dsa::analysis::analyzeAccumulatorTags(DF, CGC, DAR);
      DSA_LOG(PASS) << i << ": Fusing affined dimensions...";
      DAR.fuseAffineDimensions(CGC.SE);
      DSA_LOG(PASS) << i << ": Extracting SPAD...";
      dsa::analysis::extractSpadFromScope(DF, CGC, DAR);
      DSA_LOG(PASS) << i << ": Emitting DFG...";
      {
        std::error_code EC;
        llvm::raw_fd_ostream RFO(DF.getName(), EC);
        dsa::xform::emitDFG(RFO, &DF, DAR, CGC);
      }
      // If extraction only, we do not schedule and analyze.
      if (dsa::utils::ModuleContext().EXTRACT) {
        DSA_LOG(PASS) << i << ": Extracting DFG only, don't transform...";
        continue;
      }
      DSA_LOG(PASS) << i << ": Scheduling DFG, and extracting port information...";
      DAR.CI = dsa::analysis::extractDFGPorts(DF, DAR.SI, true);
      auto &CI = DAR.CI;
      DSA_LOG(DSE) << "Exploring: " << DF.FileName << ", " << CI.EstimatedILP;
      if (CI.empty()) {
        DSA_LOG(PASS) << DF.getName() << " failed to schedule!";
        continue;
      }
      LocalSuccessSchedule = true;
    }
    if (!dsa::utils::ModuleContext().EXTRACT) {
      dsa::analysis::DFGAnalysisResult &DAR = DU.best();
      auto &CI = DAR.CI;
      DF.FileName = CI.Name + ".dfg";
      {
        std::string Raw = CI.Name;
        int R = Raw.size(), L = Raw.size() - 1;
        for (int i = DF.DFGs.size() - 1; i >= 0; --i) { // NOLINT
          while (L >= 0 && Raw[L] != '_') --L;
          int X = std::atoi(std::string(Raw.begin() + L + 1, Raw.begin() + R).c_str());
          if (auto *DD = dyn_cast<DedicatedDFG>(DF.DFGs[i])) {
            DD->UnrollFactor = X;
          }
          R = L--;
        }
      }
      DSA_LOG(DSE) << "Use DSE: " << DF.getName();
      DSA_LOG(PASS) << i << ": Injecting configuration...";
      dsa::analysis::extractDFGPorts(DF, DAR.SI, false);
      DSA_LOG(PASS) << i << ": Injecting configuration...";
      dsa::xform::injectConfiguration(CGC, CI, Start, End);
      DSA_LOG(PASS) << i << ": Injecting control intrinsics...";
      dsa::xform::injectStreamIntrinsics(CGC, DF, DAR);
      DSA_LOG(PASS) << i << ": Erasing offloaded instructions...";
      eraseOffloadedInstructions(DF, CGC);
    }
    GlobalSuccessSchedule = GlobalSuccessSchedule && LocalSuccessSchedule;
    if (!GlobalSuccessSchedule) {
      DSA_LOG(PASS) << "DFG " << i << " failed to schedule";
      break;
    }
    DSA_LOG(DSE) << "Best/Potential=" << DU.BestAt << "/" << DU.Cnt;
  }

  DSA_LOG(PASS) << "Done with transformation and rewriting!";

  if (!dsa::utils::ModuleContext().EXTRACT) {
    DSA_LOG(PASS) << "Erasing all config scopes!";
    for (auto &Pair : ScopePairs) {
      Pair.second->eraseFromParent();
      Pair.first->eraseFromParent();
    }
  } else {
    return false;
  }

  DSA_CHECK(GlobalSuccessSchedule);

  DSA_LOG(PASS) << "Done! " << GlobalSuccessSchedule;

  DSA_LOG(RES) << F;

  return false;
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
  AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
  AU.addRequired<MemorySSAWrapperPass>();
}

char StreamSpecialize::ID = 0;

static RegisterPass<StreamSpecialize>
    X("stream-specialize", "Decoupld-Spatial Specialized Transformation");
