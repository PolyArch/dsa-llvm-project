
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

  if (!dsa::utils::ModuleContext().TEMPORAL) {
    dsa::xform::eliminateTemporal(F);
  }


  IRBuilder<> IB(F.getContext());
  IBPtr = &IB;

  dsa::analysis::DFGAnalysisResult DAR;

  dsa::analysis::gatherConfigScope(F, DAR);
  auto &ScopePairs = DAR.Scope;
  if (!ScopePairs.empty()) {
    if (!dsa::utils::ModuleContext().EXTRACT) {
      DSARegs = dsa::xform::injectDSARegisterFile(F);
    }
  } else {
    LLVM_DEBUG(DSA_INFO << "No need to transform " << F.getName() << "\n");
  }
  LLVM_DEBUG(DSA_INFO << "Transforming " << F.getName() << "\n");
  SCEVExpander SEE(*SE, F.getParent()->getDataLayout(), "");
  dsa::xform::CodeGenContext CGC(&IB, DSARegs, *SE, SEE, DT, LI);
  for (int i = 0, N = ScopePairs.size(); i < N; ++i) { // NOLINT
    std::string Name = F.getName().str() + "_dfg_" + std::to_string(i) + ".dfg";
    auto *Start = ScopePairs[i].first;
    auto *End = ScopePairs[i].second;
    DFGFile DF(Name, Start, End, this);
    DSA_LOG(PASS) << i << ": Extracting DFG IR...";
    dsa::analysis::extractDFGFromScope(DF, CGC);
    DSA_LOG(PASS) << i << ": Analyzing loop trip counts...";
    dsa::analysis::analyzeDFGLoops(DF, CGC, DAR);
    DSA_LOG(PASS) << i << ": Analyzing affine memory access...";
    dsa::analysis::analyzeAffineMemoryAccess(DF, CGC, DAR);
    DSA_LOG(PASS) << i << ": Coalescing SLP memories...";
    dsa::analysis::gatherMemoryCoalescing(DF, *SE, DAR);
    DSA_LOG(PASS) << i << ": Analyzing accumulators...";
    dsa::analysis::analyzeAccumulatorTags(DF, CGC, DAR);
    DSA_LOG(PASS) << i << ": Fusing affined dimensions...";
    dsa::analysis::fuseAffineDimensions(DF, CGC, DAR);
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
    auto CI = dsa::analysis::extractDFGPorts(Name, DF, DAR.SI);
    if (dsa::utils::ModuleContext().EXTRACT) {
      continue;
    }
    DSA_LOG(PASS) << i << ": Injecting configuration...";
    dsa::xform::injectConfiguration(CGC, CI, Start, End);
    DSA_LOG(PASS) << i << ": Injecting control intrinsics...";
    dsa::xform::injectStreamIntrinsics(CGC, DF, DAR);
    DSA_LOG(PASS) << i << ": Erasing offloaded instructions...";
    eraseOffloadedInstructions(DF, CGC);
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

  DSA_LOG(PASS) << "Done!";

  LLVM_DEBUG(llvm::errs() << "After transformation:\n"; F.dump());

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
