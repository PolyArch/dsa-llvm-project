
#include <cstdlib>
#include <fstream>
#include <map>
#include <queue>
#include <sstream>

#include "./llvm_common.h"

#include "CodeXform.h"
#include "DFGAnalysis.h"
#include "DFGEntry.h"
#include "Pass.h"
#include "Transformation.h"
#include "Util.h"
#include "dsa/rf.h"

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
    llvm::legacy::FunctionPassManager fpass(&M);
    llvm::legacy::PassManager mpass;
    PMB.populateFunctionPassManager(fpass);
    PMB.populateModulePassManager(mpass);
    PMB.Inliner = llvm::createFunctionInliningPass(3, 0, false);
    for (auto &F : M) {
      runOnFunction(F);
    }
    fpass.doFinalization();
    mpass.run(M);
  }

  return false;
}

bool StreamSpecialize::runOnFunction(Function &F) {

  if (!dsa::utils::ModuleContext().TEMPORAL) {
    dsa::xform::EliminateTemporal(F);
  }


  IRBuilder<> IB(F.getContext());
  IBPtr = &IB;

  auto ScopePairs = dsa::analysis::GatherConfigScope(F);
  if (!ScopePairs.empty()) {
    if (!dsa::utils::ModuleContext().EXTRACT) {
      DSARegs = dsa::xform::InjectDSARegisterFile(F);
    }
  } else {
    LLVM_DEBUG(INFO << "No need to transform " << F.getName() << "\n");
  }
  LLVM_DEBUG(INFO << "Transforming " << F.getName() << "\n");
  SCEVExpander SEE(*SE, F.getParent()->getDataLayout(), "");
  dsa::xform::CodeGenContext CGC(&IB, DSARegs, *SE, SEE);
  for (int i = 0, n = ScopePairs.size(); i < n; ++i) {
    std::string Name = F.getName().str() + "_dfg_" + std::to_string(i) + ".dfg";
    auto Start = ScopePairs[i].first;
    auto End = ScopePairs[i].second;
    DFGFile DF(Name, Start, End, this);
    dsa::analysis::ExtractDFGFromScope(DF, Start, End, DT, LI);
    dsa::xform::EmitDFG(nullptr, &DF);
    // dsa::xform::EmitDFG(&llvm::errs(), &DF);
    // If extraction only, we do not schedule and analyze.
    if (dsa::utils::ModuleContext().EXTRACT) {
      continue;
    }
    auto SBCONFIG = getenv("SBCONFIG");
    CHECK(SBCONFIG);
    auto Cmd =
        formatv("ss_sched {0} {1} {2} -e 0 > /dev/null", "-v", SBCONFIG, Name)
            .str();
    LLVM_DEBUG(INFO << Cmd);
    CHECK(system(Cmd.c_str()) == 0)
        << "Not successfully scheduled! Try another DFG!";
    // TODO(@were): When making the DFG's of index expression is done, uncomment
    // these. auto Graphs = DFG.DFGFilter<DFGBase>();
    // std::vector<std::vector<int>> Ports(Graphs.size());
    // for (int i = 0, n = Graphs.size(); i < n; ++i) {
    //   Ports[i].resize(Graphs[i]->Entries.size(), -1);
    // }
    // DF.InspectSPADs();
    auto CI = dsa::analysis::ExtractDFGPorts(Name, DF);
    dsa::xform::InjectConfiguration(CGC, CI, Start, End);
    if (dsa::utils::ModuleContext().EXTRACT) {
      continue;
    }
    dsa::xform::InjectStreamIntrinsics(CGC, DF);
    DF.EraseOffloadedInstructions();
  }
  if (!dsa::utils::ModuleContext().EXTRACT) {
    for (auto &Pair : ScopePairs) {
      Pair.second->eraseFromParent();
      Pair.first->eraseFromParent();
    }
  } else {
    return false;
  }

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
