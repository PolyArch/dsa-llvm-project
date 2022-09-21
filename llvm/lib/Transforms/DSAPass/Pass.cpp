#include <cstdlib>
#include <fstream>
#include <map>
#include <queue>
#include <sstream>

// #include "dsa/arch/model.h"

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
  auto &MC = dsa::utils::ModuleContext();
  auto &TP = MC.TP;
  TP.beginRoi();

  // TODO(@were): Open these after fully decoupled ADG and DSE libs.
  {
    auto *ADGFile = getenv("SBCONFIG");
    DSA_CHECK(ADGFile);
    auto Cmd = formatv("ss_sched --extract-llvm-flags {0}", ADGFile).str();
    ENFORCED_SYSTEM(Cmd.c_str());
    std::ifstream Ifs(".extracted-llvm-flags");
    DSA_CHECK(Ifs.good());

    std::string Ky;
    DSA_CHECK(Ifs >> Ky);
    DSA_CHECK(Ky == "REC");
    int RecBusFound;
    Ifs >> RecBusFound;
    MC.REC = MC.REC && RecBusFound;

    DSA_CHECK(Ifs >> Ky);
    DSA_CHECK(Ky == "IND");
    int IndirectFound;
    Ifs >> IndirectFound;
    MC.IND = MC.IND && IndirectFound;

    DSA_CHECK(Ifs >> Ky);
    DSA_CHECK(Ky == "FU-GRAN");
    int MostFineGrainFU;
    Ifs >> MostFineGrainFU;
    if (MC.GRANULARITY == -1) {
      MC.GRANULARITY = MostFineGrainFU;
      DSA_WARNING << "Granularity is overriden by ADG!";
    }
  }

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
  if (!dsa::utils::ModuleContext().EXTRACT &&
      !dsa::utils::ModuleContext().RAW) {
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

  TP.endRoi();
  DSA_INFO << TP.toString();
  return false;
}

bool StreamSpecialize::runOnFunction(Function &F) {
  DSA_LOG(PASS) << "Processing Function: " << F.getName();

  IRBuilder<> IB(F.getContext());
  IBPtr = &IB;

  auto ScopePairs = dsa::analysis::gatherConfigScope(F);
  if (!ScopePairs.empty()) {
    if (!dsa::utils::ModuleContext().EXTRACT) {
      // DSARegs = dsa::xform::injectDSARegisterFile(F);
    }
  } else {
    DSA_LOG(PASS) << "No need to transform " << F.getName();
    return false;
  }
  DSA_LOG(PASS) << "Transforming " << F.getName();
  SCEVExpander SEE(*SE, F.getParent()->getDataLayout(), "");
  dsa::xform::CodeGenContext CGC(&IB, DSARegs, *SE, SEE, DT, LI, BFI);

  // Store old temporal fallback option
  int OldTF = dsa::utils::ModuleContext().TEMPORAL_FALLBACK;
  std::vector<int> TemporalFallbackCand;
  // If we still use default fallback decision.
  if (OldTF == -1) {
    // without any temporal PE
    if (!dsa::utils::ModuleContext().TemporalFound) {
      // We first try fallback to dedicated PE
      TemporalFallbackCand.push_back(1);
      // If failed, we fallback to CPU
      TemporalFallbackCand.push_back(0);
    } else {
      // If we have temporal PE. We just go to temporal PE.
      TemporalFallbackCand.push_back(0);
    }
  } else {
    TemporalFallbackCand.push_back(dsa::utils::ModuleContext().TEMPORAL_FALLBACK);
  }

  for (auto &TEMPORAL_FALLBACK : TemporalFallbackCand) { // NOLINT
    dsa::utils::ModuleContext().TEMPORAL_FALLBACK = TEMPORAL_FALLBACK;
    DSA_LOG(PASS) << "Temporal Fallback? " << TEMPORAL_FALLBACK
      << " Temporal Found? " << dsa::utils::ModuleContext().TemporalFound;
    // If we have neither dedicated PE fallback or temporal PE, we just fallback to CPU.
    if (!TEMPORAL_FALLBACK && !dsa::utils::ModuleContext().TemporalFound) {
      dsa::xform::eliminateTemporal(F);
    }
    for (int i = 0; i < (int) ScopePairs.size(); ++i) { // NOLINT
      if (!dsa::utils::ModuleContext().EXTRACT) {
        dsa::utils::ModuleContext().TP.beginRoi();
      }
      auto *Start = ScopePairs[i].first;
      auto *End = ScopePairs[i].second;
      auto LinearOverride = dsa::analysis::gatherLinearOverride(Start, End, CGC);

      DFGFile DF(Start, End, this);
      DF.ID = i;
      DSA_LOG(PASS) << i << ": Extracting DFG IR from "
        << *ScopePairs[i].first << " " << *ScopePairs[i].second;
      dsa::analysis::extractDFGFromScope(DF, CGC);
      DSA_LOG(PASS) << DF.DFGs.size() << " DFGs extracted...";
      dsa::analysis::DFGUnroll DU(DF, CGC);
      bool LocalSuccessSchedule = false;
      while (DU.hasNext()) {
        DU.next(true);
        dsa::analysis::DFGAnalysisResult &DAR = DU.DAR.back();
        DSA_LOG(PASS) << i << ": Gather array size hints";
        dsa::analysis::gatherArraySizeHints(DF, CGC, DAR);
        DAR.LinearOverride = LinearOverride;
        DSA_LOG(PASS) << i << ": Analyzing loop trip counts...";
        dsa::analysis::analyzeDFGLoops(DF, CGC, DAR);
        DSA_LOG(PASS) << i << ": Analyzing affine memory access...";
        DAR.initAffineCache(DF, CGC.SE);
        if (dsa::utils::ModuleContext().SLP_STREAM) {
          DSA_LOG(PASS) << i << ": Coalescing SLP memories...";
          dsa::analysis::gatherMemoryCoalescing(DF, *SE, DAR);
        }
        DSA_LOG(PASS) << i << ": Analyzing accumulators...";
        dsa::analysis::analyzeAccumulatorTags(DF, CGC, DAR);
        if (dsa::utils::ModuleContext().FUSE_STREAM) {
          DSA_LOG(PASS) << i << ": Fusing affined dimensions...";
          DAR.fuseAffineDimensions(CGC.SE);
        } 
        DSA_LOG(PASS) << i << ": Beginning reuse analysis..."; 
        DAR.injectAnalyzedArrayHint(DF, CGC);
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
        if (LocalSuccessSchedule) {
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
          DSA_LOG(PASS) << *Start << " " << *End << " transforation succeeds! Erased offloaded instructions!";
          End->eraseFromParent();
          Start->eraseFromParent();
          ScopePairs.erase(ScopePairs.begin() + i);
          --i;
        } else {
          DSA_LOG(PASS) << *Start << " " << *End << " transforation failed! Will try more potential configs!";
        }
      }
      for (auto &Elem : DU.DAR[0].ArraySize) {
        Elem.second->eraseFromParent();
      }
      DSA_LOG(DSE) << "Best/Potential=" << DU.BestAt << "/" << DU.Cnt;
      if (!dsa::utils::ModuleContext().EXTRACT) {
        dsa::utils::ModuleContext().TP.endRoi();
      }
    }
    // If we either successfully scheduled one or are extracting DFG,
    // we no longer need to explore this dimension.
    if (dsa::utils::ModuleContext().EXTRACT) {
      break;
    }
  }

  DSA_LOG(PASS) << "Done with transformation and rewriting!";

  if (dsa::utils::ModuleContext().EXTRACT) {
    return false;
  }

  for (auto &Elem : ScopePairs) {
    DSA_WARNING << *Elem.first << " " << Elem.second << " scope not transformed, fallback to host execution!";
  }

  DSA_LOG(PASS) << "Done! All scopes mapped!";

  DSA_LOG(RES) << F;
  // Restore the old value
  dsa::utils::ModuleContext().TEMPORAL_FALLBACK = OldTF;

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
