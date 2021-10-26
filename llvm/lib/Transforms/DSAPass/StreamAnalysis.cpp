#include "dsa/debug.h"

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include <sstream>

#include "StreamAnalysis.h"

#define DEBUG_TYPE "stream-analysis"

namespace dsa {
namespace analysis {

const uint64_t *LoopInvariant::constInt() const {
  if (const auto *SC = dyn_cast<SCEVConstant>(Raw)) {
    return SC->getAPInt().getRawData();
  }
  return nullptr;
}

std::string SEWrapper::toString() const {
  std::string S;
  llvm::raw_string_ostream RSO(S);
  RSO << *Raw;
  return RSO.str();
}

std::string LinearCombine::toString() const {
  std::string S;
  llvm::raw_string_ostream RSO(S);
  RSO << "(";
  for (int i = 0, N = Coef.size(); i < N; ++i) { // NOLINT
    RSO << "i" << i << "[" << TripCount[i]->toString() << "]";
    RSO << " * " << Coef[i]->toString() << " + ";
  }
  RSO << Base->toString() << ")";
  return RSO.str();
}

const uint64_t *constInt(SEWrapper *SW) {
  if (auto *LI = dyn_cast<LoopInvariant>(SW)) {
    return LI->constInt();
  }
  return nullptr;
}

int LinearCombine::partialInvariant() const {
  for (int i = 0, N = Coef.size(); i < N; ++i) { // NOLINT
    if (const auto *CI = constInt(Coef[i])) {
      if (CI && *CI == 0) {
        continue;
      }
    }
    return i;
  }
  return Coef.size();
}

LinearCombine::~LinearCombine() {
  // for (int i = 0; i < (int) Coef.size(); ++i) { // NOLINT
  //   delete Coef[i];
  // }
  // for (int i = 0; i < (int) TripCount.size(); ++i) { // NOLINT
  //   delete TripCount[i];
  // }
}

LinearCombine *LoopInvariant::toLinearCombine(ScalarEvolution *SE) {
  auto *Res = new LinearCombine(this->Parent.Raw, this->Raw);
  Res->TripCount = this->TripCount;
  Res->Coef.reserve(TripCount.size());
  if (SE) {
    for (int i = 0; i < (int) TripCount.size(); ++i) { // NOLINT
      Res->Coef.push_back(new LoopInvariant(Res, SE->getConstant(APInt(64, 0, true))));
    }
  }
  return Res;
}

SEWrapper *analyzeIndexExpr(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                            const std::vector<Loop *> &Loops,
                            const std::vector<SEWrapper *> &TripCount) {
  for (int i = 0; i < (int) TripCount.size(); ++i) { // NOLINT
    DSA_LOG(AFFINE) << i << ": " << TripCount[i]->toString();
  }
  int i = 0; // NOLINT
  for (int N = Loops.size(); i < N; ++i) {
    if (!SE->isLoopInvariant(Raw, Loops[i])) {
      break;
    }
  }
  if (!isa<SCEVAddRecExpr>(Raw) || i == (int)Loops.size()) {
    if (i == (int)Loops.size()) {
      auto *LI = new LoopInvariant(Parent, Raw);
      LI->TripCount = TripCount;
      return LI;
    }
    return nullptr;
  }
  LinearCombine *Res = new LinearCombine(Parent, Raw);
  for (int j = 0; j < i; ++j) { // NOLINT
    Res->Coef.push_back(new LoopInvariant(Parent, SE->getConstant(APInt(64, 0))));
  }
  auto *Cur = Raw;
  for (int N = Loops.size(); i < N; ++i) {
    if (const auto *SARE = dyn_cast<SCEVAddRecExpr>(Cur)) {
      if (!Loops.back()->contains(SARE->getLoop())) {
        Res->Coef.push_back(new LoopInvariant(Res, SE->getConstant(APInt(64, 0))));
        continue;
      }
      if (SARE->getLoop() != Loops[i]) {
        CHECK(SE->isLoopInvariant(Cur, Loops[i]))
          << "\n" << *Raw << "\n" << *Cur << "\nNot an invariant in loop " << *Loops[i]
          << "\nCurrent Loop: " << *SARE->getLoop()
          << "\nOuter Most: " << *Loops.back();
        Res->Coef.push_back(new LoopInvariant(Res, SE->getConstant(APInt(64, 0))));
        continue;
      }
      std::vector<Loop*> SliceLoop(Loops.begin() + i + 1, Loops.end());
      std::vector<SEWrapper*> SliceTripCount(TripCount.begin() + i + 1, TripCount.end());
      Res->Coef.push_back(analyzeIndexExpr(SE, SARE->getStepRecurrence(*SE), Res,
                                           SliceLoop, SliceTripCount));
      Cur = SARE->getStart();
    } else {
      CHECK(SE->isLoopInvariant(Cur, Loops[i]))
        << "\n" << *Raw << "\n" << *Cur << "\nNot an invariant in loop " << *Loops[i];
      Res->Coef.push_back(new LoopInvariant(Res, SE->getConstant(APInt(64, 0))));
    }
  }
  Res->TripCount = TripCount;
  for (int i = 0; i < (int) Loops.size(); ++i) { // NOLINT
    DSA_LOG(AFFINE)
      << i << ": " << "Coef " << Res->Coef[i]->toString()
      << " ,Trip " << Res->TripCount[i]->toString();
  }
  CHECK(Res->Coef.size() == Loops.size()) << Res->Coef.size() << " != " << Loops.size();
  Res->Base = analyzeIndexExpr(SE, Cur, Res, {}, {});
  return Res;
}

void fuseInnerDimensions(LinearCombine &LI, int DType, int Unroll, ScalarEvolution &SE, int CutOff) {
  if (LI.Coef.empty()) {
    return;
  }
  int PI = LI.partialInvariant();
  std::vector<SEWrapper*> SlicedCoef(LI.Coef.begin(), LI.Coef.begin() + PI);
  std::vector<SEWrapper*> SlicedLoop(LI.TripCount.begin(), LI.TripCount.begin() + PI);

  LI.Coef.erase(LI.Coef.begin(), LI.Coef.begin() + PI);
  LI.TripCount.erase(LI.TripCount.begin(), LI.TripCount.begin() + PI);

  auto &Coef = LI.Coef;
  auto &Loop = LI.TripCount;
  while ((int) Coef.size() > CutOff) {
    if (const auto *S1D = constInt(Coef.front())) {
      if (((int) *S1D) == DType) {
        DSA_LOG(FUSE) << "S1D: " << *S1D << " , DType" << DType;
        if (const auto *N = constInt(Loop[0])) {
          // Fuse it only when it is divisible.
          DSA_LOG(FUSE) << "InnerN: " << *N;
          if ((*N + 1) % Unroll) {
            break;
          }
          if (const auto *S2D = constInt(Coef[1])) {
            DSA_LOG(FUSE) << "Stride2D: " << *S2D;
            // TODO(@were): Relax this condition.
            if (isa<LoopInvariant>(Loop[1])) {
              if ((*S1D) * (*N + 1) == *S2D) {
                Loop.erase(Loop.begin());
                Coef.erase(Coef.begin());
                auto *LoopParent = Loop.front()->Parent.Raw;
                auto *CoefParent = Coef.front()->Parent.Raw;
                Coef.front() = new LoopInvariant(LoopParent,
                                                 SE.getConstant(APInt(64, DType, true)));
                auto *SCEVN = SE.getConstant(APInt(64, *N + 1, true));
                auto *SCEVNegOne = SE.getConstant(APInt(64, -1, true));
                auto *NewLoop = Loop.front()->Raw;
                NewLoop = SE.getMulExpr(NewLoop, SCEVN);
                NewLoop = SE.getAddExpr(NewLoop, SCEVN);
                NewLoop = SE.getAddExpr(NewLoop, SCEVNegOne);
                Loop.front() = new LoopInvariant(CoefParent, NewLoop);
                continue;
              }
            }
          }
        }
      }
    }
    break;
  }
  LI.Coef.insert(LI.Coef.begin(), SlicedCoef.begin(), SlicedCoef.end());
  LI.TripCount.insert(LI.TripCount.begin(), SlicedLoop.begin(), SlicedLoop.end());
}

namespace test {

/*!
 * \brief Expose these functions in the .so for the purpose of test.
 */
struct StreamAnalysisPass : public FunctionPass {
  ScalarEvolution *SE{nullptr};
  LoopInfo *LI{nullptr};
  DependenceInfo *DI{nullptr};
  std::vector<Loop *> Loops;

  void AnalyzeLoopNest(const std::vector<Loop *> &Loops) { // NOLINT
    CHECK(!Loops.empty());
    auto *L = Loops.front();
    for (auto &BB : L->getBlocks()) {
      for (auto &I : *BB) {
        if (auto *Load = dyn_cast<LoadInst>(&I)) {
          auto *Index = Load->getPointerOperand();
          CHECK(SE->isSCEVable(Index->getType()));
          auto *LI = analyzeIndexExpr(SE, SE->getSCEV(Index), Load, Loops,
                                      std::vector<SEWrapper*>(Loops.size(), nullptr));
          DSA_LOG(LOOP) << LI->toString();
        }
      }
    }
    for (auto *L : Loops) {
      auto *LI = analyzeIndexExpr(SE, SE->getBackedgeTakenCount(L), L, Loops,
                                  std::vector<SEWrapper*>(Loops.size(), nullptr));
      DSA_LOG(LOOP) << LI->toString();
    }
  }

  void Dfs(Loop *L) { // NOLINT
    Loops.insert(Loops.begin(), L);
    if (L->empty()) {
      if (GetUnrollMetadata(L->getLoopID(), "llvm.loop.ss.dedicated")) {
        DSA_LOG(LOOP) << "Offload: " << *L;
        auto I = Loops.begin();
        decltype(Loops) Slice;
        while (I < Loops.end()) {
          auto *IndVar = (*I)->getCanonicalInductionVariable();
          std::string S;
          llvm::raw_string_ostream OSS(S);
          if (IndVar) {
            OSS << *IndVar;
          } else if ((*I)->getInductionVariable(*SE)) {
            OSS << *(*I)->getInductionVariable(*SE);
          } else {
            OSS << "Non-Canonical";
          }
          DSA_LOG(LOOP) << "Loop: " << *(*I) << " " << S;
          if (GetUnrollMetadata((*I)->getLoopID(), "llvm.loop.ss.stream")) {
            Slice = decltype(Loops)(Loops.begin(), I + 1);
            break;
          }
          ++I;
        }
        AnalyzeLoopNest(Slice);
      }
    } else {
      for (auto *SubLoop : *L) {
        Dfs(SubLoop);
      }
    }
    Loops.erase(Loops.begin());
  }

  bool runOnFunction(Function &F) override {
    SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    DI = &getAnalysis<DependenceAnalysisWrapperPass>().getDI();
    for (auto *L : *LI) {
      Dfs(L);
    }
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
    // AU.addRequired<DemandedBitsWrapperPass>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<MemorySSAWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    // AU.addPreserved<BasicAAWrapperPass>();
    // AU.addPreserved<GlobalsAAWrapperPass>();
    AU.addPreserved<DependenceAnalysisWrapperPass>();
  }

  StreamAnalysisPass() : FunctionPass(ID) {}

  static char ID;
};

char StreamAnalysisPass::ID = 0;

static RegisterPass<StreamAnalysisPass>
    Y("analyze-stream", "Invoke stream analysis from streams...");

} // namespace test

} // namespace analysis
} // namespace dsa
