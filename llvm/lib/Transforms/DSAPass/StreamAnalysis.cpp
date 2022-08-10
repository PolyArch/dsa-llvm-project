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

std::map<std::pair<void*, const SCEV*>, LoopInvariant*> LoopInvariant::UniqueInvariant;

LoopInvariant *LoopInvariant::get(void *Parent, const SCEV *Raw) {
  auto Iter = UniqueInvariant.find({Parent, Raw});
  if (Iter != UniqueInvariant.end()) {
    return Iter->second;
  }
  UniqueInvariant[{Parent, Raw}] = new LoopInvariant(Parent, Raw);
  return UniqueInvariant[{Parent, Raw}];
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
    RSO << "$i" << i << "[" << TripCount[i]->toString() << "]";
    RSO << " * " << Coef[i]->toString() << " + ";
  }
  RSO << Base->toString() << ")";
  return RSO.str();
}

std::string LoopInvariant::toString() const {
  std::string S;
  llvm::raw_string_ostream RSO(S);
  if (const auto *SC = dyn_cast<SCEVConstant>(Raw)) {
    RSO << SC->getAPInt().getSExtValue();
  } else {
    RSO << "(" << *Raw << ")";
    if (!TripCount.empty()) {
      RSO << " x (";
      for (int i = 0, N = TripCount.size(); i < N; ++i) { // NOLINT
        if (i) RSO << " * ";
        RSO << TripCount[i]->toString();
      }
      RSO << ")";
    }
  }
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
  Res->Base = this;
  if (SE) {
    Res->Coef.reserve(TripCount.size());
    for (int i = 0; i < (int) TripCount.size(); ++i) { // NOLINT
      Res->Coef.push_back(LoopInvariant::get(Res, SE->getConstant(APInt(64, 0, true))));
    }
  }
  return Res;
}


Type *SWCast::destTy() const {
  return SCE->getType();
}

Type *SWCast::srcTy() const {
  return SCE->getOperand(0)->getType();
}

std::string SWCast::toString() const {
  std::string Res;
  llvm::raw_string_ostream OSS(Res);
  OSS << "( (" << *srcTy() << ")" << Stripped->toString() << " -> " << *destTy() << ")";
  return OSS.str();
}


SEWrapper *analyzeIndexExpr(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                            const std::vector<Loop *> &Loops,
                            const std::vector<SEWrapper *> &TripCount,
                            const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride) {
  int i = 0; // NOLINT
  for (int N = Loops.size(); i < N; ++i) {
    if (!SE->isLoopInvariant(Raw, Loops[i])) {
      break;
    }
  }
  if (i == (int)Loops.size()) {
    if (i == (int)Loops.size()) {
      auto *LI = LoopInvariant::get(Parent, Raw);
      LI->TripCount = TripCount;
      return LI;
    }
  }
  if (auto *Res = analyzeCast(SE, Raw, Parent, Loops, TripCount, LinearOverride)) {
    return Res;
  }
  if (auto *Res = analyzeIndirectPointer(SE, Raw, Parent, Loops, TripCount, LinearOverride)) {
    return Res;
  }
  if (auto *Res = analyzeBinary(SE, Raw, Parent, Loops, TripCount, LinearOverride)) {
    return Res;
  }
  DSA_CHECK(isa<SCEVAddRecExpr>(Raw)) << *Raw;
  LinearCombine *Res = new LinearCombine(Parent, Raw);
  for (int j = 0; j < i; ++j) { // NOLINT
    Res->Coef.push_back(LoopInvariant::get(Parent, SE->getConstant(APInt(64, 0))));
  }
  auto *Cur = Raw;
  for (int N = Loops.size(); i < N; ++i) {
    if (const auto *SARE = dyn_cast<SCEVAddRecExpr>(Cur)) {
      if (!Loops.back()->contains(SARE->getLoop())) {
        Res->Coef.push_back(LoopInvariant::get(Res, SE->getConstant(APInt(64, 0))));
        continue;
      }
      if (SARE->getLoop() != Loops[i]) {
        DSA_CHECK(SE->isLoopInvariant(Cur, Loops[i]))
          << "\n" << *Raw << "\n" << *Cur << "\nNot an invariant in loop " << *Loops[i]
          << "\nCurrent Loop: " << *SARE->getLoop()
          << "\nOuter Most: " << *Loops.back();
        Res->Coef.push_back(LoopInvariant::get(Res, SE->getConstant(APInt(64, 0))));
        continue;
      }
      std::vector<Loop*> SliceLoop(Loops.begin() + i + 1, Loops.end());
      std::vector<SEWrapper*> SliceTripCount(TripCount.begin() + i + 1, TripCount.end());
      Res->Coef.push_back(analyzeIndexExpr(SE, SARE->getStepRecurrence(*SE), Res,
                                           SliceLoop, SliceTripCount, LinearOverride));
      Cur = SARE->getStart();
    } else if (SE->isLoopInvariant(Cur, Loops[i])) {
      Res->Coef.push_back(LoopInvariant::get(Res, SE->getConstant(APInt(64, 0))));
    } else {
      break;
    }
  }
  Res->TripCount = std::vector<SEWrapper*>(TripCount.begin(), TripCount.begin() + i);
  // for (int i = 0; i < (int) Loops.size(); ++i) { // NOLINT
  //   if (Loops[i]->getCanonicalInductionVariable()) {
  //     DSA_LOG(AFFINE) << "i" << i << " -> "<< *Loops[i]->getCanonicalInductionVariable();
  //   } else {
  //     DSA_LOG(AFFINE) << "i" << i;
  //   }
  //   DSA_LOG(AFFINE) << i << ": " << "Coef " << Res->Coef[i]->toString()
  //     << " ,Trip " << Res->TripCount[i]->toString();
  // }
  // DSA_CHECK(Res->Coef.size() == Loops.size()) << Res->Coef.size() << " != " << Loops.size();
  std::vector<Loop*> ResidueLoops(Loops.begin() + i, Loops.end());
  std::vector<SEWrapper*> ResidueTripCount(TripCount.begin() + i, TripCount.end());
  // A simple hack overrides linear analysis.
  if (auto *Bin = analyzeBinary(SE, Cur, Res, ResidueLoops, ResidueTripCount, LinearOverride)) {
    if (isa<SWBinary>(Bin)) {
      Res->Base = Bin;
    } else {
      DSA_CHECK(isa<LinearCombine>(Bin));
      return Bin;
    }
  } else {
    Res->Base = analyzeIndexExpr(SE, Cur, Res, ResidueLoops, ResidueTripCount, LinearOverride);
  }
  return Res;
}

void fuseInnerDimensions(LinearCombine &LI, int DType, int Unroll, ScalarEvolution &SE, int CutOff,
                         bool IsSLP) {
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
  int Iteration = 0;
  while ((int) Coef.size() > CutOff) {
    ++Iteration;
    if (const auto *S1D = constInt(Coef.front())) {
      if (((int) *S1D) == DType) {
        DSA_LOG(FUSE) << "S1D: " << *S1D << " , DType" << DType;
        if (const auto *N = constInt(Loop[0])) {
          DSA_LOG(FUSE) << "InnerN: " << *N;
          // If the first dimension is derived from SLP fusion.
          if (Iteration == 1 && IsSLP) {
            // The outer (2nd) dimension is the actual dimension to check.
            if (const auto *M = constInt(Loop[1])) {
              if (*M % Unroll) {
                break;
              }
            } else {
              break;
            }
          } else {
            // Fuse it only when it is divisible for normal case.
            if (*N % Unroll) {
              break;
            }
          }
          if (const auto *S2D = constInt(Coef[1])) {
            DSA_LOG(FUSE) << "Stride2D: " << *S2D;
            // TODO(@were): Relax this condition.
            if (isa<LoopInvariant>(Loop[1])) {
              if ((*S1D) * (*N) == *S2D) {
                Loop.erase(Loop.begin());
                Coef.erase(Coef.begin());
                auto *LoopParent = Loop.front()->Parent.Raw;
                auto *CoefParent = Coef.front()->Parent.Raw;
                Coef.front() = LoopInvariant::get(LoopParent,
                                                  SE.getConstant(APInt(64, DType, true)));
                auto *SCEVN = SE.getConstant(APInt(64, *N, true));
                auto *NewLoop = Loop.front()->Raw;
                NewLoop = SE.getMulExpr(NewLoop, SCEVN);
                Loop.front() = LoopInvariant::get(CoefParent, NewLoop);
                Loop.front()->Parent = Loop[1]->Parent;
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

SEWrapper *analyzeBinary(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                         const std::vector<Loop *> &Loops,
                         const std::vector<SEWrapper *> &TripCount,
                         const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride) {
  SWBinary *Res = nullptr;
  if (auto *Add = dyn_cast<SCEVAddExpr>(Raw)) {
    {
      for (int i = 0; i < 2; ++i) { // NOLINT
        auto Iter = LinearOverride.find(Add->getOperand(i));
        if (Iter != LinearOverride.end()) {
          auto *LC = new LinearCombine(Parent, Raw);
          LC->Base = analyzeIndexExpr(SE, Iter->first, Parent, {}, {}, {});
          // TODO(@were): Fix the dtype.
          LC->Coef.push_back(LoopInvariant::get(Parent, SE->getConstant(APInt(64, 8))));
          LC->TripCount.push_back(analyzeIndexExpr(SE, Iter->second, Parent, {}, {}, {}));
          return LC;
        }
      }
    }
    Res = new SWBinary(Parent, Raw, 0);
    Res->A = analyzeIndexExpr(SE, Add->getOperand(0), Parent, Loops, TripCount, LinearOverride);
    Res->B = analyzeIndexExpr(SE, Add->getOperand(1), Parent, Loops, TripCount, LinearOverride);
    return Res;
  }
  if (auto *Mul = dyn_cast<SCEVMulExpr>(Raw)) {
    Res = new SWBinary(Parent, Raw, 1);
    Res->A = analyzeIndexExpr(SE, Mul->getOperand(0), Parent, Loops, TripCount, LinearOverride);
    Res->B = analyzeIndexExpr(SE, Mul->getOperand(1), Parent, Loops, TripCount, LinearOverride);
    return Res;
  }
  return Res;
}

SWCast *analyzeCast(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                    const std::vector<Loop *> &Loops,
                    const std::vector<SEWrapper *> &TripCount,
                    const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride) {
  if (auto *SCE = dyn_cast<SCEVCastExpr>(Raw)) {
    auto *Res = new SWCast(Parent, SCE);
    Res->Stripped = analyzeIndexExpr(SE, SCE->getOperand(0), Parent, Loops, TripCount, LinearOverride);
    return Res;
  }
  return nullptr;
}

std::string SWBinary::toString() const {
  return "(" + A->toString() + " " + "+*"[Op] + " " + B->toString() + ")";
}

IndirectPointer* analyzeIndirectPointer(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                                        const std::vector<Loop *> &Loops,
                                        const std::vector<SEWrapper *> &TripCount,
                                        const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride) {
  if (auto *SU = dyn_cast<SCEVUnknown>(Raw)) {
    auto *Val = SU->getValue();
    if (auto *Load = dyn_cast<LoadInst>(Val)) {
      auto *Res = new IndirectPointer(Parent, Raw, Load);
      const auto *Raw = SE->getSCEV(Load->getPointerOperand());
      Res->Pointer = analyzeIndexExpr(SE, Raw, Parent, Loops, TripCount, LinearOverride);
      return Res;
    }
  }
  return nullptr;
}

std::string IndirectPointer::toString() const {
  std::string Res = "(*(" + Pointer->toString() + "))";
  return Res;
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
    DSA_CHECK(!Loops.empty());
    auto *L = Loops.front();
    for (auto &BB : L->getBlocks()) {
      for (auto &I : *BB) {
        if (auto *Load = dyn_cast<LoadInst>(&I)) {
          auto *Index = Load->getPointerOperand();
          DSA_CHECK(SE->isSCEVable(Index->getType()));
          auto *LI = analyzeIndexExpr(SE, SE->getSCEV(Index), Load, Loops,
                                      std::vector<SEWrapper*>(Loops.size(), nullptr), {});
          DSA_LOG(LOOP) << LI->toString();
        }
      }
    }
    for (auto *L : Loops) {
      auto *LI = analyzeIndexExpr(SE, SE->getBackedgeTakenCount(L), L, Loops,
                                  std::vector<SEWrapper*>(Loops.size(), nullptr), {});
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
