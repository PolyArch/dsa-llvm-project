#include <cstdio>
#include <fstream>
#include <queue>
#include <set>
#include <sstream>
#include <utility>

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

#include "CodeXform.h"
#include "DFGEntry.h"
#include "DFGIR.h"
#include "StreamAnalysis.h"
#include "Util.h"

#include "dsa-ext/rf.h"
#include "dsa-ext/spec.h"
//#include "dsa/mapper/scheduler.h"
//#include "dsa/mapper/scheduler_sa.h"

using namespace llvm;

#define DEBUG_TYPE "stream-specialize"

namespace dsa {

void DFGVisitor::Visit(DFGBase *Node) {}
void DFGVisitor::Visit(DedicatedDFG *Node) {
  Visit(static_cast<DFGBase *>(Node));
}
void DFGVisitor::Visit(TemporalDFG *Node) {
  Visit(static_cast<DFGBase *>(Node));
}

} // namespace dsa

const std::string &DFGFile::getName() { return FileName; }

/// Check if a given SCEV is loop invariant
bool CheckLoopInvariant(const SCEV *S, int From, // NOLINT
                        const std::vector<Loop*> &LoopNest,
                        ScalarEvolution *SE) {
  for (size_t i = From; i < LoopNest.size(); ++i) { // NOLINT
    auto *LI = LoopNest[i];
    if (!SE->isLoopInvariant(S, LI)) {
      LLVM_DEBUG(S->dump(); DSA_INFO << "Is NOT a loop invariant under ";
                 LI->dump());
      return false;
    }
  }
  return true;
}

/// Chech if a SCEV can be a repeat stretch
bool CanBeStretched(int x, const std::vector<Loop*> &LoopNest, // NOLINT
                    ScalarEvolution *SE) {
  if (x != 1) {
    LLVM_DEBUG(DSA_INFO << "[Can be stretch] x != 1\n");
    return false;
  }
  if (LoopNest.size() <= 1) {
    LLVM_DEBUG(DSA_INFO << "[Can be stretch] Too few loops to stretch!\n");
    return false;
  }
  const SCEV *S = SE->getBackedgeTakenCount(LoopNest[0]);
  if (S->getSCEVType() != scAddRecExpr) {
    LLVM_DEBUG(DSA_INFO << "[Can be stretch] trip count not stretch!\n");
    return false;
  }
  if (!SE->isLoopInvariant(S, LoopNest[1])) {
    for (size_t i = 2; i < LoopNest.size(); ++i) { // NOLINT
      auto *LI = LoopNest[i];
      if (!SE->isLoopInvariant(S, LI)) {
        LLVM_DEBUG(S->dump();
                   DSA_INFO << "[Can be stretch] Is NOT a loop invariant under ";
                   LI->dump());
        return false;
      }
    }
    const auto *SARE = dyn_cast<SCEVAddRecExpr>(S)->getStart();
    if (!CheckLoopInvariant(SARE, 1, LoopNest, SE)) {
      LLVM_DEBUG(DSA_INFO << "[Can be stretch] trip count not invariant!\n");
      return false;
    }
    return true;
  }
  LLVM_DEBUG(
      DSA_INFO << "[Can be stretch] invariant for the right outside loop!\n");
  return false;
}

DFGEntry *DFGBase::InThisDFG(Value *Val) {
  for (auto &Elem : Entries) {
    for (auto &Iter : Elem->underlyingValues()) {
      if (Iter == Val) {
        return Elem;
      }
    }
  }
  return nullptr;
}

Instruction *DFGBase::DefaultIP() { assert(false && "Not supported yet!"); }

Instruction *TemporalDFG::DefaultIP() { return IP; }

Instruction *DedicatedDFG::DefaultIP() { 
  return Preheader ? &Preheader->back() : nullptr;
}

Accumulator *DedicatedDFG::ConsumedByAccumulator(MemPort *MP) {
  std::set<Value *> Visited{MP->underlyingInst()};
  std::queue<Value *> Q;
  Q.push(MP->underlyingInst());
  while (!Q.empty()) {
    auto *Cur = Q.front();
    Q.pop();
    for (auto *User : Cur->users()) {
      if (auto *DE = InThisDFG(User)) {
        if (isa<Accumulator>(DE)) {
          return dyn_cast<Accumulator>(DE);
        }
      }
      if (Visited.find(User) == Visited.end()) {
        Q.push(User);
        Visited.insert(User);
      }
    }
  }
  return nullptr;
}

int ScalarBits2T(int Bits) { // NOLINT
  switch (Bits) {
  case 64:
    return 0;
  case 32:
    return 1;
  case 16:
    return 2;
  case 8:
    return 3;
  }
  assert(false);
}

DFGBase *DFGBase::BelongOtherDFG(Instruction *I) {
  for (auto &DFG : Parent->DFGs) {
    if (DFG == this)
      continue;
    if (DFG->Contains(I))
      return DFG;
  }
  return nullptr;
}

std::pair<std::set<Instruction *>, std::set<Instruction *>>
BFSOperands(DFGBase *DFG, DominatorTree *DT, Instruction *From) { // NOLINT

  std::set<Instruction *> Visited, OutBound;
  std::queue<Instruction *> Q;

  Visited.insert(From);
  Q.push(From);

  while (!Q.empty()) {
    auto *Cur = Q.front();
    Q.pop();
    for (size_t i = 0; i < Cur->getNumOperands(); ++i) { // NOLINT
      if (auto *Inst = dyn_cast<Instruction>(Cur->getOperand(i))) {
        if (!DT->dominates(Inst, From)) {
          continue;
        }
        if (!Visited.count(Inst)) {
          if (DFG->InThisScope(Inst)) {
            Visited.insert(Inst);
            Q.push(Inst);
          } else {
            OutBound.insert(Inst);
          }
        }
      }
    }
  }

  return {Visited, OutBound};
}

Predicate *DFGBase::FindEquivPredicate(Value *LHS, Value *RHS) {
  for (auto *Elem : EntryFilter<Predicate>()) {
    if (Elem->Cond[0]->getOperand(0) == LHS &&
        Elem->Cond[0]->getOperand(1) == RHS)
      return Elem;
    if (Elem->Cond[0]->getOperand(1) == LHS &&
        Elem->Cond[0]->getOperand(0) == RHS)
      return Elem;
  }
  return nullptr;
}

bool DedicatedDFG::Contains(const Loop *L) {
  for (auto *Elem : LoopNest) {
    if (Elem == L)
      return true;
  }
  return false;
}

Value *DedicatedDFG::TripCount(int x, Instruction *InsertBefore) { // NOLINT
  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");
  auto *IB = Parent->Query->IBPtr;
  auto *BackSE = Parent->Query->SE->getBackedgeTakenCount(LoopNest[x]);
  assert(CheckLoopInvariant(BackSE, x + 1, LoopNest, Parent->Query->SE));
  auto *BackTaken = Expander.expandCodeFor(BackSE, nullptr, InsertBefore);
  IB->SetInsertPoint(InsertBefore);
  auto *Trip =
      IB->CreateAdd(BackTaken, createConstant(getCtx(), 1), "trip.count");
  return Trip;
}

Value *DedicatedDFG::ProdTripCount(int l, int r, Instruction *InsertBefore) { // NOLINT
  Value *Prod = createConstant(getCtx(), 1);
  for (int i = l; i < r; ++i) { // NOLINT
    Prod = BinaryOperator::Create(BinaryOperator::Mul, Prod,
                                  TripCount(i, InsertBefore), "trip.prod",
                                  InsertBefore);
  }
  return Prod;
}

Value *DedicatedDFG::ProdTripCount(int x, Instruction *InsertBefore) { // NOLINT
  return ProdTripCount(0, x, InsertBefore);
}

DedicatedDFG::DedicatedDFG(DFGFile *Parent_, Loop *LI, int Unroll) // NOLINT
    : DFGBase(Parent_), UnrollFactor(Unroll) {

  TyEnum = DFGBase::Dedicated;

  if (GetUnrollMetadata(LI->getLoopID(), "llvm.loop.ss.datamove")) {
    LLVM_DEBUG(DSA_INFO << "A data-move 'DFG'\n");
  }

  LoopNest.push_back(LI);
  while (LoopNest.back()->getLoopDepth() > 1) {
    auto *Cur = LoopNest.back();
    LLVM_DEBUG(DSA_INFO << "Loop level: " << *Cur; DSA_INFO << Cur->getLoopDepth());
    if (GetUnrollMetadata(Cur->getLoopID(), "llvm.loop.ss.stream")) {
      break;
    }
    LoopNest.push_back(Cur->getParentLoop());
  }

  DSA_CHECK(GetUnrollMetadata(LoopNest.back()->getLoopID(), "llvm.loop.ss.stream"))
    << "A stream level required!\n" << *LoopNest.back() << "\n" << *LoopNest.back()->getLoopID();

  Loop *InnerLoop = nullptr;
  std::set<BasicBlock *> Exclude;

  for (auto *LI : LoopNest) {
    LLVM_DEBUG(DSA_INFO << "Loop: "; LI->dump());
    for (auto *Child : LI->getSubLoops()) {
      if (Child != InnerLoop) {
        for (auto &Block : Child->getBlocks())
          Exclude.insert(Block);
      }
    }

    for (auto &Block : LI->getBlocks()) {
      if (!Exclude.count(Block))
        Blocks.insert(Block);
    }

    InnerLoop = LI;
  }

  LLVM_DEBUG(DSA_INFO << "DFG" << (void *)(this) << ": ";
             for (auto Block
                  : Blocks) { DSA_INFO << (void *)Block << ", "; });

  LLVM_DEBUG(DSA_INFO << "Init blocks done\n");

  auto *OuterMost = LoopNest.back();
  if (!(Preheader = OuterMost->getLoopPreheader())) {
    Preheader = InsertPreheaderForLoop(OuterMost, Parent->Query->DT,
                                       Parent->Query->LI, nullptr, false);
  }

  auto *Prologue = FindLoopPrologue(LoopNest.back());
  assert(Prologue);
  PrologueIP = &Prologue->back();
}

void DFGBase::dump(std::ostringstream &OS) {}

void DFGFile::addDFG(DFGBase *DB) {
  assert(!AllInitialized &&
         "You can no longer modify the dfg after scheduling");
  DFGs.push_back(DB);
}

Loop *DedicatedDFG::InnerMost() { return LoopNest.front(); }

Loop *DedicatedDFG::OuterMost() { return LoopNest.back(); }

DFGBase::DFGBase(DFGFile *Parent_) : Parent(Parent_) { // NOLINT
  ID = Parent_->DFGs.size();
  TyEnum = DFGBase::Unknown;
}

DFGBase::DFGKind DFGBase::getKind() const { return TyEnum; }

TemporalDFG::TemporalDFG(DFGFile *Parent, IntrinsicInst *Begin,
                         IntrinsicInst *End)
    : DFGBase(Parent), Begin(Begin), End(End) {

  std::set<Instruction *> Users;
  for (Instruction *I = Begin; I != End; I = I->getNextNode()) {
    for (auto *Usr : I->users()) {
      if (auto *Inst = dyn_cast<Instruction>(Usr)) {
        if (Inst->getParent() == Begin->getParent()) {
          Users.insert(Inst);
        }
      }
    }
  }

  for (auto &Inst : *Begin->getParent()) {
    if (Users.count(&Inst)) {
      IP = &Inst;
    }
  }

  TyEnum = DFGBase::Temporal;
}

void TemporalDFG::dump(std::ostringstream &OS) {
  if (!OS.str().empty())
    OS << "\n----\n\n";
  OS << "#pragma group temporal\n";
  DFGBase::dump(OS);
}

void DedicatedDFG::dump(std::ostringstream &OS) {
  if (!OS.str().empty())
    OS << "\n----\n\n";
  if (dsa::utils::ModuleContext().TRIGGER) {
    DSA_CHECK(dsa::utils::ModuleContext().TemporalFound)
        << "Trigger cannot be enabled without temporal";
    OS << "#pragma group temporal\n";
  }
  DFGBase::dump(OS);
}

bool DedicatedDFG::Contains(Instruction *Inst) {

  // FIXME(@were): I forgot what this is doing.

  // if (Inst->getParent() == Parent->Config->getParent()) {
  //   for (Instruction *I = Parent->Config, *E =
  //   &Parent->Config->getParent()->back();
  //        I != E; I = I->getNextNode()) {
  //     if (I == Inst)
  //       return true;
  //   }
  // }

  // if (Inst->getParent() == Parent->Fence->getParent()) {
  //   for (Instruction *I = Inst, *E = &Parent->Fence->getParent()->back();
  //        I != E; I = I->getNextNode()) {
  //     if (I == Inst)
  //       return true;
  //   }
  // }

  return Contains(Inst->getParent());
}

bool DedicatedDFG::Contains(BasicBlock *BB) {
  // FIXME: I hope for now it is good enough.
  //        Later maybe we need to dive into the paritally contain thing.
  return Blocks.find(BB) != Blocks.end();
}

bool TemporalDFG::Contains(Instruction *Inst) {
  for (Instruction *I = Begin; I != End; I = I->getNextNode())
    if (I == Inst)
      return true;
  return false;
}

bool TemporalDFG::Contains(BasicBlock *BB) { return BB == Begin->getParent(); }

int TemporalDFG::getUnroll() { return 1; }

int DedicatedDFG::getUnroll() { return UnrollFactor; }

AnalyzedStream DedicatedDFG::AnalyzeDataStream(Value *Index, int Bytes) {
  return AnalyzeDataStream(Index, Bytes, false, nullptr);
}

AnalyzedStream DedicatedDFG::AnalyzeDataStream(Value *Index, int Bytes,
                                               bool DoOuterRepeat,
                                               Instruction *InsertBefore) {

  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");
  auto *IB = Parent->Query->IBPtr;

  if (InsertBefore == nullptr)
    InsertBefore = DefaultIP();

  IB->SetInsertPoint(InsertBefore);

  assert(InsertBefore);

  LLVM_DEBUG(DSA_INFO << "Analyzing index "; Index->dump();
             DSA_INFO << "Bytes: " << Bytes << "\n");

  auto *SE = Parent->Query->SE;
  AnalyzedStream Res;
  Value *One = createConstant(getCtx(), 1);
  Res.AR.Wrapped = One;

  size_t i = 0; // NOLINT
  for (; i < LoopNest.size(); ++i) {
    auto *LI = LoopNest[i];
    LLVM_DEBUG(DSA_INFO << "Loop: "; LI->dump());
    if (!LI->isLoopInvariant(Index)) {
      LLVM_DEBUG(DSA_INFO << "Non-Invariant here!\n");
      break;
    }
  }

  if (i) {
    Res.AR.Prime = SE->getBackedgeTakenCount(LoopNest[0]);
  }
  if (CanBeStretched(i, LoopNest, SE)) {
    Res.AR.PT = AnalyzedRepeat::StretchedRepeat;
  } else {
    if (CanBeStretched(1, LoopNest, SE)) {
      Res.AR.PT = AnalyzedRepeat::SumOfStretchedRepeat;
      Res.AR.Wrapped = ProdTripCount(2, i, InsertBefore);
    } else if (i) {
      Res.AR.Wrapped = ProdTripCount(1, i, InsertBefore);
    }
  }

  if (!SE->isSCEVable(Index->getType())) {
    assert(DoOuterRepeat);
    Res.OuterRepeat = ProdTripCount(i, LoopNest.size(), InsertBefore);
    return Res;
  }

  const auto *EV = SE->getSCEV(Index);
  LLVM_DEBUG(EV->dump(); DSA_INFO << "Index (" << EV->getSCEVType() << "): ";
             EV->dump());

  if (i == LoopNest.size()) {
    LLVM_DEBUG(DSA_INFO << "Prime Repeat: "; Res.AR.Prime->dump();
               DSA_INFO << "Wrapped Repeat: "; Res.AR.Wrapped->dump();
               DSA_INFO << "\n");
    return Res;
  }

  if (EV->getSCEVType() != scAddRecExpr) {
    assert(DoOuterRepeat);
    Res.OuterRepeat = ProdTripCount(i, LoopNest.size(), InsertBefore);
    return Res;
  }

  assert(EV->getSCEVType() == scAddRecExpr &&
         "The loop should starts with a polyhedral");

  int RawSize = Bytes;
  Value *Cnt = createConstant(getCtx(), RawSize);

  int Stretch = 0;

  for (bool FirstExec = true; i < LoopNest.size(); ++i, FirstExec = false) {

    const auto *Cur = dyn_cast<SCEVAddRecExpr>(EV);
    LLVM_DEBUG(EV->dump());

    if (DoOuterRepeat && (!Cur || Cur->getLoop() != LoopNest[i])) {
      IB->SetInsertPoint(InsertBefore);
      Res.OuterRepeat = ProdTripCount(i + 1, LoopNest.size(), InsertBefore);
      LLVM_DEBUG(DSA_INFO << "Loop gap detected! Get outer repeat!\n");
      break;
    }

    Value *Step = nullptr;
    if (Cur) {
      assert(
          CheckLoopInvariant(Cur->getStepRecurrence(*SE), i + 2, LoopNest, SE));
      Step = Expander.expandCodeFor(Cur->getStepRecurrence(*SE), nullptr,
                                    InsertBefore);
      const auto *L = Cur->getLoop();
      LLVM_DEBUG(DSA_INFO << "Cur: "; Cur->getLoop()->dump(); DSA_INFO << "Nest:";
                 LoopNest[i]->dump(););
      if (L != LoopNest[i]) {
        // FIXME: Later check required, but I think it is correct for now.
        assert(L->contains(LoopNest[i]));
        Step = createConstant(getCtx(), 0);
      } else {
        EV = Cur->getStart();
      }
      LLVM_DEBUG(DSA_INFO << "======= Loop Induction =======\n");
    } else if (SE->isLoopInvariant(EV, LoopNest[i])) {
      Step = createConstant(getCtx(), 0);
      LLVM_DEBUG(DSA_INFO << "======= Loop Invariant =======\n");
    } else if (const auto *SAE = dyn_cast<SCEVAddExpr>(EV)) {
      SAE->dump();
      Index->dump();
      assert(false);
    }

    int StretchInt = 0;
    const auto *BackTaken = SE->getBackedgeTakenCount(LoopNest[i]);
    Value *DimTripCount = nullptr;

    if (CheckLoopInvariant(BackTaken, i + 1, LoopNest, SE)) {
      assert(CheckLoopInvariant(BackTaken, i + 2, LoopNest, SE));
      DimTripCount = TripCount(i, InsertBefore);
    } else {
      /// Support triangular streams
      if (!SE->isLoopInvariant(BackTaken, LoopNest[i + 1])) {
        assert(CheckLoopInvariant(BackTaken, i + 2, LoopNest, SE));
      }
      const auto *BackTaken_ = dyn_cast<SCEVAddRecExpr>(BackTaken); // NOLINT
      assert(BackTaken_);
      auto *Cnt = Expander.expandCodeFor(BackTaken_->getStart(), nullptr, InsertBefore);
      assert(CheckLoopInvariant(BackTaken_->getStart(), i + 1, LoopNest, SE));
      IB->SetInsertPoint(InsertBefore);
      DimTripCount = IB->CreateAdd(Cnt, One, "trip.count");
      Value *NextStretch = nullptr;
      if (i + 1 < LoopNest.size() && BackTaken_->getLoop() == LoopNest[i + 1]) {
        NextStretch = Expander.expandCodeFor(BackTaken_->getStepRecurrence(*SE),
                                             nullptr, InsertBefore);
      } else {
        NextStretch = createConstant(getCtx(), 0);
      }
      auto *StretchConst = dyn_cast<Constant>(NextStretch);
      assert(StretchConst);
      StretchInt = StretchConst->getUniqueInteger().getSExtValue();
      LLVM_DEBUG(DSA_INFO << "Stretch: "; NextStretch->dump());
    }

    /// Coalease the inner most dimension
    if (FirstExec) {
      bool Coalease = false;
      if (isa<Constant>(Cnt)) {
        int64_t CntInt =
            dyn_cast<Constant>(Cnt)->getUniqueInteger().getSExtValue();
        StretchInt *= CntInt;
        if (isa<Constant>(Step)) {
          int64_t StepInt =
              dyn_cast<Constant>(Step)->getUniqueInteger().getSExtValue();
          if (CntInt == StepInt) {
            IB->SetInsertPoint(InsertBefore);
            Cnt = IB->CreateMul(Step, DimTripCount);
            Coalease = true;
          }
        }
      }

      if (Coalease) {
        Stretch = StretchInt;
        LLVM_DEBUG(DSA_INFO << "Coaleased!\nStretch: " << StretchInt << "\n");
        continue;
      }
    }

    Res.Dimensions.emplace_back(Step, DimTripCount, Stretch);

    LLVM_DEBUG(DSA_INFO << "Injected: "; InsertBefore->dump();
               DSA_INFO << "Current: "; Step->dump();
               DSA_INFO << "Stretch: " << Stretch; DSA_INFO << "\n");

    Stretch = StretchInt;
  }

  LLVM_DEBUG(DSA_INFO << "After exiting: "; EV->dump());

  Value *Start = nullptr;

  Start = Expander.expandCodeFor(EV, nullptr, &Preheader->back());
  if (const auto *SARE = dyn_cast<SCEVAddRecExpr>(EV)) {
    if (SARE->getLoop() != LoopNest.back() &&
        SARE->getLoop()->contains(LoopNest.back())) {
      Start =
          Expander.expandCodeFor(SARE->getStart(), nullptr, &Preheader->back());
      auto *IndVar = SARE->getLoop()->getCanonicalInductionVariable();
      assert(IndVar);
      auto *Stride = Expander.expandCodeFor(SARE->getStepRecurrence(*SE),
                                            nullptr, InsertBefore);
      IB->SetInsertPoint(InsertBefore);
      auto *Delta = IB->CreateMul(IndVar, Stride);
      auto *Casted = IB->CreatePtrToInt(Start, Delta->getType());
      Start = IB->CreateAdd(Casted, Delta, "", InsertBefore);
      LLVM_DEBUG(DSA_INFO << "Due to out of loop contribution: "; Start->dump());
    } else {
      // FIXME: Why did I leave this branch empty?
    }
  }

  Res.Dimensions.emplace_back(Start, Cnt, 0);

  LLVM_DEBUG(DSA_INFO << "\n");

  return Res;
}

Value *AnalyzedStream::BytesFromMemory(IRBuilder<> *IB) {
  Value *Res = createConstant(IB->getContext(), 1);
  for (size_t i = 0; i < Dimensions.size(); ++i) // NOLINT
    Res = IB->CreateMul(Res, std::get<1>(Dimensions[i]), "");
  return Res;
}

Value *DFGBase::UnrollConstant() {
  return Parent->Query->IBPtr->getInt64(getUnroll());
}

LLVMContext &DFGBase::getCtx() { return Parent->getCtx(); }

LLVMContext &DFGFile::getCtx() { return Query->IBPtr->getContext(); }

template <typename DFGType> void AddDFG(DFGFile *DF, MDNode *Ptr, Loop *LI) { // NOLINT
  assert(Ptr->getNumOperands() == 2);
  auto *MDFactor = dyn_cast<ConstantAsMetadata>(Ptr->getOperand(1));
  assert(MDFactor);
  int Factor = (int)MDFactor->getValue()->getUniqueInteger().getSExtValue();
  DF->addDFG(new DFGType(DF, LI, Factor));
}

DFGFile::DFGFile(IntrinsicInst *Start, IntrinsicInst *End,
                 StreamSpecialize *Query)
    : Func(*Start->getParent()->getParent()), Config(Start),
      Fence(End), Query(Query) {}

int getPortImpl() {
  static const int Ports[] = {23, 24, 25, 26, 27, 28, 29, 30, 31};
  static const int N = (sizeof Ports) / (sizeof(int));
  static int Cur = 0;
  int Res = Ports[Cur];
  Cur = (Cur + 1) % N;
  return Res;
}

int DFGBase::getNextIND() {
  return getPortImpl();
  // static const int Ports[] = {27, 28, 29, 30, 31};
  // static const int N = (sizeof Ports) / (sizeof(int));
  // static int Cur = 0;
  // int Res = Ports[Cur];
  // Cur = (Cur + 1) % N;
  // return Res;
}

int DFGBase::getNextReserved() {
  return getPortImpl();
  // static const int Ports[] = {23, 24, 25, 26};
  // static const int N = (sizeof Ports) / (sizeof(int));
  // static int Cur = 0;
  // int Res = Ports[Cur];
  // Cur = (Cur + 1) % N;
  // return Res;
}

std::vector<BasicBlock *> DedicatedDFG::getBlocks() {
  std::vector<BasicBlock *> Res(InnerMost()->getBlocks().begin(),
                                InnerMost()->getBlocks().end());
  return Res;
}

std::vector<BasicBlock *> TemporalDFG::getBlocks() {
  std::vector<BasicBlock *> Res{Begin->getParent()};
  return Res;
}

AnalyzedStream TemporalDFG::AnalyzeDataStream(Value *Index, int Bytes) {
  AnalyzedStream Res;
  auto &Ctx = Parent->getCtx();
  Res.AR.Wrapped = createConstant(Ctx, 1);
  Res.Dimensions.emplace_back(Index, createConstant(Ctx, Bytes), 0);
  return Res;
}

bool DedicatedDFG::InThisScope(Instruction *I) {
  return LoopNest.back()->getBlocksSet().count(I->getParent());
}

bool TemporalDFG::InThisScope(Instruction *Inst) {
  for (Instruction *I = Begin; I != End; I = I->getNextNode()) {
    if (I == Inst) {
      return true;
    }
  }
  return false;
}

void DFGBase::accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }
void DedicatedDFG::accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }
void TemporalDFG::accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }

std::string DFGBase::nameOf(Value *Val, int VecIdx) {
  auto *Entry = InThisDFG(Val);
  DSA_CHECK(Entry) << "CANNOT find entry for " << Val << ": " << *Val;
  auto Vs = Entry->underlyingValues();
  auto Iter = std::find(Vs.begin(), Vs.end(), Val);
  DSA_CHECK(Iter != Vs.end());
  int ValueIdx = Iter - Vs.begin();
  std::ostringstream OSS;
  OSS << "sub" << ID << "_v" << Entry->ID << "_" << ValueIdx << "_";
  if (VecIdx != -1 && Entry->shouldUnroll()) {
    OSS << VecIdx;
  }
  return OSS.str();
}

DedicatedDFG::DedicatedDFG(DFGFile *P, dsa::analysis::SEWrapper *SW) : DFGBase(P) {
  DSA_INFO << SW->toString();
  auto *IP = dyn_cast<dsa::analysis::IndirectPointer>(SW);
  DSA_CHECK(IP) << SW->toString();
  auto *SU = dyn_cast<SCEVUnknown>(SW->Raw);
  auto *Load = dyn_cast<LoadInst>(SU->getValue());
  Entries.push_back(new MemPort(this, Load));
  Entries.push_back(new OutputPort(this, Load));
}

