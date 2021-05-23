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
#include "StreamAnalysis.h"
#include "Transformation.h"
#include "Util.h"

#include "dsa/rf.h"
#include "dsa/spec.h"
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

namespace inject {

std::stack<IRBuilder<> *> DSAIntrinsicEmitter::REG::IBStack;

MemoryType
InjectLinearStream(IRBuilder<> *IB,
                   const std::vector<dsa::utils::StickyRegister> &Regs,
                   int PortNum, const AnalyzedStream &Stream,
                   MemoryOperation MO, Padding PP, MemoryType MT, int DType) {
  DSAIntrinsicEmitter DIE(IB, Regs);
  Value *Start = std::get<0>(Stream.Dimensions.back());
  Value *Bytes = std::get<1>(Stream.Dimensions.back());
  Value *DTyValue = IB->getInt64(DType);
  if (Stream.Dimensions.size() == 1) {
    DIE.INSTANTIATE_1D_STREAM(Start, DType, DIE.DIV(Bytes, DTyValue), PortNum,
                              PP, DSA_Access, MO, MT, DType, 0);
    return DMT_DMA;
  } else if (Stream.Dimensions.size() == 2) {
    Value *Stride = std::get<0>(Stream.Dimensions[0]);
    Value *N = std::get<1>(Stream.Dimensions[0]);
    int Stretch = std::get<2>(Stream.Dimensions[0]);
    DIE.INSTANTIATE_2D_STREAM(Start, DType, DIE.DIV(Bytes, DTyValue),
                              DIE.DIV(Stride, DTyValue),
                              IB->getInt64(Stretch / DType), N, PortNum, PP,
                              DSA_Access, MO, MT, DType, 0);
    return DMT_DMA;
  } else {
    llvm::errs() << Stream.Dimensions.size();
  }
  llvm_unreachable("Unsupported stream dimension");
}

} // namespace inject
} // namespace dsa

const std::string &DFGFile::getName() { return FileName; }

/// Check if a given SCEV is loop invariant
bool CheckLoopInvariant(const SCEV *S, int From,
                        const std::vector<Loop*> &LoopNest,
                        ScalarEvolution *SE) {
  for (size_t i = From; i < LoopNest.size(); ++i) {
    auto LI = LoopNest[i];
    if (!SE->isLoopInvariant(S, LI)) {
      LLVM_DEBUG(S->dump(); dbgs() << "Is NOT a loop invariant under ";
                 LI->dump());
      return false;
    }
  }
  return true;
}

Value *DFGBase::ComputeRepeat(Value *Prime, Value *Wrapper, bool isVectorized,
                              bool isPortConfig) {
  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");
  auto &IB = *Parent->Query->IBPtr;
  if (IB.GetInsertPoint() != DefaultIP()->getIterator())
    IB.SetInsertPoint(DefaultIP());
  if (isVectorized) {
    if (isPortConfig) {
      if (isOne(Wrapper)) {
        auto ShiftedPrime = IB.CreateShl(Prime, 3);
        auto VectorizedPrime = IB.CreateUDiv(ShiftedPrime, UnrollConstant());
        return VectorizedPrime;
      } else {
        auto CD = CeilDiv(Prime, UnrollConstant(), DefaultIP());
        return IB.CreateShl(IB.CreateMul(CD, Wrapper), 3);
      }
    } else {
      auto CD = CeilDiv(Prime, UnrollConstant(), DefaultIP());
      return IB.CreateMul(CD, Wrapper);
    }
  } else {
    auto Res = IB.CreateMul(Prime, Wrapper);
    if (isPortConfig) {
      return IB.CreateShl(Res, 3);
    }
    return Res;
  }
}

Value *DFGBase::ComputeRepeat(const AnalyzedRepeat &AR, bool isVectorized,
                              bool isPortConfig) {
  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");
  if (!AR.Prime)
    return createConstant(getCtx(), 1);
  return ComputeRepeat(Expander.expandCodeFor(AR.Prime, nullptr, DefaultIP()),
                       AR.Wrapped, isVectorized, isPortConfig);
}

/// Chech if a SCEV can be a repeat stretch
bool CanBeStretched(int x, const std::vector<Loop*> &LoopNest,
                    ScalarEvolution *SE) {
  if (x != 1) {
    LLVM_DEBUG(dbgs() << "[Can be stretch] x != 1\n");
    return false;
  }
  if (LoopNest.size() <= 1) {
    LLVM_DEBUG(dbgs() << "[Can be stretch] Too few loops to stretch!\n");
    return false;
  }
  const SCEV *S = SE->getBackedgeTakenCount(LoopNest[0]);
  if (S->getSCEVType() != scAddRecExpr) {
    LLVM_DEBUG(dbgs() << "[Can be stretch] trip count not stretch!\n");
    return false;
  }
  if (!SE->isLoopInvariant(S, LoopNest[1])) {
    for (size_t i = 2; i < LoopNest.size(); ++i) {
      auto LI = LoopNest[i];
      if (!SE->isLoopInvariant(S, LI)) {
        LLVM_DEBUG(S->dump();
                   dbgs() << "[Can be stretch] Is NOT a loop invariant under ";
                   LI->dump());
        return false;
      }
    }
    auto SARE = dyn_cast<SCEVAddRecExpr>(S)->getStart();
    if (!CheckLoopInvariant(SARE, 1, LoopNest, SE)) {
      LLVM_DEBUG(dbgs() << "[Can be stretch] trip count not invariant!\n");
      return false;
    } else {
      return true;
    }
  }
  LLVM_DEBUG(
      dbgs() << "[Can be stretch] invariant for the right outside loop!\n");
  return false;
}

DFGEntry *DFGBase::InThisDFG(Value *Val) {
  for (auto &Elem : Entries) {
    for (auto &Iter : Elem->UnderlyingValues()) {
      if (Iter == Val) {
        return Elem;
      }
    }
  }
  return nullptr;
}

Instruction *DFGBase::DefaultIP() { assert(false && "Not supported yet!"); }

Instruction *TemporalDFG::DefaultIP() { return IP; }

Instruction *DedicatedDFG::DefaultIP() { return &Preheader->back(); }

bool DedicatedDFG::ConsumedByAccumulator(MemPort *MP) {
  std::set<Value *> Visited{MP->UnderlyingInst()};
  std::queue<Value *> Q;
  Q.push(MP->UnderlyingInst());
  while (!Q.empty()) {
    auto Cur = Q.front();
    Q.pop();
    for (auto User : Cur->users()) {
      if (auto DE = InThisDFG(User)) {
        if (isa<Accumulator>(DE)) {
          return true;
        }
      }
      if (Visited.find(User) == Visited.end()) {
        Q.push(User);
        Visited.insert(User);
      }
    }
  }
  return false;
}

int ScalarBits2T(int Bits) {
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

Instruction *DFGBase::InjectRepeat(const AnalyzedRepeat &AR, Value *Val,
                                   int Port) {
  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");

  if (!AR.Prime) {
    LLVM_DEBUG(dbgs() << "No repeat!\n");
    return nullptr;
  }

  auto SE = Parent->Query->SE;
  auto IB = Parent->Query->IBPtr;
  auto One = createConstant(getCtx(), 1);

  IB->SetInsertPoint(DefaultIP());

  if (AR.PT == AnalyzedRepeat::PlainRepeat) {
    auto PrimeRepeat = Expander.expandCodeFor(AR.Prime, nullptr, DefaultIP());
    return InjectRepeat(IB->CreateAdd(PrimeRepeat, createConstant(getCtx(), 1)),
                        AR.Wrapped, 0, Val, Port);
  } else if (AR.PT == AnalyzedRepeat::StretchedRepeat) {
    assert(AR.Prime->getSCEVType() == scAddRecExpr);
    auto SARE = dyn_cast<SCEVAddRecExpr>(AR.Prime);
    auto BT = Expander.expandCodeFor(SE->getBackedgeTakenCount(SARE->getLoop()),
                                     nullptr, DefaultIP());
    auto SV = Expander.expandCodeFor(SARE->getStepRecurrence(*SE), nullptr,
                                     DefaultIP());
    assert(isa<ConstantInt>(SV));
    return InjectRepeat(IB->CreateAdd(BT, One), AR.Wrapped,
                        dyn_cast<ConstantInt>(SV)->getSExtValue(), Val, Port);
  } else if (AR.PT == AnalyzedRepeat::SumOfStretchedRepeat) {
    // FIXME: Kinda ugly here.
    // Once we have a better hardware support to do this we no longer need this
    assert(AR.Prime->getSCEVType() == scAddRecExpr);
    auto SARE = dyn_cast<SCEVAddRecExpr>(AR.Prime);
    auto First = IB->CreateAdd(
        Expander.expandCodeFor(SARE->getStart(), nullptr, DefaultIP()), One);
    auto BT = Expander.expandCodeFor(SE->getBackedgeTakenCount(SARE->getLoop()),
                                     nullptr, DefaultIP());
    auto SV = Expander.expandCodeFor(SARE->getStepRecurrence(*SE), nullptr,
                                     DefaultIP());
    auto SVCI = dyn_cast<ConstantInt>(SV);
    CHECK(SVCI);
    auto SVInt = SVCI->getSExtValue();
    CHECK(SVInt == 1 || SVInt == -1);
    auto Last = IB->CreateAdd(First, IB->CreateMul(BT, SV));

    switch (getUnroll()) {
    case 1: {
      // (First + Last) * (BT + 1) / 2
      auto Prime = IB->CreateUDiv(
          IB->CreateMul(IB->CreateAdd(First, Last), IB->CreateAdd(BT, One)),
          createConstant(getCtx(), 2));
      return InjectRepeat(Prime, AR.Wrapped,
                          /*I am not sure if put 0 here is correct*/ 0, Val,
                          Port);
    }
    case 2: {
      Value *Range;
      if (SVInt == -1) {
        // FIXME: Support last != 0 case later.
        auto F2 = IB->CreateAdd(First, IB->getInt64(2));
        auto FF =
            IB->CreateUDiv(IB->CreateMul(F2, F2), createConstant(getCtx(), 4));
        Range = FF;
      } else {
        assert(false && "Not supported yet...");
      }
      Range = IB->CreateShl(Range, 1);
      return InjectRepeat(Range, AR.Wrapped, /*Same as above*/ 0, Val, Port);
    }
    default: {
      llvm_unreachable("Not supported vectorization width");
    }
    }
    llvm_unreachable("Not supported yet...");
    return nullptr;
  }

  llvm_unreachable("Unknown kind of AnalyzedRepeat's Repeat Type");
}

Instruction *DFGBase::InjectRepeat(Value *Prime, Value *Wrapper,
                                   int64_t Stretch, Value *Val, int Port) {

  auto IP = DefaultIP();
  auto &IB = *Parent->Query->IBPtr;
  IB.SetInsertPoint(IP);

  auto ShiftedStretch = createConstant(getCtx(), Stretch << 3);
  auto VectorizedStretch = IB.CreateSDiv(ShiftedStretch, UnrollConstant());
  auto ActualStretch = IB.CreateShl(VectorizedStretch, 1);
  (void)ActualStretch;

  dsa::inject::DSAIntrinsicEmitter DIE(Parent->Query->IBPtr,
                                       Parent->Query->DSARegs);
  if (Val == nullptr) {
    auto Repeat = IB.CreateAdd(
        IB.CreateSDiv(IB.CreateSub(Prime, IB.getInt64(1)), UnrollConstant()),
        IB.getInt64(1));
    DIE.SS_CONFIG_PORT(Port, DPF_PortRepeat, Repeat);
    if (Stretch) {
      DIE.SS_CONFIG_PORT(Port, DPF_PortPeriod, getUnroll());
      DIE.SS_CONFIG_PORT(Port, DPF_PortRepeatStretch, Stretch);
    }
    return DIE.res.back();
  } else {
    LLVM_DEBUG(dbgs() << "Inject Repeat: "; Val->dump();
               dbgs() << "For port: " << Port);
    assert(Port != -1);
    DIE.SS_CONST(Port, Val,
                 /*Times=*/ComputeRepeat(Prime, Wrapper, true, false),
                 /*Const Type*/ Val->getType()->getScalarSizeInBits() / 8);
    return DIE.res.back();
  }
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
BFSOperands(DFGBase *DFG, DominatorTree *DT, Instruction *From) {

  std::set<Instruction *> Visited, OutBound;
  std::queue<Instruction *> Q;

  Visited.insert(From);
  Q.push(From);

  while (!Q.empty()) {
    auto Cur = Q.front();
    Q.pop();
    for (size_t i = 0; i < Cur->getNumOperands(); ++i) {
      if (auto Inst = dyn_cast<Instruction>(Cur->getOperand(i))) {
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
  for (auto Elem : EntryFilter<Predicate>()) {
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
  for (auto Elem : LoopNest) {
    if (Elem == L)
      return true;
  }
  return false;
}

Value *DedicatedDFG::TripCount(int x, Instruction *InsertBefore) {
  SCEVExpander Expander(*Parent->Query->SE,
                        Parent->Func.getParent()->getDataLayout(), "");
  auto IB = Parent->Query->IBPtr;
  auto BackSE = Parent->Query->SE->getBackedgeTakenCount(LoopNest[x]);
  assert(CheckLoopInvariant(BackSE, x + 1, LoopNest, Parent->Query->SE));
  auto BackTaken = Expander.expandCodeFor(BackSE, nullptr, InsertBefore);
  IB->SetInsertPoint(InsertBefore);
  auto Trip =
      IB->CreateAdd(BackTaken, createConstant(getCtx(), 1), "trip.count");
  return Trip;
}

Value *DedicatedDFG::ProdTripCount(int l, int r, Instruction *InsertBefore) {
  Value *Prod = createConstant(getCtx(), 1);
  for (int i = l; i < r; ++i) {
    Prod = BinaryOperator::Create(BinaryOperator::Mul, Prod,
                                  TripCount(i, InsertBefore), "trip.prod",
                                  InsertBefore);
  }
  return Prod;
}

Value *DedicatedDFG::ProdTripCount(int x, Instruction *InsertBefore) {
  return ProdTripCount(0, x, InsertBefore);
}

DedicatedDFG::DedicatedDFG(DFGFile *Parent_, Loop *LI, int Unroll)
    : DFGBase(Parent_), UnrollFactor(std::max(1, Unroll)) {

  Kind = DFGBase::Dedicated;

  if (GetUnrollMetadata(LI->getLoopID(), "llvm.loop.ss.datamove")) {
    LLVM_DEBUG(dbgs() << "A data-move 'DFG'\n");
  }

  LoopNest.push_back(LI);
  while (LoopNest.back()->getLoopDepth() > 1) {
    auto Cur = LoopNest.back();
    LLVM_DEBUG(dbgs() << "Loop level: "; Cur->dump());

    if (GetUnrollMetadata(Cur->getLoopID(), "llvm.loop.ss.stream"))
      break;

    LoopNest.push_back(Cur->getParentLoop());
  }

  assert(
      GetUnrollMetadata(LoopNest.back()->getLoopID(), "llvm.loop.ss.stream") &&
      "A stream level required!");

  Loop *InnerLoop = nullptr;
  std::set<BasicBlock *> Exclude;

  for (auto LI : LoopNest) {
    LLVM_DEBUG(dbgs() << "Loop: "; LI->dump());
    for (auto Child : LI->getSubLoops()) {
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

  LLVM_DEBUG(dbgs() << "DFG" << (void *)(this) << ": ";
             for (auto Block
                  : Blocks) { dbgs() << (void *)Block << ", "; });

  LLVM_DEBUG(dbgs() << "Init blocks done\n");

  auto OuterMost = LoopNest.back();
  if (!(Preheader = OuterMost->getLoopPreheader())) {
    Preheader = InsertPreheaderForLoop(OuterMost, Parent->Query->DT,
                                       Parent->Query->LI, nullptr, false);
  }

  auto Prologue = FindLoopPrologue(LoopNest.back());
  assert(Prologue);
  PrologueIP = &Prologue->back();
}

void DFGBase::dump(std::ostringstream &os) {}

void DFGFile::addDFG(DFGBase *DB) {
  assert(!AllInitialized &&
         "You can no longer modify the dfg after scheduling");
  DFGs.push_back(DB);
}

void DFGFile::EraseOffloadedInstructions() {

  std::set<Instruction *> Unique;

  for (auto &DFG : DFGs) {
    for (auto Entry : DFG->Entries) {

      // Skip instructions cannot be offloaded because of flags
      if (isa<IndMemPort>(Entry) && !dsa::utils::ModuleContext().IND) {
        continue;
      }
      if (isa<AtomicPortMem>(Entry) && !dsa::utils::ModuleContext().IND) {
        continue;
      }
      if ((isa<CtrlMemPort>(Entry) || isa<Predicate>(Entry)) &&
          !dsa::utils::ModuleContext().PRED) {
        continue;
      }

      auto F = [&Unique](Instruction *Inst) {
        bool SS = false;
        LLVM_DEBUG(Inst->dump());
        for (auto User : Inst->users()) {
          LLVM_DEBUG(dbgs() << "user: "; User->dump());
          if (auto Call = dyn_cast<CallInst>(User)) {
            if (auto IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
              SS |= IA->getAsmString().find("ss_") == 0;
            }
          }
        }
        for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
          auto Use = Inst->getOperand(i);
          LLVM_DEBUG(dbgs() << "use: "; Use->dump());
          if (auto Call = dyn_cast<CallInst>(Use)) {
            if (auto IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
              SS |= IA->getAsmString().find("ss_") == 0;
            }
          }
        }
        if (!SS) {
          Unique.insert(Inst);
          LLVM_DEBUG(dbgs() << "DELETE: "; Inst->dump());
        }
        LLVM_DEBUG(dbgs() << "\n");
      };

      if (auto P = dyn_cast<Predicate>(Entry)) {
        for (auto Elem : P->Cond)
          F(Elem);
      } else if (Entry->UnderlyingInst()) {
        F(Entry->UnderlyingInst());
      }
    }

    if (auto DD = dyn_cast<DedicatedDFG>(DFG)) {
      auto StreamMD = GetUnrollMetadata(DD->LoopNest.back()->getLoopID(),
                                        "llvm.loop.ss.stream");
      auto BarrierMD = dyn_cast<ConstantAsMetadata>(StreamMD->getOperand(1));
      if (BarrierMD->getValue()->getUniqueInteger().getSExtValue()) {
        // Find the "break" finger, and inject the wait at the "break" finger
        // block's end
        auto OutBB = FindLoopPrologue(DD->LoopNest.back());
        Instruction *I = &OutBB->back();
        for (; !isa<PHINode>(I); I = I->getPrevNode()) {
          bool Found = false;
          for (auto Elem : DD->InjectedCode) {
            if (I == Elem) {
              Found = true;
              break;
            }
          }
          if (isa<PHINode>(I) || Found) {
            auto IB = Query->IBPtr;
            IB->SetInsertPoint(I->getNextNode());
            dsa::inject::DSAIntrinsicEmitter(IB, Query->DSARegs).SS_WAIT_ALL();
            break;
          }
          if (I == &I->getParent()->front()) {
            auto IB = Query->IBPtr;
            IB->SetInsertPoint(I);
            dsa::inject::DSAIntrinsicEmitter(IB, Query->DSARegs).SS_WAIT_ALL();
            break;
          }
        }

      } else {
        LLVM_DEBUG(dbgs() << "No barrier required!\n");
      }
    } else if (auto TD = dyn_cast<TemporalDFG>(DFG)) {
      TD->End->eraseFromParent();
      TD->Begin->eraseFromParent();
    }
  }

  for (auto Inst : Unique) {
    Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
    Inst->eraseFromParent();
  }

  LLVM_DEBUG(dbgs() << "Rip out all original instrucitons\n");
}

Loop *DedicatedDFG::InnerMost() { return LoopNest.front(); }

Loop *DedicatedDFG::OuterMost() { return LoopNest.back(); }

DFGBase::DFGBase(DFGFile *Parent_) : Parent(Parent_) {
  ID = Parent_->DFGs.size();
  Kind = DFGBase::Unknown;
}

DFGBase::DFGKind DFGBase::getKind() const { return Kind; }

TemporalDFG::TemporalDFG(DFGFile *Parent, IntrinsicInst *Begin,
                         IntrinsicInst *End)
    : DFGBase(Parent), Begin(Begin), End(End) {

  std::set<Instruction *> users;
  for (Instruction *I = Begin; I != End; I = I->getNextNode()) {
    for (auto Usr : I->users()) {
      if (auto Inst = dyn_cast<Instruction>(Usr)) {
        if (Inst->getParent() == Begin->getParent()) {
          users.insert(Inst);
        }
      }
    }
  }

  for (auto &Inst : *Begin->getParent()) {
    if (users.count(&Inst)) {
      IP = &Inst;
    }
  }

  Kind = DFGBase::Temporal;
}

void TemporalDFG::dump(std::ostringstream &os) {
  if (!os.str().empty())
    os << "\n----\n\n";
  os << "#pragma group temporal\n";
  DFGBase::dump(os);
}

void DedicatedDFG::dump(std::ostringstream &os) {
  if (!os.str().empty())
    os << "\n----\n\n";
  if (dsa::utils::ModuleContext().TRIGGER) {
    CHECK(dsa::utils::ModuleContext().TEMPORAL)
        << "Trigger cannot be enabled without temporal";
    os << "#pragma group temporal\n";
  }
  DFGBase::dump(os);
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
  auto IB = Parent->Query->IBPtr;

  if (InsertBefore == nullptr)
    InsertBefore = DefaultIP();

  IB->SetInsertPoint(InsertBefore);

  assert(InsertBefore);

  LLVM_DEBUG(dbgs() << "Analyzing index "; Index->dump();
             dbgs() << "Bytes: " << Bytes << "\n");

  auto SE = Parent->Query->SE;
  AnalyzedStream Res;
  Value *One = createConstant(getCtx(), 1);
  Res.AR.Wrapped = One;

  size_t i = 0;
  for (; i < LoopNest.size(); ++i) {
    auto LI = LoopNest[i];
    LLVM_DEBUG(llvm::dbgs() << "Loop: "; LI->dump());
    if (!LI->isLoopInvariant(Index)) {
      LLVM_DEBUG(dbgs() << "Non-Invariant here!\n");
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

  auto EV = SE->getSCEV(Index);
  LLVM_DEBUG(EV->dump(); dbgs() << "Index (" << EV->getSCEVType() << "): ";
             EV->dump());

  if (i == LoopNest.size()) {
    LLVM_DEBUG(dbgs() << "Prime Repeat: "; Res.AR.Prime->dump();
               dbgs() << "Wrapped Repeat: "; Res.AR.Wrapped->dump();
               dbgs() << "\n");
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

    auto Cur = dyn_cast<SCEVAddRecExpr>(EV);
    LLVM_DEBUG(EV->dump());

    if (DoOuterRepeat && (!Cur || Cur->getLoop() != LoopNest[i])) {
      IB->SetInsertPoint(InsertBefore);
      Res.OuterRepeat = ProdTripCount(i + 1, LoopNest.size(), InsertBefore);
      LLVM_DEBUG(dbgs() << "Loop gap detected! Get outer repeat!\n");
      break;
    }

    Value *Step = nullptr;
    if (Cur) {
      assert(
          CheckLoopInvariant(Cur->getStepRecurrence(*SE), i + 2, LoopNest, SE));
      Step = Expander.expandCodeFor(Cur->getStepRecurrence(*SE), nullptr,
                                    InsertBefore);
      auto L = Cur->getLoop();
      LLVM_DEBUG(dbgs() << "Cur: "; Cur->getLoop()->dump(); dbgs() << "Nest:";
                 LoopNest[i]->dump(););
      if (L != LoopNest[i]) {
        // FIXME: Later check required, but I think it is correct for now.
        assert(L->contains(LoopNest[i]));
        Step = createConstant(getCtx(), 0);
      } else {
        EV = Cur->getStart();
      }
      LLVM_DEBUG(dbgs() << "======= Loop Induction =======\n");
    } else if (SE->isLoopInvariant(EV, LoopNest[i])) {
      Step = createConstant(getCtx(), 0);
      LLVM_DEBUG(dbgs() << "======= Loop Invariant =======\n");
    } else if (auto SAE = dyn_cast<SCEVAddExpr>(EV)) {
      SAE->dump();
      Index->dump();
      assert(false);
    }

    int StretchInt = 0;
    auto BackTaken = SE->getBackedgeTakenCount(LoopNest[i]);
    Value *DimTripCount = nullptr;

    if (CheckLoopInvariant(BackTaken, i + 1, LoopNest, SE)) {
      assert(CheckLoopInvariant(BackTaken, i + 2, LoopNest, SE));
      DimTripCount = TripCount(i, InsertBefore);
    } else {
      /// Support triangular streams
      if (!SE->isLoopInvariant(BackTaken, LoopNest[i + 1])) {
        assert(CheckLoopInvariant(BackTaken, i + 2, LoopNest, SE));
      }
      auto BackTaken_ = dyn_cast<SCEVAddRecExpr>(BackTaken);
      assert(BackTaken_);
      auto Cnt =
          Expander.expandCodeFor(BackTaken_->getStart(), nullptr, InsertBefore);
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
      auto StretchConst = dyn_cast<Constant>(NextStretch);
      assert(StretchConst);
      StretchInt = StretchConst->getUniqueInteger().getSExtValue();
      LLVM_DEBUG(dbgs() << "Stretch: "; NextStretch->dump());
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
        LLVM_DEBUG(dbgs() << "Coaleased!\nStretch: " << StretchInt << "\n");
        continue;
      }
    }

    Res.Dimensions.emplace_back(Step, DimTripCount, Stretch);

    LLVM_DEBUG(dbgs() << "Injected: "; InsertBefore->dump();
               dbgs() << "Current: "; Step->dump();
               dbgs() << "Stretch: " << Stretch; dbgs() << "\n");

    Stretch = StretchInt;
  }

  LLVM_DEBUG(dbgs() << "After exiting: "; EV->dump());

  Value *Start = nullptr;

  Start = Expander.expandCodeFor(EV, nullptr, &Preheader->back());
  if (auto SARE = dyn_cast<SCEVAddRecExpr>(EV)) {
    if (SARE->getLoop() != LoopNest.back() &&
        SARE->getLoop()->contains(LoopNest.back())) {
      Start =
          Expander.expandCodeFor(SARE->getStart(), nullptr, &Preheader->back());
      auto IndVar = SARE->getLoop()->getCanonicalInductionVariable();
      assert(IndVar);
      auto Stride = Expander.expandCodeFor(SARE->getStepRecurrence(*SE),
                                           nullptr, InsertBefore);
      IB->SetInsertPoint(InsertBefore);
      auto Delta = IB->CreateMul(IndVar, Stride);
      auto Casted = IB->CreatePtrToInt(Start, Delta->getType());
      Start = IB->CreateAdd(Casted, Delta, "", InsertBefore);
      LLVM_DEBUG(dbgs() << "Due to out of loop contribution: "; Start->dump());
    } else {
      // FIXME: Why did I leave this branch empty?
    }
  }

  Res.Dimensions.emplace_back(Start, Cnt, 0);

  LLVM_DEBUG(dbgs() << "\n");

  return Res;
}

Value *AnalyzedStream::BytesFromMemory(IRBuilder<> *IB) {
  Value *Res = createConstant(IB->getContext(), 1);
  for (size_t i = 0; i < Dimensions.size(); ++i)
    Res = IB->CreateMul(Res, std::get<1>(Dimensions[i]), "");
  return Res;
}

Value *DFGBase::UnrollConstant() {
  return Parent->Query->IBPtr->getInt64(getUnroll());
}

LLVMContext &DFGBase::getCtx() { return Parent->getCtx(); }

LLVMContext &DFGFile::getCtx() { return Query->IBPtr->getContext(); }

template <typename DFGType> void AddDFG(DFGFile *DF, MDNode *Ptr, Loop *LI) {
  assert(Ptr->getNumOperands() == 2);
  auto MDFactor = dyn_cast<ConstantAsMetadata>(Ptr->getOperand(1));
  assert(MDFactor);
  int Factor = (int)MDFactor->getValue()->getUniqueInteger().getSExtValue();
  DF->addDFG(new DFGType(DF, LI, Factor));
}

DFGFile::DFGFile(StringRef Name, IntrinsicInst *Start, IntrinsicInst *End,
                 StreamSpecialize *Query_)
    : FileName(Name), Func(*Start->getParent()->getParent()), Config(Start),
      Fence(End), Query(Query_) {}

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

SmallVector<BasicBlock *, 0> DedicatedDFG::getBlocks() {
  SmallVector<BasicBlock *, 0> Res(InnerMost()->getBlocks().begin(),
                                   InnerMost()->getBlocks().end());
  return Res;
}

SmallVector<BasicBlock *, 0> TemporalDFG::getBlocks() {
  SmallVector<BasicBlock *, 0> Res{Begin->getParent()};
  return Res;
}

AnalyzedStream TemporalDFG::AnalyzeDataStream(Value *Index, int Bytes) {
  AnalyzedStream res;
  auto &Ctx = Parent->getCtx();
  res.AR.Wrapped = createConstant(Ctx, 1);
  res.Dimensions.emplace_back(Index, createConstant(Ctx, Bytes), 0);
  return res;
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

void DFGFile::InspectSPADs() {

  AddrsOnSpad.clear();

  Function *start = nullptr, *end = nullptr;

  for (auto &Iter : *Func.getParent()) {
    if (Iter.getName().startswith("llvm.lifetime.start")) {
      start = &Iter;
    }
    if (Iter.getName().startswith("llvm.lifetime.end")) {
      end = &Iter;
    }
  }

  auto hasAlloc = [](Function &F) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (isa<AllocaInst>(&I)) {
          return true;
        }
      }
    }
    return false;
  };

  if (!hasAlloc(Func)) {
    return;
  }

  if (!start) {
    assert(!end);
    return;
  }

  auto IP = Config;
  auto IBPtr = Query->IBPtr;
  if (!isa<BranchInst>(IP))
    IP = IP->getNextNode();
  IBPtr->SetInsertPoint(IP);
  auto SpadPtr = IBPtr->CreateAlloca(IBPtr->getInt64Ty(), IBPtr->getInt64(1));
  auto SpadI8Ptr = IBPtr->CreateBitCast(SpadPtr, IBPtr->getInt8PtrTy());
  auto Self = IBPtr->CreateCall(start, {IBPtr->getInt64(8), SpadI8Ptr});
  auto GEP = IBPtr->CreateGEP(SpadPtr, IBPtr->getInt64(0));
  IBPtr->CreateStore(IBPtr->getInt64(0), GEP);

  std::vector<Instruction *> ToInject;
  auto DT = Query->DT;

  for (auto &BB : Func) {
    if (!DT->dominates(&BB.front(), Fence))
      continue;
    if (&BB != Config->getParent() && !DT->dominates(Config, &BB))
      continue;
    auto range = make_range(
        &BB != Config->getParent() ? BB.begin() : Config->getIterator(),
        &BB != Fence->getParent() ? BB.end() : Fence->getIterator());
    for (auto &Inst : range) {
      if (isa<ReturnInst>(Inst)) {
        ToInject.push_back(&Inst);
      }

      auto Intrin = dyn_cast<IntrinsicInst>(&Inst);
      if (!Intrin)
        continue;
      if (Intrin == Self)
        continue;

      if (Intrin->getIntrinsicID() == Intrinsic::lifetime_start ||
          Intrin->getIntrinsicID() == Intrinsic::lifetime_end) {
        ToInject.push_back(&Inst);
      }
    }
  }

  for (auto Inst : ToInject) {
    if (isa<ReturnInst>(Inst)) {
      IBPtr->SetInsertPoint(Inst);
      IBPtr->CreateCall(end, {IBPtr->getInt64(8), SpadI8Ptr});
    }
    if (auto Intrin = dyn_cast<IntrinsicInst>(Inst)) {

      auto f = [this, GEP, IBPtr](IntrinsicInst *Intrin) {
        assert(Intrin->getNumOperands() == 3);
        auto Size = Intrin->getOperand(0);
        // Calling an LLVM function will put this function as the last argument
        // of the CallSite.
        auto CI = dyn_cast<CastInst>(Intrin->getOperand(1));
        assert(CI);
        auto AI = dyn_cast<AllocaInst>(CI->getOperand(0));
        IBPtr->SetInsertPoint(Intrin);
        auto Ptr = IBPtr->CreateLoad(GEP);
        Value *Val = nullptr;
        switch (Intrin->getIntrinsicID()) {
        case Intrinsic::lifetime_start:
          AddrsOnSpad[AI] = Ptr;
          AddrsOnSpad[CI] = Ptr;
          Val = IBPtr->CreateAdd(Ptr, Size);
          break;
        case Intrinsic::lifetime_end:
          Val = IBPtr->CreateSub(Ptr, Size);
          break;
        default:
          assert(0);
        }
        IBPtr->CreateStore(Val, GEP);
      };

      f(Intrin);
    }
  }
}

void DFGBase::Accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }
void DedicatedDFG::Accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }
void TemporalDFG::Accept(dsa::DFGVisitor *Visitor) { Visitor->Visit(this); }
