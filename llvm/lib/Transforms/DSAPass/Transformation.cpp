#include <cstdio>
#include <fstream>
#include <queue>
#include <set>
#include <sstream>
#include <utility>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

#include "Transformation.h"
#include "Util.h"

#include "dsa/rf.h"
#include "dsa/spec.h"
//#include "dsa/mapper/scheduler.h"
//#include "dsa/mapper/scheduler_sa.h"

using namespace llvm;

#define DEBUG_TYPE "stream-specialize"

namespace dsa {
namespace inject {

std::stack<IRBuilder<>*> DSAIntrinsicEmitter::REG::IBStack;

MemoryType
InjectLinearStream(IRBuilder<> *IB, int PortNum, const AnalyzedStream &Stream,
                   MemoryOperation MO, Padding PP, MemoryType MT, int DType) {
  DSAIntrinsicEmitter DIE(IB);
  Value *Start = std::get<0>(Stream.Dimensions.back());
  Value *Bytes = std::get<1>(Stream.Dimensions.back());
  Value *DTyValue = IB->getInt64(DType);
  if (Stream.Dimensions.size() == 1) {
    DIE.INSTANTIATE_1D_STREAM(Start, DIE.DIV(Bytes, DTyValue),
                              PortNum, PP, DSA_Access, MO, MT, 1, DType, 0);
    return DMT_DMA;
  } else if (Stream.Dimensions.size() == 2) {
    Value *Stride = std::get<0>(Stream.Dimensions[0]);
    Value *N = std::get<1>(Stream.Dimensions[0]);
    int Stretch = std::get<2>(Stream.Dimensions[0]);
    DIE.INSTANTIATE_2D_STREAM(Start,
                              DIE.DIV(Stride, DTyValue),
                              DIE.DIV(Bytes, DTyValue),
                              DIE.DIV(Stretch, DTyValue),
                              N, PortNum, PP, DSA_Access, MO, MT, 1, DType, 0);
    return DMT_DMA;
  }
  llvm_unreachable("Unsupported stream dimension");
}

}
}



/// Check if a given SCEV is loop invariant
bool CheckLoopInvariant(const SCEV *S, int From, const SmallVector<Loop*, 0> &LoopNest,
                        ScalarEvolution *SE) {
  for (size_t i = From; i < LoopNest.size(); ++i) {
    auto LI = LoopNest[i];
    if (!SE->isLoopInvariant(S, LI)) {
      LLVM_DEBUG(
        S->dump();
        dbgs() << "Is NOT a loop invariant under ";
        LI->dump()
      );
      return false;
    }
  }
  return true;
}

Value *DfgBase::ComputeRepeat(Value *Prime, Value *Wrapper, bool isVectorized,
                              bool isPortConfig) {
  SCEVExpander Expander(*Parent->Query->SE, Parent->Func.getParent()->getDataLayout(), "");
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

Value *DfgBase::ComputeRepeat(const AnalyzedRepeat &AR, bool isVectorized, bool isPortConfig) {
  SCEVExpander Expander(*Parent->Query->SE, Parent->Func.getParent()->getDataLayout(), "");
  if (!AR.Prime)
    return createConstant(getCtx(), 1);
  return ComputeRepeat(Expander.expandCodeFor(AR.Prime, nullptr, DefaultIP()),
                       AR.Wrapped, isVectorized, isPortConfig);
}

/// Chech if a SCEV can be a repeat stretch
bool CanBeStretched(int x, const SmallVector<Loop*, 0> &LoopNest, ScalarEvolution *SE) {
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
        LLVM_DEBUG(
          S->dump();
          dbgs() << "[Can be stretch] Is NOT a loop invariant under ";
          LI->dump()
        );
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
  LLVM_DEBUG(dbgs() << "[Can be stretch] invariant for the right outside loop!\n");
  return false;
}

DfgEntry *DfgBase::InThisDFG(Value *Val) {
  for (auto &Elem : Entries) {
    for (auto &Iter : Elem->UnderlyingValues()) {
      if (Iter == Val) {
        return Elem;
      }
    }
  }
  return nullptr;
}

Instruction *DfgBase::DefaultIP() {
  assert(false && "Not supported yet!");
}

Instruction *TemporalDfg::DefaultIP() {
  return IP;
}

Instruction *DedicatedDfg::DefaultIP() {
  return &Preheader->back();
}

bool DedicatedDfg::ConsumedByAccumulator(MemPort *MP) {
  std::set<Value*> Visited{MP->UnderlyingInst()};
  std::queue<Value*> Q;
  Q.push(MP->UnderlyingInst());
  while (!Q.empty()) {
    auto Cur = Q.front(); Q.pop();
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
    case 64: return 0;
    case 32: return 1;
    case 16: return 2;
    case 8: return 3;
  }
  assert(false);
}

void DfgFile::InjectStreamIntrinsics() {
  auto IB = Query->IBPtr;

  for (auto &DFG : DFGs) {
    for (auto Port : DFG->EntryFilter<InputPort>()) {
      LLVM_DEBUG(dbgs() << "Inject for "; dbgs() << Port->dump());
      Port->InjectStreamIntrinsic(IB);
    }
  }

  for (auto &DFG : DFGs) {
    for (auto Port : DFG->EntryFilter<OutputPort>()) {
      LLVM_DEBUG(dbgs() << "Inject for "; dbgs() << Port->dump());
      Port->InjectStreamIntrinsic(IB);
    }
  }

  for (auto &DD : DFGs) {
    for (auto &PB : DD->EntryFilter<PortBase>()) {
      if (!PB->IntrinInjected) {
        PB->dump();
        assert(false && "All the ports should be fed");
      }
    }
  }

  IB->SetInsertPoint(Fence);
  dsa::inject::DSAIntrinsicEmitter(IB).SS_WAIT_ALL();

}

Instruction *DfgBase::InjectRepeat(const AnalyzedRepeat &AR, Value *Val, int Port) {
  SCEVExpander Expander(*Parent->Query->SE, Parent->Func.getParent()->getDataLayout(), "");

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
    auto BT =
      Expander.expandCodeFor(SE->getBackedgeTakenCount(SARE->getLoop()), nullptr, DefaultIP());
    auto SV = Expander.expandCodeFor(SARE->getStepRecurrence(*SE), nullptr, DefaultIP());
    assert(isa<ConstantInt>(SV));
    return InjectRepeat(IB->CreateAdd(BT, One), AR.Wrapped,
                        dyn_cast<ConstantInt>(SV)->getSExtValue(), Val, Port);
  } else if (AR.PT == AnalyzedRepeat::SumOfStretchedRepeat) {
    // FIXME: Kinda ugly here.
    // Once we have a better hardware support to do this we no longer need this
    assert(AR.Prime->getSCEVType() == scAddRecExpr);
    auto SARE = dyn_cast<SCEVAddRecExpr>(AR.Prime);
    auto First = Expander.expandCodeFor(SARE->getStart(), nullptr, DefaultIP());
    auto BT =
      Expander.expandCodeFor(SE->getBackedgeTakenCount(SARE->getLoop()), nullptr, DefaultIP());
    auto SV = Expander.expandCodeFor(SARE->getStepRecurrence(*SE), nullptr, DefaultIP());
    assert(isa<ConstantInt>(SV));
    auto SVInt = dyn_cast<ConstantInt>(SV)->getSExtValue();
    assert(SVInt == 1 || SVInt == -1);
    auto Last = IB->CreateAdd(First, IB->CreateMul(BT, SV));

    switch (getUnroll()) {
      case 1: {
        // (First + Last) * (BT + 1) / 2
        auto Prime = IB->CreateUDiv(IB->CreateMul(IB->CreateAdd(First, Last), IB->CreateAdd(BT, One)),
                                    createConstant(getCtx(), 2));
        return InjectRepeat(Prime, AR.Wrapped, /*I am not sure if put 0 here is correct*/0,
                            Val, Port);
      }
      case 2: {
        Value *Range;
        if (SVInt == -1) {
          //FIXME: Support last != 0 case later.
          auto F2 = IB->CreateAdd(First, IB->getInt64(2));
          auto FF = IB->CreateUDiv(IB->CreateMul(F2, F2), createConstant(getCtx(), 4));
          Range = FF;
        } else {
          assert(false && "Not supported yet...");
        }
        Range = IB->CreateShl(Range, 1);
        return InjectRepeat(Range, AR.Wrapped, /*Same as above*/0, Val, Port);
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

Instruction *DfgBase::InjectRepeat(Value *Prime, Value *Wrapper, int64_t Stretch,
                                   Value *Val, int Port) {

  auto IP = DefaultIP();
  auto &IB = *Parent->Query->IBPtr; IB.SetInsertPoint(IP);

  auto ShiftedStretch = createConstant(getCtx(), Stretch << 3);
  auto VectorizedStretch = IB.CreateSDiv(ShiftedStretch, UnrollConstant());
  auto ActualStretch = IB.CreateShl(VectorizedStretch, 1);
  (void) ActualStretch;

  dsa::inject::DSAIntrinsicEmitter DIE(Parent->Query->IBPtr);
  if (Val ==  nullptr) {
    DIE.SS_CONFIG_PORT(Port, DPF_PortRepeat, Prime);
    return DIE.res.back();
  } else {
    LLVM_DEBUG(dbgs() << "Inject Repeat: "; Val->dump();
               dbgs() << "For port: " << Port);
    assert(Port != -1);
    DIE.SS_CONST(Port, Val,
                 /*Times=*/ComputeRepeat(Prime, Wrapper, true, false),
                 /*Const Type*/Val->getType()->getScalarSizeInBits() / 8);
    return DIE.res.back();
  }
}

DfgBase *DfgBase::BelongOtherDFG(Instruction *I) {
  for (auto &DFG : Parent->DFGs) {
    if (DFG == this)
      continue;
    if (DFG->Contains(I))
      return DFG;
  }
  return nullptr;
}

std::pair<std::set<Instruction*>, std::set<Instruction*>>
BFSOperands(DfgBase *DFG, DominatorTree *DT, Instruction *From) {

  std::set<Instruction*> Visited, OutBound;
  std::queue<Instruction*> Q;

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

DfgEntry *DfgBase::DifferentiateMemoryStream(LoadInst *Load) {
  if (auto GEP = dyn_cast<GetElementPtrInst>(Load->getPointerOperand())) {

    auto BFSBack = BFSOperands(this, Parent->Query->DT, GEP);

    auto fLoad = [this, Load, BFSBack] (Value *Val) -> DfgEntry* {
      LoadInst *IdxLoad = nullptr;
      for (auto Elem : BFSBack.first) {
        if (auto ThisLoad = dyn_cast<LoadInst>(Elem)) {
          assert(!IdxLoad && "For now only one level indirect supported!");
          IdxLoad = ThisLoad;
        }
      }
      if (IdxLoad) {
        return new IndMemPort(this, IdxLoad, Load);
      }
      return nullptr;
    };

    auto fGather = [Load, GEP, this] (Value *Val) -> DfgEntry* {
      auto DT = this->Parent->Query->DT;
      auto DD = dyn_cast<DedicatedDfg>(this);

      auto Casted = dyn_cast<Instruction>(Val);
      if (!Casted)
        return nullptr;

      if (!DD)
        return nullptr;

      {
        bool simpleLoop = false;
        auto BI = dyn_cast<BranchInst>(&DD->InnerMost()->getLoopLatch()->back());
        auto Latch = DD->InnerMost()->getLoopLatch();
        assert(BI);
        for (auto BB : BI->successors()) {
          if (BB == Latch) {
            simpleLoop = true;
          }
        }
        if (simpleLoop) {
          return nullptr;
        }
      }

      std::set<Instruction*> Equiv;
      LLVM_DEBUG(dbgs() << "Equiv of: ");
      FindEquivPHIs(Casted, Equiv);

      Value *TripCount = nullptr;
      SmallVector<std::pair<ICmpInst*, bool>, 0> Conditions;
      for (auto Elem : Equiv) {
        if (auto PHI = dyn_cast<PHINode>(Elem)) {
          for (auto &Essense : PHI->incoming_values()) {
            auto Inst = dyn_cast<Instruction>(Essense);
            if (Inst && !isa<PHINode>(Inst)) {
              if (Inst->getOpcode() == BinaryOperator::Add) {
                auto DomBB = DT->getNode(Inst->getParent())->getIDom()->getBlock();
                LLVM_DEBUG(DomBB->back().dump(); Inst->dump());
                auto BI = dyn_cast<BranchInst>(&DomBB->back());
                assert(BI);
                if (BI->isConditional()) {
                  auto CondCmp = dyn_cast<ICmpInst>(BI->getCondition());
                  bool OK = true;
                  for (size_t i = 0; i < Conditions.size(); ++i) {
                    auto AlreadyCmp = Conditions[i].first;
                    if (CondCmp->getNumOperands() != AlreadyCmp->getNumOperands()) {
                      OK = false;
                      break;
                    }
                    OK = OK && ((AlreadyCmp->getOperand(0) == CondCmp->getOperand(0) &&
                                AlreadyCmp->getOperand(1) == CondCmp->getOperand(1)) ||
                                (AlreadyCmp->getOperand(0) == CondCmp->getOperand(1) &&
                                AlreadyCmp->getOperand(1) == CondCmp->getOperand(0)));
                  }
                  assert(OK && "Controlled by more than one predicate!");
                  Conditions.push_back(std::make_pair(CondCmp,
                                                      Inst->getParent() == BI->getSuccessor(0)));
                }
              }
            }
          }
        }
        if (DD && Elem->getParent() == DD->InnerMost()->getLoopLatch()) {
          LLVM_DEBUG(dbgs() << "Latch"; Elem->dump());
          for (auto Elem_ : Elem->users()) {
            auto Cmp = dyn_cast<ICmpInst>(Elem_);
            if (!Cmp)
              continue;
            if (Cmp->getParent() != Elem->getParent())
              continue;
            assert(Cmp->getPredicate() == ICmpInst::Predicate::ICMP_SLT &&
                   "For now only support SLT");
            for (size_t i = 0; i < Cmp->getNumOperands(); ++i) {
              if (Cmp->getOperand(i) != Elem) {
                TripCount = Cmp->getOperand(i);
                LLVM_DEBUG(dbgs() << "TripCount"; TripCount->dump());
              }
            }
          }
        }
      }
      if (TripCount && !Conditions.empty()) {

        int Mask = 0;
        SmallVector<bool, 0> Reverse;

        auto Pred =
          FindEquivPredicate(Conditions[0].first->getOperand(0), Conditions[0].first->getOperand(1));

        if (!Pred) {
          Pred = new Predicate(this, Conditions[0].first);
          Entries.push_back(Pred);
        }

        for (size_t i = 0; i < Conditions.size(); ++i) {
          Reverse.push_back(Pred->addCond(Conditions[i].first));
        }

        for (size_t i = 0; i < Conditions.size(); ++i) {
          auto Cond = Conditions[i];
          LLVM_DEBUG(dbgs() << "Moveforward: " << Cond.second << " "; Cond.first->dump());
          int SubMask = PredicateToInt(Cond.first->getPredicate(), Cond.second, Reverse[i]);
          Mask |= SubMask;
        }

        LLVM_DEBUG(dbgs() << "Forward mask: " << Mask << "\n");
        // FIXME: GEP for not is good enough, but we need a better way to figure out the start
        //        pointer later.
        return new CtrlMemPort(this, Load, GEP->getOperand(0), TripCount, Pred, Mask);
      }
      LLVM_DEBUG(dbgs() << "\n");
      return nullptr;
    };

    for (size_t i = 1; i < GEP->getNumOperands(); ++i) {
      if (auto Res = fLoad(GEP->getOperand(i)))
        return Res;
      if (auto Res = fGather(GEP->getOperand(i)))
        return Res;
      if (auto Cast = dyn_cast<CastInst>(GEP->getOperand(i))) {
        for (size_t j = 0; j < Cast->getNumOperands(); ++j) {
          if (auto Res = fGather(Cast->getOperand(j)))
            return Res;
        }
      }
    }
  }
  return new MemPort(this, Load);
}

Predicate* DfgBase::FindEquivPredicate(Value *LHS, Value *RHS) {
  for (auto Elem : EntryFilter<Predicate>()) {
    if (Elem->Cond[0]->getOperand(0) == LHS && Elem->Cond[0]->getOperand(1) == RHS)
      return Elem;
    if (Elem->Cond[0]->getOperand(1) == LHS && Elem->Cond[0]->getOperand(0) == RHS)
      return Elem;
  }
  return nullptr;
}

void DfgBase::AnalyzeEntryOp(Instruction *Inst) {

  LLVM_DEBUG(dbgs() << "Analyze Entry: "; Inst->dump());

  bool isAcc = false;

  auto ToOffload = !isa<BranchInst>(Inst) ? Inst :
    dyn_cast<Instruction>(dyn_cast<BranchInst>(Inst)->getCondition());

  for (size_t i = 0; i < ToOffload->getNumOperands(); ++i) {
    auto Operand = ToOffload->getOperand(i);
    LLVM_DEBUG(dbgs() << "Operand: "; Operand->dump());
    if (InThisDFG(Operand)) {
      LLVM_DEBUG(dbgs() << "Already-in skip!\n");
      continue;
    }
    if (auto Phi = dyn_cast<PHINode>(Operand)) {

      std::queue<PHINode*> Q;
      std::set<PHINode*> Visited;

      for (Q.push(Phi), Visited.insert(Phi); !Q.empty(); ) {
        auto Poll = Q.front(); Q.pop();
        for (auto &InComing : Poll->incoming_values()) {
          if (InComing == Inst) {
            isAcc = true;
            break;
          }
          if (auto AnotherPhi = dyn_cast<PHINode>(InComing)) {
            if (!Visited.count(AnotherPhi)) {
              Q.push(AnotherPhi);
              Visited.insert(AnotherPhi);
            }
          }
        }
      }

      // FIXME: I am not sure if this will suffice. I relax the constraint
      // of detecting a accumulation by checking the BFS successors.
      if (!isAcc) {
        llvm::errs() << "PhiNode: "; Phi->dump();
        assert(false && "Accumulator check goes wrong.");
      }

    } else if (auto Load = dyn_cast<LoadInst>(Operand)) {
      Entries.push_back(DifferentiateMemoryStream(Load));
    } else if (auto Consumee = dyn_cast<Instruction>(Operand)) {
      LLVM_DEBUG(dbgs() << "Not in this Nest: " << Contains(Consumee) << "\n");
      if (!Contains(Consumee)) {
        if (BelongOtherDFG(Consumee)) {
          Entries.push_back(new StreamInPort(this, Consumee));
          LLVM_DEBUG(dbgs() << "Upstream:"; Consumee->dump());
        } else {
          Entries.push_back(new InputConst(this, Consumee));
          LLVM_DEBUG(dbgs() << "Outer loop invariant:"; Consumee->dump());
        }
      }
    } else if (!isa<Constant>(Operand)) {
      Entries.push_back(new InputConst(this, Operand));
      LLVM_DEBUG(dbgs() << "Other non const:"; Operand->dump());
    }
  }

  DfgEntry *Entry = nullptr;
  if (!isAcc) {
    if (auto BI = dyn_cast<BranchInst>(Inst)) {
      assert(BI->isConditional());
      if (ICmpInst* Cmp = dyn_cast<ICmpInst>(BI->getCondition())) {
        Predicate *PredEntry = FindEquivPredicate(Cmp->getOperand(0), Cmp->getOperand(1));
        if (!PredEntry) {
          PredEntry = new Predicate(this, Cmp);
          Entries.push_back(PredEntry);
        } else {
          PredEntry->addCond(Cmp);
        }
      } else if (Instruction *Cond = dyn_cast<Instruction>(BI->getCondition())) {
        Entries.push_back(new Predicate(this, Cond));
      }
      Entry = Entries.back();
    } else {
      auto CB = new ComputeBody(this, Inst);
      Entries.push_back(CB);
      Entry = CB;
      LLVM_DEBUG(dbgs() << "Plain Inst: "; Inst->dump());
    }
  } else {
    assert(Inst->getOpcode() == BinaryOperator::Add ||
           Inst->getOpcode() == BinaryOperator::FAdd);
    auto CS = new CtrlSignal(this);
    Entries.push_back(CS);
    auto Acc = new Accumulator(this, Inst, CS);
    Entries.push_back(Acc);
    CS->Controlled = Acc;
    Entry = Acc;
    LLVM_DEBUG(dbgs() << "Accumulator: "; Inst->dump());
  }

  assert(Entry);

}

bool DedicatedDfg::Contains(const Loop *L) {
  for (auto Elem : LoopNest) {
    if (Elem == L)
      return true;
  }
  return false;
}

void DfgBase::InspectConsumers(Instruction *Inst) {
  auto DD = dyn_cast<DedicatedDfg>(this);

  for (auto User : Inst->users()) {
    if (auto Store = dyn_cast<StoreInst>(User)) {
      LoadInst *Load = nullptr;

      if (auto GEP = dyn_cast<GetElementPtrInst>(Store->getPointerOperand())) {
        for (size_t i = 0; i < GEP->getNumOperands(); ++i) {
          if ((bool) (Load = dyn_cast<LoadInst>(GEP->getOperand(i)))) {
            break;
          }
        }
      }

      if (Load && DD && Contains(Load)) {

        if (auto BO = dyn_cast<BinaryOperator>(Store->getValueOperand())) {
          bool isUpdate = false;
          Value *AtomicOperand = nullptr;
          if (BO->getOpcode() == Instruction::BinaryOps::Add) {
            for (size_t i = 0; i < BO->getNumOperands(); ++i) {
              auto Operand = dyn_cast<LoadInst>(BO->getOperand(i));
              if (Operand && Operand->getPointerOperand() == Store->getPointerOperand()) {
                isUpdate = true;
              } else {
                AtomicOperand = BO->getOperand(i);
              }
            }
          }
          Entries.push_back(new AtomicPortMem(this, Load, Store, isUpdate ? 0 : 3,
                                              Inst, AtomicOperand));
        } else {
          Entries.push_back(new AtomicPortMem(this, Load, Store, 3, Inst, nullptr));
        }
        LLVM_DEBUG(dbgs() << "AtomicMem: "; Inst->dump());

      } else {
        auto Out = new PortMem(this, Store);
        Entries.push_back(Out);
        LLVM_DEBUG(dbgs() << "PortMem: "; Inst->dump());
      }
    // Support downstream data consumption
    } else if (CanBeAEntry(User)) {
      auto Consume = dyn_cast<Instruction>(User);
      LLVM_DEBUG(dbgs() << "Comsumed by: "; Consume->dump());
      if (BelongOtherDFG(Consume)) {
        auto Out = new StreamOutPort(this, Inst);
        Entries.push_back(Out);
        LLVM_DEBUG(dbgs() << "DownStream: "; Inst->dump(); Consume->dump());
      }
    }
  }
}



Value *DedicatedDfg::TripCount(int x, Instruction *InsertBefore) {
  SCEVExpander Expander(*Parent->Query->SE, Parent->Func.getParent()->getDataLayout(), "");
  auto IB = Parent->Query->IBPtr;
  auto BackSE = Parent->Query->SE->getBackedgeTakenCount(LoopNest[x]);
  assert(CheckLoopInvariant(BackSE, x + 1, LoopNest, Parent->Query->SE));
  auto BackTaken = Expander.expandCodeFor(BackSE, nullptr, InsertBefore);
  IB->SetInsertPoint(InsertBefore);
  auto Trip = IB->CreateAdd(BackTaken, createConstant(getCtx(), 1), "trip.count");
  return Trip;
}

Value *DedicatedDfg::ProdTripCount(int l, int r, Instruction *InsertBefore) {
  Value *Prod = createConstant(getCtx(), 1);
  for (int i = l; i < r; ++i) {
    Prod = BinaryOperator::Create(BinaryOperator::Mul, Prod, TripCount(i, InsertBefore),
                                  "trip.prod", InsertBefore);
  }
  return Prod;
}

Value *DedicatedDfg::ProdTripCount(int x, Instruction *InsertBefore) {
  return ProdTripCount(0, x, InsertBefore);
}

DedicatedDfg::DedicatedDfg(DfgFile *Parent_, Loop *LI, int Unroll)
  : DfgBase(Parent_), UnrollFactor(std::max(1, Unroll)) {

  Kind = DfgBase::Dedicated;

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

  assert(GetUnrollMetadata(LoopNest.back()->getLoopID(), "llvm.loop.ss.stream") &&
         "A stream level required!");

  Loop *InnerLoop = nullptr;
  std::set<BasicBlock*> Exclude;

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


  LLVM_DEBUG(
    dbgs() << "DFG" << (void*)(this) << ": ";
    for (auto Block : Blocks) {
      dbgs() << (void*) Block << ", ";
    }
  );


  LLVM_DEBUG(dbgs() << "Init blocks done\n");

  auto OuterMost = LoopNest.back();
  if (!(Preheader = OuterMost->getLoopPreheader())) {
    Preheader = InsertPreheaderForLoop(OuterMost, Parent->Query->DT, Parent->Query->LI, nullptr, false);
  }

  auto Prologue = FindLoopPrologue(LoopNest.back());
  assert(Prologue);
  PrologueIP = &Prologue->back();
}

void DfgBase::InstsToEntries(iterator_range<BasicBlock::iterator> IRange,
                             std::set<Instruction*> &Visited) {

  std::queue<Instruction*> Q;
  for (auto &Inst : IRange) {

    if (auto Load = dyn_cast<LoadInst>(&Inst)) {
      Q.push(Load);
      Visited.insert(Load);
    }

    // FIXME: Can I delete the Temporal DFG clause?
    if (isa<TemporalDfg>(this) && CanBeAEntry(&Inst)){
      for (size_t i = 0; i < Inst.getNumOperands(); ++i) {
        if (auto InstOperand = dyn_cast<Instruction>(Inst.getOperand(i))) {
          if (!Contains(InstOperand)) {
            // A exteneral stream-in value
            Q.push(&Inst);
            Visited.insert(&Inst);
          }
        }
      }
    }
    
    while (!Q.empty()) {
      auto Cur = Q.front();
      Q.pop();
      LLVM_DEBUG(dbgs() << "Analyze Users of: "; Cur->dump());
      for (auto Elem : Cur->users()) {
        auto Inst = dyn_cast<Instruction>(Elem);
        if (!Inst) {
          LLVM_DEBUG(dbgs() << "Not a inst: "; Elem->dump());
          continue;
        }
        if (!Contains(Inst)) {
          LLVM_DEBUG(dbgs() << "Not in blocks: "; Elem->dump());
          continue;
        }
        if (!CanBeAEntry(Inst)) {
          LLVM_DEBUG(dbgs() << "Not a entry: "; Elem->dump());
          continue;
        }
        if (Visited.find(Inst) == Visited.end()) {
          Q.push(Inst);
          Visited.insert(Inst);
        }
      }
    }
  }

}

void DedicatedDfg::InitEntries() {

  std::set<Instruction*> Visited;
  auto DT = Parent->Query->DT;

  // FIXME: I believe for now assume the BBs in a topological order is safe?
  for (auto BB : getBlocks()) {

    // I am not sure if this is a safe assumption: All the blocks have its own immediate dom.
    auto DomBB = DT->getNode(BB)->getIDom()->getBlock();

    // Is the assumption too strong here?
    // A intruction with a idom conditional instruction which does not belong to this DFG indicates
    // the predicate is always true.
    if (InnerMost()->getBlocksSet().count(DomBB)) {
      auto BI = dyn_cast<BranchInst>(&DomBB->back());
      if (BI->isConditional())
        Visited.insert(dyn_cast<Instruction>(BI));
    }

    InstsToEntries(iterator_range<BasicBlock::iterator>(BB->begin(), BB->end()), Visited);
  }

  for (auto Inst : Visited) {
    if (!isa<LoadInst>(Inst)) {
      AnalyzeEntryOp(Inst);
      std::set<Instruction*> Equiv;
      FindEquivPHIs(Inst, Equiv);
      for (auto EquivInst : Equiv) {
        InspectConsumers(EquivInst);
      }
    }
  }

  /// To handle data move DFGs.
  for (auto Inst : Visited) {
    auto Load = dyn_cast<LoadInst>(Inst);

    if (!Load)
      continue;

    if (!InThisDFG(Load)) {
      auto MP = dyn_cast<PortBase>(DifferentiateMemoryStream(Load));
      assert(MP);
      Entries.push_back(MP);
      size_t j = Entries.size();
      InspectConsumers(Load);
      // FIXME: For now we only support one consumer.
      assert(j + 1 == Entries.size() && "A load without usage?");
      for (; j < Entries.size(); ++j) {
        auto Entry = Entries[j];
        if (auto PM = dyn_cast<PortMem>(Entry)) {
          PM->SoftPortNum = MP->SoftPortNum = getNextReserved();
        } else if (auto APM = dyn_cast<AtomicPortMem>(Entry)) {
          assert(APM->Store->getValueOperand() == MP->UnderlyingInst());
          APM->Op = MP->UnderlyingInst();
          // FIXME: This is not correct...
          // MP->SoftPortNum = getNextReserved();
        } else {
          assert(false && "This should not happen");
        }
      }
    }

  }

  CleanupEntryDependences();
  ReorderEntries();
}

void DataMoveDfg::InitEntries() {
  assert(getBlocks().size() == 1);
  for (auto &I0 : *getBlocks()[0]) {
    auto Load = dyn_cast<LoadInst>(&I0);
    if (Load) {
      LLVM_DEBUG(Load->dump());
      for (auto I1 = I0.getNextNode(); I1 != &I0.getParent()->back(); I1 = I1->getNextNode()) {
        LLVM_DEBUG(I1->dump());
        auto Store = dyn_cast<StoreInst>(I1);
        if (!Store)
          continue;
        if (Store->getValueOperand() == Load) {
          auto MP = new MemPort(this, Load);
          Entries.push_back(MP);
          auto PM = new PortMem(this, Store);
          Entries.push_back(PM);
          MP->SoftPortNum = MemScrPort;
          PM->SoftPortNum = MemScrPort;
          LLVM_DEBUG(
            MP->UnderlyingInst()->dump();
            PM->UnderlyingInst()->dump());
        }
      }
    }
    //TODO: Test this!
    auto Store = dyn_cast<StoreInst>(&I0);
    if (!Store)
      continue;
    if (isa<ConstantData>(Store->getValueOperand())) {
      auto PM = new PortMem(this, Store);
      PM->SoftPortNum = MemScrPort;
      Entries.push_back(PM);
      LLVM_DEBUG(PM->UnderlyingInst()->dump());
    }
  }

  FinalizeEntryID();
}

void TemporalDfg::InitEntries() {
  std::set<Instruction*> Visited;
  assert(getBlocks().size() == 1);

  InstsToEntries(make_range(Begin, End), Visited);

  for (auto Inst : Visited) {
    if (!isa<LoadInst>(Inst)) {
      AnalyzeEntryOp(Inst);
      std::set<Instruction*> Equiv;
      FindEquivPHIs(Inst, Equiv);
      for (auto EquivInst : Equiv)
        InspectConsumers(EquivInst);
    }
  }

  CleanupEntryDependences();
  ReorderEntries();
}

void DfgBase::CleanupEntryDependences() {

  {
    std::set<DfgEntry*> ToRemove;
    for (auto Entry : EntryFilter<IndMemPort>()) {
      for (auto Elem : BFSOperands(this, Parent->Query->DT, Entry->UnderlyingInst()).first) {
        if (Elem == Entry->UnderlyingInst())
          continue;
        if (auto Entry = InThisDFG(Elem)) {
          if (!isa<ComputeBody>(Entry))
            continue;
          ToRemove.insert(Entry);
        }
      }
    }
    std::vector<int> Ids;
    for (auto Elem : ToRemove) {
      for (size_t i = 0; i < Entries.size(); ++i) {
        if (Elem == Entries[i])
          Ids.push_back(i);
      }
    }
    std::sort(Ids.begin(), Ids.end());
    for (size_t i = 0; i < Ids.size(); ++i) {
      Entries.erase(Entries.begin() + Ids[i] - i);
    }
  }

  /// Figure out entry write to registers
  {
    std::vector<DfgEntry*> ToAdd;
    for (auto Entry : Entries) {
      if (isa<ComputeBody>(Entry)) {
        auto Val = Entry->UnderlyingValue();
        std::set<Value*> ToInspect;
        if (auto Inst = dyn_cast<Instruction>(Val)) {
          std::set<Instruction*> Equivs;
          FindEquivPHIs(Inst, Equivs);
          for (auto Iter : Equivs)
            ToInspect.insert(Iter);
        } else {
          ToInspect.insert(Val);
        }
        bool Written = false;
        for (auto Iter : ToInspect) {
          for (auto User : Iter->users()) {
            if (auto UserInst = dyn_cast<Instruction>(User)) {
              if (isa<PHINode>(UserInst))
                continue;
              if (!BelongOtherDFG(UserInst) && !InThisDFG(UserInst)) {
                ToAdd.push_back(new OutputPort(this, Val));
                LLVM_DEBUG(dbgs() << "Write to register: ";
                           Iter->dump(); Val->dump(); UserInst->dump());
                Written = true;
                break;
              }
            }
          }
          if (Written)
            break;
        }
      }
    }
    Entries.insert(Entries.end(), ToAdd.begin(), ToAdd.end());
  }

}

void DfgBase::ReorderEntries() {
  LLVM_DEBUG(
    dbgs() << "Before reordering: " << Entries.size() << "\n";
    for (auto &Entry : Entries)
      dbgs() << Entry->dump() << "\n";
    dbgs() << "\n";
  );

  // Reorder instructions in a topological order
  // Hoist all the input entries to the very first ones
  for (size_t i = 0; i < Entries.size(); ++i)
    if (!isa<InputPort>(Entries[i]))
      for (size_t j = i + 1; j < Entries.size(); ++j)
        if (isa<InputPort>(Entries[j]))
          std::swap(Entries[i], Entries[j]);

  // Postpone all the output entries to the very last ones
  for (int i = Entries.size() - 1; i >= 0; --i)
    if (!isa<OutputPort>(Entries[i]))
      for (int j = i - 1; j >= 0; --j)
        if (isa<OutputPort>(Entries[j]))
          std::swap(Entries[i], Entries[j]);

  std::set<Value*> Ready;
  for (size_t i = 0; i < Entries.size(); ++i) {

    if (isa<CtrlSignal>(Entries[i]))
      continue;

    if (isa<InputPort>(Entries[i])) {
      Ready.insert(Entries[i]->UnderlyingValue());
      LLVM_DEBUG(dbgs() << "Already OK: "; Entries[i]->UnderlyingValue()->dump());
      continue;
    }


    // TODO: Refactor this by replacing the `operand ready' by dominators
    if (!isa<OutputPort>(Entries[i])) {
      if (Entries[i]->OperandReady(Ready)) {
        LLVM_DEBUG(dbgs() << "Already OK: "; Entries[i]->UnderlyingValue()->dump());
        Ready.insert(Entries[i]->UnderlyingValue());
      } else {
        LLVM_DEBUG(dbgs() << "Looking for replacement of: ";
                   Entries[i]->UnderlyingInst()->dump());
        bool Found = false;
        for (size_t j = i + 1; j < Entries.size() && !Found && !isa<OutputPort>(Entries[j]); ++j) {
          if (Entries[j]->OperandReady(Ready)) {
            Ready.insert(Entries[j]->UnderlyingValue());
            std::swap(Entries[i], Entries[j]);
            Found = true;
          }
        }
        if (!Found) {
          FinalizeEntryID();
          errs() << Entries[i]->dump() << "\n";
          std::ostringstream oss;
          dump(oss);
          errs() << oss.str() << "\n";
          assert(false && "NOT acyclic DFG?");
        }
      }
      if (auto Pred = dyn_cast<Predicate>(Entries[i])) {
        for (auto Cond : Pred->Cond)
          Ready.insert(Cond);
      }
    } else {
      break;
    }
  }

  LLVM_DEBUG(
    dbgs() << "After reordering: " << Entries.size() << "\n";
    for (auto &Entry : Entries)
      dbgs() << Entry->dump() << "\n";
    dbgs() << "\n";
  );

  FinalizeEntryID();

}

void DfgBase::dump(std::ostringstream &os) {


  if (!Entries.empty()) {
    auto BF = Parent->Query->BFI->getBlockFreq(getBlocks()[0]);
    os << "#pragma group frequency " << BF.getFrequency() << "\n";
  }

  if (getUnroll() != 1) {
    os << "#pragma group unroll " << getUnroll() << "\n";
  }

  for (auto Elem : EntryFilter<InputPort>())
    Elem->EmitInPort(os);

  for (auto Elem : Entries) {
    if (auto CB = dyn_cast<ComputeBody>(Elem))
      CB->EmitCB(os);
    if (auto P = dyn_cast<Predicate>(Elem))
      P->EmitCond(os);
  }

  /// Emit intermediate result for atomic operation
  for (auto Elem : EntryFilter<ComputeBody>())
    Elem->EmitAtomic(os);

  for (auto Elem : EntryFilter<OutputPort>())
    Elem->EmitOutPort(os);

}

void DfgFile::addDfg(DfgBase *DB) {
  assert(!AllInitialized && "You can no longer modify the dfg after scheduling");
  DFGs.push_back(DB);
}

void DfgFile::InitAllDfgs() {
  assert(!AllInitialized && "You can no longer modify the dfg after scheduling");
  for (auto &Elem : DFGs) {
    LLVM_DEBUG(dbgs() << "Working on DFG[" << Elem->ID << "]\n");
    Elem->InitEntries();
  }
  AllInitialized = true;
}

void DfgFile::EmitAndScheduleDfg() {
  assert(AllInitialized && "Only after all initialized this DFG file is ready to schedule!");

  std::ostringstream oss;
  for (size_t i = 0; i < DFGs.size(); ++i) {
    LLVM_DEBUG(dbgs() << "Dump DFG[" << i << "]\n");
    DFGs[i]->dump(oss);
  }

  if (!oss.str().empty()) {
    std::ofstream Fout(FileName);
    Fout << oss.str();
    Fout.close();
  } else {
    return;
  }

  auto SCHEDULED = getenv("SCHEDULED");
  std::string NameOnly;

  if (SCHEDULED) {
    std::string SCHEDString(SCHEDULED);
    int From = SCHEDString.size(), Len = 0;
    while (SCHEDString[From - 1] != '/') {
      --From;
      ++Len;
    }
    NameOnly = SCHEDString.substr(From, Len);
  } else {
    auto SBCONFIG = getenv("SBCONFIG");
    assert(SBCONFIG && "Please specify CGRA config environment variable $SBCONFIG");
    LLVM_DEBUG(
      dbgs() << "Emitted DFG:\n";
      system(formatv("cat {0} 1>&2", FileName).str().c_str());
      dbgs() << "\n\n";
    );

    //SS_CONFIG::SSModel model(SBCONFIG);
    //SSDfg dfg(FileName);
    //SchedulerSimulatedAnnealing *sa = new SchedulerSimulatedAnnealing(&model);
    //sa->verbose = DebugFlag && isCurrentDebugType(DEBUG_TYPE);
    //sa->str_subalg = "";
    //sa->set_max_iters(Query->MF.EXTRACT ? 1 : 20000);
    //sa->setTimeout(20);
    //sa->setGap(0.1, 1.0);
    //Schedule *sched = sa->invoke(&model, &dfg, false);
    std::string Verbose = isCurrentDebugType(DEBUG_TYPE) ? "-v" : "";
    if (Query->MF.EXTRACT) {
      Verbose += " --max-iters 1";
    }
    auto Cmd = formatv("ss_sched {0} {1} {2} > /dev/null", Verbose, SBCONFIG, FileName);
    LLVM_DEBUG(dbgs() << Cmd);
    if (system(Cmd.str().c_str()) != 0) {
      // TODO(@were): throw exception here.
    }
  }


  std::ifstream ifs(SCHEDULED ? std::string(SCHEDULED) : formatv("{0}.h", FileName).str());

  if (!ifs.is_open()) {
    assert(Query->MF.EXTRACT);
    return;
  }

  std::string Stripped(SCHEDULED ? NameOnly.substr(0, NameOnly.size() - 2) : FileName);
  while (Stripped.back() != '.') Stripped.pop_back();
  Stripped.pop_back();
  LLVM_DEBUG(dbgs() << "Stripped: " << Stripped << "\n");

  int ConfigSize = 0;
  std::string ConfigString;

  std::string Line;
  std::string PortPrefix(formatv("P_{0}_sub", Stripped).str());
  while (std::getline(ifs, Line)) {
    std::istringstream iss(Line);
    std::string Token;
    iss >> Token;
    // #define xxx
    if (Token == "#define") {
      iss >> Token;
      // #define P_dfgX_subY_vZ
      if (Token.find(PortPrefix) == 0) {
        int X, Y;
        Token = Token.substr(PortPrefix.size(), Token.size());
        if (sscanf(Token.c_str(), "%d_v%d", &X, &Y) != 2) {
          // TODO(@were): throw exception here!
        }
        int Port;
        iss >> Port;
        LLVM_DEBUG(dbgs() << "sub" << X << "v" << Y << " -> " << Port << "\n");
        auto Entry = DFGs[X]->Entries[Y];
        if (auto PB = dyn_cast<PortBase>(Entry)) {
          PB->SoftPortNum = Port;
        } else if (auto CB = dyn_cast<ComputeBody>(Entry)) {
          if (!CB->isImmediateAtomic()) {
            LLVM_DEBUG(llvm::dbgs() << "OutputPorts:\n");
            auto OutPorts = CB->GetOutPorts();
            for (auto &Port : CB->GetOutPorts()) {
              LLVM_DEBUG(Port->UnderlyingInst()->dump());
            }
            // FIXME: For now only one destination is supported
            // Later divergence will be supported
            CHECK(OutPorts.size() == 1) << OutPorts.size();
            OutPorts[0]->SoftPortNum = Port;

            // Fill in the latency of each node.
            //{
            //  OutputPort *OP = OutPorts[0];
            //  std::string ON = OP->Parent->InThisDFG(OP->Output)->NameInDfg();
            //  for (auto SDVO : dfg.nodes<SSDfgVecOutput*>()) {
            //    if (SDVO->name() == ON) {
            //      OP->Latency = sched->latOf(SDVO);
            //      LLVM_DEBUG(dbgs() << "[lat] " << ON << ": " << OP->Latency << "\n");
            //      break;
            //    }
            //  }
            //}

          } else {
            CB->SoftPortNum = Port;
          }
        } else {
          assert(false && "What's going on?");
        }
      // #define dfgx_size size
      } else if (Token.find(formatv("{0}_size", Stripped).str()) == 0) {
        iss >> ConfigSize;
      }
    // char dfgx_config[size] = "filename:dfgx.sched";
    } else if (Token == "char") {
      // dfgx_config[size]
      iss >> Token;
      // =
      iss >> Token;
      // "filename:dfgx.sched";
      iss >> Token;
      ConfigString = Token.substr(1, Token.size() - 3);
      ConfigString += std::string(ConfigSize - ConfigString.size() - 1, '\0');
    }
  }

  LLVM_DEBUG(dbgs() << "[Config] " << ConfigSize << ": " << ConfigString << "\n");

  auto Module = Func.getParent();
  auto ConfigData = ConstantDataArray::getString(getCtx(), ConfigString);
  auto GV = new GlobalVariable(*Module, ConfigData->getType(), false, GlobalValue::ExternalLinkage,
                               ConfigData, formatv("{0}_config", Stripped));

  GV->setAlignment(llvm::MaybeAlign(1));
  GV->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);

  LLVM_DEBUG(dbgs() << "Inject global configuration value "; GV->dump());

  auto APConfigSize = APInt(64, ConfigSize);
  auto ConstConfig = Constant::getIntegerValue(Type::getInt64Ty(getCtx()), APConfigSize);

  auto IB = Query->IBPtr;
  IB->SetInsertPoint(Config);
  dsa::inject::DSAIntrinsicEmitter DIE(IB);
  DIE.SS_CONFIG(GV, ConstConfig);
  LLVM_DEBUG(dbgs() << "Inject config asm "; DIE.res.back()->dump());
}

void DfgFile::EraseOffloadedInstructions() {

  std::set<Instruction*> Unique;

  for (auto &DFG : DFGs) {
    for (auto Entry: DFG->Entries) {

      // Skip instructions cannot be offloaded because of flags
      if (isa<IndMemPort>(Entry) && !Query->MF.IND) {
        continue;
      }
      if (isa<AtomicPortMem>(Entry) && !Query->MF.IND) {
        continue;
      }
      if ((isa<CtrlMemPort>(Entry) || isa<Predicate>(Entry)) && !Query->MF.PRED) {
        continue;
      }

      auto F = [&Unique] (Instruction *Inst) {
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

    if (auto DD = dyn_cast<DedicatedDfg>(DFG)) {
      auto StreamMD = GetUnrollMetadata(DD->LoopNest.back()->getLoopID(), "llvm.loop.ss.stream");
      auto BarrierMD = dyn_cast<ConstantAsMetadata>(StreamMD->getOperand(1));
      if (BarrierMD->getValue()->getUniqueInteger().getSExtValue()) {
        // Find the "break" finger, and inject the wait at the "break" finger block's end
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
            dsa::inject::DSAIntrinsicEmitter(IB).SS_WAIT_ALL();
            break;
          }
          if (I == &I->getParent()->front()) {
            auto IB = Query->IBPtr;
            IB->SetInsertPoint(I);
            dsa::inject::DSAIntrinsicEmitter(IB).SS_WAIT_ALL();
            break;
          }
        }

      } else {
        LLVM_DEBUG(dbgs() << "No barrier required!\n");
      }
    } else if (auto TD = dyn_cast<TemporalDfg>(DFG)) {
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

Loop *DedicatedDfg::InnerMost() {
  return LoopNest.front();
}

Loop *DedicatedDfg::OuterMost() {
  return LoopNest.back();
}

DfgBase::DfgBase(DfgFile *Parent_) :
  Parent(Parent_) {
  ID = Parent_->DFGs.size();
  Kind = DfgBase::Unknown;
}

DfgBase::DfgKind DfgBase::getKind() const {
  return Kind;
}

TemporalDfg::TemporalDfg(DfgFile *Parent, IntrinsicInst *Begin, IntrinsicInst *End)
  : DfgBase(Parent), Begin(Begin), End(End) {

  std::set<Instruction*> users;
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

  Kind = DfgBase::Temporal;
}

void TemporalDfg::dump(std::ostringstream &os) {
  if (!os.str().empty())
    os << "\n----\n\n";
  os << "#pragma group temporal\n";
  DfgBase::dump(os);
}

void DedicatedDfg::dump(std::ostringstream &os) {
  if (!os.str().empty())
    os << "\n----\n\n";
  if (Parent->Query->MF.TRIGGER) {
    assert(Parent->Query->MF.TEMPORAL && "Environment should not contradict!");
    os << "#pragma group temporal\n";
  }
  DfgBase::dump(os);
}

void DataMoveDfg::dump(std::ostringstream &os) {
  LLVM_DEBUG(dbgs() << "Data move DFG, use specialized ports!\n");
  return;
}

bool DedicatedDfg::Contains(Instruction *Inst) {

  // FIXME(@were): I forgot what this is doing.

  // if (Inst->getParent() == Parent->Config->getParent()) {
  //   for (Instruction *I = Parent->Config, *E = &Parent->Config->getParent()->back();
  //        I != E; I = I->getNextNode()) {
  //     if (I == Inst)
  //       return true;
  //   }
  // }

  // if (Inst->getParent() == Parent->Fence->getParent()) {
  //   for (Instruction *I = Inst, *E = &Parent->Fence->getParent()->back();
  //        I != E; I = I->getNextNode()) {
  //     if (I == Parent->Fence)
  //       return true;
  //   }
  // }

  return Contains(Inst->getParent());
}

bool DedicatedDfg::Contains(BasicBlock *BB) {
  // FIXME: I hope for now it is good enough.
  //        Later maybe we need to dive into the paritally contain thing.
  return Blocks.find(BB) != Blocks.end();
}

bool TemporalDfg::Contains(Instruction *Inst) {
  for (Instruction *I = Begin; I != End; I = I->getNextNode())
    if (I == Inst)
      return true;
  return false;
}

bool TemporalDfg::Contains(BasicBlock *BB) {
  return BB == Begin->getParent();
}

int TemporalDfg::getUnroll() {
  return 1;
}

int DedicatedDfg::getUnroll() {
  return UnrollFactor;
}

AnalyzedStream DedicatedDfg::AnalyzeDataStream(Value *Index, int Bytes) {
  return AnalyzeDataStream(Index, Bytes, false, nullptr);
}

AnalyzedStream
DedicatedDfg::AnalyzeDataStream(Value *Index, int Bytes, bool DoOuterRepeat,
                                Instruction *InsertBefore) {
  SCEVExpander Expander(*Parent->Query->SE, Parent->Func.getParent()->getDataLayout(), "");
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
  LLVM_DEBUG(EV->dump(); dbgs() << "Index (" << EV->getSCEVType() << "): "; EV->dump());

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

  assert(EV->getSCEVType() == scAddRecExpr && "The loop should starts with a polyhedral");

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
      assert(CheckLoopInvariant(Cur->getStepRecurrence(*SE), i + 2, LoopNest, SE));
      Step = Expander.expandCodeFor(Cur->getStepRecurrence(*SE), nullptr, InsertBefore);
      auto L = Cur->getLoop();
      LLVM_DEBUG(
        dbgs() << "Cur: "; Cur->getLoop()->dump();
        dbgs() << "Nest:"; LoopNest[i]->dump();
      );
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
      auto Cnt = Expander.expandCodeFor(BackTaken_->getStart(), nullptr, InsertBefore);
      assert(CheckLoopInvariant(BackTaken_->getStart(), i + 1, LoopNest, SE));
      IB->SetInsertPoint(InsertBefore);
      DimTripCount = IB->CreateAdd(Cnt, One, "trip.count");
      Value *NextStretch = nullptr;
      if (i + 1 < LoopNest.size() && BackTaken_->getLoop() == LoopNest[i + 1]) {
        NextStretch = Expander.expandCodeFor(BackTaken_->getStepRecurrence(*SE), nullptr,
                                             InsertBefore);
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
        int64_t CntInt = dyn_cast<Constant>(Cnt)->getUniqueInteger().getSExtValue();
        StretchInt *= CntInt;
        if (isa<Constant>(Step)) {
          int64_t StepInt = dyn_cast<Constant>(Step)->getUniqueInteger().getSExtValue();
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

    LLVM_DEBUG(
      dbgs() << "Injected: "; InsertBefore->dump();
      dbgs() << "Current: "; Step->dump();
      dbgs() << "Stretch: " << Stretch;
      dbgs() << "\n"
    );

    Stretch = StretchInt;
  }

  LLVM_DEBUG(
    dbgs() << "After exiting: ";
    EV->dump()
  );

  Value* Start = nullptr;

  Start = Expander.expandCodeFor(EV, nullptr, &Preheader->back());
  if (auto SARE = dyn_cast<SCEVAddRecExpr>(EV)) {
    if (SARE->getLoop() != LoopNest.back() && SARE->getLoop()->contains(LoopNest.back())) {
      Start = Expander.expandCodeFor(SARE->getStart(), nullptr, &Preheader->back());
      auto IndVar = SARE->getLoop()->getCanonicalInductionVariable();
      assert(IndVar);
      auto Stride = Expander.expandCodeFor(SARE->getStepRecurrence(*SE), nullptr, InsertBefore);
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

DataMoveDfg::DataMoveDfg(DfgFile *Parent_, Loop *LI, int Unroll) :
  DedicatedDfg(Parent_, LI, Unroll) {
  Kind = DfgBase::DataMove;
}

Value *DfgBase::UnrollConstant() {
  return Parent->Query->IBPtr->getInt64(getUnroll());
}


LLVMContext &DfgBase::getCtx() {
  return Parent->getCtx();
}


LLVMContext &DfgFile::getCtx() {
  return Query->IBPtr->getContext();
}

template<typename DfgType>
void AddDfg(DfgFile *DF, MDNode *Ptr, Loop *LI) {
  assert(Ptr->getNumOperands() == 2);
  auto MDFactor = dyn_cast<ConstantAsMetadata>(Ptr->getOperand(1));
  assert(MDFactor);
  int Factor =(int) MDFactor->getValue()->getUniqueInteger().getSExtValue();
  DF->addDfg(new DfgType(DF, LI, Factor));
}

DfgFile::DfgFile(StringRef Name, Function &F, IntrinsicInst *Start, IntrinsicInst *End,
                 StreamSpecialize *SS) : FileName(Name), Func(F), Config(Start), Fence(End), Query(SS) {

  auto LI = SS->LI;
  auto DT = SS->DT;

  if (Start && End) {
    std::set<BasicBlock*> OutOfBound;
    for (auto BBN : breadth_first(DT->getNode(Fence->getParent()))) {
      if (BBN->getBlock() == Fence->getParent())
        continue;
      OutOfBound.insert(BBN->getBlock());
    }
    for (auto NestedLoop : *LI) {
      for (auto SubLoop : breadth_first(NestedLoop)) {
        if (!DT->dominates(Start, SubLoop->getBlocks()[0]))
          continue;
        if (!SubLoop->getLoopID() || SubLoop->getLoopID()->getNumOperands() == 0)
          continue;
        bool InBound = true;
        for (auto BB : SubLoop->getBlocks()) {
          if (OutOfBound.count(BB))
            InBound = false;
        }
        if (!InBound)
          continue;
        if (MDNode *MD = GetUnrollMetadata(SubLoop->getLoopID(), "llvm.loop.ss.dedicated")) {
          AddDfg<DedicatedDfg>(this, MD, SubLoop);
        }
        if (MDNode *MM = GetUnrollMetadata(SubLoop->getLoopID(), "llvm.loop.ss.datamove")) {
          AddDfg<DataMoveDfg>(this, MM, SubLoop);
        }
      }
    }

    for (auto BBN : breadth_first(DT->getNode(Config->getParent()))) {
      auto BB = BBN->getBlock();

      auto range = make_range(BB != Start->getParent() ? BB->begin() : Start->getIterator(),
                              BB != End->getParent() ? BB->end() : End->getIterator());
      for (auto &I : range) {
        auto TemporalStart = dyn_cast<IntrinsicInst>(&I);
        if (!TemporalStart || TemporalStart->getIntrinsicID() != Intrinsic::ss_temporal_region_start)
          continue;
        // TODO: Maybe later we need control flow in the temporal regions
        bool Found = false;
        for (Instruction *Cur =TemporalStart; Cur != &Cur->getParent()->back();
          Cur = Cur->getNextNode()) {
          auto TemporalEnd = dyn_cast<IntrinsicInst>(Cur);
          if (!TemporalEnd || TemporalEnd->getIntrinsicID() != Intrinsic::ss_temporal_region_end)
            continue;
          assert(TemporalEnd->getOperand(0) == TemporalStart);
          addDfg(new TemporalDfg(this, TemporalStart, TemporalEnd));
          Found = true;
        }
        assert(Found);
      }

      if (BB == Fence->getParent()) {
        break;
      }
    }
  }

}

int getPortImpl() {
  static const int Ports[] = {23, 24, 25, 26, 27, 28, 29, 30, 31};
  static const int N = (sizeof Ports) / (sizeof(int));
  static int Cur = 0;
  int Res = Ports[Cur];
  Cur = (Cur + 1) % N;
  return Res;
}

int DfgBase::getNextIND() {
  return getPortImpl();
  //static const int Ports[] = {27, 28, 29, 30, 31};
  //static const int N = (sizeof Ports) / (sizeof(int));
  //static int Cur = 0;
  //int Res = Ports[Cur];
  //Cur = (Cur + 1) % N;
  //return Res;
}

int DfgBase::getNextReserved() {
  return getPortImpl();
  //static const int Ports[] = {23, 24, 25, 26};
  //static const int N = (sizeof Ports) / (sizeof(int));
  //static int Cur = 0;
  //int Res = Ports[Cur];
  //Cur = (Cur + 1) % N;
  //return Res;
}

SmallVector<BasicBlock*, 0> DedicatedDfg::getBlocks() {
  SmallVector<BasicBlock*, 0> Res(InnerMost()->getBlocks().begin(),
                                  InnerMost()->getBlocks().end());
  return Res;
}

SmallVector<BasicBlock*, 0> TemporalDfg::getBlocks() {
  SmallVector<BasicBlock*, 0> Res{Begin->getParent()};
  return Res;
}

void DfgBase::FinalizeEntryID() {
  for (size_t i = 0; i < Entries.size(); ++i)
    Entries[i]->ID = i;
}

AnalyzedStream TemporalDfg::AnalyzeDataStream(Value *Index, int Bytes) {
  AnalyzedStream res;
  auto &Ctx = Parent->getCtx();
  res.AR.Wrapped = createConstant(Ctx, 1);
  res.Dimensions.emplace_back(Index, createConstant(Ctx, Bytes), 0);
  return res;
}

bool DedicatedDfg::InThisScope(Instruction *I) {
  return LoopNest.back()->getBlocksSet().count(I->getParent());
}

bool TemporalDfg::InThisScope(Instruction *Inst) {
  for (Instruction *I = Begin; I != End; I = I->getNextNode()) {
    if (I == Inst) {
      return true;
    }
  }
  return false;
}

bool IntrinDfg::InThisScope(Instruction *Inst) {
  return Inst == Intrin;
}

void DfgFile::InspectSPADs() {

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

  std::vector<Instruction*> ToInject;
  auto DT = Query->DT;

  for (auto &BB : Func) {
    if (!DT->dominates(&BB.front(), Fence))
      continue;
    if (&BB != Config->getParent() && !DT->dominates(Config, &BB))
      continue;
    auto range = make_range(&BB != Config->getParent() ? BB.begin() : Config->getIterator(),
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
        // Calling an LLVM function will put this function as the last argument of the
        // CallSite.
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
