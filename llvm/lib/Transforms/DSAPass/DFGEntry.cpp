#include "llvm/IR/Dominators.h"
#include "llvm/Support/FormatVariadic.h"
#include <queue>
#include <sstream>

#include "DFGEntry.h"
#include "StreamAnalysis.h"
#include "Transformation.h"
#include "Util.h"

#define DEBUG_TYPE "stream-specialize"

using namespace llvm;

const char *KindStr[] = {
    "DFGEntry",

    // Computation {
    "ComputeStarts", "ComputeBody", "Duplicate", "Accumulator", "ComputeEnds",
    // }

    // Predicate {
    "Predicate",
    // }

    // Port {
    "PortStarts", "PortBase",

    // InPort {
    "InPortStarts", "InputPort", "MemPort", "IndMemPort", "CtrlMemPort",
    "InputConst", "StreamInPort", "CtrlSignal", "InPortEnds",
    // }

    // OutPort {
    "OutPortStarts", "OutputPort", "PortMem", "AtomicPortMem", "StreamOutPort",
    "OutPortEnds",
    // }

    "PortEnds"
    // }
};

DFGEntry::DFGEntry(DFGBase *Parent_) : Parent(Parent_) {
  ID = Parent_->Entries.size();
}

Predicate *DFGEntry::getPredicate(int *x) {
  auto DT = Parent->Parent->Query->DT;

  if (!UnderlyingInst())
    return nullptr;
  // Sometimes, the CFG is too simple to have a immediate dom.
  if (auto Inst = dyn_cast<Instruction>(UnderlyingInst())) {
    Predicate *Res = nullptr;
    for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
      if (auto Entry = Parent->InThisDFG(Inst->getOperand(i))) {
        if (Res == nullptr) {
          Res = Entry->getPredicate();
        } else {
          if (Entry->getPredicate()) {
            assert(Res == Entry->getPredicate());
          }
        }
      }
    }
    if (auto DomNode = DT->getNode(Inst->getParent())->getIDom()) {
      auto &LastInst = DomNode->getBlock()->back();
      bool FindDom = false;
      for (auto Elem : Parent->getBlocks()) {
        if (Elem == DomNode->getBlock()) {
          FindDom = true;
          break;
        }
      }
      if (!FindDom)
        return nullptr;
      if (auto BI = dyn_cast<BranchInst>(&LastInst)) {
        if (BI->isConditional()) {
          auto RawRes = Parent->InThisDFG(BI->getCondition());
          if (!RawRes) {
            // I am not sure how to properly handle this condition...
            return nullptr;
          }
          if (Res == nullptr) {
            Res = dyn_cast<Predicate>(RawRes);
          } else {
            assert(Res == RawRes);
          }
          return Res;
        }
      }
    }
  }
  return nullptr;
}

int DFGEntry::getAbstainBit() {
  if (auto Inst = UnderlyingInst()) {
    auto DT = Parent->Parent->Query->DT;
    auto CurrentBB = Inst->getParent();
    Predicate *Pred = nullptr;
    int Res = 7;
    while (true) {
      auto DomNode = DT->getNode(CurrentBB)->getIDom();
      if (!DomNode)
        break;
      if (!Parent->Contains(DomNode->getBlock()))
        break;
      auto DomBB = DomNode->getBlock();
      auto BI = dyn_cast<BranchInst>(&DomBB->back());
      if (BI->isConditional()) {
        auto Cond = BI->getCondition();
        if (Pred == nullptr) {
          Pred = dyn_cast<Predicate>(Parent->InThisDFG(Cond));
          assert(Pred);
        } else {
          assert(Pred == Parent->InThisDFG(Cond));
        }
        int SubRes = Pred->ToCompareRes(dyn_cast<Instruction>(Cond),
                                        BI->getSuccessor(0) == CurrentBB);
        assert(SubRes != -1);
        Res &= SubRes;
      }
      CurrentBB = DomBB;
    }
    return ~Res & 7;
  }
  return 0;
}

std::string DFGEntry::Name(int Idx) {
  if (Idx != -1 && ShouldUnroll()) {
    return formatv("sub{0}_v{1}_{2}", Parent->ID, ID, Idx);
  }
  return formatv("sub{0}_v{1}_", Parent->ID, ID);
}

PortBase::PortBase(DFGBase *Parent_)
    : DFGEntry(Parent_), SoftPortNum(-1), IntrinInjected(false) {
  Kind = kPortBase;
}

OutputPort::OutputPort(DFGBase *Parent_, Value *Value_) : PortBase(Parent_) {
  auto Inst = dyn_cast<Instruction>(Value_);
  assert(Inst);

  LLVM_DEBUG(Inst->dump());

  if (!Parent_->InThisDFG(Inst)) {
    int Cnt = 0;
    PHINode *Phi = dyn_cast<PHINode>(Inst);
    assert(Phi);

    std::set<Instruction *> Equivs;
    FindEquivPHIs(Phi, Equivs);

    for (auto &Inst : Equivs) {
      if (Parent_->InThisDFG(Inst)) {
        Output = dyn_cast<Instruction>(Inst);
        assert(Output);
        LLVM_DEBUG(dbgs() << "incoming: "; Inst->dump());
        ++Cnt;
      }
    }

    // TODO: Support multiple convergence later...
    assert(Cnt == 1);
  } else {
    Output = Inst;
  }
  Kind = kOutputPort;
}

PortMem::PortMem(DFGBase *Parent_, StoreInst *Store_)
    : OutputPort(Parent_, Store_->getValueOperand()), Store(Store_) {
  Kind = kPortMem;
}

Accumulator::Accumulator(DFGBase *Parent_, Instruction *Operation_,
                         CtrlSignal *Ctrl_)
    : ComputeBody(Parent_, Operation_), Ctrl(Ctrl_) {
  Kind = kAccumulator;
}

InputPort::InputPort(DFGBase *Parent_) : PortBase(Parent_) {
  Kind = kInputPort;
}

MemPort::MemPort(DFGBase *Parent_, LoadInst *Load_)
    : InputPort(Parent_), Load(Load_) {
  Kind = kMemPort;
}

ComputeBody::ComputeBody(DFGBase *Parent_, Instruction *Operation_)
    : DFGEntry(Parent_), Operation(Operation_) {
  assert(CanBeAEntry(Operation_));
  Kind = kComputeBody;
}

CtrlSignal::CtrlSignal(DFGBase *Parent_) : InputPort(Parent_) {
  Kind = kCtrlSignal;
}

CtrlMemPort::CtrlMemPort(DFGBase *Parent_, LoadInst *Load_, Value *Start_,
                         Value *TripCnt_, Predicate *Pred_, int Mask_)
    : InputPort(Parent_), Load(Load_), Start(Start_), TripCnt(TripCnt_),
      Pred(Pred_), Mask(Mask_) {
  Kind = kCtrlMemPort;
}

Predicate *CtrlMemPort::getPredicate(int *x) { return Pred; }

Instruction *CtrlMemPort::UnderlyingInst() { return Load; }

int PortBase::PortWidth() {
  return UnderlyingValue()->getType()->getScalarSizeInBits();
}

Instruction *DFGEntry::UnderlyingInst() { return nullptr; }

Value *DFGEntry::UnderlyingValue() { return UnderlyingInst(); }

bool DFGEntry::IsInMajor() {
  if (!UnderlyingInst()) {
    return false;
  }
  for (auto BB : Parent->getBlocks())
    if (UnderlyingInst()->getParent() == BB)
      return true;
  return false;
}

Instruction *ComputeBody::UnderlyingInst() { return Operation; }

Instruction *MemPort::UnderlyingInst() { return Load; }

Instruction *PortMem::UnderlyingInst() { return Store; }

std::vector<Instruction *> InputConst::UnderlyingInsts() {
  if (auto Inst = dyn_cast<Instruction>(Val)) {
    return {Inst};
  }
  return {};
}

Instruction *InputConst::UnderlyingInst() { return dyn_cast<Instruction>(Val); }

std::vector<Value *> InputConst::UnderlyingValues() { return {Val}; }

Value *InputConst::UnderlyingValue() { return Val; }

InputConst::InputConst(DFGBase *Parent_, Value *Val_)
    : InputPort(Parent_), Val(Val_) {
  Kind = kInputConst;
}

StreamInPort::StreamInPort(DFGBase *Parent_, Instruction *Inst)
    : InputPort(Parent_), DataFrom(Inst) {
  Kind = kStreamInPort;
}

StreamOutPort::StreamOutPort(DFGBase *Parent_, Instruction *Inst)
    : OutputPort(Parent_, Inst) {
  Kind = kStreamOutPort;
}

Instruction *OutputPort::UnderlyingInst() { return Output; }

Instruction *StreamInPort::UnderlyingInst() { return DataFrom; }

int OutputPort::PortWidth() { return Output->getType()->getScalarSizeInBits(); }

StreamInPort *StreamOutPort::FindConsumer() {
  for (auto &DFG : Parent->Parent->DFGs) {
    if (DFG == Parent)
      continue;
    for (auto &SIP : DFG->EntryFilter<StreamInPort>()) {
      if (SIP->DataFrom == this->Output)
        return SIP;
    }
  }
  CHECK(false) << "Cannot find consumer for " << *UnderlyingInst();
  return nullptr;
}

std::vector<OutputPort *> ComputeBody::GetOutPorts() {
  std::vector<OutputPort *> Res;
  for (auto Elem : Parent->Entries) {
    if (auto OP = dyn_cast<OutputPort>(Elem)) {
      std::queue<Value *> Q;
      std::set<Value *> Visited;
      Q.push(OP->Output);
      Visited.insert(OP->Output);
      while (!Q.empty()) {
        auto Cur = Q.front();
        Q.pop();
        if (Cur == UnderlyingInst()) {
          Res.push_back(OP);
          break;
        }
        for (auto &Elem : Cur->uses()) {
          if (!Visited.count(Elem)) {
            Q.push(Elem);
            Visited.insert(Elem);
          }
        }
      }
    }
  }
  return Res;
}

bool DFGEntry::ShouldUnroll() {
  if (Parent->getUnroll() <= 1)
    return false;
  if (!IsInMajor())
    return false;
  return true;
}

bool ComputeBody::ShouldUnroll() {
  if (!DFGEntry::ShouldUnroll())
    return false;
  auto Inst = UnderlyingInst();
  for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
    if (auto Entry = Parent->InThisDFG(Inst->getOperand(i))) {
      if (Entry->ShouldUnroll())
        return true;
    }
  }
  return false;
}

bool Accumulator::ShouldUnroll() { return false; }

bool CtrlSignal::ShouldUnroll() { return false; }

bool OutputPort::ShouldUnroll() {
  if (!DFGEntry::ShouldUnroll())
    return false;
  auto OV = Parent->InThisDFG(Output);
  CHECK(OV);
  return OV->ShouldUnroll();
}

bool MemPort::ShouldUnroll() {
  if (!DFGEntry::ShouldUnroll())
    return false;
  if (auto DD = dyn_cast<DedicatedDFG>(Parent))
    return !DD->InnerMost()->isLoopInvariant(Load->getPointerOperand());
  return false;
}

bool IndMemPort::ShouldUnroll() {
  if (!DFGEntry::ShouldUnroll())
    return false;
  if (auto DD = dyn_cast<DedicatedDFG>(Parent))
    return !DD->InnerMost()->isLoopInvariant(Index->Load->getPointerOperand());
  return false;
}

bool HasOtherUser(InputPort *IP, Value *Val) {
  for (auto User : Val->users()) {
    if (auto Entry = IP->Parent->InThisDFG(User)) {
      if (auto CB = dyn_cast<ComputeBody>(Entry)) {
        if (!CB->isAtomic())
          return true;
      }
      if (isa<Predicate>(Entry)) {
        return true;
      }
    }
  }
  return false;
}

int DFGEntry::Index() {
  assert(ID != -1);
  return ID;
}

void DFGEntry::dump(std::ostringstream &os) {
  os << "[" << (void *)this << "] " << KindStr[Kind] << " ("
     << (void *)getPredicate() << ")";
  if (UnderlyingInst()) {
    std::string res;
    raw_string_ostream oss(res);
    oss << *UnderlyingInst();
    os << oss.str();
  } else {
    os << "\n";
  }
}

Value *Accumulator::NumValuesProduced() {
  auto Inst = UnderlyingInst();
  assert(IsInMajor());
  for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
    if (auto Phi = dyn_cast<PHINode>(Inst->getOperand(i))) {
      for (size_t j = 0; j < Phi->getNumIncomingValues(); ++j) {
        auto IB = Phi->getIncomingBlock(j);
        bool Found = false;
        for (auto BB : Parent->getBlocks()) {
          if (BB == IB) {
            Found = true;
            break;
          }
        }
        if (!Found) {
          auto DD = dyn_cast<DedicatedDFG>(Parent);
          assert(DD);
          for (size_t k = 0; k < DD->LoopNest.size(); ++k) {
            if (DD->LoopNest[k]->getBlocksSet().count(IB)) {
              return DD->ProdTripCount(
                  k, DD->Preheader->getFirstNonPHI()->getNextNode());
            }
          }
          return DD->ProdTripCount(
              DD->LoopNest.size(),
              DD->Preheader->getFirstNonPHI()->getNextNode());
        }
      }
    }
  }
  assert(false);
  return nullptr;
}

int MemPort::FillMode() {
  if (auto DD = dyn_cast<DedicatedDFG>(Parent)) {
    if (Parent->getUnroll() <= 1)
      return DP_NoPadding;
    return DD->ConsumedByAccumulator(this) ? DP_PostStrideZero
                                           : DP_PostStridePredOff;
  }
  return DP_NoPadding;
}

IndMemPort::IndMemPort(DFGBase *Parent_, LoadInst *Index_, LoadInst *Load)
    : InputPort(Parent_), Load(Load) {
  Index = new MemPort(Parent, Index_);
  Kind = kIndMemPort;
}

Instruction *IndMemPort::UnderlyingInst() { return Load; }

std::string getOperationStr(Instruction *Inst, bool isAcc, bool predicated) {
  std::string OpStr;
  int BitWidth = Inst->getType()->getScalarSizeInBits();

  if (auto Cmp = dyn_cast<CmpInst>(Inst)) {
    // TODO: Support floating point
    OpStr = "compare";
    BitWidth = Cmp->getOperand(0)->getType()->getScalarSizeInBits();
  } else if (auto Call = dyn_cast<CallInst>(Inst)) {
    CHECK(Call);
    OpStr = Call->getCalledFunction()->getName().str();
  } else {
    OpStr = Inst->getOpcodeName();
    if (isAcc) {
      if (!predicated) {
        OpStr = OpStr[0] == 'f' ? "facc" : "acc";
      } else {
        OpStr = OpStr[0] == 'f' ? "faccumulate" : "accumulate";
      }
    }
  }

  for (int i = 0, e = OpStr[0] == 'f' ? 2 : 1; i < e; ++i) {
    OpStr[i] -= 'a';
    OpStr[i] += 'A';
  }

  return formatv("{0}{1}", OpStr, BitWidth);
}

std::string ValueToOperandText(Value *Val) {

  if (auto CI = dyn_cast<ConstantInt>(Val)) {
    return formatv("{0}", CI->getValue().getSExtValue());
  } else if (auto CFP = dyn_cast<ConstantFP>(Val)) {
    // TODO: Support more data types
    double FPV = CFP->getValueAPF().convertToDouble();
    uint64_t *RI = reinterpret_cast<uint64_t *>(&FPV);
    return formatv("{0}", *RI);
  }

  CHECK(false) << "Cannot dump " << *Val;
  return "";
}

bool Predicate::addCond(Instruction *Inst) {
  auto Cmp = dyn_cast<ICmpInst>(Inst);
  assert(Cmp);

  bool NonReverse = Cmp->getOperand(0) == Cond[0]->getOperand(0) &&
                    Cmp->getOperand(1) == Cond[0]->getOperand(1);
  bool Reverse = (Cmp->getOperand(1) == Cond[0]->getOperand(0) &&
                  Cmp->getOperand(0) == Cond[0]->getOperand(1));
  assert(NonReverse || Reverse);

  for (size_t i = 0; i < Cond.size(); ++i) {
    auto Elem = Cond[i];
    if (Cmp == Elem) {
      LLVM_DEBUG(dbgs() << "Alread added! No further operation needed!");
      return Reversed[i];
    }
  }

  Cond.push_back(Inst);
  Reversed.push_back(Reverse);

  return Reverse;
}

int Predicate::Contains(Instruction *Inst) {
  for (size_t i = 0; i < Cond.size(); ++i) {
    if (Cond[i] == Inst)
      return i;
  }
  return -1;
}

int Predicate::ToCompareRes(Instruction *Inst, bool TF) {
  int Idx = Contains(Inst);
  assert(Idx != -1);
  auto Cmp = dyn_cast<ICmpInst>(Inst);
  if (!Cmp)
    return -1;
  return PredicateToInt(Cmp->getPredicate(), TF, Reversed[Idx]);
}

struct ControlBit {
  std::ostringstream SubCtrl[3];
  Predicate *Pred{nullptr};

  void addControlledMemoryStream(int Idx, DFGEntry *DE) {
    if (auto CMP = dyn_cast<CtrlMemPort>(DE)) {
      if (Pred == nullptr) {
        Pred = CMP->Pred;
      } else {
        assert(Pred == CMP->Pred && "An instruction cannot be controlled by "
                                    "more than one predication.");
      }
      assert(Pred);
      for (int j = 0; j < 3; ++j) {
        if (~CMP->Mask >> j & 1) {
          if (!SubCtrl[j].str().empty()) {
            SubCtrl[j] << "|";
          }
          SubCtrl[j] << "b" << (Idx + 1);
        }
      }
    }
  }

  bool empty() {
    for (int i = 0; i < 3; ++i)
      if (!SubCtrl[i].str().empty())
        return false;
    return true;
  }

  std::string finalize() {
    std::ostringstream Ctrl;
    for (int i = 0; i < 3; ++i) {
      if (!SubCtrl[i].str().empty()) {
        if (!Ctrl.str().empty())
          Ctrl << ", ";
        Ctrl << i << ":" << SubCtrl[i].str();
      }
    }
    return Ctrl.str();
  }

  void updateAbstain(int x, bool isAcc) {
    for (int i = 0; i < 3; ++i) {
      if (x >> i & 1) {
        if (!SubCtrl[i].str().empty()) {
          SubCtrl[i] << "|";
        }
        SubCtrl[i] << "a";
      } else if (isAcc) {
        if (!SubCtrl[i].str().empty()) {
          SubCtrl[i] << "|";
        }
        SubCtrl[i] << "d";
      }
    }
  }
};

// TODO(@were): Do I need to support vectorized comparison?
void Predicate::EmitCond(std::ostringstream &os) {

  if (!dsa::utils::ModuleContext().PRED) {
    return;
  }

  {
    os << "# [Predication] Combination\n";
    for (auto I : Cond) {
      std::string Tmp;
      raw_string_ostream oss(Tmp);
      I->print(oss);
      os << "# " << Tmp << "\n";
    }
  }

  ControlBit CtrlBit;
  os << Name(-1) << " = Compare"
     << Cond[0]->getOperand(0)->getType()->getScalarSizeInBits() << "(";
  for (size_t i = 0; i < Cond[0]->getNumOperands(); ++i) {
    auto Val = Cond[0]->getOperand(i);
    if (i)
      os << ", ";
    if (auto EntryOp = Parent->InThisDFG(Val)) {
      os << EntryOp->Name(-1);
      CtrlBit.addControlledMemoryStream(i, EntryOp);
      if (auto CMP = dyn_cast<CtrlMemPort>(EntryOp))
        CMP->ForPredicate = true;
    } else {
      os << ValueToOperandText(Val);
    }
  }

  if (!CtrlBit.empty()) {
    if (CtrlBit.Pred == this)
      os << ", self=";
    else
      os << ", ctrl=" << CtrlBit.Pred->Name(-1);
    os << "{" << CtrlBit.finalize() << "}";
  }

  os << ")\n";
}

AtomicPortMem *ComputeBody::isAtomic() {
  for (auto Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (Entry->Op == UnderlyingInst()) {
      return Entry;
    }
  }
  return nullptr;
}

void ComputeBody::EmitAtomic(std::ostringstream &os) {
  if (isImmediateAtomic()) {
    os << "Output" << UnderlyingInst()->getType()->getScalarSizeInBits() << ": "
       << Name();
    if (ShouldUnroll())
      os << "[" << Parent->getUnroll() << "]";
    os << "\n";
  }
}

AtomicPortMem *ComputeBody::isImmediateAtomic() {
  for (auto Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (Entry->OpCode != 3 && Entry->Operand == UnderlyingInst()) {
      return Entry;
    }
  }
  return nullptr;
}

Predicate::Predicate(DFGBase *Parent_, Instruction *Cond_)
    : DFGEntry(Parent_), Cond{Cond_}, Reversed{false} {
  Kind = kPredicate;
}

bool Predicate::ShouldUnroll() { return false; }

Instruction *Predicate::UnderlyingInst() { return Cond[0]; }

int TBits(int Bits) {
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

bool IndMemPort::duplicated() {
  for (auto Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (Index->UnderlyingInst() == Entry->Index->UnderlyingInst()) {
      return true;
    }
  }
  return false;
}

bool MemPort::InjectUpdateStream(IRBuilder<> *IB) {
  if (!dsa::utils::ModuleContext().REC)
    return false;

  if (!IsInMajor())
    return false;

  // Wrappers
  auto DFG = dyn_cast<DedicatedDFG>(Parent);

  if (!DFG)
    return false;

  // Wrappers
  auto MP = this;

  LLVM_DEBUG(dbgs() << "Injecting update streams!\n");

  for (auto &PM : DFG->EntryFilter<PortMem>()) {
    if (!PM->IsInMajor() || PM->IntrinInjected)
      continue;
    auto Ptr0 = dyn_cast<Instruction>(MP->Load->getPointerOperand());
    auto Ptr1 = dyn_cast<Instruction>(PM->Store->getPointerOperand());
    LLVM_DEBUG(MP->Load->dump(); PM->Store->dump());
    if (Ptr0 == Ptr1) {
      LLVM_DEBUG(dbgs() << "A stream update detected!\n");
      auto Analyzed = DFG->AnalyzeDataStream(
          Ptr0,
          MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);
      /* This portion of code is deprecated. I guess this is because LLVM's SCEV
       * behaviour changed. for (int i = 0; i < n; ++i) for (int j = 0; j < m
       * ++j)
       *      // use a[j];
       * i's n trip count used to be put in outer repeat.
       * After adopting new version of LLVM, it seems to be a zero-step AddRecur
       * now.
       *
       * if (!Analyzed.OuterRepeat) {
       *   LLVM_DEBUG(dbgs() << "No outer repeat, skip!\n");
       *   continue;
       * }
       * if (isOne(Analyzed.OuterRepeat)) {
       *   LLVM_DEBUG(dbgs() << "One time update, skip!\n");
       *   continue;
       * }
       */
      if (Analyzed.Dimensions.size() == 1) {
        LLVM_DEBUG(dbgs() << "One time update, skip!\n");
        continue;
      }
      bool StrideZero = true;
      for (size_t i = 0; i < Analyzed.Dimensions.size() - 1; ++i) {
        if (auto Step =
                dyn_cast<ConstantInt>(std::get<0>(Analyzed.Dimensions[i]))) {
          if (Step->getSExtValue() != 0) {
            StrideZero = false;
            break;
          }
        }
        if (int Stretch = std::get<2>(Analyzed.Dimensions[i])) {
          LLVM_DEBUG(dbgs() << "Stretched repeat, skip!\n");
          StrideZero = false;
          break;
        }
      }
      if (!StrideZero) {
        LLVM_DEBUG(dbgs() << "No outer repeat, skip!\n");
        continue;
      }
      if (Analyzed.AR.Prime) {
        LLVM_DEBUG(dbgs() << "Isn't it an accumulation?!\n");
        continue;
      }
      Value *RepeatTime = IB->getInt64(1);
      while (Analyzed.Dimensions.size() != 1) {
        auto TripCnt = std::get<1>(Analyzed.Dimensions.front());
        RepeatTime = IB->CreateMul(RepeatTime, TripCnt);
        Analyzed.Dimensions.erase(Analyzed.Dimensions.begin());
      }
      assert(!Analyzed.Dimensions.empty());
      LLVM_DEBUG(dbgs() << "Inject a initial stream!\n");
      dsa::inject::InjectLinearStream(
          Parent->Parent->Query->IBPtr, Parent->Parent->Query->DSARegs,
          MP->SoftPortNum, Analyzed, DMO_Read, DP_NoPadding, DMT_DMA,
          MP->Load->getType()->getScalarSizeInBits() / 8);

      /// {
      auto MinusOne = IB->CreateSub(RepeatTime, IB->getInt64(1));
      auto NumElements = IB->CreateUDiv(Analyzed.BytesFromMemory(IB),
                                        IB->getInt64(PM->PortWidth() / 8));
      auto Recurrenced = IB->CreateMul(MinusOne, NumElements);
      /// }

      dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);
      DIE.SS_RECURRENCE(PM->SoftPortNum, MP->SoftPortNum, Recurrenced,
                        MP->Load->getType()->getScalarSizeInBits() / 8);

      int II = 1;
      int Conc = -1;
      if (auto CI =
              dyn_cast<ConstantInt>(std::get<1>(Analyzed.Dimensions.back()))) {
        auto CII = CI->getZExtValue();
        int CanHide = CII * 8 / PortWidth();
        if (PM->Latency - CanHide > 0) {
          II = PM->Latency - CanHide;
          LLVM_DEBUG(dbgs() << "Recur II: " << II << "\n");
        } else {
          II = 1;
          errs() << "[Warning] To hide the latency " << PM->Latency << ", "
                 << CII * 8 / PortWidth() << " elements are active\n";
          errs() << "This requires a " << CanHide - PM->Latency
                 << "-deep FIFO buffer\n";
        }
        Conc = CII;
      } else {
        errs() << "[Warning] To hide the latency " << PM->Latency
               << ", make sure your variable recur distance will not overwhlem "
                  "the FIFO buffer!";
      }
      PM->Meta.set("dest", "localport");
      PM->Meta.set("dest", MP->Name());
      {
        std::ostringstream oss;
        oss << Conc * 8 / PortWidth();
        PM->Meta.set("conc", oss.str());
      }
      dsa::inject::InjectLinearStream(
          IB, Parent->Parent->Query->DSARegs, PM->SoftPortNum, Analyzed,
          DMO_Write, DP_NoPadding, DMT_DMA,
          PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8);
      PM->IntrinInjected = MP->IntrinInjected = true;
      return true;
    }
  }

  return false;
}

void InjectLinearStreamImpl(ScalarEvolution *SE, SCEVExpander &SEE,
                            IRBuilder<> *IB, const SCEV *Idx,
                            std::vector<Loop *> LoopNest,
                            dsa::inject::RepeatInjector &RI,
                            dsa::inject::LinearInjector &LI, int Port,
                            int Unroll, int DType, MemoryOperation MO,
                            Padding Padding, MemoryType MT) {
  auto IdxLI = dsa::analysis::AnalyzeIndexExpr(SE, Idx, LoopNest);
  std::vector<dsa::analysis::LinearInfo *> LoopLI;
  for (int i = 0, N = LoopNest.size(); i < N; ++i) {
    auto CurDim = dsa::analysis::AnalyzeIndexExpr(
        SE, SE->getBackedgeTakenCount(LoopNest[i]), LoopNest);
    LoopLI.push_back(CurDim);
  }
  if (MO == MemoryOperation::DMO_Read) {
    RI.Inject(IdxLI, LoopLI, Port, Unroll);
  }
  LI.Inject(IdxLI, LoopLI, Port, MO, Padding, MT, DType);
}

AtomicPortMem::AtomicPortMem(DFGBase *Parent_, LoadInst *Index_,
                             StoreInst *Store_, int OpCode_, Instruction *Op_,
                             Value *Operand_)
    : OutputPort(Parent_, Store_->getValueOperand()),
      Index(new MemPort(Parent_, Index_)), Store(Store_), OpCode(OpCode_),
      Op(Op_), Operand(Operand_) {

  Kind = kAtomicPortMem;

  if (OpCode == 0) {
    assert(Operand);
  }
}

Instruction *AtomicPortMem::UnderlyingInst() { return Store; }

std::vector<Instruction *> Predicate::UnderlyingInsts() {
  return std::vector<Instruction *>(Cond.data(), Cond.data() + Cond.size());
}

std::vector<Instruction *> IndMemPort::UnderlyingInsts() {
  return {Index->Load, Load};
}

std::vector<Instruction *> AtomicPortMem::UnderlyingInsts() {
  if (Op) {
    return {Index->Load, Store, Op};
  }
  return {Index->Load, Store};
}

void AtomicPortMem::EmitOutPort(std::ostringstream &os) {
  // TODO: Should I just migrate EmitAtomic here?
}

int PortBase::VectorizeFactor() {
  return ShouldUnroll() ? Parent->getUnroll() : 1;
}

#define VISIT_IMPL(TYPE)                                                       \
  void TYPE::Accept(dsa::DFGEntryVisitor *V) { V->Visit(this); }
VISIT_IMPL(DFGEntry)
VISIT_IMPL(ComputeBody)
VISIT_IMPL(Predicate)
VISIT_IMPL(Accumulator)
VISIT_IMPL(PortBase)
VISIT_IMPL(InputPort)
VISIT_IMPL(CtrlMemPort)
VISIT_IMPL(MemPort)
VISIT_IMPL(StreamInPort)
VISIT_IMPL(CtrlSignal)
VISIT_IMPL(InputConst)
VISIT_IMPL(OutputPort)
VISIT_IMPL(PortMem)
VISIT_IMPL(StreamOutPort)
VISIT_IMPL(IndMemPort)
VISIT_IMPL(AtomicPortMem)
#undef VISIT_IMPL

namespace dsa {

void DFGEntryVisitor::Visit(DFGEntry *Node) {}
void DFGEntryVisitor::Visit(ComputeBody *Node) {
  Visit(static_cast<DFGEntry *>(Node));
}
void DFGEntryVisitor::Visit(Predicate *Node) {
  Visit(static_cast<DFGEntry *>(Node));
}
void DFGEntryVisitor::Visit(Accumulator *Node) {
  Visit(static_cast<ComputeBody *>(Node));
}
void DFGEntryVisitor::Visit(PortBase *Node) {
  Visit(static_cast<DFGEntry *>(Node));
}
void DFGEntryVisitor::Visit(InputPort *Node) {
  Visit(static_cast<PortBase *>(Node));
}
void DFGEntryVisitor::Visit(CtrlMemPort *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(MemPort *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(StreamInPort *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(CtrlSignal *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(InputConst *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(OutputPort *Node) {
  Visit(static_cast<PortBase *>(Node));
}
void DFGEntryVisitor::Visit(PortMem *Node) {
  Visit(static_cast<OutputPort *>(Node));
}
void DFGEntryVisitor::Visit(StreamOutPort *Node) {
  Visit(static_cast<OutputPort *>(Node));
}
void DFGEntryVisitor::Visit(IndMemPort *Node) {
  Visit(static_cast<InputPort *>(Node));
}
void DFGEntryVisitor::Visit(AtomicPortMem *Node) {
  Visit(static_cast<OutputPort *>(Node));
}

} // namespace dsa