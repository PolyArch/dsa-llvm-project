#include <queue>
#include <sstream>
#include "llvm/Support/FormatVariadic.h"
#include "llvm/IR/Dominators.h"

#include "Util.h"
#include "DfgEntry.h"
#include "Transformation.h"

#define DEBUG_TYPE "stream-specialize"

using namespace llvm;

const char *KindStr[] = {
  "DfgEntry",

  // Computation {
  "ComputeStarts",
  "ComputeBody",
  "Duplicate",
  "Accumulator",
  "ComputeEnds",
  // }

  // Predicate {
  "Predicate",
  // }

  // Port {
  "PortStarts",
  "PortBase",

  // InPort {
  "InPortStarts",
  "InputPort",
  "MemPort",
  "IndMemPort",
  "CtrlMemPort",
  "InputConst",
  "StreamInPort",
  "CtrlSignal",
  "InPortEnds",
  // }

  // OutPort {
  "OutPortStarts",
  "OutputPort",
  "PortMem",
  "AtomicPortMem",
  "StreamOutPort",
  "OutPortEnds",
  // }

  "PortEnds"
  // }
};

DfgEntry::DfgEntry(DfgBase *Parent_) : Parent(Parent_) {}

Predicate *DfgEntry::getPredicate(int *x) {
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

int DfgEntry::getAbstainBit() {
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
        int SubRes =
          Pred->ToCompareRes(dyn_cast<Instruction>(Cond), BI->getSuccessor(0) == CurrentBB);
        assert(SubRes != -1);
        Res &= SubRes;
      }
      CurrentBB = DomBB;
    }
    return ~Res & 7;
  }
  return 0;
}

std::string DfgEntry::NameInDfg(int vec) {
  if (!ShouldUnroll())
    return formatv("sub{0}_v{1}", Parent->ID, ID);
  if (vec != -1)
    return formatv("sub{0}_v{1}_{2}", Parent->ID, ID, vec);
  return formatv("sub{0}_v{1}_", Parent->ID, ID);
}

PortBase::PortBase(DfgBase *Parent_) : DfgEntry(Parent_), SoftPortNum(-1), IntrinInjected(false) {
  Kind = kPortBase;
}

OutputPort::OutputPort(DfgBase *Parent_, Value *Value_) : PortBase(Parent_) {
  auto Inst = dyn_cast<Instruction>(Value_);
  assert(Inst);

  LLVM_DEBUG(Inst->dump());

  if (!Parent_->InThisDFG(Inst)) {
    int Cnt = 0;
    PHINode *Phi = dyn_cast<PHINode>(Inst);
    assert(Phi);

    std::set<Instruction*> Equivs;
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

PortMem::PortMem(DfgBase *Parent_, StoreInst *Store_) :
  OutputPort(Parent_, Store_->getValueOperand()), Store(Store_) {
  Kind = kPortMem;
}

Accumulator::Accumulator(DfgBase *Parent_, Instruction *Operation_, CtrlSignal *Ctrl_) :
  ComputeBody(Parent_, Operation_), Ctrl(Ctrl_) {
  Kind = kAccumulator;
}

InputPort::InputPort(DfgBase *Parent_) :
  PortBase(Parent_) {
  Kind = kInputPort;
}

MemPort::MemPort(DfgBase *Parent_, LoadInst *Load_) : InputPort(Parent_), Load(Load_) {
  Kind = kMemPort;
}

ComputeBody::ComputeBody(DfgBase *Parent_, Instruction *Operation_) :
  DfgEntry(Parent_), Operation(Operation_) {
  assert(CanBeAEntry(Operation_));
  Kind = kComputeBody;
}

CtrlSignal::CtrlSignal(DfgBase *Parent_) : InputPort(Parent_) {
  Kind = kCtrlSignal;
}

CtrlMemPort::CtrlMemPort(DfgBase *Parent_, LoadInst *Load_, Value *Start_, Value *TripCnt_,
                         Predicate *Pred_, int Mask_) : InputPort(Parent_), Load(Load_),
                                                        Start(Start_), TripCnt(TripCnt_),
                                                        Pred(Pred_), Mask(Mask_) {
  Kind = kCtrlMemPort;
}

Predicate *CtrlMemPort::getPredicate(int *x) {
  return Pred;
}

Instruction *CtrlMemPort::UnderlyingInst() {
  return Load;
}

int PortBase::PortWidth() {
  return UnderlyingValue()->getType()->getScalarSizeInBits();
}

Instruction* DfgEntry::UnderlyingInst() {
  return nullptr;
}

Value* DfgEntry::UnderlyingValue() {
  return UnderlyingInst();
}

bool DfgEntry::IsInMajor() {
  if (!UnderlyingInst()) {
    return false;
  }
  for (auto BB : Parent->getBlocks())
    if (UnderlyingInst()->getParent() == BB)
      return true;
  return false;
}

Instruction *ComputeBody::UnderlyingInst() {
  return Operation;
}

Instruction *MemPort::UnderlyingInst() {
  return Load;
}

Instruction *PortMem::UnderlyingInst() {
  return Store;
}

std::vector<Instruction*> InputConst::UnderlyingInsts() {
  if (auto Inst = dyn_cast<Instruction>(Val)) {
    return {Inst};
  }
  return {};
}

Instruction *InputConst::UnderlyingInst() {
  return dyn_cast<Instruction>(Val);
}

std::vector<Value*>InputConst::UnderlyingValues() {
  return {Val};
}

Value *InputConst::UnderlyingValue() {
  return Val;
}

InputConst::InputConst(DfgBase *Parent_, Value *Val_) : InputPort(Parent_), Val(Val_) {
  Kind = kInputConst;
}

StreamInPort::StreamInPort(DfgBase *Parent_, Instruction *Inst) : InputPort(Parent_), DataFrom(Inst) {
  Kind = kStreamInPort;
}

StreamOutPort::StreamOutPort(DfgBase *Parent_, Instruction *Inst) : OutputPort(Parent_, Inst) {
  Kind = kStreamOutPort;
}

Instruction *OutputPort::UnderlyingInst() {
  return Output;
}

Instruction *StreamInPort::UnderlyingInst() {
  return DataFrom;
}

int OutputPort::PortWidth() {
  return Output->getType()->getScalarSizeInBits();
}

StreamInPort *StreamOutPort::FindConsumer() {
  for (auto &DFG : Parent->Parent->DFGs) {
    if (DFG == Parent)
      continue;
    for (auto &SIP : DFG->EntryFilter<StreamInPort>()) {
      if (SIP->DataFrom == this->Output)
        return SIP;
    }
  }
  assert(false && "Stream I/O should be in pairs!");
}

std::vector<OutputPort*> ComputeBody::GetOutPorts() {
  std::vector<OutputPort*> Res;
  for (auto Elem : Parent->Entries) {
    if (auto OP = dyn_cast<OutputPort>(Elem)) {
      std::queue<Value*> Q;
      std::set<Value*> Visited;
      Q.push(OP->Output);
      Visited.insert(OP->Output);
      while (!Q.empty()) {
        auto Cur = Q.front(); Q.pop();
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

bool DfgEntry::ShouldUnroll() {
  if (Parent->getUnroll() <= 1)
      return false;
  if (!IsInMajor())
    return false;
  return true;
}

bool ComputeBody::ShouldUnroll() {
  if (!DfgEntry::ShouldUnroll())
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

bool Accumulator::ShouldUnroll() {
  return false;
}

bool CtrlSignal::ShouldUnroll() {
  return false;
}

bool PortMem::ShouldUnroll() {
  if (!DfgEntry::ShouldUnroll())
    return false;
  if (auto DD = dyn_cast<DedicatedDfg>(Parent))
    return !DD->InnerMost()->isLoopInvariant(Store->getPointerOperand());
  return false;
}

bool MemPort::ShouldUnroll() {
  if (!DfgEntry::ShouldUnroll())
    return false;
  if (auto DD = dyn_cast<DedicatedDfg>(Parent))
    return !DD->InnerMost()->isLoopInvariant(Load->getPointerOperand());
  return false;
}

bool IndMemPort::ShouldUnroll() {
  if (!DfgEntry::ShouldUnroll())
    return false;
  if (auto DD = dyn_cast<DedicatedDfg>(Parent))
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

void InputPort::EmitInPort(std::ostringstream &os) {

  if (!Parent->Parent->Query->MF.PRED) {
    bool OnlyPredicate{true};
    for (auto User : UnderlyingInst()->users()) {
      auto Entry = Parent->InThisDFG(User);
      if (Entry && !isa<Predicate>(Entry)) {
        OnlyPredicate = false;
        break;
      }
    }
    if (OnlyPredicate) {
      return;
    }
  }

  // FIXME: We need also inspect all the consumers to make sure that
  //        this indirect memory is not used by other instructions.
  if (auto IMP = dyn_cast<IndMemPort>(this)) {
    if (IMP->duplicated()) {
      return;
    }
  }

  if (!HasOtherUser(this, UnderlyingInst())) {
    return;
  }

  os << "# From Inst: " << dump() << "\n";
  std::ostringstream oss;
  Meta.to_pragma(oss);
  os << oss.str();

  os << "Input" << PortWidth() << ": " << NameInDfg();
  if (ShouldUnroll())
    os << "[" << Parent->getUnroll() << "]";
  os << "\n";
}

void InputConst::EmitInPort(std::ostringstream &os) {
  if (!HasOtherUser(this, Val)) {
    return;
  }
  os << "# " << dump() << "\n";
  os << "Input" << PortWidth() << ": " << NameInDfg() << "\n";
}

int DfgEntry::Index() {
  assert(ID != -1);
  return ID;
}

void DfgEntry::dump(std::ostringstream &os) {
  os << "[" << (void*) this << "] " << KindStr[Kind] << " (" << (void*) getPredicate() << ")";
  if (UnderlyingInst()) {
    std::string res;
    raw_string_ostream oss(res);
    oss << *UnderlyingInst();
    os << oss.str();
  } else {
    os << "\n";
  }
}

bool DfgEntry::OperandReady(std::set<Value*> &Ready) {
  auto Inst = UnderlyingInst();
  for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
    auto InstOperand = Inst->getOperand(i);
      auto Entry = Parent->InThisDFG(InstOperand);
      if (!Entry) {
        continue;
      }
      // A self-control port is allowed...
      if (isa<InputPort>(Entry) && Entry->getPredicate() == this)
        Ready.insert(InstOperand);
      if (Ready.find(InstOperand) == Ready.end())
        return false;
  }
  auto Pred = getPredicate();
  if (!Pred)
    return true;
  return Ready.count(Pred->UnderlyingInst());
}

bool Accumulator::OperandReady(std::set<Value*> &Ready) {
  auto Inst = UnderlyingInst();
  for (size_t i = 0; i < Inst->getNumOperands(); ++i) {
    if (isa<PHINode>(Inst->getOperand(i)))
        continue;
    if (Ready.find(Inst->getOperand(i)) == Ready.end())
      return false;
  }
  return true;
}

bool PortBase::OperandReady(std::set<Value*> &Ready) {
  return true;
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
          auto DD = dyn_cast<DedicatedDfg>(Parent);
          assert(DD);
          for (size_t k = 0; k < DD->LoopNest.size(); ++k) {
            if (DD->LoopNest[k]->getBlocksSet().count(IB)) {
              return DD->ProdTripCount(k, DD->Preheader->getFirstNonPHI()->getNextNode());
            }
          }
          return DD->ProdTripCount(DD->LoopNest.size(),
                                   DD->Preheader->getFirstNonPHI()->getNextNode());
        }
      }
    }
  }
  assert(false);
  return nullptr;
}

int MemPort::FillMode() {
  if (auto DD = dyn_cast<DedicatedDfg>(Parent)) {
    if (Parent->getUnroll() <= 1)
      return DP_NoPadding;
    return DD->ConsumedByAccumulator(this) ? DP_PostStrideZero : DP_PostStridePredOff;
  }
  return DP_NoPadding;
}

IndMemPort::IndMemPort(DfgBase *Parent_, LoadInst *Index_, LoadInst *Load) : InputPort(Parent_),
  Load(Load) {
  Index = new MemPort(Parent, Index_);
  Kind = kIndMemPort;
}

Instruction *IndMemPort::UnderlyingInst() {
  return Load;
}

std::string getOperationStr(Instruction *Inst, bool isAcc, bool predicated) {
  std::string OpStr;
  int BitWidth = Inst->getType()->getScalarSizeInBits();

  if (auto Cmp = dyn_cast<CmpInst>(Inst)) {
    // TODO: Support floating point
    OpStr = "compare";
    BitWidth = Cmp->getOperand(0)->getType()->getScalarSizeInBits();
  } else if (auto Call = dyn_cast<CallInst>(Inst)) {
    assert(Call);
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
    //TODO: Support more data types
    double FPV = CFP->getValueAPF().convertToDouble();
    uint64_t *RI = reinterpret_cast<uint64_t*>(&FPV);
    return formatv("{0}", *RI);
  }

  Val->dump();
  assert(0 && "The value requested not found!");
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

  void addControlledMemoryStream(int Idx, DfgEntry *DE) {
    if (auto CMP = dyn_cast<CtrlMemPort>(DE)) {
       if (Pred == nullptr) {
         Pred = CMP->Pred;
       } else {
         assert(Pred == CMP->Pred &&
                "An instruction cannot be controlled by more than one predication.");
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
        if (!Ctrl.str().empty()) Ctrl << ", ";
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

  if (!Parent->Parent->Query->MF.PRED) {
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
  os << NameInDfg(-1) << " = Compare" << Cond[0]->getOperand(0)->getType()->getScalarSizeInBits()
     << "(";
  for (size_t i = 0; i < Cond[0]->getNumOperands(); ++i) {
    auto Val = Cond[0]->getOperand(i);
    if (i) os << ", ";
    if (auto EntryOp = Parent->InThisDFG(Val)) {
      os << EntryOp->NameInDfg(-1);
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
      os << ", ctrl=" << CtrlBit.Pred->NameInDfg(-1);
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
    os << "Output" << UnderlyingInst()->getType()->getScalarSizeInBits() << ": " << NameInDfg();
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

void ComputeBody::EmitCB(std::ostringstream &os) {

  // If this ComputeBody is handled by a atomic operation skip it!
  if (isAtomic())
    return;

  os << "# " << dump() << "\n";

  for (int vec = 0; vec < (ShouldUnroll() ? Parent->getUnroll() : 1); ++vec) {
    os << NameInDfg(vec) << " = " << getOperationStr(Operation, false, false) << "(";
    ControlBit CtrlBit;

    if (auto Call = dyn_cast<CallInst>(Operation)) {
      for (size_t i = 0; i < Call->getNumArgOperands(); ++i) {
        auto Val = Call->getArgOperand(i);
        if (i) os << ", ";
        if (auto EntryOp = Parent->InThisDFG(Val)) {
          os << EntryOp->NameInDfg(vec);
          CtrlBit.addControlledMemoryStream(i, EntryOp);
        } else {
          os << ValueToOperandText(Val);
        }
      }
    } else {
      for (size_t i = 0; i < Operation->getNumOperands(); ++i) {
        auto Val = Operation->getOperand(i);
        if (i) os << ", ";
        if (auto EntryOp = Parent->InThisDFG(Val)) {
          os << EntryOp->NameInDfg(vec);
          CtrlBit.addControlledMemoryStream(i, EntryOp);
        } else {
          os << ValueToOperandText(Val);
        }
      }
    }

    if (Parent->Parent->Query->MF.PRED) {
      if (getPredicate())
        CtrlBit.updateAbstain(getAbstainBit(), false);
      if (!CtrlBit.empty()) {
        os << ", ctrl=" << CtrlBit.Pred->NameInDfg(vec) << "{" << CtrlBit.finalize() << "}";
      }
    }

    os << ")\n";
  }
}

void Accumulator::EmitCB(std::ostringstream &os) {
  os << "# " << dump() << "\n";

  auto Inst = Operation;
  std::queue<std::string> Q;
  auto Reduce = getOperationStr(Inst, false, false);
  ControlBit CtrlBit;

  for (int vec = 0; vec < Parent->getUnroll(); ++vec) {
    for (size_t j = 0; j < 2; ++j) {
      auto Operand = Inst->getOperand(j);
      if (!isa<PHINode>(Operand)) {
        auto Entry = Parent->InThisDFG(Operand);
        assert(Entry);
        Q.push(Entry->NameInDfg(vec));
      }
    }
  }

  int &TempCnt = Parent->Parent->TempCnt;
  while (Q.size() > 1) {
    auto A = Q.front(); Q.pop(); assert(!Q.empty());
    auto B = Q.front(); Q.pop();
    os << formatv("TMP{0} = {1}({2}, {3})", TempCnt, Reduce, A, B).str() << "\n";
    Q.push(formatv("TMP{0}", TempCnt++));
  }

  auto P = getPredicate();
  os << NameInDfg() << " = " << getOperationStr(Inst, true, P != nullptr) << "(" << Q.front()
     << ", ";

  if (Parent->Parent->Query->MF.PRED) {
    if (P || !CtrlBit.empty()) {
      CtrlBit.updateAbstain(this->getAbstainBit(), true);
      os << "ctrl=" << P->NameInDfg(-1) << "{" << CtrlBit.finalize() << "}";
    } else {
      os << Ctrl->NameInDfg();
    }
  } else {
    os << "ctrl=" << Ctrl->NameInDfg() << "{2:d}";
  }

  os << ")\n";
}

void OutputPort::EmitOutPort(std::ostringstream &os) {
  os << "# From Inst: " << dump() << "\n";
  std::ostringstream oss;
  Meta.to_pragma(oss);
  os << oss.str();
  auto Entry = Parent->InThisDFG(Output);
  assert(Entry);
  os << "Output" << PortWidth() << ": " << Entry->NameInDfg();
  if (Entry->ShouldUnroll())
    os << "[" << Parent->getUnroll() << "]";
  os << "\n";
}

void CtrlSignal::EmitInPort(std::ostringstream &os) {
  if (!Controlled->getPredicate() || !Parent->Parent->Query->MF.PRED) {
    os << "# [Control Signal]" << Controlled->dump() << "\n";
    os << "Input: " << NameInDfg() << "\n";
  }
}

Predicate::Predicate(DfgBase *Parent_, Instruction *Cond_) :
  DfgEntry(Parent_), Cond{Cond_}, Reversed{false} {
  Kind = kPredicate;
}

bool Predicate::ShouldUnroll() {
  return false;
}

Instruction *Predicate::UnderlyingInst() {
  return Cond[0];
}

int TBits(int Bits) {
  switch (Bits) {
  case 64: return 0;
  case 32: return 1;
  case 16: return 2;
  case 8: return 3;
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

void IndMemPort::InjectStreamIntrinsic(IRBuilder<> *IB) {
  if (IntrinInjected)
    return;

  auto &Ctx = Parent->getCtx();
  auto VoidTy = Type::getVoidTy(Ctx);

  if (!Parent->Parent->Query->MF.IND) {
    createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r, r, i",
                       {Load, createConstant(Ctx, 1), createConstant(Ctx, SoftPortNum)},
                       Load->getNextNode());
    IntrinInjected = true;
    Meta.set("src", "memory");
    Meta.set("cmd", "0.1");
    return;
  }

  if (duplicated()) {
    IntrinInjected = true;
    return;
  }

  std::vector<IndMemPort*> Together;
  std::vector<int> INDs;

  for (auto &IMP1 : Parent->EntryFilter<IndMemPort>()) {
    if (IMP1->IntrinInjected)
      continue;
    if (this->Index->Load == IMP1->Index->Load) {
      Together.push_back(IMP1);
      INDs.push_back(Parent->getNextIND());
    }
  }

  assert(Together[0] == this);

  for (size_t i = 1; i < Together.size(); ++i) {
    createAssembleCall(VoidTy, "ss_add_port zero, zero, $0", "i",
                       {createConstant(Ctx, INDs[i])}, Parent->DefaultIP());
  }

  auto Index = this->Index->Load->getPointerOperand();
  auto Analyzed = Parent->AnalyzeDataStream(
    Index, this->Index->Load->getType()->getScalarSizeInBits() / 8);
  Parent->InjectRepeat(Analyzed.AR, nullptr, this->SoftPortNum);
  auto ActualSrc = dsa::inject::InjectLinearStream(IB, INDs[0], Analyzed, DMO_Read, DP_NoPadding, DMT_DMA,
                                                   this->Index->Load->getType()->getScalarSizeInBits() / 8);

  for (size_t i = 0; i < Together.size(); ++i) {
    auto Cur = Together[i];
    int IBits = Cur->Index->Load->getType()->getScalarSizeInBits();
    int DBits = Cur->UnderlyingInst()->getType()->getScalarSizeInBits();

    auto TImm = createConstant(Ctx, (1 << 4) | (TBits(IBits) << 2) | TBits(DBits));
    createAssembleCall(VoidTy, "ss_cfg_ind $0, $1, $2", "r,r,i",
                       {createConstant(Ctx, 0), createConstant(Ctx, DBits / 8), TImm},
                       Parent->DefaultIP());

    auto Num = IB->CreateUDiv(Analyzed.BytesFromMemory(IB),
                              createConstant(Ctx, IBits / 8));
    auto PortImm = createConstant(Ctx, (Cur->SoftPortNum << 5) | INDs[i]);
    auto GEP = dyn_cast<GetElementPtrInst>(Cur->Load->getPointerOperand());
    createAssembleCall(VoidTy, "ss_ind $0, $1, $2", "r,r,i",
                       {GEP->getOperand(0), Num, PortImm}, Parent->DefaultIP());
    // TODO: Support indirect read on the SPAD(?)
    Cur->Meta.set("src", dsa::dfg::MetaPort::DataText[(int) ActualSrc]);
    Cur->Meta.set("dest", "memory");
    Cur->Meta.set("op", "indread");

    Cur->IntrinInjected = true;
  }

  IntrinInjected = true;
}

bool MemPort::InjectUpdateStream(IRBuilder<> *IB) {
  if (!Parent->Parent->Query->MF.REC)
    return false;

  if (!IsInMajor())
    return false;

  // Wrappers
  auto DFG = dyn_cast<DedicatedDfg>(Parent);

  if (!DFG)
    return false;

  // Wrappers
  auto MP = this;

  IB->SetInsertPoint(Parent->DefaultIP());

  LLVM_DEBUG(dbgs() << "Injecting update streams!\n");

  for (auto &PM : DFG->EntryFilter<PortMem>()) {
    if (!PM->IsInMajor() || PM->IntrinInjected)
      continue;
    auto Ptr0 = dyn_cast<Instruction>(MP->Load->getPointerOperand());
    auto Ptr1 = dyn_cast<Instruction>(PM->Store->getPointerOperand());
    LLVM_DEBUG(MP->Load->dump(); PM->Store->dump());
    if (Ptr0 == Ptr1) {
      LLVM_DEBUG(
        dbgs() << "A stream update detected!\n");
      auto Analyzed = DFG->AnalyzeDataStream(
        Ptr0, MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);
      /* This portion of code is deprecated. I guess this is because LLVM's SCEV behaviour
       * changed.
       * for (int i = 0; i < n; ++i)
       *   for (int j = 0; j < m ++j)
       *      // use a[j];
       * i's n trip count used to be put in outer repeat.
       * After adopting new version of LLVM, it seems to be a zero-step AddRecur now.
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
        if (auto Step = dyn_cast<ConstantInt>(std::get<0>(Analyzed.Dimensions[i]))) {
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
      dsa::inject::InjectLinearStream(Parent->Parent->Query->IBPtr, MP->SoftPortNum, Analyzed,
                                      DMO_Write, DP_NoPadding, DMT_DMA,
                                      MP->Load->getType()->getScalarSizeInBits() / 8);

      /// {
      auto MinusOne = IB->CreateSub(RepeatTime, IB->getInt64(1));
      auto NumElements = IB->CreateUDiv(Analyzed.BytesFromMemory(IB),
                                        IB->getInt64(PM->PortWidth() / 8));
      auto Recurrenced = IB->CreateMul(MinusOne, NumElements);
      /// }

      LLVM_DEBUG(dbgs() << "Inject a initial stream!\n");
      dsa::inject::DSAIntrinsicEmitter DIE(IB);
      DIE.SS_RECURRENCE(PM->SoftPortNum, MP->SoftPortNum, Recurrenced,
                        MP->Load->getType()->getScalarSizeInBits() / 8);
      int II = 1;
      int Conc = -1;
      if (auto CI = dyn_cast<ConstantInt>(std::get<1>(Analyzed.Dimensions.back()))) {
        auto CII = CI->getZExtValue();
        int CanHide = CII * 8 / PortWidth();
        if (PM->Latency - CanHide > 0) {
          II = PM->Latency - CanHide;
          LLVM_DEBUG(dbgs() << "Recur II: " << II << "\n");
        } else {
          II = 1;
          errs() << "[Warning] To hide the latency " << PM->Latency << ", " << CII * 8 / PortWidth()
                 << " elements are active\n";
          errs() << "This requires a " << CanHide - PM->Latency << "-deep FIFO buffer\n";
        }
        Conc = CII;
      } else {
        errs() << "[Warning] To hide the latency " << PM->Latency
               << ", make sure your variable recur distance will not overwhlem the FIFO buffer!";
      }
      PM->Meta.set("dest", "localport");
      PM->Meta.set("dest", MP->NameInDfg());
      {
        std::ostringstream oss;
        oss << Conc * 8 / PortWidth();
        PM->Meta.set("conc", oss.str());
      }
      dsa::inject::InjectLinearStream(IB, PM->SoftPortNum, Analyzed,
                                      DMO_Write, DP_NoPadding, DMT_DMA,
                                      PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8);
      PM->IntrinInjected = MP->IntrinInjected = true;
      return true;
    }
  }

  return false;

}

void MemPort::InjectStreamIntrinsic(IRBuilder<> *IB) {
  if (IntrinInjected)
    return;

  if (!HasOtherUser(this, UnderlyingInst()) && !isa<DataMoveDfg>(Parent)) {
    IntrinInjected = true;
    return;
  }

  if (InjectUpdateStream(IB)) {
    return;
  }

  // Wrappers
  auto MP = this;
  auto DFG = this->Parent;

  LLVM_DEBUG(dbgs() << "Analyzing "; MP->Load->dump());

  // Handle data stream with predicate
  if (MP->getPredicate()) {
    assert(false && "Predicated stream should be handled in CtrlMemPort.");
  }

  auto Analyzed = DFG->AnalyzeDataStream(
    MP->Load->getPointerOperand(),
    MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);

  if (Analyzed.Dimensions.empty()) {
    DFG->InjectRepeat(Analyzed.AR, MP->Load, MP->SoftPortNum);
  } else {

    auto Fill = MP->FillMode();
    DFG->InjectRepeat(Analyzed.AR, nullptr, this->SoftPortNum);
    auto Src =
      dsa::inject::InjectLinearStream(IB, MP->SoftPortNum, Analyzed, DMO_Read, (Padding) Fill, DMT_DMA,
                                      MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);
    Meta.set("src", dsa::dfg::MetaPort::DataText[(int) Src]);
    Meta.set("op", "read");
  }


  IntrinInjected = true;
}

void PortMem::InjectStreamIntrinsic(IRBuilder<> *IB) {
  auto PM = this;
  auto DFG = Parent;
  if (PM->IntrinInjected)
    return;
  IB->SetInsertPoint(Parent->DefaultIP());
  LLVM_DEBUG(dbgs() << "Injecting intrin for PM: "; PM->UnderlyingInst()->dump());
  int Bytes = PM->Store->getValueOperand()->getType()->getScalarType()->getScalarSizeInBits() / 8;
  auto Analyzed = DFG->AnalyzeDataStream(PM->Store->getPointerOperand(), Bytes);
  if (!Analyzed.Dimensions.empty()) {
    auto Dst = dsa::inject::InjectLinearStream(
      IB, PM->SoftPortNum, Analyzed, DMO_Write, DP_NoPadding, DMT_DMA, Bytes);
    Meta.set("op", "write");
    Meta.set("dest", dsa::dfg::MetaPort::DataText[(int) Dst]);
  } else {

    auto &Ctx = Parent->getCtx();
    auto VoidTy = Type::getVoidTy(Ctx);
    int VBtyes = PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8;
    auto Intrin = createAssembleCall(VoidTy, "ss_wr_dma $0, $1, $2", "r,r,i",
                       {PM->Store->getPointerOperand(),
                       IB->getInt64(VBtyes),
                       IB->getInt64(PM->SoftPortNum << 1)},
                       PM->Store);
    Parent->InjectedCode.push_back(Intrin);
    //auto FromCGRA = createAssembleCall(PM->Store->getValueOperand()->getType(),
    //                                   "ss_recv $0, zero, $1", "=r,i",
    //                                   {createConstant(Parent->getCtx(), PM->SoftPortNum)},
    //                                   DFG->DefaultIP());
    //auto ValueInst = dyn_cast<Instruction>(PM->Store->getValueOperand());
    //assert(ValueInst);
    //ValueInst->replaceAllUsesWith(FromCGRA);
  }

  PM->IntrinInjected = true;
}

void InputConst::InjectStreamIntrinsic(IRBuilder<> *IB) {

  if (auto DD = dyn_cast<DedicatedDfg>(Parent)) {
    auto Analyzed = DD->AnalyzeDataStream(this->Val, Val->getType()->getScalarSizeInBits() / 8,
                                          true, Parent->DefaultIP());
    /// FIXME: Will this cause other problem?
    DD->InjectRepeat(Analyzed.AR, Val, SoftPortNum);
    //DD->InjectRepeat(DD->TripCount(0, DD->DefaultIP()),
    //                 DD->ProdTripCount(1, DD->LoopNest.size(), Parent->DefaultIP()), 0,
    //                 Val, SoftPortNum);
  } else {
    assert(isa<TemporalDfg>(Parent));
    Parent->InjectRepeat(IB->getInt64(1), IB->getInt64(1),
                         0, Val, SoftPortNum);
  }

  IntrinInjected = true;
}

void CtrlSignal::InjectStreamIntrinsic(IRBuilder<> *IB) {
  auto CS = this;
  auto DD = dyn_cast<DedicatedDfg>(Parent);
  assert(DD);
  auto InsertBefore = DD->DefaultIP();
  auto One = IB->getInt64(1);
  auto Two = IB->getInt64(2);

  dsa::inject::DSAIntrinsicEmitter DIE(IB);


  if (CS->Controlled->getPredicate()) {
    if (Parent->Parent->Query->MF.PRED) {
      CS->IntrinInjected = true;
      LLVM_DEBUG(dbgs() << "Skipped:"; CS->dump());
    } else {
      DIE.SS_CONST(SoftPortNum, Two, One, Two->getType()->getScalarSizeInBits() / 8);
      DIE.SS_CONST(SoftPortNum, One, One, Two->getType()->getScalarSizeInBits() / 8);
    }
    IntrinInjected = true;
    return;
  }


  assert(!CS->IntrinInjected);
  auto CR = CS->Controlled->NumValuesProduced();
  assert(CR);

  /// {
  auto Iters = IB->CreateUDiv(DD->ProdTripCount(DD->LoopNest.size(), InsertBefore),
                              CR, "const.iters");
  auto Unroll = IB->getInt64(DD->UnrollFactor);
  auto Ceil = CeilDiv(CR, Unroll, InsertBefore);
  auto RepeatTwo = IB->CreateSub(Ceil, One, "repeat.two", InsertBefore);
  DIE.SS_2D_CONST(CS->SoftPortNum, Two, RepeatTwo, One, One, Iters,
                  Two->getType()->getScalarSizeInBits() / 8);
  /// }

  CS->IntrinInjected = true;
}

void CtrlMemPort::InjectStreamIntrinsic(IRBuilder<> *IB) {

  auto &Ctx = Parent->getCtx();
  auto CMP = this;
  auto VoidTy = Type::getVoidTy(Ctx);
  auto One = createConstant(Ctx, 1);
  auto Zero = createConstant(Ctx, 0);

  if (!Parent->Parent->Query->MF.PRED) {
    // PortNum == -1 indicates this port is omitted because of no predication support
    if (CMP->SoftPortNum != -1) {
      createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
                         {CMP->Load, One, createConstant(Ctx, CMP->SoftPortNum)},
                         Load->getNextNode());
      auto DD = dyn_cast<DedicatedDfg>(Parent);
      assert(DD && "This node only exists in stream DFGs");
      createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
                         {Zero, One, createConstant(Ctx, SoftPortNum)},
                         DD->PrologueIP);
    }
    IntrinInjected = true;
    return;
  }

  IB->SetInsertPoint(Parent->DefaultIP());
  auto Port = createConstant(Ctx, CMP->SoftPortNum << 1);
  int Bits = CMP->Load->getType()->getScalarSizeInBits();
  auto ScalarBytes = createConstant(Ctx, Bits / 8,
                                    CMP->TripCnt->getType()->getScalarSizeInBits());
  auto Bytes = IB->CreateMul(CMP->TripCnt, ScalarBytes);

  // This is a little bit zig-zag here:
  // If this stream is for the predicate, we require users to put sentinal at the end the next
  // word of the array.
  if (CMP->ForPredicate)
    Bytes = IB->CreateAdd(Bytes, ScalarBytes);

  // TODO: Support putting the join stream onto the SPAD
  createAssembleCall(VoidTy, "ss_dma_rd $0, $1, $2", "r,r,i", {CMP->Start, Bytes, Port},
                     Parent->DefaultIP());
  Meta.set("op", "read");
  Meta.set("src", "memory");

  // If this stream is NOT for the predicate, we pad two zero values to produce the final result.
  if (!CMP->ForPredicate) {
    createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
                       {createConstant(Ctx, 0), One,
                        createConstant(Ctx, CMP->SoftPortNum)}, Parent->DefaultIP());
  }

  // This is kinda ad-hoc, because we current do not support a runtime-determined length stream.
  // This assumption does not work on that case.

  //FIXME: Automatically inject sentinal tail
  //if (CMP->ForPredicate) {
  //  auto Sentinal = createConstant(getCtx(), 1ull << (Bits - 1), Bits);
  //  createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
  //                     {Sentinal, One, createConstant(getCtx(), CMP->SoftPortNum)},
  //                     DFG->DefaultIP());
  //} else {
  //  createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
  //                     {createConstant(getCtx(), 0), One,
  //                     createConstant(getCtx(), CMP->SoftPortNum)},
  //                     DFG->DefaultIP());
  //}

  CMP->IntrinInjected = true;
}

void OutputPort::InjectStreamIntrinsic(IRBuilder<> *IB) {
  auto OP = this;
  dsa::inject::DSAIntrinsicEmitter DIE(IB);
  DIE.SS_RECV(OP->SoftPortNum, OP->Output->getType()->getScalarSizeInBits() / 8);
  auto Recv = IB->CreateBitCast(DIE.res[0], OP->Output->getType());
  std::set<Instruction*> Equiv;
  FindEquivPHIs(OP->Output, Equiv);
  for (auto Iter : Equiv) {
    Iter->replaceAllUsesWith(Recv);
  }
  OP->IntrinInjected = true;
}

void StreamOutPort::InjectStreamIntrinsic(IRBuilder<> *IB) {
  auto SOP = this;

  LLVM_DEBUG(dbgs() << "StreamOut: "; SOP->Output->dump());
  auto SIP = SOP->FindConsumer();
  assert(!SOP->IntrinInjected && !SIP->IntrinInjected);
  dsa::inject::DSAIntrinsicEmitter DIE(IB);
  if (auto DD = dyn_cast<DedicatedDfg>(SIP->Parent)) {
    int Bytes = SOP->Output->getType()->getScalarType()->getScalarSizeInBits() / 8;
    auto Analyzed = DD->AnalyzeDataStream(SOP->Output, Bytes, true, Parent->DefaultIP());
    /// FIXME: Will this cause other problem?
    DD->InjectRepeat(Analyzed.AR, nullptr, SIP->SoftPortNum);
    assert(Analyzed.OuterRepeat);
    assert(IB);
    DIE.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, Analyzed.OuterRepeat,
                      SOP->Output->getType()->getScalarSizeInBits() / 8);
  } else if (isa<TemporalDfg>(SIP->Parent)) {
    // TODO: Support temporal stream
    DIE.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, IB->getInt64(1),
                      SOP->Output->getType()->getScalarSizeInBits() / 8);
  }
  SOP->IntrinInjected = SIP->IntrinInjected = true;
}

AtomicPortMem::AtomicPortMem(DfgBase *Parent_, LoadInst *Index_, StoreInst *Store_,
                             int OpCode_, Instruction *Op_, Value *Operand_) :
  OutputPort(Parent_, Store_->getValueOperand()), Index(new MemPort(Parent_, Index_)),
  Store(Store_), OpCode(OpCode_), Op(Op_), Operand(Operand_) {

  Kind = kAtomicPortMem;

  if (OpCode == 0) {
    assert(Operand);
  }
}

Instruction *AtomicPortMem::UnderlyingInst() {
  return Store;
}

void AtomicPortMem::InjectStreamIntrinsic(IRBuilder<> *IB) {
  if (!Parent->Parent->Query->MF.IND) {
    if (auto DfgEntry = Parent->InThisDFG(Operand)) {
      assert(false && "TODO: ss_recv operand from port!");
      (void) DfgEntry;
    } else {
      (void) DfgEntry;
    }
    IntrinInjected = true;
    Meta.set("cmd", "0.1");
    return;
  }
  // TODO: Support OpCode() == 3.
  assert(OpCode == 0);

  SoftPortNum = Parent->getNextIND();

  auto Index = this->Index->Load->getPointerOperand();
  auto Analyzed = Parent->AnalyzeDataStream(
    Index, this->Index->Load->getType()->getScalarSizeInBits() / 8);
  Parent->InjectRepeat(Analyzed.AR, nullptr, SoftPortNum);
  auto ActualSrc =
    dsa::inject::InjectLinearStream(IB, SoftPortNum, Analyzed, DMO_Read, DP_NoPadding, DMT_DMA,
                                    this->Index->Load->getType()->getScalarSizeInBits() / 8);
  int OperandPort = -1;
  auto DD = dyn_cast<DedicatedDfg>(Parent);
  assert(DD);
  // FIXME: Is trip count a temporary solution?
  auto TripCnt = DD->ProdTripCount(DD->LoopNest.size(), DD->DefaultIP());

  if (auto DfgEntry = Parent->InThisDFG(Operand)) {
    if (auto CB = dyn_cast<ComputeBody>(DfgEntry)) {
      assert(CB->isImmediateAtomic());
      OperandPort = CB->SoftPortNum;
    } else if (auto IP = dyn_cast<InputPort>(DfgEntry)) {
      OperandPort = IP->SoftPortNum;
    }
  } else {
    OperandPort = Parent->getNextReserved();
    uint64_t CI = stoul(ValueToOperandText(Operand));
    int DBits = this->Store->getValueOperand()->getType()->getScalarSizeInBits();
    createAssembleCall(IB->getVoidTy(), "ss_const $0, $1, $2", "r,r,i",
                       {IB->getInt64(CI), TripCnt,
                        IB->getInt64(OperandPort | ((TBits(DBits) + 1) << 9))},
                       Parent->DefaultIP());
  }

  int IBits = this->Index->Load->getType()->getScalarSizeInBits();
  int DBits = this->Store->getValueOperand()->getType()->getScalarSizeInBits();

  auto TImm = IB->getInt64((TBits(DBits) << 4) | (TBits(DBits) << 2) | TBits(IBits));
  auto NumUpdates = IB->getInt64(1);
  auto TupleLen = IB->getInt64(1);
  createAssembleCall(IB->getVoidTy(), "ss_cfg_atom_op $0, $1, $2", "r,r,i",
                     {TupleLen, NumUpdates, TImm},
                     Parent->DefaultIP());
  Meta.set("src", dsa::dfg::MetaPort::DataText[(int) ActualSrc]);
  Meta.set("dest", "spad");
  Meta.set("op", "atomic");
  // FIXME: offset is not always 0
  uint32_t OffsetList = 0;
  auto AddrPort = IB->getInt64(OffsetList | (SoftPortNum << 24));
  auto ValuePort = IB->getInt64((OperandPort << 2) | ((int) OpCode));
  createAssembleCall(IB->getVoidTy(), "ss_atom_op $0, $1, $2", "r,r,i",
                     {AddrPort, TripCnt, ValuePort},
                     Parent->DefaultIP());

  IntrinInjected = true;

}

std::vector<Instruction*> Predicate::UnderlyingInsts() {
  return std::vector<Instruction*>(Cond.data(), Cond.data() + Cond.size());
}

std::vector<Instruction*> IndMemPort::UnderlyingInsts() {
  return {Index->Load, Load};
}

std::vector<Instruction*> AtomicPortMem::UnderlyingInsts() {
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
