#include <queue>
#include <sstream>
#include "llvm/Support/FormatVariadic.h"
#include "llvm/IR/Dominators.h"

#include "Util.h"
#include "DFGEntry.h"
#include "Transformation.h"
#include "StreamAnalysis.h"

#define DEBUG_TYPE "stream-specialize"

using namespace llvm;

const char *KindStr[] = {
  "DFGEntry",

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

std::string DFGEntry::Name(int Idx) {
  if (Idx != -1 && ShouldUnroll()) {
    return formatv("sub{0}_v{1}_{2}", Parent->ID, ID, Idx);
  }
  return formatv("sub{0}_v{1}_", Parent->ID, ID);
}

PortBase::PortBase(DFGBase *Parent_) : DFGEntry(Parent_), SoftPortNum(-1), IntrinInjected(false) {
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

PortMem::PortMem(DFGBase *Parent_, StoreInst *Store_) :
  OutputPort(Parent_, Store_->getValueOperand()), Store(Store_) {
  Kind = kPortMem;
}

Accumulator::Accumulator(DFGBase *Parent_, Instruction *Operation_, CtrlSignal *Ctrl_) :
  ComputeBody(Parent_, Operation_), Ctrl(Ctrl_) {
  Kind = kAccumulator;
}

InputPort::InputPort(DFGBase *Parent_) :
  PortBase(Parent_) {
  Kind = kInputPort;
}

MemPort::MemPort(DFGBase *Parent_, LoadInst *Load_) : InputPort(Parent_), Load(Load_) {
  Kind = kMemPort;
}

ComputeBody::ComputeBody(DFGBase *Parent_, Instruction *Operation_) :
  DFGEntry(Parent_), Operation(Operation_) {
  assert(CanBeAEntry(Operation_));
  Kind = kComputeBody;
}

CtrlSignal::CtrlSignal(DFGBase *Parent_) : InputPort(Parent_) {
  Kind = kCtrlSignal;
}

CtrlMemPort::CtrlMemPort(DFGBase *Parent_, LoadInst *Load_, Value *Start_, Value *TripCnt_,
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

Instruction* DFGEntry::UnderlyingInst() {
  return nullptr;
}

Value* DFGEntry::UnderlyingValue() {
  return UnderlyingInst();
}

bool DFGEntry::IsInMajor() {
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

InputConst::InputConst(DFGBase *Parent_, Value *Val_) : InputPort(Parent_), Val(Val_) {
  Kind = kInputConst;
}

StreamInPort::StreamInPort(DFGBase *Parent_, Instruction *Inst) : InputPort(Parent_), DataFrom(Inst) {
  Kind = kStreamInPort;
}

StreamOutPort::StreamOutPort(DFGBase *Parent_, Instruction *Inst) : OutputPort(Parent_, Inst) {
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
  CHECK(false) << "Cannot find consumer for " << *UnderlyingInst();
  return nullptr;
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

bool Accumulator::ShouldUnroll() {
  return false;
}

bool CtrlSignal::ShouldUnroll() {
  return false;
}

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

bool DFGEntry::OperandReady(std::set<Value*> &Ready) {
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
          auto DD = dyn_cast<DedicatedDFG>(Parent);
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
  if (auto DD = dyn_cast<DedicatedDFG>(Parent)) {
    if (Parent->getUnroll() <= 1)
      return DP_NoPadding;
    return DD->ConsumedByAccumulator(this) ? DP_PostStrideZero : DP_PostStridePredOff;
  }
  return DP_NoPadding;
}

IndMemPort::IndMemPort(DFGBase *Parent_, LoadInst *Index_, LoadInst *Load) : InputPort(Parent_),
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
    //TODO: Support more data types
    double FPV = CFP->getValueAPF().convertToDouble();
    uint64_t *RI = reinterpret_cast<uint64_t*>(&FPV);
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
  os << Name(-1) << " = Compare" << Cond[0]->getOperand(0)->getType()->getScalarSizeInBits()
     << "(";
  for (size_t i = 0; i < Cond[0]->getNumOperands(); ++i) {
    auto Val = Cond[0]->getOperand(i);
    if (i) os << ", ";
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
    os << "Output" << UnderlyingInst()->getType()->getScalarSizeInBits() << ": " << Name();
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

Predicate::Predicate(DFGBase *Parent_, Instruction *Cond_) :
  DFGEntry(Parent_), Cond{Cond_}, Reversed{false} {
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

  if (!dsa::utils::ModuleContext().IND) {
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
      CHECK(IMP1->Index->SoftPortNum != -1);
      INDs.push_back(IMP1->Index->SoftPortNum);
    }
  }

  CHECK(Together[0] == this);

  dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);

  for (size_t i = 1; i < Together.size(); ++i) {
    DIE.SS_CONFIG_PORT(INDs[i], DPF_PortBroadcast, true);
  }

  auto Index = this->Index->Load->getPointerOperand();
  auto Analyzed = Parent->AnalyzeDataStream(
    Index, this->Index->Load->getType()->getScalarSizeInBits() / 8);
  Parent->InjectRepeat(Analyzed.AR, nullptr, this->SoftPortNum);
  auto ActualSrc = dsa::inject::InjectLinearStream(IB, Parent->Parent->Query->DSARegs,
                                                   this->Index->SoftPortNum, Analyzed,
                                                   DMO_Read, DP_NoPadding, DMT_DMA,
                                                   this->Index->Load->getType()->getScalarSizeInBits() / 8);

  for (size_t i = 0; i < Together.size(); ++i) {
    auto Cur = Together[i];
    int IBits = Cur->Index->Load->getType()->getScalarSizeInBits();
    int DBits = Cur->UnderlyingInst()->getType()->getScalarSizeInBits();
    auto Num = IB->CreateUDiv(Analyzed.BytesFromMemory(IB),
                              createConstant(Ctx, IBits / 8));
    auto GEP = dyn_cast<GetElementPtrInst>(Cur->Load->getPointerOperand());
    DIE.SS_INDIRECT_READ(this->SoftPortNum, this->IndexOutPort, GEP->getOperand(0),
                         Cur->Load->getType()->getScalarSizeInBits() / 8, Num, DMT_DMA);

    // TODO: Support indirect read on the SPAD(?)
    Cur->Meta.set("src", dsa::dfg::MetaPort::DataText[(int) ActualSrc]);
    Cur->Meta.set("dest", "memory");
    Cur->Meta.set("op", "indread");

    Cur->IntrinInjected = true;
  }

  IntrinInjected = true;
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
      dsa::inject::InjectLinearStream(Parent->Parent->Query->IBPtr, Parent->Parent->Query->DSARegs,
                                      MP->SoftPortNum, Analyzed,
                                      DMO_Read, DP_NoPadding, DMT_DMA,
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
      PM->Meta.set("dest", MP->Name());
      {
        std::ostringstream oss;
        oss << Conc * 8 / PortWidth();
        PM->Meta.set("conc", oss.str());
      }
      dsa::inject::InjectLinearStream(IB, Parent->Parent->Query->DSARegs,
                                      PM->SoftPortNum, Analyzed,
                                      DMO_Write, DP_NoPadding, DMT_DMA,
                                      PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8);
      PM->IntrinInjected = MP->IntrinInjected = true;
      return true;
    }
  }

  return false;

}

void InjectLinearStreamImpl(ScalarEvolution *SE, SCEVExpander &SEE, IRBuilder<> *IB,
                            const SCEV *Idx, std::vector<Loop*> LoopNest,
                            dsa::inject::RepeatInjector &RI,
                            dsa::inject::LinearInjector &LI,
                            int Port, int Unroll, int DType,
                            MemoryOperation MO, Padding Padding, MemoryType MT) {
  auto IdxLI = dsa::analysis::AnalyzeIndexExpr(SE, Idx, LoopNest);
  std::vector<dsa::analysis::LinearInfo*> LoopLI;
  for (int i = 0, N = LoopNest.size(); i < N; ++i) {
    auto CurDim = dsa::analysis::AnalyzeIndexExpr(SE, SE->getBackedgeTakenCount(LoopNest[i]), LoopNest);
    LoopLI.push_back(CurDim);
  }
  if (MO == MemoryOperation::DMO_Read) {
    RI.Inject(IdxLI, LoopLI, Port, Unroll);
  }
  LI.Inject(IdxLI, LoopLI, Port, MO, Padding, MT, DType);
}


void MemPort::InjectStreamIntrinsic(IRBuilder<> *IB) {
  IB->SetInsertPoint(this->Parent->DefaultIP());

  if (IntrinInjected)
    return;

  if (!HasOtherUser(this, UnderlyingInst())) {
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

  if (auto DD = dyn_cast<DedicatedDFG>(DFG)) {
    // FIXME(@were): Make this more unified.
    SCEVExpander SEE(*Parent->Parent->Query->SE,
                     Parent->Parent->Func.getParent()->getDataLayout(), "");
    SEE.setInsertPoint(Parent->DefaultIP());
    dsa::inject::RepeatInjector RI(IB, &SEE, Parent->Parent->Query->DSARegs);
    dsa::inject::LinearInjector LI(IB, &SEE, Parent->Parent->Query->DSARegs);
    std::vector<Loop*> LoopNest(DD->LoopNest.begin(), DD->LoopNest.end());
    auto SE = Parent->Parent->Query->SE;
    auto SCEVIdx = SE->getSCEV(MP->Load->getPointerOperand());
    int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
    InjectLinearStreamImpl(SE, SEE, IB, SCEVIdx, LoopNest, RI, LI, MP->SoftPortNum,
                           Parent->getUnroll(), DType, DMO_Read,
                           (Padding) MP->FillMode(), DMT_DMA);
    MP->IntrinInjected = true;
    return;
  }

  auto Analyzed = DFG->AnalyzeDataStream(
    MP->Load->getPointerOperand(),
    MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);

  if (Analyzed.Dimensions.empty()) {
    auto RepeatedConst = IB->CreateBitCast(
      IB->CreateLoad(MP->Load->getPointerOperand()), IB->getInt64Ty());
    DFG->InjectRepeat(Analyzed.AR, RepeatedConst, MP->SoftPortNum);
  } else {
    auto Fill = MP->FillMode();
    DFG->InjectRepeat(Analyzed.AR, nullptr, this->SoftPortNum);
    auto Src =
      dsa::inject::InjectLinearStream(IB, Parent->Parent->Query->DSARegs,
                                      MP->SoftPortNum, Analyzed, DMO_Read, (Padding) Fill, DMT_DMA,
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
  if (auto DD = dyn_cast<DedicatedDFG>(Parent)) {
    SCEVExpander SEE(*Parent->Parent->Query->SE,
                     Parent->Parent->Func.getParent()->getDataLayout(), "");
    SEE.setInsertPoint(Parent->DefaultIP());
    dsa::inject::RepeatInjector RI(IB, &SEE, Parent->Parent->Query->DSARegs);
    dsa::inject::LinearInjector LI(IB, &SEE, Parent->Parent->Query->DSARegs);
    std::vector<Loop*> LoopNest(DD->LoopNest.begin(), DD->LoopNest.end());
    auto SE = Parent->Parent->Query->SE;
    auto SCEVIdx = SE->getSCEV(PM->Store->getPointerOperand());
    int DType = PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8;
    InjectLinearStreamImpl(SE, SEE, IB, SCEVIdx, LoopNest, RI, LI, PM->SoftPortNum,
                           Parent->getUnroll(), DType, DMO_Write, DP_NoPadding, DMT_DMA);
    PM->IntrinInjected = true;
    return;
  }

  LLVM_DEBUG(dbgs() << "Injecting intrin for PM: "; PM->UnderlyingInst()->dump());
  int Bytes = PM->Store->getValueOperand()->getType()->getScalarType()->getScalarSizeInBits() / 8;
  auto Analyzed = DFG->AnalyzeDataStream(PM->Store->getPointerOperand(), Bytes);
  if (!Analyzed.Dimensions.empty()) {
    auto Dst = dsa::inject::InjectLinearStream(
      IB, Parent->Parent->Query->DSARegs, PM->SoftPortNum, Analyzed, DMO_Write, DP_NoPadding, DMT_DMA, Bytes);
    Meta.set("op", "write");
    Meta.set("dest", dsa::dfg::MetaPort::DataText[(int) Dst]);
  } else {
    dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);
    IB->SetInsertPoint(Store);
    DIE.INSTANTIATE_1D_STREAM(PM->Store->getPointerOperand(), /*length*/1,
                              PM->SoftPortNum, /*padding*/0, DSA_Access, DMO_Write, DMT_DMA,
                              /*signal*/0,
                              PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8,
                              0);
    auto Intrin = DIE.res.back();
    IB->SetInsertPoint(Parent->DefaultIP());
    //auto &Ctx = Parent->getCtx();
    //auto VoidTy = Type::getVoidTy(Ctx);
    //int VBtyes = PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8;
    //auto Intrin = createAssembleCall(VoidTy, "ss_wr_dma $0, $1, $2", "r,r,i",
    //                   {PM->Store->getPointerOperand(),
    //                   IB->getInt64(VBtyes),
    //                   IB->getInt64(PM->SoftPortNum << 1)},
    //                   PM->Store);
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

  if (auto DD = dyn_cast<DedicatedDFG>(Parent)) {
    auto Analyzed = DD->AnalyzeDataStream(this->Val, Val->getType()->getScalarSizeInBits() / 8,
                                          true, Parent->DefaultIP());
    /// FIXME: Will this cause other problem?
    DD->InjectRepeat(Analyzed.AR, Val, SoftPortNum);
    //DD->InjectRepeat(DD->TripCount(0, DD->DefaultIP()),
    //                 DD->ProdTripCount(1, DD->LoopNest.size(), Parent->DefaultIP()), 0,
    //                 Val, SoftPortNum);
  } else {
    assert(isa<TemporalDFG>(Parent));
    Parent->InjectRepeat(IB->getInt64(1), IB->getInt64(1),
                         0, Val, SoftPortNum);
  }

  IntrinInjected = true;
}

void CtrlSignal::InjectStreamIntrinsic(IRBuilder<> *IB) {
  auto CS = this;
  auto DD = dyn_cast<DedicatedDFG>(Parent);
  assert(DD);
  auto InsertBefore = DD->DefaultIP();
  auto One = IB->getInt64(1);
  auto Two = IB->getInt64(2);

  dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);

  if (CS->Controlled->getPredicate()) {
    if (dsa::utils::ModuleContext().PRED) {
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

  if (!dsa::utils::ModuleContext().PRED) {
    // PortNum == -1 indicates this port is omitted because of no predication support
    if (CMP->SoftPortNum != -1) {
      createAssembleCall(VoidTy, "ss_const $0, $1, $2", "r,r,i",
                         {CMP->Load, One, createConstant(Ctx, CMP->SoftPortNum)},
                         Load->getNextNode());
      auto DD = dyn_cast<DedicatedDFG>(Parent);
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
  dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);
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
  dsa::inject::DSAIntrinsicEmitter DIE(IB, Parent->Parent->Query->DSARegs);
  if (auto DD = dyn_cast<DedicatedDFG>(SIP->Parent)) {
    int Bytes = SOP->Output->getType()->getScalarType()->getScalarSizeInBits() / 8;
    auto Analyzed = DD->AnalyzeDataStream(SOP->Output, Bytes, true, Parent->DefaultIP());
    /// FIXME: Will this cause other problem?
    DD->InjectRepeat(Analyzed.AR, nullptr, SIP->SoftPortNum);
    assert(Analyzed.OuterRepeat);
    assert(IB);
    DIE.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, Analyzed.OuterRepeat,
                      SOP->Output->getType()->getScalarSizeInBits() / 8);
  } else if (isa<TemporalDFG>(SIP->Parent)) {
    // TODO: Support temporal stream
    DIE.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, IB->getInt64(1),
                      SOP->Output->getType()->getScalarSizeInBits() / 8);
  }
  SOP->IntrinInjected = SIP->IntrinInjected = true;
}

AtomicPortMem::AtomicPortMem(DFGBase *Parent_, LoadInst *Index_, StoreInst *Store_,
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
  if (!dsa::utils::ModuleContext().IND) {
    if (auto DFGEntry = Parent->InThisDFG(Operand)) {
      assert(false && "TODO: ss_recv operand from port!");
      (void) DFGEntry;
    } else {
      (void) DFGEntry;
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
    dsa::inject::InjectLinearStream(IB, Parent->Parent->Query->DSARegs,
                                    SoftPortNum, Analyzed, DMO_Read, DP_NoPadding, DMT_DMA,
                                    this->Index->Load->getType()->getScalarSizeInBits() / 8);
  int OperandPort = -1;
  auto DD = dyn_cast<DedicatedDFG>(Parent);
  assert(DD);
  // FIXME: Is trip count a temporary solution?
  auto TripCnt = DD->ProdTripCount(DD->LoopNest.size(), DD->DefaultIP());

  if (auto DFGEntry = Parent->InThisDFG(Operand)) {
    if (auto CB = dyn_cast<ComputeBody>(DFGEntry)) {
      assert(CB->isImmediateAtomic());
      OperandPort = CB->SoftPortNum;
    } else if (auto IP = dyn_cast<InputPort>(DFGEntry)) {
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

#define VISIT_IMPL(TYPE) void TYPE::Accept(dsa::DFGEntryVisitor *V) { V->Visit(this); }
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

void DFGEntryVisitor::Visit(DFGEntry *Node) { }
void DFGEntryVisitor::Visit(ComputeBody *Node) { Visit(static_cast<DFGEntry*>(Node)); }
void DFGEntryVisitor::Visit(Predicate *Node) { Visit(static_cast<DFGEntry*>(Node)); }
void DFGEntryVisitor::Visit(Accumulator *Node) { Visit(static_cast<ComputeBody*>(Node)); }
void DFGEntryVisitor::Visit(PortBase *Node) { Visit(static_cast<DFGEntry*>(Node)); }
void DFGEntryVisitor::Visit(InputPort *Node) { Visit(static_cast<PortBase*>(Node)); }
void DFGEntryVisitor::Visit(CtrlMemPort *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(MemPort *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(StreamInPort *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(CtrlSignal *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(InputConst *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(OutputPort *Node) { Visit(static_cast<PortBase*>(Node)); }
void DFGEntryVisitor::Visit(PortMem *Node) { Visit(static_cast<OutputPort*>(Node)); }
void DFGEntryVisitor::Visit(StreamOutPort *Node) { Visit(static_cast<OutputPort*>(Node)); }
void DFGEntryVisitor::Visit(IndMemPort *Node) { Visit(static_cast<InputPort*>(Node)); }
void DFGEntryVisitor::Visit(AtomicPortMem *Node) { Visit(static_cast<OutputPort*>(Node)); }

}