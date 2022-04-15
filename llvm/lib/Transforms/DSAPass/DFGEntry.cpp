#include "llvm/IR/Dominators.h"
#include "llvm/Support/FormatVariadic.h"
#include <queue>
#include <sstream>

#include "DFGEntry.h"
#include "DFGIR.h"
#include "StreamAnalysis.h"
#include "Util.h"

#define DEBUG_TYPE "stream-specialize"

using namespace llvm;

const char *KindStr[]= {
#define MACRO(X) #X
#include "./DFGKind.def"
#undef MACRO
};

DFGEntry::DFGEntry(DFGBase *Parent_) : Parent(Parent_) { // NOLINT
  ID = Parent_->Entries.size();
}

Predicate *DFGEntry::getPredicate(int *X) {
  auto *DT = Parent->Parent->Query->DT;

  if (!underlyingInst())
    return nullptr;
  // Sometimes, the CFG is too simple to have a immediate dom.
  if (auto *Inst = dyn_cast<Instruction>(underlyingInst())) {
    Predicate *Res = nullptr;
    for (size_t i = 0; i < Inst->getNumOperands(); ++i) { // NOLINT
      if (auto *Entry = Parent->InThisDFG(Inst->getOperand(i))) {
        if (Res == nullptr) {
          Res = Entry->getPredicate();
        } else {
          if (Entry->getPredicate()) {
            DSA_CHECK(Res == Entry->getPredicate());
          }
        }
      }
    }
    if (auto *DomNode = DT->getNode(Inst->getParent())->getIDom()) {
      auto &LastInst = DomNode->getBlock()->back();
      bool FindDom = false;
      for (auto *Elem : Parent->getBlocks()) {
        if (Elem == DomNode->getBlock()) {
          FindDom = true;
          break;
        }
      }
      if (!FindDom)
        return nullptr;
      if (auto *BI = dyn_cast<BranchInst>(&LastInst)) {
        if (BI->isConditional()) {
          auto *RawRes = Parent->InThisDFG(BI->getCondition());
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
  if (auto *Inst = underlyingInst()) {
    auto *DT = Parent->Parent->Query->DT;
    auto *CurrentBB = Inst->getParent();
    Predicate *Pred = nullptr;
    int Res = 7;
    while (true) {
      auto *DomNode = DT->getNode(CurrentBB)->getIDom();
      if (!DomNode)
        break;
      if (!Parent->Contains(DomNode->getBlock()))
        break;
      auto *DomBB = DomNode->getBlock();
      auto *BI = dyn_cast<BranchInst>(&DomBB->back());
      if (BI->isConditional()) {
        auto *Cond = BI->getCondition();
        if (Pred == nullptr) {
          Pred = dyn_cast<Predicate>(Parent->InThisDFG(Cond));
          assert(Pred);
        } else {
          assert(Pred == Parent->InThisDFG(Cond));
        }
        int SubRes = Pred->toCompareRes(dyn_cast<Instruction>(Cond),
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

std::string DFGEntry::name(int Idx) {
  return Parent->nameOf(underlyingValue(), Idx);
}

std::string OutputPort::name(int VecIdx) {
  auto *Entry = this;
  DSA_CHECK(Entry);
  auto Vs = Entry->underlyingValues();
  if (!isa<AtomicPortMem>(this)) {
    DSA_CHECK(Vs.size() == 1) << Vs.size() << ": " << dump();
  }
  std::ostringstream OSS;
  OSS << "sub" << Parent->ID << "_v" << Entry->ID << "_";
  if (VecIdx != -1 && Entry->shouldUnroll()) {
    OSS << VecIdx;
  }
  return OSS.str();
}

PortBase::PortBase(DFGBase *Parent_) // NOLINT
    : DFGEntry(Parent_), SoftPortNum(-1), IntrinInjected(false) {
  Kind = kPortBase;
  Meta.clear();
}

OutputPort::OutputPort(DFGBase *Parent_, Value *Value_) : PortBase(Parent_) { // NOLINT
  auto *Inst = dyn_cast<Instruction>(Value_);
  DSA_CHECK(Inst);

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
        LLVM_DEBUG(DSA_INFO << "incoming: "; Inst->dump());
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

PortMem::PortMem(DFGBase *Parent_, StoreInst *Store_) // NOLINT
    : OutputPort(Parent_, Store_->getValueOperand()), Store(Store_) {
  Kind = kPortMem;
}

Accumulator::Accumulator(DFGBase *Parent_, Instruction *Operation_) // NOLINT
  : ComputeBody(Parent_, Operation_) { // NOLINT
  Kind = kAccumulator;
}

InputPort::InputPort(DFGBase *Parent_) : PortBase(Parent_) { // NOLINT
  Kind = kInputPort;
}

MemPort::MemPort(DFGBase *Parent_, LoadInst *Load_) // NOLINT
    : InputPort(Parent_), Load(Load_) {
  Kind = kMemPort;
}

ComputeBody::ComputeBody(DFGBase *Parent_, Instruction *Operation_) // NOLINT
    : DFGEntry(Parent_), Operation(Operation_) {
  assert(CanBeAEntry(Operation_));
  Kind = kComputeBody;
}

CtrlMemPort::CtrlMemPort(DFGBase *Parent_, LoadInst *Load_, Value *Start_, // NOLINT
                         Value *TripCnt_, Predicate *Pred_, int Mask_) // NOLINT
    : InputPort(Parent_), Load(Load_), Start(Start_), TripCnt(TripCnt_),
      Pred(Pred_), Mask(Mask_) {
  Kind = kCtrlMemPort;
}

Predicate *CtrlMemPort::getPredicate(int *) { return Pred; }

Instruction *CtrlMemPort::underlyingInst() { return Load; }

int PortBase::portWidth() {
  return underlyingValue()->getType()->getScalarSizeInBits();
}

Instruction *DFGEntry::underlyingInst() { return nullptr; }

Value *DFGEntry::underlyingValue() { return underlyingInst(); }

bool DFGEntry::isInMajor() {
  auto Insts = underlyingInsts();
  if (Insts.empty()) {
    return false;
  }
  auto Blocks = Parent->getBlocks();
  for (auto *Elem : Insts) {
    Elem->getParent();
    auto Iter = std::find(Blocks.begin(), Blocks.end(), Elem->getParent());
    if (Iter != Blocks.end()) {
      return true;
    }
  }
  return false;
}

Instruction *ComputeBody::underlyingInst() { return Operation; }

Instruction *MemPort::underlyingInst() { return Load; }

Instruction *PortMem::underlyingInst() { return Store; }

std::vector<Instruction *> InputConst::underlyingInsts() {
  if (auto *Inst = dyn_cast<Instruction>(Val)) {
    return {Inst};
  }
  return {};
}

Instruction *InputConst::underlyingInst() { return dyn_cast<Instruction>(Val); }

std::vector<Value *> InputConst::underlyingValues() { return {Val}; }

Value *InputConst::underlyingValue() { return Val; }

InputConst::InputConst(DFGBase *Parent_, Value *Val_) // NOLINT
    : InputPort(Parent_), Val(Val_) {
  Kind = kInputConst;
}

StreamInPort::StreamInPort(DFGBase *Parent_, Instruction *Inst) // NOLINT
    : InputPort(Parent_), DataFrom(Inst) {
  Kind = kStreamInPort;
}

StreamOutPort::StreamOutPort(DFGBase *Parent_, Instruction *Inst) // NOLINT
    : OutputPort(Parent_, Inst) {
  Kind = kStreamOutPort;
}

Instruction *OutputPort::underlyingInst() { return Output; }

Instruction *StreamInPort::underlyingInst() { return DataFrom; }

int OutputPort::portWidth() { return Output->getType()->getScalarSizeInBits(); }

StreamInPort *StreamOutPort::findConsumer() {
  for (auto &DFG : Parent->Parent->DFGs) {
    if (DFG == Parent)
      continue;
    for (auto &SIP : DFG->EntryFilter<StreamInPort>()) {
      if (SIP->DataFrom == this->Output)
        return SIP;
    }
  }
  DSA_CHECK(false) << "Cannot find consumer for " << *underlyingInst();
  return nullptr;
}

std::vector<OutputPort *> ComputeBody::getOutPorts() {
  std::vector<OutputPort *> Res;
  for (auto *Elem : Parent->Entries) {
    if (auto *OP = dyn_cast<OutputPort>(Elem)) {
      std::queue<Value *> Q;
      std::set<Value *> Visited;
      Q.push(OP->Output);
      Visited.insert(OP->Output);
      while (!Q.empty()) {
        auto *Cur = Q.front();
        Q.pop();
        if (Cur == underlyingInst()) {
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

bool DFGEntry::shouldUnroll() {
  if (Parent->getUnroll() <= 1)
    return false;
  if (!isInMajor())
    return false;
  return true;
}

bool ComputeBody::shouldUnroll() {
  if (!DFGEntry::shouldUnroll())
    return false;
  auto *Inst = underlyingInst();
  for (size_t i = 0; i < Inst->getNumOperands(); ++i) { // NOLINT
    if (auto *Entry = Parent->InThisDFG(Inst->getOperand(i))) {
      if (Entry->shouldUnroll())
        return true;
    }
  }
  return false;
}

bool Accumulator::shouldUnroll() { return false; }

bool OutputPort::shouldUnroll() {
  if (!DFGEntry::shouldUnroll())
    return false;
  auto *OV = Parent->InThisDFG(Output);
  DSA_CHECK(OV);
  return OV->shouldUnroll();
}

bool MemPort::shouldUnroll() {
  if (!DFGEntry::shouldUnroll())
    return false;
  if (auto *DD = dyn_cast<DedicatedDFG>(Parent))
    return !DD->InnerMost()->isLoopInvariant(Load->getPointerOperand());
  return false;
}

bool IndMemPort::shouldUnroll() {
  if (!DFGEntry::shouldUnroll())
    return false;
  if (auto *DD = dyn_cast<DedicatedDFG>(Parent)) {
    return !DD->InnerMost()->isLoopInvariant(Index->Load->getPointerOperand());
  }
  return false;
}

bool HasOtherUser(InputPort *IP, Value *Val) { // NOLINT
  for (auto *User : Val->users()) {
    if (auto *Entry = IP->Parent->InThisDFG(User)) {
      if (auto *CB = dyn_cast<ComputeBody>(Entry)) {
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

int DFGEntry::index() {
  assert(ID != -1);
  return ID;
}

void DFGEntry::dump(std::ostringstream &OS) {
  OS << "[" << (void *)this << "] " << KindStr[Kind] << " ("
     << (void *)getPredicate() << ")";
  if (underlyingInst()) {
    std::string Res;
    raw_string_ostream OSS(Res);
    OSS << *underlyingInst();
    OS << OSS.str();
  } else {
    OS << "\n";
  }
}

int MemPort::fillMode() {
  if (auto *DD = dyn_cast<DedicatedDFG>(Parent)) {
    (void) DD;
    if (Parent->getUnroll() <= 1)
      return DP_NoPadding;
    return DP_PostStrideZero;
    // return DD->ConsumedByAccumulator(this) ? DP_PostStrideZero : DP_PostStridePredOff;
  }
  return DP_NoPadding;
}

IndMemPort::IndMemPort(DFGBase *Parent_, LoadInst *Index_, LoadInst *Load) // NOLINT
    : InputPort(Parent_), Load(Load) {
  Index = new MemPort(Parent, Index_);
  Kind = kIndMemPort;
}

Instruction *IndMemPort::underlyingInst() { return Load; }

std::string getOperationStr(Instruction *Inst, bool isAcc, bool predicated) { // NOLINT
  std::string OpStr;
  int BitWidth = Inst->getType()->getScalarSizeInBits();

  if (auto *Cmp = dyn_cast<CmpInst>(Inst)) {
    // TODO: Support floating point
    OpStr = "compare";
    BitWidth = Cmp->getOperand(0)->getType()->getScalarSizeInBits();
  } else if (auto *Call = dyn_cast<CallInst>(Inst)) {
    DSA_CHECK(Call);
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

  for (int i = 0, e = OpStr[0] == 'f' ? 2 : 1; i < e; ++i) { // NOLINT
    OpStr[i] -= 'a';
    OpStr[i] += 'A';
  }

  return formatv("{0}{1}", OpStr, BitWidth);
}

std::string ValueToOperandText(Value *Val) { // NOLINT

  if (auto *CI = dyn_cast<ConstantInt>(Val)) {
    return formatv("{0}", CI->getValue().getSExtValue());
  }
  auto *CFP = dyn_cast<ConstantFP>(Val);
  DSA_CHECK(CFP);
  // TODO: Support more data types
  double FPV = CFP->getValueAPF().convertToDouble();
  uint64_t *RI = reinterpret_cast<uint64_t *>(&FPV);
  return formatv("{0}", *RI);
}

bool Predicate::addCond(Instruction *Inst) {
  auto *Cmp = dyn_cast<ICmpInst>(Inst);
  assert(Cmp);

  bool NonReverse = Cmp->getOperand(0) == Cond[0]->getOperand(0) &&
                    Cmp->getOperand(1) == Cond[0]->getOperand(1);
  (void) NonReverse;
  bool Reverse = (Cmp->getOperand(1) == Cond[0]->getOperand(0) &&
                  Cmp->getOperand(0) == Cond[0]->getOperand(1));
  assert(NonReverse || Reverse);

  for (size_t i = 0; i < Cond.size(); ++i) { // NOLINT
    auto *Elem = Cond[i];
    if (Cmp == Elem) {
      LLVM_DEBUG(DSA_INFO << "Alread added! No further operation needed!");
      return Reversed[i];
    }
  }

  Cond.push_back(Inst);
  Reversed.push_back(Reverse);

  return Reverse;
}

int Predicate::contains(Instruction *Inst) {
  for (size_t i = 0; i < Cond.size(); ++i) { // NOLINT
    if (Cond[i] == Inst)
      return i;
  }
  return -1;
}

int Predicate::toCompareRes(Instruction *Inst, bool TF) {
  int Idx = contains(Inst);
  assert(Idx != -1);
  auto *Cmp = dyn_cast<ICmpInst>(Inst);
  if (!Cmp)
    return -1;
  return PredicateToInt(Cmp->getPredicate(), TF, Reversed[Idx]);
}

struct ControlBit {
  std::ostringstream SubCtrl[3];
  Predicate *Pred{nullptr};

  void addControlledMemoryStream(int Idx, DFGEntry *DE) {
    if (auto *CMP = dyn_cast<CtrlMemPort>(DE)) {
      if (Pred == nullptr) {
        Pred = CMP->Pred;
      } else {
        assert(Pred == CMP->Pred && "An instruction cannot be controlled by "
                                    "more than one predication.");
      }
      assert(Pred);
      for (int j = 0; j < 3; ++j) { // NOLINT
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
    for (int i = 0; i < 3; ++i) // NOLINT
      if (!SubCtrl[i].str().empty())
        return false;
    return true;
  }

  std::string finalize() {
    std::ostringstream Ctrl;
    for (int i = 0; i < 3; ++i) { // NOLINT
      if (!SubCtrl[i].str().empty()) {
        if (!Ctrl.str().empty())
          Ctrl << ", ";
        Ctrl << i << ":" << SubCtrl[i].str();
      }
    }
    return Ctrl.str();
  }

  void updateAbstain(int x, bool isAcc) { // NOLINT
    for (int i = 0; i < 3; ++i) { // NOLINT
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
void Predicate::emitCond(std::ostringstream &OS) {

  if (!dsa::utils::ModuleContext().PRED) {
    return;
  }

  {
    OS << "# [Predication] Combination\n";
    for (auto *I : Cond) {
      std::string Tmp;
      raw_string_ostream OSS(Tmp);
      I->print(OSS);
      OS << "# " << Tmp << "\n";
    }
  }

  ControlBit CtrlBit;
  OS << name(-1) << " = Compare"
     << Cond[0]->getOperand(0)->getType()->getScalarSizeInBits() << "(";
  for (size_t i = 0; i < Cond[0]->getNumOperands(); ++i) { // NOLINT
    auto *Val = Cond[0]->getOperand(i);
    if (i) {
      OS << ", ";
    }
    if (auto *EntryOp = Parent->InThisDFG(Val)) {
      OS << EntryOp->name(-1);
      CtrlBit.addControlledMemoryStream(i, EntryOp);
      if (auto *CMP = dyn_cast<CtrlMemPort>(EntryOp))
        CMP->ForPredicate = true;
    } else {
      OS << ValueToOperandText(Val);
    }
  }

  if (!CtrlBit.empty()) {
    if (CtrlBit.Pred == this)
      OS << ", self=";
    else
      OS << ", ctrl=" << CtrlBit.Pred->name(-1);
    OS << "{" << CtrlBit.finalize() << "}";
  }

  OS << ")\n";
}

AtomicPortMem *ComputeBody::isAtomic() {
  for (auto *Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (!Entry->Operand) {
      continue;
    }
    if (Entry->Op == underlyingInst()) {
      return Entry;
    }
  }
  return nullptr;
}

// void ComputeBody::EmitAtomic(std::ostringstream &OS) {
//   if (isImmediateAtomic()) {
//     OS << "Output" << underlyingInst()->getType()->getScalarSizeInBits() << ": "
//        << name();
//     if (shouldUnroll())
//       OS << "[" << Parent->getUnroll() << "]";
//     OS << "\n";
//   }
// }

AtomicPortMem *ComputeBody::isImmediateAtomic() {
  for (auto *Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (Entry->OpCode != 3 && Entry->Operand == underlyingInst()) {
      return Entry;
    }
  }
  return nullptr;
}

Predicate::Predicate(DFGBase *Parent_, Instruction *Cond_) // NOLINT
    : DFGEntry(Parent_), Cond{Cond_}, Reversed{false} {
  Kind = kPredicate;
}

bool Predicate::shouldUnroll() { return false; }

Instruction *Predicate::underlyingInst() { return Cond[0]; }

int TBits(int Bits) { // NOLINT
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
  DSA_CHECK(false);
  return -1;
}


// If this IndMemPort is a source operand of atomic update, i.e. a[b[i]] ?= operand.
bool IndMemPort::duplicated() {
  for (auto *Entry : Parent->EntryFilter<AtomicPortMem>()) {
    if (!Entry->Operand) {
      continue;
    }
    if (Index->underlyingInst() == Entry->Index->underlyingInst()) {
      return true;
    }
  }
  return false;
}

AtomicPortMem::AtomicPortMem(DFGBase *Parent_, LoadInst *Index_, // NOLINT
                             StoreInst *Store_, int OpCode_, Instruction *Op_, // NOLINT
                             Value *Operand_) // NOLINT
    : OutputPort(Parent_, Store_->getValueOperand()),
      Index(new MemPort(Parent_, Index_)), Store(Store_), OpCode(OpCode_),
      Op(Op_), Operand(Operand_) {

  Kind = kAtomicPortMem;

  if (OpCode == 0) {
    assert(Operand);
  }
}

Instruction *AtomicPortMem::underlyingInst() { return Store; }

std::vector<Instruction *> Predicate::underlyingInsts() {
  return std::vector<Instruction *>(Cond.data(), Cond.data() + Cond.size());
}

std::vector<Instruction *> IndMemPort::underlyingInsts() {
  return {Index->Load, Load};
}

std::vector<Instruction *> AtomicPortMem::underlyingInsts() {
  if (Op) {
    return {Index->Load, Store, Op};
  }
  return {Index->Load, Store};
}

int PortBase::vectorizeFactor() {
  return shouldUnroll() ? Parent->getUnroll() : 1;
}

namespace dsa {

void DFGEntryVisitor::Visit(DFGEntry *Node) {}

#define VISIT_IMPL(Ext, Super)             \
  void DFGEntryVisitor::Visit(Ext *Node) { \
    Visit(static_cast<Super *>(Node));     \
  }

VISIT_IMPL(ComputeBody, DFGEntry)
VISIT_IMPL(Predicate, DFGEntry)
VISIT_IMPL(Accumulator, ComputeBody)
VISIT_IMPL(PortBase, DFGEntry)
VISIT_IMPL(InputPort, PortBase)
VISIT_IMPL(CtrlMemPort, InputPort)
VISIT_IMPL(MemPort, InputPort)
VISIT_IMPL(StreamInPort, InputPort)
VISIT_IMPL(InputConst, InputPort)
VISIT_IMPL(OutputPort, PortBase)
VISIT_IMPL(PortMem, OutputPort)
VISIT_IMPL(StreamOutPort, OutputPort)

void DFGEntryVisitor::Visit(IndMemPort *IMP) {
  Visit(IMP->Index);
  Visit(static_cast<InputPort*>(IMP));
}

void DFGEntryVisitor::Visit(AtomicPortMem *APM) {
  Visit(APM->Index);
  Visit(static_cast<OutputPort*>(APM));
}

#undef VISIT_IMPL

#define COAL_VISIT_IMPL(Ext, Super)       \
  void DFGEntryVisitor::Visit(Ext *SMP) { \
    for (auto *Elem : SMP->Coal) {        \
      Elem->accept(this);                 \
    }                                     \
    Visit(static_cast<Super*>(SMP));      \
  }

COAL_VISIT_IMPL(SLPMemPort, InputPort)
COAL_VISIT_IMPL(SLPPortMem, OutputPort)

#undef COAL_VISIT_IMPL


} // namespace dsa
