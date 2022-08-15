#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

#include "DFGEntry.h"
#include "DFGIR.h"
#include "Util.h"

#include <queue>
#include <set>
#include <sys/select.h>

#define DEBUG_TYPE "stream-specialize"

std::string bitwiseRename(Instruction *Inst) {
  std::string Res = Inst->getOpcodeName();
  std::ostringstream OSS;
  std::map<std::string, std::string> Kv = {
    {"shl", "LShf"},
    {"shr", "RShf"},
    {"and", "And"},
    {"or", "Or"},
  };
  auto Iter = Kv.find(Res);
  if (Iter != Kv.end()) {
    OSS << Iter->second << "_U" << Inst->getType()->getScalarSizeInBits();
    return OSS.str();
  }
  return std::string();
}

CallInst *createAssembleCall(Type *Ty, StringRef OpStr, StringRef Operand,
                             ArrayRef<Value *> Args, Instruction *Before) {
  SmallVector<Type *, 0> ArgTypes;
  for (auto &Elem : Args)
    ArgTypes.push_back(Elem->getType());
  auto *FuncTy = FunctionType::get(Ty, ArgTypes, false);
  auto *IA = InlineAsm::get(FuncTy, OpStr, Operand, true);
  auto *Inst = CallInst::Create(IA, Args, None, "", Before);
  Inst->setTailCall();
  return Inst;
}

Constant *createConstant(LLVMContext &Context, uint64_t Val, int Bits) {
  APInt Bytes(Bits, Val);
  return Constant::getIntegerValue(IntegerType::get(Context, Bits), Bytes);
}

std::string funcNameToDFGName(const StringRef &Name) {
  llvm::errs() << "\n";
  assert(Name.startswith(OffloadPrefix));
  if (Name.equals(OffloadPrefix))
    return "dfg0.dfg";
  assert(Name[OffloadPrefix.size()] == '.');
  return formatv("dfg{0}.dfg",
                 Name.substr(OffloadPrefix.size() + 1, Name.size()))
      .str();
}

Value *GetLoopTripCount(ScalarEvolution *SE, SCEVExpander *Expander, Loop *Loop, // NOLINT
                        Instruction *InsertBefore) {
  auto *One = createConstant(Loop->getExitBlock()->getContext(), 1);
  auto *MinusOne = Expander->expandCodeFor(SE->getBackedgeTakenCount(Loop),
                                          nullptr, InsertBefore);
  auto *TripCount = BinaryOperator::Create(Instruction::Add, MinusOne, One,
                                          "trip.count", InsertBefore);
  return TripCount;
}

const std::map<std::string, std::string> IntrinsicCalls = {
  {"sqrt", ""},
  {"fsqrt", ""},
  {"min64", ""},
  {"max64", ""},
  {"fmax64", ""},
  {"min32", ""},
  {"max32", ""},
  {"min16", ""},
  {"max16", ""},
  {"min8", ""},
  {"max8", ""},
  {"div16", ""},
  {"hladd64", "HLAdd_I64"},
  {"hladd32x2", "HLAdd_I32x2"},
  {"add16x4", "Add_I16x4"},
  {"mul16x4", "Mul_I16x4"},
  {"div16x4", "Div_I16x4"},
  {"concat64", "Concat_I64"},
  {"concat32", "Concat_I32"},
  {"concat32x2", "Concat_I32x2"},
  {"fmul32x2", "FMul_F32x2"},
  {"fadd32x2", "FAdd_F32x2"},
  {"fsub32x2", "FSub_F32x2"},
  {"fhladd64", "FAdd_F32x2"}, // TODO(@Sihao): Implement these two FU later!
  {"fhladd32x2", "FAdd_F32x2"},
};

const std::map<std::string, std::string> &spatialIntrinics() {
  return IntrinsicCalls;
}

bool CanBeAEntry(Value *Val) {
  auto *Inst = dyn_cast<Instruction>(Val);
  if (!Inst) {
    return false;
  }
  if (auto *Call = dyn_cast<CallInst>(Inst)) {
    auto Name = Call->getCalledFunction()->getName();
    if (spatialIntrinics().find(Name.str()) != spatialIntrinics().end()) {
      return true;
    }
  }
  if (isa<CmpInst>(Inst)) {
    for (auto *User : Inst->users()) {
      if (isa<BranchInst>(User)) {
        return false;
      }
    }
    return true;
  }
  return Inst->isBinaryOp() || isa<SelectInst>(Inst);
}

Value *CeilDiv(Value *A, Value *B, Instruction *InsertBefore) {
  auto *One = createConstant(A->getContext(), 1);
  auto *SubOne =
      BinaryOperator::Create(BinaryOperator::Sub, A, One, "", InsertBefore);
  auto *Div =
      BinaryOperator::Create(BinaryOperator::SDiv, SubOne, B, "", InsertBefore);
  return BinaryOperator::Create(BinaryOperator::Add, Div, One, "",
                                InsertBefore);
}

Value *CeilDiv(Value *A, Value *B, IRBuilder<> *IB) {
  auto *One = IB->getIntN(A->getType()->getScalarSizeInBits(), 1);
  return IB->CreateAdd(IB->CreateSDiv(IB->CreateSub(A, One), B), One);
}

void FindEquivPHIs(Instruction *Inst, std::set<Instruction *> &Equiv) {
  std::queue<Instruction *> Q;
  Q.push(Inst);
  Equiv.insert(Inst);
  while (!Q.empty()) {
    if (auto *PHI = dyn_cast<PHINode>(Q.front())) {
      for (auto &Elem : PHI->incoming_values()) {
        auto *Casted = dyn_cast<Instruction>(Elem);
        if (!Casted)
          continue;
        if (Equiv.count(Casted))
          continue;
        Q.push(Casted);
        Equiv.insert(Casted);
      }
    }
    for (auto *User : Q.front()->users()) {
      auto *Phi = dyn_cast<PHINode>(User);
      if (!Phi)
        continue;
      if (Equiv.count(Phi))
        continue;
      Q.push(Phi);
      Equiv.insert(Phi);
    }
    Q.pop();
  }

  DSA_LOG(EQUIV) << *Inst;
  for (auto *I: Equiv) {
    DSA_LOG(EQUIV) << *I;
  }
}

int PredicateToInt(ICmpInst::Predicate Pred, bool TF, bool Reverse) {
  int Res = 0;
  switch (Pred) {
  case ICmpInst::ICMP_EQ:
    Res = 1 << 0;
    break;
  case ICmpInst::ICMP_SGT:
  case ICmpInst::ICMP_UGT:
    Res = !Reverse ? 1 << 1 : 1 << 2;
    break;
  case ICmpInst::ICMP_SLT:
  case ICmpInst::ICMP_ULT:
    Res = !Reverse ? 1 << 2 : 1 << 1;
    break;
  case ICmpInst::ICMP_SLE:
  case ICmpInst::ICMP_ULE:
    Res = !Reverse ? (1 << 2 | 1 << 0) : (1 << 1 | 1 << 0);
    break;
  case ICmpInst::ICMP_SGE:
  case ICmpInst::ICMP_UGE:
    Res = !Reverse ? (1 << 1 | 1 << 0) : (1 << 2 | 1 << 0);
    break;
  default:
    assert(false && "Not supported yet!");
  }
  return TF ? Res : (~Res & 7);
}

BasicBlock *FindLoopPrologue(Loop *L) {
  auto *Latch = L->getLoopLatch();
  assert(Latch);
  auto *BI = dyn_cast<BranchInst>(&Latch->back());
  assert(BI);
  for (int i = 0; i < (int) BI->getNumSuccessors(); ++i) { // NOLINT
    auto *DstBB = BI->getSuccessor(i);
    LLVM_DEBUG(DSA_INFO << "Inject stream wait fence " << DstBB->getName()
                      << "\n");
    if (!L->getBlocksSet().count(DstBB)) {
      return DstBB;
    }
  }
  return nullptr;
}

bool isOne(Value *Val) {
  if (!Val)
    return false;
  auto *CI = dyn_cast<ConstantInt>(Val);
  if (!CI)
    return false;
  return CI->getSExtValue() == 1;
}

namespace dsa {
namespace utils {

std::string nameOfLLVMValue(Function &Func, Value *Val) {
  if (Val->hasName()) {
    return Val->getName().str();
  }
  ModuleSlotTracker MST(Func.getParent());
  MST.incorporateFunction(Func);
  std::ostringstream OSS;
  OSS << "Array_of_" << Func.getName().str() << "_" << MST.getLocalSlot(Val);
  return OSS.str();
}

int consumerLevel(Value *Val, const std::vector<DFGEntry*> &Entries,
                  const std::vector<Loop*> &Loops) {
  std::vector<Instruction*> Consumers;
  for (auto *Entry : Entries) {
    for (auto *Inst : Entry->underlyingInsts()) {
      for (int i = 0; i < (int) Inst->getNumOperands(); ++i) { // NOLINT
        if (Inst->getOperand(i) == Val) {
          Consumers.push_back(Inst);
        }
      }
    }
  }
  std::vector<int> Res;
  Res.resize(Consumers.size(), -1);
  DSA_CHECK(Consumers.size() == Res.size());
  for (int i = 0; i < (int) Consumers.size(); ++i) { // NOLINT
    for (int j = 0; j < (int) Loops.size(); ++j) { // NOLINT
      if (Loops[j]->contains(Consumers[i])) {
        Res[i] = j;
        break;
      }
    }
    DSA_CHECK(Res[i] != -1) << *Val << " used by " << *Consumers[i];
  }
  for (int i = 1; i < (int) Res.size(); ++i) { // NOLINT
    if (Res[i] != Res[0]) {
      return -1;
    }
  }
  return Res[0];
}

ModuleFlags &ModuleContext() {
  static ModuleFlags Instance;
  return Instance;
}


int DSUGetSet(int Elem, std::vector<int> &DSU) {
  if (DSU[Elem] == Elem) {
    return Elem;
  }
  return DSU[Elem] = DSUGetSet(DSU[Elem], DSU);
}

std::vector<std::vector<int>> DSU2Sets(std::vector<int> &DSU) {
  std::vector<std::vector<int>> Res(DSU.size());
  for (int i = 0; i < (int) DSU.size(); ++i) { // NOLINT
    Res[DSUGetSet(i, DSU)].push_back(i);
  }
  return Res;
}

uint64_t TimeProfiler::currentTime() {
  timeval TV;
  gettimeofday(&TV, nullptr);
  return TV.tv_sec * 1000000 + TV.tv_usec;
}

void TimeProfiler::beginRoi() {
  TimeStack.emplace_back(currentTime(), std::vector<int>());
}

void TimeProfiler::endRoi() {
  Buffer.emplace_back();
  Buffer.back().TimeEllapsed = currentTime() - TimeStack.back().first;
  Buffer.back().Child = TimeStack.back().second;
  TimeStack.pop_back();
  if (!TimeStack.empty()) {
    TimeStack.back().second.push_back(Buffer.size() - 1);
  }
}

void TimeProfiler::dfsImpl(int X, std::ostringstream &OSS) {
  if (!Buffer[X].Child.empty()) {
    OSS << "(" << Buffer[X].TimeEllapsed << ": ";
    int First = true;
    for (auto Elem : Buffer[X].Child) {
      if (!First) {
        OSS << ", ";
      }
      First = false;
      dfsImpl(Elem, OSS);
    }
    OSS << ")";
  } else {
    OSS << Buffer[X].TimeEllapsed;
  }
}

std::string TimeProfiler::toString() {
  std::ostringstream OSS;
  OSS << "Profiled Time: ";
  DSA_CHECK(TimeStack.empty());
  dfsImpl(Buffer.size() - 1, OSS);
  return OSS.str();
}

} // namespace utils
} // namespace dsa

raw_ostream &operator<<(raw_ostream &OS, DFGEntry &DE) {

  static const char *KindStr[] = {
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

  OS << "# [" << KindStr[(int) DE.Kind] << "]: DFG" << DE.Parent->ID << " Entry"
     << DE.ID << "\n";
  int i = 0; // NOLINT
  auto Insts = DE.underlyingInsts();
  for (auto *Elem : Insts) {
    OS << "# Inst";
    if (Insts.size() != 1) {
      OS << i++;
    }
    OS << ": " << *Elem << "\n";
  }
  return OS;
}

Value *stripCast(Value *V) {
  while (auto *CI = dyn_cast<CastInst>(V)) {
    V = CI->getOperand(0);
  }
  return V;
}

const SCEV *stripCast(const SCEV *SE) {
  while (auto *SCE = dyn_cast<SCEVCastExpr>(SE)) {
    SE = SCE->getOperand(0);
  }
  return SE;
}


void traverseAndApply(Instruction *Start, Instruction *Terminator, DominatorTree *DT,
                      std::function<void(Instruction*)> F) {
  DSA_CHECK(DT->dominates(Start, Terminator));
  for (auto *BB : breadth_first(Start->getParent())) {
    if (DT->dominates(Start, BB) || BB == Start->getParent()) {
      auto *Begin = BB == Start->getParent() ? Start : &BB->front();
      auto *End = BB == Terminator->getParent() ? Terminator : &BB->back();
      DSA_LOG(TRAVERSE) << BB->getName();
      for (auto *I = Begin; I != End; I = I->getNextNode()) {
        DSA_LOG(TRAVERSE) << *I;
        F(I);
      }
      F(End);
    }
  }
}


