#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

#include "DFGEntry.h"
#include "DFGIR.h"
#include "Util.h"

#include <queue>
#include <set>

#define DEBUG_TYPE "stream-specialize"

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

bool CanBeAEntry(Value *Val) {
  auto *Inst = dyn_cast<Instruction>(Val);
  if (!Inst) {
    return false;
  }
  if (auto *Call = dyn_cast<CallInst>(Inst)) {
    return Call->getCalledFunction()->getName() == "sqrt";
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

  LLVM_DEBUG(errs() << "equiv of "; Inst->dump(); for (auto I
                                                       : Equiv) { I->dump(); });
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
