#ifndef STREAM_SPECIALIZE_UTIL_H_
#define STREAM_SPECIALIZE_UTIL_H_

#include <string>
#include <map>
#include <tuple>
#include <set>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"

using namespace llvm;

#undef assert
#define assert(x) do { if (!(x)) exit(1); } while(false)

const std::string OffloadPrefix = "__ss_offload";
const std::string TemporalPrefix = "__ss_temporal";
const double Eps = 1e-5;
const int ReservedPorts[] = {23, 24, 25, 26};
const int MemScrPort = 23;

/// Helper function to build a InlineAsm-Call
CallInst *createAssembleCall(Type *Ty, StringRef Inst, StringRef Operand, ArrayRef<Value*> Args,
                             Instruction *Before);

Constant *createConstant(LLVMContext &Context, uint64_t Val, int Bits = 64);

Value *CeilDiv(Value *A, Value *B, Instruction *InsertBefore);

std::string funcNameToDfgName(const StringRef &Name);

template<typename Desired, typename Iteratable>
std::vector<Desired*> TypeFilter(const Iteratable &List) {
  std::vector<Desired*> Res;
  for (auto Elem : List) {
    if (auto Val = dyn_cast<Desired>(Elem)) {
      Res.push_back(Val);
    }
  }
  return Res;
}

bool CanBeAEntry(Value *Inst);

bool isOne(Value *Val);

void FindEquivPHIs(Instruction *, std::set<Instruction*>&);

int PredicateToInt(ICmpInst::Predicate Pred, bool TF, bool Reverse);

BasicBlock *FindLoopPrologue(Loop *L);

#endif
