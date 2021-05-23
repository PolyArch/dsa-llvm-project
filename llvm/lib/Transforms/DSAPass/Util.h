#pragma once

#include <map>
#include <set>
#include <string>
#include <tuple>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"

using namespace llvm;

namespace dsa {
namespace utils {

/*!
 * \brief The compilation transformations enabled modularly.
 */
struct ModuleFlags {

#define DEFINE_FLAG(x, default_)                                               \
  int64_t x{default_};                                                         \
  void getFlag##x() {                                                          \
    char *env = getenv(#x);                                                    \
    if (env)                                                                   \
      x = std::stol(env);                                                      \
  }
  /*!
   * \brief Indirect memory access like a[b[i]].
   */
  DEFINE_FLAG(IND, 1)
  /*!
   * \brief Optimization for recurrent update.
   */
  DEFINE_FLAG(REC, 1)
  /*!
   * \brief Converting control flow to data flow predication.
   */
  DEFINE_FLAG(PRED, 1)
  /*!
   * \brief If we have temporal processing elements on the spatial architecture.
   */
  DEFINE_FLAG(TEMPORAL, 1)
  /*!
   * \brief If we want to move all the processing elements on triggered PE (even
   * if they are not annotated with temporal).
   */
  DEFINE_FLAG(TRIGGER, 0)
  /*!
   * \brief If we just want to extract the DFG without further transformation.
   */
  DEFINE_FLAG(EXTRACT, 0)
  /*!
   * \brief If we want to execute the peephole optimization over dsa register
   * file instructions.
   */
  DEFINE_FLAG(FUSION, 0)
#undef DEFINE_FLAG

  ModuleFlags() {
    getFlagIND();
    getFlagREC();
    getFlagPRED();
    getFlagTEMPORAL();
    getFlagTRIGGER();
    getFlagEXTRACT();
    getFlagFUSION();
  }
};

/*!
 * \brief Return the features enabled.
 */
ModuleFlags &ModuleContext();

/*!
 * \brief The data structure bundle for DSA registers.
 */
struct StickyRegister {
  /*!
   * \brief The struct allocation instruction.
   */
  Value *Alloca;
  /*!
   * \brief The memory that holds the value of the register.
   */
  Value *Reg;
  /*!
   * \brief The memory that holds the value of the stickiness.
   */
  Value *Sticky;

  StickyRegister(Value *A, Value *R, Value *S) : Alloca(A), Reg(R), Sticky(S) {}
};

} // namespace utils

using RegisterFile = std::vector<utils::StickyRegister>;

} // namespace dsa

#undef assert
#define assert(x)                                                              \
  do {                                                                         \
    if (!(x))                                                                  \
      exit(1);                                                                 \
  } while (false)

const std::string OffloadPrefix = "__ss_offload";
const std::string TemporalPrefix = "__ss_temporal";
const double Eps = 1e-5;
const int ReservedPorts[] = {23, 24, 25, 26};
const int MemScrPort = 23;

/// Helper function to build a InlineAsm-Call
CallInst *createAssembleCall(Type *Ty, StringRef Inst, StringRef Operand,
                             ArrayRef<Value *> Args, Instruction *Before);

Constant *createConstant(LLVMContext &Context, uint64_t Val, int Bits = 64);

Value *CeilDiv(Value *A, Value *B, Instruction *InsertBefore);

std::string funcNameToDFGName(const StringRef &Name);

template <typename Desired, typename Iteratable>
std::vector<Desired *> TypeFilter(const Iteratable &List) {
  std::vector<Desired *> Res;
  for (auto Elem : List) {
    if (auto Val = dyn_cast<Desired>(Elem)) {
      Res.push_back(Val);
    }
  }
  return Res;
}

bool CanBeAEntry(Value *Inst);

bool isOne(Value *Val);

void FindEquivPHIs(Instruction *, std::set<Instruction *> &);

int PredicateToInt(ICmpInst::Predicate Pred, bool TF, bool Reverse);

BasicBlock *FindLoopPrologue(Loop *L);

class DFGEntry;

raw_ostream &operator<<(raw_ostream &OS, DFGEntry &DE);
