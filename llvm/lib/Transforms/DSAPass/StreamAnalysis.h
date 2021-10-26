#pragma once

#include <map>
#include <memory>
#include <set>
#include <vector>

#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Casting.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

#include "./Pass.h"
#include "./RTTIUtils.h"
#include "./Util.h"


namespace dsa {
namespace analysis {

enum StreamAnalyzeTy {
  kSEWrapper,
  kLoopInvariant,
  kLinearCombine,
  kUnknown
};

/*!
 * \brief Streams are analyzed by the ScalarEvolution module.
 *        In this pass, we need a helper wrapper to store the decoded SCEV information.
 */
struct SEWrapper {
  /*!
   * \brief The enum of LLVM RTTI.
   */
  StreamAnalyzeTy TyEnum{kUnknown};
  // TODO(@were): Let's see, I think I have all the specific site of using this instance.
  //              Thus, it is ok to be a union.
  /*!
   * \brief The DFG entry this SCEV derived.
   */
  union {
    void *Raw;
    DFGEntry *DE;
    Value *Val;
    Loop *L;
  } Parent{nullptr};
  /*!
   * \brief The raw SCEV to be extracted.
   */
  const SCEV *Raw;
  /*!
   * \brief Dump to text for debugging.
   */
  virtual std::string toString() const;

  virtual const SCEV *base() { return Raw;}

  SEWrapper(void *Parent, const SCEV *Raw) : Raw(Raw) {
    this->Parent.Raw = Parent;
  }

  RTTI_CLASS_OF(SEWrapper, kSEWrapper)

  virtual ~SEWrapper() {}
};

/*!
 * \brief Assuming the index expression is affined,
 *        we have sum(Loops[i] * Coef[i]) + Base.
 *        More complicatedly, Base can recursively be another level of linear combine.
 */
struct LinearCombine : SEWrapper {
  /*!
   * \brief The coefficient of each loop variable.
   */
  std::vector<SEWrapper*> Coef;
  /*!
   * \brief The trip count of each loop variable.
   */
  std::vector<SEWrapper*> TripCount;
  /*!
   * \brief The base coefficient
   */
  SEWrapper *Base;
  /*!
   * \brief Dump this result of analysis for debugging.
   * \param Loops The loops on which analysis is based.
   */
  std::string toString() const override;
  /*!
   * \brief Return the loop level from which, this value is no longer a loop
   * nest invariant.
   */
  int partialInvariant() const;

  LinearCombine(void *Parent, const SCEV *Raw) : SEWrapper(Parent, Raw) {
    this->TyEnum = kLinearCombine;
  }

  const SCEV *base() override { return Base->base();}

  ~LinearCombine();

  RTTI_CLASS_OF(SEWrapper, kLinearCombine)
};

/*!
 * \brief THis value is a loop invariant under the given loop.
 */
struct LoopInvariant : SEWrapper {
  /*!
   * \brief The trip count of loops above.
   */
  std::vector<SEWrapper*> TripCount;
  /*!
   * \brief If this value is a constant, return this value. Otherwise, return nullptr.
   */
  const uint64_t *constInt() const;

  LoopInvariant(void *Parent, const SCEV *Raw) : SEWrapper(Parent, Raw) {
    this->TyEnum = kLoopInvariant;
  }

  /*!
   * \brief A loop invariant can also be represented in a trivial linear combination.
   */
  LinearCombine *toLinearCombine(ScalarEvolution *SE);

  RTTI_CLASS_OF(SEWrapper, kLoopInvariant)
};


/*!
 * \brief
 */
SEWrapper *analyzeIndexExpr(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                            const std::vector<Loop *> &Loops,
                            const std::vector<SEWrapper *> &TripCount);

/*!
 * \brief Fuse continous inner-most memory access dimensions.
 * \param LI The memory access pattern to be fused.
 * \param DType The data type of memory access.
 * \param Unroll The unrolling degree of this access.
 * \param P The padding strategy of the access.
 * \param SE The SCEV analysis.
 * \param CutOff The dimension to stop fusing. Sometimes we do not want every dimension to be fused.
 */
void fuseInnerDimensions(LinearCombine &LI, int DType, int Unroll,
                         ScalarEvolution &SE, int CutOff);

} // namespace analysis
} // namespace dsa
