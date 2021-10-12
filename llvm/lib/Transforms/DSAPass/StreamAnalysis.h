#pragma once

#include "Pass.h"
#include "Util.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Casting.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include <map>
#include <memory>
#include <set>
#include <vector>

namespace dsa {
namespace analysis {

struct LinearTerm {
  virtual ~LinearTerm() {}
};

struct LoopInvariant : LinearTerm {
  /*!
   * \brief The loop invariant value under the linear combination.
   */
  const SCEV *Value;
  /*!
   * \brief If this LinearInfo is a constant int, return the value, o.w. return
   * nullptr.
   */
  const uint64_t *constInt() const { return nullptr; }
};

struct LinearCombination : LinearTerm {
  /*!
   * \brief The coefficient of linear combination.
   */
  std::vector<LinearTerm*> Coef;
  /*!
   * \brief The inductive variable of linear combination.
   */
  std::vector<Value*> *IndVar;
  /*!
   * \brief The trip count of each loop induction.
   */
  std::vector<LinearCombination*> *TripCount;
  /*!
   * \brief Return the loop level from which, this value is no longer a loop
   * nest invariant.
   */
  int partialInvariant() const { return 0; }
};

/*!
 * \brief Assuming the index expression is affined, we have sum(Loops[i] *
 * Coef[i]) + Base.
 */
struct LinearInfo {
  /*!
   * \brief The coefficient of each loop variable.
   */
  std::vector<LinearInfo> Coef;
  /*!
   * \brief The trip count of each loop variable.
   */
  std::vector<LinearInfo> TripCount;
  /*!
   * \brief The base coefficient
   */
  const SCEV *Base{nullptr};
  /*!
   * \brief Create loop invariant.
   * \param N The number of levels of loop nest.
   */
  static LinearInfo loopInvariant(ScalarEvolution *SE, int N, const SCEV *Base);
  /*!
   * \brief Dump this result of analysis for debugging.
   * \param Loops The loops on which analysis is based.
   */
  std::string
  toString(const std::vector<Loop *> &Loops = std::vector<Loop *>());
  /*!
   * \brief If this LinearInfo is a constant int, return the value, o.w. return
   * nullptr.
   */
  const uint64_t *constInt() const;
  /*!
   * \brief If this value is a loop invariant, return the SCEV for expansion.
   * O.w. return nullptr.
   */
  const SCEV *invariant() const;
  /*!
   * \brief Return the loop level from which, this value is no longer a loop
   * nest invariant.
   */
  int partialInvariant() const;
};

LinearInfo analyzeIndexExpr(ScalarEvolution *SE, const SCEV *Index,
                            const std::vector<Loop *> &LoopNest);

/*!
 * \brief Fuse continous inner-most memory access dimensions.
 * \param LI The memory access pattern to be fused.
 * \param DType The data type of memory access.
 * \param Unroll The unrolling degree of this access.
 * \param P The padding strategy of the access.
 * \param SE The SCEV analysis.
 * \param CutOff The dimension to stop fusing. Sometimes we do not want every dimension to be fused.
 */
void fuseInnerDimensions(LinearInfo &LI, int DType, int Unroll,
                         ScalarEvolution &SE, int CutOff);

} // namespace analysis
} // namespace dsa
