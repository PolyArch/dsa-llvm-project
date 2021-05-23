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

/*!
 * \brief Assuming the index expression is affined, we have sum(Loops[i] *
 * Coef[i]) + Base.
 */
struct LinearInfo {
  /*!
   * \brief The coefficient of each loop variable.
   */
  std::vector<LinearInfo *> Coef;
  /*!
   * \brief The base coefficient
   */
  const SCEV *Base{nullptr};
  /*!
   * \brief Create loop invariant.
   * \param N The number of levels of loop nest.
   */
  static LinearInfo *LoopInvariant(ScalarEvolution *SE, int N,
                                   const SCEV *Base);
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
  const uint64_t *ConstInt() const;
  /*!
   * \brief If this value is a loop invariant, return the SCEV for expansion.
   * O.w. return nullptr.
   */
  const SCEV *Invariant() const;
  /*!
   * \brief Return the loop level from which, this value is no longer a loop
   * nest invariant.
   */
  int PatialInvariant() const;
};

LinearInfo *AnalyzeIndexExpr(ScalarEvolution *SE, const SCEV *Index,
                             const std::vector<Loop *> &LoopNest);

} // namespace analysis
} // namespace dsa
