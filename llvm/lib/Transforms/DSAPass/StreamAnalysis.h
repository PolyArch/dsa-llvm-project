#pragma once

#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Casting.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

#include "dsa/debug.h"

#include "./Pass.h"
#include "./RTTIUtils.h"
#include "./Util.h"


namespace dsa {
namespace analysis {

enum StreamAnalyzeTy {
  kSEWrapper,
  kSWBinary,
  kSWCast,
  kIndirectPointer,
  kLinearCombine,
  kLoopInvariant,
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
 * \brief a op b where op is either * or +.
 */
struct SWBinary : SEWrapper {
  int Op{-1}; // Add, Mul
  SEWrapper *A{nullptr};
  SEWrapper *B{nullptr};

  std::string toString() const override;

  SWBinary(void *Parent, const SCEV *Raw, int Op) : SEWrapper(Parent, Raw), Op(Op) {
    TyEnum = kSWBinary;
  }

  RTTI_CLASS_OF(SEWrapper, kSWBinary)
};

struct SWCast :SEWrapper {
  const SCEVCastExpr *SCE;
  SEWrapper *Stripped{nullptr};

  Type *destTy() const;

  Type *srcTy() const;

  std::string toString() const override;

  SWCast(void *Parent, const SCEV *Raw) : SEWrapper(Parent, Raw) {
    SCE = dyn_cast<SCEVCastExpr>(Raw);
    DSA_CHECK(SCE);
    TyEnum = kSWCast;
  }

  RTTI_CLASS_OF(SEWrapper, kSWCast)
};

/*!
 * \brief a[b[i]]
 */
struct IndirectPointer : SEWrapper {
  /*!
   * \brief Memory load to be analyzed.
   */
  LoadInst *Load{nullptr};
  /*!
   * \brief Analyzed pointer wrapper.
   */
  SEWrapper *Pointer{nullptr};

  std::string toString() const override;

  IndirectPointer(void *Parent, const SCEV *Raw,
                  LoadInst *L) : SEWrapper(Parent, Raw), Load(L) {
    TyEnum = kIndirectPointer;
  }

  RTTI_CLASS_OF(SEWrapper, kIndirectPointer)
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
    TyEnum = kLinearCombine;
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

  /*!
   * \brief Wrapped constructor.
   */
  static LoopInvariant *get(void *Parent, const SCEV *Raw);

  /*!
   * \brief A loop invariant can also be represented in a trivial linear combination.
   */
  LinearCombine *toLinearCombine(ScalarEvolution *SE);

  std::string toString() const override;

  RTTI_CLASS_OF(SEWrapper, kLoopInvariant)

 private:
  LoopInvariant(void *Parent, const SCEV *Raw) : SEWrapper(Parent, Raw) {
    TyEnum = kLoopInvariant;
  }

  static std::map<std::pair<void*, const SCEV*>, LoopInvariant*> UniqueInvariant;
};


/*!
 * \brief
 */
SEWrapper *analyzeIndexExpr(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                            const std::vector<Loop *> &Loops,
                            const std::vector<SEWrapper *> &TripCount,
                            const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride);

/*!
 * \brief
 */
IndirectPointer* analyzeIndirectPointer(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                                        const std::vector<Loop *> &Loops,
                                        const std::vector<SEWrapper *> &TripCount,
                                        const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride);

/*!
 * \brief
 */
SEWrapper *analyzeBinary(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                         const std::vector<Loop *> &Loops,
                         const std::vector<SEWrapper *> &TripCount,
                         const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride);

/*!
 * \brief
 */
SWCast *analyzeCast(ScalarEvolution *SE, const SCEV *Raw, void *Parent,
                    const std::vector<Loop *> &Loops,
                    const std::vector<SEWrapper *> &TripCount,
                    const std::unordered_map<const SCEV*, const SCEV*> &LinearOverride);

/*!
 * \brief Fuse continous inner-most memory access dimensions.
 * \param LI The memory access pattern to be fused.
 * \param DType The data type of memory access.
 * \param Unroll The unrolling degree of this access.
 * \param SE The SCEV analysis.
 * \param CutOff The dimension to stop fusing. Sometimes we do not want every dimension to be fused.
 * \param IsSLP If the LI is derived from SLP.
 */
void fuseInnerDimensions(LinearCombine &LI, int DType, int Unroll,
                         ScalarEvolution &SE, int CutOff, bool IsSLP);

} // namespace analysis
} // namespace dsa
