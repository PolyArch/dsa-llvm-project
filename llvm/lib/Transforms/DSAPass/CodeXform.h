#pragma once

#include <iostream>

#include "./llvm_common.h"

#include "DFGAnalysis.h"
#include "DFGIR.h"
#include "Util.h"

namespace dsa {
namespace xform {

/*!
 * \brief Eliminate temporal intrinsics when temporal is not supported.
 * \param F The function to be transformed.
 */
void eliminateTemporal(Function &F);

/*!
 * \brief Inject DSA registers.
          These memory buffer will be used for register stickiness optimization.
 * \param F The function to be transformed.
 */
std::vector<utils::StickyRegister> injectDSARegisterFile(Function &F);

/*!
 * \brief Emit DFG to the given destination.
 * \param os Where the given DFG is emitted. If null, dump to the filename of
 * the given DFGFile.
 */
void emitDFG(raw_ostream &OS, DFGFile *DFG, analysis::DFGAnalysisResult &DAR, CodeGenContext &CGC);

struct CodeGenContext {
  /*!
   * \brief The IR injection wrapper.
   */
  IRBuilder<> *IB;
  /*!
   * \brief The DSA register file for peephole injection.
   */
  const RegisterFile &Regs;
  /*!
   * \brief Loop scalar analyzer.
   */
  ScalarEvolution &SE;
  /*!
   * \brief SCEV expander.
   */
  SCEVExpander &SEE;
  /*!
   * \brief Instruction domination.
   */
  DominatorTree *DT;
  /*!
   * \brief Block frequency.
   */
  BlockFrequencyInfo *BFI;
  /*!
   * \brief Loop information.
   */
  LoopInfo *LI;
  /*!
   * \brief The injected intrinsics.
   */
  std::vector<CallInst *> Res;

  /*!
   * \brief Implemeting the register to make it compatible with intrin_impl.
   */
  class REG {
    // I am not sure if it is a good design decision.
    Value *Val{nullptr};
    uint64_t I{0};

  public:
    REG() : Val() {}
    // If the value fed is already a llvm::Value, just feed it into Val.
    REG(Value *V) : Val(V) {}
    // If it is a C-PoD int, store it temporarily in I.
    REG(uint64_t V) : I(V) {}
    // This value should be finalized into a llvm::Value when accessing.
    Value *&value(IRBuilder<> *IB) {
      if (!Val) {
        Val = IB->getInt64(I);
      }
      return Val;
    }
  };

  CodeGenContext(IRBuilder<> *IB, const RegisterFile &Regs, ScalarEvolution &SE, SCEVExpander &SEE,
                 DominatorTree *DT, LoopInfo *LI, BlockFrequencyInfo *BFI) :
    IB(IB), Regs(Regs), SE(SE), SEE(SEE), DT(DT), BFI(BFI), LI(LI) {}

  /*!
   * \brief Inject load/store instructions so that the compiler can
   * automatically analyze the stickiness.
   */
  void injectFusionHints(std::string Mnemonic, REG &A, REG &B, int C);

  /*!
   * \brief Injector of intrinsic instructions.
   * \param Mnemonic The mnmonic of the instruction.
   * \param OpConstrain The operand constrain of the instructions.
   * \param Args The argument of the instruction call.
   * \param ResTy The result of the instruction.
   */
  void intrinsicImpl(const std::string &Mnemonic,
                     const std::string &OpConstrain,
                     const std::vector<Value *> &Args, Type *ResTy);

  /// Implementing the interfaces for intrinsic injection.
  /// @{
  REG DIV(REG a, REG b) { return IB->CreateUDiv(a.value(IB), b.value(IB)); } // NOLINT

  REG SUB(REG a, REG b) { return IB->CreateSub(a.value(IB), b.value(IB)); } // NOLINT

  REG SHL(REG a, REG b) { return IB->CreateShl(a.value(IB), b.value(IB)); } // NOLINT

  REG MUL(REG a, REG b) { return IB->CreateMul(a.value(IB), b.value(IB)); } // NOLINT

  void INTRINSIC_DRI(std::string Mnemonic, REG &A, REG B, int C) { // NOLINT
    intrinsicImpl(Mnemonic, "=r,r,i", {B.value(IB), IB->getInt64(C)},
                  IB->getInt64Ty());
    A.value(IB) = Res.back();
  }

  void INTRINSIC_RRI(std::string Mnemonic, REG A, REG B, int C) { // NOLINT
    // injectFusionHints(Mnemonic, A, B, C);
    intrinsicImpl(Mnemonic, "r,r,i",
                  {A.value(IB), B.value(IB), IB->getInt64(C)}, IB->getVoidTy());
  }

  void INTRINSIC_RI(std::string Mnemonic, REG A, int B) { // NOLINT
    intrinsicImpl(Mnemonic, "r,i", {A.value(IB), IB->getInt64(B)},
                  IB->getVoidTy());
  }

  void INTRINSIC_R(std::string Mnemonic, REG A) { // NOLINT
    intrinsicImpl(Mnemonic, "r", {A.value(IB)}, IB->getVoidTy());
  }
  /// @}

#include "intrin_impl.h"
};


/*!
 * \brief Inject configuration instruction.
 * \param CGC The injection wrapper.
 * \param CI The result of config analysis.
 * \param Start Where the config is injected.
 * \param End Where the wait all is injected.
 */
void injectConfiguration(CodeGenContext &CGC, analysis::ConfigInfo &CI,
                         Instruction *Start, Instruction *End);

/*!
 * \brief Inject stream intrinsics.
 * \param CGC The context of code injection.
 */
void injectStreamIntrinsics(CodeGenContext &CGC, DFGFile &DF, analysis::DFGAnalysisResult &DAR);

/*!
 *  \brief Erase offloaded instructions.
 *  \param DF
 *  \param CGC
 */
void eraseOffloadedInstructions(DFGFile &DF, CodeGenContext &CGC);

} // namespace xform
} // namespace dsa
