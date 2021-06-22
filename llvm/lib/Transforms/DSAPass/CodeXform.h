#pragma once

#include <iostream>

#include "./llvm_common.h"

#include "DFGAnalysis.h"
#include "Transformation.h"
#include "Util.h"

namespace dsa {
namespace xform {

/*!
 * \brief Eliminate temporal intrinsics when temporal is not supported.
 * \param F The function to be transformed.
 */
void EliminateTemporal(Function &F);

/*!
 * \brief Inject DSA registers.
          These memory buffer will be used for register stickiness optimization.
 * \param F The function to be transformed.
 */
std::vector<utils::StickyRegister> InjectDSARegisterFile(Function &F);

/*!
 * \brief Emit DFG to the given destination.
 * \param os Where the given DFG is emitted. If null, dump to the filename of
 * the given DFGFile.
 */
void EmitDFG(raw_ostream *os, DFGFile *DF);

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
   * \brief The injected intrinsics.
   */
  ScalarEvolution &SE;
  /*!
   * \brief The injected intrinsics.
   */
  SCEVExpander &SEE;
  /*!
   * \brief The injected intrinsics.
   */
  std::vector<CallInst *> res;

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

  CodeGenContext(IRBuilder<> *IB_, const RegisterFile &Regs_,
                 ScalarEvolution &SE_, SCEVExpander &SEE_)
      : IB(IB_), Regs(Regs_), SE(SE_), SEE(SEE_) {}

  /*!
   * \brief Inject load/store instructions so that the compiler can
   * automatically analyze the stickiness.
   */
  void InjectFusionHints(std::string Mnemonic, REG &a, REG &b, int c);

  /*!
   * \brief Injector of intrinsic instructions.
   * \param Mnemonic The mnmonic of the instruction.
   * \param OpConstrain The operand constrain of the instructions.
   * \param Args The argument of the instruction call.
   * \param ResTy The result of the instruction.
   */
  void IntrinsicImpl(const std::string &Mnemonic,
                     const std::string &OpConstrain,
                     const std::vector<Value *> &Args, Type *ResTy);

  /// Implementing the interfaces for intrinsic injection.
  /// @{
  REG DIV(REG a, REG b) { return IB->CreateUDiv(a.value(IB), b.value(IB)); }

  REG SUB(REG a, REG b) { return IB->CreateSub(a.value(IB), b.value(IB)); }

  REG SHL(REG a, REG b) { return IB->CreateShl(a.value(IB), b.value(IB)); }

  REG MUL(REG a, REG b) { return IB->CreateMul(a.value(IB), b.value(IB)); }

  void INTRINSIC_DRI(std::string Mnemonic, REG &a, REG b, int c) {
    IntrinsicImpl(Mnemonic, "=r,r,i", {b.value(IB), IB->getInt64(c)},
                  IB->getInt64Ty());
    a.value(IB) = res.back();
  }

  void INTRINSIC_RRI(std::string Mnemonic, REG a, REG b, int c) {
    InjectFusionHints(Mnemonic, a, b, c);
    IntrinsicImpl(Mnemonic, "r,r,i",
                  {a.value(IB), b.value(IB), IB->getInt64(c)}, IB->getVoidTy());
  }

  void INTRINSIC_RI(std::string Mnemonic, REG a, int b) {
    IntrinsicImpl(Mnemonic, "r,i", {a.value(IB), IB->getInt64(b)},
                  IB->getVoidTy());
  }

  void INTRINSIC_R(std::string Mnemonic, REG a) {
    IntrinsicImpl(Mnemonic, "r", {a.value(IB)}, IB->getVoidTy());
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
void InjectConfiguration(CodeGenContext &CGC, analysis::ConfigInfo &CI,
                         Instruction *Start, Instruction *End);

/*!
 * \brief Inject stream intrinsics.
 * \param CGC The context of code injection.
 */
void InjectStreamIntrinsics(CodeGenContext &CGC, DFGFile &DF);

} // namespace xform
} // namespace dsa
