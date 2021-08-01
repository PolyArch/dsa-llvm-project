#include <cstdlib>
#include <fstream>
#include <map>
#include <queue>
#include <sstream>

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Format.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

#include "dsa/debug.h"

#define O1_CLEANUP                             \
  do {                                         \
    llvm::PassManagerBuilder PMB;              \
    PMB.OptLevel = 1;                          \
    PMB.Inliner = nullptr;                     \
    PMB.LoopVectorize = false;                 \
    PMB.SLPVectorize = false;                  \
    PMB.DisableUnrollLoops = true;             \
    llvm::legacy::FunctionPassManager FPM(&M); \
    llvm::legacy::PassManager PM;              \
    PMB.populateFunctionPassManager(FPM);      \
    PMB.populateModulePassManager(PM);         \
    for (auto &F : M.getFunctionList()) {      \
      FPM.run(F);                              \
    }                                          \
    FPM.doFinalization();                      \
    PM.run(M);                                 \
  } while (false)

using namespace llvm;

namespace dsa {
namespace tvm {


#define DEBUG_TYPE "tvm-cleanup"

struct RemoveBoundChecker : public ModulePass {

  RemoveBoundChecker() : ModulePass(ID) {}

  // {
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  // }


  static char ID;
};

bool RemoveBoundChecker::runOnModule(Module &M) {
  std::vector<std::string> ToRemove;
  for (auto &F : M.getFunctionList()) {
    if (F.getName().endswith("_compute_")) {
      auto Name = F.getName();
      ToRemove.emplace_back(Name.substr(0, Name.size() - std::string("_compute_").size()).str());
      llvm::errs() << "Will remove " << ToRemove.back() << "\n";
    }
  }
  for (auto &Elem : ToRemove) {
    auto *F = M.getFunction(Elem);
    CHECK(F) << Elem << " function not found!";
    F->replaceAllUsesWith(UndefValue::get(F->getType()));
    F->eraseFromParent();
    auto *FC = M.getFunction(Elem + "_compute_");
    CHECK(FC) << Elem << "_compute_ function not found!";
    FC->setName(Elem);
    FC->setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
  }

  O1_CLEANUP;

  return false;
}

void RemoveBoundChecker::getAnalysisUsage(AnalysisUsage &AU) const {
}

char RemoveBoundChecker::ID = 0;

static RegisterPass<RemoveBoundChecker>
  X("tvm-rm-bound-checker", "Cleanup the boundry enforcement generated by TVM...");

struct SignatureUnifier : public ModulePass {

  SignatureUnifier() : ModulePass(ID) {}

  // {
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {}
  // }

  static char ID;
};

bool SignatureUnifier::runOnModule(Module &M) {
  std::vector<Function*> ToDo;
  for (auto &F : M.functions()) {
    bool Resignature = true;
    for (auto &Arg : F.args()) {
      if (auto *PT = dyn_cast<llvm::PointerType>(Arg.getType())) {
        if (auto *IT = dyn_cast<llvm::IntegerType>(PT->getElementType())) {
          if (IT->getScalarSizeInBits() == 8) {
            continue;
          }
        }
      }
      Resignature = false;
      break;
    }
    if (Resignature) {
      ToDo.push_back(&F);
    }
  }
  for (auto *FPtr : ToDo) {
    auto &F = *FPtr;
    IRBuilder<> IB(F.getContext());
    auto *I8 = IB.getInt8PtrTy();
    auto *I8Ptr = llvm::PointerType::get(I8, 0);

    auto *FT = FunctionType::get(F.getReturnType(), {I8Ptr}, false);
    std::string UName = ("unified_" + F.getName()).str();
    std::string FName = F.getName().str();
    auto *UFunc =
      Function::Create(FT, F.getLinkage(), F.getAddressSpace(), UName, F.getParent());
    UFunc->setCallingConv(CallingConv::C);
    UFunc->setDLLStorageClass(GlobalValue::DLLStorageClassTypes::DLLExportStorageClass);
    auto *Entry = llvm::BasicBlock::Create(IB.getContext(), "entry", UFunc);
    int Idx = 0;
    IB.SetInsertPoint(Entry);
    auto *ArgStruct = UFunc->getArg(0);
    ValueToValueMapTy VVM;
    for (auto &Arg : F.args()) {
      auto *Ptr = IB.CreateInBoundsGEP(ArgStruct, {IB.getInt64(Idx)});
      auto *Load = IB.CreateLoad(Ptr);
      VVM[&Arg] = IB.CreateBitCast(Load, Arg.getType());
      ++Idx;
    }
    SmallVector<ReturnInst*, 0> Returns;
    llvm::CloneFunctionInto(UFunc, &F, VVM, true, Returns);
    IB.CreateBr(UFunc->getEntryBlock().getNextNode());
    F.eraseFromParent();
    UFunc->setName(FName);
  }

  O1_CLEANUP;

  return false;
}

char SignatureUnifier::ID = 0;

static RegisterPass<SignatureUnifier>
  Y("tvm-unify-signature", "Unify the function signature of a TVM generated function...");

} // namespace tvm
} // namespace dsa
