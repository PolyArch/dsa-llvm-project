#include <cstdlib>
#include <sstream>
#include <fstream>
#include <queue>
#include <map>

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Support/Format.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

#include "dsa-ext/rf.h"
#include "dsa/debug.h"

using namespace llvm;

#define DEBUG_TYPE "dsa-peephole"

const std::string StickyStr[] = {"Non-sticky", "Sticky"};

const std::string PaddingStr[] = {
  "NoPadding",
  "PostStridePredOff",
  "PostStride_0",
  "PreStridePredOff",
  "PreStride_0",
};

const int Signal[] = {0, 1, 0, -1};

const std::string MemoryStr[] = {
  "DMA",
  "SPAD",
};

const std::string OperationStr[] = {
  "Read",
  "Write",
  "AtomAdd",
  "AtomSub",
  "AtomMul",
  "AtomDiv",
  "AtomMax",
  "AtomMin",
};

struct DSAFusion : public FunctionPass {

  DSAFusion() : FunctionPass(ID) {}

  // {
  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  // }


  static char ID;
};

void EliminateEquals(Function &F) {
  IRBuilder<> IB(F.getContext());
  struct Equality {
    bool ES{false};
    bool EV{false};
    Equality(bool ES = false, bool EV = false) : ES(ES), EV(EV) {}
  };

  for (auto &BB : F) {
    std::vector<Instruction*> ToErase;
    std::vector<Equality> Operands(2);
    for (auto Iter = BB.begin(); Iter != BB.end(); ++Iter) {
      Instruction *Inst = &(*Iter);
      if (auto Call = dyn_cast<CallInst>(Inst)) {
        if (auto IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
          llvm::errs() << "[Call] "<< *Call << "\n";
          if (IA->getAsmString().find("ss_lin_strm") == 0) {
            // uint64_t res = port & 127;
            // res = (res << 3) | (padding & 7);
            // res = (res << 1) | (action & 1);
            // res = (res << 2) | (dimension & 3);
            // res = (res << 3) | (operation & 7);
            // res = (res << 1) | (memory & 1);
            // res = (res << 2) | (signal & 3);
            // return res;
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(0));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            int Sign = Imm & 3;
            Imm >>= 2;
            int Memory = Imm & 1;
            Imm >>= 1;
            int Operation = Imm & 7;
            Imm >>= 3;
            int Dim = Imm & 3;
            Imm >>= 2;
            int Action = Imm & 1;
            Imm >>= 1;
            int Padding = Imm & 7;
            Imm >>= 3;
            int Port = Imm & 127;
            llvm::errs() << "[LinearStream] Signal: " << Signal[Sign]
                         << ", Memory: " << MemoryStr[Memory]
                         << ", Operation: " << OperationStr[Operation]
                         << ", Dimension: " << (Dim + 1)
                         << ", Action: " << (Action ? "Generate" : "Access")
                         << ", Padding: " << PaddingStr[Padding]
                         << ", Port: " << Port << "\n";
          } else if (IA->getAsmString().find("ss_ind_strm") == 0) {
            // uint64_t value = (in_port) & 127;
            // value = (value << 3) | ((lin_mode) & 7);
            // value = (value << 3) | ((ind_mode) & 7);
            // value = (value << 3) | (DMO_Read);
            // value = (value << 1) | ((memory) & 1);
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(0));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            int Memory = Imm & 1;
            Imm >>= 1;
            int Operation = Imm & 7;
            Imm >>= 3;
            int Ind = Imm & 7;
            Imm >>= 3;
            int Lin = Imm & 7;
            Imm >>= 3;
            int Port = Imm & 127;
            llvm::errs() << "[IndirectStream] Memory: " << MemoryStr[Memory]
                         << ", Operation: " << OperationStr[Operation]
                         << ", LinearMode: " << Lin
                         << ", IndirectMode: " << Ind
                         << ", Port: " << Port << "\n";
          } else if (IA->getAsmString().find("ss_recv") == 0) {
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(0));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            Imm >>= 1;
            int DType = Imm & 3;
            Imm >>= 2;
            Imm >>= 1;
            int Port = Imm & 127;
            llvm::errs() << "[Recv] DType: " << (1 << DType)
                         << "Port: " << Port << "\n";
          } else if (IA->getAsmString().find("ss_wr_rd") == 0) {
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(0));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            int IPort = Imm & 127;
            int OPort = (Imm >> 7) & 127;
            llvm::errs() << "[Recurrence] " << OPort << " -> " << IPort << "\n";
          } else if (IA->getAsmString().find("ss_cfg_param") == 0) {
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(2));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            int Idx[] = {(int)(Imm & 31), int((Imm >> 5) & 31)};
            int S[] =  {(int)((Imm >> 10) & 1), (int)((Imm >> 11) & 1)};
            auto DType = [] (int x, Value *Vy) {
              if (x == DSARF::CSR) {
                // int direct_ = _LOG2((direct) / DSA_ADDRESSABLE_MEM);
                // int const_ = _LOG2((const_type) / DSA_ADDRESSABLE_MEM);
                // int indirect_ = _LOG2((indirect) / DSA_ADDRESSABLE_MEM);
                // uint64_t value = (direct_) | (const_ << 2) | ((indirect_) << 4);
                // CONFIG_PARAM(DSARF::CSR, value, 0);
                auto YCI = dyn_cast<ConstantInt>(Vy);
                DSA_CHECK(YCI);
                auto y = YCI->getSExtValue();
                int Direct = 1 << (y & 3);
                y >>= 2;
                int Const = 1 << (y & 3);
                y >>= 2;
                int Indirect = 1 << (y & 3);
                llvm::errs() << "[DType] Direct: " << Direct
                             << "bytes, Const: " << Const
                             << "bytes, Indirect: " << Indirect << "bytes\n";
              }
            };
            for (int i = 0; i < 2; ++i) {
              if (Idx[i]) {
                llvm::errs() << "[Set " << (i + 1) << "] " << REG_NAMES[Idx[i]]
                             << " " << *Call->getOperand(i) << " " << StickyStr[S[i]] << "\n";
                DType(Idx[i], Call->getOperand(i));
                llvm::errs() << "[Equal] " << Operands[i].ES << " " << Operands[i].EV << "\n";
                if (Operands[i].ES && Operands[i].EV) {
                  Call->setOperand(i, IB.getInt64(0));
                  Idx[i] = 0;
                }
              }
            }
            int S1 = S[0];
            int S2 = S[1];
            int S2_ = S2 ? ~((1 << 11) - 1) : 0;
            Call->setOperand(2, IB.getInt64(Idx[0] | (Idx[1] << 5) | (S1 << 10) | S2_));
            Operands[0] = Operands[1] = Equality();
            if (!Idx[0] && !Idx[1]) {
              ToErase.push_back(Call);
            }
          } else if (IA->getAsmString().find("equal.hint.") == 0) {
            int Id;
            auto Val = dyn_cast<ConstantInt>(Call->getOperand(0));
            if (Val && Val->getSExtValue()) {
              auto Suf = IA->getAsmString().substr(std::string("equal.hint.").size());
              DSA_CHECK(sscanf(Suf.c_str() + 1, "%d", &Id) == 1);
              --Id;
              llvm::errs() << "[Suffix] " << Suf << " " << Suf[0] << " " << Id << "\n";
              if (Suf[0] == 's') {
                Operands[Id].ES = true;
              } else {
                DSA_CHECK(Suf[0] == 'v');
                Operands[Id].EV = true;
              }
              llvm::errs() << "[Equal] " << Id << ": "
                           << Operands[Id].ES << " " << Operands[Id].EV << "\n";
            } else {
              llvm::errs() << "[Equal] 1: "
                           << Operands[0].ES << " " << Operands[0].EV << "\n";
              llvm::errs() << "[Equal] 0: "
                           << Operands[1].ES << " " << Operands[1].EV << "\n";
            }
            ToErase.push_back(Inst);
            continue;
          }
          llvm::errs() << "\n";
        }
      }
    }
    for (auto Inst : ToErase) {
      Inst->eraseFromParent();
    }
  }
}

void FuseZeroConfigs(Function &F, DominatorTree *DT) {
  IRBuilder<> IB(F.getContext());
  struct OrphanSlot {
    int Idx;
    int Sticky;
    Value *V;
    Instruction *Inst;
    OrphanSlot(int I, int S, Value *V_, Instruction *Inst_) :
      Idx(I), Sticky(S), V(V_), Inst(Inst_) {}
  };
  for (auto &BB : F) {
    std::vector<OrphanSlot> Slots;
    std::vector<Instruction*> ToErase;
    for (auto Iter = BB.begin(); Iter != BB.end(); ++Iter) {
      Instruction *Inst = &(*Iter);
      if (auto Call = dyn_cast<CallInst>(Inst)) {
        if (auto IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
          llvm::errs() << "[Call] "<< *Call << "\n";
          if (IA->getAsmString().find("ss_cfg_param") == 0) {
            auto CI = dyn_cast<ConstantInt>(Call->getOperand(2));
            DSA_CHECK(CI);
            auto Imm = CI->getSExtValue();
            int Idx[2] = {(int)(Imm & 31), (int)((Imm >> 5) & 31)};
            int S[2] = {(int)((Imm >> 10) & 1), (int)((Imm >> 11) & 1)};
            if (Idx[0] == 0 || Idx[1] == 0) {
              llvm::errs() << "Single slot!\n";
              for (int i = 0; i < 2; ++i) {
                if (Idx[i]) {
                  Slots.emplace_back(Idx[i], S[i], Call->getOperand(i), Call);
                }
              }
            }
            if (Slots.size() == 2) {
              if (auto V = dyn_cast<Instruction>(Slots[1].V)) {
                if (!DT->dominates(V, Slots[0].Inst)) {
                  Slots.erase(Slots.begin());
                  continue;
                }
              }
              auto S2_ = Slots[1].Sticky ? ~((1 << 11) - 1) : 0;
              int64_t Imm = S2_ | (Slots[0].Sticky << 10) | (Slots[1].Idx << 5) | Slots[0].Idx;
              IB.SetInsertPoint(Slots[0].Inst);
              IB.CreateCall(IA, {Slots[0].V, Slots[1].V, IB.getInt64(Imm)});
              ToErase.push_back(Slots[0].Inst);
              ToErase.push_back(Slots[1].Inst);
              Slots.clear();
            }
          } else if (IA->getAsmString().find("ss_lin_strm") == 0 ||
                     IA->getAsmString().find("ss_ind_strm") == 0 ||
                     IA->getAsmString().find("ss_wr_rd") == 0 ||
                     IA->getAsmString().find("ss_recv") == 0) {
            Slots.clear();
          }
        }
      }
    }
    for (auto Inst : ToErase) {
      llvm::errs() << "Erase " << *Inst << "\n";
      Inst->eraseFromParent();
    }
  }

}

bool DSAFusion::runOnFunction(Function &F) {
  EliminateEquals(F);
  auto DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  FuseZeroConfigs(F, DT);
  return false;
}

void DSAFusion::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<BlockFrequencyInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<TargetTransformInfoWrapperPass>();
  AU.addRequired<LoopAccessLegacyAnalysis>();
  AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
}

char DSAFusion::ID = 0;

static RegisterPass<DSAFusion> X("dsa-fusion", "Peephole optimization of dsa program...");
