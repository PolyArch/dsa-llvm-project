#include "CodeXform.h"
#include "DFGAnalysis.h"
#include "StreamAnalysis.h"
#include "Util.h"

#include "dsa-ext/rf.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ScopedPrinter.h"
#include <unordered_map>

// raw_ostream &operator<<(raw_ostream &os, DFGEntry &DE) {
//   os << "# [" << dsa::xform::KindStr[DE.Kind] << "]" << " DFG" <<
//   DE.Parent->ID << " Entry" << DE.ID; if (DE.underlyingInsts().size() == 1) {
//     os << " " << *DE.underlyingInst();
//   } else {
//     os << "\n";
//     for (auto Elem : DE.underlyingInsts()) {
//       os << *Elem << "\n";
//     }
//   }
//   return os;
// }
//
// raw_ostream &operator<<(raw_ostream &os, DFGBase &DB) {
//   std::ostringstream oss;
//   DB.dump(oss);
//   os << oss.str();
//   return os;
// }

namespace dsa {
namespace xform {

namespace {

/*!
 * \brief To avoid some unexpected iterator issue.
 *        We delete the instructions together.
 * \param Insts The instructions to be removed.
 */
void EliminateInstructions(const std::vector<Instruction *> &Insts) { // NOLINT
  for (auto *I : Insts) {
    I->replaceAllUsesWith(UndefValue::get(I->getType()));
    I->eraseFromParent();
  }
}

int tagBitmask(int ResetLevel) {
  // L2D End      5
  // L2D Start    4
  // L1D End      3
  // L1D Start    2
  // Stream End   1
  // Stream Start 0
  int X = (ResetLevel + 1) % 3 * 2 + 1;
  return 1 << X;
}

} // namespace

void Indirect1D::emitIntrinsic(xform::CodeGenContext &CGC) {
}

void Indirect2D::emitIntrinsic(xform::CodeGenContext &CGC) {
  auto *IB = CGC.IB;
  auto &SEE = CGC.SEE;
  CGC.CONFIG_PARAM(DSARF::L2D, SEE.expandCodeFor(L2D), false, DSARF::I1D, IB->getInt64(1), false);
  CGC.SS_INDIRECT_2D_READ(DestPort, DType, OffsetPort, CGC.SEE.expandCodeFor(SAR->Raw), -1, IType,
                          -1, CGC.SEE.expandCodeFor(L1D->Raw), IB->getInt64(0), DMT_DMA);
}

void eliminateTemporal(Function &F) {
  std::vector<Instruction *> ToRemove;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *Intrin = dyn_cast<IntrinsicInst>(&I)) {
        switch (Intrin->getIntrinsicID()) {
        case Intrinsic::ss_temporal_region_start:
        case Intrinsic::ss_temporal_region_end:
          ToRemove.push_back(Intrin);
          break;
        default:
          break;
        }
      }
    }
  }
  EliminateInstructions(ToRemove);
}

std::vector<utils::StickyRegister> injectDSARegisterFile(Function &F) {
  IRBuilder<> IB(F.getContext());
  IB.SetInsertPoint(&F.getEntryBlock().front());
  std::vector<utils::StickyRegister> Res;
  std::string TyName("reg.type");
  auto *RegType = StructType::create(TyName, IB.getInt64Ty(), IB.getInt8Ty());
  for (int i = 0; i < DSARF::TOTAL_REG; ++i) { // NOLINT
    auto *A = IB.CreateAlloca(RegType, nullptr, REG_NAMES[i]);
    auto *R = IB.CreateInBoundsGEP(A, {IB.getInt32(0), IB.getInt32(0)},
                                  std::string(REG_NAMES[i]) + ".r.ptr");
    auto *S = IB.CreateInBoundsGEP(A, {IB.getInt32(0), IB.getInt32(1)},
                                  std::string(REG_NAMES[i]) + ".s.ptr");
    IB.CreateStore(IB.getInt64(REG_STICKY[i]), R);
    IB.CreateStore(IB.getInt8(i == DSARF::TBC), S);
    Res.emplace_back(A, R, S);
  }
  return Res;
}

std::string ValueToOperandText(Value *Val) { // NOLINT

  if (auto *CI = dyn_cast<ConstantInt>(Val)) {
    return formatv("{0}", (uint64_t) CI->getValue().getSExtValue());
  }
  auto *CFP = dyn_cast<ConstantFP>(Val);
  DSA_CHECK(CFP) << "Cannot dump " << *Val;
  // TODO: Support more data types
  double FPV = CFP->getValueAPF().convertToDouble();
  uint64_t *RI = reinterpret_cast<uint64_t *>(&FPV);
  return formatv("{0}", *RI);
}

std::string getOperationStr(Instruction *Inst, bool Acc, bool Predicated) {
  std::string OpStr;
  int BitWidth = Inst->getType()->getScalarSizeInBits();
  auto *Ty = Inst->getType();
  std::string TyStr;
  if (Ty->isFloatTy()) {
    TyStr = "F";
  } else if (Ty->isDoubleTy()) {
    TyStr = "D";
  } else if (Ty->isIntegerTy()) {
    TyStr = "I";
  }

  if (auto *Cmp = dyn_cast<CmpInst>(Inst)) {
    // TODO: Support floating point
    OpStr = (Cmp->getPredicate() >= 32) ? "compare" : "fcompare";
    BitWidth = Cmp->getOperand(0)->getType()->getScalarSizeInBits();
  } else if (auto *Call = dyn_cast<CallInst>(Inst)) {
    OpStr = Call->getCalledFunction()->getName().str();
    while (isdigit(OpStr.back())) {
      OpStr.pop_back();
    }
  } else {
    OpStr = Inst->getOpcodeName();
    if (Acc) {
      if (!Predicated) {
        OpStr = OpStr[0] == 'f' ? "fadd" : "add";
      } else {
        OpStr = OpStr[0] == 'f' ? "faccumulate" : "accumulate";
      }
    }
  }

  for (int i = 0, e = (OpStr[0] == 'f') + 1; i < e; ++i) { // NOLINT
    OpStr[i] -= 'a';
    OpStr[i] += 'A';
  }

  return formatv("{0}_{1}{2}", OpStr, TyStr, BitWidth);
}

/*!
 * \brief I anyways need the DFG entries to be reordered in which the order the
 *        are emitted.
 * \param DB The DFG to reorder the entries.
 */
static std::vector<DFGEntry *> ReorderEntries(DFGBase *DB) { // NOLINT
  std::vector<DFGEntry *> Res;
  Res.reserve(DB->Entries.size());
  for (auto *Elem : DB->EntryFilter<InputPort>()) {
    Res.push_back(Elem);
  }
  for (auto *Elem : DB->Entries) {
    if (isa<InputPort>(Elem) || isa<OutputPort>(Elem)) {
      continue;
    }
    Res.push_back(Elem);
  }
  for (auto *Elem : DB->EntryFilter<OutputPort>()) {
    Res.push_back(Elem);
  }
  return Res;
}

struct DFGPrinter : dsa::DFGVisitor {

  struct ControlBit {
    std::ostringstream SubCtrl[3];
    Predicate *Pred{nullptr};

    void addControlledMemoryStream(int Idx, DFGEntry *DE) {
      if (auto *CMP = dyn_cast<CtrlMemPort>(DE)) {
        if (Pred == nullptr) {
          Pred = CMP->Pred;
        } else {
          DSA_CHECK(Pred == CMP->Pred) << "An instruction cannot be controlled by "
                                      "more than one predication.";
        }
        assert(Pred);
        for (int j = 0; j < 3; ++j) { // NOLINT
          if (~CMP->Mask >> j & 1) {
            if (!SubCtrl[j].str().empty()) {
              SubCtrl[j] << "|";
            }
            SubCtrl[j] << "b" << (Idx + 1);
          }
        }
      }
    }

    bool empty() {
      for (int i = 0; i < 3; ++i) // NOLINT
        if (!SubCtrl[i].str().empty())
          return false;
      return true;
    }

    std::string finalize() {
      std::ostringstream Ctrl;
      for (int i = 0; i < 3; ++i) { // NOLINT
        if (!SubCtrl[i].str().empty()) {
          if (!Ctrl.str().empty())
            Ctrl << ", ";
          Ctrl << i << ":" << SubCtrl[i].str();
        }
      }
      return Ctrl.str();
    }

    void updateAbstain(int x, bool isAcc) { // NOLINT
      for (int i = 0; i < 3; ++i) { // NOLINT
        if (x >> i & 1) {
          if (!SubCtrl[i].str().empty()) {
            SubCtrl[i] << "|";
          }
          if (isAcc) {
            SubCtrl[i] << "a";
          } else {
            SubCtrl[i] << "d";
          }
        } else if (isAcc) {
          if (!SubCtrl[i].str().empty()) {
            SubCtrl[i] << "|";
          }
          SubCtrl[i] << "d";
        }
      }
    }
  };

  struct DFGEntryEmitter : DFGEntryVisitor {
    void Visit(DFGEntry *DE) override {
      OS << "# [" << KindStr[DE->Kind] << "]: DFG" << DE->Parent->ID << " Entry"
         << DE->ID << "\n";
      int i = 0; // NOLINT
      auto Insts = DE->underlyingInsts();
      for (auto *Elem : Insts) {
        OS << "# Inst";
        if (Insts.size() != 1) {
          OS << i++;
        }
        OS << ": " << *Elem << "\n";
      }
    }

    void Visit(Accumulator *Acc) override {

      Visit(cast<DFGEntry>(Acc));
      auto *Inst = Acc->Operation;
      auto Reduce = getOperationStr(Inst, false, false);
      ControlBit CtrlBit;

      std::queue<std::string> ReduceQ;
      for (int i = 0; i < Acc->Parent->getUnroll(); ++i) { // NOLINT
        for (size_t j = 0; j < 2; ++j) { // NOLINT
          auto *Operand = Inst->getOperand(j);
          if (!isa<PHINode>(Operand)) {
            auto *Entry = Acc->Parent->InThisDFG(Operand);
            DSA_CHECK(Entry);
            ReduceQ.push(Entry->name(i));
          }
        }
      }

      while (ReduceQ.size() > 1) {
        auto A = ReduceQ.front();
        ReduceQ.pop();
        DSA_CHECK(!ReduceQ.empty());
        auto B = ReduceQ.front();
        ReduceQ.pop();
        OS << formatv("TMP{0} = {1}({2}, {3})", Parent->TmpCnt, Reduce, A, B).str() << "\n";
        ReduceQ.push(formatv("TMP{0}", Parent->TmpCnt++));
      }

      auto *P = Acc->getPredicate();
      auto Op = getOperationStr(Inst, true, P != nullptr);

      if (P) {
        OS << Acc->name() << " = " << Op << "(" << ReduceQ.front();
      } else {
        OS << "#pragma $Reg0 " << Acc->name() << "\n";
        OS << Acc->name() << " = " << Op << "(" << ReduceQ.front() << ", $Reg0";
      }

      if (dsa::utils::ModuleContext().PRED) {
        if (P || !CtrlBit.empty()) {
          CtrlBit.updateAbstain(Acc->getAbstainBit(), true);
          OS << ", ctrl=" << P->name(-1) << "{" << CtrlBit.finalize() << "}";
        } else {
          struct TagNamer : DFGEntryVisitor {
            std::string wrap(const std::string &S) {
              return '$' + S + "State & " + ResetLevel;
            }
            void Visit(SLPMemPort *SMP) {
              DSA_CHECK(Name.empty());
              Name = wrap(formatv("ICluster_{0}_{1}_", SMP->Parent->ID, SMP->ID));
            }
            void Visit(MemPort *MP) {
              DSA_CHECK(Name.empty());
              Name = wrap(MP->name(-1));
            }
            void Visit(IndMemPort *IMP) {
              DSA_CHECK(Name.empty());
              Name = dsa::utils::ModuleContext().IND ? wrap(IMP->name(-1)) : IMP->TagString;
            }
            std::string Name;
            std::string ResetLevel;
          };
          auto &Entry = Parent->DAR.AI[Acc];
          // TODO(@were): Confirm this is correct.
          TagNamer TN;
          for (auto *IP : Acc->Parent->EntryFilter<InputPort>()) {
            auto Iter = std::find(IP->Tagged.begin(), IP->Tagged.end(), Acc);
            if (Iter != IP->Tagged.end()) {
              TN.ResetLevel = std::to_string(tagBitmask(Entry.ResetLevel));
              IP->accept(&TN);
              OS << ", ctrl=" << TN.Name << "{";
            }
          }
          DSA_CHECK(!TN.Name.empty()) << Acc->dump() << " not tagged!";
          if (Entry.ResetLevel == Entry.ProduceLevel) {
            OS << "0: d, " << tagBitmask(Entry.ResetLevel) << ": r}";
          } else {
            DSA_CHECK(Entry.ProduceLevel == -1) << Entry.ProduceLevel << " " << Entry.ResetLevel;
            OS << tagBitmask(Entry.ResetLevel) << ": r}";
          }
          DSA_LOG(CODEGEN) << Acc->dump() << ", ResetLevel: " << Entry.ResetLevel;
          DSA_LOG(CODEGEN) << "BMSS: " << tagBitmask(Entry.ResetLevel);
        }
      }

      OS << ")\n";
      ++AccIdx;
    }

    void Visit(InputConst *IC) override {
      Visit(cast<DFGEntry>(IC));
      OS << "Input" << IC->Val->getType()->getScalarSizeInBits() << ": "
         << IC->name() << "\n";
    }

    void Visit(IndMemPort *IMP) override {
      if (IMP->duplicated()) {
        return;
      }
      Visit(static_cast<InputPort*>(IMP));
    }

    void Visit(InputPort *IP) override {
      if (!utils::ModuleContext().PRED) {
        for (auto *User : IP->underlyingInst()->users()) {
          auto *Entry = IP->Parent->InThisDFG(User);
          if (Entry && !isa<Predicate>(Entry)) {
            return;
          }
        }
      }
      Visit(cast<DFGEntry>(IP));
      {
        using dfg::MetaPort;
        auto Meta = IP->Meta;
        if (Meta.source != MetaPort::Data::Unknown) {
          OS << "#pragma src=" << dfg::MetaPort::DataText[(int)Meta.source]
             << "\n";
        }
        if (Meta.dest != MetaPort::Data::Unknown) {
          OS << "#pragma dest=" << dfg::MetaPort::DataText[(int)Meta.dest]
             << "\n";
        }
        if (!Meta.dest_port.empty()) {
          OS << "#pragma dest=" << Meta.dest_port << "\n";
        }
        for (int i = 0; i < (int)MetaPort::Operation::Unknown; ++i) { // NOLINT
          if (Meta.op >> i & 1) {
            OS << "#pragma op=" << MetaPort::OperationText[i] << "\n";
          }
        }
        if (Meta.conc) {
          OS << "#pragma conc=" << Meta.conc << "\n";
        }
        OS << "#pragma cmd=" << Meta.cmd << "\n";
        OS << "#pragma repeat=" << Meta.repeat << "\n";
      }

      OS << "Input" << IP->underlyingInst()->getType()->getScalarSizeInBits()
         << ": " << IP->name();
      if (IP->shouldUnroll()) {
        OS << "[" << IP->Parent->getUnroll() << "]";
      }
      bool Signaled = false;
      if (!IP->Tagged.empty()) {
        if (isa<MemPort>(IP) || (isa<IndMemPort>(IP) && dsa::utils::ModuleContext().IND)) {
          OS << " stated";
          IP->TagString = '$' + IP->name() + "State";
        } else if (isa<IndMemPort>(IP) && !IP->Tagged.empty()) {
          Signaled = true;
        }
      }
      OS << "\n";
      if (Signaled) {
        OS << "Input: " << IP->name() << "_signal\n";
        IP->TagString = IP->name() + "_signal";
      }
    }

    void Visit(ComputeBody *CB) override {
      // If this ComputeBody is handled by a atomic operation skip it!
      if (CB->isAtomic()) {
        return;
      }

      Visit(cast<DFGEntry>(CB));

      int Degree = (CB->shouldUnroll() ? CB->Parent->getUnroll() : 1);
      for (int vec = 0; vec < Degree; ++vec) { // NOLINT
        OS << CB->name(vec) << " = "
           << getOperationStr(CB->Operation, false, false) << "(";
        ControlBit CtrlBit;

        bool FuncCall = isa<CallInst>(CB->Operation); // NOLINT
        for (int i = 0; i < (int)(CB->Operation->getNumOperands() - FuncCall); ++i) { // NOLINT
          auto *Val = CB->Operation->getOperand(i);
          if (i)
            OS << ", ";
          if (auto *EntryOp = CB->Parent->InThisDFG(Val)) {
            OS << CB->Parent->nameOf(Val, vec);
            CtrlBit.addControlledMemoryStream(i, EntryOp);
          } else {
            OS << ValueToOperandText(Val);
          }
        }

        if (utils::ModuleContext().PRED) {
          if (CB->getPredicate())
            CtrlBit.updateAbstain(CB->getAbstainBit(), false);
          if (!CtrlBit.empty()) {
            OS << ", ctrl=" << CtrlBit.Pred->name(vec) << "{"
               << CtrlBit.finalize() << "}";
          }
        }

        if (auto *CI = dyn_cast<CmpInst>(CB->Operation)) {
          int Pred = 0;
          switch (CI->getPredicate()) {
          // <
          case llvm::CmpInst::Predicate::FCMP_OLT:
          case llvm::CmpInst::Predicate::ICMP_SLT:
            Pred |= 1;
            break;
          // ==
          case llvm::CmpInst::Predicate::FCMP_OEQ:
          case llvm::CmpInst::Predicate::ICMP_EQ:
            Pred |= 2;
            break;
          // >
          case llvm::CmpInst::Predicate::FCMP_OGT:
          case llvm::CmpInst::Predicate::ICMP_SGT:
            Pred |= 4;
            break;
          default:
            DSA_CHECK(false) << CI->getPredicate();
          }
          OS << ", " << Pred;
        }

        OS << ")\n";
      }
    }

    // TODO(@were): Support unroll
    void Visit(SLPMemPort *SMP) override {
      int Degree = (SMP->shouldUnroll() ? SMP->Parent->getUnroll() : 1);
      OS << "# Cluster " << SMP->ID << "\n";
      for (int i = 0; i < (int) SMP->Coal.size(); ++i) { // NOLINT
        Visit(static_cast<DFGEntry*>(SMP->Coal[i]));
      }
      int Bits = SMP->Coal[0]->underlyingInst()->getType()->getScalarSizeInBits();
      int Lanes = SMP->Coal.size();
      std::string Name = formatv("ICluster_{0}_{1}_", SMP->Parent->ID, SMP->ID);
      OS << "# Vector Port Width: " << Lanes << " * " << Degree << "\n";
      OS << "Input" << Bits << ": " << Name << "[" << Lanes * Degree << "]";
      if (!SMP->Tagged.empty()) {
        OS << " stated";
      }
      OS << "\n";
      int Idx = 0;
      for (int i = 0; i < Degree; ++i) { // NOLINT
        for (int j = 0; j < (int) SMP->Coal.size(); ++j) { // NOLINT
          auto *Val = SMP->Coal[j]->underlyingInst();
          OS << SMP->Parent->nameOf(Val, i) << " = " << Name << Idx << "\n";
          ++Idx;
        }
      }
    }

    void Visit(SLPPortMem *SPM) override {
      int Degree = (SPM->shouldUnroll() ? SPM->Parent->getUnroll() : 1);
      int Lanes = SPM->Coal.size();
      int Bits = SPM->Coal[0]->Store->getValueOperand()->getType()->getScalarSizeInBits();
      OS << "# Cluster " << SPM->ID << "\n";
      std::string Name = formatv("OCluster_{0}_{1}_", SPM->Parent->ID, SPM->ID);
      for (int i = 0; i < (int) SPM->Coal.size(); ++i) { // NOLINT
        Visit(static_cast<DFGEntry*>(SPM->Coal[i]));
      }
      int Idx = 0;
      for (int i = 0; i < Degree; ++i) { // NOLINT
        for (int j = 0; j < (int) SPM->Coal.size(); ++j) { // NOLINT
          auto *Val = SPM->Coal[j]->Store->getValueOperand();
          OS << Name << Idx << " = " << SPM->Parent->nameOf(Val, i) << "\n";
          ++Idx;
        }
      }
      OS << "# Vector Port Width: " << Lanes << " * " << Degree << "\n";
      OS << "Output" << Bits << ":" << Name << "[" << Lanes * Degree << "]" << "\n";
    }

    void Visit(AtomicPortMem *APM) override {
      // TODO(@were): Support more complicated DFG. For now a single operand DFG is supported.
      if (APM->Parent->Entries.size() == 3) {
        auto Name = formatv("sub{0}_v{1}_", APM->Parent->ID, APM->ID);
        int DBits = APM->Op->getType()->getScalarSizeInBits();
        OS << "Input" << DBits << ": Operand_" << Name << "\n";
        OS << Name << " = Operand_" << Name << "\n";
        OS << "Output" << DBits << ": " << Name << "\n";
      } else if (!APM->Operand) {
        Visit(static_cast<OutputPort*>(APM));
      } else {
        DSA_CHECK(false) << "Not supported yet!";
      }
    }

    void Visit(Predicate *P) override {
      if (!utils::ModuleContext().PRED) {
        return;
      }

      {
        // TODO(@were): Finalize this.
        OS << "# [Predication] Combination\n";
        for (auto *I : P->Cond) {
          OS << "# " << *I << "\n";
        }
      }

      ControlBit CtrlBit;
      OS << P->name(-1) << " = Compare"
         << P->Cond[0]->getOperand(0)->getType()->getScalarSizeInBits() << "(";
      for (size_t i = 0; i < P->Cond[0]->getNumOperands(); ++i) { // NOLINT
        auto *Val = P->Cond[0]->getOperand(i);
        if (i) {
          OS << ", ";
        }
        if (auto *EntryOp = P->Parent->InThisDFG(Val)) {
          OS << EntryOp->name(-1);
          CtrlBit.addControlledMemoryStream(i, EntryOp);
          if (auto *CMP = dyn_cast<CtrlMemPort>(EntryOp)) {
            CMP->ForPredicate = true;
          }
        } else {
          OS << ValueToOperandText(Val);
        }
      }

      if (!CtrlBit.empty()) {
        if (CtrlBit.Pred == P)
          OS << ", self=";
        else
          OS << ", ctrl=" << CtrlBit.Pred->name(-1);
        OS << "{" << CtrlBit.finalize() << "}";
      }

      OS << ")\n";
    }

    void Visit(OutputPort *OP) override {
      Visit(cast<DFGEntry>(OP));
      std::ostringstream OSS;
      OP->Meta.to_pragma(OSS);
      OS << OSS.str();
      auto *Entry = OP->Parent->InThisDFG(OP->Output);
      DSA_CHECK(Entry);
      int N = (Entry->shouldUnroll() ? OP->Parent->getUnroll() : 1);
      for (int i = 0; i < N; ++i) { // NOLINT
        auto LHS = OP->name(i);
        auto RHS = Entry->name(i);
        OS << LHS << " = " << RHS << "\n";
      }
      OS << "Output" << OP->Output->getType()->getScalarSizeInBits() << ": "
         << OP->name();
      if (Entry->shouldUnroll())
        OS << "[" << OP->Parent->getUnroll() << "]";
      OS << "\n";
    }

    raw_ostream &OS;
    DFGPrinter *Parent;
    /*!
     * \brief The index of the accumulator to be emitted.
     */
    int AccIdx{0};

    DFGEntryEmitter(raw_ostream &OS, DFGPrinter *Parent) : OS(OS), Parent(Parent) {}
  };

  void Visit(DedicatedDFG *DD) override {
    if (utils::ModuleContext().TRIGGER || DD->GoTemporal) {
      DSA_CHECK(utils::ModuleContext().TEMPORAL)
          << "Trigger cannot be enabled without temporal";
      OS << "#pragma group temporal\n";
    }
    DFGVisitor::Visit(DD);
  }

  void Visit(TemporalDFG *TD) override {
    OS << "#pragma group temporal\n";
    DFGVisitor::Visit(TD);
  }

  void Visit(DFGBase *DB) override {
    // FIXME(@were): Add block freqency an attribute of DFG.
    // auto BF = Parent->Query->BFI->getBlockFreq(getBlocks()[0]);
    // os << "#pragma group frequency " << 1 << "\n";
    OS << "#pragma group unroll " << DB->getUnroll() << "\n";

    auto Reordered = ReorderEntries(DB);

    DFGEntryEmitter DEE(OS, this);
    for (auto *Elem : Reordered) {
      Elem->accept(&DEE);
    }

    // TODO(@were): Bing this back for atomic operations.
    // /// Emit intermediate result for atomic operation
    // for (auto Elem : EntryFilter<ComputeBody>())
    //   Elem->EmitAtomic(os);

    // TODO(@were): Move this to a DFG.
    if (dsa::utils::ModuleContext().IND) {
      for (auto *Elem : DB->EntryFilter<IndMemPort>()) {
        auto *DS = analysis::extractStreamIntrinsics(Elem, CGC, DAR);
        bool Penetrate = !Elem->Tagged.empty() && isa<Indirect1D>(DS);
        OS << "\n\n----\n\n";
        OS << "Input" << Elem->Index->Load->getType()->getScalarSizeInBits()
           << ": indirect_in_" << DB->ID << "_" << Elem->ID << "_";
        bool Unrolled = false;
        if (Elem->shouldUnroll()) {
          Unrolled = true;
          OS << "[" << Elem->Parent->getUnroll() << "]";
        }
        if (Penetrate) {
          OS << " stated";
        }
        OS << "\n";
        if (Unrolled) {
          for (int i = 0; i < Elem->Parent->getUnroll(); ++i) { // NOLINT
            OS << "indirect_out_" << DB->ID << "_" << Elem->ID << "_" << i << " = "
               << "indirect_in_" << DB->ID << "_" << Elem->ID << "_" << i << "\n";
          }
        } else {
          OS << "indirect_out_" << DB->ID << "_" << Elem->ID << "_" << " = "
             << "indirect_in_" << DB->ID << "_" << Elem->ID << "_\n";
        }
        OS << "Output" << Elem->Index->Load->getType()->getScalarSizeInBits()
           << ": indirect_out_" << DB->ID << "_" << Elem->ID << "_";
        if (Elem->shouldUnroll()) {
          Unrolled = true;
          OS << "[" << Elem->Parent->getUnroll() << "]";
        }
        if (Penetrate) {
          OS << " state=indirect_in_" << DB->ID << "_" << Elem->ID << "_";
        }
        OS << "\n";
        if (auto *S2D = dyn_cast<Indirect2D>(DS)) {
          if (!isa<analysis::LoopInvariant>(S2D->L1D)) {
            auto *DFG = new DedicatedDFG(DB->Parent, S2D->L1D);
            DFG->UnrollFactor = 1;
            S2D->L1DDFG = DFG;
            auto *DD = dyn_cast<DedicatedDFG>(DB);
            DSA_CHECK(DD);
            DFG->LoopNest = DD->LoopNest;
            DFG->LoopNest.erase(DFG->LoopNest.begin());
            DB->Parent->DFGs.push_back(DFG);
            DAR.DLI.push_back(DAR.DLI[Elem->Parent->ID]);
            DAR.DLI.back().TripCount.erase(DAR.DLI.back().TripCount.begin());
            DAR.DLI.back().LoopNest.erase(DAR.DLI.back().LoopNest.begin());
            auto *SW = DAR.affineMemoryAccess(S2D->L1DDFG->Entries[0], CGC.SE, false);
            (void) SW;
          }
        }
      }
    }
  }

  raw_ostream &OS;
  /*!
   * \brief Count the ticker of temp variables for accumulator reduction.
   */
  int TmpCnt{0};

  /*!
   * \brief Clustered output should be delayed.
   */
  std::vector<std::string> DelayEmission;
  /*!
   * \brief The scalar evolution for access analysis.
   */
  ScalarEvolution &SE;
  /*!
   * \brief
   */
  std::unordered_map<DFGEntry*, xform::DataStream*> &Streams;

  CodeGenContext &CGC;
  analysis::DFGAnalysisResult &DAR;

  DFGPrinter(raw_ostream &OS, CodeGenContext &CGC, analysis::DFGAnalysisResult &DAR)
    : OS(OS), SE(CGC.SE), Streams(DAR.Streams), CGC(CGC), DAR(DAR) {}
};

void emitDFG(raw_ostream &OS, DFGFile *DFG, analysis::DFGAnalysisResult &DAR,
             CodeGenContext &CGC) {
  auto &Graphs = DFG->DFGs;
  auto &SI = DAR.SI;
  for (int i = 0; i < (int)Graphs.size(); ++i) { // NOLINT
    DSA_LOG(DFG) << "========== " << i << " ==========";
    for (auto *Elem : Graphs[i]->Entries) {
      DSA_LOG(DFG) << Elem->dump();
    }
  }
  for (int i = 0; i < (int)Graphs.size(); ++i) { // NOLINT
    DFGPrinter DP(OS, CGC, DAR);
    auto *Elem = Graphs[i];
    if (i) {
      OS << "----\n";
    }
    Elem->accept(&DP);
    for (auto &CO : DP.DelayEmission) {
      OS << CO << "\n";
    }
  }
  for (int i = 0; i < (int) SI.Buffet.size(); ++i) { // NOLINT
    OS << "----\n";
    OS << "Input: IBuffet_" << i << "_\n"
       << "OBuffet_" << i << "_ = " << "IBuffet_" << i << "_\n"
       << "Output: OBuffet_" << i << "_\n";
  }
}

void CodeGenContext::injectFusionHints(std::string Mnemonic, REG &a, REG &b, int c) { // NOLINT
  // Convert an int-like value to the exact int64 type.
  auto MakeInt64 = [this](Value *Val) -> Value * {
    if (Val->getType()->isPointerTy()) {
      return IB->CreatePtrToInt(Val, IB->getInt64Ty());
    }
    auto *Ty = IB->getIntNTy(Val->getType()->getScalarSizeInBits());
    auto *RI = IB->CreateBitCast(Val, Ty);
    if (RI->getType()->getScalarSizeInBits() < 64) {
      RI = IB->CreateSExt(RI, IB->getInt64Ty());
    }
    return RI;
  };

  if (!utils::ModuleContext().FUSION) {
    return;
  }
  if (Mnemonic != "ss_cfg_param") {
    return;
  }
  if (c == 98) {
    return;
  }
  for (int i = 0; i < 2; ++i) { // NOLINT
    int Idx = (c >> (i * 5)) & 31; 
    int Sticky = (c >> (10 + i)) & 1;
    if (Idx) {
      auto *AA = IB->CreateLoad(Regs[Idx].Reg);
      auto *AS = IB->CreateLoad(Regs[Idx].Sticky);
      auto *AV = MakeInt64(a.value(IB));
      IB->CreateStore(AV, Regs[Idx].Reg);
      IB->CreateStore(IB->getInt8(Sticky), Regs[Idx].Sticky);
      intrinsicImpl("equal.hint.v1", "r", {IB->CreateICmpEQ(AA, AV)},
                    IB->getVoidTy());
      intrinsicImpl("equal.hint.s1", "r",
                    {IB->CreateICmpEQ(AS, IB->getInt8(Sticky))},
                    IB->getVoidTy());
      auto *V = IB->CreateLoad(Regs[Idx].Reg);
      (i ? b : a) = V;
    }
  }
}

void CodeGenContext::intrinsicImpl(const std::string &Mnemonic,
                                   const std::string &OpConstrain,
                                   const std::vector<Value *> &Args,
                                   Type *ResTy) {
  std::ostringstream MOSS;
  MOSS << Mnemonic << " $0";
  for (int i = 0, n = OpConstrain.size(), j = 1; i < n; ++i) { // NOLINT
    if (OpConstrain[i] == ',') {
      MOSS << ", $" << j;
      ++j;
    }
  }
  std::vector<Type *> Types;
  for (auto *Arg : Args) {
    Types.push_back(Arg->getType());
  }
  auto *FTy = FunctionType::get(ResTy, Types, false);
  auto *IA = InlineAsm::get(FTy, MOSS.str(), OpConstrain, true);
  Res.push_back(IB->CreateCall(IA, Args));
  // if (Mnemonic == "ss_lin_strm" || Mnemonic == "ss_ind_strm" ||
  //     Mnemonic == "ss_recv" || Mnemonic == "ss_wr_rd") {
  //   for (int i = 0; i < DSARF::TOTAL_REG; ++i) { // NOLINT
  //     auto *C = IB->CreateTrunc(IB->CreateLoad(Regs[i].Sticky), IB->getInt1Ty());
  //     auto *SV = IB->CreateLoad(Regs[i].Reg);
  //     auto *Reset = IB->CreateSelect(C, SV, IB->getInt64(REG_STICKY[i]));
  //     IB->CreateStore(Reset, Regs[i].Reg);
  //   }
  // }
}

void injectConfiguration(CodeGenContext &CGC, analysis::ConfigInfo &CI,
                         Instruction *Start, Instruction *End) {
  auto *IB = CGC.IB;
  IB->SetInsertPoint(Start);

  GlobalVariable *GV;
  if (utils::ModuleContext().BITSTREAM) {
    int64_t *DPtr = (int64_t*)(const_cast<char*>(CI.Bitstream.data()));
    ArrayRef<int64_t> A(DPtr, DPtr + CI.Size);
    Constant *AConst = ConstantDataArray::get(IB->getContext(), A);
    auto *M = Start->getParent()->getParent()->getParent();
     GV = new GlobalVariable(
        *M, AConst->getType(), true, GlobalValue::PrivateLinkage,
        AConst, CI.Name, nullptr, GlobalVariable::NotThreadLocal, GlobalValue::ExternalLinkage);
    GV->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    GV->setAlignment(Align(16));
  } else {
    GV = IB->CreateGlobalString(CI.Bitstream, CI.Name + "_bitstream",
                                      GlobalValue::ExternalLinkage);
    GV->setAlignment(Align(8));
  }
  CGC.SS_CONFIG(GV, IB->getInt64(CI.Size));
  IB->SetInsertPoint(End);
  CGC.SS_WAIT_ALL();
}


/*!
 * \brief Emit port repeat operands;
 *        Note: First is repeat, the raw value. Second is stretch, already shifted by fixed-point.
 * \param CGC The DSA code generator wrapper.
 * \param Loops The loop nest of repeat.
 * \param N The index of loop invariant.
 * \param Unroll The unrolling degree.
 */
std::pair<Value*, Value*>
injectComputedRepeat(CodeGenContext &CGC, // NOLINT
                     std::vector<dsa::analysis::SEWrapper*> Loops, int N,
                     int Unroll, bool ConstRepeat) {
  auto *IB = CGC.IB;
  auto &SEE = CGC.SEE;
  Value *Repeat = IB->getInt64(1);
  Value *Stretch = nullptr;
  auto FWrapUp = [&IB, ConstRepeat](Value *Val){
    if (!ConstRepeat) {
      Val = IB->CreateMul(Val, IB->getInt64(1 << DSA_REPEAT_DIGITAL_POINT));
    }
    return Val;
  };

  switch (N) {
  case 1: {
    const SCEV *Base = Loops[0]->base();
    if (auto *LI = dyn_cast<analysis::LinearCombine>(Loops[0])) {
      Stretch = SEE.expandCodeFor(LI->Coef[0]->base());
      Stretch = IB->CreateMul(Stretch, IB->getInt64(1 << DSA_REPEAT_DIGITAL_POINT));
      Stretch = IB->CreateSDiv(Stretch, IB->getInt64(Unroll));
    }
    auto *Dim0 = SEE.expandCodeFor(Base);
    if (Stretch) {
      Repeat = IB->CreateMul(Dim0, IB->getInt64(1 << DSA_REPEAT_DIGITAL_POINT));
      Repeat = IB->CreateSDiv(Repeat, IB->getInt64(Unroll));
    } else {
      Repeat = CeilDiv(Dim0, IB->getInt64(Unroll), IB);
      Repeat = FWrapUp(Repeat);
    }
    DSA_LOG(CODEGEN) << *Repeat;
    break;
  }
  case 2: {
    auto *Outer = dyn_cast<analysis::LoopInvariant>(Loops[1]);
    DSA_CHECK(Outer);
    auto *Dim1 = SEE.expandCodeFor(Outer->Raw);
    if (auto *LC = dyn_cast<analysis::LinearCombine>(Loops[0])) {
      DSA_INFO << LC->toString();
      auto *Dim0 = SEE.expandCodeFor(LC->Base->Raw);
      if (Unroll == 1) {
        // (Dim0 + Dim0 + (Dim1 - 1) * Stretch) * Dim1 / 2
        // TODO(@were): I am not sure...
        Stretch = SEE.expandCodeFor(LC->Coef[0]->Raw);
        auto *Dim0x2 = IB->CreateAdd(Dim0, Dim0);
        auto *Delta = IB->CreateMul(Stretch, IB->CreateSub(Dim1, IB->getInt64(1)));
        auto *Last = IB->CreateAdd(Dim0x2, Delta);
        Repeat = IB->CreateSDiv(IB->CreateMul(Last, Dim0), IB->getInt64(2));
        Stretch = nullptr;
        DSA_INFO << "Stretched 2-D Repeat: " << *Repeat;
        Repeat = FWrapUp(Repeat);
      } else if (Unroll == 2) {
        auto *Dim1Add1 = IB->CreateAdd(Dim1, IB->getInt64(1));
        auto *Dim1Sqr = IB->CreateMul(Dim1Add1, Dim1Add1);
        Repeat = IB->CreateSDiv(Dim1Sqr, IB->getInt64(4));
        Stretch = nullptr;
        DSA_INFO << *Repeat;
        DSA_INFO << *Dim1 << " " << LC->toString();
        DSA_INFO << LC->Base->toString();
        Repeat = FWrapUp(Repeat);
        DSA_INFO << *Repeat;
      }
    } else {
      auto *Dim0 = SEE.expandCodeFor(Loops[0]->Raw);
      Repeat = IB->CreateMul(CeilDiv(Dim0, IB->getInt64(Unroll), IB), Dim1);
      DSA_LOG(CODEGEN) << *Repeat;
      Repeat = FWrapUp(Repeat);
    }
    break;
  }
  case 3:
    auto *Dim0 = SEE.expandCodeFor(Loops[0]->Raw);
    auto *Dim1 = SEE.expandCodeFor(Loops[1]->Raw);
    auto *Dim2 = SEE.expandCodeFor(Loops[2]->Raw);
    Repeat = IB->CreateMul(CeilDiv(Dim0, IB->getInt64(Unroll), IB), Dim1);
    Repeat = IB->CreateMul(Repeat, Dim2);
    FWrapUp(Repeat);
    Stretch = nullptr;
    // DSA_CHECK(N == 0) << "TODO: Support N == " << N << " later";
    break;
  }
  return {Repeat, Stretch};
}


void injectLinearStreamImpl(CodeGenContext &CGC, analysis::SEWrapper *SW,
                              int Port, int Unroll, int DType, MemoryOperation MO,
                              Padding P, analysis::SpadInfo &SI, int BuffetIdx) {
  analysis::LinearCombine *LCPtr = dyn_cast<analysis::LinearCombine>(SW);
  if (!LCPtr) {
    auto *LI = dyn_cast<analysis::LoopInvariant>(SW);
    DSA_CHECK(LI) << SW->toString();
    LCPtr = LI->toLinearCombine(&CGC.SE);
  }
  analysis::LinearCombine &LC = *LCPtr;

  auto InjectRepeat = [&CGC](analysis::LinearCombine &LI, int Port, int Unroll) {
    auto &Loops = LI.TripCount;
    DSA_CHECK(Loops.size() == LI.Coef.size() || LI.Coef.empty());
    int N = LI.Coef.empty() ? Loops.size() : LI.partialInvariant();
    auto CR = injectComputedRepeat(CGC, Loops, N, Unroll, false);
    auto *Repeat = CR.first;
    auto *Stretch = CR.second;
    if (auto *CI = dyn_cast<ConstantInt>(Repeat)) {
      if (CI->getSExtValue() == 1) {
        return;
      }
    }
    CGC.SS_CONFIG_PORT(Port, DPF_PortRepeat, Repeat);
    if (Stretch) {
      CGC.SS_CONFIG_PORT(Port, DPF_PortRepeatStretch, Stretch);
    }
  };

  auto LinearInstantiation = [&CGC](analysis::LinearCombine *LC, int Port,
                                    MemoryOperation MO, Padding P, analysis::SpadInfo &SI,
                                    int BuffetIdx, int DType) {
    DSA_LOG(CODEGEN) << LC->toString();
    auto *IB = CGC.IB;
    auto &SEE = CGC.SEE;
    auto *Start = SEE.expandCodeFor(LC->Base->Raw);
    auto MT = SI.isSpad(Start) ? DMT_SPAD : DMT_DMA;
    if (LC->Coef.empty()) {
      CGC.INSTANTIATE_1D_STREAM(Start, IB->getInt64(0), IB->getInt64(1), Port, P,
                                DSA_Access, MO, MT, DType, 0);
      return;
    }
    auto &Loops = LC->TripCount;
    int Dim = Loops.size() - LC->partialInvariant();
    DSA_CHECK(0 <= Dim && Dim <= 3) << Dim;
    // if (const auto *LII = LI.invariant()) {
    //   CGC.INSTANTIATE_1D_STREAM(SEE.expandCodeFor(LII), IB->getInt64(0),
    //                             IB->getInt64(1), Port, P, DSA_Access, MO, MT,
    //                             DType, 0);
    //   return;
    // }
    int i = LC->partialInvariant(); // NOLINT
    std::vector<Value*> N;
    std::vector<Value*> Stride;
    for (int j = i; j < (int) Loops.size(); ++j) { // NOLINT
      N.push_back(SEE.expandCodeFor(Loops[j]->base()));
      Stride.push_back(SEE.expandCodeFor(LC->Coef[j]->base()));
    }
    switch (Dim) {
    case 0: {
      CGC.INSTANTIATE_1D_STREAM(Start, IB->getInt64(0), IB->getInt64(1), Port,
                                P, DSA_Access, MO, MT, DType, 0);
      break;
    }
    case 1: {
      auto *N1D = N[0];
      auto *Stride1D = IB->CreateSDiv(Stride[0], IB->getInt64(DType));
      CGC.INSTANTIATE_1D_STREAM(Start, Stride1D, N1D, Port, P, DSA_Access, MO, MT, DType, 0);
      DSA_LOG(CODEGEN)
        << "[1-d Linear] Start: " << *Start << ", Stride: " << *Stride1D << ", N: " << *N1D
        << ", DType: " << DType << ", Port: " << Port << " -> " << (MT == DMT_DMA ? "DMA" : "SPAD")
        << (MO == DMO_Read ? ", Read" : ", Write") << " Padding: " << P;
      break;
    }
    case 2: {
      auto *N1D = N[0];
      auto *Stride1D = IB->CreateSDiv(Stride[0], IB->getInt64(DType));
      // TODO(@were): Make assumption check!
      Value *Stretch = IB->getInt64(0);
      if (auto *LoopLC = dyn_cast<analysis::LinearCombine>(Loops[i])) {
        Stretch = SEE.expandCodeFor(LoopLC->Coef[0]->base());
      }
      auto *N2D = N[1];
      auto *Stride2D = IB->CreateSDiv(Stride[1], IB->getInt64(DType));
      CGC.INSTANTIATE_2D_STREAM(Start, Stride1D, N1D, Stride2D, Stretch,
                                N2D, Port, P, DSA_Access, MO, MT, DType,
                                0);
      DSA_LOG(CODEGEN)
        << "[2-d Linear] Start: " << *Start << ", S1D: " << *Stride1D << ", N: " << *N1D
        << ", S2D: " << *Stride2D << ", Stretch: " << *Stretch << ", M: " << *N2D
        << ", DType: " << DType << ", Port: " << Port << " -> " << (MT == DMT_DMA ? "DMA" : "SPAD")
        << (MO == DMO_Read ? ", Read" : ", Write") << " Padding: " << P;
      break;
    }
    case 3: {
      // TODO(@were): Support 3D stretch!
      auto *Zero = IB->getInt64(0);
      auto *Stride1D = IB->CreateSDiv(Stride[0], IB->getInt64(DType));
      auto *Stride2D = IB->CreateSDiv(Stride[1], IB->getInt64(DType));
      auto *Stride3D = IB->CreateSDiv(Stride[2], IB->getInt64(DType));
      if (MO == DMO_Read && BuffetIdx >= 0 && BuffetIdx < (int) SI.Buffet.size()) {
        DSA_CHECK(MT == DMT_DMA);
        int StartSpad = std::get<1>(SI.Buffet[BuffetIdx]);
        int BufferSize = std::get<2>(SI.Buffet[BuffetIdx]);
        int LoadPort = std::get<3>(SI.Buffet[BuffetIdx]);
        int StorePort = std::get<4>(SI.Buffet[BuffetIdx]);
        // Skip the middle dimension.
        CGC.INSTANTIATE_2D_STREAM(Start, Stride1D, N[0], Stride3D, Zero, N[2],
                                  LoadPort, P, DSA_Access, MO, MT, DType, 0);
        CGC.SS_BUFFET_ALLOC(StartSpad, StartSpad + BufferSize);
        DSA_LOG(CODEGEN) << "Allocate Buffet: [" << StartSpad << ", " << StartSpad + BufferSize << ")";
        CGC.INSTANTIATE_2D_STREAM(StartSpad, Stride1D, N[0], Stride3D, Zero, N[2],
                                  StorePort, P, DSA_Access, DMO_Write, DMT_SPAD, DType, 0);
        DSA_LOG(CODEGEN)
          << "[2-d Linear] Start: " << StartSpad << ", S1D: " << *Stride1D << ", N1D: " << *N[0]
          << ", S2D: " << *Stride2D << ", N2D: " << *N[2] << ", Stride2D: " << *Stride3D
          << ", DType: " << DType << ", Port: " << Port << " -> Write Buffet";
        CGC.SS_BUFFET_ALLOC(StartSpad, StartSpad + BufferSize);
        CGC.INSTANTIATE_3D_STREAM(StartSpad, Stride1D, N[0], Stride2D, Zero, N[1],
                                  Zero, Zero, Zero, Zero, Stride3D, N[2],
                                  Port, P, DSA_Access, MO, DMT_SPAD, DType, 0);
        DSA_LOG(CODEGEN)
          << "[3-d Linear] Start: " << StartSpad << ", S1D: " << *Stride1D << ", N1D: " << *N[0]
          << ", N2D: " << *N[1] << ", S2D: " << *Stride2D << ", N3D: " << *N[2]
          << ", Stride3D: " << *Stride3D << ", DType: " << DType
          << ", Port: " << Port << " -> Read Buffet" << " Padding: " << P;
        CGC.SS_BUFFET_DEALLOC();
        DSA_LOG(CODEGEN) << "Deallocate Buffet!";
        break;
      }
      CGC.INSTANTIATE_3D_STREAM(Start, Stride1D, N[0], Stride2D, Zero, N[1],
                                Zero, Zero, Zero, Zero, Stride3D, N[2],
                                Port, P, DSA_Access, MO, MT, DType, 0);
      DSA_LOG(CODEGEN)
        << "[3-d Linear] Start: " << *Start << ", S1D: " << *Stride1D << ", N1D: " << *N[0]
        << ", N2D: " << *N[1] << ", S2D: " << *Stride2D << ", N3D: " << *N[2]
        << ", Stride3D: " << *Stride3D << ", DType: " << DType
        << ", Port: " << Port << " -> " << (MT == DMT_DMA ? "DMA" : "SPAD")
        << (MO == DMO_Read ? ", Read" : ", Write") << " Padding: " << P;
      break;
    }
    default:
      DSA_CHECK(false) << "Unsupported dimension: " << Dim;
    }
  };

  if (MO == MemoryOperation::DMO_Read) {
    InjectRepeat(LC, Port, Unroll);
  }

  LinearInstantiation(&LC, Port, MO, P, SI, BuffetIdx, DType);
}


void injectStreamIntrinsics(CodeGenContext &CGC, DFGFile &DF, analysis::DFGAnalysisResult &DAR) {

  auto DFGs = DF.DFGFilter<DFGBase>();

  struct UpdateStreamInjector : DFGEntryVisitor {

    void Visit(MemPort *MP) override {
      // No outer repeat
      auto *DFG = MP->Parent;
      if (!isa<DedicatedDFG>(DFG)) {
        return;
      }
      if (DAR.DLI[DFG->ID].TripCount.size() <= 1) {
        return;
      }
      auto *IB = CGC.IB;
      for (auto *PM : DFG->EntryFilter<PortMem>()) {
        if (!PM->isInMajor() || PM->IntrinInjected)
          continue;
        auto *Ptr0 = dyn_cast<Instruction>(MP->Load->getPointerOperand());
        auto *Ptr1 = dyn_cast<Instruction>(PM->Store->getPointerOperand());
        auto DType = MP->Load->getType()->getScalarSizeInBits() / 8;
        if (Ptr0 == Ptr1) {
          DSA_LOG(CODEGEN) << "Recurrencing: \n" << *MP->Load << "\n" << *PM->Store;
          auto *FLI = DAR.affineMemoryAccess(MP, CGC.SE, false);
          auto *LC = dyn_cast<analysis::LinearCombine>(FLI);
          DSA_CHECK(LC);
          LC = new analysis::LinearCombine(*LC);
          auto LoopN = LC->TripCount;
          // No repeat!
          if (LC->partialInvariant() != 0) {
            DSA_LOG(CODEGEN) << "Recurrence should not have inner repeat";
            return;
          }
          if (LC->Coef.size() != 2) {
            DSA_LOG(CODEGEN) << "Not a two dimension update and reduce";
            return;
          }
          // Outer should not be stretched!
          if (!isa<analysis::LoopInvariant>(LC->Coef.back())) {
            DSA_LOG(CODEGEN) << "Recurrence should not be stretched";
            return;
          }
          if (auto *O = dyn_cast<ConstantInt>(CGC.SEE.expandCodeFor(LC->Coef[1]->base()))) {
            if (O->getSExtValue()) {
              DSA_LOG(CODEGEN) << "Not a repeated update!";
              return;
            }
          }

          LC->Coef.pop_back();
          LC->TripCount.pop_back();

          injectLinearStreamImpl(
            CGC, LC, MP->SoftPortNum, DFG->getUnroll(), DType, DMO_Read,
            (Padding) MP->fillMode(), SI, -1);

          if (LoopN.size() == 2) {
            // TODO(@were): Support stretch later.
            auto *InnerN = CGC.SEE.expandCodeFor(LoopN[0]->base());
            auto *OuterN = IB->CreateSub(CGC.SEE.expandCodeFor(LoopN[1]->base()), IB->getInt64(1));
            auto *N = IB->CreateMul(InnerN, OuterN);
            DSA_LOG(CODEGEN)
              << PM->SoftPortNum << " -> " << MP->SoftPortNum
              << ", DType: " << DType << " x N: " << *N;
            CGC.SS_RECURRENCE(PM->SoftPortNum, MP->SoftPortNum, N, DType);
          } else {
            DSA_CHECK(false) << "Not supported yet";
          }

          injectLinearStreamImpl(
            CGC, LC, PM->SoftPortNum, DFG->getUnroll(), DType, DMO_Write, (Padding) 0, SI, -1);

          // Performance Model
          int II = 1;
          int Conc = -1;
          if (auto *CI = dyn_cast<ConstantInt>(CGC.SEE.expandCodeFor(LC->TripCount[0]->base()))) {
            auto CII = CI->getZExtValue();
            int CanHide = CII * DType;
            if (PM->Latency - CanHide > 0) {
              II = PM->Latency - CanHide;
              DSA_INFO << "Recur II: " << II;
            } else {
              II = 1;
              DSA_WARNING << "To hide the latency " << PM->Latency << ", "
                          << CII * DType << " elements are active";
              DSA_WARNING << "This requires a " << CanHide - PM->Latency
                          << "-deep FIFO buffer";
            }
            Conc = CII;
          } else {
            errs() << "[Warning] To hide the latency " << PM->Latency
                   << ", make sure your variable recur distance will not overwhlem "
                      "the FIFO buffer!";
          }
          PM->Meta.set("dest", "localport");
          PM->Meta.set("dest", MP->name());
          if (Conc != -1) {
            std::ostringstream OSS;
            OSS << Conc * DType;
            PM->Meta.set("conc", OSS.str());
          }
          PM->IntrinInjected = MP->IntrinInjected = true;
          return;
        }
      }
    }

    CodeGenContext &CGC;
    analysis::DFGAnalysisResult &DAR;
    analysis::SpadInfo &SI;
    UpdateStreamInjector(CodeGenContext &CGC, analysis::DFGAnalysisResult &DAR) :
      CGC(CGC), DAR(DAR), SI(DAR.SI) {}
  };

  struct StreamIntrinsicInjector : DFGEntryVisitor {

    void Visit(IndMemPort *IMP) override {
      if (IMP->IntrinInjected)
        return;

      auto *IB = CGC.IB;
      auto &SEE = CGC.SEE;

      if (!dsa::utils::ModuleContext().IND) {
        auto Inst = IB->GetInsertPoint();
        IB->SetInsertPoint(IMP->Load->getNextNode());
        CGC.SS_CONST(IMP->SoftPortNum, IMP->Load, IB->getInt64(1),
                     IMP->Load->getType()->getScalarSizeInBits() / 8);
        DSA_LOG(CODEGEN) << IMP->SoftPortNum << " <- " << *IMP->Load;
        if (!IMP->Tagged.empty()) {
          Value *Prod = IB->getInt64(1);
          auto &Entry = DAR.AI[IMP->Tagged[0]];
          auto &ALI = DAR.DLI[IMP->Parent->ID];
          SEE.setInsertPoint(&ALI.LoopNest[Entry.ResetLevel]->getLoopPreheader()->back());
          IB->SetInsertPoint(&ALI.LoopNest[Entry.ResetLevel]->getLoopPreheader()->back());
          for (int i = 0; i <= Entry.ResetLevel; ++i) { // NOLINT
            auto *TC = SEE.expandCodeFor(ALI.TripCount[i]->Raw);
            Prod = IB->CreateMul(Prod, TC);
            DSA_LOG(CODEGEN) << *TC;
          }
          auto *SignalVal = IB->getInt64(tagBitmask(Entry.ResetLevel));
          Prod = IB->CreateSub(Prod, IB->getInt64(1));
          DSA_LOG(CODEGEN) << IMP->SignalPort << " <- 0 x " << *Prod;
          CGC.SS_CONST(IMP->SignalPort, IB->getInt64(0), Prod);
          DSA_LOG(CODEGEN) << IMP->SignalPort << " <- " << *SignalVal << " x 1";
          CGC.SS_CONST(IMP->SignalPort, SignalVal, IB->getInt64(1));
          SEE.setInsertPoint(&*Inst);
        }
        IB->SetInsertPoint(&*Inst);
        IMP->IntrinInjected = true;
        IMP->Meta.set("src", "memory");
        IMP->Meta.set("cmd", "0.1");
        return;
      }

      if (IMP->duplicated()) {
        IMP->IntrinInjected = true;
        return;
      }

      std::vector<IndMemPort *> Together;
      std::vector<int> INDs;

      for (auto &IMP1 : IMP->Parent->EntryFilter<IndMemPort>()) {
        if (IMP1->IntrinInjected)
          continue;
        if (IMP->Index->Load == IMP1->Index->Load) {
          Together.push_back(IMP1);
          DSA_CHECK(IMP1->Index->SoftPortNum != -1) << IMP1->dump();
          INDs.push_back(IMP1->Index->SoftPortNum);
        }
      }

      DSA_CHECK(Together[0] == IMP);
      for (size_t i = 1; i < Together.size(); ++i) { // NOLINT
        CGC.SS_CONFIG_PORT(INDs[i], DPF_PortBroadcast, true);
      }

      int DType = IMP->Load->getType()->getScalarSizeInBits() / 8;

      // (DType * (?)) + %SAR
      auto *IdxLI = DAR.affineMemoryAccess(IMP, CGC.SE, false);
      int IType = 8;
      analysis::SEWrapper *Idx = nullptr;

      if (auto *SA = dyn_cast<analysis::SWBinary>(IdxLI)) {
        DSA_CHECK(SA && SA->Op == 0) << IdxLI->toString();
        Idx = SA->A;
        // const SCEV *SAR = SA->B->Raw;
        // Strip the Coef
        if (DType == 1) {
          DSA_CHECK(false) << Idx->toString();
        } else {
          auto *SM = dyn_cast<analysis::SWBinary>(Idx);
          DSA_CHECK(SM);
          if (const auto *SC = dyn_cast<SCEVConstant>(SM->A->Raw)) {
            DSA_CHECK(SC->getAPInt().getSExtValue() == DType);
          } else {
            DSA_CHECK(false);
          }
          Idx = SM->B;
        }
        if (const auto *SCE = dyn_cast<analysis::SWCast>(Idx)) {
          IType = SCE->srcTy()->getScalarSizeInBits() / 8;
          Idx = SCE->Stripped;
        }
      } else if (auto *LC = dyn_cast<analysis::LinearCombine>(IdxLI)) {
        auto *Add = dyn_cast<analysis::SWBinary>(LC->Base);
        DSA_CHECK(Add) << LC->Base->toString();
        auto *SAR = dyn_cast<analysis::LoopInvariant>(Add->B);
        auto *Mul = dyn_cast<analysis::SWBinary>(Add->A);
        DSA_CHECK(Mul) << Add->A->toString();
        auto *IndPtr = dyn_cast<analysis::IndirectPointer>(Mul->B);
        DSA_CHECK(IndPtr) << Mul->B->toString();
        injectLinearStreamImpl(CGC, IndPtr->Pointer, IMP->Index->SoftPortNum,
                               IMP->Parent->getUnroll(), IType, DMO_Read, DP_NoPadding, SI, -1);
        int LengthPort = -1;
        Value *N2D = nullptr;
        if (auto *DS = analysis::extractStreamIntrinsics(IMP, CGC, DAR)) {
          if (auto *I2D = dyn_cast<Indirect2D>(DS)) {
            if (I2D->L1DDFG) {
              DSA_LOG(CODEGEN) << "L1D Loading: ";
              I2D->L1DDFG->Entries[0]->accept(this);
              auto *OP = dyn_cast<OutputPort>(I2D->L1DDFG->Entries[1]);
              DSA_CHECK(OP);
              LengthPort = OP->SoftPortNum;
              DSA_LOG(CODEGEN) << "N1D from: " << LengthPort;
              N2D = IB->getInt64(0);
            }
          }
        }
        if (!N2D) {
          N2D = CGC.SEE.expandCodeFor(LC->TripCount[0]->Raw);
        }
        DSA_LOG(CODEGEN)
          << "[Indirect 2D] Port: " << IMP->SoftPortNum << ", DType: " << DType
          << ", SARPort: " << IMP->IndexOutPort << ", SAR: " << *SAR->Raw
          << ", IType: " << IType << ", InnerN: " << LC->TripCount[0]->toString();
        CGC.CONFIG_PARAM(DSARF::L2D, CGC.SEE.expandCodeFor(SAR->TripCount[0]->Raw), false,
                         DSARF::I1D, IB->getInt64(1), false);
        CGC.SS_INDIRECT_2D_READ(IMP->SoftPortNum, DType, IMP->IndexOutPort,
                                CGC.SEE.expandCodeFor(SAR->Raw), -1, IType, LengthPort, N2D,
                                IB->getInt64(0), DMT_DMA);
        IMP->IntrinInjected = true;
        return;
      }

      auto *IndPtr = dyn_cast<analysis::IndirectPointer>(Idx);
      bool Pene = false;
      if (!IMP->Tagged.empty()) {
        Pene = true;
      }
      injectLinearStreamImpl(CGC, IndPtr->Pointer, IMP->Index->SoftPortNum,
                             IMP->Parent->getUnroll(), IType,
                             DMO_Read, DP_NoPadding, SI, -1);

      auto *ILC = dyn_cast<analysis::LinearCombine>(IndPtr->Pointer);
      Value *N = CGC.SEE.expandCodeFor(productTripCount(ILC->TripCount, &CGC.SE));

      for (size_t i = 0; i < Together.size(); ++i) { // NOLINT
        auto *Cur = Together[i];
        auto *GEP = dyn_cast<GetElementPtrInst>(Cur->Load->getPointerOperand());
        auto MT = SI.isSpad(GEP->getOperand(0)) ? DMT_SPAD : DMT_DMA;
        CGC.INSTANTIATE_1D_INDIRECT(
            Cur->SoftPortNum, Cur->Load->getType()->getScalarSizeInBits() / 8,
            Cur->IndexOutPort, Cur->Index->Load->getType()->getScalarSizeInBits() / 8,
            GEP->getOperand(0), IB->getInt64(0), N, MT, DMO_Read, Pene && (i == 0), false);

        // TODO: Support indirect read on the SPAD(?)
        Cur->Meta.set("src", dsa::dfg::MetaPort::DataText[(int)DMT_DMA]);
        Cur->Meta.set("dest", "memory");
        Cur->Meta.set("op", "indread");

        Cur->IntrinInjected = true;
      }
    }

    void Visit(MemPort *MP) override {

      if (MP->IntrinInjected)
        return;

      // Wrappers
      auto *DFG = MP->Parent;
      int Port = MP->SoftPortNum;
      // Handle data stream with predicate
      if (MP->getPredicate()) {
        DSA_CHECK(false) << "Predicated stream should be handled in CtrlMemPort.";
      }
      int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
      auto Cond = [MP] (analysis::SpadInfo::BuffetEntry &BE) { return std::get<0>(BE) == MP; };
      auto BIter = std::find_if(SI.Buffet.begin(), SI.Buffet.end(), Cond);
      auto *IdxLI = DAR.affineMemoryAccess(MP, CGC.SE, false);
      injectLinearStreamImpl(CGC, IdxLI, Port, DFG->getUnroll(), DType, DMO_Read,
                             (Padding) MP->fillMode(), SI, BIter - SI.Buffet.begin());

      MP->IntrinInjected = true;
    }

    void Visit(SLPMemPort *SMP) override {
      auto *IB = CGC.IB;
      IB->SetInsertPoint(SMP->Parent->DefaultIP());

      // Wrappers
      auto *DFG = SMP->Parent;
      int Port = SMP->SoftPortNum;
      auto *MP = SMP->Coal[0];
      // Handle data stream with predicate
      if (MP->getPredicate()) {
        DSA_CHECK(false) << "Predicated stream should be handled in CtrlMemPort.";
      }
      int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
      auto Cond = [MP] (analysis::SpadInfo::BuffetEntry &BE) { return std::get<0>(BE) == MP; };
      auto BIter = std::find_if(SI.Buffet.begin(), SI.Buffet.end(), Cond);
      DSA_CHECK(SMP->Coal.size() >= 2);
      auto *IdxLI = DAR.affineMemoryAccess(SMP, CGC.SE, false);
      auto *LC = dyn_cast<analysis::LinearCombine>(IdxLI);
      if (!LC) {
        LC = dyn_cast<analysis::LoopInvariant>(IdxLI)->toLinearCombine(nullptr);
      }
      injectLinearStreamImpl(CGC, LC, Port, DFG->getUnroll(), DType, DMO_Read,
                             (Padding) 0, SI, BIter - SI.Buffet.begin());

      SMP->IntrinInjected = true;
    }

    void Visit(PortMem *PM) override {
      auto *DFG = PM->Parent;
      if (PM->IntrinInjected)
        return;

      CGC.IB->SetInsertPoint(DFG->DefaultIP());
      CGC.SEE.setInsertPoint(DFG->DefaultIP());
      int DType = PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8;
      auto *IdxLI = DAR.affineMemoryAccess(PM, CGC.SE, false);
      injectLinearStreamImpl(CGC, IdxLI, PM->SoftPortNum, DFG->getUnroll(), DType,
                             DMO_Write, DP_NoPadding, SI, -1);

      PM->IntrinInjected = true;
    }

    void Visit(SLPPortMem *SPM) override {
      auto *DFG = SPM->Parent;
      auto *PM = SPM->Coal[0];

      CGC.IB->SetInsertPoint(DFG->DefaultIP());
      CGC.SEE.setInsertPoint(DFG->DefaultIP());
      int DType = PM->Store->getValueOperand()->getType()->getScalarSizeInBits() / 8;
      DSA_CHECK(SPM->Coal.size() >= 2) << SPM->Coal.size();
      auto *IdxLI = DAR.affineMemoryAccess(SPM, CGC.SE, false);
      injectLinearStreamImpl(CGC, IdxLI, SPM->SoftPortNum, DFG->getUnroll(), DType, DMO_Write,
                             DP_NoPadding, SI, -1);

      SPM->IntrinInjected = true;
    }

    void Visit(InputConst *IC) override {
      auto &LoopNest = DAR.DLI[IC->Parent->ID].LoopNest;
      for (int i = 0; i < (int) LoopNest.size(); ++i) { // NOLINT
        DSA_CHECK(LoopNest[i]->isLoopInvariant(IC->Val))
          << *IC->Val << " is not a loop invariant under " << *LoopNest[i];
      }
      auto &TripCount = DAR.DLI[IC->Parent->ID].TripCount;
      auto CR = injectComputedRepeat(CGC, TripCount, TripCount.size(), IC->Parent->getUnroll(), true);
      DSA_CHECK(!CR.second) << "Should not be stretched!";
      DSA_LOG(CODEGEN) << *IC->Val << " x " << *CR.first;
      CGC.SS_CONST(IC->SoftPortNum, IC->Val, CR.first,
                   IC->Val->getType()->getScalarSizeInBits() / 8);
      IC->IntrinInjected = true;
    }

    void Visit(CtrlMemPort *CMP) override {

      auto *IB = CGC.IB;
      auto *One = IB->getInt64(1);
      auto *Zero = IB->getInt64(0);
      IB->SetInsertPoint(CMP->Parent->DefaultIP());

      if (!dsa::utils::ModuleContext().PRED) {
        // PortNum == -1 indicates this port is omitted because of no
        // predication support
        if (CMP->SoftPortNum != -1) {
          CGC.SS_CONST(CMP->SoftPortNum, CMP->Load, One,
                       CMP->Load->getType()->getScalarSizeInBits() / 8);
          auto *DD = dyn_cast<DedicatedDFG>(CMP->Parent);
          DSA_CHECK(DD && "This node only exists in stream DFGs");
          CGC.SS_CONST(CMP->SoftPortNum, Zero, One);
        }
        CMP->IntrinInjected = true;
        return;
      }

      // If this stream is for the predicate, we require users to put sentinal
      // at the end the next word of the array.
      int DType = CMP->Load->getType()->getScalarSizeInBits() / 8;
      CGC.INSTANTIATE_1D_STREAM(CMP->Start, IB->getInt64(1), CMP->TripCnt,
                                CMP->SoftPortNum, 0, DSA_Access, DMO_Read,
                                DMT_DMA, DType, 0);

      CMP->Meta.set("op", "read");
      CMP->Meta.set("src", "memory");

      if (!CMP->ForPredicate) {
        // If this stream is NOT for the predicate, we pad two zero values to
        // produce the final result.
        CGC.SS_CONST(CMP->SoftPortNum, IB->getInt64(0), IB->getInt64(1), DType);
      } else {
        // This is kinda ad-hoc, because we current do not support a
        // runtime-determined length stream. This assumption does not work on that
        // case.
        auto *Sentinal = IB->getInt64(1ull << (DType * 8 - 1));
        CGC.SS_CONST(CMP->SoftPortNum, Sentinal, IB->getInt64(1));
      }

      CMP->IntrinInjected = true;
    }

    void Visit(OutputPort *OP) override {
      auto *Recv = CGC.SS_RECV(OP->SoftPortNum,
                              OP->Output->getType()->getScalarSizeInBits() / 8).value(CGC.IB);
      Recv = CGC.IB->CreateBitCast(Recv, OP->Output->getType());
      std::set<Instruction *> Equiv;
      FindEquivPHIs(OP->Output, Equiv);
      for (auto *Iter : Equiv) {
        Iter->replaceAllUsesWith(Recv);
      }
      OP->IntrinInjected = true;
    }

    void Visit(StreamInPort *SIP) override {
      auto F = [SIP] () -> StreamOutPort* {
        for (auto *DFG : SIP->Parent->Parent->DFGFilter<DFGBase>()) {
          for (auto *Elem : DFG->Entries) {
            if (auto *Casted = dyn_cast<StreamOutPort>(Elem)) {
              if (SIP->DataFrom == Casted->underlyingInst()) {
                return Casted;
              }
            }
          }
        }
        DSA_CHECK(false) << SIP->dump() << " stream out not found!";
        return nullptr;
      };
      StreamOutPort *SOP = F();
      auto *IB = CGC.IB;
      auto &SEE = CGC.SEE;
      assert(!SIP->IntrinInjected);
      if (auto *DD = dyn_cast<DedicatedDFG>(SIP->Parent)) {
        int Bytes =
            SOP->Output->getType()->getScalarType()->getScalarSizeInBits() / 8;
        auto &DLI = DAR.DLI[SIP->Parent->ID];
        auto &LoopNest = DLI.LoopNest;
        auto &TripCount = DLI.TripCount;
        int i = 0; // NOLINT
        for (i = 0; i < (int) LoopNest.size(); ++i) {
          if (!LoopNest[i]->isLoopInvariant(SOP->underlyingInst())) {
            break;
          }
        }
        auto Repeat = injectComputedRepeat(CGC, TripCount, i, DD->getUnroll(), false);
        CGC.SS_CONFIG_PORT(SIP->SoftPortNum, DPF_PortRepeat, Repeat.first);
        if (Repeat.second) {
          CGC.SS_CONFIG_PORT(SIP->SoftPortNum, DPF_PortRepeatStretch, Repeat.second);
        }
        Value *N = IB->getInt64(1);
        for (; i < (int) DLI.LoopNest.size(); ++i) {
          N = IB->CreateMul(N, SEE.expandCodeFor(DLI.TripCount[i]->base()));
        }
        CGC.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, N, Bytes);
      } else if (isa<TemporalDFG>(SIP->Parent)) {
        // TODO: Support temporal stream
        CGC.SS_RECURRENCE(SOP->SoftPortNum, SIP->SoftPortNum, IB->getInt64(1),
                          SOP->Output->getType()->getScalarSizeInBits() / 8);
      }
      SIP->IntrinInjected = true;
    }

    void Visit(StreamOutPort *SOP) override {
      assert(!SOP->IntrinInjected);
      SOP->IntrinInjected = true;
    }

    void Visit(AtomicPortMem *APM) override {
      // Open these when bringing APM back.
      auto *DFG = APM->Parent;
      if (!dsa::utils::ModuleContext().IND) {
        if (auto *DFGEntry = DFG->InThisDFG(APM->Operand)) {
          assert(false && "TODO: ss_recv operand from port!");
          (void) DFGEntry;
        } else {
          (void) DFGEntry;
        }
        APM->IntrinInjected = true;
        APM->Meta.set("cmd", "0.1");
        return;
      }
      // TODO: Support OpCode() == 3.
      if (APM->Operand) {
        DSA_CHECK(APM->OpCode == 0);
      }

      int IdxPort = -1;
      auto *IB = CGC.IB;
      // FIXME(@were): A more systematic trip count required.
      auto *Index = APM->Index->Load->getPointerOperand();
      int IBits = APM->Index->Load->getType()->getScalarSizeInBits();
      auto Analyzed = DFG->AnalyzeDataStream(Index, IBits / 8);
      auto *N = IB->CreateSDiv(Analyzed.BytesFromMemory(IB), IB->getInt64(IBits / 8));
      for (int i = 0; i < (int) DFG->Entries.size(); ++i) { // NOLINT
        if (auto *IMP = dyn_cast<IndMemPort>(DFG->Entries[i])) {
          if (IMP->Index->underlyingInst() == APM->Index->underlyingInst()) {
            auto *MP = IMP->Index;
            auto *IdxLI = DAR.affineMemoryAccess(MP, CGC.SE, false);
            int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
            injectLinearStreamImpl(CGC, IdxLI, MP->SoftPortNum, DFG->getUnroll(), DType, DMO_Read,
                                   (Padding) MP->fillMode(), SI, -1);
            IdxPort = IMP->IndexOutPort;
          }
        }
        // FIXME(@were): Is this too ad-hoc? This is doing const atomic operand.
        if (auto *CB = dyn_cast<ComputeBody>(DFG->Entries[i])) {
          if (DFG->Entries.size() != 3) {
            continue;
          }
          auto *Inst = CB->underlyingInst();
          for (int j = 0; j < (int) Inst->getNumOperands(); ++j) { // NOLINT
            if (!DFG->InThisDFG(Inst->getOperand(j))) {
              DSA_LOG(CODEGEN)
                << "[Const Sream] (" << *Inst->getOperand(j) << ") * ("
                << *N << ") -> " << APM->OperandPort;
              CGC.SS_CONST(APM->OperandPort, Inst->getOperand(j), N);
            }
          }
        }
      }
      int DType = APM->Op->getType()->getScalarSizeInBits() / 8;
      int IdxType = APM->Index->Load->getType()->getScalarSizeInBits() / 8;
      auto *GEP = dyn_cast<GetElementPtrInst>(APM->Store->getPointerOperand());
      DSA_CHECK(GEP);
      CGC.INSTANTIATE_1D_INDIRECT(APM->SoftPortNum, DType, IdxPort, IdxType,
                                  GEP->getOperand(0), IB->getInt64(0),
                                  N, DMT_SPAD, DMO_Add, false, false);
      DSA_LOG(CODEGEN)
        << "[AtomicSpad] WritePort: " << APM->SoftPortNum << ", DType: " << DType
        << ", IdxPort: " << IdxPort << ", IdxType: " << IdxType << ", Start: " << GEP->getOperand(0)
        << ", N: " << *N << ", SPAD Add";

      APM->IntrinInjected = true;
    }

    CodeGenContext &CGC;
    analysis::DFGAnalysisResult &DAR;
    analysis::SpadInfo &SI;
    StreamIntrinsicInjector(CodeGenContext &CGC, analysis::DFGAnalysisResult &DAR) :
      CGC(CGC), DAR(DAR), SI(DAR.SI) {}
  };

  for (int i = 0; i < (int) DFGs.size(); ++i) { // NOLINT
    auto *DFG = DFGs[i];
    UpdateStreamInjector USI(CGC, DAR);
    StreamIntrinsicInjector SII(CGC, DAR);
    if (!DFG->DefaultIP()) {
      continue;
    }
    CGC.IB->SetInsertPoint(DFG->DefaultIP());
    CGC.SEE.setInsertPoint(DFG->DefaultIP());
    for (auto *Elem : ReorderEntries(DFG)) {
      if (dsa::utils::ModuleContext().REC) {
        Elem->accept(&USI);
      }
      Elem->accept(&SII);
    }
  }

  for (auto &DFG : DFGs) {
    if (!DFG->DefaultIP()) {
      continue;
    }
    for (auto &PB : DFG->EntryFilter<PortBase>()) {
      DSA_CHECK(PB->IntrinInjected) << PB->dump();
    }
  }

  // Replace all the local memory variables by addresses on spads.
  auto *IB = CGC.IB;
  for (auto &Elem : DAR.SI.Offset) {
    Value *SAR = IB->getInt64(Elem.second);
    SAR = IB->CreateIntToPtr(SAR, Elem.first->getType());
    Elem.first->replaceAllUsesWith(SAR);
  }
}


void eraseOffloadedInstructions(DFGFile &DF, CodeGenContext &CGC) {

  std::set<Instruction *> Unique;

  for (auto &DFG : DF.DFGs) {
    for (auto *Entry : DFG->Entries) {

      // Skip instructions cannot be offloaded because of flags
      if (isa<IndMemPort>(Entry) && !dsa::utils::ModuleContext().IND) {
        continue;
      }
      if (isa<AtomicPortMem>(Entry) && !dsa::utils::ModuleContext().IND) {
        continue;
      }
      if ((isa<CtrlMemPort>(Entry) || isa<Predicate>(Entry)) &&
          !dsa::utils::ModuleContext().PRED) {
        continue;
      }

      auto F = [&Unique](Instruction *Inst) {
        bool SS = false;
        DSA_LOG(ERASE) << *Inst;
        for (auto *User : Inst->users()) {
          DSA_LOG(ERASE) << "user: " << *User;
          if (auto *Call = dyn_cast<CallInst>(User)) {
            if (auto *IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
              SS |= IA->getAsmString().find("ss_") == 0;
            }
          }
        }
        for (size_t i = 0; i < Inst->getNumOperands(); ++i) { // NOLINT
          auto *Use = Inst->getOperand(i);
          DSA_LOG(ERASE) << "use: " << *Use;
          if (auto *Call = dyn_cast<CallInst>(Use)) {
            if (auto *IA = dyn_cast<InlineAsm>(Call->getCalledOperand())) {
              SS |= IA->getAsmString().find("ss_") == 0;
            }
          }
        }
        if (!SS) {
          Unique.insert(Inst);
          DSA_LOG(ERASE) << "DELETE: " << *Inst;
        }
      };

      if (auto *P = dyn_cast<Predicate>(Entry)) {
        for (auto *Elem : P->Cond)
          F(Elem);
      } else {
        auto Insts = Entry->underlyingInsts();
        for (auto *Inst : Insts) {
          F(Inst);
        }
      }
    }

    if (auto *DD = dyn_cast<DedicatedDFG>(DFG)) {
      auto *StreamMD = GetUnrollMetadata(DD->LoopNest.back()->getLoopID(),
                                        "llvm.loop.ss.stream");
      auto *BarrierMD = dyn_cast<ConstantAsMetadata>(StreamMD->getOperand(1));
      if (BarrierMD->getValue()->getUniqueInteger().getSExtValue()) {
        // Find the "break" finger, and inject the wait at the "break" finger
        // block's end
        auto *OutBB = FindLoopPrologue(DD->LoopNest.back());
        Instruction *I = &OutBB->back();
        for (; !isa<PHINode>(I); I = I->getPrevNode()) {
          bool Found = false;
          for (auto *Elem : DD->InjectedCode) {
            if (I == Elem) {
              Found = true;
              break;
            }
          }
          auto *IB = CGC.IB;
          if (isa<PHINode>(I) || Found) {
            IB->SetInsertPoint(I->getNextNode());
            CGC.SS_WAIT_ALL();
            break;
          }
          if (I == &I->getParent()->front()) {
            IB->SetInsertPoint(I);
            CGC.SS_WAIT_ALL();
            break;
          }
        }

      } else {
        DSA_LOG(ERASE) << "No barrier required!";
      }
    } else if (auto *TD = dyn_cast<TemporalDFG>(DFG)) {
      TD->End->eraseFromParent();
      TD->Begin->eraseFromParent();
    }
  }

  for (auto *Inst : Unique) {
    Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
    Inst->eraseFromParent();
  }

  DSA_LOG(ERASE) << DF.Func;
}

} // namespace xform
} // namespace dsa
