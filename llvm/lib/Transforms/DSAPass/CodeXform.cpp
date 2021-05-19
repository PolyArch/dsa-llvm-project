#include "CodeXform.h"
#include "DFGAnalysis.h"

#include "dsa/rf.h"


// raw_ostream &operator<<(raw_ostream &os, DFGEntry &DE) {
//   os << "# [" << dsa::xform::KindStr[DE.Kind] << "]" << " DFG" << DE.Parent->ID << " Entry" << DE.ID;
//   if (DE.UnderlyingInsts().size() == 1) {
//     os << " " << *DE.UnderlyingInst();
//   } else {
//     os << "\n";
//     for (auto Elem : DE.UnderlyingInsts()) {
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
void EliminateInstructions(const std::vector<Instruction*> &Insts) {
  for (auto I : Insts) {
    I->replaceAllUsesWith(UndefValue::get(I->getType()));
    I->eraseFromParent();
  }
}

}

void EliminateTemporal(Function &F) {
  std::vector<Instruction*> ToRemove;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto Intrin = dyn_cast<IntrinsicInst>(&I)) {
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


std::vector<utils::StickyRegister>
InjectDSARegisterFile(Function &F) {
  IRBuilder<> IB(F.getContext());
  IB.SetInsertPoint(&F.getEntryBlock().back());
  std::vector<utils::StickyRegister> Res;
  std::string TyName("reg.type");
  auto RegType = StructType::create(TyName, IB.getInt64Ty(), IB.getInt8Ty());
  for (int i = 0; i < DSARF::TOTAL_REG; ++i) {
    auto A = IB.CreateAlloca(RegType, nullptr, REG_NAMES[i]);
    auto R = IB.CreateInBoundsGEP(A, {IB.getInt32(0), IB.getInt32(0)}, std::string(REG_NAMES[i]) + ".r.ptr");
    auto S = IB.CreateInBoundsGEP(A, {IB.getInt32(0), IB.getInt32(1)}, std::string(REG_NAMES[i]) + ".s.ptr");
    IB.CreateStore(IB.getInt64(REG_STICKY[i]), R);
    IB.CreateStore(IB.getInt8(i == DSARF::TBC), S);
    Res.emplace_back(A, R, S);
  }
  return Res;
}

// TODO(@were): I did not remember what is this function for.
bool HasOtherUser(InputPort *IP, Value *Val) {
  for (auto User : Val->users()) {
    if (auto Entry = IP->Parent->InThisDFG(User)) {
      if (auto CB = dyn_cast<ComputeBody>(Entry)) {
        if (!CB->isAtomic())
          return true;
      }
      if (isa<Predicate>(Entry)) {
        return true;
      }
    }
  }
  return false;
}

std::string ValueToOperandText(Value *Val) {

  if (auto CI = dyn_cast<ConstantInt>(Val)) {
    return formatv("{0}", CI->getValue().getSExtValue());
  } else if (auto CFP = dyn_cast<ConstantFP>(Val)) {
    //TODO: Support more data types
    double FPV = CFP->getValueAPF().convertToDouble();
    uint64_t *RI = reinterpret_cast<uint64_t*>(&FPV);
    return formatv("{0}", *RI);
  }

  CHECK(false) << "Cannot dump " << *Val;
  return "";
}


std::string GetOperationStr(Instruction *Inst, bool isAcc, bool predicated) {
  std::string OpStr;
  int BitWidth = Inst->getType()->getScalarSizeInBits();

  if (auto Cmp = dyn_cast<CmpInst>(Inst)) {
    // TODO: Support floating point
    OpStr = "compare";
    BitWidth = Cmp->getOperand(0)->getType()->getScalarSizeInBits();
  } else if (auto Call = dyn_cast<CallInst>(Inst)) {
    OpStr = Call->getCalledFunction()->getName().str();
  } else {
    OpStr = Inst->getOpcodeName();
    if (isAcc) {
      if (!predicated) {
        OpStr = OpStr[0] == 'f' ? "facc" : "acc";
      } else {
        OpStr = OpStr[0] == 'f' ? "faccumulate" : "accumulate";
      }
    }
  }

  for (int i = 0, e = OpStr[0] == 'f' ? 2 : 1; i < e; ++i) {
    OpStr[i] -= 'a';
    OpStr[i] += 'A';
  }

  return formatv("{0}{1}", OpStr, BitWidth);
}

const char *KindStr[] = {
  "DFGEntry",

  // Computation {
  "ComputeStarts",
  "ComputeBody",
  "Duplicate",
  "Accumulator",
  "ComputeEnds",
  // }

  // Predicate {
  "Predicate",
  // }

  // Port {
  "PortStarts",
  "PortBase",

  // InPort {
  "InPortStarts",
  "InputPort",
  "MemPort",
  "IndMemPort",
  "CtrlMemPort",
  "InputConst",
  "StreamInPort",
  "CtrlSignal",
  "InPortEnds",
  // }

  // OutPort {
  "OutPortStarts",
  "OutputPort",
  "PortMem",
  "AtomicPortMem",
  "StreamOutPort",
  "OutPortEnds",
  // }

  "PortEnds"
  // }
};


/*!
 * \brief I anyways need the DFG entries to be reordered in which the order the are emitted. 
 * \param DB The DFG to reorder the entries.
 */
static std::vector<DFGEntry*> ReorderEntries(DFGBase *DB) {
  std::vector<DFGEntry*> Res;
  Res.reserve(DB->Entries.size());
  for (auto Elem : DB->EntryFilter<InputPort>()) {
    Res.push_back(Elem);
  }
  for (auto Elem : DB->Entries) {
    if (isa<InputPort>(Elem) || isa<OutputPort>(Elem)) {
      continue;
    }
    Res.push_back(Elem);
  }
  for (auto Elem : DB->EntryFilter<OutputPort>()) {
    Res.push_back(Elem);
  }
  return Res;
}


struct DFGPrinter : dsa::DFGVisitor {

  struct ControlBit {
    std::ostringstream SubCtrl[3];
    Predicate *Pred{nullptr};

    void addControlledMemoryStream(int Idx, DFGEntry *DE) {
      if (auto CMP = dyn_cast<CtrlMemPort>(DE)) {
         if (Pred == nullptr) {
           Pred = CMP->Pred;
         } else {
           CHECK(Pred == CMP->Pred)
              << "An instruction cannot be controlled by more than one predication.";
         }
         assert(Pred);
         for (int j = 0; j < 3; ++j) {
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
      for (int i = 0; i < 3; ++i)
        if (!SubCtrl[i].str().empty())
          return false;
      return true;
    }

    std::string finalize() {
      std::ostringstream Ctrl;
      for (int i = 0; i < 3; ++i) {
        if (!SubCtrl[i].str().empty()) {
          if (!Ctrl.str().empty()) Ctrl << ", ";
          Ctrl << i << ":" << SubCtrl[i].str();
        }
      }
      return Ctrl.str();
    }

    void updateAbstain(int x, bool isAcc) {
      for (int i = 0; i < 3; ++i) {
        if (x >> i & 1) {
          if (!SubCtrl[i].str().empty()) {
            SubCtrl[i] << "|";
          }
          SubCtrl[i] << "a";
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
      os << "# [" << KindStr[DE->Kind] << "]: DFG" << DE->Parent->ID << " Entry" << DE->ID << "\n";
      int i = 0;
      auto Insts = DE->UnderlyingInsts();
      for (auto Elem : Insts) {
        os << "# Inst";
        if(Insts.size() != 1) {
          os << i++;
        }
        os << ": " << *Elem << "\n";
      }
    }

    void Visit(Accumulator *Acc) {

      Visit(cast<DFGEntry>(Acc));
      auto Inst = Acc->Operation;
      std::queue<std::string> Q;
      auto Reduce = GetOperationStr(Inst, false, false);
      ControlBit CtrlBit;

      for (int vec = 0; vec < Acc->Parent->getUnroll(); ++vec) {
        for (size_t j = 0; j < 2; ++j) {
          auto Operand = Inst->getOperand(j);
          if (!isa<PHINode>(Operand)) {
            auto Entry = Acc->Parent->InThisDFG(Operand);
            CHECK(Entry);
            Q.push(Entry->Name(vec));
          }
        }
      }

      while (Q.size() > 1) {
        auto A = Q.front(); Q.pop(); assert(!Q.empty());
        auto B = Q.front(); Q.pop();
        os << formatv("TMP{0} = {1}({2}, {3})", Parent->TmpCnt, Reduce, A, B).str() << "\n";
        Q.push(formatv("TMP{0}", Parent->TmpCnt++));
      }

      auto P = Acc->getPredicate();
      os << Acc->Name() << " = " << GetOperationStr(Inst, true, P != nullptr) << "(" << Q.front()
         << ", ";

      if (dsa::utils::ModuleContext().PRED) {
        if (P || !CtrlBit.empty()) {
          CtrlBit.updateAbstain(Acc->getAbstainBit(), true);
          os << "ctrl=" << P->Name(-1) << "{" << CtrlBit.finalize() << "}";
        } else {
          os << Acc->Ctrl->Name();
        }
      } else {
        os << "ctrl=" << Acc->Ctrl->Name() << "{2:d}";
      }

      os << ")\n";
    }

    void Visit(CtrlSignal *CS) {
      if (!CS->Controlled->getPredicate() || !dsa::utils::ModuleContext().PRED) {
        Visit(cast<DFGEntry>(CS));
        os << "Input: " << CS->Name() << "\n";
      }
    }

    void Visit(InputConst *IC) {
      if (!HasOtherUser(IC, IC->Val)) {
        return;
      }
      Visit(cast<DFGEntry>(IC));
      os << "Input" << IC->Val->getType()->getScalarSizeInBits() << ": " << IC->Name() << "\n";
    }

    void Visit(InputPort *IP) override {
      if (!utils::ModuleContext().PRED) {
        for (auto User : IP->UnderlyingInst()->users()) {
          auto Entry = IP->Parent->InThisDFG(User);
          if (Entry && !isa<Predicate>(Entry)) {
            return;
          }
        }
      }
      if (auto IMP = dyn_cast<IndMemPort>(IP)) {
        if (IMP->duplicated()) {
          return;
        }
      }
      if (!HasOtherUser(IP, IP->UnderlyingInst())) {
        return;
      }
      Visit(cast<DFGEntry>(IP));
      {
        using dfg::MetaPort;
        auto Meta = IP->Meta;
        if (Meta.source != MetaPort::Data::Unknown) {
          os << "#pragma src=" << dfg::MetaPort::DataText[(int) Meta.source] << "\n";
        }
        if (Meta.dest != MetaPort::Data::Unknown) {
          os << "#pragma dest=" << dfg::MetaPort::DataText[(int) Meta.dest] << "\n";
        }
        if (!Meta.dest_port.empty()) {
          os << "#pragma dest=" << Meta.dest_port << "\n";
        }
        for (int i = 0; i < (int) MetaPort::Operation::Unknown; ++i) {
          if (Meta.op >> i & 1) {
            os << "#pragma op=" << MetaPort::OperationText[i] << "\n";
          }
        }
        if (Meta.conc) {
          os << "#pragma conc=" << Meta.conc << "\n";
        }
        os << "#pragma cmd=" << Meta.cmd << "\n";
        os << "#pragma repeat=" << Meta.repeat << "\n";
      }

      os << "Input" << IP->UnderlyingInst()->getType()->getScalarSizeInBits()
                    << ": " << IP->Name();
      if (IP->ShouldUnroll()) {
        os << "[" << IP->Parent->getUnroll() << "]";
      }
      os << "\n";
    }

    void Visit(ComputeBody *CB) override {
      // If this ComputeBody is handled by a atomic operation skip it!
      if (CB->isAtomic())
        return;

      Visit(cast<DFGEntry>(CB));

      int Degree = (CB->ShouldUnroll() ? CB->Parent->getUnroll() : 1);
      for (int vec = 0; vec < Degree; ++vec) {
        os << CB->Name(vec) << " = " << GetOperationStr(CB->Operation, false, false) << "(";
        ControlBit CtrlBit;

        bool isCall = isa<CallInst>(CB->Operation);
        for (int i = 0; i < (int) (CB->Operation->getNumOperands() - isCall); ++i) {
          auto Val = CB->Operation->getOperand(i);
          if (i) os << ", ";
          if (auto EntryOp = CB->Parent->InThisDFG(Val)) {
            os << EntryOp->Name(vec);
            CtrlBit.addControlledMemoryStream(i, EntryOp);
          } else {
            os << ValueToOperandText(Val);
          }
        }

        if (utils::ModuleContext().PRED) {
          if (CB->getPredicate())
            CtrlBit.updateAbstain(CB->getAbstainBit(), false);
          if (!CtrlBit.empty()) {
            os << ", ctrl=" << CtrlBit.Pred->Name(vec) << "{" << CtrlBit.finalize() << "}";
          }
        }

        os << ")\n";
      }

    }

    void Visit(Predicate *P) override {
      if (!utils::ModuleContext().PRED) {
        return;
      }

      {
        // TODO(@were): Finalize this.
        os << "# [Predication] Combination\n";
        for (auto I : P->Cond) {
          os << "# " << *I << "\n";
        }
      }

      ControlBit CtrlBit;
      os << P->Name(-1) << " = Compare" << P->Cond[0]->getOperand(0)->getType()->getScalarSizeInBits()
         << "(";
      for (size_t i = 0; i < P->Cond[0]->getNumOperands(); ++i) {
        auto Val = P->Cond[0]->getOperand(i);
        if (i) os << ", ";
        if (auto EntryOp = P->Parent->InThisDFG(Val)) {
          os << EntryOp->Name(-1);
          CtrlBit.addControlledMemoryStream(i, EntryOp);
          if (auto CMP = dyn_cast<CtrlMemPort>(EntryOp))
            CMP->ForPredicate = true;
        } else {
          os << ValueToOperandText(Val);
        }
      }

      if (!CtrlBit.empty()) {
        if (CtrlBit.Pred == P)
          os << ", self=";
        else
          os << ", ctrl=" << CtrlBit.Pred->Name(-1);
        os << "{" << CtrlBit.finalize() << "}";
      }

      os << ")\n";

    }

    void Visit(OutputPort *OP) {
      Visit(cast<DFGEntry>(OP));
      std::ostringstream oss;
      OP->Meta.to_pragma(oss);
      os << oss.str();
      auto Entry = OP->Parent->InThisDFG(OP->Output);
      CHECK(Entry);
      for (int i = 0; i < (Entry->ShouldUnroll() ? OP->Parent->getUnroll() : 1); ++i) {
        os << OP->Name(i) << " = " << Entry->Name(i) << "\n";
      }
      os << "Output" << OP->Output->getType()->getScalarSizeInBits() << ": " << OP->Name();
      if (Entry->ShouldUnroll())
        os << "[" << OP->Parent->getUnroll() << "]";
      os << "\n";
    }

    raw_ostream &os;
    DFGPrinter *Parent;

    DFGEntryEmitter(raw_ostream &os_, DFGPrinter *Parent_) : os(os_), Parent(Parent_) {}

  };

  void Visit(DedicatedDFG *DD) override {
    if (utils::ModuleContext().TRIGGER) {
      CHECK(utils::ModuleContext().TEMPORAL)
        << "Trigger cannot be enabled without temporal";
      os << "#pragma group temporal\n";
    }
    DFGVisitor::Visit(DD);
  }

  void Visit(TemporalDFG *TD) override {
    os << "#pragma group temporal\n";
    DFGVisitor::Visit(TD);
  }

  void Visit(DFGBase *DB) {
    // FIXME(@were): Add block freqency an attribute of DFG.
    // auto BF = Parent->Query->BFI->getBlockFreq(getBlocks()[0]);
    // os << "#pragma group frequency " << 1 << "\n";
    os << "#pragma group unroll " << DB->getUnroll() << "\n";

    auto Reordered = ReorderEntries(DB);

    DFGEntryEmitter DEE(os, this);
    for (auto Elem : DB->Entries) {
      Elem->Accept(&DEE);
    }

    // TODO(@were): Bing this back for atomic operations.
    // /// Emit intermediate result for atomic operation
    // for (auto Elem : EntryFilter<ComputeBody>())
    //   Elem->EmitAtomic(os);

    // TODO(@were): Move this to a DFG.
    for (auto Elem : DB->EntryFilter<IndMemPort>()) {
      os << "\n\n----\n\n";
      os << "Input" << Elem->Index->Load->getType()->getScalarSizeInBits()
         << ": indirect_in_" << DB->ID << "_" << Elem->ID << "\n";
      os << "indirect_out_" << DB->ID << "_" << Elem->ID << " = "
         << "indirect_in_" << DB->ID << "_" << Elem->ID << "\n";
      os << "Output" << Elem->Index->Load->getType()->getScalarSizeInBits()
         << ": indirect_out_" << DB->ID << "_" << Elem->ID << "\n";
    }
  }

  raw_ostream &os;
  /*!
   * \brief Count the ticker of temp variables for accumulator reduction.
   */
  int TmpCnt{0};

  DFGPrinter(raw_ostream &os_) : os(os_) {}
};


void EmitDFG(raw_ostream *os, DFGFile *DFG) {
  bool DeleteOS = false;
  if (!os) {
    std::error_code EC;
    os = new raw_fd_ostream(DFG->getName(), EC);
    DeleteOS = true;
  }
  DFGPrinter DP(*os);
  auto Graphs = DFG->DFGFilter<DFGBase>();
  for (int i = 0; i < (int) Graphs.size(); ++i) {
    auto Elem = Graphs[i];
    if (i) {
      *os << "----\n";
    }
    Elem->Accept(&DP);
  }
  if (DeleteOS) {
    delete os;
  }
}


void CodeGenContext::InjectFusionHints(std::string Mnemonic, REG &a, REG &b, int c) {
  // Convert an int-like value to the exact int64 type.
  auto MakeInt64 = [this](Value *Val) -> Value* {
    if (Val->getType()->isPointerTy()) {
      return IB->CreatePtrToInt(Val, IB->getInt64Ty());
    }
    auto Ty = IB->getIntNTy(Val->getType()->getScalarSizeInBits());
    auto RI = IB->CreateBitCast(Val, Ty);
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
  for (int i = 0; i < 2; ++i) {
    int idx = (c >> (i * 5)) & 31;
    int sticky = (c >> (10 + i)) & 1;
    if (idx) {
      auto AA = IB->CreateLoad(Regs[idx].Reg);
      auto AS = IB->CreateLoad(Regs[idx].Sticky);
      auto AV = MakeInt64(a.value(IB));
      IB->CreateStore(AV, Regs[idx].Reg);
      IB->CreateStore(IB->getInt8(sticky), Regs[idx].Sticky);
      IntrinsicImpl("equal.hint.v1", "r", {IB->CreateICmpEQ(AA, AV)}, IB->getVoidTy());
      IntrinsicImpl("equal.hint.s1", "r", {IB->CreateICmpEQ(AS, IB->getInt8(sticky))}, IB->getVoidTy());
      auto V = IB->CreateLoad(Regs[idx].Reg);
      (i ? b : a) = V;
    }
  }
}

void CodeGenContext::IntrinsicImpl(const std::string &Mnemonic, const std::string &OpConstrain,
                                 const std::vector<Value*> &Args, Type *ResTy) {
  std::ostringstream MOSS;
  MOSS << Mnemonic << " $0";
  for (int i = 0, n = OpConstrain.size(), j = 1; i < n; ++i) {
    if (OpConstrain[i] == ',') {
      MOSS << ", $" << j;
      ++j;
    }
  }
  std::vector<Type*> Types;
  for (auto Arg : Args) {
    Types.push_back(Arg->getType());
  }
  auto FTy = FunctionType::get(ResTy, Types, false);
  auto IA = InlineAsm::get(FTy, MOSS.str(), OpConstrain, true);
  res.push_back(IB->CreateCall(IA, Args));
  if (Mnemonic == "ss_lin_strm" ||
      Mnemonic == "ss_ind_strm" ||
      Mnemonic == "ss_recv" ||
      Mnemonic == "ss_wr_rd") {
    for (int i = 0; i < DSARF::TOTAL_REG; ++i) {
      auto C = IB->CreateTrunc(IB->CreateLoad(Regs[i].Sticky), IB->getInt1Ty());
      auto SV = IB->CreateLoad(Regs[i].Reg);
      auto Reset = IB->CreateSelect(C, SV, IB->getInt64(REG_STICKY[i]));
      IB->CreateStore(Reset, Regs[i].Reg);
    }
  }
}

void InjectConfiguration(CodeGenContext &CGC, analysis::ConfigInfo &CI, Instruction *Start, Instruction *End) {
  auto IB = CGC.IB;
  IB->SetInsertPoint(Start);
  auto GV = IB->CreateGlobalString(CI.Bitstream, CI.Name + "_bitstream", GlobalValue::ExternalLinkage);
  CGC.SS_CONFIG(GV, IB->getInt64(CI.Size));
  IB->SetInsertPoint(End);
  CGC.SS_WAIT_ALL();
}

void InjectLinearStreamImpl(ScalarEvolution *SE, SCEVExpander &SEE, IRBuilder<> *IB,
                            const SCEV *Idx, std::vector<Loop*> LoopNest,
                            dsa::inject::RepeatInjector &RI,
                            dsa::inject::LinearInjector &LI,
                            int Port, int Unroll, int DType,
                            MemoryOperation MO, Padding Padding, MemoryType MT) {
  auto IdxLI = dsa::analysis::AnalyzeIndexExpr(SE, Idx, LoopNest);
  std::vector<dsa::analysis::LinearInfo*> LoopLI;
  for (int i = 0, N = LoopNest.size(); i < N; ++i) {
    auto CurDim = dsa::analysis::AnalyzeIndexExpr(SE, SE->getBackedgeTakenCount(LoopNest[i]), LoopNest);
    LoopLI.push_back(CurDim);
  }
  if (MO == MemoryOperation::DMO_Read) {
    RI.Inject(IdxLI, LoopLI, Port, Unroll);
  }
  LI.Inject(IdxLI, LoopLI, Port, MO, Padding, MT, DType);
}

void InjectStreamIntrinsics(CodeGenContext &CGC, DFGFile &DF) {

  auto DFGs = DF.DFGFilter<DFGBase>();

  struct StreamIntrinsicInjector : DFGEntryVisitor {
    void Visit(InputPort *IP) {
      IP->InjectStreamIntrinsic(CGC.IB);
    }

    void Visit(OutputPort *IP) {
      IP->InjectStreamIntrinsic(CGC.IB);
    }

    void Visit(IndMemPort *IMP) override {
      if (IMP->IntrinInjected)
        return;

      auto IB = CGC.IB;

      if (!dsa::utils::ModuleContext().IND) {
        CGC.SS_CONST(IMP->SoftPortNum, IMP->Load, IB->getInt64(1), IMP->Load->getType()->getScalarSizeInBits() / 8);
        IMP->IntrinInjected = true;
        IMP->Meta.set("src", "memory");
        IMP->Meta.set("cmd", "0.1");
        return;
      }

      if (IMP->duplicated()) {
        IMP->IntrinInjected = true;
        return;
      }

      std::vector<IndMemPort*> Together;
      std::vector<int> INDs;

      for (auto &IMP1 : IMP->Parent->EntryFilter<IndMemPort>()) {
        if (IMP1->IntrinInjected)
          continue;
        if (IMP->Index->Load == IMP1->Index->Load) {
          Together.push_back(IMP1);
          CHECK(IMP1->Index->SoftPortNum != -1);
          INDs.push_back(IMP1->Index->SoftPortNum);
        }
      }

      CHECK(Together[0] == IMP);

      for (size_t i = 1; i < Together.size(); ++i) {
        CGC.SS_CONFIG_PORT(INDs[i], DPF_PortBroadcast, true);
      }

      auto Index = IMP->Index->Load->getPointerOperand();
      auto Analyzed = IMP->Parent->AnalyzeDataStream(
        Index, IMP->Index->Load->getType()->getScalarSizeInBits() / 8);
      IMP->Parent->InjectRepeat(Analyzed.AR, nullptr, IMP->SoftPortNum);
      auto ActualSrc = dsa::inject::InjectLinearStream(IB, CGC.Regs,
                                                       IMP->Index->SoftPortNum, Analyzed,
                                                       DMO_Read, DP_NoPadding, DMT_DMA,
                                                       IMP->Index->Load->getType()->getScalarSizeInBits() / 8);

      for (size_t i = 0; i < Together.size(); ++i) {
        auto Cur = Together[i];
        int IBits = Cur->Index->Load->getType()->getScalarSizeInBits();
        auto Num = IB->CreateUDiv(Analyzed.BytesFromMemory(IB),
                                  IB->getInt64(IBits / 8));
        auto GEP = dyn_cast<GetElementPtrInst>(Cur->Load->getPointerOperand());
        CGC.SS_INDIRECT_READ(IMP->SoftPortNum, IMP->IndexOutPort, GEP->getOperand(0),
                             Cur->Load->getType()->getScalarSizeInBits() / 8, Num, DMT_DMA);

        // TODO: Support indirect read on the SPAD(?)
        Cur->Meta.set("src", dsa::dfg::MetaPort::DataText[(int) ActualSrc]);
        Cur->Meta.set("dest", "memory");
        Cur->Meta.set("op", "indread");

        Cur->IntrinInjected = true;
      }
      IMP->IntrinInjected = true;
    }
    
    void Visit(MemPort *MP) override {
      auto IB = CGC.IB;
      IB->SetInsertPoint(MP->Parent->DefaultIP());

      if (MP->IntrinInjected)
        return;

      if (!HasOtherUser(MP, MP->UnderlyingInst())) {
        MP->IntrinInjected = true;
        return;
      }

      if (MP->InjectUpdateStream(IB)) {
        return;
      }

      // Wrappers
      auto DFG = MP->Parent;


      // Handle data stream with predicate
      if (MP->getPredicate()) {
        assert(false && "Predicated stream should be handled in CtrlMemPort.");
      }

      if (auto DD = dyn_cast<DedicatedDFG>(DFG)) {
        // FIXME(@were): Make this more unified.
        auto &SEE = CGC.SEE;
        SEE.setInsertPoint(DFG->DefaultIP());
        dsa::inject::RepeatInjector RI(IB, &SEE, CGC.Regs);
        dsa::inject::LinearInjector LI(IB, &SEE, CGC.Regs);
        std::vector<Loop*> LoopNest(DD->LoopNest.begin(), DD->LoopNest.end());
        auto SCEVIdx = CGC.SE.getSCEV(MP->Load->getPointerOperand());
        int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
        InjectLinearStreamImpl(&CGC.SE, SEE, IB, SCEVIdx, LoopNest, RI, LI, MP->SoftPortNum,
                               DFG->getUnroll(), DType, DMO_Read,
                               (Padding) MP->FillMode(), DMT_DMA);
        MP->IntrinInjected = true;
        return;
      }

      auto Analyzed = DFG->AnalyzeDataStream(
        MP->Load->getPointerOperand(),
        MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);

      if (Analyzed.Dimensions.empty()) {
        auto RepeatedConst = IB->CreateBitCast(
          IB->CreateLoad(MP->Load->getPointerOperand()), IB->getInt64Ty());
        DFG->InjectRepeat(Analyzed.AR, RepeatedConst, MP->SoftPortNum);
      } else {
        auto Fill = MP->FillMode();
        DFG->InjectRepeat(Analyzed.AR, nullptr, MP->SoftPortNum);
        auto Src =
          dsa::inject::InjectLinearStream(IB, CGC.Regs,
                                          MP->SoftPortNum, Analyzed, DMO_Read, (Padding) Fill, DMT_DMA,
                                          MP->Load->getType()->getScalarType()->getScalarSizeInBits() / 8);
        MP->Meta.set("src", dsa::dfg::MetaPort::DataText[(int) Src]);
        MP->Meta.set("op", "read");
      }

      MP->IntrinInjected = true;
    }

    CodeGenContext &CGC;
    StreamIntrinsicInjector(CodeGenContext &CGC_) : CGC(CGC_) {}
  };

  StreamIntrinsicInjector SII(CGC);

  for (auto DFG : DFGs) {
    for (auto Elem : ReorderEntries(DFG)) {
      Elem->Accept(&SII);
    }
  }

  for (auto &DD : DFGs) {
    for (auto &PB : DD->EntryFilter<PortBase>()) {
      CHECK(PB->IntrinInjected);
    }
  }

}

}
}
