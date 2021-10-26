#include "Util.h"
#include "dsa/debug.h"

#include "./CodeXform.h"
#include "./DFGAnalysis.h"
#include "./StreamAnalysis.h"

#include "llvm/ADT/iterator_range.h"

#define DEBUG_TYPE "dfg-analysis"

namespace dsa {
namespace analysis {

void gatherConfigScope(Function &F, DFGAnalysisResult &DAR) {
  auto &Res = DAR.Scope;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *End = dyn_cast<IntrinsicInst>(&I)) {
        if (End->getIntrinsicID() == Intrinsic::ss_config_end) {
          auto *Start = dyn_cast<IntrinsicInst>(End->getOperand(0));
          CHECK(Start && Start->getIntrinsicID() == Intrinsic::ss_config_start);
          Res.emplace_back(Start, End);
        }
      }
    }
  }
}

std::pair<std::set<Instruction *>, std::set<Instruction *>>
bfsOperands(DFGBase *DB, Instruction *From, DominatorTree *DT) {
  std::set<Instruction *> Visited, OutBound;
  std::queue<Instruction *> Q;
  Visited.insert(From);
  Q.push(From);
  while (!Q.empty()) {
    auto *Cur = Q.front();
    Q.pop();
    for (size_t I = 0; I < Cur->getNumOperands(); ++I) {
      if (auto *Inst = dyn_cast<Instruction>(Cur->getOperand(I))) {
        if (DT && !DT->dominates(Inst, From)) {
          continue;
        }
        if (!Visited.count(Inst)) {
          if (DB->InThisScope(Inst)) {
            Visited.insert(Inst);
            Q.push(Inst);
          } else {
            OutBound.insert(Inst);
          }
        }
      }
    }
  }
  return {Visited, OutBound};
}

/*!
 * \brief How DFG Entries are analyzed and extracted.
 */
struct DFGEntryAnalyzer : DFGVisitor {
  /*!
   * \brief The DFG to be analyzed.
   */
  DFGBase *DBPtr;
  /*!
   * \brief The result of an analyzer.
   */
  DominatorTree *DT;

  /*!
   * \brief Find all the PHI function that is essentially the same value as the
   * given instruction. \param Inst The instruction to be analyzed. \param Equiv
   * The result to be stored.
   */
  void findEquivPhIs(Instruction *Inst, std::set<Instruction *> &Equiv) {
    std::queue<Instruction *> Q;
    Q.push(Inst);
    Equiv.insert(Inst);
    while (!Q.empty()) {
      if (auto *PHI = dyn_cast<PHINode>(Q.front())) {
        for (auto &Elem : PHI->incoming_values()) {
          auto *Casted = dyn_cast<Instruction>(Elem);
          if (!Casted)
            continue;
          if (Equiv.count(Casted))
            continue;
          Q.push(Casted);
          Equiv.insert(Casted);
        }
      }
      for (auto *User : Q.front()->users()) {
        auto *Phi = dyn_cast<PHINode>(User);
        if (!Phi)
          continue;
        if (Equiv.count(Phi))
          continue;
        Q.push(Phi);
        Equiv.insert(Phi);
      }
      Q.pop();
    }

    LLVM_DEBUG(DSA_INFO << "equiv of " << *Inst;
               for (auto I : Equiv) { DSA_INFO << *I; });
  }

  Predicate *findEquivPredicate(Value *LHS, Value *RHS) {
    auto &DB = *DBPtr;
    for (auto *Elem : DB.EntryFilter<Predicate>()) {
      if (Elem->Cond[0]->getOperand(0) == LHS &&
          Elem->Cond[0]->getOperand(1) == RHS)
        return Elem;
      if (Elem->Cond[0]->getOperand(1) == LHS &&
          Elem->Cond[0]->getOperand(0) == RHS)
        return Elem;
    }
    return nullptr;
  }

  DFGEntry *differentiateMemoryStream(LoadInst *Load) {
    auto &DB = *DBPtr;
    if (auto *GEP = dyn_cast<GetElementPtrInst>(Load->getPointerOperand())) {

      auto BFSBack = bfsOperands(DBPtr, GEP, DT);

      auto FLoad = [Load, BFSBack, &DB](Value *Val) -> DFGEntry * {
        LoadInst *IdxLoad = nullptr;
        for (auto *Elem : BFSBack.first) {
          if (auto *ThisLoad = dyn_cast<LoadInst>(Elem)) {
            CHECK(!IdxLoad) << "For now only one level indirect supported!";
            IdxLoad = ThisLoad;
          }
        }
        if (IdxLoad) {
          return new IndMemPort(&DB, IdxLoad, Load);
        }
        return nullptr;
      };

      auto FGather = [Load, GEP, this, &DB](Value *Val) -> DFGEntry * {
        auto *DD = dyn_cast<DedicatedDFG>(&DB);

        auto *Casted = dyn_cast<Instruction>(Val);
        if (!Casted)
          return nullptr;

        if (!DD)
          return nullptr;

        {
          bool SimpleLoop = false;
          auto *BI = dyn_cast<BranchInst>(&DD->InnerMost()->getLoopLatch()->back());
          auto *Latch = DD->InnerMost()->getLoopLatch();
          CHECK(BI);
          for (auto *BB : BI->successors()) {
            if (BB == Latch) {
              SimpleLoop = true;
            }
          }
          if (SimpleLoop) {
            return nullptr;
          }
        }

        std::set<Instruction *> Equiv;
        LLVM_DEBUG(DSA_INFO << "Equiv of: ");
        findEquivPhIs(Casted, Equiv);

        Value *TripCount = nullptr;
        SmallVector<std::pair<ICmpInst *, bool>, 0> Conditions;
        for (auto *Elem : Equiv) {
          if (auto *PHI = dyn_cast<PHINode>(Elem)) {
            for (auto &Essense : PHI->incoming_values()) {
              auto *Inst = dyn_cast<Instruction>(Essense);
              if (Inst && !isa<PHINode>(Inst)) {
                if (Inst->getOpcode() == BinaryOperator::Add) {
                  auto *DomBB = DT->getNode(Inst->getParent())->getIDom()->getBlock();
                  LLVM_DEBUG(DomBB->back().dump(); Inst->dump());
                  auto *BI = dyn_cast<BranchInst>(&DomBB->back());
                  assert(BI);
                  if (BI->isConditional()) {
                    auto *CondCmp = dyn_cast<ICmpInst>(BI->getCondition());
                    bool OK = true;
                    for (size_t I = 0; I < Conditions.size(); ++I) {
                      auto *AlreadyCmp = Conditions[I].first;
                      if (CondCmp->getNumOperands() !=
                          AlreadyCmp->getNumOperands()) {
                        OK = false;
                        break;
                      }
                      OK = OK && ((AlreadyCmp->getOperand(0) ==
                                       CondCmp->getOperand(0) &&
                                   AlreadyCmp->getOperand(1) ==
                                       CondCmp->getOperand(1)) ||
                                  (AlreadyCmp->getOperand(0) ==
                                       CondCmp->getOperand(1) &&
                                   AlreadyCmp->getOperand(1) ==
                                       CondCmp->getOperand(0)));
                    }
                    assert(OK && "Controlled by more than one predicate!");
                    Conditions.push_back(std::make_pair(
                        CondCmp, Inst->getParent() == BI->getSuccessor(0)));
                  }
                }
              }
            }
          }
          if (DD && Elem->getParent() == DD->InnerMost()->getLoopLatch()) {
            LLVM_DEBUG(DSA_INFO << "Latch"; Elem->dump());
            for (auto *User : Elem->users()) {
              auto *Cmp = dyn_cast<ICmpInst>(User);
              if (!Cmp)
                continue;
              if (Cmp->getParent() != Elem->getParent())
                continue;
              assert(Cmp->getPredicate() == ICmpInst::Predicate::ICMP_SLT &&
                     "For now only support SLT");
              for (size_t I = 0; I < Cmp->getNumOperands(); ++I) {
                if (Cmp->getOperand(I) != Elem) {
                  TripCount = Cmp->getOperand(I);
                  LLVM_DEBUG(DSA_INFO << "TripCount"; TripCount->dump());
                }
              }
            }
          }
        }
        if (TripCount && !Conditions.empty()) {

          int Mask = 0;
          SmallVector<bool, 0> Reverse;

          auto *Pred = findEquivPredicate(Conditions[0].first->getOperand(0),
                                         Conditions[0].first->getOperand(1));

          if (!Pred) {
            Pred = new Predicate(&DB, Conditions[0].first);
            DB.Entries.push_back(Pred);
          }

          for (size_t I = 0; I < Conditions.size(); ++I) {
            Reverse.push_back(Pred->addCond(Conditions[I].first));
          }

          for (size_t I = 0; I < Conditions.size(); ++I) {
            auto Cond = Conditions[I];
            LLVM_DEBUG(DSA_INFO << "Moveforward: " << Cond.second << " ";
                       Cond.first->dump());
            int SubMask = PredicateToInt(Cond.first->getPredicate(),
                                         Cond.second, Reverse[I]);
            Mask |= SubMask;
          }

          LLVM_DEBUG(DSA_INFO << "Forward mask: " << Mask << "\n");
          // FIXME: GEP for not is good enough, but we need a better way to
          // figure out the start
          //        pointer later.
          return new CtrlMemPort(&DB, Load, GEP->getOperand(0), TripCount, Pred,
                                 Mask);
        }
        LLVM_DEBUG(DSA_INFO << "\n");
        return nullptr;
      };

      // TODO(@were): Can I hoist BFSOperands out here?
      for (size_t I = 1; I < GEP->getNumOperands(); ++I) {
        if (auto *Res = FLoad(GEP->getOperand(I)))
          return Res;
        if (auto *Res = FGather(GEP->getOperand(I)))
          return Res;
        if (auto *Cast = dyn_cast<CastInst>(GEP->getOperand(I))) {
          for (size_t J = 0; J < Cast->getNumOperands(); ++J) {
            if (auto *Res = FGather(Cast->getOperand(J)))
              return Res;
          }
        }
      }
    }
    auto *MP = new MemPort(&DB, Load);
    return MP;
  }

  /*!
   * \brief Starting with the given instructions, BFS out to find all
   * instrucitons slices. \param Q The given starting instructions. \param
   * Visited Push the found instruction.
   */
  void gatherEntryInsts(std::queue<Instruction *> &Q,
                        std::vector<Instruction *> &Visited) {
    auto &DB = *DBPtr;
    while (!Q.empty()) {
      auto *Cur = Q.front();
      int Idx = std::find(Visited.begin(), Visited.end(), Cur) - Visited.begin();
      Q.pop();
      LLVM_DEBUG(DSA_INFO << "Analyze Users of: " << *Cur);
      for (auto *Elem : Cur->users()) {
        auto *Inst = dyn_cast<Instruction>(Elem);
        if (!Inst) {
          LLVM_DEBUG(DSA_INFO << "Not a Inst: " << *Elem);
          continue;
        }
        if (!DB.Contains(Inst)) {
          LLVM_DEBUG(DSA_INFO << "Not in blocks: " << *Elem);
          continue;
        }
        if (!CanBeAEntry(Inst)) {
          LLVM_DEBUG(DSA_INFO << "Not a entry: " << *Elem);
          continue;
        }
        auto Iter = std::find(Visited.begin(), Visited.end(), Inst);
        if (Iter == Visited.end()) {
          Q.push(Inst);
          Visited.push_back(Inst);
        } else {
          if (Iter - Visited.begin() < Idx) {
            Visited.erase(Iter);
            Q.push(Inst);
            Visited.push_back(Inst);
          }
        }
      }
    }
  }

  /*!
   * \brief Inspect the operands of an instruction, and wrap them by DFG entry.
   * \param Inst The instruction to be inspected.
   */
  void inspectOperands(Instruction *Inst) {
    // TODO(@were): Make this a InstVisitor
    auto &DB = *DBPtr;
    LLVM_DEBUG(DSA_INFO << "Analyze Entry: "; Inst->dump());

    bool IsAcc = false;

    auto *ToOffload =
        !isa<BranchInst>(Inst)
            ? Inst
            : dyn_cast<Instruction>(dyn_cast<BranchInst>(Inst)->getCondition());

    for (size_t I = 0; I < ToOffload->getNumOperands(); ++I) {
      auto *Operand = ToOffload->getOperand(I);
      LLVM_DEBUG(DSA_INFO << "Operand: "; Operand->dump());
      if (DB.InThisDFG(Operand)) {
        LLVM_DEBUG(DSA_INFO << "Already-in skip!\n");
        continue;
      }
      if (auto *Phi = dyn_cast<PHINode>(Operand)) {

        std::queue<PHINode *> Q;
        std::set<PHINode *> Visited;

        for (Q.push(Phi), Visited.insert(Phi); !Q.empty();) {
          auto *Poll = Q.front();
          Q.pop();
          for (auto &InComing : Poll->incoming_values()) {
            if (InComing == Inst) {
              IsAcc = true;
              break;
            }
            if (auto *AnotherPhi = dyn_cast<PHINode>(InComing)) {
              if (!Visited.count(AnotherPhi)) {
                Q.push(AnotherPhi);
                Visited.insert(AnotherPhi);
              }
            }
          }
        }

        // FIXME: I am not sure if this will suffice. I relax the constraint
        // of detecting a accumulation by checking the BFS successors.
        CHECK(IsAcc) << "Phi should be an accumulator! " << *Phi;

      } else if (auto *Load = dyn_cast<LoadInst>(Operand)) {
        DB.Entries.push_back(differentiateMemoryStream(Load));
      } else if (auto *Consumee = dyn_cast<Instruction>(Operand)) {
        LLVM_DEBUG(DSA_INFO << "Not in this Nest: " << DB.Contains(Consumee)
                          << "\n");
        if (!DB.Contains(Consumee)) {
          if (DB.BelongOtherDFG(Consumee)) {
            DB.Entries.push_back(new StreamInPort(&DB, Consumee));
            LLVM_DEBUG(DSA_INFO << "Upstream:"; Consumee->dump());
          } else {
            DB.Entries.push_back(new InputConst(&DB, Consumee));
            LLVM_DEBUG(DSA_INFO << "Outer loop invariant:"; Consumee->dump());
          }
        }
      } else if (!isa<Constant>(Operand)) {
        DB.Entries.push_back(new InputConst(&DB, Operand));
        LLVM_DEBUG(DSA_INFO << "Other non const:"; Operand->dump());
      }
    }

    DFGEntry *Entry = nullptr;
    if (!IsAcc) {
      if (auto *BI = dyn_cast<BranchInst>(Inst)) {
        assert(BI->isConditional());
        if (ICmpInst *Cmp = dyn_cast<ICmpInst>(BI->getCondition())) {
          Predicate *PredEntry =
              findEquivPredicate(Cmp->getOperand(0), Cmp->getOperand(1));
          if (!PredEntry) {
            PredEntry = new Predicate(&DB, Cmp);
            DB.Entries.push_back(PredEntry);
          } else {
            PredEntry->addCond(Cmp);
          }
        } else if (Instruction *Cond =
                       dyn_cast<Instruction>(BI->getCondition())) {
          DB.Entries.push_back(new Predicate(&DB, Cond));
        }
        Entry = DB.Entries.back();
      } else {
        auto *CB = new ComputeBody(&DB, Inst);
        DB.Entries.push_back(CB);
        Entry = CB;
        LLVM_DEBUG(DSA_INFO << "Plain Inst: "; Inst->dump());
      }
    } else {
      assert(Inst->getOpcode() == BinaryOperator::Add ||
             Inst->getOpcode() == BinaryOperator::FAdd);
      auto *Acc = new Accumulator(&DB, Inst);
      DB.Entries.push_back(Acc);
      Entry = Acc;
      LLVM_DEBUG(DSA_INFO << "Accumulator: "; Inst->dump());
    }
    CHECK(Entry);
  }

  /*!
   * \brief Inspect the ends up of an instruction, and wrap them by DFG entry.
   * \param Inst The instruction to be inspected.
   */
  void inspectConsumers(Instruction *Inst) {
    auto &DB = *DBPtr;
    auto &Entries = DB.Entries;
    std::set<Instruction *> Equiv;
    findEquivPhIs(Inst, Equiv);
    for (auto *Elem : Equiv) {
      for (auto *User : Elem->users()) {
        if (auto *Store = dyn_cast<StoreInst>(User)) {
          LoadInst *Load = nullptr;

          if (auto *GEP =
                  dyn_cast<GetElementPtrInst>(Store->getPointerOperand())) {
            for (size_t I = 0; I < GEP->getNumOperands(); ++I) {
              if ((bool)(Load = dyn_cast<LoadInst>(GEP->getOperand(I)))) {
                break;
              }
            }
          }

          if (Load && DB.Contains(Load)) {
            if (auto *BO = dyn_cast<BinaryOperator>(Store->getValueOperand())) {
              bool IsUpdate = false;
              Value *AtomicOperand = nullptr;
              if (BO->getOpcode() == Instruction::BinaryOps::Add) {
                for (size_t I = 0; I < BO->getNumOperands(); ++I) {
                  auto *Operand = dyn_cast<LoadInst>(BO->getOperand(I));
                  if (Operand && Operand->getPointerOperand() ==
                                     Store->getPointerOperand()) {
                    IsUpdate = true;
                  } else {
                    AtomicOperand = BO->getOperand(I);
                  }
                }
              }
              Entries.push_back(new AtomicPortMem(
                  &DB, Load, Store, IsUpdate ? 0 : 3, Inst, AtomicOperand));
            } else {
              Entries.push_back(
                  new AtomicPortMem(&DB, Load, Store, 3, Inst, nullptr));
            }
            LLVM_DEBUG(DSA_INFO << "AtomicMem: " << *Inst);

          } else {
            auto *Out = new PortMem(&DB, Store);
            Entries.push_back(Out);
            LLVM_DEBUG(DSA_INFO << "PortMem: " << *Inst);
          }
        } else if (CanBeAEntry(User)) {
          // Understand this, why this cannot be an assertion?
          // Support downstream data consumption
          auto *Consume = dyn_cast<Instruction>(User);
          if (DB.BelongOtherDFG(Consume)) {
            auto *Out = new StreamOutPort(&DB, Inst);
            Entries.push_back(Out);
            LLVM_DEBUG(DSA_INFO << "Stream " << *Inst << " to " << *Consume);
          }
        } else {
          if (auto *UserInst = dyn_cast<Instruction>(User)) {
            if (isa<PHINode>(UserInst))
              continue;
            if (!DB.BelongOtherDFG(UserInst) && !DB.InThisDFG(UserInst)) {
              Entries.push_back(new OutputPort(&DB, Inst));
              LLVM_DEBUG(DSA_INFO << "Write to register: " << *Inst;
                         DSA_INFO << "User: " << UserInst);
            }
          }
        }
      }
    }
  }

  void Visit(DedicatedDFG *DDPtr) override {
    std::vector<Instruction *> Visited;
    DBPtr = DDPtr;
    auto &DD = *DDPtr;
    std::queue<Instruction *> Q;

    for (auto *BB : DD.InnerMost()->getBlocks()) {

      // I am not sure if this is a safe assumption: All the blocks have its own
      // immediate dom.
      auto *DomBB = DT->getNode(BB)->getIDom()->getBlock();

      // Is the assumption too strong here?
      // A intruction with a idom conditional instruction which does not belong
      // to this DFG indicates the predicate is always true.
      if (DD.InnerMost()->getBlocksSet().count(DomBB)) {
        auto *BI = dyn_cast<BranchInst>(&DomBB->back());
        if (BI->isConditional()) {
          Visited.push_back(BI);
        }
      }
      for (auto &Inst : *BB) {
        if (auto *Load = dyn_cast<LoadInst>(&Inst)) {
          Visited.push_back(Load);
          Q.push(Load);
        }
      }
      gatherEntryInsts(Q, Visited);
    }

    for (auto *Inst : Visited) {
      if (!isa<LoadInst>(Inst)) {
        inspectOperands(Inst);
        inspectConsumers(Inst);
      }
    }

    if (DD.Entries.empty()) {
      CHECK(Visited.size() == 1 && isa<LoadInst>(Visited[0]));
      DD.Entries.push_back(differentiateMemoryStream(dyn_cast<LoadInst>(Visited[0])));
      inspectConsumers(Visited[0]);
    }

    CHECK(!DD.Entries.empty());
  }

  void Visit(TemporalDFG *TD) override {
    DBPtr = TD;
    std::queue<Instruction *> Q;
    std::vector<Instruction *> Visited;
    CHECK(TD->getBlocks().size() == 1);

    for (auto *I = TD->Begin->getNextNode(); I != TD->End;
         I = I->getNextNode()) {
      if (CanBeAEntry(I)) {
        Q.push(I);
        Visited.push_back(I);
      }
    }
    gatherEntryInsts(Q, Visited);

    for (auto *Inst : Visited) {
      if (!isa<LoadInst>(Inst)) {
        inspectOperands(Inst);
        std::set<Instruction *> Equiv;
        inspectConsumers(Inst);
      }
    }
  }

  DFGEntryAnalyzer(xform::CodeGenContext &CGC) : DT(CGC.DT) {}
};

void extractSpadFromScope(DFGFile &DF, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR) {
  Instruction *Start = DF.Config;
  Instruction *End = DF.Fence;
  auto &Offset = DAR.SI.Offset;
  auto &Total = DAR.SI.Total;
  for (auto *BB : breadth_first(Start->getParent())) {
    iterator_range<BasicBlock::InstListType::iterator> Range(BB->begin(), BB->end());
    if (BB == Start->getParent()) {
      Range = iterator_range<BasicBlock::InstListType::iterator>(Start->getIterator(), BB->end());
    } else if (BB == End->getParent()) {
      Range = iterator_range<BasicBlock::InstListType::iterator>(BB->begin(), End->getIterator());
    }
    for (auto &Inst : Range) {
      if (auto *GEP = dyn_cast<GetElementPtrInst>(&Inst)) {
        if (auto *Alloc = dyn_cast<AllocaInst>(GEP->getPointerOperand())) {
          if (auto *AT = dyn_cast<ArrayType>(Alloc->getType()->getElementType())) {
            if (!Offset.count(Alloc)) {
              int Size = AT->getNumElements() * AT->getElementType()->getScalarSizeInBits() / 8;
              Offset[Alloc] = Total;
              DSA_LOG(SPAD) << *Alloc << ": " << Total;
              Total += Size;
            }
          }
        }
      }
    }
  }
  auto DFGs = DF.DFGFilter<DFGBase>();
  for (int i = 0; i < (int) DFGs.size(); ++i) { // NOLINT
    auto *DFG = DFGs[i];
    struct Analyzer : DFGEntryVisitor {
      void Visit(MemPort *MP) {
        auto &IdxLI = LI[MP];
        std::vector<const SCEV*> N;
        std::vector<const SCEV*> Stride;
        if (auto *LC = dyn_cast<LinearCombine>(IdxLI)) {
          int PI = LC->partialInvariant();
          auto &TripCnt = LC->TripCount;
          for (int j = PI; j < (int) TripCnt.size(); ++j) { // NOLINT
            N.push_back(TripCnt[j]->Raw);
            Stride.push_back(LC->Coef[j]->Raw);
          }
          if (LC->Coef.size() - PI == 3) {
            if (auto *CIS2D = dyn_cast<SCEVConstant>(Stride[1])) {
              if (auto *CIN1D = dyn_cast<SCEVConstant>(N[0])) {
                if (auto *CIS3D = dyn_cast<SCEVConstant>(Stride[2])) {
                  if (CIS2D->getAPInt().getSExtValue() == 0 && CIS3D->getAPInt().getSExtValue() != 0) {
                    int DType = MP->Load->getType()->getScalarSizeInBits() / 8;
                    int BufferSize = (CIN1D->getAPInt().getSExtValue() + 1) * 2 * DType * SLPMul;
                    DSA_LOG(BUFFET)
                      << SI.Buffet.size() << ": " << MP->dump() << ", "
                      << (CIN1D->getAPInt().getSExtValue() + 1) << " * " << SLPMul << " * " << DType
                      << " * 2 = " << BufferSize << "\n" << LC->toString() << "\n"
                      << SI.isSpad(MP->Load);
                    // MP, Total, BufferSize, -1
                    SI.Buffet.emplace_back(MP, SI.Total, BufferSize, -1, -1);
                    SI.Total += BufferSize;
                  }
                }
              }
            }
          }
        }
        SLPMul = 1;
      }

      void Visit(SLPMemPort *SMP) {
        SLPMul = SMP->Coal.size();
      }

      int SLPMul{1};
      int Unroll;
      SpadInfo &SI;
      DFGLoopInfo &DLI;
      std::unordered_map<DFGEntry*, SEWrapper*> &LI;
      IRBuilder<> *IB;
      ScalarEvolution &SE;
      Analyzer(int U, SpadInfo &SI, DFGLoopInfo &DLI,
               std::unordered_map<DFGEntry*, SEWrapper*> &LI,
               xform::CodeGenContext &CGC) :
        Unroll(U), SI(SI), DLI(DLI), LI(LI), IB(CGC.IB), SE(CGC.SE) {}
    };
    Analyzer A(DFG->getUnroll(), DAR.SI, DAR.DLI[i], DAR.LI[i], CGC);
    for (auto &Elem : DFG->Entries) {
      Elem->accept(&A);
    }
  }
}

void extractDFGFromScope(DFGFile &DF, dsa::xform::CodeGenContext &CGC) {
  auto *Start = DF.Config;
  auto *End = DF.Fence;
  auto *DT = CGC.DT;
  auto *LI = CGC.LI;
  // Extract the sketch of dedicated and temporal DFGs respectively.
  // The instruction entries in each DFG cannot be instantiated until all the
  // sketches are extracted, because we need this to analyze inter-DFG
  // communication in one pass.
  std::set<BasicBlock *> OutOfBound;
  for (auto *BBN : breadth_first(DT->getNode(End->getParent()))) {
    if (BBN->getBlock() == End->getParent())
      continue;
    OutOfBound.insert(BBN->getBlock());
  }
  for (auto *NestedLoop : *LI) {
    for (auto *SubLoop : breadth_first(NestedLoop)) {
      if (!DT->dominates(Start, SubLoop->getBlocks()[0]))
        continue;
      if (!SubLoop->getLoopID() || SubLoop->getLoopID()->getNumOperands() == 0)
        continue;
      bool InBound = true;
      for (auto *BB : SubLoop->getBlocks()) {
        if (OutOfBound.count(BB))
          InBound = false;
      }
      if (!InBound)
        continue;
      if (MDNode *MD = GetUnrollMetadata(SubLoop->getLoopID(),
                                         "llvm.loop.ss.dedicated")) {
        auto *MDFactor = dyn_cast<ConstantAsMetadata>(MD->getOperand(1));
        CHECK(MDFactor);
        int Factor = (int)MDFactor->getValue()->getUniqueInteger().getSExtValue();
        auto *DD = new DedicatedDFG(&DF, SubLoop, Factor);
        DF.addDFG(DD);
      }
    }
  }
  for (auto *BBN : breadth_first(DT->getNode(Start->getParent()))) {
    auto *BB = BBN->getBlock();
    auto Range = make_range(
        BB != Start->getParent() ? BB->begin() : Start->getIterator(),
        BB != End->getParent() ? BB->end() : End->getIterator());
    for (auto &I : Range) {
      auto *TemporalStart = dyn_cast<IntrinsicInst>(&I);
      if (!TemporalStart || TemporalStart->getIntrinsicID() !=
                                Intrinsic::ss_temporal_region_start)
        continue;
      // TODO: Maybe later we need control flow in the temporal regions
      bool Found = false;
      for (Instruction *Cur = TemporalStart; Cur != &Cur->getParent()->back();
           Cur = Cur->getNextNode()) {
        if (auto *TemporalEnd = dyn_cast<IntrinsicInst>(Cur)) {
          if (TemporalEnd->getIntrinsicID() !=
              Intrinsic::ss_temporal_region_end)
            continue;
          CHECK(TemporalEnd->getOperand(0) == TemporalStart);
          auto *TD = new TemporalDFG(&DF, TemporalStart, TemporalEnd);
          DF.addDFG(TD);
          Found = true;
          break;
        }
      }
      CHECK(Found);
    }
    if (BB == End->getParent()) {
      break;
    }
  }
  auto DFGs = DF.DFGFilter<DFGBase>();
  // All the sketches are extracted. Fill in the entries.
  for (int i = 0; i < (int) DFGs.size(); ++i) { // NOLINT
    DFGEntryAnalyzer DEA(CGC);
    DFGs[i]->accept(&DEA);
  }
}

ConfigInfo extractDFGPorts(std::string FName, DFGFile &DF, SpadInfo &SI) {
  auto *SBCONFIG = getenv("SBCONFIG");
  CHECK(SBCONFIG);
  auto Cmd = formatv("ss_sched {0} {1} {2} -e 0 > /dev/null", "-v", SBCONFIG, FName).str();
  LLVM_DEBUG(DSA_INFO << Cmd);
  CHECK(system(Cmd.c_str()) == 0) << "Not successfully scheduled! Try another DFG!";

  std::ifstream Ifs(FName + ".h");
  auto DFGs = DF.DFGFilter<DFGBase>();

  std::string Stripped(FName);
  while (Stripped.back() != '.')
    Stripped.pop_back();
  Stripped.pop_back();

  int ConfigSize = 0;
  std::string ConfigString;

  std::string Line;
  std::string PortPrefix(formatv("P_{0}_", Stripped).str());
  std::string IOPortPrefix = PortPrefix + "sub";
  std::string IClusterPrefix = PortPrefix + "ICluster";
  std::string OClusterPrefix = PortPrefix + "OCluster";
  std::string IndirectPrefix = PortPrefix + "indirect_";
  std::string IBuffetPrefix = PortPrefix + "IBuffet";
  std::string OBuffetPrefix = PortPrefix + "OBuffet";
  while (std::getline(Ifs, Line)) {
    std::istringstream Iss(Line);
    std::string Token;
    Iss >> Token;
    // #define xxx
    if (Token == "#define") {
      Iss >> Token;
      // #define P_dfgX_subY_vZ
      if (Token.find(IOPortPrefix) == 0) {
        int X, Y;
        auto Stripped = Token.substr(IOPortPrefix.size());
        CHECK(sscanf(Stripped.c_str(), "%d_v%d", &X, &Y) == 2);
        int Port;
        Iss >> Port;
        LLVM_DEBUG(DSA_INFO << "sub" << X << "v" << Y << " -> " << Port << "\n");
        CHECK(X >= 0 && X < (int) DFGs.size()) << Token << ": " << X << ", " << DFGs.size();
        CHECK(Y >= 0 && Y < (int) DFGs[X]->Entries.size());
        auto *Entry = DFGs[X]->Entries[Y];
        if (auto *PB = dyn_cast<PortBase>(Entry)) {
          PB->SoftPortNum = Port;
        } else if (auto *CB = dyn_cast<ComputeBody>(Entry)) {
          CHECK(false) << "This should be deprecated!";
          if (!CB->isImmediateAtomic()) {
            LLVM_DEBUG(DSA_INFO << "OutputPorts:\n");
            auto OutPorts = CB->getOutPorts();
            for (auto *Port : CB->getOutPorts()) {
              (void) Port;
              LLVM_DEBUG(Port->underlyingInst()->dump());
            }
            // FIXME: For now only one destination is supported
            // Later divergence will be supported
            CHECK(OutPorts.size() == 1)
                << *CB->underlyingInst() << " " << OutPorts.size();
            OutPorts[0]->SoftPortNum = Port;

            // Fill in the latency of each node.
            //{
            //  OutputPort *OP = OutPorts[0];
            //  std::string ON = OP->Parent->InThisDFG(OP->Output)->NameInDFG();
            //  for (auto SDVO : dfg.nodes<SSDFGVecOutput*>()) {
            //    if (SDVO->name() == ON) {
            //      OP->Latency = sched->latOf(SDVO);
            //      LLVM_DEBUG(DSA_INFO << "[lat] " << ON << ": " << OP->Latency
            //      << "\n"); break;
            //    }
            //  }
            //}

          } else {
            CB->SoftPortNum = Port;
          }
        } else {
          CHECK(false) << "DSAPass port information gathering unreachable!";
        }
        // #define dfgx_size size
      } else if (Token.find(IClusterPrefix) == 0 || Token.find(OClusterPrefix) == 0) {
        Token = Token.substr(IClusterPrefix.size());
        int X, Y, Port;
        CHECK(sscanf(Token.c_str(), "_%d_%d_", &X, &Y) == 2);
        Iss >> Port;
        auto *SLP = dyn_cast<PortBase>(DFGs[X]->Entries[Y]);
        CHECK(SLP);
        SLP->SoftPortNum = Port;
      } else if (Token.find(formatv("{0}_size", Stripped).str()) == 0) {
        Iss >> ConfigSize;
      } else if (Token.find(IndirectPrefix) == 0) {
        Token = Token.substr(IndirectPrefix.size());
        int X, Y;
        if (sscanf(Token.c_str(), "in_%d_%d", &X, &Y) == 2) {
          auto *IMP = dyn_cast<IndMemPort>(DFGs[X]->Entries[Y]);
          CHECK(IMP);
          Iss >> IMP->Index->SoftPortNum;
        } else {
          CHECK(sscanf(Token.c_str(), "out_%d_%d", &X, &Y) == 2);
          auto *IMP = dyn_cast<IndMemPort>(DFGs[X]->Entries[Y]);
          CHECK(IMP);
          Iss >> IMP->IndexOutPort;
        }
      } else if (Token.find(PortPrefix + "Operand_") == 0) {
        Token = Token.substr(std::string(PortPrefix + "Operand_").size());
        int X, Y;
        CHECK(sscanf(Token.c_str(), "sub%d_v%d_", &X, &Y) == 2);
        auto *APM = dyn_cast<AtomicPortMem>(DFGs[X]->Entries[Y]);
        CHECK(APM);
        Iss >> APM->OperandPort;
      } else if (Token.find(IBuffetPrefix) == 0 || Token.find(OBuffetPrefix) == 0) {
        bool IsInput = Token.find(IBuffetPrefix) == 0;
        Token = Token.substr(IBuffetPrefix.size());
        int X;
        CHECK(sscanf(Token.c_str(), "_%d_", &X));
        if (IsInput) {
          Iss >> std::get<3>(SI.Buffet[X]);
          DSA_INFO << "Buffet Read Port: " << std::get<3>(SI.Buffet[X]);
        } else {
          Iss >> std::get<4>(SI.Buffet[X]);
          DSA_INFO << "Buffet Write Port: " << std::get<4>(SI.Buffet[X]);
        }
      } else {
        CHECK(false) << "Unrecognized token: " << Token;
      }
      // char dfgx_config[size] = "filename:dfgx.sched";
    } else if (Token == "char") {
      // dfgx_config[size]
      Iss >> Token;
      // =
      Iss >> Token;
      // "filename:dfgx.sched";
      Iss >> Token;
      ConfigString = Token.substr(1, Token.size() - 3);
      ConfigString += std::string(ConfigSize - ConfigString.size() - 1, '\0');
    }
  }

  LLVM_DEBUG(DSA_INFO << "[Config] " << ConfigSize << ": " << ConfigString << "\n");

  return ConfigInfo(Stripped, ConfigString, ConfigSize);
}

void analyzeDFGLoops(DFGFile &DF, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR) {
  struct DFGLoopAnalyzer : DFGVisitor {
    void Visit(DedicatedDFG *DD) override {
      auto &LoopNest = DD->LoopNest;
      DLI.LoopNest = LoopNest;
      for (int i = (int) LoopNest.size() - 1; i >= 0; --i) { // NOLINT
        auto *NSCEV = SE.getBackedgeTakenCount(LoopNest[i]);
        if (isa<SCEVCouldNotCompute>(NSCEV)) {
          DLI.TripCount.emplace_back();
        } else {
          auto LoopSlice = std::vector<Loop*>(LoopNest.begin() + i + 1, LoopNest.end());
          DLI.TripCount.push_back(analysis::analyzeIndexExpr(&SE, NSCEV, LoopNest[i],
                                                             LoopSlice, DLI.TripCount));
          DSA_LOG(AFFINE) << i << ": " << DLI.TripCount.back()->toString();
        }
      }
      std::reverse(DLI.TripCount.begin(), DLI.TripCount.end());
    }

    void Visit(TemporalDFG *TD) override {}

    ScalarEvolution &SE;
    DFGLoopInfo &DLI;

    DFGLoopAnalyzer(ScalarEvolution &SE, DFGLoopInfo &DLI) : SE(SE), DLI(DLI) {}
  };

  for (auto *DB : DF.DFGFilter<DFGBase>()) {
    DAR.DLI.emplace_back();
    DFGLoopAnalyzer DLA(CGC.SE, DAR.DLI.back());
    DB->accept(&DLA);
  }
}


/*!
 * \brief Calulate the difference between two index. (B-A)
 *        If their difference is a constant, return it.
 *        If not, return -1.
 * \param A The result of affine analysis of A.
 * \param A The result of affine analysis of B.
 * \param SE The LLVM scalar evolution analyzer.
 * \param Signed If the result returned is abs.
 *        If abs is true, and -1 is returned, it is not a constant.
 *        If abs is false, constant should be garanteed to call.
 */
int64_t indexPairOffset(SEWrapper *ASW, SEWrapper *BSW, ScalarEvolution &SE, bool Signed) {
  bool SameDims = true;
  const SCEV *ABase = nullptr;
  const SCEV *BBase = nullptr;
  if (auto *A = dyn_cast<LinearCombine>(ASW)) {
    if (auto *B = dyn_cast<LinearCombine>(BSW)) {
      if (A->Coef.size() != B->Coef.size()) {
        CHECK(!Signed);
        return -1;
      }
      for (int j = 0; j < (int) A->Coef.size(); ++j) { // NOLINT
        if (A->Coef[j]->Raw != B->Coef[j]->Raw) {
          DSA_LOG(COAL) << *SE.getEqualPredicate(A->Coef[j]->Raw, B->Coef[j]->Raw);
          SameDims = false;
        }
      }
      if (SameDims && isa<LoopInvariant>(A->Base) && isa<LoopInvariant>(B->Base)) {
        ABase = A->Base->Raw;
        BBase = B->Base->Raw;
      }
    }
  } else {
    if (auto *A = dyn_cast<LoopInvariant>(ASW)) {
      if (auto *B = dyn_cast<LoopInvariant>(BSW)) {
        ABase = A->Raw;
        BBase = B->Raw;
      }
    }
  }
  if (ABase && BBase) {
    if (auto *Offset = dyn_cast<SCEVConstant>(SE.getAddExpr(BBase, SE.getNegativeSCEV(ABase)))) {
      auto Res = Offset->getAPInt().getSExtValue();
      return Signed ? Res : std::abs(Res);
    }
  }
  CHECK(!Signed) << "If signed, same access pattern should be garanteed!";
  return -1;
}

void analyzeAffineMemoryAccess(DFGFile &DF, dsa::xform::CodeGenContext &CGC,
                               DFGAnalysisResult &DAR) {

  struct AffineExtractor : DFGEntryVisitor {
    void Visit(MemPort *MP) override {
      auto &LI = DAR.LI[MP->Parent->ID];
      auto &DLI = DAR.DLI[MP->Parent->ID];
      LI[MP] = analyzeIndexExpr(&SE, SE.getSCEV(MP->Load->getPointerOperand()), MP, DLI.LoopNest,
                                DLI.TripCount);
    }
    void Visit(PortMem *PM) override {
      auto &LI = DAR.LI[PM->Parent->ID];
      auto &DLI = DAR.DLI[PM->Parent->ID];
      auto *Res = analyzeIndexExpr(&SE, SE.getSCEV(PM->Store->getPointerOperand()), PM, DLI.LoopNest,
                                   DLI.TripCount);
      if (auto *LC = dyn_cast<LinearCombine>(Res)) {
        LC->TripCount = DLI.TripCount;
        auto PI = LC->partialInvariant();
        if (!LC->Coef.empty()) {
          LC->Coef.erase(LC->Coef.begin(), LC->Coef.begin() + PI);
          LC->TripCount.erase(LC->TripCount.begin(), LC->TripCount.begin() + PI);
        }
      }
      LI[PM] = Res;
    }
    DFGAnalysisResult &DAR;
    ScalarEvolution &SE;
    AffineExtractor(DFGAnalysisResult &DAR, ScalarEvolution &SE) : DAR(DAR), SE(SE) {}
  };

  auto DFGs = DF.DFGFilter<DFGBase>();
  DAR.LI.resize(DFGs.size());
  AffineExtractor AE(DAR, CGC.SE);
  for (int i = 0; i < (int) DFGs.size(); ++i) { // NOLINT
    for (auto *Elem : DFGs[i]->Entries) {
      Elem->accept(&AE);
      {
        auto Iter = DAR.LI[i].find(Elem);
        if (Iter != DAR.LI[i].end()) {
          DSA_LOG(AFFINE) << Elem->dump();
          DSA_LOG(AFFINE) << Iter->second->toString();
        }
      }
    }
  }
}

template<typename T>
void gatherMemoryCoalescingImpl(std::vector<DFGEntry*> &Entries, ScalarEvolution &SE,
                                std::vector<int> &DSU,
                                std::unordered_map<DFGEntry*, SEWrapper*> &LI) {
  bool Iterative = true;
  while (Iterative) {
    Iterative = false;
    for (int i = 0; i < (int) Entries.size(); ++i) { // NOLINT
      if (auto *A = dyn_cast<T>(Entries[i])) {
        for (int j = i + 1; j < (int) Entries.size(); ++j) { // NOLINT
          if (auto *B = dyn_cast<T>(Entries[j])) {
            auto PtrA = A->underlyingInst()->getOperand(T::PtrOperandIdx);
            auto PtrB = B->underlyingInst()->getOperand(T::PtrOperandIdx);
            if (PtrA->getType() != PtrB->getType()) {
              continue;
            }
            auto Offset = indexPairOffset(LI[Entries[i]], LI[Entries[j]], SE, false);
            if (Offset == -1) {
              continue;
            }
            int DBits = PtrA->getType()->getPointerElementType()->getScalarSizeInBits();
            DSA_LOG(SLP) << i << " " << j << ": " << Offset;
            if (Offset == DBits / 8) {
              DSA_LOG(SLP) << *PtrA;
              DSA_LOG(SLP) << *PtrB;
              if (utils::DSUGetSet(i, DSU) != utils::DSUGetSet(j, DSU)) {
                DSU[utils::DSUGetSet(i, DSU)] = DSU[utils::DSUGetSet(j, DSU)];
                Iterative = true;
              }
            }
          }
        }
      }
    }
  }
}

template<typename TSLP, typename TEntry>
void constructCoalescedMemory(DFGBase *DB, std::vector<DFGEntry*> &Entries,
                              std::vector<int> &DSU, std::vector<int> &DSize,
                              ScalarEvolution &SE, std::unordered_map<DFGEntry*, SEWrapper*> &LI,
                              std::vector<int> &Remove) {
  for (int j = 0; j < (int) Entries.size(); ++j) { // NOLINT
    if (auto *Entry = dyn_cast<TEntry>(Entries[j])) {
      int DSet = utils::DSUGetSet(j, DSU);
      if (DSet == j && DSize[DSet] != 1) {
        auto *Res = new TSLP(DB);
        Res->Coal.push_back(Entry);
        Entries[j] = Res;
      }
    }
  }
  for (int j = 0; j < (int) Entries.size(); ++j) { // NOLINT
    if (auto *Entry = dyn_cast<TEntry>(Entries[j])) {
      int DSet = utils::DSUGetSet(j, DSU);
      if (DSet != j && DSize[DSet] != 1) {
        auto *SLP = dyn_cast<TSLP>(Entries[DSet]);
        CHECK(SLP);
        DSA_LOG(SLP) << DSet << "(" << DSize[DSet] << "): " << Entry->dump();
        SLP->Coal.push_back(Entry);
        Remove.push_back(j);
      }
    }
  }
  for (int i = 0; i < (int) Entries.size(); ++i) { // NOLINT
    if (auto *Entry = dyn_cast<TSLP>(Entries[i])) {
      auto &V = Entry->Coal;
      auto FCmp = [&V, &SE, &LI](TEntry *A, TEntry *B) {
        auto KeyA = indexPairOffset(LI[V[0]], LI[A], SE, true);
        auto KeyB = indexPairOffset(LI[V[0]], LI[B], SE, true);
        return KeyA < KeyB;
      };
      std::sort(V.begin(), V.end(), FCmp);
      for (int j = 0; j < (int) V.size(); ++j) { // NOLINT
        V[j]->ID = j;
      }
      auto *Raw = LI[Entry->Coal[0]];
      LinearCombine *L = nullptr;
      if (isa<LinearCombine>(Raw)) {
        L = dyn_cast<LinearCombine>(Raw);
      } else if (auto LI = dyn_cast<LoopInvariant>(Raw)) {
        L = LI->toLinearCombine(&SE);
      }
      CHECK(L);
      L = new LinearCombine(*L);
      auto Ptr = Entry->Coal[0]->underlyingInst()->getOperand(TEntry::PtrOperandIdx);
      int DBits = Ptr->getType()->getPointerElementType()->getScalarSizeInBits();
      auto &TripCount = L->TripCount;
      const auto *ExtraTC = SE.getConstant(APInt(64, Entry->Coal.size() - 1, true));
      TripCount.insert(TripCount.begin(), new analysis::LoopInvariant(Entry, ExtraTC));
      auto &Coef = L->Coef;
      const auto *ExtraCoef = SE.getConstant(APInt(64, DBits / 8, true));
      Coef.insert(L->Coef.begin(), new LoopInvariant(Entry, ExtraCoef));
      // If it used to be a constant, we need to make the higher dimensions to be zero-padded.
      if (Coef.size() == 1) {
        auto *SCEVZero = SE.getConstant(APInt(64, 0, true));
        auto *ZeroCoef = new LoopInvariant(Entry, SCEVZero);
        Coef.reserve(TripCount.size());
        while (Coef.size() < TripCount.size()) {
          Coef.push_back(ZeroCoef);
        }
      }
      LI[Entry] = L;
    }
  }
}

void gatherMemoryCoalescing(DFGFile &DF, ScalarEvolution &SE, DFGAnalysisResult &DAR) {
  auto DFGs = DF.DFGFilter<DFGBase>();
  CHECK(DAR.DLI.size() == DFGs.size());
  for (int i = 0; i < (int) DFGs.size(); ++i) { // NOLINT
    auto &Entries = DFGs[i]->Entries;
    std::vector<int> DSU;
    DSU.resize(Entries.size());
    for (int j = 0; j < (int) Entries.size(); ++j) { // NOLINT
      DSU[j] = j;
    }
    gatherMemoryCoalescingImpl<MemPort>(Entries, SE, DSU, DAR.LI[i]);
    gatherMemoryCoalescingImpl<PortMem>(Entries, SE, DSU, DAR.LI[i]);
    // TODO(@were): Make too wide port splitted later.
    std::vector<int> DSize(Entries.size(), 0);
    for (int j = 0; j < (int) Entries.size(); ++j) { // NOLINT
      ++DSize[utils::DSUGetSet(j, DSU)];
    }
    std::vector<int> Remove;
    constructCoalescedMemory<SLPMemPort, MemPort>(DFGs[i], Entries, DSU, DSize, SE, DAR.LI[i], Remove);
    constructCoalescedMemory<SLPPortMem, PortMem>(DFGs[i], Entries, DSU, DSize, SE, DAR.LI[i], Remove);
    std::sort(Remove.begin(), Remove.end());
    for (int j = 0; j < (int) Remove.size(); ++j) { // NOLINT
      Entries.erase(Entries.begin() + Remove[j] - j);
    }
    for (int j = 0; j < (int) Entries.size(); ++j) { // NOLINT
      Entries[j]->ID = j;
    }
  }
}

bool SpadInfo::isSpad(Value *Ptr) {
  auto Cond = [this](Value *Val) -> bool {
    if (auto *AI = dyn_cast<AllocaInst>(Val)) {
      return Offset.count(AI);
    }
    return false;
  };
  if (Cond(Ptr)) {
    return true;
  }
  if (auto *Inst = dyn_cast<Instruction>(Ptr)) {
    std::queue<Instruction*> Q;
    std::set<Instruction*> Visited;
    Q.push(Inst);
    Visited.insert(Inst);
    while (!Q.empty()) {
      auto *Cur = Q.front();
      Q.pop();
      for (auto &Operand: Cur->operands()) {
        if (auto *Prev = dyn_cast<Instruction>(Operand)) {
          if (Cond(Prev)) {
            return true;
          }
          if (!Visited.count(Prev)) {
            Q.push(Prev);
            Visited.insert(Prev);
          }
        }
      }
    }
  }
  return false;
}

void analyzeAccumulatorTags(DFGFile &DF, xform::CodeGenContext &CGC,
                            DFGAnalysisResult &DAR) {
  auto Graphs = DF.DFGFilter<DFGBase>();
  for (int i = 0; i < (int) Graphs.size(); ++i) { // NOLINT
    auto &LI = DAR.LI[i];
    auto &Loops = DAR.DLI[i].LoopNest;
    std::unordered_map<DFGEntry*, int> Cnt;
    if (auto *DD = dyn_cast<DedicatedDFG>(Graphs[i])) {
      for (auto *Acc : DD->EntryFilter<Accumulator>()) {
        auto V = analysis::bfsOperands(DD, Acc->Operation, nullptr).first;
        InputPort *Tag = nullptr;
        for (auto &Elem : V) {
          auto *DE = Acc->Parent->InThisDFG(Elem);
          if (!DE) {
            continue;
          }
          if (auto *IP = dyn_cast<InputPort>(DE)) {
            auto Iter = LI.find(IP);
            if (Iter != LI.end()) {
              if (auto *LC = dyn_cast<LinearCombine>(Iter->second)) {
                if (LC->partialInvariant() == 0) {
                  if (!Tag) {
                    IP->Tagged.push_back(Acc);
                    Tag = IP;
                  } else if (IP->Tagged.size() >= Tag->Tagged.size()) {
                    CHECK(Acc == Tag->Tagged.back());
                    Tag->Tagged.pop_back();
                    IP->Tagged.push_back(Acc);
                  }
                }
              }
            }
          }
        }
        if (Tag) {
          for (auto *User : Acc->Operation->users()) {
            if (auto *Inst = dyn_cast<Instruction>(User)) {
              if (!Graphs[i]->InThisDFG(Inst)) {
                if (!Graphs[i]->BelongOtherDFG(Inst)) {
                  continue;
                }
              }
              for (int j = (int) Loops.size() - 1; j >= 0; --j) { // NOLINT
                if (Loops[j]->contains(Acc->Operation) && !Loops[j]->contains(Inst)) {
                  DSA_LOG(ACC) << "User: " << *Inst;
                  DSA_LOG(ACC) << Acc->dump() << " Reset@" << j;
                  Acc->ResetLevel = j;
                  break;
                }
              }
            }
          }
        }
      }
    }
    for (auto *IP : Graphs[i]->EntryFilter<InputPort>()) {
      if (!IP->Tagged.empty()) {
        DSA_LOG(ACC) << IP->dump(); 
        auto Iter = DAR.LI[i].find(IP);
        CHECK(Iter != DAR.LI[i].end());
        DSA_LOG(ACC) << Iter->second << " " << Iter->second->toString();
        auto *LC = dyn_cast<LinearCombine>(Iter->second);
        CHECK(LC);
        for (auto *Acc : IP->Tagged) {
          if (isa<SLPMemPort>(IP)) {
            ++Acc->ResetLevel;
          }
          CHECK(Acc->ResetLevel < (int) LC->Coef.size());
          DSA_LOG(ACC) << Acc->dump() << ", Reset@" << Acc->ResetLevel;
        }
        DSA_LOG(ACC) << "Finalized reset: " << resetLevel(IP);
      }
    }
  }
}

void fuseAffineDimensions(DFGFile &DF, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR) {
  struct FuseInfoExtractor : DFGEntryVisitor {
    void Visit(MemPort *MP) override {
      DBits = MP->Load->getType()->getScalarSizeInBits();
      Padding = MP->fillMode();
      CutOff = resetLevel(MP);
    }
    void Visit(PortMem *PM) override {
      DBits = PM->Store->getValueOperand()->getType()->getScalarSizeInBits();
    }
    void Visit(SLPMemPort *SMP) override {
      auto *MP = SMP->Coal[0];
      DBits = MP->Load->getType()->getScalarSizeInBits();
      CutOff = resetLevel(SMP);
    }
    void Visit(SLPPortMem *SPM) override {
      auto *PM = SPM->Coal[0];
      DBits = PM->Store->getValueOperand()->getType()->getScalarSizeInBits();
    }
    int DBits{-1};
    int Padding{0};
    int CutOff{-1};
  };
  auto Graphs = DF.DFGFilter<DFGBase>();
  for (int i = 0; i < (int) Graphs.size(); ++i) { // NOLINT
    auto *DFG = Graphs[i];
    auto &LI = DAR.LI[i];
    for (auto &Elem : LI) {
      if (auto *Pattern = dyn_cast<LinearCombine>(Elem.second)) {
        FuseInfoExtractor FIE;
        Elem.first->accept(&FIE);
        if (FIE.CutOff == -1) {
          FIE.CutOff = Pattern->TripCount.size() - 1;
        }
        CHECK(FIE.DBits != -1);
        DSA_LOG(FUSE) << Pattern << " " << Elem.first->dump();
        DSA_LOG(FUSE) << "Before: " << Pattern->toString() << ", CutOff: " << FIE.CutOff;
        int Before = Pattern->Coef.size();
        fuseInnerDimensions(*Pattern, FIE.DBits / 8, DFG->getUnroll(), CGC.SE,
                            Pattern->TripCount.size() - FIE.CutOff);
        DSA_LOG(FUSE) << "After: " << Pattern->toString();
        if (auto *IP = dyn_cast<InputPort>(Elem.first)) {
          int Delta = Before - Pattern->Coef.size();
          DSA_LOG(FUSE) << "Fuse Delta: " << Delta;
          DSA_LOG(FUSE) << IP->dump();
          for (auto *Acc : IP->Tagged) {
            Acc->ResetLevel -= Delta;
            DSA_LOG(FUSE) << Acc->dump() << ": " << Acc->ResetLevel;
          }
        }
      }
    }
  }
}

int resetLevel(InputPort *IP) {
  if (IP->Tagged.empty()) {
    return -1;
  }
  auto FRed = [](int X, Accumulator *A) { return std::min(X, A->ResetLevel); };
  return std::accumulate(IP->Tagged.begin(), IP->Tagged.end(), INT_MAX, FRed);
}

} // namespace analysis
} // namespace dsa
