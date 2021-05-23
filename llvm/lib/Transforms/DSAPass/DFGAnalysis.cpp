#include "dsa/debug.h"

#include "./DFGAnalysis.h"

#define DEBUG_TYPE "dfg-analysis"

namespace dsa {
namespace analysis {

std::vector<std::pair<IntrinsicInst *, IntrinsicInst *>>
GatherConfigScope(Function &F) {
  std::vector<std::pair<IntrinsicInst *, IntrinsicInst *>> Res;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto End = dyn_cast<IntrinsicInst>(&I)) {
        if (End->getIntrinsicID() == Intrinsic::ss_config_end) {
          auto Start = dyn_cast<IntrinsicInst>(End->getOperand(0));
          CHECK(Start && Start->getIntrinsicID() == Intrinsic::ss_config_start);
          Res.emplace_back(Start, End);
        }
      }
    }
  }
  return Res;
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
  void FindEquivPHIs(Instruction *Inst, std::set<Instruction *> &Equiv) {
    std::queue<Instruction *> Q;
    Q.push(Inst);
    Equiv.insert(Inst);
    while (!Q.empty()) {
      if (auto PHI = dyn_cast<PHINode>(Q.front())) {
        for (auto &Elem : PHI->incoming_values()) {
          auto Casted = dyn_cast<Instruction>(Elem);
          if (!Casted)
            continue;
          if (Equiv.count(Casted))
            continue;
          Q.push(Casted);
          Equiv.insert(Casted);
        }
      }
      for (auto User : Q.front()->users()) {
        auto Phi = dyn_cast<PHINode>(User);
        if (!Phi)
          continue;
        if (Equiv.count(Phi))
          continue;
        Q.push(Phi);
        Equiv.insert(Phi);
      }
      Q.pop();
    }

    LLVM_DEBUG(INFO << "equiv of " << *Inst; for (auto I
                                                  : Equiv) { INFO << *I; });
  }

  Predicate *FindEquivPredicate(Value *LHS, Value *RHS) {
    auto &DB = *DBPtr;
    for (auto Elem : DB.EntryFilter<Predicate>()) {
      if (Elem->Cond[0]->getOperand(0) == LHS &&
          Elem->Cond[0]->getOperand(1) == RHS)
        return Elem;
      if (Elem->Cond[0]->getOperand(1) == LHS &&
          Elem->Cond[0]->getOperand(0) == RHS)
        return Elem;
    }
    return nullptr;
  }

  DFGEntry *DifferentiateMemoryStream(LoadInst *Load) {
    auto &DB = *DBPtr;
    if (auto GEP = dyn_cast<GetElementPtrInst>(Load->getPointerOperand())) {

      auto BFSBack = BFSOperands(GEP);

      auto fLoad = [this, Load, BFSBack, &DB](Value *Val) -> DFGEntry * {
        LoadInst *IdxLoad = nullptr;
        for (auto Elem : BFSBack.first) {
          if (auto ThisLoad = dyn_cast<LoadInst>(Elem)) {
            CHECK(!IdxLoad) << "For now only one level indirect supported!";
            IdxLoad = ThisLoad;
          }
        }
        if (IdxLoad) {
          return new IndMemPort(&DB, IdxLoad, Load);
        }
        return nullptr;
      };

      auto fGather = [Load, GEP, this, &DB](Value *Val) -> DFGEntry * {
        auto DD = dyn_cast<DedicatedDFG>(&DB);

        auto Casted = dyn_cast<Instruction>(Val);
        if (!Casted)
          return nullptr;

        if (!DD)
          return nullptr;

        {
          bool simpleLoop = false;
          auto BI =
              dyn_cast<BranchInst>(&DD->InnerMost()->getLoopLatch()->back());
          auto Latch = DD->InnerMost()->getLoopLatch();
          assert(BI);
          for (auto BB : BI->successors()) {
            if (BB == Latch) {
              simpleLoop = true;
            }
          }
          if (simpleLoop) {
            return nullptr;
          }
        }

        std::set<Instruction *> Equiv;
        LLVM_DEBUG(dbgs() << "Equiv of: ");
        FindEquivPHIs(Casted, Equiv);

        Value *TripCount = nullptr;
        SmallVector<std::pair<ICmpInst *, bool>, 0> Conditions;
        for (auto Elem : Equiv) {
          if (auto PHI = dyn_cast<PHINode>(Elem)) {
            for (auto &Essense : PHI->incoming_values()) {
              auto Inst = dyn_cast<Instruction>(Essense);
              if (Inst && !isa<PHINode>(Inst)) {
                if (Inst->getOpcode() == BinaryOperator::Add) {
                  auto DomBB =
                      DT->getNode(Inst->getParent())->getIDom()->getBlock();
                  LLVM_DEBUG(DomBB->back().dump(); Inst->dump());
                  auto BI = dyn_cast<BranchInst>(&DomBB->back());
                  assert(BI);
                  if (BI->isConditional()) {
                    auto CondCmp = dyn_cast<ICmpInst>(BI->getCondition());
                    bool OK = true;
                    for (size_t i = 0; i < Conditions.size(); ++i) {
                      auto AlreadyCmp = Conditions[i].first;
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
            LLVM_DEBUG(dbgs() << "Latch"; Elem->dump());
            for (auto Elem_ : Elem->users()) {
              auto Cmp = dyn_cast<ICmpInst>(Elem_);
              if (!Cmp)
                continue;
              if (Cmp->getParent() != Elem->getParent())
                continue;
              assert(Cmp->getPredicate() == ICmpInst::Predicate::ICMP_SLT &&
                     "For now only support SLT");
              for (size_t i = 0; i < Cmp->getNumOperands(); ++i) {
                if (Cmp->getOperand(i) != Elem) {
                  TripCount = Cmp->getOperand(i);
                  LLVM_DEBUG(dbgs() << "TripCount"; TripCount->dump());
                }
              }
            }
          }
        }
        if (TripCount && !Conditions.empty()) {

          int Mask = 0;
          SmallVector<bool, 0> Reverse;

          auto Pred = FindEquivPredicate(Conditions[0].first->getOperand(0),
                                         Conditions[0].first->getOperand(1));

          if (!Pred) {
            Pred = new Predicate(&DB, Conditions[0].first);
            DB.Entries.push_back(Pred);
          }

          for (size_t i = 0; i < Conditions.size(); ++i) {
            Reverse.push_back(Pred->addCond(Conditions[i].first));
          }

          for (size_t i = 0; i < Conditions.size(); ++i) {
            auto Cond = Conditions[i];
            LLVM_DEBUG(dbgs() << "Moveforward: " << Cond.second << " ";
                       Cond.first->dump());
            int SubMask = PredicateToInt(Cond.first->getPredicate(),
                                         Cond.second, Reverse[i]);
            Mask |= SubMask;
          }

          LLVM_DEBUG(dbgs() << "Forward mask: " << Mask << "\n");
          // FIXME: GEP for not is good enough, but we need a better way to
          // figure out the start
          //        pointer later.
          return new CtrlMemPort(&DB, Load, GEP->getOperand(0), TripCount, Pred,
                                 Mask);
        }
        LLVM_DEBUG(dbgs() << "\n");
        return nullptr;
      };

      // TODO(@were): Can I hoist BFSOperands out here?
      for (size_t i = 1; i < GEP->getNumOperands(); ++i) {
        if (auto Res = fLoad(GEP->getOperand(i)))
          return Res;
        if (auto Res = fGather(GEP->getOperand(i)))
          return Res;
        if (auto Cast = dyn_cast<CastInst>(GEP->getOperand(i))) {
          for (size_t j = 0; j < Cast->getNumOperands(); ++j) {
            if (auto Res = fGather(Cast->getOperand(j)))
              return Res;
          }
        }
      }
    }
    return new MemPort(&DB, Load);
  }

  /*!
   * \brief Starting with the given instructions, BFS out to find all
   * instrucitons slices. \param Q The given starting instructions. \param
   * Visited Push the found instruction.
   */
  void GatherEntryInsts(std::queue<Instruction *> &Q,
                        std::vector<Instruction *> &Visited) {
    auto &DB = *DBPtr;
    while (!Q.empty()) {
      auto Cur = Q.front();
      Q.pop();
      LLVM_DEBUG(INFO << "Analyze Users of: " << *Cur);
      for (auto Elem : Cur->users()) {
        auto Inst = dyn_cast<Instruction>(Elem);
        if (!Inst) {
          LLVM_DEBUG(INFO << "Not a Inst: " << *Elem);
          continue;
        }
        if (!DB.Contains(Inst)) {
          LLVM_DEBUG(INFO << "Not in blocks: " << *Elem);
          continue;
        }
        if (!CanBeAEntry(Inst)) {
          LLVM_DEBUG(INFO << "Not a entry: " << *Elem);
          continue;
        }
        if (std::find(Visited.begin(), Visited.end(), Inst) == Visited.end()) {
          Q.push(Inst);
          Visited.push_back(Inst);
        }
      }
    }
  }

  /*!
   * \brief Inspect the operands of an instruction, and wrap them by DFG entry.
   * \param Inst The instruction to be inspected.
   */
  void InspectOperands(Instruction *Inst) {
    // TODO(@were): Make this a InstVisitor
    auto &DB = *DBPtr;
    LLVM_DEBUG(dbgs() << "Analyze Entry: "; Inst->dump());

    bool isAcc = false;

    auto ToOffload =
        !isa<BranchInst>(Inst)
            ? Inst
            : dyn_cast<Instruction>(dyn_cast<BranchInst>(Inst)->getCondition());

    for (size_t i = 0; i < ToOffload->getNumOperands(); ++i) {
      auto Operand = ToOffload->getOperand(i);
      LLVM_DEBUG(dbgs() << "Operand: "; Operand->dump());
      if (DB.InThisDFG(Operand)) {
        LLVM_DEBUG(dbgs() << "Already-in skip!\n");
        continue;
      }
      if (auto Phi = dyn_cast<PHINode>(Operand)) {

        std::queue<PHINode *> Q;
        std::set<PHINode *> Visited;

        for (Q.push(Phi), Visited.insert(Phi); !Q.empty();) {
          auto Poll = Q.front();
          Q.pop();
          for (auto &InComing : Poll->incoming_values()) {
            if (InComing == Inst) {
              isAcc = true;
              break;
            }
            if (auto AnotherPhi = dyn_cast<PHINode>(InComing)) {
              if (!Visited.count(AnotherPhi)) {
                Q.push(AnotherPhi);
                Visited.insert(AnotherPhi);
              }
            }
          }
        }

        // FIXME: I am not sure if this will suffice. I relax the constraint
        // of detecting a accumulation by checking the BFS successors.
        CHECK(isAcc) << "Phi should be an accumulator! " << *Phi;

      } else if (auto Load = dyn_cast<LoadInst>(Operand)) {
        DB.Entries.push_back(DifferentiateMemoryStream(Load));
      } else if (auto Consumee = dyn_cast<Instruction>(Operand)) {
        LLVM_DEBUG(dbgs() << "Not in this Nest: " << DB.Contains(Consumee)
                          << "\n");
        if (!DB.Contains(Consumee)) {
          if (DB.BelongOtherDFG(Consumee)) {
            DB.Entries.push_back(new StreamInPort(&DB, Consumee));
            LLVM_DEBUG(dbgs() << "Upstream:"; Consumee->dump());
          } else {
            DB.Entries.push_back(new InputConst(&DB, Consumee));
            LLVM_DEBUG(dbgs() << "Outer loop invariant:"; Consumee->dump());
          }
        }
      } else if (!isa<Constant>(Operand)) {
        DB.Entries.push_back(new InputConst(&DB, Operand));
        LLVM_DEBUG(dbgs() << "Other non const:"; Operand->dump());
      }
    }

    DFGEntry *Entry = nullptr;
    if (!isAcc) {
      if (auto BI = dyn_cast<BranchInst>(Inst)) {
        assert(BI->isConditional());
        if (ICmpInst *Cmp = dyn_cast<ICmpInst>(BI->getCondition())) {
          Predicate *PredEntry =
              FindEquivPredicate(Cmp->getOperand(0), Cmp->getOperand(1));
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
        auto CB = new ComputeBody(&DB, Inst);
        DB.Entries.push_back(CB);
        Entry = CB;
        LLVM_DEBUG(dbgs() << "Plain Inst: "; Inst->dump());
      }
    } else {
      assert(Inst->getOpcode() == BinaryOperator::Add ||
             Inst->getOpcode() == BinaryOperator::FAdd);
      auto CS = new CtrlSignal(&DB);
      DB.Entries.push_back(CS);
      auto Acc = new Accumulator(&DB, Inst, CS);
      DB.Entries.push_back(Acc);
      CS->Controlled = Acc;
      Entry = Acc;
      LLVM_DEBUG(dbgs() << "Accumulator: "; Inst->dump());
    }
    CHECK(Entry);
  }

  /*!
   * \brief Inspect the ends up of an instruction, and wrap them by DFG entry.
   * \param Inst The instruction to be inspected.
   */
  void InspectConsumers(Instruction *Inst) {
    auto &DB = *DBPtr;
    auto &Entries = DB.Entries;
    std::set<Instruction *> Equiv;
    FindEquivPHIs(Inst, Equiv);
    for (auto Elem : Equiv) {
      for (auto User : Elem->users()) {
        if (auto Store = dyn_cast<StoreInst>(User)) {
          LoadInst *Load = nullptr;

          if (auto GEP =
                  dyn_cast<GetElementPtrInst>(Store->getPointerOperand())) {
            for (size_t i = 0; i < GEP->getNumOperands(); ++i) {
              if ((bool)(Load = dyn_cast<LoadInst>(GEP->getOperand(i)))) {
                break;
              }
            }
          }

          if (Load && DB.Contains(Load)) {
            if (auto BO = dyn_cast<BinaryOperator>(Store->getValueOperand())) {
              bool isUpdate = false;
              Value *AtomicOperand = nullptr;
              if (BO->getOpcode() == Instruction::BinaryOps::Add) {
                for (size_t i = 0; i < BO->getNumOperands(); ++i) {
                  auto Operand = dyn_cast<LoadInst>(BO->getOperand(i));
                  if (Operand && Operand->getPointerOperand() ==
                                     Store->getPointerOperand()) {
                    isUpdate = true;
                  } else {
                    AtomicOperand = BO->getOperand(i);
                  }
                }
              }
              Entries.push_back(new AtomicPortMem(
                  &DB, Load, Store, isUpdate ? 0 : 3, Inst, AtomicOperand));
            } else {
              Entries.push_back(
                  new AtomicPortMem(&DB, Load, Store, 3, Inst, nullptr));
            }
            LLVM_DEBUG(INFO << "AtomicMem: " << *Inst);

          } else {
            auto Out = new PortMem(&DB, Store);
            Entries.push_back(Out);
            LLVM_DEBUG(INFO << "PortMem: " << *Inst);
          }
        } else if (CanBeAEntry(User)) {
          // Understand this, why this cannot be an assertion?
          // Support downstream data consumption
          auto Consume = dyn_cast<Instruction>(User);
          if (DB.BelongOtherDFG(Consume)) {
            auto Out = new StreamOutPort(&DB, Inst);
            Entries.push_back(Out);
            LLVM_DEBUG(INFO << "Stream " << *Inst << " to " << *Consume);
          }
        } else {
          if (auto UserInst = dyn_cast<Instruction>(User)) {
            if (isa<PHINode>(UserInst))
              continue;
            if (!DB.BelongOtherDFG(UserInst) && !DB.InThisDFG(UserInst)) {
              Entries.push_back(new OutputPort(&DB, Inst));
              LLVM_DEBUG(INFO << "Write to register: " << *Inst;
                         INFO << "User: " << UserInst);
            }
          }
        }
      }
    }
  }

  std::pair<std::set<Instruction *>, std::set<Instruction *>>
  BFSOperands(Instruction *From) {
    auto &DB = *DBPtr;
    std::set<Instruction *> Visited, OutBound;
    std::queue<Instruction *> Q;
    Visited.insert(From);
    Q.push(From);
    while (!Q.empty()) {
      auto Cur = Q.front();
      Q.pop();
      for (size_t i = 0; i < Cur->getNumOperands(); ++i) {
        if (auto Inst = dyn_cast<Instruction>(Cur->getOperand(i))) {
          if (!DT->dominates(Inst, From)) {
            continue;
          }
          if (!Visited.count(Inst)) {
            if (DB.InThisScope(Inst)) {
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

  void Visit(DedicatedDFG *DDPtr) {
    std::vector<Instruction *> Visited;
    DBPtr = DDPtr;
    auto &DD = *DDPtr;
    std::queue<Instruction *> Q;

    for (auto BB : DD.InnerMost()->getBlocks()) {

      // I am not sure if this is a safe assumption: All the blocks have its own
      // immediate dom.
      auto DomBB = DT->getNode(BB)->getIDom()->getBlock();

      // Is the assumption too strong here?
      // A intruction with a idom conditional instruction which does not belong
      // to this DFG indicates the predicate is always true.
      if (DD.InnerMost()->getBlocksSet().count(DomBB)) {
        auto BI = dyn_cast<BranchInst>(&DomBB->back());
        if (BI->isConditional()) {
          Visited.push_back(BI);
        }
      }
      for (auto &Inst : *BB) {
        if (auto Load = dyn_cast<LoadInst>(&Inst)) {
          Visited.push_back(Load);
          Q.push(Load);
        }
      }
      GatherEntryInsts(Q, Visited);
    }

    for (auto Inst : Visited) {
      if (!isa<LoadInst>(Inst)) {
        InspectOperands(Inst);
        InspectConsumers(Inst);
      }
    }

    if (DD.Entries.empty()) {
      CHECK(Visited.size() == 1 && isa<LoadInst>(Visited[0]));
      DD.Entries.push_back(DifferentiateMemoryStream(dyn_cast<LoadInst>(Visited[0])));
      InspectConsumers(Visited[0]);
      for (auto Elem : DD.Entries) {
        INFO << *Elem;
      }
    }

    CHECK(!DD.Entries.empty());


    // TODO(@were): Open this to support data move.
    // for (auto Inst : Visited) {
    //   auto Load = dyn_cast<LoadInst>(Inst);

    //   if (!Load)
    //     continue;

    //   if (!DD.InThisDFG(Load)) {
    //     auto MP = dyn_cast<PortBase>(DifferentiateMemoryStream(Load));
    //     CHECK(MP);
    //     Entries.push_back(MP);
    //     size_t j = Entries.size();
    //     InspectConsumers(Load);
    //     // FIXME: For now we only support one consumer.
    //     CHECK(j + 1 == DD.Entries.size()) << "A load without usage?";
    //     for (; j < Entries.size(); ++j) {
    //       auto Entry = Entries[j];
    //       if (auto PM = dyn_cast<PortMem>(Entry)) {
    //         // FIXME(@were): Deprecate the reserved ports.
    //         (void) PM; // Pretend I used this variable to avoid warnings.
    //         CHECK(false) << "Data movement not supported yet!";
    //       } else if (auto APM = dyn_cast<AtomicPortMem>(Entry)) {
    //         assert(APM->Store->getValueOperand() == MP->UnderlyingInst());
    //         APM->Op = MP->UnderlyingInst();
    //         // FIXME: This is not correct...
    //         // MP->SoftPortNum = getNextReserved();
    //       } else {
    //         assert(false && "This should not happen");
    //       }
    //     }
    //   }
    // }
  }

  void Visit(TemporalDFG *TD) override {
    DBPtr = TD;
    std::queue<Instruction *> Q;
    std::vector<Instruction *> Visited;
    CHECK(TD->getBlocks().size() == 1);

    for (auto I = TD->Begin->getNextNode(); I != TD->End;
         I = I->getNextNode()) {
      if (CanBeAEntry(I)) {
        Q.push(I);
        Visited.push_back(I);
      }
    }
    GatherEntryInsts(Q, Visited);

    for (auto Inst : Visited) {
      if (!isa<LoadInst>(Inst)) {
        InspectOperands(Inst);
        std::set<Instruction *> Equiv;
        InspectConsumers(Inst);
      }
    }
  }

  DFGEntryAnalyzer(DominatorTree *DT_) : DT(DT_) {}
};

void ExtractDFGFromScope(DFGFile &DF, IntrinsicInst *Start, IntrinsicInst *End,
                         DominatorTree *DT, LoopInfo *LI) {
  // Extract the sketch of dedicated and temporal DFGs respectively.
  // The instruction entries in each DFG cannot be instantiated until all the
  // sketches are extracted, because we need this to analyze inter-DFG
  // communication in one pass.
  std::set<BasicBlock *> OutOfBound;
  for (auto BBN : breadth_first(DT->getNode(End->getParent()))) {
    if (BBN->getBlock() == End->getParent())
      continue;
    OutOfBound.insert(BBN->getBlock());
  }
  for (auto NestedLoop : *LI) {
    for (auto SubLoop : breadth_first(NestedLoop)) {
      if (!DT->dominates(Start, SubLoop->getBlocks()[0]))
        continue;
      if (!SubLoop->getLoopID() || SubLoop->getLoopID()->getNumOperands() == 0)
        continue;
      bool InBound = true;
      for (auto BB : SubLoop->getBlocks()) {
        if (OutOfBound.count(BB))
          InBound = false;
      }
      if (!InBound)
        continue;
      if (MDNode *MD = GetUnrollMetadata(SubLoop->getLoopID(),
                                         "llvm.loop.ss.dedicated")) {
        auto MDFactor = dyn_cast<ConstantAsMetadata>(MD->getOperand(1));
        int Factor =
            (int)MDFactor->getValue()->getUniqueInteger().getSExtValue();
        auto DD = new DedicatedDFG(&DF, SubLoop, Factor);
        DF.addDFG(DD);
      }
    }
  }
  for (auto BBN : breadth_first(DT->getNode(Start->getParent()))) {
    auto BB = BBN->getBlock();
    auto range = make_range(
        BB != Start->getParent() ? BB->begin() : Start->getIterator(),
        BB != End->getParent() ? BB->end() : End->getIterator());
    for (auto &I : range) {
      auto TemporalStart = dyn_cast<IntrinsicInst>(&I);
      if (!TemporalStart || TemporalStart->getIntrinsicID() !=
                                Intrinsic::ss_temporal_region_start)
        continue;
      // TODO: Maybe later we need control flow in the temporal regions
      bool Found = false;
      for (Instruction *Cur = TemporalStart; Cur != &Cur->getParent()->back();
           Cur = Cur->getNextNode()) {
        if (auto TemporalEnd = dyn_cast<IntrinsicInst>(Cur)) {
          if (TemporalEnd->getIntrinsicID() !=
              Intrinsic::ss_temporal_region_end)
            continue;
          CHECK(TemporalEnd->getOperand(0) == TemporalStart);
          auto TD = new TemporalDFG(&DF, TemporalStart, TemporalEnd);
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
  // All the sketches are extracted. Fill in the entries.
  for (auto Elem : DF.DFGFilter<DFGBase>()) {
    DFGEntryAnalyzer DEA(DT);
    Elem->Accept(&DEA);
  }
}

ConfigInfo ExtractDFGPorts(std::string FName, DFGFile &DF) {
  std::ifstream ifs(FName + ".h");
  auto DFGs = DF.DFGFilter<DFGBase>();

  std::string Stripped(FName);
  while (Stripped.back() != '.')
    Stripped.pop_back();
  Stripped.pop_back();

  int ConfigSize = 0;
  std::string ConfigString;

  std::string Line;
  std::string PortPrefix(formatv("P_{0}_", Stripped).str());
  while (std::getline(ifs, Line)) {
    std::istringstream iss(Line);
    std::string Token;
    iss >> Token;
    // #define xxx
    if (Token == "#define") {
      iss >> Token;
      // #define P_dfgX_subY_vZ
      if (Token.find(PortPrefix + "sub") == 0) {
        int X, Y;
        Token = Token.substr(PortPrefix.size() + 3, Token.size());
        CHECK(sscanf(Token.c_str(), "%d_v%d", &X, &Y) == 2);
        int Port;
        iss >> Port;
        LLVM_DEBUG(dbgs() << "sub" << X << "v" << Y << " -> " << Port << "\n");
        auto Entry = DFGs[X]->Entries[Y];
        if (auto PB = dyn_cast<PortBase>(Entry)) {
          PB->SoftPortNum = Port;
        } else if (auto CB = dyn_cast<ComputeBody>(Entry)) {
          CHECK(false) << "This should be deprecated!";
          if (!CB->isImmediateAtomic()) {
            LLVM_DEBUG(llvm::dbgs() << "OutputPorts:\n");
            auto OutPorts = CB->GetOutPorts();
            for (auto &Port : CB->GetOutPorts()) {
              LLVM_DEBUG(Port->UnderlyingInst()->dump());
            }
            // FIXME: For now only one destination is supported
            // Later divergence will be supported
            CHECK(OutPorts.size() == 1)
                << *CB->UnderlyingInst() << " " << OutPorts.size();
            OutPorts[0]->SoftPortNum = Port;

            // Fill in the latency of each node.
            //{
            //  OutputPort *OP = OutPorts[0];
            //  std::string ON = OP->Parent->InThisDFG(OP->Output)->NameInDFG();
            //  for (auto SDVO : dfg.nodes<SSDFGVecOutput*>()) {
            //    if (SDVO->name() == ON) {
            //      OP->Latency = sched->latOf(SDVO);
            //      LLVM_DEBUG(dbgs() << "[lat] " << ON << ": " << OP->Latency
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
      } else if (Token.find(formatv("{0}_size", Stripped).str()) == 0) {
        iss >> ConfigSize;
      } else if (Token.find(PortPrefix + "indirect_") == 0) {
        Token = Token.substr(std::string(PortPrefix + "indirect_").size());
        int X, Y;
        int Port;
        if (sscanf(Token.c_str(), "in_%d_%d", &X, &Y) == 2) {
          auto IMP = dyn_cast<IndMemPort>(DFGs[X]->Entries[Y]);
          CHECK(IMP);
          iss >> Port;
          IMP->Index->SoftPortNum = Port;
        } else {
          CHECK(sscanf(Token.c_str(), "out_%d_%d", &X, &Y) == 2);
          auto IMP = dyn_cast<IndMemPort>(DFGs[X]->Entries[Y]);
          CHECK(IMP);
          iss >> Port;
          IMP->IndexOutPort = Port;
        }
      }
      // char dfgx_config[size] = "filename:dfgx.sched";
    } else if (Token == "char") {
      // dfgx_config[size]
      iss >> Token;
      // =
      iss >> Token;
      // "filename:dfgx.sched";
      iss >> Token;
      ConfigString = Token.substr(1, Token.size() - 3);
      ConfigString += std::string(ConfigSize - ConfigString.size() - 1, '\0');
    }
  }

  LLVM_DEBUG(INFO << "[Config] " << ConfigSize << ": " << ConfigString << "\n");

  return ConfigInfo(Stripped, ConfigString, ConfigSize);
}


DFGLoopInfo AnalyzeDFGLoops(DFGBase *DB, ScalarEvolution &SE) {
  struct DFGLoopAnalyzer : DFGVisitor {
    void Visit(DedicatedDFG *DD) override {
      auto &LoopNest = DD->LoopNest;
      DLI.LoopNest = LoopNest;
      for (int i = 0; i < (int) LoopNest.size(); ++i) {
        DLI.TripCount.push_back(
          analysis::AnalyzeIndexExpr(&SE, SE.getBackedgeTakenCount(LoopNest[i]), LoopNest));
      }
    }

    void Visit(TemporalDFG *TD) override {}

    DFGLoopInfo DLI;
    ScalarEvolution &SE;

    DFGLoopAnalyzer(ScalarEvolution &SE_) : SE(SE_) {}
  };

  DFGLoopAnalyzer DLA(SE);
  DB->Accept(&DLA);
  return DLA.DLI;
}

} // namespace analysis
} // namespace dsa