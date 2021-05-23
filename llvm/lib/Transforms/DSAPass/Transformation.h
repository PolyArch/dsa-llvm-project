#pragma once

#include "DFGEntry.h"
#include "Pass.h"
#include "StreamAnalysis.h"
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

#include "dsa/rf.h"
#include "dsa/spec.h"

using namespace llvm;

class DFGFile;
class DedicatedDFG;
class TemporalDFG;
class DFGBase;

struct AnalyzedRepeat {

  enum PrimeType {
    PlainRepeat,     // Simple repeat wrapped by fixed trip count loops
    StretchedRepeat, // 2-nested loop, the inner one is affected by the outer
                     // one
    SumOfStretchedRepeat // 2-nested loop, but count the sum of the trip counts
  };

  PrimeType PT{PlainRepeat};
  const SCEV *Prime{nullptr};
  Value *Wrapped{nullptr};
};

struct AnalyzedStream {
  AnalyzedRepeat AR;
  Value *OuterRepeat{nullptr};
  std::vector<std::tuple<Value *, Value *, int>> Dimensions;
  Value *BytesFromMemory(IRBuilder<> *IB);
};

namespace dsa {

/*!
 * \brief The visitor for each sub DFG.
 */
struct DFGVisitor {
  virtual void Visit(DFGBase *);
  virtual void Visit(DedicatedDFG *);
  virtual void Visit(TemporalDFG *);
};

} // namespace dsa

/// The class of the base dfg
class DFGBase {
public:
  enum DFGKind { Unknown, Dedicated, Temporal, DataMove };

  /// DFG #ID in the .dfg file.
  int ID{-1};
  /// The DFGFile contains this DFG
  DFGFile *Parent;
  /// The instructions to be emitted as DFG
  std::vector<DFGEntry*> Entries;
  /// Find a value among the compute bodies
  std::string ValueToOperandText(Value *Val, int Vec = -1);
  /// To unify the comparisons
  std::map<std::pair<Value *, Value *>, Predicate *> Comparison;

  DFGKind Kind;

  std::vector<Instruction *> InjectedCode;

  DFGBase(DFGFile *);

  friend class DFGFile;
  friend struct DFGEntry;
  friend struct StreamOutPort;
  friend struct ComputeBody;
  friend struct PortBase;
  friend struct InputPort;
  friend struct Accumulator;
  friend struct MemPort;
  friend struct PortMem;
  friend struct IndMemPort;
  friend struct Predicate;
  friend struct CtrlMemPort;
  friend struct CtrlSignal;
  friend struct AtomicPortMem;

  /// Get the current context
  virtual LLVMContext &getCtx();
  /// The blocks to be offloaded to the dataflow
  virtual SmallVector<BasicBlock *, 0> getBlocks() = 0;
  /// Dump the dfg to an I/O stream
  virtual void dump(std::ostringstream &os);
  /// Check if this given instruction/Block is in the DFG
  virtual bool Contains(Instruction *) = 0;
  virtual bool Contains(BasicBlock *) = 0;
  /// Get the unroll factor of the DFG
  virtual int getUnroll() = 0;
  /// Get the unroll factor of the DFG wrapped in LLVM data structure
  virtual Value *UnrollConstant();

  /*!
   * \brief Entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGVisitor *);

  /// TODO(@were): Decouple and remove all these.
  // {
  /// Check if this block belong to the DFGs
  DFGBase *BelongOtherDFG(Instruction *I);
  /// Check if a value is in this DFG
  DFGEntry *InThisDFG(Value *Val);
  /// The default position to inject the instructions
  virtual Instruction *DefaultIP();
  /// Find the predicate that can be merged into one.
  Predicate *FindEquivPredicate(Value *LHS, Value *RHS);

  /// The helper function to calculate the actual repeat time.
  /// Refer injection doc's example for more details.
  /// If it is vectorized, it the prime should be ceiling divided.
  /// If it is for a stream family port, it should be shift left 3 bits
  // (since last 3 bits are for fixed point thing)
  Value *ComputeRepeat(Value *Prime, Value *Wrapper, bool isVectorized,
                       bool isPortConfig);
  Value *ComputeRepeat(const AnalyzedRepeat &AR, bool isVectorized,
                       bool isPortConfig);

  /// Inject port repeat
  Instruction *InjectRepeat(const AnalyzedRepeat &AR, Value *Val, int Port);

  /// Injecting repeat is little bit tricky, let's consider such a scenario:
  /// for i in 1..10
  ///   for j in 1..3
  ///     vectorize by 2
  /// Then we should do ceil_div(3, 2) * 10 = 20, instead of 3 * 10 / 2 = 15.
  /// The Prime indicates the "3" here.
  /// The Wrap indicates the "10" here.
  Instruction *InjectRepeat(Value *Prime, Value *Wrap, int64_t Stretch,
                            Value *Val, int Port);

  DFGKind getKind() const;

  /// Analyze data stream
  virtual AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) {
    return AnalyzedStream();
  }
  // }

  /// Get the indirect port number.
  int getNextIND();
  /// Get the next reserved port number for random use.
  /// FIXME: I am not sure if it is good. Do we need a systematic way to manage
  /// all the port?
  int getNextReserved();
  /// The scope of the DFG to be offload
  virtual bool InThisScope(Instruction *) = 0;

  static bool classof(DFGBase *DB) { return true; }

  template <typename T> std::vector<T *> EntryFilter() {
    return TypeFilter<T>(Entries);
  }
};

/// The class holds the DFG information
class DFGFile {

  std::string FileName;
  Function &Func;
  Instruction *Config, *Fence;
  StreamSpecialize *Query;
  /// DFGs included by this DFGFile
  std::vector<DFGBase *> DFGs;
  std::map<Value *, Value *> AddrsOnSpad;

  bool AllInitialized{false};

public:
  friend class DFGBase;
  friend class DedicatedDFG;
  friend class TemporalDFG;
  friend struct DFGEntry;
  friend struct StreamOutPort;
  friend struct MemPort;
  friend struct PortMem;
  friend struct OutputPort;
  friend struct IndMemPort;
  friend struct Predicate;
  friend struct ComputeBody;
  friend struct CtrlMemPort;
  friend struct Accumulator;
  friend struct CtrlSignal;
  friend struct InputPort;
  friend struct AtomicPortMem;

  /// The constructor
  DFGFile(StringRef Name, IntrinsicInst *Start, IntrinsicInst *End,
          StreamSpecialize *Query);

  /*!
   * \brief Get the name of the DFG.
   */
  const std::string &getName();

  /// Add the given DFG to this file
  void addDFG(DFGBase *DFG);
  /// Erase all the instructions offloaded to CGRA
  void EraseOffloadedInstructions();
  /// Get the current context
  LLVMContext &getCtx();
  /// Allocate addresses on the scratch pad
  void InspectSPADs();

  template <typename T> std::vector<T *> DFGFilter() {
    return TypeFilter<T>(DFGs);
  }
};

/// The class of the temporal DFG
class TemporalDFG : public DFGBase {

public:
  IntrinsicInst *Begin, *End;
  Instruction *IP{nullptr};

  friend class DFGFile;
  friend struct DFGEntry;
  friend struct StreamOutPort;
  friend struct ComputeBody;

  TemporalDFG(DFGFile *Parent, IntrinsicInst *Begin, IntrinsicInst *End);

  /// Return the blocks of the DFG
  SmallVector<BasicBlock *, 0> getBlocks() override;
  /// Dump the DFG to text format
  void dump(std::ostringstream &os) override;
  /// Check if this given instruction is in the DFG
  bool Contains(Instruction *) override;
  bool Contains(BasicBlock *) override;
  /// Get the unroll factor of the DFG
  int getUnroll() override;
  /// The default position to inject instructions
  Instruction *DefaultIP() override;
  /// Analyze data stream
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) override;
  /// The scope of the DFG to be offload
  bool InThisScope(Instruction *I) override;
  /*!
   * \brief Entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGVisitor *) override;

  static bool classof(const DFGBase *DB) { return DB->getKind() == Temporal; }
};

/// The class of the dedicated DFG
class DedicatedDFG : public DFGBase {

  /// The current fill mode
  enum FillMode {
    NoFill,
    PostZeroFill,
    PreZeroFill,
    StrideZeroFill,
    StrideDiscardFill,
    None
  };
  FillMode CurrentFill{NoFill};

  bool ConsumedByAccumulator(MemPort *MP);

public:
  /// The loop levels from dfg to stream pragma
  std::vector<Loop*> LoopNest;
  /// How many times the instances should be duplicated
  int UnrollFactor;
  /// Blocks in this path of loop nest
  std::set<BasicBlock *> Blocks;
  /// The insert point of the instructions
  BasicBlock *Preheader;
  /// Prologue IP
  Instruction *PrologueIP;

  friend class DFGFile;
  friend class DFGBase;
  friend struct DFGEntry;
  friend struct MemPort;
  friend struct PortMem;
  friend struct StreamOutPort;
  friend struct ComputeBody;
  friend struct Accumulator;
  friend struct InputConst;
  friend struct CtrlSignal;
  friend struct CtrlMemPort;
  friend struct AtomicPortMem;

  /// The trip count of each loop level
  Value *TripCount(int x, Instruction *InsertBefore);
  /// The trip count product of inner loop levels
  /// If the bool is true, the inner most loop should be ceil divided by the
  /// unroll factor
  Value *ProdTripCount(int l, int r, Instruction *InsertBefore);
  Value *ProdTripCount(int x, Instruction *InsertBefore);

  /// Analyze data stream
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) override;
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes,
                                   bool DoOuterRepeat,
                                   Instruction *InsertBefore);

  DedicatedDFG(DFGFile *, Loop *, int);

  /// Inputs of this DFG
  virtual void dump(std::ostringstream &os) override;
  /// Return the blocks of the DFG
  SmallVector<BasicBlock *, 0> getBlocks() override;
  /// Inner/outer-most loop level
  Loop *OuterMost();
  Loop *InnerMost();
  /// Check if this given stuff is in the DFG
  bool Contains(Instruction *) override;
  bool Contains(BasicBlock *) override;
  bool Contains(const Loop *);
  /// Get the unroll factor of the DFG
  int getUnroll() override;
  /// The default position to inject instructions
  Instruction *DefaultIP() override;
  /// The scope of the DFG to be offload
  bool InThisScope(Instruction *I) override;
  /*!
   * \brief Entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGVisitor *) override;

  static bool classof(const DFGBase *DB) {
    return DB->getKind() == Dedicated || DB->getKind() == DataMove;
  }
};

namespace dsa {
namespace inject {

/*!
 * \brief Inject linear memory stream
 * \param IB IRBuilder of manipulating the IR.
 * \param PortNum The number of the port this stream involved.
 * \param Stream The analyzed memory information.
 * \param MO The memory operation. Refer MemoryOperation enum for more details.
 * \param PP The padding policy. Refer Padding enum for more details.
 * \param MT The memory type DMA or SPAD.
 * \param DType The data type of each element in the injected stream.
 */
MemoryType InjectLinearStream(IRBuilder<> *IB, const RegisterFile &Regs,
                              int PortNum, const AnalyzedStream &Stream,
                              MemoryOperation MO, Padding PP, MemoryType MT,
                              int DType);

struct DSAIntrinsicEmitter {
  bool Prepass{true};
  IRBuilder<> *IB;
  std::vector<CallInst *> res;
  RegisterFile Regs;

  struct REG {
    static std::stack<IRBuilder<> *> IBStack;
    Value *value{nullptr};
    REG() {}
    REG(Value *value_) : value(value_) {}
    REG(uint64_t x) { value = IBStack.top()->getInt64(x); }
    operator Value *&() { return value; }
  };

  DSAIntrinsicEmitter(IRBuilder<> *IB_, const RegisterFile &Regs_)
      : IB(IB_), Regs(Regs_) {
    REG::IBStack.push(IB_);
  }

  ~DSAIntrinsicEmitter() { REG::IBStack.pop(); }

  REG DIV(REG a, REG b) { return IB->CreateUDiv(a, b); }

  REG SUB(REG a, REG b) { return IB->CreateSub(a, b); }

  void IntrinsicImpl(const std::string &Mnemonic,
                     const std::string &OpConstrain,
                     const std::vector<Value *> &Args, Type *ResTy) {
    std::ostringstream MOSS;
    MOSS << Mnemonic << " $0";
    for (int i = 0, n = OpConstrain.size(), j = 1; i < n; ++i) {
      if (OpConstrain[i] == ',') {
        MOSS << ", $" << j;
        ++j;
      }
    }
    std::vector<Type *> Types;
    for (auto Arg : Args) {
      Types.push_back(Arg->getType());
    }
    auto FTy = FunctionType::get(ResTy, Types, false);
    auto IA = InlineAsm::get(FTy, MOSS.str(), OpConstrain, true);
    res.push_back(IB->CreateCall(IA, Args));
    if (Mnemonic == "ss_lin_strm" || Mnemonic == "ss_ind_strm" ||
        Mnemonic == "ss_recv" || Mnemonic == "ss_wr_rd") {
      for (int i = 0; i < DSARF::TOTAL_REG; ++i) {
        auto C =
            IB->CreateTrunc(IB->CreateLoad(Regs[i].Sticky), IB->getInt1Ty());
        auto SV = IB->CreateLoad(Regs[i].Reg);
        auto Reset = IB->CreateSelect(C, SV, IB->getInt64(REG_STICKY[i]));
        IB->CreateStore(Reset, Regs[i].Reg);
      }
    }
  }

  void INTRINSIC_DRI(std::string Mnemonic, REG &a, REG b, int c) {
    IntrinsicImpl(Mnemonic, "=r,r,i", {b.value, IB->getInt64(c)},
                  IB->getInt64Ty());
    a.value = res.back();
  }

  Value *MakeValue(Value *Val) {
    if (Val->getType()->isPointerTy()) {
      return IB->CreatePtrToInt(Val, IB->getInt64Ty());
    }
    auto Ty = IB->getIntNTy(Val->getType()->getScalarSizeInBits());
    auto RI = IB->CreateBitCast(Val, Ty);
    if (RI->getType()->getScalarSizeInBits() < 64) {
      RI = IB->CreateSExt(RI, IB->getInt64Ty());
    }
    return RI;
  }

  void INTRINSIC_RRI(std::string Mnemonic, REG a, REG b, int c) {
    if (Prepass && (Mnemonic == "ss_cfg_param" && c != 98)) {
      int idx1 = c & 31;
      int s1 = (c >> 10) & 1;
      int idx2 = (c >> 5) & 31;
      int s2 = (c >> 11) & 1;
      Value *IV1 = IB->getInt64(idx1);
      if (idx1) {
        auto AA = IB->CreateLoad(Regs[idx1].Reg);
        auto AS = IB->CreateLoad(Regs[idx1].Sticky);
        auto AV = MakeValue(a.value);
        IB->CreateStore(AV, Regs[idx1].Reg);
        IB->CreateStore(IB->getInt8(s1), Regs[idx1].Sticky);
        if (getenv("FUSION")) {
          IntrinsicImpl("equal.hint.v1", "r", {IB->CreateICmpEQ(AA, AV)},
                        IB->getVoidTy());
          IntrinsicImpl("equal.hint.s1", "r",
                        {IB->CreateICmpEQ(AS, IB->getInt8(s1))},
                        IB->getVoidTy());
        }
      }
      Value *IV2 = IB->getInt64(idx2);
      if (idx2) {
        auto BB = IB->CreateLoad(Regs[idx2].Reg);
        auto BS = IB->CreateLoad(Regs[idx2].Sticky);
        auto BV = MakeValue(b.value);
        IB->CreateStore(BV, Regs[idx2].Reg);
        IB->CreateStore(IB->getInt8(s2), Regs[idx2].Sticky);
        if (getenv("FUSION")) {
          IntrinsicImpl("equal.hint.v2", "r", {IB->CreateICmpEQ(BB, BV)},
                        IB->getVoidTy());
          IntrinsicImpl("equal.hint.s2", "r",
                        {IB->CreateICmpEQ(BS, IB->getInt8(s2))},
                        IB->getVoidTy());
        }
      }
      auto A = IB->CreateLoad(Regs[idx1].Reg);
      auto B = IB->CreateLoad(Regs[idx2].Reg);
      auto S1 = IB->getInt64(s1 << 10);
      auto S2 = s2 ? IB->getInt64(~((1 << 11) - 1)) : IB->getInt64(0);
      auto Imm = IB->CreateOr(
          IB->CreateOr(IB->CreateOr(IV1, IB->CreateShl(IV2, 5)), S1), S2);
      IntrinsicImpl(Mnemonic, "r,r,i", {A, B, Imm}, IB->getVoidTy());
      return;
    }
    IntrinsicImpl(Mnemonic, "r,r,i", {a.value, b.value, IB->getInt64(c)},
                  IB->getVoidTy());
  }

  void INTRINSIC_RI(std::string Mnemonic, REG a, int b) {
    IntrinsicImpl(Mnemonic, "r,i", {a.value, IB->getInt64(b)}, IB->getVoidTy());
  }

  void INTRINSIC_R(std::string Mnemonic, REG a) {
    IntrinsicImpl(Mnemonic, "r", {a.value}, IB->getVoidTy());
  }

#include "intrin_impl.h"
};

struct AffinedInjector {
  IRBuilder<> *IB;
  SCEVExpander *SEE;
  DSAIntrinsicEmitter DIE;
  AffinedInjector(IRBuilder<> *IB_, SCEVExpander *SEE_,
                  const std::vector<dsa::utils::StickyRegister> &Regs)
      : IB(IB_), SEE(SEE_), DIE(IB_, Regs) {}
};

struct RepeatInjector : AffinedInjector {
  RepeatInjector(IRBuilder<> *IB, SCEVExpander *SEE,
                 const std::vector<dsa::utils::StickyRegister> &Regs)
      : AffinedInjector(IB, SEE, Regs) {}

  void Inject(analysis::LinearInfo *LI,
              const std::vector<analysis::LinearInfo *> &Loops, int Port,
              int Unroll) {
    CHECK(Loops.size() == LI->Coef.size() || LI->Coef.empty());
    Value *Repeat = IB->getInt64(1);
    int N = LI->Coef.empty() ? Loops.size() : LI->PatialInvariant();
    for (int i = 0; i < N; ++i) {
      auto Coef = LI->Coef[i]->ConstInt();
      CHECK(Coef && *Coef == 0);
      if (!Loops[i]->Coef.empty()) {
        CHECK(i == 0)
            << "Only the inner most dimension supports repeat stretch.";
        for (int j = 0; j < N; ++j) {
          if (j == 1) {
            continue;
          }
          auto CI = Loops[i]->Coef[j]->ConstInt();
          CHECK(CI && *CI == 0);
        }
        DIE.SS_CONFIG_PORT(Port, DPF_PortPeriod, Unroll);
        DIE.SS_CONFIG_PORT(Port, DPF_PortRepeatStretch,
                           SEE->expandCodeFor(LI->Coef[i]->Coef[1]->Base));
      }
      auto Current =
          IB->CreateAdd(SEE->expandCodeFor(Loops[i]->Base), IB->getInt64(1));
      if (i == 0 && Unroll != 1) {
        Current = IB->CreateSub(Current, IB->getInt64(1));
        Current = IB->CreateSDiv(Current, IB->getInt64(Unroll));
        Current = IB->CreateAdd(Current, IB->getInt64(1));
      }
      Repeat = IB->CreateMul(Repeat, Current);
    }
    DIE.SS_CONFIG_PORT(Port, DPF_PortRepeat, Repeat);
  }
};

struct LinearInjector : AffinedInjector {

  LinearInjector(IRBuilder<> *IB, SCEVExpander *SEE,
                 const std::vector<dsa::utils::StickyRegister> &Regs)
      : AffinedInjector(IB, SEE, Regs) {}

  void Inject(analysis::LinearInfo *LI,
              const std::vector<analysis::LinearInfo *> &Loops, int Port,
              MemoryOperation MO, Padding PP, MemoryType MT, int DType) {
    if (auto LII = LI->Invariant()) {
      DIE.INSTANTIATE_1D_STREAM(SEE->expandCodeFor(LII), IB->getInt64(0),
                                IB->getInt64(1), Port, PP, DSA_Access, MO, MT,
                                DType, 0);
      return;
    }
    CHECK(Loops.size() == LI->Coef.size())
        << Loops.size() << " != " << LI->Coef.size();
    int Dim = Loops.size() - LI->PatialInvariant();
    CHECK(0 <= Dim && Dim <= 3) << Dim;
    auto Start = SEE->expandCodeFor(LI->Base);
    int i = LI->PatialInvariant();
    switch (Dim) {
    case 0: {
      DIE.INSTANTIATE_1D_STREAM(Start, IB->getInt64(0), IB->getInt64(1), Port,
                                PP, DSA_Access, MO, MT, DType, 0);
      break;
    }
    case 1: {
      auto N = Loops[i]->Invariant();
      CHECK(N) << "No stretch should be in 1d stream! " << Loops[i]->toString();
      auto Stride = LI->Coef[i]->Invariant();
      CHECK(Stride) << "Stride should not be stretched!";
      DIE.INSTANTIATE_1D_STREAM(
          Start, SEE->expandCodeFor(LI->Coef[i]->Invariant()),
          IB->CreateAdd(SEE->expandCodeFor(Loops[i]->Invariant()),
                        IB->getInt64(1)),
          Port, PP, DSA_Access, MO, MT, DType, 0);
      break;
    }
    case 2: {
      // TODO(@were): Make assumption check!
      auto Length1D =
          IB->CreateAdd(SEE->expandCodeFor(Loops[i]->Base), IB->getInt64(1));
      Value *Stretch = IB->getInt64(0);
      if (!Loops[i]->Coef.empty()) {
        Stretch =
            IB->CreateSDiv(SEE->expandCodeFor(Loops[i]->Coef[i + 1]->Base),
                           IB->getInt64(DType));
      }
      auto Length2D = IB->CreateAdd(SEE->expandCodeFor(Loops[i + 1]->Base),
                                    IB->getInt64(1));
      auto Stride1D = SEE->expandCodeFor(LI->Coef[i]->Invariant());
      auto Stride2D =
          IB->CreateSDiv(SEE->expandCodeFor(LI->Coef[i + 1]->Invariant()),
                         IB->getInt64(DType));
      DIE.INSTANTIATE_2D_STREAM(Start, Stride1D, Length1D, Stride2D, Stretch,
                                Length2D, Port, PP, DSA_Access, MO, MT, DType,
                                0);
      break;
    }
    case 3: {
      CHECK(false) << "Unsupported dimension: " << Dim;
      break;
    }
    default:
      CHECK(false) << "Unsupported dimension: " << Dim;
    }
  }
};

} // namespace inject
} // namespace dsa
