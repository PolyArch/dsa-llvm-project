#pragma once

#include <map>
#include <memory>
#include <set>
#include <vector>
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/Casting.h"
#include "Util.h"
#include "DfgEntry.h"
#include "Pass.h"

#include "dsa/rf.h"
#include "dsa/spec.h"

using namespace llvm;

class DfgFile;
class DedicatedDfg;
class TemporalDfg;
class DfgBase;

struct AnalyzedRepeat {

  enum PrimeType {
    PlainRepeat, // Simple repeat wrapped by fixed trip count loops
    StretchedRepeat, // 2-nested loop, the inner one is affected by the outer one
    SumOfStretchedRepeat // 2-nested loop, but count the sum of the trip counts
  };

  PrimeType PT{PlainRepeat};
  const SCEV *Prime{nullptr};
  Value *Wrapped{nullptr};

};

struct AnalyzedStream {
  AnalyzedRepeat AR;
  Value *OuterRepeat{nullptr};
  std::vector<std::tuple<Value*, Value*, int>> Dimensions;
  Value *BytesFromMemory(IRBuilder<> *IB);
};


/// The class of the base dfg
class DfgBase {
public:
  enum DfgKind {
    Unknown,
    Dedicated,
    Temporal,
    DataMove
  };

  /// DFG #ID in the .dfg file.
  int ID{-1};
  /// The DfgFile contains this Dfg
  DfgFile *Parent;
  /// The instructions to be emitted as DFG
  SmallVector<DfgEntry*, 0> Entries;
  /// Find a value among the compute bodies
  std::string ValueToOperandText(Value *Val, int Vec = -1);
  /// To unify the comparisons
  std::map<std::pair<Value*, Value*>, Predicate*> Comparison;

  DfgKind Kind;

  std::vector<Instruction*> InjectedCode;

  DfgBase(DfgFile *);

public:
  friend class DfgFile;
  friend struct DfgEntry;
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
  virtual SmallVector<BasicBlock*, 0> getBlocks() = 0;
  /// Dump the dfg to an I/O stream
  virtual void dump(std::ostringstream &os);
  /// Check if this given instruction/Block is in the DFG
  virtual bool Contains(Instruction *) = 0;
  virtual bool Contains(BasicBlock *) = 0;
  /// Get the unroll factor of the DFG
  virtual int getUnroll() = 0;
  /// Get the unroll factor of the DFG wrapped in LLVM data structure
  virtual Value *UnrollConstant();
  /// Initialize the dfg's instructions
  virtual void InitEntries() = 0;
  /// After gathering all the entries, finalize their #ID
  void FinalizeEntryID();
  /// Gather the instructions to be converted to entries
  void InstsToEntries(iterator_range<BasicBlock::iterator> IRange,
                      std::set<Instruction*> &Visited);
  /// Reorder the entries in topological order
  void ReorderEntries();
  /// Clean up the dependences among entries
  /// Specifically, fill the predicate information, and add register write
  void CleanupEntryDependences();
  /// Add a binary operation in the DFG as well as its affiliations (Input/Output)
  void AnalyzeEntryOp(Instruction *Inst);
  /// Check if this block belong to the DFGs
  DfgBase *BelongOtherDFG(Instruction *I);
  /// Check if a value is in this DFG
  DfgEntry *InThisDFG(Value *Val);
  /// The default position to inject the instructions
  virtual Instruction* DefaultIP();
  /// Differentiate indirect or direct memory streams
  DfgEntry *DifferentiateMemoryStream(LoadInst *Load);
  /// Find the predicate that can be merged into one.
  Predicate* FindEquivPredicate(Value *LHS, Value *RHS);

  /// The helper function to calculate the actual repeat time.
  /// Refer injection doc's example for more details.
  /// If it is vectorized, it the prime should be ceiling divided.
  /// If it is for a stream family port, it should be shift left 3 bits
  // (since last 3 bits are for fixed point thing)
  Value *ComputeRepeat(Value *Prime, Value *Wrapper, bool isVectorized,
                       bool isPortConfig);
  Value *ComputeRepeat(const AnalyzedRepeat &AR, bool isVectorized, bool isPortConfig);

  /// Inject port repeat
  Instruction *InjectRepeat(const AnalyzedRepeat &AR, Value *Val, int Port);

  /// Injecting repeat is little bit tricky, let's consider such a scenario:
  /// for i in 1..10
  ///   for j in 1..3
  ///     vectorize by 2
  /// Then we should do ceil_div(3, 2) * 10 = 20, instead of 3 * 10 / 2 = 15.
  /// The Prime indicates the "3" here.
  /// The Wrap indicates the "10" here.
  Instruction *InjectRepeat(Value *Prime, Value *Wrap, int64_t Stretch, Value *Val, int Port);

  DfgKind getKind() const;

  /// Analyze data stream
  virtual AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) {
    return AnalyzedStream();
  }

  /// Get the indirect port number.
  int getNextIND();
  /// Get the next reserved port number for random use.
  /// FIXME: I am not sure if it is good. Do we need a systematic way to manage all the port?
  int getNextReserved();
  /// Inspect the consumers of the given instruciton.
  void InspectConsumers(Instruction *Inst);
  /// The scope of the DFG to be offload
  virtual bool InThisScope(Instruction *) = 0;

  static bool classof(DfgBase *DB) {
    return true;
  }

  template<typename T>
  std::vector<T*> EntryFilter() {
    return TypeFilter<T>(Entries);
  }
};

/// The class holds the DFG information
class DfgFile {

  std::string FileName;
  Function &Func;
  Instruction *Config, *Fence;
  StreamSpecialize *Query;
  /// DFGs included by this DfgFile
  std::vector<DfgBase*> DFGs;
  std::map<Value *, Value *> AddrsOnSpad;

  bool AllInitialized{false};

public:
  friend class DfgBase;
  friend class DedicatedDfg;
  friend class TemporalDfg;
  friend struct DfgEntry;
  friend struct StreamOutPort;
  friend struct MemPort;
  friend struct IndMemPort;
  friend struct Predicate;
  friend struct ComputeBody;
  friend struct CtrlMemPort;
  friend struct Accumulator;
  friend struct CtrlSignal;
  friend struct InputPort;
  friend struct AtomicPortMem;

  int TempCnt{0};

  /// The constructor
  DfgFile(StringRef Name, Function &F, IntrinsicInst *Start, IntrinsicInst *End,
          StreamSpecialize *SS);
  /// Add the given DFG to this file
  void addDfg(DfgBase *DFG);
  /// Initialize all the DFGs
  void InitAllDfgs();
  /// Emit the dfg to file so that it can be scheduled
  void EmitAndScheduleDfg();
  /// Analyze the data streams
  void InjectStreamIntrinsics();
  /// Erase all the instructions offloaded to CGRA
  void EraseOffloadedInstructions();
  /// Get the current context
  LLVMContext &getCtx();
  /// Allocate addresses on the scratch pad
  void InspectSPADs();

  template<typename T>
  std::vector<T*> DFGFilter() {
    return TypeFilter<T>(DFGs);
  }

};

/// The class of the temporal DFG
class TemporalDfg : public DfgBase {

  IntrinsicInst *Begin, *End;

  Instruction *IP{nullptr};

public:
  friend class DfgFile;
  friend struct DfgEntry;
  friend struct StreamOutPort;
  friend struct ComputeBody;

  TemporalDfg(DfgFile *Parent, IntrinsicInst *Begin, IntrinsicInst *End);

  /// Initialize the dfg's instructions
  void InitEntries() override;
  /// Return the blocks of the DFG
  SmallVector<BasicBlock*, 0> getBlocks() override;
  /// Dump the DFG to text format
  void dump(std::ostringstream &os) override;
  /// Check if this given instruction is in the DFG
  bool Contains(Instruction *) override;
  bool Contains(BasicBlock *) override;
  /// Get the unroll factor of the DFG
  int getUnroll() override;
  /// The default position to inject instructions
  Instruction* DefaultIP() override;
  /// Analyze data stream
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) override;
  /// The scope of the DFG to be offload
  bool InThisScope(Instruction *I) override;

  static bool classof(const DfgBase *DB) {
    return DB->getKind() == Temporal;
  }
};

/// The class of the dedicated DFG
class DedicatedDfg : public DfgBase {
  /// The loop levels from dfg to stream pragma
  SmallVector<Loop*, 0> LoopNest;
  /// How many times the instances should be duplicated
  int UnrollFactor;
  /// Blocks in this path of loop nest
  std::set<BasicBlock*> Blocks;
  /// The insert point of the instructions
  BasicBlock *Preheader;
  /// Prologue IP
  Instruction *PrologueIP;

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
  friend class DfgFile;
  friend class DfgBase;
  friend struct DfgEntry;
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
  /// If the bool is true, the inner most loop should be ceil divided by the unroll factor
  Value *ProdTripCount(int l, int r, Instruction *InsertBefore);
  Value *ProdTripCount(int x, Instruction *InsertBefore);

  /// Analyze data stream
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes) override;
  AnalyzedStream AnalyzeDataStream(Value *Index, int ScalarBytes, bool DoOuterRepeat,
                                   Instruction *InsertBefore);


  DedicatedDfg(DfgFile *, Loop *, int);

  /// Initialize the dfg's instructions
  void InitEntries() override;
  /// Inputs of this DFG
  virtual void dump(std::ostringstream &os) override;
  /// Return the blocks of the DFG
  SmallVector<BasicBlock*, 0> getBlocks() override;
  /// Inner/outer-most loop level
  Loop* OuterMost();
  Loop* InnerMost();
  /// Check if this given stuff is in the DFG
  bool Contains(Instruction *) override;
  bool Contains(BasicBlock *) override;
  bool Contains(const Loop *);
  /// Get the unroll factor of the DFG
  int getUnroll() override;
  /// The default position to inject instructions
  Instruction* DefaultIP() override;
  /// The scope of the DFG to be offload
  bool InThisScope(Instruction *I) override;

  static bool classof(const DfgBase *DB) {
    return DB->getKind() == Dedicated ||
           DB->getKind() == DataMove;
  }
};

class DataMoveDfg : public DedicatedDfg {
 public:

  DataMoveDfg(DfgFile *, Loop *, int);

  /// Inputs of this DFG
  void dump(std::ostringstream &os) override;

  /// Initialize the dfg's instructions
  void InitEntries() override;

  static bool classof(const DfgBase *DB) {
    return DB->getKind() == DataMove;
  }
};

class IntrinDfg : public DfgBase {

 public:
  IntrinsicInst *Intrin;
  IntrinDfg(DfgFile &DF, IntrinsicInst *Intrin_) : DfgBase(&DF), Intrin(Intrin_) {}

  Instruction *DefaultIP() override {
    return Intrin;
  }

  bool Contains(Instruction *Inst) override {
    return Inst == Intrin;
  }

  /// All these are not supposed to be used!
  SmallVector<BasicBlock*, 0> getBlocks() override { assert(0); }
  bool Contains(BasicBlock *) override { assert(0); }
  int getUnroll() override { assert(0); }
  Value *UnrollConstant() override { assert(0); }
  void InitEntries() override { assert(0); }
  /// The scope of the DFG to be offload
  bool InThisScope(Instruction *I) override;
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
MemoryType
InjectLinearStream(IRBuilder<> *IB, int PortNum, const AnalyzedStream &Stream,
                   MemoryOperation MO, Padding PP, MemoryType MT, int DType);

struct DSAIntrinsicEmitter {
  IRBuilder<> *IB;
  std::vector<CallInst*> res;

  struct REG {
    static std::stack<IRBuilder<>*> IBStack;
    Value *value{nullptr};
    REG() {}
    REG(Value *value_) : value(value_) {}
    // REG(uint64_t x) : value(IB->getInt64(x)) {}
    REG(uint64_t x) {
      value = IBStack.top()->getInt64(x);
    }
    operator Value*&() { return value; }
  };

  DSAIntrinsicEmitter(IRBuilder<> *IB_) : IB(IB_) {
    REG::IBStack.push(IB_);
  }

  ~DSAIntrinsicEmitter() {
    REG::IBStack.pop();
  }

  REG DIV(REG a, REG b) {
    return IB->CreateUDiv(a, b);
  }

  REG SUB(REG a, REG b) {
    return IB->CreateSub(a, b);
  }

  void IntrinsicImpl(const std::string &Mnemonic,
                     const std::string &OpConstrain,
                     const std::vector<Value*> &Args,
                     Type *ResTy) {
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
  }

  void INTRINSIC_DRI(std::string Mnemonic, REG &a, REG b, int c) {
    IntrinsicImpl(Mnemonic, "=r,r,i", {b.value, IB->getInt64(c)}, IB->getInt64Ty());
    a.value = res.back();
  }

  void INTRINSIC_RRI(std::string Mnemonic, REG a, REG b, int c) {
    IntrinsicImpl(Mnemonic, "r,r,i", {a.value, b.value, IB->getInt64(c)}, IB->getVoidTy());
  }

  void INTRINSIC_RI(std::string Mnemonic, REG a, int b) {
    IntrinsicImpl(Mnemonic, "r,i", {a.value, IB->getInt64(b)}, IB->getVoidTy());
  }

  void INTRINSIC_R(std::string Mnemonic, REG a) {
    IntrinsicImpl(Mnemonic, "r", {a.value}, IB->getVoidTy());
  }

#include "intrin_impl.h"

};

}
}
