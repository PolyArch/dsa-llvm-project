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

#include "dsa-ext/rf.h"
#include "dsa-ext/spec.h"

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
