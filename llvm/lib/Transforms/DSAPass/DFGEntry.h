#ifndef STREAM_SPECIALIZE_PORT_H_
#define STREAM_SPECIALIZE_PORT_H_

#include <set>

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

#include "dsa/dfg/metadata.h"

using namespace llvm;

class DFGBase;

namespace dsa {

struct DFGEntryVisitor;

} // namespace dsa

enum EntryKind {
#define MACRO(X) k##X
#include "./DFGKind.def"
#undef MACRO
};

extern const char *KindStr[];

struct Predicate;

/*!
 * \brief The base class of the extracted DFG entry.
 */
struct DFGEntry {
  /*!
   * \brief The subclass kind of the entry.
   */
  EntryKind Kind;
  /*!
   * \brief The DFG this entry to which it belongs.
   */
  DFGBase *Parent;

  DFGEntry(DFGBase *Parent);
  virtual ~DFGEntry() {}

  /*!
   * \brief If this entry is in the major block (inner most loop body).
   */
  virtual bool isInMajor();
  /*!
   * \brief If this entry should be unrolled.
   */
  virtual bool shouldUnroll();
  /*!
   * \brief Return the underlying value of this entry.
   */
  virtual Value *underlyingValue();
  /*!
   * \brief Return the underlying instruction of this entry.
   */
  virtual Instruction *underlyingInst();
  /*!
   * \brief Sometimes, it is not only one instruction.
   */
  virtual std::vector<Instruction *> underlyingInsts() {
    if (underlyingInst()) {
      return {underlyingInst()};
    }
    return {};
  }
  /*!
   * \brief Sometimes, it is not only one value.
   */
  virtual std::vector<Value *> underlyingValues() {
    std::vector<Instruction *> Tmp(underlyingInsts());
    std::vector<Value *> Res(Tmp.size());
    for (size_t i = 0; i < Tmp.size(); ++i) // NOLINT
      Res[i] = Tmp[i];
    return Res;
  }

  virtual void dump(std::ostringstream &OS);
  std::string dump() {
    std::ostringstream OSS;
    dump(OSS);
    return OSS.str();
  }

  virtual int getAbstainBit();

  /// Get the name of the entry to be dumped in the DFG textformat
  virtual std::string name(int Idx = -1);

  /// Get the predicate of the entry if exists. O.w. return nullptr.
  virtual Predicate *getPredicate(int *MaskPtr = nullptr);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *);

  int ID{-1};
  int index();

  static bool classof(const DFGEntry *DE) { return true; }
};

struct OutputPort;
struct InputPort;
struct AtomicPortMem;

// A wrapper to Instruction
// A simple compute instruction
struct ComputeBody : DFGEntry {
  Instruction *Operation;

  ComputeBody(DFGBase *Parent, Instruction *Operation);
  int SoftPortNum{-1};

  Instruction *underlyingInst() override;
  std::vector<OutputPort *> getOutPorts();
  bool shouldUnroll() override;

  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;
  // If this instruction is handled by atomic operation.
  AtomicPortMem *isAtomic();
  // If this instruction is immidiately consumed by an atomic operation.
  AtomicPortMem *isImmediateAtomic();
  // (base on the method above) If so, regard this as an output.
  // void EmitAtomic(std::ostringstream &os);

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kComputeStarts && DE->Kind < kComputeEnds;
  }
};

struct Predicate : DFGEntry {
  SmallVector<Instruction *, 0> Cond;
  SmallVector<bool, 0> Reversed;

  Predicate(DFGBase *Parent, Instruction *Cond);
  Instruction *underlyingInst() override;
  bool shouldUnroll() override;
  void emitCond(std::ostringstream &OS);
  bool addCond(Instruction *Inst);
  int contains(Instruction *Inst);
  int toCompareRes(Instruction *Inst, bool TF);
  std::vector<Instruction *> underlyingInsts() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPredicate; }
};

// A accumulator Instruction
struct Accumulator : ComputeBody {

  Accumulator(DFGBase *Parent, Instruction *Operation);
  /*!
   * \brief If this value should be unrolled in DFG.
   */
  bool shouldUnroll() override;

  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kAccumulator; }
};

// Base class for ports
// The essential difference is data stream vector
struct PortBase : DFGEntry {
  int SoftPortNum;
  bool IntrinInjected;
  dsa::dfg::MetaPort Meta;

  virtual int portWidth();
  PortBase(DFGBase *Parent);
  int vectorizeFactor();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kPortStarts && DE->Kind < kPortEnds;
  }
};

// Input port has a repeat
struct InputPort : PortBase {
  InputPort(DFGBase *Parent);
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;
  /*!
   * \brief If this memory stream should be tagged.
   */
  std::vector<Accumulator *> Tagged;
  /*!
   * \brief The string of stream state.
   */
  std::string TagString;

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kInPortStarts && DE->Kind < kInPortEnds;
  }
};

struct CtrlMemPort : InputPort {
  LoadInst *Load;
  Value *Start, *TripCnt;
  Predicate *Pred;
  int Mask;
  bool ForPredicate{false};

  CtrlMemPort(DFGBase *, LoadInst *, Value *Start, Value *TripCnt, Predicate *, int Mask);

  Predicate *getPredicate(int *MaskPtr = nullptr) override;
  Instruction *underlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCtrlMemPort; }
};


// Memory port can be either a spad or a DMA
struct MemPort : InputPort {
  /*!
   * \brief The memory load under affined loops to be re-written.
   */
  LoadInst *Load;

  MemPort(DFGBase *Parent, LoadInst *Load);

  /*!
   * \brief The operand idx of pointer in the underlying instruction.
   *        Both Load and Store require a uniform interface to extract the pointers
   *        for the functions analyze the pointers.
   */
  static constexpr int PtrOperandIdx = 0;

  /*!
   * \brief If this entry should be unrolled.
   */
  bool shouldUnroll() override;
  /*!
   * \brief The corresponding instruction in LLVM.
   */
  Instruction *underlyingInst() override;
  /*!
   * \brief The policy of data padding.
   */
  int fillMode();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kMemPort; }
};

template<typename T, typename TBase, EntryKind K>
struct SLPIO : TBase {
  std::vector<T*> Coal;

  inline void accept(dsa::DFGEntryVisitor *DEV) override;

  Instruction *underlyingInst() override {
    DSA_CHECK(false) << "This node for sure has multiple instructions!";
    return nullptr;
  }

  void dump(std::ostringstream &OS) override {
    for (auto *Elem : Coal) {
      Elem->dump(OS);
      OS << "\n";
    }
  }

  std::vector<Value *> underlyingValues() override {
    std::vector<Value *> Res;
    Res.reserve(Coal.size());
    for (auto *Elem : Coal) {
      Res.push_back(Elem->underlyingValue());
    }
    return Res;
  }

  std::vector<Instruction *> underlyingInsts() override {
    std::vector<Instruction *> Res;
    Res.reserve(Coal.size());
    for (auto *Elem : Coal) {
      Res.push_back(Elem->underlyingInst());
    }
    return Res;
  }

  Predicate *getPredicate(int *) override {
    for (auto Elem : Coal) {
      DSA_CHECK(!Elem->getPredicate(nullptr));
    }
    return nullptr;
  }

  SLPIO(DFGBase *Parent) : TBase(Parent) {
    TBase::Kind = K;
  }

  bool shouldUnroll() override {
    return TBase::shouldUnroll();
  }

  static bool classof(const DFGEntry *DE) { return DE->Kind == K; }
};

using SLPMemPort = SLPIO<MemPort, InputPort, kSLPMemPort>;

// The data to this port is from an output of certain DFG
struct StreamInPort : InputPort {
  Instruction *DataFrom;

  StreamInPort(DFGBase *Parent, Instruction *Inst);
  Instruction *underlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamInPort; }
};

// A loop invariant through all the loop levels,
// but not a compilation time constant.
struct InputConst : InputPort {
  Value *Val;

  InputConst(DFGBase *Parent, Value *Val);

  Value *underlyingValue() override;
  Instruction *underlyingInst() override;
  std::vector<Value *> underlyingValues() override;
  std::vector<Instruction *> underlyingInsts() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kInputConst; }
};

// Each later usage of a compute body will form a output port
// Essentially output port is something like a duplication
struct OutputPort : PortBase {
  Instruction *Output;
  Value *ConsumeRate;
  OutputPort(DFGBase *Parent, Value *Value);
  OutputPort(DFGBase *Parent) : PortBase(Parent), Output(nullptr) {}
  int Latency{-1};

  Instruction *underlyingInst() override;
  int portWidth() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;
  /*!
   * \brief If this value should be unrolled.
   */
  bool shouldUnroll() override;

  /*!
   * \brief The name of this output port in DFG.
   */
  std::string name(int Idx = -1) override;

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kOutPortStarts && DE->Kind < kOutPortEnds;
  }
};

// Value will be written to memory through a port
struct PortMem : OutputPort {
  StoreInst *Store;
  PortMem(DFGBase *Parent, StoreInst *Store);

  static constexpr int PtrOperandIdx = 1;

  Instruction *underlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPortMem; }
};

using SLPPortMem = SLPIO<PortMem, OutputPort, kSLPPortMem>;

template<>
inline bool SLPPortMem::shouldUnroll() {
  bool Res = Coal[0]->shouldUnroll();
  for (int i = 1; i < (int) Coal.size(); ++i) { // NOLINT
    DSA_CHECK(Coal[i]->shouldUnroll() == Res);
  }
  return Res;
}

// Value will be consumed by another dfg
struct StreamOutPort : OutputPort {

  StreamOutPort(DFGBase *Parent, Instruction *Inst);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamOutPort; }

  StreamInPort *findConsumer();
};

struct IndMemPort : InputPort {
  /*!
   * \TODO(@were): Deprecate this!
   */
  MemPort *Index;
  /*!
   * \brief The output port that generates indices.
   *        Do differentiate it with Index->SoftPortNum, that is the input port that feeds indices in.
   */
  union {
    int IndexOutPort{-1};
    int SignalPort;
  };
  LoadInst *Load;

  IndMemPort(DFGBase *Parent, LoadInst *Index, LoadInst *Load);
  Instruction *underlyingInst() override;
  std::vector<Instruction *> underlyingInsts() override;
  bool duplicated();
  bool shouldUnroll() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kIndMemPort; }
};

struct AtomicPortMem : OutputPort {
  MemPort *Index;
  StoreInst *Store;

  /// Op
  /// 0 +=
  /// 1 <?=
  /// 2 >?=
  /// 3 =
  int OpCode;
  int OperandPort{-1};
  Instruction *Op;
  Value *Operand;

  AtomicPortMem(DFGBase *Parent_, LoadInst *Index_, StoreInst *Store_, // NOLINT
                int OpCode, Instruction *Op_, Value *Operand_); // NOLINT
  Instruction *underlyingInst() override;

  std::vector<Instruction *> underlyingInsts() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  inline virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kAtomicPortMem; }
};


namespace dsa {
/*!
 * \brief The visitor class for the visitor pattern of the DFG entries.
 */
struct DFGEntryVisitor {
  virtual void Visit(DFGEntry *);         // NOLINT
  virtual void Visit(ComputeBody *);      // NOLINT
  virtual void Visit(Predicate *);        // NOLINT
  virtual void Visit(Accumulator *);      // NOLINT
  virtual void Visit(PortBase *);         // NOLINT
  virtual void Visit(InputPort *);        // NOLINT
  virtual void Visit(CtrlMemPort *);      // NOLINT
  virtual void Visit(MemPort *);          // NOLINT
  virtual void Visit(SLPMemPort *);       // NOLINT
  virtual void Visit(SLPPortMem *);       // NOLINT
  virtual void Visit(StreamInPort *);     // NOLINT
  virtual void Visit(InputConst *);       // NOLINT
  virtual void Visit(OutputPort *);       // NOLINT
  virtual void Visit(PortMem *);          // NOLINT
  virtual void Visit(StreamOutPort *);    // NOLINT
  virtual void Visit(IndMemPort *);       // NOLINT
  virtual void Visit(AtomicPortMem *);    // NOLINT
};

} // namespace dsa

#define VISIT_IMPL(TYPE) inline void TYPE::accept(dsa::DFGEntryVisitor *V) { V->Visit(this); }
VISIT_IMPL(DFGEntry)
VISIT_IMPL(ComputeBody)
VISIT_IMPL(Predicate)
VISIT_IMPL(Accumulator)
VISIT_IMPL(PortBase)
VISIT_IMPL(InputPort)
VISIT_IMPL(CtrlMemPort)
VISIT_IMPL(MemPort)
VISIT_IMPL(StreamInPort)
VISIT_IMPL(InputConst)
VISIT_IMPL(OutputPort)
VISIT_IMPL(PortMem)
VISIT_IMPL(StreamOutPort)
VISIT_IMPL(IndMemPort)
VISIT_IMPL(AtomicPortMem)
#undef VISIT_IMPL

template<> inline void SLPMemPort::accept(dsa::DFGEntryVisitor *DEV) { DEV->Visit(this); }
template<> inline void SLPPortMem::accept(dsa::DFGEntryVisitor *DEV) { DEV->Visit(this); }

#endif // STREAM_SPECIALIZE_PORT_H_
