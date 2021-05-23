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

}

enum EntryKind {
  kDFGEntry,

  // Computation {
  kComputeStarts,
  kComputeBody,
  kDuplicate,
  kAccumulator,
  kComputeEnds,
  // }

  // Predicate {
  kPredicate,
  // }

  // Port {
  kPortStarts,
  kPortBase,

  // InPort {
  kInPortStarts,
  kInputPort,
  kMemPort,
  kIndMemPort,
  kCtrlMemPort,
  kInputConst,
  kStreamInPort,
  kCtrlSignal,
  kInPortEnds,
  // }

  // OutPort {
  kOutPortStarts,
  kOutputPort,
  kPortMem,
  kAtomicPortMem,
  kStreamOutPort,
  kOutPortEnds,
  // }

  kPortEnds
  // }
};

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

  DFGEntry(DFGBase *Parent_);
  virtual ~DFGEntry() {}

  /*!
   * \brief If this entry is in the major block (inner most loop body).
   */
  virtual bool IsInMajor();
  /*!
   * \brief If this entry should be unrolled.
   */
  virtual bool ShouldUnroll();
  /*!
   * \brief Return the underlying value of this entry.
   */
  virtual Value *UnderlyingValue();
  /*!
   * \brief Return the underlying instruction of this entry.
   */
  virtual Instruction *UnderlyingInst();
  /*!
   * \brief Sometimes, it is not only one instruction.
   */
  virtual std::vector<Instruction *> UnderlyingInsts() {
    if (UnderlyingInst()) {
      return {UnderlyingInst()};
    }
    return {};
  }
  /*!
   * \brief Sometimes, it is not only one value.
   */
  virtual std::vector<Value *> UnderlyingValues() {
    std::vector<Instruction *> Res_(UnderlyingInsts());
    std::vector<Value *> Res(Res_.size());
    for (size_t i = 0; i < Res_.size(); ++i)
      Res[i] = Res_[i];
    return Res;
  }

  virtual void dump(std::ostringstream &os);
  std::string dump() {
    std::ostringstream oss;
    dump(oss);
    return oss.str();
  }

  virtual int getAbstainBit();

  /// Get the name of the entry to be dumped in the DFG textformat
  std::string Name(int Idx = -1);

  /// Get the predicate of the entry if exists. O.w. return nullptr.
  virtual Predicate *getPredicate(int *MaskPtr = nullptr);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  int ID{-1};
  int Index();

  static bool classof(const DFGEntry *DE) { return true; }
};

struct CtrlSignal;
struct OutputPort;
struct InputPort;
struct AtomicPortMem;

// A wrapper to Instruction
// A simple compute instruction
struct ComputeBody : DFGEntry {
  Instruction *Operation;

  ComputeBody(DFGBase *Parent_, Instruction *Operation_);
  int SoftPortNum{-1};

  Instruction *UnderlyingInst() override;
  std::vector<OutputPort *> GetOutPorts();
  bool ShouldUnroll() override;

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);
  // If this instruction is handled by atomic operation.
  AtomicPortMem *isAtomic();
  // If this instruction is immidiately consumed by an atomic operation.
  AtomicPortMem *isImmediateAtomic();
  // (base on the method above) If so, regard this as an output.
  void EmitAtomic(std::ostringstream &os);

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kComputeStarts && DE->Kind < kComputeEnds;
  }
};

struct Predicate : DFGEntry {
  SmallVector<Instruction *, 0> Cond;
  SmallVector<bool, 0> Reversed;

  Predicate(DFGBase *Parent_, Instruction *Cond_);
  Instruction *UnderlyingInst() override;
  bool ShouldUnroll() override;
  void EmitCond(std::ostringstream &os);
  bool addCond(Instruction *Inst);
  int Contains(Instruction *Inst);
  int ToCompareRes(Instruction *Inst, bool TF);
  std::vector<Instruction *> UnderlyingInsts() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPredicate; }
};

// A accumulator Instruction
struct Accumulator : ComputeBody {
  CtrlSignal *Ctrl;
  Accumulator(DFGBase *Parent_, Instruction *Operation_, CtrlSignal *Ctrl_);
  bool ShouldUnroll() override;
  Value *NumValuesProduced();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kAccumulator; }
};

// Base class for ports
// The essential difference is data stream vector
struct PortBase : DFGEntry {
  int SoftPortNum;
  bool IntrinInjected;
  dsa::dfg::MetaPort Meta;

  virtual int PortWidth();
  PortBase(DFGBase *Parent_);
  int VectorizeFactor();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kPortStarts && DE->Kind < kPortEnds;
  }
};

// Input port has a repeat
struct InputPort : PortBase {
  InputPort(DFGBase *Parent_);
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

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

  CtrlMemPort(DFGBase *, LoadInst *, Value *Start_, Value *TripCnt_,
              Predicate *, int Mask_);

  Predicate *getPredicate(int *MaskPtr = nullptr) override;
  Instruction *UnderlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCtrlMemPort; }
};

// Memory port can be either a spad or a DMA
struct MemPort : InputPort {
  LoadInst *Load;
  MemPort(DFGBase *Parent_, LoadInst *Load_);

  bool ShouldUnroll() override;
  Instruction *UnderlyingInst() override;
  int FillMode();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kMemPort; }

  bool InjectUpdateStream(IRBuilder<> *IB);
};

// The data to this port is from an output of certain DFG
struct StreamInPort : InputPort {
  Instruction *DataFrom;

  StreamInPort(DFGBase *Parent, Instruction *Inst);
  Instruction *UnderlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamInPort; }
};

// For control signal, the data consume rate matters
// The control signal should match its consume rate
struct CtrlSignal : InputPort {
  Accumulator *Controlled;
  CtrlSignal(DFGBase *Parent_);

  Value *FindConsumeRate();

  bool ShouldUnroll() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCtrlSignal; }
};

// A loop invariant through all the loop levels,
// but not a compilation time constant.
struct InputConst : InputPort {
  Value *Val;

  InputConst(DFGBase *Parent, Value *Val);

  Value *UnderlyingValue() override;
  Instruction *UnderlyingInst() override;
  std::vector<Value *> UnderlyingValues() override;
  std::vector<Instruction *> UnderlyingInsts() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kInputConst; }
};

// Each later usage of a compute body will form a output port
// Essentially output port is something like a duplication
struct OutputPort : PortBase {
  Instruction *Output;
  Value *ConsumeRate;
  OutputPort(DFGBase *Parent_, Value *Value_);
  int Latency{-1};

  Instruction *UnderlyingInst() override;
  int PortWidth() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);
  /*!
   * \brief If this value should be unrolled.
   */
  bool ShouldUnroll() override;

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kOutPortStarts && DE->Kind < kOutPortEnds;
  }
};

// Value will be written to memory through a port
struct PortMem : OutputPort {
  StoreInst *Store;
  PortMem(DFGBase *Parent_, StoreInst *Store_);

  Instruction *UnderlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPortMem; }
};

// Value will be consumed by another dfg
struct StreamOutPort : OutputPort {

  StreamOutPort(DFGBase *Parent_, Instruction *Inst);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamOutPort; }

  StreamInPort *FindConsumer();
};

struct IndMemPort : InputPort {
  MemPort *Index;
  int IndexOutPort{-1};
  LoadInst *Load;

  IndMemPort(DFGBase *Parent_, LoadInst *Index, LoadInst *Load);
  Instruction *UnderlyingInst() override;
  std::vector<Instruction *> UnderlyingInsts() override;
  bool duplicated();
  bool ShouldUnroll() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

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
  Instruction *Op;
  Value *Operand;

  AtomicPortMem(DFGBase *Parent_, LoadInst *Index_, StoreInst *Store_,
                int OpCode, Instruction *Op_, Value *Operand_);
  Instruction *UnderlyingInst() override;

  std::vector<Instruction *> UnderlyingInsts() override;
  void EmitOutPort(std::ostringstream &os);
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void Accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kAtomicPortMem; }
};

namespace dsa {
/*!
 * \brief The visitor class for the visitor pattern of the DFG entries.
 */
struct DFGEntryVisitor {
  virtual void Visit(DFGEntry *);
  virtual void Visit(ComputeBody *);
  virtual void Visit(Predicate *);
  virtual void Visit(Accumulator *);
  virtual void Visit(PortBase *);
  virtual void Visit(InputPort *);
  virtual void Visit(CtrlMemPort *);
  virtual void Visit(MemPort *);
  virtual void Visit(StreamInPort *);
  virtual void Visit(CtrlSignal *);
  virtual void Visit(InputConst *);
  virtual void Visit(OutputPort *);
  virtual void Visit(PortMem *);
  virtual void Visit(StreamOutPort *);
  virtual void Visit(IndMemPort *);
  virtual void Visit(AtomicPortMem *);
};

} // namespace dsa

#endif // STREAM_SPECIALIZE_PORT_H_
