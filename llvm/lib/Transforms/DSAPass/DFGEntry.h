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
  std::string name(int Idx = -1);

  /// Get the predicate of the entry if exists. O.w. return nullptr.
  virtual Predicate *getPredicate(int *MaskPtr = nullptr);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *);

  int ID{-1};
  int index();

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

  ComputeBody(DFGBase *Parent, Instruction *Operation);
  int SoftPortNum{-1};

  Instruction *underlyingInst() override;
  std::vector<OutputPort *> getOutPorts();
  bool shouldUnroll() override;

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;
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
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPredicate; }
};

// A accumulator Instruction
struct Accumulator : ComputeBody {
  CtrlSignal *Ctrl;
  Accumulator(DFGBase *Parent, Instruction *Operation, CtrlSignal *Ctrl);
  bool shouldUnroll() override;
  Value *numValuesProduced();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

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
  virtual void accept(dsa::DFGEntryVisitor *) override;

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
  virtual void accept(dsa::DFGEntryVisitor *) override;

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
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCtrlMemPort; }
};

// Memory port can be either a spad or a DMA
struct MemPort : InputPort {
  LoadInst *Load;
  MemPort(DFGBase *Parent, LoadInst *Load);

  static const int PtrOperandIdx;

  bool shouldUnroll() override;
  Instruction *underlyingInst() override;
  int fillMode();
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kMemPort; }
};

// The data to this port is from an output of certain DFG
struct StreamInPort : InputPort {
  Instruction *DataFrom;

  StreamInPort(DFGBase *Parent, Instruction *Inst);
  Instruction *underlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamInPort; }
};

// For control signal, the data consume rate matters
// The control signal should match its consume rate
struct CtrlSignal : InputPort {
  Accumulator *Controlled;
  CtrlSignal(DFGBase *Parent);

  Value *findConsumeRate();

  bool shouldUnroll() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCtrlSignal; }
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
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kInputConst; }
};

// Each later usage of a compute body will form a output port
// Essentially output port is something like a duplication
struct OutputPort : PortBase {
  Instruction *Output;
  Value *ConsumeRate;
  OutputPort(DFGBase *Parent, Value *Value);
  int Latency{-1};

  Instruction *underlyingInst() override;
  int portWidth() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;
  /*!
   * \brief If this value should be unrolled.
   */
  bool shouldUnroll() override;

  static bool classof(const DFGEntry *DE) {
    return DE->Kind > kOutPortStarts && DE->Kind < kOutPortEnds;
  }
};

// Value will be written to memory through a port
struct PortMem : OutputPort {
  StoreInst *Store;
  PortMem(DFGBase *Parent, StoreInst *Store);

  static const int PtrOperandIdx;

  Instruction *underlyingInst() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kPortMem; }
};

// Value will be consumed by another dfg
struct StreamOutPort : OutputPort {

  StreamOutPort(DFGBase *Parent, Instruction *Inst);

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kStreamOutPort; }

  StreamInPort *findConsumer();
};

struct IndMemPort : InputPort {
  MemPort *Index;
  /*!
   * \brief The output port that generates indices.
   *        Do differentiate it with Index->SoftPortNum, that is the input port that feeds indices in.
   */
  int IndexOutPort{-1};
  LoadInst *Load;

  IndMemPort(DFGBase *Parent, LoadInst *Index, LoadInst *Load);
  Instruction *underlyingInst() override;
  std::vector<Instruction *> underlyingInsts() override;
  bool duplicated();
  bool shouldUnroll() override;
  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *) override;

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
  virtual void accept(dsa::DFGEntryVisitor *) override;

  static bool classof(const DFGEntry *DE) { return DE->Kind == kAtomicPortMem; }
};

struct CoalescedMemPort : InputPort {
  std::vector<std::pair<int, MemPort*>> Operations;

  std::vector<Instruction *> underlyingInsts() {
    std::vector<Instruction *> Res;
    auto F = [&Res] (std::pair<int, MemPort*> &Elem) { Res.push_back(Elem.second->underlyingInst()); };
    std::for_each(Operations.begin(), Operations.end(), F);
    return Res;
  }

  /*!
   * \brief The entrance of the visitor pattern.
   */
  virtual void accept(dsa::DFGEntryVisitor *);

  static bool classof(const DFGEntry *DE) { return DE->Kind == kCoalMemPort; }
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
  virtual void Visit(CoalescedMemPort *); // NOLINT
  virtual void Visit(StreamInPort *);     // NOLINT
  virtual void Visit(CtrlSignal *);       // NOLINT
  virtual void Visit(InputConst *);       // NOLINT
  virtual void Visit(OutputPort *);       // NOLINT
  virtual void Visit(PortMem *);          // NOLINT
  virtual void Visit(StreamOutPort *);    // NOLINT
  virtual void Visit(IndMemPort *);       // NOLINT
  virtual void Visit(AtomicPortMem *);    // NOLINT
};

} // namespace dsa

#endif // STREAM_SPECIALIZE_PORT_H_
