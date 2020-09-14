#ifndef STREAM_SPECIALIZE_PORT_H_
#define STREAM_SPECIALIZE_PORT_H_

#include <set>

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"

#include "dsa/dfg/metadata.h"

using namespace llvm;

class DfgBase;

enum EntryKind {
  kDfgEntry,

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

struct DfgEntry {
  EntryKind Kind;
  DfgBase *Parent;
  std::set<Instruction*> PotentialEpilogue;

  DfgEntry(DfgBase *Parent_);
  virtual ~DfgEntry() {}

  virtual bool IsInMajor();
  virtual bool ShouldUnroll();
  virtual Value *UnderlyingValue();
  virtual Instruction *UnderlyingInst();
  virtual std::vector<Instruction*> UnderlyingInsts() {
    return { UnderlyingInst() };
  }
  virtual std::vector<Value*> UnderlyingValues() {
    std::vector<Instruction*> Res_(UnderlyingInsts());
    std::vector<Value*> Res(Res_.size());
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

  virtual bool OperandReady(std::set<Value*> &Ready);
  virtual int getAbstainBit();

  /// Get the name of the entry to be dumped in the DFG textformat
  std::string NameInDfg(int vec = -1);

  /// Get the predicate of the entry if exists. O.w. return nullptr.
  virtual Predicate *getPredicate(int *MaskPtr = nullptr);

  int ID{-1};
  int Index();

  static bool classof(const DfgEntry *DE) {
    return true;
  }

};

struct CtrlSignal;
struct OutputPort;
struct InputPort;
struct AtomicPortMem;

// A wrapper to Instruction
// A simple compute instruction
struct ComputeBody : DfgEntry {
  Instruction *Operation;
  
  ComputeBody(DfgBase *Parent_, Instruction *Operation_);
  int SoftPortNum{-1};

  Instruction *UnderlyingInst() override;
  std::vector<OutputPort*> GetOutPorts();
  bool ShouldUnroll() override;
  virtual void EmitCB(std::ostringstream &os);

  // If this instruction is handled by atomic operation.
  AtomicPortMem *isAtomic();
  // If this instruction is immidiately consumed by an atomic operation.
  AtomicPortMem *isImmediateAtomic();
  // (base on the method above) If so, regard this as an output.
  void EmitAtomic(std::ostringstream &os);

  static bool classof(const DfgEntry *DE) {
    return DE->Kind > kComputeStarts && DE->Kind < kComputeEnds;
  }

};

struct Predicate : DfgEntry {
  SmallVector<Instruction*, 0> Cond;
  SmallVector<bool, 0> Reversed;

  Predicate(DfgBase *Parent_, Instruction *Cond_);
  Instruction *UnderlyingInst() override;
  bool ShouldUnroll() override;
  void EmitCond(std::ostringstream &os);
  bool addCond(Instruction *Inst);
  int Contains(Instruction *Inst);
  int ToCompareRes(Instruction *Inst, bool TF);
  std::vector<Instruction*> UnderlyingInsts() override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kPredicate;
  }
};

// A accumulator Instruction
struct Accumulator : ComputeBody {
  CtrlSignal *Ctrl;
  Accumulator(DfgBase *Parent_, Instruction *Operation_, CtrlSignal *Ctrl_);
  bool ShouldUnroll() override;
  bool OperandReady(std::set<Value*> &Ready) override;
  void EmitCB(std::ostringstream &os) override;
  Value *NumValuesProduced();

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kAccumulator;
  }

};

// Base class for ports
// The essential difference is data stream vector
struct PortBase : DfgEntry {
  int SoftPortNum;
  bool IntrinInjected;
  dsa::dfg::MetaPort Meta;

  virtual int PortWidth();
  PortBase(DfgBase *Parent_);
  bool OperandReady(std::set<Value*> &Ready) override;
  virtual void InjectStreamIntrinsic(IRBuilder<> *IB) {}
  int VectorizeFactor();

  static bool classof(const DfgEntry *DE) {
    return DE->Kind > kPortStarts && DE->Kind < kPortEnds;
  }

};

// Input port has a repeat
struct InputPort : PortBase {
  InputPort(DfgBase *Parent_);

  virtual void EmitInPort(std::ostringstream &os);

  static bool classof(const DfgEntry *DE) {
    return DE->Kind > kInPortStarts && DE->Kind < kInPortEnds;
  }

};

struct CtrlMemPort : InputPort {
  LoadInst *Load;
  Value *Start, *TripCnt;
  Predicate *Pred;
  int Mask;
  bool ForPredicate{false};

  CtrlMemPort(DfgBase *, LoadInst *, Value *Start_, Value *TripCnt_, Predicate *, int Mask_);

  Predicate *getPredicate(int *MaskPtr = nullptr) override;
  Instruction *UnderlyingInst() override;
  void InjectStreamIntrinsic(IRBuilder<> *) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kCtrlMemPort;
  }
};

// Memory port can be either a spad or a DMA
struct MemPort : InputPort {
  LoadInst *Load;
  MemPort(DfgBase *Parent_, LoadInst *Load_);

  bool ShouldUnroll() override;
  Instruction *UnderlyingInst() override;
  int FillMode();

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kMemPort;
  }
  void InjectStreamIntrinsic(IRBuilder<> *IB) override;

 private:
  bool InjectUpdateStream(IRBuilder<> *IB);
};

// The data to this port is from an output of certain DFG
struct StreamInPort : InputPort {
  Instruction *DataFrom;

  StreamInPort(DfgBase *Parent, Instruction *Inst);
  Instruction *UnderlyingInst() override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kStreamInPort;
  }

};

// For control signal, the data consume rate matters
// The control signal should match its consume rate
struct CtrlSignal : InputPort {
  Accumulator *Controlled;
  CtrlSignal(DfgBase *Parent_);

  Value *FindConsumeRate();

  bool ShouldUnroll() override;
  void EmitInPort(std::ostringstream &os) override;
  void InjectStreamIntrinsic(IRBuilder<> *IB) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kCtrlSignal;
  }

};

// A loop invariant through all the loop levels,
// but not a compilation time constant.
struct InputConst : InputPort {
  Value *Val;

  InputConst(DfgBase *Parent, Value *Val);

  Value *UnderlyingValue() override;
  Instruction *UnderlyingInst() override;
  std::vector<Value*> UnderlyingValues() override;
  std::vector<Instruction*> UnderlyingInsts() override;
  void EmitInPort(std::ostringstream &os) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kInputConst;
  }

  void InjectStreamIntrinsic(IRBuilder<> *IB) override;

};

// Each later usage of a compute body will form a output port
// Essentially output port is something like a duplication
struct OutputPort : PortBase {
  Instruction *Output;
  Value *ConsumeRate;
  OutputPort(DfgBase *Parent_, Value *Value_);
  int Latency{-1};

  Instruction *UnderlyingInst() override;
  int PortWidth() override;
  virtual void EmitOutPort(std::ostringstream &os);

  static bool classof(const DfgEntry *DE) {
    return DE->Kind > kOutPortStarts && DE->Kind < kOutPortEnds;
  }

  void InjectStreamIntrinsic(IRBuilder<> *) override;

};

// Value will be written to memory through a port
struct PortMem : OutputPort {
  StoreInst *Store;
  PortMem(DfgBase *Parent_, StoreInst *Store_);

  bool ShouldUnroll() override;
  Instruction *UnderlyingInst() override;
  void InjectStreamIntrinsic(IRBuilder<> *IB) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kPortMem;
  }

};

// Value will be consumed by another dfg
struct StreamOutPort : OutputPort {

  StreamOutPort(DfgBase *Parent_, Instruction *Inst);

  void InjectStreamIntrinsic(IRBuilder<> *IB);

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kStreamOutPort;
  }

  StreamInPort *FindConsumer();

};

struct IndMemPort : InputPort {
  MemPort *Index;
  LoadInst *Load;

  IndMemPort(DfgBase *Parent_, LoadInst *Index, LoadInst *Load);
  Instruction *UnderlyingInst() override;
  std::vector<Instruction*> UnderlyingInsts() override;
  bool duplicated();
  bool ShouldUnroll() override;

  void InjectStreamIntrinsic(IRBuilder<> *IB) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kIndMemPort;
  }

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

  AtomicPortMem(DfgBase *Parent_, LoadInst *Index_, StoreInst *Store_, int OpCode,
                Instruction *Op_, Value *Operand_);
  Instruction *UnderlyingInst() override;

  void InjectStreamIntrinsic(IRBuilder<> *IB) override;
  std::vector<Instruction*> UnderlyingInsts() override;
  void EmitOutPort(std::ostringstream &os) override;

  static bool classof(const DfgEntry *DE) {
    return DE->Kind == kAtomicPortMem;
  }

};

#endif // STREAM_SPECIALIZE_PORT_H_
