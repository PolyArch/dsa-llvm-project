#pragma once

#include <map>
#include <unordered_map>

#include "./llvm_common.h"

#include "./DFGEntry.h"
#include "./DFGIR.h"
#include "./RTTIUtils.h"

namespace dsa {

namespace xform {

struct CodeGenContext;

enum DataStreamKind {
  kDataStream,
  kLinear1D,
  kLinear2D,
  kIndirect1D,
  kIndirect2D
};


/*!
 * \brief The base class of indirect stream emission.
 */
struct DataStream {
  /*!
   * \brief RTTI type.
   */
  int TyEnum{kDataStream};
  /*!
   * \brief Port destination.
   */
  int DestPort{-1};
  /*!
   * \brief The data type of data accessed.
   */
  int DType;
  /*!
   * \brief The data type of index.
   */
  int IType;
  /*!
   * \brief Emit this stream to program intrinsic.
   */
  virtual void emitIntrinsic(xform::CodeGenContext &CGC) = 0;

  DataStream(int D, int I) : DType(D), IType(I) {}

  RTTI_CLASS_OF(DataStream, kDataStream)
};

struct Linear1D : DataStream {
  /*
   * \brief Begin address.
   */
  const SCEV *SAR;
  /*!
   * \brief Trip count.
   */
  const SCEV *L1D;
  /*!
   * \brief Word stride.
   */
  const SCEV *I1D;
  /*!
   * \brief Repeat.
   */
  const SCEV *Repeat;
  /*!
   * \brief Repeat stretch.
   */
  const SCEV *RStretch;

  void emitIntrinsic(xform::CodeGenContext &CGC) override;

  RTTI_CLASS_OF(DataStream, kLinear1D)
};

struct Linear2D : DataStream {
  /*!
   * \brief Inner dimension.
   */
  Linear1D L1D;
  /*!
   * \brief Outer trip count.
   */
  const SCEV *L2D;
  /*!
   * \brief Inner stride.
   */
  const SCEV *I2D;
  /*!
   * \brief Inner stretch.
   */
  const SCEV *E2D;

  RTTI_CLASS_OF(DataStream, kLinear2D)
};

/*!
 * \brief The extracted 1D stream. a[b[i]].
 */
// TODO(@were): Support more complicated pattern than b[i].
struct Indirect1D : DataStream {
  /*!
   * \brief The base address of indirect load.
   */
  const SCEV *SAR;
  /*!
   * \brief The trip count of loading.
   */
  const SCEV *L1D;
  /*!
   * \brief The port of index analysis.
   */
  int IdxPort{-1};
  /*!
   * \brief Stream of b[i].
   */
  analysis::SEWrapper *Idx;
  /*!
   * \brief Emit this stream to program intrinsic.
   */
  void emitIntrinsic(xform::CodeGenContext &CGC);

  Indirect1D(int D, int I, const SCEV *S, const SCEV *L, analysis::SEWrapper *Idx) :
    DataStream(D, I), SAR(S), L1D(L), Idx(Idx) {
    TyEnum = kIndirect1D;
  }

  RTTI_CLASS_OF(DataStream, kIndirect1D)
};

/*!
 * \brief The extracted 1D stream. (a + b[i])[idx[j] + j * stride1d].
 */
struct Indirect2D : DataStream {
  /*!
   * \brief The port where (a + b[i]) comes.
   */
  int OffsetPort{-1};
  /*!
   * \brief The begin address can either be a stream or a constant.
   */
  analysis::SEWrapper *SAR;
  /*
   * \brief The port where idx[j] comes.
   */
  int IdxPort{-1};
  /*!
   * \brief The index can either be a stream or a constant 0.
   */
  analysis::SEWrapper *Idx;
  /*!
   * \brief The 1D trip count can either be a stream or a constant from L1D register.
   */
  analysis::SEWrapper *L1D;
  /*!
   * \brief Later, this L1D will be instantiated into this DFG.
   */
  DedicatedDFG *L1DDFG{nullptr};
  /*!
   * \brief The outer loop trip count.
   */
  const SCEV *L2D;
  /*!
   * \brief Emit this stream to program intrinsic.
   */
  void emitIntrinsic(xform::CodeGenContext &CGC);

  Indirect2D(int D, int I, analysis::SEWrapper *S, analysis::SEWrapper *Idx,
             analysis::SEWrapper *L1D, const SCEV *L2D) :
    DataStream(D, I), SAR(S), Idx(Idx), L1D(L1D), L2D(L2D) {
    TyEnum = kIndirect2D;
  }

  RTTI_CLASS_OF(DataStream, kIndirect2D)
};

} // namespace xform

namespace analysis {


/*!
 * \brief Information of the bitstream.
 */
struct ConfigInfo {
  /*!
   * \brief The name of the bitstream array.
   */
  std::string Name;
  /*!
   * \brief The content of the bitstream.
   */
  std::string Bitstream;
  union {
    /*!
     * \brief The size of the bitstream array.
     */
    int Size;
    /*!
     * \brief The code of scheduler return when failed.
     */
    int Code;
  };
  /*
   * \brief The performance estimated for the DFG.
   */
  double EstimatedILP{0};
  /*!
   * \brief If this is an empty configuration.
   */
  bool empty() { return Bitstream.empty(); }

  ConfigInfo(const std::string &N, const std::string &B, int S)
      : Name(N), Bitstream(B), Size(S) {}

  ConfigInfo() : Name(""), Bitstream(""), Size(0) {}
};

/*!
 * \brief The information of the scratchpads.
 */
struct SpadInfo {
  /*! \brief Offset The begin of arrays. */
  std::map<AllocaInst*, int> Offset;

  // [Linear Read Stream, Address Offset, Buffer Size, Load Port, Store Port]
  using BuffetEntry = std::tuple<InputPort*, int, int, int, int>;
  /*! \brief Buffet The information of buffet double buffering. */
  std::vector<BuffetEntry> Buffet;
  /*! \brief The total bytes occupied on SPAD. */
  int Total{0};

  /*!
   * \brief If the given pointer is on scratchpad.
   * \param Val The pointer to be inspected.
   */
  bool isSpad(Value *Val);

  SpadInfo(std::map<AllocaInst*, int> &O, std::vector<BuffetEntry> &B, int T) :
    Offset(O), Buffet(B), Total(T) {}

  SpadInfo() {}
};

/*!
 * \brief Analyze DFG loops for code generation.
 */
struct DFGLoopInfo {
  /*!
   * \brief The loop nest, from inner to outer.
   */
  std::vector<Loop*> LoopNest;
  /*!
   * \brief The trip count of each loop level, corresponding to the loop nest above.
   */
  std::vector<analysis::SEWrapper*> TripCount;

  DFGLoopInfo() {}

  DFGLoopInfo(const std::vector<Loop*> &L, const std::vector<analysis::SEWrapper*> &T) :
    LoopNest(L), TripCount(T) {}
};

struct AccInfo {
  /*!
   * \brief The loop level of accumulator register resetting.
   */
  int ResetLevel;
  /*
   * \brief The loop level of finalizing the result.
   */
  int ProduceLevel;

  AccInfo(int R = -1, int P = INT_MAX) : ResetLevel(R), ProduceLevel(P) {}
};


/*! \brief The result of DFG analysis. */
struct DFGAnalysisResult {
  /*!
   * \brief The information of DFG configuration. Filled by `extractDFGPorts`.
   */
  ConfigInfo CI;
  /*!
   * \brief Scratchpad infomation is global in a configuration-wise.
   *        Filled by `extractSpadFromScope`.
   */
  SpadInfo SI;
  /*!
   * \brief The loop information of each DFG. Filled by `analyzeDFGLoops`.
   */
  std::vector<DFGLoopInfo> DLI;
  /*!
   * \brief The information of an accumulator.
   */
  std::unordered_map<Accumulator*, AccInfo> AI;
  /*!
   * \brief Data structures for streams that are ready-codegen.
   */
  std::unordered_map<DFGEntry*, xform::DataStream*> Streams;
  /*!
   * \brief The size of the given array pointer array.
   */
  std::unordered_map<Value *, llvm::CallInst*> ArraySize;

 private:
  /*!
   * \brief The linear memory access information of each affine stream.
   *        Filled by `analyzeDFGMemoryAccess`.
   */
  std::unordered_map<DFGEntry*, SEWrapper*> AffineInfoCache;
 public:
  /*!
   * \brief Override linear stream analysis.
   */
  std::unordered_map<const SCEV*, const SCEV*> LinearOverride;
  /*!
   * \brief
   */
  SEWrapper *affineMemoryAccess(DFGEntry *DE, ScalarEvolution &SE, bool AllowNull);
  /*!
   * \brief
   */
  void initAffineCache(DFGFile &DF, ScalarEvolution &SE);
  /*!
   * \brief
   */
  void overrideStream(DFGEntry *DE, SEWrapper *SW) { AffineInfoCache[DE] = SW; }
  /*!
   * \brief
   */
  void fuseAffineDimensions(ScalarEvolution &SE);

  void injectAnalyzedArrayHint(DFGFile &DF, dsa::xform::CodeGenContext &CGC);
};


/*!
 * \brief Enumerate the unrolling degree.
 */
struct DFGUnroll {

  DFGUnroll(DFGFile &DF, xform::CodeGenContext &CGC);

  /*!
   * \brief If we have next points to enumerate.
   */
  bool hasNext();

  /*!
   * \brief The next point of the DFG file.
   * \param Apply If it is applied.
   */
  bool next(bool Apply);

  /*!
   * \brief The suffix of the file name.
   */
  std::string toString();

  /*!
   * \brief The DFG file to explore
   */
  DFGFile &DF;

  /*
   * \brief The total number of points to be explored.
   */
  int Cnt{0};

  /*!
   * \brief The total number skipped because of pruning.
   */
  int Skip{0};

  /*!
   * \brief The results of scheduling.
   */
  int BestAt{-1};

  /*!
   * \brief The current enumeration.
   */
  std::vector<int> Idx;

  std::vector<bool> Explored;

  /*!
   * \brief The total degrees to enum.
   */
  std::vector<std::vector<int>> Degrees;

  /*!
   * \brief Sumup the block freqency.
   */
  std::vector<int> Freq;

  /*!
   * \brief The result of DFG analysis.
   */
  std::vector<DFGAnalysisResult> DAR;

  DFGAnalysisResult &best();
};

/*!
 * \brief Gather all the pairs of dsa.config.start/end
 * \param F The function to be analyzed.
 */
std::vector<std::pair<IntrinsicInst *, IntrinsicInst *>>
gatherConfigScope(Function &F);

/*!
 * \brief Gather the array size hint intrinsics.
 * \param DF The DFG file to be analyzed.
 * \param CGC The LLVM context.
 * \param DAR The analyzed results to put in.
 */
void gatherArraySizeHints(DFGFile &DF, dsa::xform::CodeGenContext &CGC, DFGAnalysisResult &DAR);

/*!
 * \brief
 */
std::unordered_map<const SCEV*, const SCEV*>
gatherLinearOverride(IntrinsicInst *, IntrinsicInst *, xform::CodeGenContext &CGC);

/*!
 * \brief Gather the loop information of the loop nest that wraps the DFG.
 * \param DF The scope to be analyzed.
 * \param CGC The LLVM utilities passed.
 * \param DAR The result of scopes should go. Specifically, the `DLI` attr.
 */
void analyzeDFGLoops(DFGFile &DF, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR);

/*!
 * \brief Gather the the scratchpad local variables.
 * \param Start The starting scope of DFG.
 * \param End The end scope of DFG. Specifically, the `SI` attr.
 */
void extractSpadFromScope(DFGFile &DF, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR);

/*!
 * \brief Extract dataflow graphs from the given scope
 * \param DF The DFG scope to be analyzed.
 * \param CGC The LLVM utilities passed.
 */
void extractDFGFromScope(DFGFile &DF, dsa::xform::CodeGenContext &CGC);

/*!
 * \brief Extract the port number from the generated schedule.
 * \param Ports Write the result in the allocated vector buffer.
 * \param CMIs The coalesced memory.
 */
ConfigInfo extractDFGPorts(DFGFile &DF, SpadInfo &SI, bool Schedule);

/*!
 * \brief Analyze the information of accumulator.
 * \param DF The DFG file to be analyzed.
 * \param CGC The context required for the analysis.
 * \param DAR The result to be written to.
 */
void analyzeAccumulatorTags(DFGFile &DF, xform::CodeGenContext &CGC,
                            DFGAnalysisResult &DAR);

/*!
 * \brief Gather all the memory that can be SLP-coalesced in the given DFG file.
 *        By SLP, we mean a[i], a[i+1] can be coalesced into one a[2] vector port.
 * \param DF The DFG file to be analyzed.
 * \param SE The LLVM scalar evolution.
 * \param DAR The result of DFG analysis from previous pass.
 */
void gatherMemoryCoalescing(DFGFile &DF, ScalarEvolution &SE, DFGAnalysisResult &DAR);

/*!
 * \brief BFS back to all the instructions within/outside the DFG scope
 *        on which the given instruction depends.
 * \param DB The DFG scope.
 * \param From The given source instruction of BFS.
 * \param DT The dominator tree. Can be null, then domination is not checked.
 * \return A pair of sets of instructions. The instructions within the scope, and the instruction
 *         outside the scope.
 */
std::pair<std::set<Instruction *>, std::set<Instruction *>>
bfsOperands(DFGBase *DB, Instruction *From, DominatorTree *DT);


/*!
 * \brief Find The name of the array involved.
 * \param Ptr The pointer expression to be analyzed.
 * \param AS The DMA arrays declared.
 * \param SI The SPM arrays declared.
 */
Value* findArrayInvolved(Instruction *Ptr, std::unordered_map<Value*, CallInst*> &AS,
                         SpadInfo &SI);

/*!
 * \brief Extract analyzed streams to ready-codegen format.
 * \param DF The DFG file to be analyzed.
 * \param CGC The context required for the analysis.
 * \param DAR The result to be written to.
 */
xform::DataStream*
analyzedWrapperToStream(DFGEntry *DE, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR);

/*!
 * \brief A wrapper helper function.
 *        If an input port is used as a tag of accumulator, return the
 *        affine loop level of resetting the register.
 * \param IP The input port to inspect.
 */
int resetLevel(InputPort *IP, DFGAnalysisResult &DAR);

/*!
 * \brief TODO(@were): doc this!
 */
const SCEV *productTripCount(std::vector<analysis::SEWrapper*> &TC, ScalarEvolution *SE);

xform::DataStream *
extractStreamIntrinsics(DFGEntry *DE, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR);

/*
 * \brief Use DFG Loop Nest to figure out overall DFG Traffic
 */ 
float getPortDataTraffic(LinearCombine *LC, float PortDType); 
/*
 * \brief Find the reuse at a given level
 */
float getReuseTrafficAtLevel(LinearCombine *LC, int Lvl, float BaseStream);

/*
 * \brief Fint the reuse of a given port
 */
std::pair<float, float> getPortReuse(DFGEntry *DE, xform::CodeGenContext &CGC, DFGAnalysisResult &DAR, float PortDType); 

} // namespace analysis
} // namespace dsa
