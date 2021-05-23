#pragma once

#include "./llvm_common.h"

#include "./Transformation.h"

namespace dsa {
namespace analysis {

/*!
 * \brief Gather all the pairs of dsa.config.start/end
 * \param F The function to be analyzed.
 */
std::vector<std::pair<IntrinsicInst *, IntrinsicInst *>>
GatherConfigScope(Function &F);

/*!
 * \brief Extract dataflow graphs from the given scope
 * \param Start The start instrinsic annotates the scope
 * \param End The end intrinsic annotates the scope
 * \param DT The dominator tree information for analysis
 * \param LI The loop information for analysis
 */
void ExtractDFGFromScope(DFGFile &DF, IntrinsicInst *Start, IntrinsicInst *End,
                         DominatorTree *DT, LoopInfo *LI);

/*!
 * \brief Information for confiration injection.
 */
struct ConfigInfo {
  std::string Name;
  std::string Bitstream;
  int Size;
  ConfigInfo(const std::string &N, const std::string &B, int S)
      : Name(N), Bitstream(B), Size(S) {}
};

/*!
 * \brief Extract the port number from the generated schedule.
 * \param FName The emitted file to be analyzed.
 * \param Ports Write the result in the allocated vector buffer.
 */
ConfigInfo ExtractDFGPorts(std::string FName, DFGFile &DF);

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
  std::vector<analysis::LinearInfo*> TripCount;

  DFGLoopInfo() {}

  DFGLoopInfo(const std::vector<Loop*> &L, const std::vector<analysis::LinearInfo*> &T) :
    LoopNest(L), TripCount(T) {}
};

/*!
 * \brief Gather the loop information of the loop nest that wraps the DFG.
 * \param DB The DFG to be analyzed.
 * \param SE The scalar evolution for analysis.
 */
DFGLoopInfo AnalyzeDFGLoops(DFGBase *DB, ScalarEvolution &SE);

} // namespace analysis
} // namespace dsa