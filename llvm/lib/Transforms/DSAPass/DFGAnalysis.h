#pragma once

#include "./llvm_common.h"

#include "./Transformation.h"

namespace dsa {
namespace analysis {

/*!
 * \brief Gather all the pairs of dsa.config.start/end
 * \param F The function to be analyzed.
 */
std::vector<std::pair<IntrinsicInst*, IntrinsicInst*>>
GatherConfigScope(Function &F);

/*!
 * \brief Extract dataflow graphs from the given scope
 * \param Start The start instrinsic annotates the scope
 * \param End The end intrinsic annotates the scope
 * \param DT The dominator tree information for analysis
 * \param LI The loop information for analysis
 */
void ExtractDFGFromScope(DFGFile &DF,
                         IntrinsicInst *Start, IntrinsicInst *End,
                         DominatorTree *DT, LoopInfo *LI);

struct ConfigInfo {
  std::string Name;
  std::string Bitstream;
  int Size;
  ConfigInfo(const std::string &N, const std::string &B, int S) :
    Name(N), Bitstream(B), Size(S) {}
};

/*!
 * \brief Extract the port number from the generated schedule.
 * \param FName The emitted file to be analyzed.
 * \param Ports Write the result in the allocated vector buffer.
 */
ConfigInfo ExtractDFGPorts(std::string FName, DFGFile &DF);

}
}