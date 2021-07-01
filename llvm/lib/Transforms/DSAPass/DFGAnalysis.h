#pragma once

#include "./llvm_common.h"

#include "./Transformation.h"

namespace dsa {
namespace analysis {

struct CoalMemoryInfo;

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
 * \param CMIs The coalesced memory.
 */
ConfigInfo ExtractDFGPorts(std::string FName, DFGFile &DF, std::vector<CoalMemoryInfo> &CMIs);

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

/*!
 * \brief Analyze the offset between two memory operation indices.
 * \param SA The first index.
 * \param SB The second index.
 * \param SE Scalar evolution for memory stream analysis.
 * \param DLI The loop information associated to the DFG.
 * \param Signed If result of analysis is signed.
 */
int64_t IndexPairOffset(const SCEV *SA, const SCEV *SB, ScalarEvolution &SE, const DFGLoopInfo &DLI, bool Signed);

/*!
 * \brief The implementation of coalescing memory operations.
 * @tparam T The DFGEntry type to be gathered, either MemPort or PortMem.
 * \param DB The DFG to be analyzed.
 * \param SE Scalar evolution for memory stream analysis.
 * \param DLI The loop information associated to the DFG.
 * \param DSU The disjoint union to be updated by coalescing.
 */
template<typename T>
void GatherMemoryCoalescingImpl(DFGBase *DB, ScalarEvolution &SE, const DFGLoopInfo& DLI, std::vector<int> &DSU) {
  bool Iterative = true;
  while (Iterative) {
    Iterative = false;
    auto DLI = dsa::analysis::AnalyzeDFGLoops(DB, SE);
    for (int i = 0, n = DB->Entries.size(); i < n; ++i) {
      if (auto Node1 = dyn_cast<T>(DB->Entries[i])) {
        for (int j = i + 1; j < n; ++j) {
          if (auto Node2 = dyn_cast<T>(DB->Entries[j])) {
            auto PtrA = Node1->UnderlyingInst()->getOperand(T::PtrOperandIdx);
            auto PtrB = Node2->UnderlyingInst()->getOperand(T::PtrOperandIdx);
            if (PtrA->getType() != PtrB->getType()) {
              continue;
            }
            auto Offset = IndexPairOffset(SE.getSCEV(PtrA), SE.getSCEV(PtrB), SE, DLI, false);
            if (Offset != -1 && Offset <= 64) {
              if (utils::DSUGetSet(i, DSU) != utils::DSUGetSet(j, DSU)) {
                DSU[utils::DSUGetSet(i, DSU)] = utils::DSUGetSet(j, DSU);
                Iterative = true;
                break;
              }
            }
          }
        }
      }
    }
  }
}

struct CoalMemoryInfo {
  /*!
   * \brief Which set of memory coalescing this memory operation belongs to.
   */
  std::vector<int> Belong;

  struct CoalescedEntry {
    /*!
     * \brief The ID of the DFGEntry.
     */
    int ID;
    /*!
     * \brief The offset relative to the first element of the cluster.
     */
    int Offset{INT_MIN};

    CoalescedEntry(int ID_) : ID(ID_) {}
  };
  /*!
   * \brief Each vector is a cluster of coalesced memory.
   */
  std::vector<std::vector<CoalescedEntry>> Clusters;
  /*!
   * \brief The port number of each coalesced port.
   */
  std::vector<int> ClusterPortNum;
};

/*!
 * \brief
 * \param DF 
 * \param SE 
 * \param DLI 
 */
std::vector<CoalMemoryInfo> GatherMemoryCoalescing(DFGFile &DF, ScalarEvolution &SE, const std::vector<DFGLoopInfo> &DLI);

} // namespace analysis
} // namespace dsa