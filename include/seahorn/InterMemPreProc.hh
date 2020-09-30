#pragma once

#include "seadsa/CompleteCallGraph.hh"
#include "seadsa/DsaColor.hh"
#include "seadsa/Mapper.hh"
#include "seadsa/ShadowMem.hh"

#include "seahorn/Expr/ExprCore.hh"

namespace seahorn {

// preprocesor for vcgen with memory copies
class InterMemPreProc {
  /*! \brief Keeps for each CallSite of a module the simulation relation
   * between the caller and the callee (context sensitive), the nodes that
   * unsafe to copy per callee, caller and function (context insensitive).
   */

private:
  seadsa::CompleteCallGraph &m_ccg;
  seadsa::ShadowMem &m_shadowDsa;

  using SimMapperCSMap =
      llvm::DenseMap<const llvm::Instruction *, seadsa::SimulationMapper>;
  SimMapperCSMap m_smCS;

  using SimMapperFMap =
      llvm::DenseMap<const llvm::Function *, seadsa::SimulationMapper>;
  // simulation of BU graph vs SAS graph of the same Function
  SimMapperFMap m_smF;

  using NodesCSMap = llvm::DenseMap<const llvm::Instruction *, NodeSet>;

  NodesCSMap
      m_unsafen_cs_callee; // set of unsafe nodes in the callee of callsite
  NodesCSMap
      m_unsafen_cs_caller; // set of unsafe nodes in the caller of callsite

  using NodeFMap = llvm::DenseMap<const llvm::Function *, NodeSet>;

  NodeFMap m_unsafeNF; // set of unsafe nodes in the callee of a function

  using RegionsMap = llvm::DenseMap<const Node *, unsigned>;
  using FunctionRegionsMap = llvm::DenseMap<const llvm::Function *, RegionsMap>;
  FunctionRegionsMap m_frm;

  using NodeKeysMap = llvm::DenseMap<const Node *, expr::ExprVector>;
  using FunctionNodeKeysMap =
      llvm::DenseMap<const llvm::Function *, NodeKeysMap>;
  FunctionNodeKeysMap m_fnkm;

  expr::ExprFactory &m_efac;
  // -- constant base for keys
  expr::Expr m_keyBase;

public:
  InterMemPreProc(seadsa::CompleteCallGraph &ccg, seadsa::ShadowMem &shadowDsa,
                  expr::ExprFactory &efac);

  /*! \brief For each CallSite of a module, it obtains the simulation relation
   *   between the caller and the callee (context sensitive) and stores it.
   * This is used to compute which nodes are unsafe to copy.
   */
  bool runOnModule(llvm::Module &M);

  NodeSet &getUnsafeNodesCallerCS(const Instruction *I);
  NodeSet &getUnsafeNodesCalleeCS(const Instruction *I);

  bool isSafeNode(NodeSet &unsafe, const seadsa::Node *n);
  bool isSafeNode(const NodeSet &unsafe, const seadsa::Node *n);
  bool isSafeNodeFunc(const Node &n, const Function *f);

  void runOnFunction(const Function *f);

  bool hasSimulationF(const Function *f) { m_smF.count(f) > 0; }
  seadsa::SimulationMapper &getSimulationF(const Function *f) {
    return m_smF[f];
  }

  bool hasSimulationCS(const CallSite &cs) {
    m_smCS.count(cs.getInstruction()) > 0;
  }
  seadsa::SimulationMapper &getSimulationCS(const CallSite &cs) {
    return m_smCS[cs.getInstruction()];
  }

  NodeSet &getUnsafeNodes(const Function *f) { return m_unsafeNF[f]; }

  unsigned getNumAccesses(const Node *n, const Function *f) {
    assert(m_frm.count(f) > 0);
    if (m_frm[f].count(n) == 0)
      return 0;
    else
      return m_frm[f][n];
  }

  unsigned getNumCIAccessesCellSummary(const Cell &c, const Function *f);

  expr::ExprVector &getKeys(const Node *n, const Function *f);
  expr::ExprVector &getKeysCellSummary(const Cell &c, const Function *f);

private:
  void recProcessNode(const Cell &cFrom, const NodeSet &unsafeNodes,
                      SimulationMapper &simMap, RegionsMap &rm,
                      NodeKeysMap &nkm);
};
} // namespace seahorn
