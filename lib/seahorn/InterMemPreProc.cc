#include "llvm/ADT/SCCIterator.h"

#include "seahorn/InterMemPreProc.hh"
#include "seahorn/Support/SeaDebug.h"

#include "seadsa/CallGraphUtils.hh"
#include "seadsa/DsaAnalysis.hh"
#include "seadsa/Global.hh"

namespace {

using namespace seadsa;
using namespace llvm;

enum class EColor { BLACK, GRAY }; // colors for exploration
using ExplorationMap = DenseMap<const Node *, EColor>;

bool isSafeNode(NodeSet &unsafe, const Node *n) { return unsafe.count(n) == 0; }

// -- true if 2 nodes encode a memory object of unbounded size
static bool isUnboundedMem(const Node *nSumm, const Node *nTD) {
  return nSumm->isArray() || nSumm->isOffsetCollapsed();
}

struct ExplorationInfo {
  ExplorationMap m_explColor;
  NodeSet &m_calleeUnsafe;
  NodeSet &m_callerUnsafe;
  SimulationMapper &m_sm;
  ExplorationInfo(NodeSet &calleeUnsafe, NodeSet &callerUnsafe,
                  SimulationMapper &sm)
      : m_calleeUnsafe(calleeUnsafe), m_callerUnsafe(callerUnsafe), m_sm(sm) {}
};

static void propagateUnsafeChildren(const Node &n, const Node &nCaller,
                                    ExplorationInfo &ei) {

  // if (isSafeNode(ei.m_calleeUnsafe, &n))
  ei.m_calleeUnsafe.insert(&n); // store the ones that are not safe
                                // if (isSafeNode(ei.m_callerUnsafe, &nCaller))
  ei.m_callerUnsafe.insert(&nCaller);

  ei.m_explColor[&n] = EColor::BLACK;

  for (auto &links : n.getLinks()) {
    const Cell &nextC = *links.second;
    const Node *nextN = nextC.getNode();

    bool explored = ((ei.m_explColor.count(nextN) > 0) &&
                     ei.m_explColor[nextN] == EColor::BLACK);
    bool marked_unsafe = !isSafeNode(ei.m_calleeUnsafe, nextN);

    if (!(explored && marked_unsafe)) {
      const Node &nNextCaller = *ei.m_sm.get(nextC).getNode();
      propagateUnsafeChildren(*nextN, nNextCaller, ei);
    }
  }
}

// -- returns true if the nodes are unsafe
static void exploreNode(const Node &nCallee, const Node &nCaller,
                        ExplorationInfo &ei) {

  assert(ei.m_explColor.count(&nCallee) == 0);

  if (isUnboundedMem(&nCallee, &nCaller)) {
    propagateUnsafeChildren(nCallee, nCaller, ei);
    return;

  } else {
    ei.m_explColor[&nCallee] = EColor::GRAY;

    for (auto &links : nCallee.getLinks()) {
      const Cell &nextC = *links.second;
      const Cell &nextCaller = ei.m_sm.get(nextC);
      const Node *nextN = nextC.getNode();
      if (ei.m_explColor.count(nextN) == 0) // not explored
        exploreNode(*nextN, *nextCaller.getNode(), ei);
      else if (ei.m_explColor.count(nextN) > 0 && // being explored
               ei.m_explColor[nextN] == EColor::GRAY)
        propagateUnsafeChildren(nCallee, nCaller, ei);
      // else, it has been explored already
    }
    ei.m_explColor[&nCallee] = EColor::BLACK;
  }
}

// -- returns true if the nodes are unsafe
static void checkExploreNode(const Node &nCallee, const Node &nCaller,
                             ExplorationInfo &ei) {
  if (ei.m_explColor.count(&nCallee) > 0)
    return;

  exploreNode(nCallee, nCaller, ei);
}

static void computeSafeNodesSimulation(Graph &fromG, const Function &F,
                                       NodeSet &fromSafe, NodeSet &toSafe,
                                       SimulationMapper &sm) {
  NodeSet fromUnsafe, toUnsafe;

  ExplorationInfo ei(fromUnsafe, toUnsafe, sm);

  for (const Argument &a : F.args()) {
    if (fromG.hasCell(a)) { // scalar arguments don't have cells
      const Cell &c = fromG.getCell(a);
      const Node *n = c.getNode();
      const Cell &cCaller = sm.get(c);
      checkExploreNode(*n, *cCaller.getNode(), ei);
    }
  }

  // globals
  for (auto &kv : fromG.globals()) {
    Cell &c = *kv.second;
    checkExploreNode(*c.getNode(), *sm.get(c).getNode(), ei);
  }

  // return cell
  if (fromG.hasRetCell(F)) {
    Cell &c = fromG.getRetCell(F);
    checkExploreNode(*c.getNode(), *sm.get(c).getNode(), ei);
  }

  // ei.m_explColor has the nodes explored
  for (auto kv : ei.m_explColor) {
    const Node *n = kv.first;
    Node *n_caller = sm.get(*n).getNode();
    if (toUnsafe.count(n_caller) == 0) {
      assert(!isUnboundedMem(n, n_caller));
      fromSafe.insert(n);
      toSafe.insert(n_caller);
    }
  }
}
} // namespace

using namespace llvm;

namespace seahorn {
// -- computes the safe nodes per callsite of a module
bool InterMemPreProc::runOnModule(Module &M) {

  const GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  llvm::CallGraph &cg = m_ccg.getCompleteCallGraph();
  for (auto it = scc_begin(&cg); !it.isAtEnd(); ++it) {
    auto &scc = *it;
    for (CallGraphNode *cgn : scc) {
      Function *f_caller = cgn->getFunction();
      if (!f_caller || f_caller->isDeclaration() || f_caller->empty() ||
          !ga.hasGraph(*f_caller))
        continue;

      for (auto &callRecord : *cgn) {
        llvm::Optional<DsaCallSite> optDsaCS =
            call_graph_utils::getDsaCallSite(callRecord);
        if (!optDsaCS.hasValue())
          continue;
        DsaCallSite &dsaCS = optDsaCS.getValue();
        const Function *f_callee = dsaCS.getCallee();
        if (!ga.hasSummaryGraph(*f_callee))
          continue;

        ColorMap color_callee, color_caller;
        NodeSet f_node_safe;

        const Graph &callerG = ga.getGraph(*f_caller);
        const Graph &calleeG = ga.getSummaryGraph(*f_callee);

        const Instruction *I = dsaCS.getInstruction();

        // creating the SimulationMapper object
        SimulationMapper &simMap = m_smCS[I];

        Graph::computeCalleeCallerMapping(
            dsaCS, *(const_cast<Graph *>(&calleeG)),
            *(const_cast<Graph *>(&callerG)), simMap);

        NodeSet &safeCallee = getUnsafeNodesCalleeCS(I); // creates it
        NodeSet &safeCaller = getUnsafeNodesCallerCS(I); // creates it
        computeSafeNodesSimulation(*(const_cast<Graph *>(&calleeG)), *f_callee,
                                   safeCallee, safeCaller, simMap);
      }
    }
  }

  // this includes auxiliary functions, how do I get the original written by the
  // user?
  for (const Function &f : M)
    if (ga.hasSummaryGraph(f))
      runOnFunction(&f);

  return false;
}

NodeSet &InterMemPreProc::getUnsafeNodesCallerCS(const Instruction *I) {
  assert(dyn_cast<const CallInst>(I));
  return m_unsafen_cs_caller[I];
}

NodeSet &InterMemPreProc::getUnsafeNodesCalleeCS(const Instruction *I) {
  assert(dyn_cast<const CallInst>(I));
  return m_unsafen_cs_callee[I];
}

bool InterMemPreProc::isSafeNode(NodeSet &unsafe, const Node *n) {
  return !::isSafeNode(unsafe, n);
}

bool InterMemPreProc::isSafeNodeFunc(const Node &n, const Function *f) {
  assert(m_unsafeNF.count(f) > 0);
  return m_unsafeNF[f].count(&n) == 0;
}

void InterMemPreProc::runOnFunction(const Function *F) {

  GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  if (!ga.hasSummaryGraph(*F))
    return;

  Graph &buG = ga.getSummaryGraph(*F);
  const Graph &sasG = ga.getGraph(*F);

  SimulationMapper &simMap = m_smF[F]; // creates the SimulationMapper object

  bool simulated = Graph::computeSimulationMapping(
      *(const_cast<Graph *>(&buG)), *(const_cast<Graph *>(&sasG)), simMap);
  assert(simulated && "Summary graph could not be simulated with SAS graph");

  NodeSet &safeSAS = m_unsafeNF[F];
  NodeSet safeBU; // won't be used later
  computeSafeNodesSimulation(*(const_cast<Graph *>(&buG)), *F, safeBU, safeSAS,
                             simMap);

  // -- compute number of accesses to safe nodes
  RegionsMap &rm = m_frm[F];

  for (const Argument &a : F->args())
    if (buG.hasCell(a))
      recProcessNode(buG.getCell(a), safeSAS, simMap, rm);

  for (auto &kv : buG.globals())
    recProcessNode(*kv.second, safeSAS, simMap, rm);

  if (buG.hasRetCell(*F))
    recProcessNode(buG.getRetCell(*F), safeSAS, simMap, rm);
}

unsigned InterMemPreProc::getNumCIAccessesCellSummary(const Cell &c,
                                                      const Function *f) {
  assert(m_smF.count(f) > 0);
  SimulationMapper &sm = m_smF[f];
  const Cell nCI = sm.get(c);

  return getNumAccesses(nCI.getNode(), f);
}

// -- processes the nodes in a graph to obtain the number accesses to different
// offsets
// -- cycles cannot happen because those nodes would be marked as unsafe
void InterMemPreProc::recProcessNode(const Cell &cFrom, NodeSet &toSafeNodes,
                                     SimulationMapper &simMap, RegionsMap &rm) {

  const Node *nFrom = cFrom.getNode();

  if (nFrom->size() == 0)
    // the node is not accessed in this graph
    return;

  const Cell &cTo = simMap.get(cFrom);
  const Node *nTo = cTo.getNode();

  if (!isSafeNode(toSafeNodes, nTo))
    return;

  rm[nTo] = rm[nTo] + cFrom.getNode()->types().size();

  // follow the pointers of the node
  for (auto &links : nFrom->getLinks())
    recProcessNode(*links.second, toSafeNodes, simMap, rm);

}

} // namespace seahorn
