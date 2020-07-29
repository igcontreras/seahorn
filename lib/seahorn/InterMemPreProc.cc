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

  if (isSafeNode(ei.m_calleeUnsafe, &n))
    ei.m_calleeUnsafe.insert(&n); // we store the ones that are not safe
  if (isSafeNode(ei.m_callerUnsafe, &nCaller))
    ei.m_callerUnsafe.insert(&nCaller); // we store the ones that are not safe

  ei.m_explColor[&n] = EColor::BLACK;

  for (auto &links : n.getLinks()) {
    const Field &f = links.first;
    const Cell &nextC = *links.second;
    const Node *nextN = nextC.getNode();

    bool explored = ((ei.m_explColor.count(nextN) > 0) && ei.m_explColor[nextN] == EColor::BLACK);
    bool marked_safe = isSafeNode(ei.m_calleeUnsafe, nextN);

    if (!(explored && !marked_safe)) {
      const Node &nNextCaller = *ei.m_sm.get(nextC).getNode();

      propagateUnsafeChildren(*nextN, nNextCaller, ei);
    }
  }
}

static bool exploreNode(const Node &nCallee, const Node &nCaller,
                        ExplorationInfo &ei) {
  ei.m_explColor[&nCallee] = EColor::GRAY;

  for (auto &links : nCallee.getLinks()) {
    const Field &f = links.first;
    const Cell &nextC = *links.second;
    const Cell &nextCaller = ei.m_sm.get(nextC);
    const Node *nextN = nextC.getNode();
    if (nextN->isArray() || nextCaller.getNode()->isOffsetCollapsed()) { // encodes an object of unbounded size
      propagateUnsafeChildren(nCallee, nCaller, ei);
      return true;
    } else {
      if (ei.m_explColor.count(nextN) == 0 &&
               exploreNode(*nextN, *nextCaller.getNode(), ei))
	return true;
      else if (ei.m_explColor.count(nextN) > 0 && ei.m_explColor[nextN] == EColor::GRAY) {
	propagateUnsafeChildren(nCallee, nCaller, ei);
	return true;
      }
    }
  }
  ei.m_explColor[&nCallee] = EColor::BLACK;

  return false;
}

static void computeUnsafeNodesSimulation(Graph &fromG, const Function &F,
                                         NodeSet &fromUnsafe,
                                         NodeSet &callerUnsafe,
                                         SimulationMapper &sm) {
  ExplorationInfo ei(fromUnsafe, callerUnsafe, sm);

  for (const Argument &a : F.args()) {
    if (fromG.hasCell(a)) { // scalar arguments don't have cells
      const Cell &c = fromG.getCell(a);
      const Node *n = c.getNode();
      const Cell &cCaller = sm.get(c);
      exploreNode(*n, *cCaller.getNode(), ei);
    }
  }

  // globals
  for (auto &kv :
       boost::make_iterator_range(fromG.globals_begin(), fromG.globals_end())) {
    Cell &c = *kv.second;
    exploreNode(*c.getNode(), *sm.get(c).getNode(), ei);
  }

  // return cell
  if (fromG.hasRetCell(F)) {
    Cell &c = fromG.getRetCell(F);
    exploreNode(*c.getNode(), *sm.get(c).getNode(), ei);
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
        const Graph &fromG = ga.getSummaryGraph(*f_callee);

        const Instruction *I = dsaCS.getInstruction();

        // creating the SimulationMapper object
        SimulationMapper &simMap = m_smCS[I];

        Graph::computeCalleeCallerMapping(dsaCS, *(const_cast<Graph *>(&fromG)),
                                          *(const_cast<Graph *>(&callerG)),
                                          simMap);

        NodeSet &unsafeCallee = getUnsafeNodesCalleeCS(I); // creates it
        NodeSet &unsafeCaller = getUnsafeNodesCallerCS(I); // creates it
        computeUnsafeNodesSimulation(*(const_cast<Graph *>(&fromG)), *f_callee,
                                     unsafeCallee, unsafeCaller, simMap);
      }
    }
  }

  // this includes auxiliary functions, how do I get the original written by the
  // user?
  for (const Function &f : M)
    if (ga.hasSummaryGraph(f))
      preprocFunction(&f);

  return false;
}

NodeSet &InterMemPreProc::getUnsafeNodesCallerCS(const Instruction *I) {
  const CallInst *CI = dyn_cast<const CallInst>(I);
  assert(CI);
  return m_unsafen_cs_caller[I];
}

NodeSet &InterMemPreProc::getUnsafeNodesCalleeCS(const Instruction *I) {
  const CallInst *CI = dyn_cast<const CallInst>(I);
  assert(CI);
  return m_unsafen_cs_callee[I];
}

bool InterMemPreProc::isSafeNode(NodeSet &unsafe, const Node *n) {
  return ::isSafeNode(unsafe, n);
}

bool InterMemPreProc::isSafeNodeFunc(const Node &n, const Function *f) {
  assert(m_unsafeNF.count(f) > 0);
  return m_unsafeNF[f].count(&n) == 0;
}

void InterMemPreProc::preprocFunction(const Function *F) {

  GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  if(!ga.hasSummaryGraph(*F))
    return;

  Graph &buG = ga.getSummaryGraph(*F);
  const Graph &sasG = ga.getGraph(*F);

  SimulationMapper &simMap = m_smF[F]; // creates the SimulationMapper object

  bool simulated = Graph::computeSimulationMapping(
      *(const_cast<Graph *>(&buG)), *(const_cast<Graph *>(&sasG)), simMap);
  assert(simulated && "Summary graph could not be simulated with SAS graph");

  NodeSet &unsafeSAS = m_unsafeNF[F];
  NodeSet unsafeBU; // won't be used later
  computeUnsafeNodesSimulation(*(const_cast<Graph *>(&buG)), *F, unsafeBU,
                               unsafeSAS, simMap);

  // -- compute number of accesses to safe nodes
  NodeSet explored; // track exploration, needs to be empty for every starting cell
  RegionsMap &rm = m_frm[F];

  for (const Argument &a : F->args())
    if (buG.hasCell(a)){
      explored.clear();
      recProcessNode(buG.getCell(a), unsafeSAS, simMap, explored, rm);
    }

  for (auto &kv :
       boost::make_iterator_range(buG.globals_begin(), buG.globals_end())) {
    Cell &c = *kv.second;
    explored.clear();
    recProcessNode(c, unsafeSAS, simMap, explored, rm);
  }

  if (buG.hasRetCell(*F)){
    explored.clear();
    recProcessNode(buG.getRetCell(*F), unsafeSAS, simMap, explored, rm);
  }
}

unsigned InterMemPreProc::getNumCIAccessesCellSummary(const Cell &c,
                                                      const Function *f) {
  assert(m_smF.count(f) > 0);
  SimulationMapper &sm = m_smF[f];
  const Cell nCI = sm.get(c);

  return getNumAccesses(nCI.getNode(), f);
}

void InterMemPreProc::recProcessNode(const Cell &cFrom, NodeSet &unsafeNodes,
                                     SimulationMapper &simMap,
                                     NodeSet &explored, RegionsMap &rm) {

  const Node *nFrom = cFrom.getNode();
  explored.insert(nFrom);

  if (nFrom->size() == 0 || nFrom->isArray())
    // the array was created but not accessed in this graph
    return;

  const Cell &cTo = simMap.get(cFrom);
  const Node *nTo = cTo.getNode();

  if (!cFrom.getNode()->types().empty() && isSafeNode(unsafeNodes, nTo))
    rm[nTo] = rm[nTo] + cFrom.getNode()->types().size();

  if (nFrom->getLinks().empty())
    return;

  // follow the pointers of the node
  for (auto &links : nFrom->getLinks()) {
    const Cell &nextC = *links.second;
    const Node *nextN = nextC.getNode();

    if (explored.find(nextN) == explored.end()) // not explored yet
      recProcessNode(nextC, unsafeNodes, simMap, explored, rm);
  }
}

} // namespace seahorn
