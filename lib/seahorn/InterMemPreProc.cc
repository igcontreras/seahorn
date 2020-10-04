#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/InterMemPreProc.hh"
#include "seahorn/Support/SeaDebug.h"

#include "seadsa/CallGraphUtils.hh"
#include "seadsa/DsaAnalysis.hh"
#include "seadsa/Global.hh"

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprOpArray.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprOpVariant.hh"

namespace seahorn {
// flag for the maximum size of an fmap
extern unsigned FmapsMaxKeys;
} // namespace seahorn

namespace {

using namespace seadsa;
using namespace llvm;
using namespace expr;

enum class EColor { BLACK, GRAY }; // colors for exploration
using ExplorationMap = DenseMap<const Node *, EColor>;

bool isSafeNode(const NodeSet &unsafe, const Node *n) {
  return unsafe.count(n) == 0;
}

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
    if (c.getNode()->isModified())
      checkExploreNode(*c.getNode(), *sm.get(c).getNode(), ei);
  }

  // ei.m_explColor has the nodes explored
  for (auto kv : ei.m_explColor) {
    const Node *n = kv.first;
    Node *n_caller = sm.get(*n).getNode();
    if (isSafeNode(toUnsafe, n_caller)) {
      assert(!isUnboundedMem(n, n_caller));
      fromSafe.insert(n);
      toSafe.insert(n_caller);
    }
  }
}
} // namespace

using namespace llvm;

namespace seahorn {

InterMemPreProc::InterMemPreProc(seadsa::CompleteCallGraph &ccg,
                                 seadsa::ShadowMem &shadowDsa,
                                 expr::ExprFactory &efac)
    : m_ccg(ccg), m_shadowDsa(shadowDsa), m_efac(efac) {
  m_keyBase = mkTerm<std::string>("k", m_efac);
};

// -- computes the safe nodes per callsite of a module
bool InterMemPreProc::runOnModule(Module &M) {

  const GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  // -- needs to be done before because we want to know CI which nodes not to
  // copy according to a threshold
  for (const Function &f : M)
    if (ga.hasSummaryGraph(f))
      runOnFunction(&f);

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

        NodeSet &safeCallee = getSafeNodesCalleeCS(I); // creates it
        NodeSet &safeCaller = getSafeNodesCallerCS(I); // creates it
        computeSafeNodesSimulation(*(const_cast<Graph *>(&calleeG)), *f_callee,
                                   safeCallee, safeCaller, simMap);
      }
    }
  }

  return false;
}

NodeSet &InterMemPreProc::getSafeNodesCallerCS(const Instruction *I) {
  assert(dyn_cast<const CallInst>(I));
  return m_safen_cs_caller[I];
}

NodeSet &InterMemPreProc::getSafeNodesCalleeCS(const Instruction *I) {
  assert(dyn_cast<const CallInst>(I));
  return m_safen_cs_callee[I];
}

bool InterMemPreProc::isSafeNode(NodeSet &unsafe, const Node *n) {
  return !::isSafeNode(unsafe, n);
}

bool InterMemPreProc::isSafeNode(const NodeSet &unsafe, const Node *n) {
  return !::isSafeNode(unsafe, n);
}

bool InterMemPreProc::isSafeNodeFunc(const Node &n, const Function *f) {
  assert(m_safeNF.count(f) > 0);
  return isSafeNode(m_safeNF[f], &n);
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

  NodeSet &safeSAS = m_safeNF[F];
  NodeSet safeBU; // won't be used later
  computeSafeNodesSimulation(*(const_cast<Graph *>(&buG)), *F, safeBU, safeSAS,
                             simMap);

  // -- compute number of accesses to safe nodes
  RegionsMap &rm = m_frm[F];
  CellKeysMap &nkm = m_fnkm[F];

  for (const Argument &a : F->args())
    if (buG.hasCell(a))
      recProcessNode(buG.getCell(a), safeSAS, simMap, rm, nkm);

  for (auto &kv : buG.globals())
    recProcessNode(*kv.second, safeSAS, simMap, rm, nkm);

  if (buG.hasRetCell(*F))
    recProcessNode(buG.getRetCell(*F), safeSAS, simMap, rm, nkm);
}

unsigned InterMemPreProc::getNumCIAccessesCellSummary(const Cell &c,
                                                      const Function *f) {
  assert(m_smF.count(f) > 0);
  SimulationMapper &sm = m_smF[f];
  const Cell nCI = sm.get(c);

  return getNumAccesses(nCI, f);
}

ExprVector &InterMemPreProc::getKeysCell(const Cell &c, const Function *f) {
  assert(m_fnkm.count(f) > 0);
  return findKeysCellMap(m_fnkm[f], c);
}

ExprVector &InterMemPreProc::getKeysCellSummary(const Cell &c,
                                                const Function *f) {
  assert(m_smF.count(f) > 0);
  SimulationMapper &sm = m_smF[f];
  const Cell nCI = sm.get(c);

  return findKeysCellMap(m_fnkm[f], nCI);
}

// get from a map indexed by cell
template <typename ValueT>
ValueT &InterMemPreProc::findCellMap(
    DenseMap<std::pair<const Node *, unsigned>, ValueT> &map, const Cell &c) {

  auto it = map.find({c.getNode(), getOffset(c)});
  assert(it != map.end()); // there should be an entry for that always
  return it->second;
}

// get from a map indexed by cell
ExprVector &InterMemPreProc::findKeysCellMap(CellKeysMap &map, const Cell &c) {
  assert(map.count(c.getNode()) > 0 &&
         map[c.getNode()].count(getOffset(c)) > 0);
  return map[c.getNode()][getOffset(c)];
}

// -- processes the nodes in a graph to obtain the number accesses to different
// offsets
// -- cycles cannot happen because those nodes would be marked as unsafe
void InterMemPreProc::recProcessNode(const Cell &cFrom,
                                     const NodeSet &toSafeNodes,
                                     SimulationMapper &simMap, RegionsMap &rm,
                                     CellKeysMap &nkm) {

  const Node *nFrom = cFrom.getNode();
  if (nFrom->types().empty())
    return;

  const Cell &cTo = simMap.get(cFrom);
  if (!isSafeNode(toSafeNodes, cTo.getNode()))
    return;

  for (auto field : cFrom.getNode()->types()) {
    Cell cFromField(cFrom, field.getFirst());
    Cell cToField = simMap.get(cFromField);
    llvm::Optional<unsigned> opt_cellId = m_shadowDsa.getCellId(cToField);
    assert(opt_cellId.hasValue());

    auto &m = nkm[cToField.getNode()];
    ExprVector &ks = m[getOffset(cToField)];
    Expr key = finite_map::tagCell(
        bind::intConst(variant::variant(ks.size(), m_keyBase)),
        opt_cellId.getValue(), cToField.getRawOffset());
    ks.push_back(key);

    rm[{cToField.getNode(), getOffset(cToField)}]++;
  }

  if (nFrom->getLinks().empty())
    return;

  // follow the pointers of the node
  for (auto &links : nFrom->getLinks())
    recProcessNode(*links.second, toSafeNodes, simMap, rm, nkm);
}

ExprVector &InterMemPreProc::getKeysCellCS(const Cell &cCallee,
                                           const Instruction *i) {
  CellKeysMap &nkmcs = m_inkm[i];
  const Cell &cCaller = m_smCS[i].get(cCallee);
  return nkmcs[cCaller.getNode()][getOffset(cCaller)];
}

void InterMemPreProc::precomputeFiniteMapTypes(CallSite &CS) {

  GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  Function *f_callee = CS.getCalledFunction();
  if (!ga.hasSummaryGraph(*f_callee))
    return;

  const Instruction *i = CS.getInstruction();
  Graph &calleeG = ga.getSummaryGraph(*f_callee);
  SimulationMapper &sm = getSimulationCS(CS);
  NodeSet &safeCaller = getSafeNodesCallerCS(CS.getInstruction());

  // -- compute number of accesses to safe nodes
  RegionsMap &rm = m_irm[i];
  CellKeysMap &nkm = m_inkm[i];
  // -- they need to be cleaned because UfoOpSem is run twice
  rm.clear();
  nkm.clear();

  for (const Argument &a : f_callee->args()) {
    if (calleeG.hasCell(a))
      recProcessNode(calleeG.getCell(a), safeCaller, sm, rm, nkm);
  }

  for (auto &kv : calleeG.globals())
    recProcessNode(*kv.second, safeCaller, sm, rm, nkm);

  if (calleeG.hasRetCell(*f_callee)) {
    const Cell &c = calleeG.getRetCell(*f_callee);
    if (c.getNode()->isModified())
      recProcessNode(c, safeCaller, sm, rm, nkm);
  }
}

} // namespace seahorn
