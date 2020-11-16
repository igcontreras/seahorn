#pragma once
#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include "seahorn/VCGen.hh"

#include "seadsa/ShadowMem.hh"
#include "seahorn/InterMemPreProc.hh"

namespace llvm {
class GetElementPtrInst;
}

namespace seahorn {

using ValueVector = std::vector<llvm::Value *>;

struct CallSiteInfo {

  CallSiteInfo(CallSite &cs, ExprVector &fparams, ValueVector &modValues)
    : m_cs(cs), m_fparams(fparams), m_modValues(modValues) {}

  CallSite &m_cs;
  ExprVector &m_fparams;
  ValueVector &m_modValues;
};

/**
 * Operational semantics for LLVM based on one from UFO
 * This has evolved significantly from the original UFO semantics.
 *
 * All numeric types are represented by arbitrary precision integers
 * Memory is represented by arrays indexed by arbitrary precision integers
 *
 * This semantics is not very accurate. Should not be used for
 * low-level bit-precise reasoning.
 */
class UfoOpSem : public LegacyOperationalSemantics {
  Pass &m_pass;
  TrackLevel m_trackLvl;

public:
  using FunctionPtrSet = SmallPtrSet<const Function *, 8>;

private:
  FunctionPtrSet m_abs_funcs;
  const DataLayout *m_td;
  const CanFail *m_canFail;

public:
  UfoOpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
           TrackLevel trackLvl = MEM, FunctionPtrSet abs_fns = FunctionPtrSet())
      : LegacyOperationalSemantics(efac), m_pass(pass), m_trackLvl(trackLvl),
        m_abs_funcs(abs_fns), m_td(&dl) {
    m_canFail = pass.getAnalysisIfAvailable<CanFail>();
  }
  UfoOpSem(const UfoOpSem &o)
      : LegacyOperationalSemantics(o), m_pass(o.m_pass),
        m_trackLvl(o.m_trackLvl), m_abs_funcs(o.m_abs_funcs), m_td(o.m_td),
        m_canFail(o.m_canFail) {}

  Expr errorFlag(const BasicBlock &BB) override;

  Expr memStart(unsigned id) override;
  Expr memEnd(unsigned id) override;

  void exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
            Expr act) override;

  void execPhi(SymStore &s, const BasicBlock &bb, const BasicBlock &from,
               ExprVector &side, Expr act) override;

  void execEdg(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
               ExprVector &side) override;

  void execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
              ExprVector &side, Expr act) override;

  Expr symb(const Value &v) override;
  const Value &conc(Expr v) const override;
  bool isTracked(const Value &v) const override;
  Expr lookup(SymStore &s, const Value &v) override;
  bool isAbstracted(const Function &fn) override;
  Expr ptrArith(SymStore &s, llvm::GetElementPtrInst &gep);
  unsigned storageSize(const llvm::Type *t);
  unsigned fieldOff(const StructType *t, unsigned field);

  virtual void execCallSite(CallSiteInfo &csi, ExprVector &side, SymStore &s);
  virtual void execMemInit(CallSite &CS, Expr mem, ExprVector &side,
                           SymStore &s){}; // do nothing
};

enum class MemOpt { IN, OUT };

// map to store the correspondence between node ids and their correspondent
// expression
using CellExprMap = DenseMap<std::pair<const seadsa::Node *, unsigned>, Expr>;

class MemUfoOpSem : public UfoOpSem {
protected:
  std::shared_ptr<InterMemPreProc> m_preproc = nullptr;
  seadsa::ShadowMem *m_shadowDsa = nullptr;

  // original arrays names of a cell
  CellExprMap m_orig_array_in;
  CellExprMap m_orig_array_out;
  // current number to generate intermediate array names for the copies
  int m_copy_count = 0;

private:
  // array names to replace for a cell
  CellExprMap m_rep_in;
  CellExprMap m_rep_out;

  // for the intermediate arrays name for copies for a cell
  CellExprMap m_tmprep_in;
  // this creates non-deterministic vcgen (iterating over it to replace the new
  // parameter names)
  CellExprMap m_tmprep_out;

public:
  MemUfoOpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
              std::shared_ptr<InterMemPreProc> preproc,
              TrackLevel trackLvl = MEM,
              FunctionPtrSet abs_fns = FunctionPtrSet(),
              seadsa::ShadowMem *dsa = NULL)
      : UfoOpSem(efac, pass, dl, trackLvl, abs_fns), m_shadowDsa(dsa),
        m_preproc(preproc) {}

  void execCallSite(CallSiteInfo &CS, ExprVector &side, SymStore &s) override;

protected:
  unsigned getOffset(const Cell &c);

  // creates the variant of an expression using m_copy_count
  Expr arrayVariant(Expr origE);

  // generates the literals to copy of an argument
  void recVCGenMem(const seadsa::Cell &c_callee, Expr ptr,
                   const NodeSet &safeNodesCe, const NodeSet &safeNodesCr,
                   seadsa::SimulationMapper &simMap, ExprVector &side);

  // Internal methods to handle array expressions and cells.
  void addCIMemSymbol(CallInst *CI, Expr A, MemOpt ao);
  virtual void addMemSymbol(const seadsa::Cell &c, Expr A, MemOpt ao);
  Expr getOrigMemSymbol(const seadsa::Cell &c, MemOpt ao);
  bool hasOrigMemSymbol(const seadsa::Cell &c, MemOpt ao);
  // creates a new array symbol for array origE if it was not created already
  Expr getFreshMemSymbol(const seadsa::Cell &c, MemOpt ao);

  // creates a new array symbol for intermediate copies of an original array
  // origE. currE is the current intermediate name and newE is the new value to
  // copy
  void newTmpMemSymbol(const seadsa::Cell &c, Expr &currE, Expr &newE,
                       MemOpt ao);

  // processes the shadow mem instructions prior to a callsite to obtain the
  // expressions that correspond to each of the cells involved.
  virtual void processShadowMemsCallSite(CallSiteInfo &csi);
  bool hasExprCell(const CellExprMap &nim, const Cell &c);
  Expr getExprCell(const CellExprMap &nim, const Cell &c);
  Expr getExprCell(const CellExprMap &nim, const Node *n, unsigned offset);

  // \brief true if `c` is encoded with a scalar variable
  bool isMemScalar(const Cell &c);
  inline std::pair<const Node *, unsigned> cellToPair(const Cell &c) {
    return m_preproc->cellToPair(c);
  }

private:
  CellExprMap &getOrigMap(MemOpt ao) {
    return ao == MemOpt::IN ? m_orig_array_in : m_orig_array_out;
  }
};

struct InterMemStats {
  // !brief counters for encoding with InterProcMem flag
  unsigned m_n_params = 0;
  unsigned m_n_callsites = 0;
  unsigned m_n_gv = 0;

  unsigned m_fields_copied = 0;
  unsigned m_params_copied = 0;
  unsigned m_gv_copied = 0;
  unsigned m_callsites_copied = 0;

  unsigned m_node_array = 0;
  unsigned m_node_ocollapsed = 0;
  unsigned m_node_safe = 0;

  void print();

  void copyTo(InterMemStats &ims);
};

class FMapUfoOpSem : public MemUfoOpSem {

public:
  FMapUfoOpSem(expr::ExprFactory &efac, Pass &pass, const DataLayout &dl,
               std::shared_ptr<InterMemPreProc> preproc,
               TrackLevel trackLvl = MEM,
               FunctionPtrSet abs_fns = FunctionPtrSet(), ShadowMem *dsa = NULL)
      : MemUfoOpSem(efac, pass, dl, preproc, trackLvl, abs_fns, dsa)
  {
    m_keyBase = mkTerm<std::string>("k", efac);
    m_fmDefault = mkTerm<expr::mpz_class>(0UL, m_efac);
  }

  Expr symb(const Value &v) override;
  void execCallSite(CallSiteInfo &CS, ExprVector &side, SymStore &s) override;

  void execMemInit(CallSite &CS, Expr mem, ExprVector &side,
                   SymStore &s) override;

protected:
  void processShadowMemsCallSite(CallSiteInfo &csi) override;
  void addMemSymbol(const seadsa::Cell &c, Expr A, MemOpt ao) override;

private:
  // FMOpSemTransf m_fmt;

  // hides how the memory is split
  using FMapExprMap = std::map<Expr, ExprVector>;
  // -- Expr needs to be replaced by a map with the keys in this std::map
  FMapExprMap m_fmKeys;
  // -- Expr needs to be replaced by a map with the values in this std::map
  FMapExprMap m_fmValues;

  // -- Additional store operations for the out memories (copy back)
  ExprMap m_fmOut;
  // -- Additional store operations for the parameters to be replaced
  // ExprMap m_replace;

  // -- to replace in terms of cells in the SAS graph of the callee
  CellExprMap m_cellReplaceIn;
  CellExprMap m_cellReplaceOut;

  using CellExprVectorMap =
      std::map<std::pair<const seadsa::Node *, unsigned>, ExprVector>;
  CellExprVectorMap m_cellKeysIn;
  CellExprVectorMap m_cellKeysOut;
  CellExprVectorMap m_cellValuesIn;
  CellExprVectorMap m_cellValuesOut;

  // -- store the cell that corresponds to an expression
  using ExprCellMap = std::map<Expr, std::pair<const seadsa::Node *, unsigned>>;
  // TODO: unordered_map?
  ExprCellMap m_exprCell;

  // -- constant base for keys
  Expr m_keyBase;
  // -- default value for uninitialized values of maps
  Expr m_fmDefault;

  Instruction *m_csInst; // callsite that we are processing

  using CellKeysMap =
      DenseMap<std::pair<const seadsa::Node *, unsigned>, ExprVector>;
  using FunctionCellKeysMap = std::map<const Function *, CellKeysMap>;
  FunctionCellKeysMap m_fCellKeysM;

  using FunctionCellExprMap = std::map<const Function *, CellExprMap>;
  FunctionCellExprMap m_fInitSymNodes;

  void recVCGenMem(const Cell &c_callee, Expr ptrInt, Expr ptrOut,
                   const NodeSet &safeNodesCe, const NodeSet &safeNodesCr,
                   SimulationMapper &simMap, const Function &F);

  Expr fmVariant(Expr e, const Cell&c, const ExprVector &keys);
  void addKeyValCell(const Cell &cCr, const Cell &cCe, Expr basePtr,
                     unsigned offset);
  void storeVal(const Cell &cCr, const Cell &cSAS, Expr readFrom, Expr basePtr,
                unsigned offset);

  // -- creates an ExprVector if not initialized already
  ExprVector &getCellKeys(std::pair<const seadsa::Node *, unsigned> &cp,
                          MemOpt ao) {
    auto &map = (ao == MemOpt::IN) ? m_cellKeysIn : m_cellKeysOut;
    return map[cp];
  }

  ExprVector &getCellKeys(const Cell &c, MemOpt ao) {
    auto cp = cellToPair(c);
    return getCellKeys(cp, ao);
  }

  ExprVector &getCellValues(std::pair<const seadsa::Node *, unsigned> &cp,
                            MemOpt ao) {
    auto &map = (ao == MemOpt::IN) ? m_cellValuesIn : m_cellValuesOut;
    return map[cp];
  }

  ExprVector &getCellValues(const Cell &c, MemOpt ao) {
    auto cp = cellToPair(c);
    return getCellValues(cp, ao);
  }

  Expr memObtainValue(Expr mem, Expr offset);
  Expr memSetValue(Expr mem, Expr offset, Expr v);
  Expr getFreshMapSymbol(const Cell &cCr, const Cell &cCe, const Function &F,
                         MemOpt ao);
  void recCollectReachableKeys(const Cell &c, const Function &F, Expr basePtr,
                               const NodeSet &safeNsBU, const NodeSet &safeNs,
                               SimulationMapper &sm, CellKeysMap &nkm,
                               CellExprMap &nim);

  void recInlineDefs(const Expr map, const Expr def, ExprMap &defs,
                     ExprSet &added, SymStore &s);
  void storeSymInitInstruction(Instruction *I, CellExprMap &nim, Expr memE);

  CellKeysMap &getCellKeysFunction(const Function &F) {
    return m_fCellKeysM[&F]; // creates it if it doesn't exist
  }

  // bool hasNodeSymFunction(const Function &F) {
  //   return m_fInitSymNodes.count(&F) > 0;
  // }
  CellExprMap &getNodeSymFunction(const Function &F) {
    return m_fInitSymNodes[&F]; // creates it if it
                                // doesn't exist
  }
  Cell getCellValue(const Value *v);
};

} // namespace seahorn
