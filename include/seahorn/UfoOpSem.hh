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

struct CallSiteInfo {

  CallSiteInfo(CallSite &cs, ExprVector &fparams)
      : m_cs(cs), m_fparams(fparams) {}

  CallSite &m_cs;
  ExprVector &m_fparams;
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

class MemUfoOpSem : public UfoOpSem {
protected:
  std::shared_ptr<InterMemPreProc> m_preproc = nullptr;
  seadsa::ShadowMem *m_shadowDsa = nullptr;

  // map to store the correspondence between node ids and their correspondent
  // expression
  using NodeIdMap = DenseMap<std::pair<const seadsa::Node *, unsigned>, Expr>;
  // original arrays names of a cell
  NodeIdMap m_orig_array_in;
  NodeIdMap m_orig_array_out;
  // current number to generate intermediate array names for the copies
  int m_copy_count = 0;

private:
  // array names to replace for a cell
  NodeIdMap m_rep_in;
  NodeIdMap m_rep_out;

  // for the intermediate arrays name for copies for a cell
  NodeIdMap m_tmprep_in;
  // this creates non-deterministic vcgen (iterating over it to replace the new
  // parameter names)
  NodeIdMap m_tmprep_out;

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
  void VCgenArg(const seadsa::Cell &c_arg_callee, Expr base_ptr,
                NodeSet &unsafeCallerNodes, seadsa::SimulationMapper &sm,
                ExprVector &side);
  void recVCGenMem(const seadsa::Cell &c_callee, Expr ptr, NodeSet &unsafeNodes,
                   seadsa::SimulationMapper &simMap, NodeSet &explored,
                   ExprVector &side);

  // Internal methods to handle array expressions and cells.
  void addCIArraySymbol(CallInst *CI, Expr A, MemOpt ao);
  virtual void addArraySymbol(const seadsa::Cell &c, Expr A, MemOpt ao);
  Expr getOrigMemSymbol(const seadsa::Cell &c, MemOpt ao);
  bool hasOrigArraySymbol(const seadsa::Cell &c, MemOpt ao);
  // creates a new array symbol for array origE if it was not created already
  Expr getFreshArraySymbol(const seadsa::Cell &c, MemOpt ao);

  // creates a new array symbol for intermediate copies of an original array
  // origE. currE is the current intermediate name and newE is the new value to
  // copy
  void newTmpArraySymbol(const seadsa::Cell &c, Expr &currE, Expr &newE,
                         MemOpt ao);

  // processes the shadow mem instructions prior to a callsite to obtain the
  // expressions that correspond to each of the cells involved.
  virtual void processShadowMemsCallSite(CallSiteInfo &csi);

  // \brief true if `c` is encoded with a scalar variable
  bool isMemScalar(const Cell &c);

private:
  NodeIdMap &getOrigMap(MemOpt ao) {
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
  unsigned m_node_unsafe = 0;

  void print();

  void copyTo(InterMemStats &ims);
};

class FMapUfoOpSem : public MemUfoOpSem {

  // hides how the memory is split
  using FMapExprMap = std::map<Expr, ExprVector>;
  // -- Expr needs to be replaced by a map with the keys in this std::map
  FMapExprMap m_fmKeys;
  // -- Expr needs to be replaced by a map with the values in this std::map
  FMapExprMap m_fmValues;

  // -- Additional store operations for the out memories (copy back)
  ExprMap m_fmOut;
  // -- Additional store operations for the parameters to be replaced
  ExprMap m_replace;

  // -- store the cell that corresponds to an expression
  using ExprCellMap = std::map<Expr, std::pair<const seadsa::Node *, unsigned>>;
  ExprCellMap m_exprCell;

  // -- constant base for keys
  Expr m_keyBase;
  // -- default value for uninitialized values of maps
  Expr m_fmapDefault;

public:
  FMapUfoOpSem(expr::ExprFactory &efac, Pass &pass, const DataLayout &dl,
               std::shared_ptr<InterMemPreProc> preproc,
               TrackLevel trackLvl = MEM,
               FunctionPtrSet abs_fns = FunctionPtrSet(), ShadowMem *dsa = NULL)
      : MemUfoOpSem(efac, pass, dl, preproc, trackLvl, abs_fns, dsa) {
    m_keyBase = mkTerm<std::string>("k", efac);
    m_fmapDefault = mkTerm<expr::mpz_class>(0UL, m_efac);
  }

  Expr symb(const Value &v) override;
  void execCallSite(CallSiteInfo &CS, ExprVector &side, SymStore &s) override;

  void execMemInit(CallSite &CS, Expr mem, ExprVector &side,
                   SymStore &s) override;

protected:
  void processShadowMemsCallSite(CallSiteInfo &csi) override;
  void addArraySymbol(const seadsa::Cell &c, Expr A, MemOpt ao) override;

private:
  void VCgenArg(const Cell &cArgCallee, Expr basePtr,
                NodeSet &unsafeCallerNodes, SimulationMapper &sm,
                const Function &F);

  void recVCGenMem(const Cell &c_callee, Expr ptrInt, Expr ptrOut,
                   NodeSet &unsafeNodes, SimulationMapper &simMap,
                   NodeSet &explored, const Function &F);

  Expr fmVariant(Expr e, const ExprVector &keys);
  void addKeyVal(Cell c, Expr basePtr, Expr offset, MemOpt ao);
  void storeVal(Cell c, Expr readFrom, Expr basePtr, Expr offset);
  
  // creates an ExprVector if not initialized already
  ExprVector &getExprKeys(Expr e) { return m_fmKeys[e]; }
  bool hasExprKeys(Expr e) { return m_fmKeys.count(e) > 0; }
  ExprVector &getExprValues(Expr e) { return m_fmValues[e]; }
  Expr memObtainValue(Expr mem, Expr offset);
  Expr memSetValue(Expr mem, Expr offset, Expr v);
  Expr getFreshMapSymbol(const Cell &cCaller, const Cell &cCallee, MemOpt ao,
                         const Function &F);
};

} // namespace seahorn
