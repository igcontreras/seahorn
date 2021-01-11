#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornModelConverter.hh"

#include "seahorn/UfoOpSem.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {

struct FMapExprsInfo {

  // -- set of vars of the expression being rewritten, it will
  // be updated if new vars are needed
  ExprSet &m_vars;
  // -- to cache the type of a map expr
  ExprMap &m_type;
  // -- to cache the keys definition of a map expression
  ExprMap &m_fmapDefk;
  // -- to cache the keys definition of a map expression
  ExprMap &m_fmapVarTransf;
  ExprFactory &m_efac;
  ZSimplifier<EZ3> &m_zsimp;

  // -- depth of an implication (incremented every time it is found in TD
  // visitor and decremented in the BU rewriter)
  // --- an optimization can be performed if the depth is 0 (no implications)
  int &m_dimpl;

  FMapExprsInfo(ExprSet &vars, ExprMap &types, ExprMap &fmapDefk,
                ExprMap &fmapVarTransf, int &dimpl, ExprFactory &efac,
                ZSimplifier<EZ3> &zsimp)
      : m_vars(vars), m_type(types), m_fmapDefk(fmapDefk),
        m_fmapVarTransf(fmapVarTransf), m_efac(efac), m_zsimp(zsimp),
        m_dimpl(dimpl) {}
};

class FiniteMapArgRewriter : public std::unary_function<Expr, Expr> {
  ExprSet &m_evars;
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;

public:
  FiniteMapArgRewriter(ExprSet &evars, const ExprMap &pred_decl_t,
                       ExprFactory &efac)
      : m_evars(evars), m_pred_decl_t(pred_decl_t), m_efac(efac){};

  Expr operator()(Expr exp);
};

// Top-down visitor to rewrite maps in arguments of predicate fapps
class FiniteMapArgsVisitor : public std::unary_function<Expr, VisitAction> {

private:
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;
  ExprSet &m_evars;
  int m_optEq = 0;
  std::shared_ptr<FiniteMapArgRewriter> m_rw;

public:
  FiniteMapArgsVisitor(ExprSet &evars, const ExprMap &pred_decl_t,
                       ExprFactory &efac)
      : m_evars(evars), m_pred_decl_t(pred_decl_t), m_efac(efac) {
    m_rw = std::make_shared<FiniteMapArgRewriter>(evars, m_pred_decl_t, efac);
  }

  VisitAction operator()(Expr exp);
};

// Rewrites a finite map operation to remove finite map terms. The arguments
// of the operation are assumed to be already rewritten (no finite map
// terms). The rewriter needs to be initialized for every clause
class FiniteMapBodyRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  FMapExprsInfo m_fmei;

public:
  FiniteMapBodyRewriter(ExprSet &evars, ExprMap &expr_type, ExprMap &fmapDef,
                        ExprMap &fmapVarDef, int &dimpl, ExprFactory &efac,
                        ZSimplifier<EZ3> &zsimp)
      : m_fmei(evars, expr_type, fmapDef, fmapVarDef, dimpl, efac, zsimp){};

  Expr operator()(Expr exp);
};

// Bottom-up visitor to rewrite maps in bodies
class FiniteMapBodyVisitor : public std::unary_function<Expr, VisitAction> {

private:
  ExprMap m_types;
  ExprMap m_fmapDef;
  ExprMap m_fmapVarDef;
  int m_dimpl = 0;
  std::shared_ptr<FiniteMapBodyRewriter> m_rw;

public:
  FiniteMapBodyVisitor(ExprSet &evars, ExprFactory &efac,
                       ZSimplifier<EZ3> &zsimp) {
    m_rw = std::make_shared<FiniteMapBodyRewriter>(
        evars, m_types, m_fmapDef, m_fmapVarDef, m_dimpl, efac, zsimp);
  }

  VisitAction operator()(Expr exp);

private:
  bool isRewriteFiniteMapOp(Expr e);
};

} // namespace seahorn

// shared with FMapOpSemTransf
namespace seahorn {
namespace fmap_transf {

Expr mkEmptyConstMap(Expr mapConst, FMapExprsInfo &fmei);
Expr replaceDefKeys(Expr defmap, Expr keys);
template <typename Range>
Expr replaceDefValues(Expr defmap, const Range &values);
Expr mkGetDefCore(Expr defmap, Expr key);
Expr mkGetCore(Expr fm, Expr key);
Expr mkSetDefCore(Expr defmap, Expr key, Expr v);
Expr mkSetCore(Expr fm, Expr key, Expr v);
Expr mkIteDefCore(Expr cond, Expr fm1, Expr fm2);
Expr mkIteCore(Expr cond, Expr fm1, Expr fm2);
Expr mkSameKeysCore(Expr e);
Expr mkInlineDefs(Expr def, ExprMap &defmap);
void insertVarsDef(Expr defmap, ExprSet &vars);
Expr mkExpandCore(Expr fm);

} // namespace fmap_transf
} // namespace seahorn
