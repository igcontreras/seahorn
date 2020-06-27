#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {
// ----------------------------------------------------------------------
//  FiniteMapArgsVisitor
// ----------------------------------------------------------------------

// -- creates a constant with the name get(map,k)
// also used in FinteMapBodyVisitor
static Expr mkVarGet(Expr mapConst, Expr k, Expr vTy) {
  assert(bind::isFiniteMapConst(mapConst));
  return bind::mkConst(variant::variant(0, finite_map::get(mapConst, k)), vTy);
}

// \brief rewrites a map into separate scalar variables. New variables are added
// to `new_vars`, new unifications are added to `extra_unifs`
void mkVarsMap(Expr map, const ExprVector &keys, Expr vTy, ExprVector &new_vars,
               ExprVector &extra_unifs, ExprSet &evars) {

  Expr v, v_get;
  ExprVector map_values(keys.size());
  auto val_it = map_values.begin();

  for (auto k : keys) {
    v = mkVarGet(map, k, vTy);
    evars.insert(v);
    new_vars.push_back(k);
    new_vars.push_back(v);
    *val_it++ = v;
  }
  extra_unifs.push_back(
      mk<EQ>(map, finite_map::constFiniteMap(keys, map_values)));
}

// \brief rewrites the map arguments of fapps into separate scalar variables
static Expr mkFappArgsCore(Expr fapp, Expr newFdecl, ExprVector &extraUnifs,
                           ExprSet &evars, ExprFactory &efac) {

  assert(isOpX<FAPP>(fapp));

  Expr fdecl = bind::name(fapp);
  assert(bind::isFdecl(fdecl));
  Expr fname = bind::fname(fdecl);

  ExprVector newArgs;

  auto arg_it = ++(fapp->args_begin()), t_it = ++(fdecl->args_begin());
  if (arg_it == fapp->args_end()) // no args
    return fapp;

  int arg_count = 0;
  for (; arg_it != fapp->args_end(); arg_it++, arg_count++, t_it++) {
    Expr arg = *arg_it;
    Expr argTy = *t_it;

    if (isOpX<FINITE_MAP_TY>(argTy)) {
      Expr map_var_name;
      if (bind::isFiniteMapConst(arg)) {
        map_var_name = arg;
      } else {
        map_var_name = bind::mkConst(variant::variant(arg_count, fname), argTy);
        // if there is no name, we create a variant with the name of the
        // function, make new variable (same as normalization)
      }
      Expr ksTy = finite_map::keys(argTy);
      ExprVector keys(ksTy->args_begin(), ksTy->args_end());
      Expr lmdKeys = finite_map::mkKeys(keys, efac);

      mkVarsMap(map_var_name, keys, finite_map::valTy(argTy), newArgs,
                extraUnifs, evars);
      // new arguments are added to `newArgs` in the function above
    } else {
      newArgs.push_back(arg);
    }
  }
  return bind::fapp(newFdecl, newArgs); // building the new fapp
}

// rewrite bottom_up
VisitAction FiniteMapArgsVisitor::operator()(Expr exp) {

  if (isOpX<IMPL>(exp)) { // rule (or implication inside rule?)
    Expr head = exp->right();
    Expr body = exp->left();
    Expr fdecl = *head->args_begin();

    if (m_pred_decl_t.count(fdecl) == 0)
      return VisitAction::changeDoKids(exp);

    Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
    ExprVector newUnifs;
    Expr newFapp = mkFappArgsCore(head, newPredDecl, newUnifs, m_evars, m_efac);
    Expr newBody =
        newUnifs.empty() ? body : mk<AND>(mknary<AND>(newUnifs), body);

    Expr newExp = boolop::limp(newBody, newFapp);
    // efficiency: are we traversing the newly created unifs?
    return VisitAction::changeDoKids(newExp);

  } else if (isOpX<FAPP>(exp) &&
             !bind::IsConst()(exp)) { // faster to check arity >= 2?
    Expr fdecl = *exp->args_begin();
    if (m_pred_decl_t.count(fdecl) > 0) { // needs to be transformed
      ExprVector newUnifs;
      Expr newPredDecl = m_pred_decl_t.find(fdecl)->second;
      Expr newExp = mkFappArgsCore(exp, newPredDecl, newUnifs, m_evars, m_efac);
      if (!newUnifs.empty())
        newExp = mk<AND>(mknary<AND>(newUnifs), newExp);
      LOG("fmap_transf", errs() << *newExp << "\n";);
      return VisitAction::changeDoKids(newExp);
    }
  } else if (isOpX<FDECL>(exp)) {
    return VisitAction::skipKids();
  }
  return VisitAction::doKids();
}

} // namespace seahorn

namespace {

using namespace seahorn;

// ----------------------------------------------------------------------
//  FiniteMapBodyVisitor
// ----------------------------------------------------------------------

// -- rewrites a map term (if not already) to be used in a map primitive
static Expr mkFMapPrimitiveArgCore(Expr map, FMapExprsInfo &fmei) {

  Expr lmdKeys = fmei.m_typeLmd[map];
  Expr fmTy = fmei.m_type[map];
  Expr vTy = finite_map::valTy(fmTy);
  Expr ksTy = finite_map::keys(fmTy);

  if (bind::isFiniteMapConst(map)) {
    // the map is a variable, it is assumed to be defined or expanded before.
    if (fmei.m_fmapVarDef.count(map) == 0) {
      errs() << "unexpected map variable, no previous definition found\n";
    }
    map = fmei.m_fmapVarDef[map];
  }
  // ExprVector keys(ksTy->args_begin(), ksTy->args_end());
  // ExprVector values;
  // for (auto k : keys) {
  //   Expr v = mkVarGet(map, k, vTy);
  //   fmei.m_vars.insert(v);
  //   values.push_back(v);
  // }
  // return finite_map::mkInitializedMap(keys, vTy, values, lmdKeys,
  //                                     fmei.m_efac);
  if (isOpX<CONST_FINITE_MAP>(map)) { // transform map definition to lambda
    // the map is a map definition
    Expr defk = map->left();
    assert(isOpX<CONST_FINITE_MAP_KEYS>(defk));
    Expr res, valuesE = map->right();
    if (isOpX<FINITE_MAP_VAL_DEFAULT>(valuesE)) { // non init values
      return finite_map::mkEmptyMap(valuesE->left());
    } else {
      assert(isOpX<CONST_FINITE_MAP_VALUES>(valuesE)); // initialized values
      ExprVector values(valuesE->args_begin(), valuesE->args_end());
      ExprVector keys(defk->args_begin(), defk->args_end());
      return finite_map::mkInitializedMap(keys, vTy, values, lmdKeys,
                                          fmei.m_efac);
    }
  } else // already transformed map: 0 or ite expr
    return map;
}

static Expr getValueAtDef(Expr values, Expr lks, Expr k, unsigned pos) {
  if (isOpX<CONST_FINITE_MAP>(values)) {
    values = values->right();
    if (isOpX<FINITE_MAP_VAL_DEFAULT>(values))
      return values;
    else if (isOpX<CONST_FINITE_MAP_VALUES>(values))
      return values->arg(pos);
  } else // already an expanded map term
    return finite_map::mkGetVal(values, lks, k);
}

// \brief Specialized Eq if `map1` and `map2` are map definitions that
// initialize all the values.
// static Expr mkEqInitDefs(Expr map1, Expr map2) {

//   ExprVector conj;

//   for (auto k_it1 = map1->left()->args_begin(),
//             auto k_it2 = map2->left()->args_begin();
//        k_it1 != args_end(); k_it1++, k_it2++)
//     conj.push_back(mk<EQ>(*k_it1,*k_it2));

//   for (auto v_it1 = map1->left()->args_begin(),
//             auto v_it2 = map2->left()->args_begin();
//        v_it1 != args_end(); v_it1++, v_it2++)
//     conj.push_back(mk<EQ>(*v_it1, *v_it2));
// }

// \brief `ml` contains the same values as `mr`. Both maps are assumed to
// have the same keys `keys` but not necessarily in the same order, that is
// why `ksl` and `ksr` are needed.
static Expr mkEqCore(Expr ml, Expr lksl, Expr mr, Expr lksr,
                     const ExprVector &keys, Expr vTy, FMapExprsInfo &fmei) {

  ExprVector conj;

  bool is_Defml = false, is_Defmr = false;
  Expr v_ml, v_mr;

  if (bind::isFiniteMapConst(mr)) {
    if (fmei.m_fmapVarDef.count(mr) == 0)
      errs() << "Definition not found for " << *mr << "\n";
    mr = fmei.m_fmapVarDef[mr]; // get definition or already transformed
                                // expression
  }

  if (bind::isFiniteMapConst(ml)) {
    if (fmei.m_fmapVarDef.count(ml) == 0) { // first appearance
      // store map definition and transform to true
      fmei.m_fmapVarDef[ml] = mr;
      return mk<TRUE>(fmei.m_efac);
    } else
      ml = fmei.m_fmapVarDef[ml];
  }

  assert(ml);
  assert(mr);

  // if we have 2 definitions, we can skip the ites
  // if (finite_map::isInitializedFiniteMap(ml) &&
  //     finite_map::isInitializedFiniteMap(mr))
  //   return mkEqInitDefs(ml, mr);

  // unify keys?
  for (int i = 0; i < keys.size(); i++) {
    Expr k = keys.at(i);
    v_ml = getValueAtDef(ml, lksl, k, i);
    v_mr = getValueAtDef(mr, lksr, k, i);
    conj.push_back(mk<EQ>(v_ml, v_mr));
  }
  return mknary<AND>(conj);
}

// -- processes a fmap definition, building the type and the lmdkeys
// term is of the form:
//
// defmap(defk(keys), fmap-default(valTy)))
//      or
// defmap(defk(keys), defv(values)))
static Expr mkDefFMapCore(Expr map, FMapExprsInfo &fmei) {

  Expr defk = map->left();
  assert(isOpX<CONST_FINITE_MAP_KEYS>(defk));

  Expr vTy, valuesE = map->right();
  if (isOpX<FINITE_MAP_VAL_DEFAULT>(valuesE)) { // non init values
    vTy = bind::typeOf(valuesE->left());        // type of the values
  } else {
    assert(isOpX<CONST_FINITE_MAP_VALUES>(valuesE)); // initialized values
    vTy = bind::typeOf(*valuesE->args_begin());
    // can values be of unknown type?
  }

  ExprVector keys(defk->args_begin(), defk->args_end());
  Expr fmTy = sort::finiteMapTy(vTy, keys);
  fmei.m_type[map] = fmTy;
  fmei.m_typeLmd[fmTy] = finite_map::mkKeys(keys, fmei.m_efac);

  return map;
}

// -- rewrites a map get primitive
static Expr mkGetCore(Expr map, Expr key, FMapExprsInfo &fmei) {

  Expr fmTy = fmei.m_type[map];
  Expr lmdKeys = fmei.m_typeLmd[fmTy];
  assert(lmdKeys);

  return finite_map::mkGetVal(mkFMapPrimitiveArgCore(map, fmei), lmdKeys,
                                key);
}

// -- rewrites a map set primitive
static Expr mkSetCore(Expr map, Expr key, Expr value, FMapExprsInfo &fmei) {

  Expr fmTy = fmei.m_type[map];
  Expr lmdKeys = fmei.m_typeLmd[fmTy];
  assert(lmdKeys);

  Expr res = finite_map::mkSetVal(mkFMapPrimitiveArgCore(map, fmei), lmdKeys,
                                  key, value, fmei.m_efac);

  fmei.m_type[res] = fmTy;
  return res;
}

// -- processes a fmap constant, caches its type and its lambda term for the
// keys
static Expr mkFMapConstCore(Expr map_var, FMapExprsInfo &fmei) {

  if (fmei.m_type.count(map_var) == 0) {
    Expr fmTy = bind::rangeTy(bind::fname(map_var));
    Expr ksTy = finite_map::keys(fmTy);
    ExprVector keys(ksTy->args_begin(), ksTy->args_end());
    fmei.m_typeLmd[fmTy] = finite_map::mkKeys(keys, fmei.m_efac);
    fmei.m_type[map_var] = fmTy;
  }
  return map_var;
}
} // namespace

namespace seahorn {

Expr FiniteMapRewriter::operator()(Expr exp) {

  Expr res;

  if (isOpX<CONST_FINITE_MAP>(exp)) {
    res = mkDefFMapCore(exp, m_fmei);
  } else if (isOpX<GET>(exp)) {
    res = mkGetCore(exp->left(), exp->right(), m_fmei);
  } else if (isOpX<SET>(exp)) {
    res = mkSetCore(exp->arg(0), exp->arg(1), exp->arg(2), m_fmei);
  } else if (bind::isFiniteMapConst(exp)) {
    res = mkFMapConstCore(exp, m_fmei);
  } else if (isOpX<EQ>(exp)) {

    errs() << "processing: " << *exp << "\n";

    Expr fml = exp->left();
    Expr fmr = exp->right();

    Expr fmTyl = m_fmei.m_type[fml];
    Expr fmTyr = m_fmei.m_type[fmr];

    Expr lkeysl = m_fmei.m_typeLmd[fmTyl];
    Expr lkeysr = m_fmei.m_typeLmd[fmTyr];

    Expr ksTyl = finite_map::keys(fmTyl);
    Expr vTy = finite_map::valTy(fmTyl);
    ExprVector keys(ksTyl->args_begin(), ksTyl->args_end());
    res = mkEqCore(fml, lkeysl, fmr, lkeysr, keys, vTy, m_fmei);
  } else { // do nothing
    assert(false && "Unexpected map expression");
    return exp;
  }
  LOG("fmap_transf",
      errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n";);
  return res;
}

static bool returnsFiniteMap(Expr e) {
  return isOpX<CONST_FINITE_MAP>(e) || isOpX<SET>(e) ||
         bind::isFiniteMapConst(e); // this check is done before rewriting
}

VisitAction FiniteMapBodyVisitor::operator()(Expr exp) {
  LOG("fmap_transf", errs() << "Creating visit action for: " << *exp << "\n";);

  if (isVisitFiniteMapOp(exp)) {
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (bind::isFiniteMapConst(exp)) {
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (isOpX<EQ>(exp)) {
    if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right()))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (bind::IsConst()(exp) || bind::isFdecl(exp)) {
    return VisitAction::skipKids();
  }
  // The step doesn't need to be rewritten but the kids do
  return VisitAction::doKids();
}

bool FiniteMapBodyVisitor::isVisitFiniteMapOp(Expr e) {
  return isOpX<CONST_FINITE_MAP>(e) || isOpX<GET>(e) || isOpX<SET>(e);
  // we are not visiting CONST_FINITE_MAP_KEYS and DEFAULT
}

} // namespace seahorn
;
