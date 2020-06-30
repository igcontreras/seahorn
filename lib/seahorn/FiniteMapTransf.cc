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
    evars.insert(k);
    new_vars.push_back(k);
    new_vars.push_back(v);
    *val_it++ = v;
  }
  extra_unifs.push_back(
                        mk<EQ>(map, finite_map::constFiniteMap(keys, map_values.back(), map_values)));
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
        evars.insert(map_var_name);
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

  errs() << "-- mkFMapPrimitiveArgCore arg: " << *map << "\n";

  if (bind::isFiniteMapConst(map)) {
    // if the map is a variable, it is assumed to be defined or expanded before.
    assert(!(fmei.m_fmapVarTransf.count(map) == 0) && " no previous fmap definition found");
    map = fmei.m_fmapVarTransf[map];
  }

  if (isOpX<CONST_FINITE_MAP>(map)) { // transform map definition to lambda
    // the map is a map definition
    Expr defk = finite_map::fmapDefKeys(map);
    if (!finite_map::isInitializedFiniteMap(map)) { // non init values
      return finite_map::mkEmptyMap(finite_map::fmapDefDefault(map)->left());
    } else {
      Expr valuesE = finite_map::fmapDefValues(map);
      ExprVector values(valuesE->args_begin(), valuesE->args_end());
      ExprVector keys(defk->args_begin(), defk->args_end());
      return finite_map::mkInitializedMap(keys, vTy, values, lmdKeys,
                                          fmei.m_efac);
    }
  } else // already transformed map: default-map or ite expr
    return map;
}

static Expr getValueAtDef(Expr map, Expr lks, Expr k, unsigned pos) {
  if (isOpX<CONST_FINITE_MAP>(map)) {
    if (finite_map::isInitializedFiniteMap(map))
      return finite_map::fmapDefValues(map)->arg(pos);
    else
      return finite_map::fmapDefDefault(map)->left();
  } else // already an expanded map term
    return finite_map::mkGetVal(map, lks, k);
}

// \brief `ml` contains the same values as `mr`.
static Expr mkEqCore(Expr ml, Expr mr, FMapExprsInfo &fmei) {

  errs() << "-- mkEqCore " << *ml << " = " << *mr << "\n";
  Expr mrDefk = nullptr, mlDefk = nullptr;

  if (!isOpX<CONST_FINITE_MAP>(
          mr)) { // if it is not a definition, we get its key definition
    mrDefk = fmei.m_fmapDefk[mr];
    if (bind::isFiniteMapConst(
                               mr)) {// if variable, use as map expression its expansion
      if (fmei.m_fmapVarTransf.count(mr) == 0) {
        errs() << "Expansion not found " << *mr << "\n";
        assert(false);
      }
      mr = fmei.m_fmapVarTransf[mr];
    }
  } else
    mrDefk = finite_map::fmapDefKeys(mr);

  if (bind::isFiniteMapConst(ml)) {
    if (fmei.m_fmapVarTransf.count(ml) == 0) { // first appearance
      // store map definition and transform to true
      fmei.m_fmapDefk[ml] = mrDefk;
      fmei.m_type[ml] = fmei.m_type[mr];
      fmei.m_typeLmd[ml] = fmei.m_typeLmd[mr];
      fmei.m_fmapVarTransf[ml] = mr;

      errs() << "Stored keys: " << *ml << " = " << *mrDefk << "\n";
      errs() << "\t expansion: " << *mr << "\n";
      errs() << "\t lambda: "
             << *fmei.m_typeLmd[ml] << "\n";
      return mk<TRUE>(fmei.m_efac);
    } else{
      assert(fmei.m_fmapDefk.count(ml) > 0);
      mlDefk = fmei.m_fmapDefk[ml];
      ml = fmei.m_fmapVarTransf[ml];
    }
  } else{
    mlDefk = fmei.m_fmapDefk[ml];
  }

  Expr lksl = fmei.m_typeLmd[ml];
  Expr lksr = fmei.m_typeLmd[mr];

  assert(lksl);
  assert(lksr);

  assert(mrDefk);
  assert(mlDefk);

  ExprVector conj;
  auto l_it = mlDefk->args_begin();
  auto r_it = mrDefk->args_begin();
  for (int i = 0; l_it != mlDefk->args_end(); i++, l_it++, r_it++) {
    // unify keys (from the definition)
    conj.push_back(mk<EQ>(*l_it, *r_it));
    // unify values
    conj.push_back(mk<EQ>(getValueAtDef(ml, lksl, mlDefk->arg(i), i),
                          getValueAtDef(mr, lksr, mrDefk->arg(i), i)));
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

  Expr defk = finite_map::fmapDefKeys(map);
  Expr vTy = bind::typeOf(finite_map::fmapDefDefault(map)->left());

  ExprVector keys(defk->args_begin(), defk->args_end());
  Expr fmTy = sort::finiteMapTy(vTy, keys);
  fmei.m_type[map] = fmTy;
  fmei.m_typeLmd[map] = finite_map::mkKeys(keys, fmei.m_efac);

  return map;
}

// -- rewrites a map get primitive
static Expr mkGetCore(Expr map, Expr key, FMapExprsInfo &fmei) {

  errs() << "-- mkGetCore " << *map << " " << *key << "\n";
  Expr lmdKeys = fmei.m_typeLmd[map];
  assert(lmdKeys);

  return finite_map::mkGetVal(mkFMapPrimitiveArgCore(map, fmei), lmdKeys, key);
}

// -- rewrites a map set primitive
static Expr mkSetCore(Expr map, Expr key, Expr value, FMapExprsInfo &fmei) {

  errs() << "-- mkSetCore " << *map << " " << *key << " " << *value << "\n";

  Expr fmTy = fmei.m_type[map];
  Expr lmdKeys = fmei.m_typeLmd[map];
  assert(lmdKeys);

  Expr procMap = mkFMapPrimitiveArgCore(map, fmei);
  Expr res = finite_map::mkSetVal(procMap, lmdKeys, key,
                           value, fmei.m_efac);

  if(isOpX<CONST_FINITE_MAP>(map))
    fmei.m_fmapDefk[res] = finite_map::fmapDefKeys(map);
  else
    fmei.m_fmapDefk[res] = fmei.m_fmapDefk[map];

  fmei.m_typeLmd[res] = lmdKeys;
  fmei.m_type[res] = fmTy;

  return res;
}

// -- processes a fmap constant, caches its type and its lambda term for the
// keys
static Expr mkFMapConstCore(Expr map_var, FMapExprsInfo &fmei) {

  // Initializing this in mkEqCore
  // if (fmei.m_type.count(map_var) == 0) {
  //   Expr fmTy = bind::rangeTy(bind::fname(map_var));
  //   Expr ksTy = finite_map::keys(fmTy);
  //   // ExprVector keys(ksTy->args_begin(), ksTy->args_end());
  //   // fmei.m_vars.insert(keys.begin(), keys.end());
  //   // fmei.m_typeLmd[fmTy] =
  //   //     finite_map::mkKeys(keys, fmei.m_efac); // add these variables!!
  //   // errs() << "-- Creating lmd keys of " << *map_var << " "
  //   //        << *fmei.m_typeLmd[fmTy] << "\n";
  //   fmei.m_type[map_var] = fmTy;
  // }
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
    res = mkEqCore(exp->left(), exp->right(), m_fmei);
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
  //  LOG("fmap_transf", errs() << "Creating visit action for: " << *exp <<
  //  "\n";);

  if (isVisitFiniteMapOp(exp)) {
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (bind::isFiniteMapConst(exp)) {
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  } else if (isOpX<EQ>(exp)) {
    if (returnsFiniteMap(exp->left()) || returnsFiniteMap(exp->right())){
      assert(returnsFiniteMap(exp->left()));
      assert(returnsFiniteMap(exp->right()));
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    }
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
