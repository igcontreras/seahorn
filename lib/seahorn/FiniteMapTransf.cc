#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {
// ----------------------------------------------------------------------
//  FiniteMapArgsVisitor
// ----------------------------------------------------------------------

static Expr mkVarKey(Expr mapConst, Expr k, Expr kTy) {
  assert(bind::isFiniteMapConst(mapConst));
  return bind::mkConst(variant::variant(0, variant::tag(mapConst, k)), kTy);
}

// -- creates a constant with the name get(map,k)
// also used in FinteMapBodyVisitor
static Expr mkVarGet(Expr mapConst, Expr k, Expr vTy) {
  assert(bind::isFiniteMapConst(mapConst));
  return bind::mkConst(variant::variant(0, finite_map::get(mapConst, k)), vTy);
}

static inline Expr mkDefault(Expr base, Expr vTy) {
  return bind::mkConst(variant::tag(base, mkTerm<mpz_class>(0, vTy->efac())),
                       vTy);
}

// \brief rewrites a map into separate scalar variables. New arguments are added
// to `newArgs`, new unifications are added to `extra_unifs`
template <typename Range>
void mkVarsMap(Expr mapConst, Expr map, const Range &keys, int nKs, Expr kTy,
               Expr vTy, ExprVector::iterator &newArg_it,
               ExprVector &extra_unifs, ExprSet &evars) {

  Expr v, key;
  ExprVector map_values(nKs), map_keys(nKs);
  auto v_it = map_values.begin(), k_it = map_keys.begin();
  Expr mapName = bind::name(bind::fname(mapConst));

  if (nKs == 1) {
    Expr k = *keys.begin();
    key = mkVarKey(mapConst, k, kTy);
    *k_it++ = key;
    v = mkVarGet(mapConst, k, vTy);
    *v_it++ = v;
    evars.insert(v);
    evars.insert(key);
    *newArg_it++ = v;
  } else
    for (auto k : keys) {
      key = mkVarKey(mapConst, k, kTy);
      *k_it++ = key;
      v = mkVarGet(mapConst, k, vTy);
      *v_it++ = v;
      evars.insert(v);
      evars.insert(key);
      *newArg_it++ = key;
      *newArg_it++ = v;
    }
  Expr defaultV = mkDefault(map_values.back(), vTy);
  evars.insert(defaultV);

  extra_unifs.push_back(
      mk<EQ>(map, finite_map::constFiniteMap(map_keys, defaultV, map_values)));
}

// \brief rewrites the map arguments of fapps into separate scalar variables
static Expr mkFappArgsCore(Expr fapp, Expr newFdecl, ExprVector &extraUnifs,
                           ExprSet &evars, ExprFactory &efac) {

  assert(isOpX<FAPP>(fapp));

  Expr fdecl = bind::name(fapp);
  assert(bind::isFdecl(fdecl));
  Expr fname = bind::fname(fdecl);

  ExprVector newArgs(newFdecl->arity() - 2); // 2: fname, ret

  auto arg_it = ++(fapp->args_begin()), t_it = ++(fdecl->args_begin());
  auto nArg_it = newArgs.begin();

  int arg_count = 0;
  for (; arg_it != fapp->args_end(); arg_it++, arg_count++, t_it++) {
    Expr arg = *arg_it;
    Expr argTy = *t_it;

    if (isOpX<FINITE_MAP_TY>(argTy)) {
      Expr map_var_name;
      Expr ksTy;
      if (bind::isFiniteMapConst(arg)) {
        map_var_name = arg;
        ksTy = sort::finiteMapKeyTy(bind::rangeTy(bind::fname(arg)));
      } else { // TODO: can there be ITEs in calls to predicates or only heads?
        ksTy = sort::finiteMapKeyTy(argTy);
        map_var_name = bind::mkConst(variant::variant(arg_count, fname), argTy);
        // if there is no name, we create a variant with the name of the
        // function, make new variable (same as normalization)
      }

      // Expr ksTy = sort::finiteMapKeyTy(argTy);
      // the keys have to be obtained from the const, not the type. The Dsa info
      // of the type is relative to the function (context insensitive), the Dsa
      // info on the type of the const is relative to the calling context.
      auto keys = llvm::make_range(ksTy->args_begin(), ksTy->args_end());

      mkVarsMap(map_var_name, arg, keys, ksTy->arity(),
                bind::rangeTy(bind::fname(ksTy->arg(0))),
                sort::finiteMapValTy(argTy), nArg_it, extraUnifs, evars);
      // new arguments are added to `newArgs` in the function above
    } else {
      assert(!bind::isFiniteMapConst(arg));
      *nArg_it++ = arg;
    }
  }
  return bind::fapp(newFdecl, newArgs); // building the new fapp
}

Expr FiniteMapArgRewriter::operator()(Expr exp) {

  if (isOpX<IMPL>(exp)) { // rule (or implication inside rule?)
    Expr head = exp->right();
    Expr fdecl = head->first();

    ExprVector newUnifs;
    Expr newFapp = mkFappArgsCore(head, m_pred_decl_t.find(fdecl)->second,
                                  newUnifs, m_evars, m_efac);

    Expr body = exp->left();
    Expr newBody =
        newUnifs.empty() ? body : boolop::land(body, boolop::land(newUnifs));

    return boolop::limp(newBody, newFapp);
  } else if (isOpX<FAPP>(exp)) {
    ExprVector newUnifs;
    Expr newExp =
        mkFappArgsCore(exp, m_pred_decl_t.find(bind::name(exp))->second,
                       newUnifs, m_evars, m_efac);
    newUnifs.push_back(newExp);
    return boolop::land(newUnifs);
  }
  return exp;
}

// rewrite bottom_up
VisitAction FiniteMapArgsVisitor::operator()(Expr exp) {

  if (isOpX<IMPL>(exp) && bind::isFapp(exp->right()) &&
      m_pred_decl_t.count(exp->right()->first()) >
          0) // rule (or implication inside rule?)
    return VisitAction::changeDoKids((*m_rw)(exp));
  else if (bind::IsConst()(exp) ||
           bind::isFdecl(exp)) // TODO: more cases to skip?
    return VisitAction::skipKids();
  else if (bind::isFapp(exp) && m_pred_decl_t.count(bind::name(exp)) > 0)
    return VisitAction::changeDoKidsRewrite(exp, m_rw);

  return VisitAction::doKids();
}

} // namespace seahorn

namespace {

using namespace seahorn;

// ----------------------------------------------------------------------
//  Ite dsa-based top-down simplifier
// ----------------------------------------------------------------------

static Expr getCellExprVariant(Expr e) {
  assert(bind::IsConst()(e));

  // assumes only 1 level of variance
  Expr name = variant::mainVariant(bind::name(bind::fname(e)));
  Expr cellE = variant::getTag(name);

  if (!isOpX<CELL>(cellE)) // cell tags are included inside the key tag
    cellE = variant::getTag(bind::name(bind::fname(cellE)));

  assert(isOpX<CELL>(cellE));
  return cellE; // cell id
}

static Expr getCellExpr(Expr e) {

  // only supporting one level of +
  if (isOpX<PLUS>(e))
    e = e->left();

  return getCellExprVariant(e);
}

static unsigned getOffsetCellExpr(Expr e) {

  unsigned offset = 0;

  // only supporting one level of +
  if (isOpX<PLUS>(e)) {
    mpz_class o = getTerm<mpz_class>(e->right());
    offset += o.get_ui(); // TODO: overflow? dangerous?
    e = e->left();
  }

  e = getCellExprVariant(e);

  assert(isOpX<CELL>(e));
  return offset + getTerm<unsigned>(e->right());
}

// for debugging
bool sameNode(Expr e1, Expr e2) {
  return getCellExpr(e1)->left() == getCellExpr(e2)->left();
}

bool validDsaConst(Expr e) {
  if (!bind::IsConst()(e))
    return false;

  Expr name = variant::mainVariant(bind::name(bind::fname(e)));
  Expr cellE = variant::getTag(name);
  return cellE != nullptr && isOpX<CELL>(cellE);
}
bool evaluableDsaExpr(Expr e) {
  if (validDsaConst(e))
    return true;

  return isOpX<PLUS>(e) && validDsaConst(e->left()) && isOp<MPZ>(e->right());
}
static Expr evalCondDsa(Expr cond) {

  if (!evaluableDsaExpr(cond->left()) || !evaluableDsaExpr(cond->right()))
    return cond;

  unsigned lo = getOffsetCellExpr(cond->left());
  unsigned ro = getOffsetCellExpr(cond->right());

  assert(sameNode(cond->left(), cond->right()));

  if (lo != ro) // if they encode a different cell, return false
    return mk<FALSE>(cond->efac());
  else
    return cond;
}

// dsa-based ite simplifier
class IteTopDownVisitor : public std::unary_function<Expr, VisitAction> {

  ExprFactory &m_efac;

public:
  IteTopDownVisitor(ExprFactory &efac) : m_efac(efac) {}

  VisitAction operator()(Expr exp) {
    if (isOpX<ITE>(exp) && isOpX<EQ>(exp->left())) {
      Expr cond = evalCondDsa(exp->left());
      while (isOpX<FALSE>(cond)) {
        exp = exp->last();
        if (isOpX<ITE>(exp) && isOpX<EQ>(exp->left()))
          cond = evalCondDsa(exp->left());
        else
          break;
      }
      if (isOpX<FALSE>(cond))
        return VisitAction::changeDoKids(exp);
      else
        return VisitAction::changeDoKids(
            boolop::lite(cond, exp->arg(1), exp->arg(2)));
    } else if (bind::IsConst()(exp) || bind::isFdecl(exp))
      return VisitAction::skipKids();
    else
      return VisitAction::doKids();
  }
};

static Expr dsaIteSimplify(Expr e) {
  IteTopDownVisitor itdv(e->efac());
  return visit(itdv, e);
}

// ----------------------------------------------------------------------
//  FiniteMapBodyVisitor
// ----------------------------------------------------------------------

// -- rewrites a map term (if not already) to be used in a map primitive
static Expr mkFMapPrimitiveArgCore(Expr map, FMapExprsInfo &fmei) {

  Expr fmTy = fmei.m_type[map];
  assert(fmTy);
  Expr kTy = bind::rangeTy(bind::name(sort::finiteMapKeyTy(fmTy)->arg(0)));
  Expr mapTransf = map;

  if (bind::isFiniteMapConst(map)) {
    // if the map is a variable, it is assumed to be defined or expanded before.
    assert((fmei.m_fmapVarTransf.count(map) > 0) &&
           " no previous fmap definition found");
    mapTransf = fmei.m_fmapVarTransf[map];
  }

  if (isOpX<CONST_FINITE_MAP>(
          mapTransf)) { // transform map definition to lambda
    // the map is a map definition
    if (!finite_map::isInitializedFiniteMap(mapTransf)) { // non init values
      return finite_map::mkEmptyMap(
          finite_map::fmapDefDefault(mapTransf)->left());
    } else {
      Expr defk = finite_map::fmapDefKeys(mapTransf);
      Expr valuesE = finite_map::fmapDefValues(mapTransf);
      return finite_map::mkInitializedMap(
          llvm::make_range(defk->args_begin(), defk->args_end()), kTy,
          llvm::make_range(valuesE->args_begin(), valuesE->args_end()),
          finite_map::fmapDefDefault(mapTransf)->first());
    }
  } else // already transformed map: default-map or ite expr
    return mapTransf;
}

static Expr getValueAtDef(Expr map, Expr k, unsigned pos,
                          ZSimplifier<EZ3> &zsimp) {
  if (isOpX<CONST_FINITE_MAP>(map)) {
    if (finite_map::isInitializedFiniteMap(map))
      return finite_map::fmapDefValues(map)->arg(pos);
    else
      return finite_map::fmapDefDefault(map)->left();
  } // already an expanded map term

  return zsimp.simplify(dsaIteSimplify(
      finite_map::mkGetVal(map, k))); // TODO: remove basic simplifier?
}

static Expr mkEmptyConstMap(Expr mapConst, FMapExprsInfo &fmei) {
  Expr mapTy = bind::rangeTy(bind::name(mapConst));
  Expr vTy = sort::finiteMapValTy(mapTy);
  Expr keysTy = sort::finiteMapKeyTy(mapTy);
  Expr kTy = bind::rangeTy(bind::name(keysTy->first()));
  ExprVector keys(keysTy->arity());
  ExprVector values(keysTy->arity());

  auto k_it = keys.begin();
  auto v_it = values.begin();
  for (auto kty_it = keysTy->args_begin(); kty_it != keysTy->args_end();
       kty_it++, k_it++, v_it++) {
    *k_it = mkVarKey(mapConst, *kty_it, kTy);
    fmei.m_vars.insert(*k_it);
    *v_it = mkVarGet(mapConst, *kty_it, vTy);
    fmei.m_vars.insert(*v_it);
  }

  Expr defaultV = mkDefault(mapConst, vTy);
  fmei.m_vars.insert(defaultV);

  Expr mapDef = finite_map::constFiniteMap(keys, defaultV, values);
  fmei.m_fmapVarTransf[mapConst] = mapDef;
  fmei.m_type[mapConst] = mapTy;
  fmei.m_type[mapDef] = mapTy;
  Expr mapLmdKeys = finite_map::mkKeys(keys, fmei.m_efac);
  fmei.m_fmapDefk[mapConst] = finite_map::fmapDefKeys(mapDef);

  return mapDef;
}

// \brief `ml` contains the same values as `mr`.
static Expr mkEqCore(Expr ml, Expr mr, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkEqCore " << *ml << " = " << *mr << "\n";);
  Expr mrDefk, mlDefk;

  if (!isOpX<CONST_FINITE_MAP>(mr)) {
    if (bind::isFiniteMapConst(mr)) { // if variable, use its expansion
      if (fmei.m_fmapDefk.count(mr) == 0) {
        errs() << "in " << *ml << " = " << *mr << "\n"
               << "undefined fmap " << *mr->left();
        assert(false && "undefined fmap");
        return mk<EQ>(ml, mr);

      } else { // already expanded const
        mrDefk = fmei.m_fmapDefk[mr];
        mr = fmei.m_fmapVarTransf[mr];
      }
    } else { // already expanded expression
      mrDefk = fmei.m_fmapDefk[mr];
    }
  } else {
    mrDefk = finite_map::fmapDefKeys(mr);
  }

  assert(mrDefk && isOpX<CONST_FINITE_MAP_KEYS>(mrDefk));

  if (bind::isFiniteMapConst(ml)) {
    if (fmei.m_fmapVarTransf.count(ml) == 0) { // first appearance of the const
      // reduce to true equalities when the left hand side is a variable and it
      // appeared for the first time, to use the right hand side whenever the
      // left variable appears store map definition and transform to true
      //
      // this optimization can only be done if the are in the same scope
      if (fmei.m_dimpl != 0) {
        errs() << "equality inside of an implication" << *ml << " = " << *mr
               << "\n";
        assert(false);
        return mk<EQ>(ml, mr);
      }
      fmei.m_fmapDefk[ml] = mrDefk;
      fmei.m_type[ml] = fmei.m_type[mr];
      fmei.m_fmapVarTransf[ml] = mr;
      return mk<TRUE>(fmei.m_efac);
    } else {
      mlDefk = fmei.m_fmapDefk[ml];
      ml = fmei.m_fmapVarTransf[ml];
    }
  } else {
    mlDefk = fmei.m_fmapDefk[ml];
  }

  assert(mlDefk && isOpX<CONST_FINITE_MAP_KEYS>(mlDefk));

  bool skipKs = (mlDefk == mrDefk) || (mlDefk->arity() == 1);
  bool skipVs = (ml == mr);

  if (skipKs &&
      skipVs) // skip this if it is the same expansion of keys and values
    return mk<TRUE>(fmei.m_efac);

  // unsigned size = (!skipVs && !skipKs) ? 2 : 1;
  // ExprVector conj(mlDefk->arity() * size);
  ExprVector conj;
  auto l_it = mlDefk->args_begin();
  auto r_it = mrDefk->args_begin();
  // auto conj_it = conj.begin();

  for (int i = 0; l_it != mlDefk->args_end(); i++, l_it++, r_it++) {
    // unify keys (from the definition)
    if (r_it == mrDefk->args_end()) {
      errs() << "bad value matching: " << *mlDefk << "\n vs. " << *mrDefk
             << "\n";
      assert(false);
    }
    assert(r_it != mrDefk->args_end());

    if (!skipKs && *l_it != *r_it)
      conj.push_back(mk<EQ>(*l_it, *r_it));

    if (!skipVs) { // unify values
      Expr vl = getValueAtDef(ml, mlDefk->arg(i), i, fmei.m_zsimp);
      Expr vr = getValueAtDef(mr, mrDefk->arg(i), i, fmei.m_zsimp);
      if (vl != vr)
        conj.push_back(mk<EQ>(vl, vr));
    }
  }

  return conj.empty() ? mk<TRUE>(fmei.m_efac) : boolop::land(conj);
}

// -- processes a fmap definition, building the type and the lmdkeys
// term is of the form:
//
// defmap(defk(keys), fmap-default(defval)))
//      or
// defmap(defk(keys), fmap-default(defval), defv(values)))
static Expr mkDefFMapCore(Expr map, FMapExprsInfo &fmei) {

  Expr defk = finite_map::fmapDefKeys(map);
  Expr vTy = bind::typeOf(finite_map::fmapDefDefault(map)->left());

  auto keys = llvm::make_range(defk->args_begin(), defk->args_end());
  fmei.m_type[map] = sort::finiteMapTy(vTy, keys);

  return map;
}

// -- obtains a value from a definition
static Expr mkGetDefCore(Expr defmap, Expr key) {

  LOG("fmap_transf",
      errs() << "-- mkGetDefCore " << *defmap << " " << *key << "\n";);

  Expr ks = finite_map::fmapDefKeys(defmap);
  Expr vs = finite_map::fmapDefValues(defmap);

  if (ks->arity() == 1)
    return vs->left();

  std::vector<unsigned> matches;
  ExprVector conds;
  auto k_it = ks->args_begin();
  for (unsigned i = 0; i < ks->arity(); i++, k_it++) { // find keys that match
    Expr cond = evalCondDsa(mk<EQ>(*k_it, key));
    if (!isOpX<FALSE>(cond)) {
      matches.push_back(i);
      conds.push_back(cond);
    }
  }

  // if no keys match, return last value
  if (matches.empty())
    return vs->last();

  if (matches.size() == 1)
    return vs->arg(matches[0]);

  auto m_it = matches.rbegin(); // reverse iterator
  Expr ite = vs->arg(*m_it);
  m_it++;
  auto c_it = ++conds.rbegin();
  // construct ite for the keys that match
  for (; m_it != matches.rend(); m_it++, c_it++)
    ite = boolop::lite(*c_it, vs->arg(*m_it), ite);

  return ite;
}

// -- rewrites a map get primitive
static Expr mkGetCore(Expr map, Expr key, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkGetCore " << *map << " " << *key << "\n";);

  if (fmei.m_type.count(map) == 0) {
    errs() << "undefined fmap " << *map << "\n";
    assert(false && "map definition not found");
    return finite_map::get(map, key);
  }

  Expr defmap = map;
  if (bind::isFiniteMapConst(map))
    defmap = fmei.m_fmapVarTransf[map];

  // get from defmap
  if (finite_map::isInitializedFiniteMap(defmap))
    return mkGetDefCore(defmap, key);

  // get from lambda
  map = mkFMapPrimitiveArgCore(map, fmei);
  // does eager simplification during beta reduction
  return dsaIteSimplify(fmei.m_zsimp.simplify(finite_map::mkGetVal(map, key)));
}

// -- obtains a new definition after inserting a value, returns `nullptr` if the
// -- value could be placed in several keys
static Expr mkSetDefCore(Expr defmap, Expr key, Expr v) {

  LOG("fmap_transf",
      errs() << "-- mkSetDefCore " << *defmap << " " << *key << "\n";);

  Expr ks = finite_map::fmapDefKeys(defmap);
  Expr vs = finite_map::fmapDefValues(defmap);

  auto keys = llvm::make_range(ks->args_begin(), ks->args_end());

  if (ks->arity() == 1) {
    ExprVector value = {v};
    return finite_map::constFiniteMap(keys, finite_map::fmapDefDefault(defmap),
                                      value);
  }

  std::vector<unsigned> matches;
  ExprVector conds;
  auto k_it = ks->args_begin();
  for (int i = 0; i < ks->arity(); i++, k_it++) { // find keys that match
    Expr cond = evalCondDsa(mk<EQ>(*k_it, key));
    if (!isOpX<FALSE>(cond)) {
      matches.push_back(i);
      conds.push_back(cond);
    }
  }

  // if no keys match, return last value
  if (matches.empty()) // this should not happen, return def as it is?
    return vs->last();

  if (matches.size() == 1) { // replace only that one
    ExprVector nvalues(ks->arity());
    auto ov_it = vs->args_begin();
    unsigned changed = matches[0];
    for (int i = 0; i < ks->arity(); i++, ov_it++)
      if (i == changed)
        nvalues[i] = v;
      else
        nvalues[i] = *ov_it;

    return finite_map::constFiniteMap(keys, finite_map::fmapDefDefault(defmap),
                                      nvalues);
  }
  return nullptr;
}

// -- rewrites a map set primitive
static Expr mkSetCore(Expr map, Expr key, Expr value, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkSetCore " << *map << " " << *key << " "
                            << *value << "\n";);

  if (fmei.m_fmapDefk.count(map) == 0) {
    errs() << "undefined fmap " << *map << "\n";
    assert(false && "map definition not found");
    return finite_map::set(map, key, value);
  }

  Expr defmap = map;
  if (bind::isFiniteMapConst(map))
    defmap = fmei.m_fmapVarTransf[map];

  if (finite_map::isInitializedFiniteMap(defmap)) {
    defmap = mkSetDefCore(defmap, key, value);
    if (defmap != nullptr) { // optimization could be done
      fmei.m_fmapDefk[defmap] = fmei.m_fmapDefk[map];
      fmei.m_type[defmap] = fmei.m_type[map];
      return defmap;
    }
  }

  Expr procMap = mkFMapPrimitiveArgCore(map, fmei);

  Expr fmTy = fmei.m_type[map];
  Expr kTy = bind::rangeTy(bind::name(sort::finiteMapKeyTy(fmTy)->arg(0)));

  Expr res = finite_map::mkSetVal(procMap, key, kTy, value);

  if (isOpX<CONST_FINITE_MAP>(map))
    fmei.m_fmapDefk[res] = finite_map::fmapDefKeys(map);
  else
    fmei.m_fmapDefk[res] = fmei.m_fmapDefk[map];

  fmei.m_type[res] = fmTy;

  return res;
}

static Expr getDefFmapConst(Expr m, FMapExprsInfo &fmei) {
  if (fmei.m_fmapDefk.count(m) == 0)
    return finite_map::fmapDefKeys(mkEmptyConstMap(m, fmei));
  else
    return fmei.m_fmapDefk[m];
}

static Expr mkSameKeysCore(Expr lmap, Expr er, FMapExprsInfo &fmei) {

  Expr defl = getDefFmapConst(lmap, fmei);

  Expr defr = bind::isFiniteMapConst(er) ? getDefFmapConst(er, fmei) : er;

  assert(defl->arity() == defr->arity());
  ExprVector conj(defl->arity());

  auto c_it = conj.begin();
  auto l_it = defl->args_begin();
  auto r_it = defr->args_begin();
  for (; l_it != defl->args_end(); c_it++, l_it++, r_it++) {
    *c_it = mk<EQ>(*l_it, *r_it);
  }
  return boolop::land(conj);
}

// -- rewrites a map set primitive
static Expr mkIteCore(Expr ite, FMapExprsInfo &fmei) {
  Expr th = ite->arg(1);
  Expr el = ite->last();

  /// -- we can use the `th` or the `el`
  Expr defkth = fmei.m_fmapDefk[th];

  Expr ty = fmei.m_type[th];

  th = mkFMapPrimitiveArgCore(th, fmei);
  el = mkFMapPrimitiveArgCore(el, fmei);

  Expr x = bind::mkConst(mkTerm<std::string>("x", fmei.m_efac),
                         bind::rangeTy(bind::fname(defkth->arg(0))));
  Expr res =
      bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                        boolop::lite(ite->first(), bind::betaReduce(th, x),
                                     bind::betaReduce(el, x)));
  fmei.m_fmapDefk[res] = defkth;
  fmei.m_type[res] = ty;

  return res;
}

} // namespace

namespace seahorn {

Expr FiniteMapBodyRewriter::operator()(Expr exp) {

  Expr res;

  if (isOpX<CONST_FINITE_MAP>(exp)) {
    res = mkDefFMapCore(exp, m_fmei);
  } else if (isOpX<GET>(exp)) {
    res = mkGetCore(exp->left(), exp->right(), m_fmei);
  } else if (isOpX<SET>(exp)) {
    res = mkSetCore(exp->arg(0), exp->arg(1), exp->arg(2), m_fmei);
  } else if (isOpX<ITE>(exp)) {
    res = mkIteCore(exp, m_fmei);
  } else if (isOpX<EQ>(exp)) {
    res = mkEqCore(exp->left(), exp->right(), m_fmei);
  } else if (isOpX<IMPL>(exp)) {
    m_fmei.m_dimpl--;
    return exp;
  } else if (isOpX<SAME_KEYS>(exp)) {
    res = mkSameKeysCore(exp->left(), exp->right(), m_fmei);
  } else { // do nothing
    assert(false && "Unexpected map expression");
    return exp;
  }
  LOG("fmap_transf",
      errs() << "Rewritten: " << *exp << "\n   to: " << *res << "\n";);
  return res;
}

bool FiniteMapBodyVisitor::isRewriteFiniteMapOp(Expr e) {
  return isOpX<CONST_FINITE_MAP>(e) || isOpX<GET>(e) || isOpX<SET>(e) ||
         isOpX<SAME_KEYS>(e);
  // we are not visiting CONST_FINITE_MAP_KEYS and DEFAULT
}

VisitAction FiniteMapBodyVisitor::operator()(Expr exp) {

  if (isRewriteFiniteMapOp(exp))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (isOpX<ITE>(exp) && finite_map::returnsFiniteMap(exp->right()))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (isOpX<EQ>(exp) && finite_map::returnsFiniteMap(exp->left()))
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  else if (bind::IsConst()(exp) || bind::isFdecl(exp))
    return VisitAction::skipKids();
  else if (isOpX<IMPL>(exp)) {
    m_dimpl++;
    // no rewritting necessary but we need to mark that we exited it
    return VisitAction::changeDoKidsRewrite(exp, m_rw);
  }

  return VisitAction::doKids();
}

} // namespace seahorn
