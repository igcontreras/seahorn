#include "seahorn/FiniteMapTransf.hh"

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"

#include "seahorn/Support/SeaDebug.h"

using namespace expr;
using namespace expr::op;

namespace seahorn {
// ----------------------------------------------------------------------
//  FiniteMapArgsVisitor
// ----------------------------------------------------------------------

static Expr mkVarKey(Expr mapConst, Expr k, Expr kTy) {
  assert(bind::isFiniteMapConst(mapConst));
  return bind::mkConst(variant::tag(mapConst, k), kTy);
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
      if (bind::isFiniteMapConst(arg)) {
        map_var_name = arg;
      } else {
        map_var_name = bind::mkConst(variant::variant(arg_count, fname), argTy);
        // if there is no name, we create a variant with the name of the
        // function, make new variable (same as normalization)
      }

      Expr ksTy = sort::finiteMapKeyTy(argTy);
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
//  FiniteMapBodyVisitor
// ----------------------------------------------------------------------

// -- rewrites a map term (if not already) to be used in a map primitive
static Expr mkFMapPrimitiveArgCore(Expr map, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs()
                         << "-- mkFMapPrimitiveArgCore arg: " << *map << "\n");

  if (bind::isFiniteMapConst(map)) {
    // if the map is a variable, it is assumed to be defined or expanded before.
    assert(!(fmei.m_fmapVarTransf.count(map) == 0) &&
           " no previous fmap definition found");
    map = fmei.m_fmapVarTransf[map];
  }

  Expr fmTy = fmei.m_type[map];
  Expr vTy = sort::finiteMapValTy(fmTy);

  if (isOpX<CONST_FINITE_MAP>(map)) { // transform map definition to lambda
    // the map is a map definition
    if (!finite_map::isInitializedFiniteMap(map)) { // non init values
      return finite_map::mkEmptyMap(finite_map::fmapDefDefault(map)->left());
    } else {
      Expr defk = finite_map::fmapDefKeys(map);
      Expr valuesE = finite_map::fmapDefValues(map);
      return finite_map::mkInitializedMap(
          llvm::make_range(defk->args_begin(), defk->args_end()), vTy,
          llvm::make_range(valuesE->args_begin(), valuesE->args_end()),
          finite_map::fmapDefDefault(map)->first());
    }
  } else // already transformed map: default-map or ite expr
    return map;
}

static Expr getValueAtDef(Expr map, Expr lks, Expr k, unsigned pos,
                          ZSimplifier<EZ3> &zsimp) {
  if (isOpX<CONST_FINITE_MAP>(map)) {
    if (finite_map::isInitializedFiniteMap(map))
      return finite_map::fmapDefValues(map)->arg(pos);
    else
      return finite_map::fmapDefDefault(map)->left();
  } // already an expanded map term

  return zsimp.simplify(finite_map::mkGetValPos(
      map, mkTerm<mpz_class>(pos + 1, map->efac()))); // the position of first
                                                      // key is '1' vs. the
                                                      // first argument is '0'
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
  fmei.m_typeLmd[mapConst] = mapLmdKeys;
  fmei.m_typeLmd[mapDef] = mapLmdKeys;
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
        mr = mkEmptyConstMap(mr,fmei);
        mrDefk = finite_map::fmapDefValues(mr);
        // assert(false && "undefined fmap");
        // return mk<EQ>(ml, mr);
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
      fmei.m_fmapDefk[ml] = mrDefk;
      fmei.m_type[ml] = fmei.m_type[mr];
      fmei.m_typeLmd[ml] = fmei.m_typeLmd[mr];
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

  Expr lksl = fmei.m_typeLmd[ml];
  Expr lksr = fmei.m_typeLmd[mr];

  assert(lksl);
  assert(lksr);

  bool skipKs = (mlDefk == mrDefk);
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
      Expr vl = getValueAtDef(ml, lksl, mlDefk->arg(i), i, fmei.m_zsimp);
      Expr vr = getValueAtDef(mr, lksr, mrDefk->arg(i), i, fmei.m_zsimp);
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
  fmei.m_typeLmd[map] = finite_map::mkKeys(keys, fmei.m_efac);

  return map;
}

// -- rewrites a map get primitive
static Expr mkGetCore(Expr map, Expr key, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkGetCore " << *map << " " << *key << "\n";);

  if (fmei.m_typeLmd.count(map) == 0) {
    assert(bind::isFiniteMapConst(map));
    mkEmptyConstMap(map, fmei);
  }
  Expr pos =
      fmei.m_zsimp.simplify(finite_map::mkGetPosKey(fmei.m_typeLmd[map], key));

  map = mkFMapPrimitiveArgCore(map, fmei);

  return fmei.m_zsimp.simplify(finite_map::mkGetValPos(map, pos));
}

// -- rewrites a map set primitive
static Expr mkSetCore(Expr map, Expr key, Expr value, FMapExprsInfo &fmei) {

  LOG("fmap_transf", errs() << "-- mkSetCore " << *map << " " << *key << " "
                            << *value << "\n";);

  Expr lmdKeys;
  if (fmei.m_typeLmd.count(map) == 0) {
    assert(bind::isFiniteMapConst(map));
    mkEmptyConstMap(map, fmei);
  }
  lmdKeys = fmei.m_typeLmd[map];
  assert(lmdKeys);

  Expr procMap = mkFMapPrimitiveArgCore(map, fmei);

  Expr pos = fmei.m_zsimp.simplify(finite_map::mkGetPosKey(lmdKeys, key));
  Expr res = finite_map::mkSetValPos(procMap, pos, value);
  res = fmei.m_zsimp.simplify(res);

  if (isOpX<CONST_FINITE_MAP>(map))
    fmei.m_fmapDefk[res] = finite_map::fmapDefKeys(map);
  else
    fmei.m_fmapDefk[res] = fmei.m_fmapDefk[map];

  fmei.m_typeLmd[res] = lmdKeys;
  fmei.m_type[res] = fmei.m_type[map];

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
  Expr defkel = fmei.m_fmapDefk[th];

  Expr ty = fmei.m_type[th];
  Expr lmdKeys = fmei.m_typeLmd[th];

  th = mkFMapPrimitiveArgCore(th, fmei);
  el = mkFMapPrimitiveArgCore(el, fmei);

  if (defkth != defkel) { // replace the keys in `el` by the keys in `th`
    ExprMap rmap;
    auto th_it = defkth->args_begin();
    auto el_it = defkel->args_begin();
    for (; th_it != defkth->args_end(); th_it++, el_it++)
      rmap[*el_it] = *th_it;

    el = replace(el, rmap);
  }

  Expr x = bind::mkConst(mkTerm<std::string>("x", fmei.m_efac),
                         sort::finiteMapValTy(ty));
  Expr res =
      bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                        boolop::lite(ite->first(), bind::betaReduce(th, x),
                                     bind::betaReduce(el, x)));
  // TODO: fapp or betaReduce ? simplify?

  fmei.m_fmapDefk[res] = defkth;
  fmei.m_typeLmd[res] = lmdKeys;
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

  return VisitAction::doKids();
}

} // namespace seahorn
