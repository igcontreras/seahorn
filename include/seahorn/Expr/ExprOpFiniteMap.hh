/// Finite Maps
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

namespace expr {

namespace op {
enum class FiniteMapOpKind {
  CONST_FINITE_MAP_KEYS,
  CONST_FINITE_MAP_VALUES,
  FINITE_MAP_VAL_DEFAULT,
  CONST_FINITE_MAP,
  SET,
  GET,
  SAME_KEYS
};

namespace typeCheck {
namespace finiteMapType {
struct ValuesKeys;
struct ValuesDefault;
struct FiniteMap;
struct Get;
struct Set;
} // namespace finiteMapType
} // namespace typeCheck

/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP_KEYS, "defk", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesKeys)
NOP(CONST_FINITE_MAP_VALUES, "defv", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesKeys)
NOP(CONST_FINITE_MAP, "defmap", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::FiniteMap)
NOP(FINITE_MAP_VAL_DEFAULT, "fmap-default", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesDefault)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp, typeCheck::finiteMapType::Get)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp, typeCheck::finiteMapType::Set)
NOP(SAME_KEYS, "same-keys", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::FiniteMap) // TODO: type checking

namespace typeCheck {
namespace finiteMapType {

struct ValuesKeys : public TypeCheckBase {
  /// ensures that all children are the same type
  /// \return the type of its children
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnFn = [](Expr exp, TypeChecker &tc) {
      return tc.typeOf(exp->first());
    };

    return typeCheck::oneOrMore<ANY_TY>(
        exp, tc, returnFn); // children can by of any type
  }
};
struct ValuesDefault : public TypeCheckBase {
  /// ensures that there is 1 child
  /// \return the type of its child
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnFn = [](Expr exp, TypeChecker &tc) {
      return tc.typeOf(exp->first());
    };

    return typeCheck::unary<ANY_TY>(exp, tc,
                                    returnFn); // children can by of any type
  }
};

struct FiniteMap : public TypeCheckBase {
  /// ensures that the left child is a valid key type, and right is a valid
  /// value \return: FINITE_MAP_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() != 2 && exp->arity() != 3)
      return sort::errorTy(exp->efac());

    Expr keys = exp->left();
    Expr defval = exp->right();

    if (!isOp<CONST_FINITE_MAP_KEYS>(keys))
      return sort::errorTy(exp->efac());

    if (!isOp<FINITE_MAP_VAL_DEFAULT>(defval))
      return sort::errorTy(exp->efac());

    if (exp->arity() == 3) {
      Expr vals = exp->last();
      // TODO: check that all values are of the type of the default
      if (isOp<CONST_FINITE_MAP_VALUES>(vals)) {
        if (keys->arity() != vals->arity())
          return sort::errorTy(exp->efac());
        else if (tc.typeOf(defval) != tc.typeOf(vals->first()))
          return sort::errorTy(exp->efac());
      }
    }

    ExprVector keyVector(keys->args_begin(), keys->args_end());
    return sort::finiteMapTy(tc.typeOf(defval), keyVector);
  }
};

static inline bool checkMap(Expr exp, TypeChecker &tc, unsigned numChildren) {
  return exp->arity() == numChildren &&
         correctTypeAny<FINITE_MAP_TY>(exp->first(), tc);
}

static inline void getFiniteMapTypes(Expr exp, TypeChecker &tc, Expr &mapTy,
                                     Expr &indexTy, Expr &valTy) {
  mapTy = tc.typeOf(exp->left());
  indexTy =
      tc.typeOf(sort::finiteMapKeyTy(mapTy)
                    ->first()); // type of: FINITE_MAP_KEYS_TY -> first key
  valTy = sort::finiteMapValTy(mapTy);
}

struct Get : public TypeCheckBase {
  /// ensures that the expression's index type matches the map's index type
  /// checks for the following children (in order): map, index
  /// \return the map's value type
  /// \note this is the same as array select
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::mapType::select<FINITE_MAP_TY>(exp, tc,
                                                     getFiniteMapTypes);
  }
};

struct Set : public TypeCheckBase {
  /// ensures that the index type and value type match the map's index and value
  /// types checks for the following children (in order): map, index, value
  /// \return FINITE_MAP_TY
  /// \note this is the same as array store
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::mapType::store<FINITE_MAP_TY>(exp, tc, getFiniteMapTypes);
  }
};

} // namespace finiteMapType
} // namespace typeCheck

} // namespace op

namespace op {
namespace finite_map {

// --------------- finite map primitives ---------------------
template <typename Range>
inline Expr constFiniteMapValues(const Range &values) {
  return mknary<CONST_FINITE_MAP_VALUES>(values.begin(), values.end());
}

inline Expr constFiniteMapDefault(Expr def) {
  return mk<FINITE_MAP_VAL_DEFAULT>(def);
}

template <typename Range> inline Expr constFiniteMapKeys(const Range &keys) {
  return mknary<CONST_FINITE_MAP_KEYS>(keys.begin(), keys.end());
}

// \brief builds an empty map term. `e` is the default for the unitialized
// values
template <typename Range>
inline Expr constFiniteMap(const Range &keys, Expr def) {
  return mk<CONST_FINITE_MAP>(constFiniteMapKeys(keys),
                              constFiniteMapDefault(def));
}

// construct when ALL the values of the map are known (they can be
// variables)
// -- the iterators may be of different type
template <typename Range1, typename Range2>
inline Expr constFiniteMap(const Range1 &keys, Expr def, const Range2 &values) {
  return mk<CONST_FINITE_MAP>(constFiniteMapKeys(keys),
                              constFiniteMapDefault(def),
                              constFiniteMapValues(values));
}

inline Expr fmapDefKeys(Expr fmap) { return fmap->left(); }

inline Expr fmapDefDefault(Expr fmap) {
  assert(isOpX<FINITE_MAP_VAL_DEFAULT>(fmap->right()));
  return fmap->right();
}

inline Expr fmapDefValues(Expr fmap) {
  assert(isOpX<CONST_FINITE_MAP_VALUES>(fmap->last()));
  return fmap->last();
}

inline bool isInitializedFiniteMap(Expr m) {
  if (isOpX<CONST_FINITE_MAP>(m))
    return isOpX<CONST_FINITE_MAP_VALUES>(m->last());

  return false;
}

inline Expr get(Expr map, Expr idx) { return mk<GET>(map, idx); }
inline Expr set(Expr map, Expr idx, Expr v) { return mk<SET>(map, idx, v); }

inline Expr constrainKeys(Expr map1, Expr map2) {
  return mk<SAME_KEYS>(map1, map2);
}
template <typename Range>
inline Expr constrainKeys(Expr map, const Range &keys) {
  return mk<SAME_KEYS>(map, constFiniteMapKeys(keys));
}

// --------------- transformation to lambda functions ------------------------
// \brief the empty map is just the default value `defaultV`
inline Expr mkEmptyMap(Expr defaultV) { return defaultV; }

// creates a set of keys as a lambda function
template <typename Range>
inline Expr mkKeys(const Range &keys, ExprFactory &efac) {

  Expr lmdTmp = mkTerm<mpz_class>(1, efac);
  // default value for th lambda keys: a key not defined in the fmap

  // TODO: this should be generic for the type of the key
  Expr keyToPos = bind::intConst(mkTerm<std::string>("x", efac));

  // this variable is used to represent where in the map values lambda term the
  // value of a key is stored. It is not affected by the sort of the keys or the
  // values. The lambda term for the keys will be expanded to (ite k1=k1 1 0)
  // and then used in an lambda term for a map: (ite ((ite k1=k1 1 0)=1) v1
  // default)), where we are using ints also.
  unsigned count = 1;
  // this loop creates a lambda term for the keys. The lambda term is of the
  // form: l1 x.(ite x == k1 1 0)
  //       ln x.(ite x == kn n (ln-1 x))
  //
  // the lambda function returns the position of the value corresponding to a
  // key in the lambda term that represents the values
  for (auto key : keys)
    lmdTmp = boolop::lite(mk<EQ>(key, keyToPos),
                          mkTerm<mpz_class>(count++, efac), lmdTmp);

  return bind::abs<LAMBDA>(std::array<Expr, 1>{keyToPos}, lmdTmp);
}

// creates a set of keys as a lambda function
template <typename Range>
inline Expr mkKeys(const Range &keys, const Expr base, const Expr kTy,
                   ExprFactory &efac) {

  Expr lmdTmp = mkTerm<mpz_class>(0, efac);
  // default value for th lambda keys: a key not defined in the fmap

  Expr keyToPos = bind::mkConst(mkTerm<std::string>("x", efac), kTy);
  unsigned count = 1;
  for (auto key : keys)
    lmdTmp = boolop::lite(
        mk<EQ>(bind::mkConst(variant::tag(base, key), kTy), keyToPos),
        mkTerm<mpz_class>(count++, efac), lmdTmp);

  return bind::abs<LAMBDA>(std::array<Expr, 1>{keyToPos}, lmdTmp);
}

// \brief creates a map for keys and values, assuming that they are sorted
template <typename Range>
inline Expr mkInitializedMap(const Range &keys, Expr vTy, const Range &values,
                             Expr defaultV, const Expr lmdKeys) {

  ExprFactory &efac = vTy->efac();
  assert(bind::typeOf(defaultV) == vTy);
  // assuming that there is a value for every key. If this is not available,
  // "initialize" it with the default value for uninitialized memory

  Expr y = bind::mkConst(mkTerm<std::string>("y", efac), vTy);
  // internal variable for the values lambda term, it must be of the value kind

  // assuming that mkKeys assigns the position in the map starting at 1
  unsigned count = 1;

  Expr lmdMap = defaultV;
  // we create lmd expressions for the map values of the form:
  //
  // l1 x.(ite (x == 1) v1 defaultV)
  // ln x.(ite (x == n) vn (ln-1 x))
  for (auto v : values)
    lmdMap =
        boolop::lite(mk<EQ>(y, mkTerm<mpz_class>(count++, efac)), v, lmdMap);

  return bind::abs<LAMBDA>(std::array<Expr, 1>{y}, lmdMap);
}

/// \brief Constructs get expression. Non-simplifying. None of the parameters
/// should contain map terms, they should be expanded to lambdas
//      `lmdMap` contains the values of the map as a lambda term
//      `lmdKeys` represents the keys of the map as a lambda term
//      `key` is an expression of type int or bv
inline Expr mkGetVal(Expr lmdMap, Expr lmdKeys, Expr key) {

  // assert(isOpX<LAMBDA>(lmdMap));
  // lmdMap may be a lambda or the default value: a number or a const.
  assert(isOpX<LAMBDA>(lmdKeys));

  return op::bind::betaReduce(lmdMap, op::bind::betaReduce(lmdKeys, key));
}

inline Expr mkGetPosKey(Expr lmdKeys, Expr key) {

  // assert(isOpX<LAMBDA>(lmdKeys));
  if (!isOpX<LAMBDA>(lmdKeys))
    return lmdKeys;
  else
    return op::bind::fapp(lmdKeys, key);
}

// \brief operation for extracting the value when the possition is
// already know, i.e., the keys lambda term has been resolved
inline Expr mkGetValPos(Expr lmdMap, Expr pos) {

  // return op::bind::betaReduce(lmdMap, pos);
  return op::bind::fapp(lmdMap, pos);
}

/// \brief Constructs set expression. Non-simplifying. None of the parameters
/// should contain map terms, they should be expanded to lambdas
//      `lmdMap` contains the values of the map as a lambda term
//      `lmdKeys` represents the keys of the map as a lambda term
inline Expr mkSetVal(Expr lmdMap, Expr lmdKeys, Expr key, Expr value) {

  // lmdMap may be a lambda or the default value: a number or a const.
  assert(isOpX<LAMBDA>(lmdKeys));
  assert(isOpX<FDECL>(lmdKeys->arg(0)));

  Expr kTy = bind::rangeTy(lmdKeys->arg(0));
  Expr x = bind::intConst(mkTerm<std::string>("x", lmdMap->efac()));
  // this internal variable is an integer because we represent the positions of
  // the keys in the map with integers

  Expr keyToPos = op::bind::betaReduce(lmdKeys, key);
  // keyToPos is the position in which the value for key: lmdKeys(key)
  Expr cmp = mk<EQ>(x, keyToPos);
  Expr ite = boolop::lite(cmp, value, bind::betaReduce(lmdMap, x));

  // lx.(ite ((lmdKeys key) == x) value (lmdMap x))
  return bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
}

inline Expr mkSetValPos(Expr lmdMap, Expr pos, Expr value) {

  Expr x = bind::intConst(mkTerm<std::string>("x", lmdMap->efac()));
  Expr cmp = mk<EQ>(x, pos);
  Expr ite = boolop::lite(cmp, value, bind::betaReduce(lmdMap, x));

  // lx.(ite (pos == x) value (lmdMap x))
  return bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
}

// \brief expands the map types of fdecls into separate scalar variables
inline Expr mkMapsDecl(Expr fdecl) {

  assert(isOpX<FDECL>(fdecl));

  bool fmap_arg = false; // there are fmap args
  ExprVector newTypes;

  Expr fname = bind::fname(fdecl);

  for (auto type : llvm::make_range(++fdecl->args_begin(), fdecl->args_end())) {
    if (isOpX<FINITE_MAP_TY>(type)) { // the type is a FiniteMap
      fmap_arg = true;
      Expr vTy = sort::finiteMapValTy(type);
      Expr ksTy = sort::finiteMapKeyTy(type);
      assert(ksTy->arity() > 0); // the map has at least one key
      auto ksIt = ksTy->args_begin();
      Expr kTy = bind::rangeTy(bind::fname(*ksIt)); // type of the key
      for (; ksIt != ksTy->args_end(); ksIt++) {
        newTypes.push_back(kTy); // new argument for key
        newTypes.push_back(vTy); // new argument for value
      }
    } else
      newTypes.push_back(type);
  }

  Expr newfname = bind::fapp(fdecl); // to go back easier, the new name
                                     // includes the old declaration
  return fmap_arg ? bind::fdecl(newfname, newTypes) : fdecl;
}

} // namespace finite_map
} // namespace op
} // namespace expr
