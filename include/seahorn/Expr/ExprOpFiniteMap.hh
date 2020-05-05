/// Finite Maps
#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class FiniteMapOpKind { CONST_FINITE_MAP, SET, GET };
/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP, "defk", FUNCTIONAL, FiniteMapOp)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp)

} // namespace op

namespace op {
namespace finite_map {

inline Expr constFiniteMap(ExprVector &keys) {
  return expr::mknary<CONST_FINITE_MAP>(keys.begin(), keys.end());
}
inline Expr get(Expr map, Expr idx) {
  return expr::mk<GET>(map, idx);
}
inline Expr set(Expr map, Expr idx, Expr v) {
  return expr::mk<SET>(map, idx, v);
}

// fresh map with unitialized values
inline Expr empty_map_lambda(ExprFactory &efac) {
  return mkTerm<expr::mpz_class>(0, efac);
  // TODO: change 0 by the same as unitialized memory
}

// creates a set of keys as a lambda function
inline Expr make_lambda_map_keys(ExprVector &keys, ExprFactory &efac) {

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr lmd_bot = bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                                   mkTerm<expr::mpz_class>(0, efac));
  // up to here, it will be the same for all keysets

  int count = 1;

  Expr lmd_tmp = lmd_bot;

  for (auto key : keys) {
    Expr nA = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(key, x);
    Expr ite = boolop::lite(cmp, nA, op::bind::betaReduce(lmd_tmp, x));
    lmd_tmp = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  return lmd_tmp;
}

// creates a map for keys and values, assuming that they are sorted
//
// TO COMMENT: This function also outputs the lambda function for the keys,
// assume that it is created, is this a bigger formula if done externally?
inline Expr make_map_batch_values(ExprVector &keys, ExprVector &values,
                                  ExprFactory &efac, Expr &lambda_keys) {

  // assuming that there is a value for every key. If this is not available,
  // "initialize" it with the default value for uninitialized memory
  assert(keys.size() == values.size());

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr lmd_bot = bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                                   mkTerm<expr::mpz_class>(0, efac));
  int count = 1;
  Expr lmd_tmp = lmd_bot;

  for (auto key : keys) {
    Expr nA = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(key, x);
    Expr ite = boolop::lite(cmp, nA, op::bind::betaReduce(lmd_tmp, x));
    lmd_tmp = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  lambda_keys = lmd_tmp;

  count = 1;

  Expr lmd_values = empty_map_lambda(efac);

  for (auto v : values) {
    Expr pos_in_map = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(x, pos_in_map);
    Expr ite =
        boolop::lite(cmp, v, op::bind::betaReduce(lmd_values, x));
    lmd_values = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  return lmd_values;
}

inline Expr get_map_lambda(Expr map, Expr keys, Expr key) {

  Expr pos_in_map = op::bind::betaReduce(keys, key);

  return op::bind::betaReduce(map, pos_in_map);
}

inline Expr set_map_lambda(Expr map, Expr keys, Expr key, Expr value,
                           ExprFactory &efac) {

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr pos_in_map = op::bind::betaReduce(keys, key);
  Expr cmp = mk<EQ>(x, pos_in_map);
  Expr ite = boolop::lite(cmp, value, op::bind::betaReduce(map, pos_in_map));
  Expr new_map = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);

  return new_map;
}

inline Expr make_variant_key(Expr m1, Expr k) {
  // TODO: replace by |get(m1,k)|
  return bind::intConst(variant::tag(m1, k));
}

// check that one maps contains the same values as another. Both maps are
// assumed to have the same keys `keys` but not necessarily in the same order,
// that is why `ks1` and `ks2` are needed.
inline Expr make_eq_maps_lambda(Expr m1, Expr ks1, Expr m2, Expr ks2,
                                ExprVector &keys, ExprFactory &efac,
                                ExprSet &evars) {

  ExprVector conj;

  bool is_var_m1 = bind::isFiniteMapConst(m1);
  bool is_var_m2 = bind::isFiniteMapConst(m2);

  Expr e_m1, e_m2;

  for (auto k : keys) {
    if (is_var_m1) {
      e_m1 = make_variant_key(m1, k);
      evars.insert(e_m1);
    }
    else
      e_m1 = get_map_lambda(m1, ks1, k);

    if(is_var_m2) {
      e_m2 = make_variant_key(m2, k);
      evars.insert(e_m2);
    }
    else
      e_m2 = get_map_lambda(m2, ks2, k);
    conj.push_back(mk<EQ>(e_m1, e_m2));
  }
  return mknary<AND>(conj);
}

inline void expand_map_vars(Expr map, Expr lmdks, ExprVector &keys, ExprVector &new_vars,
                            ExprVector &extra_unifs, ExprFactory &efac,
                            ExprSet &evars) {

  Expr v, v_get;

  for (auto k : keys) {
    v = make_variant_key(map, k);
    evars.insert(v);
    if (evars.count(k) > 0) // TODO: maybe not necessary?
      evars.insert(k);

    new_vars.push_back(k);
    new_vars.push_back(v);

    v_get = get_map_lambda(map, lmdks, k);
    extra_unifs.push_back(mk<EQ>(v, v_get));
  }

}

// This function is just for testing
inline Expr make_map_sequence_gets(ExprVector &keys, ExprVector &values,
                                   ExprFactory &efac, Expr &lambda_keys) {

  assert(keys.size() == values.size());

  lambda_keys = make_lambda_map_keys(keys, efac);

  Expr lmd_values = empty_map_lambda(efac);

  auto it_v = values.begin();

  for (auto k : keys) {
    lmd_values = set_map_lambda(lmd_values, lambda_keys, k, *it_v, efac);
    it_v++;
  }

  return lmd_values;
}

// Takes a map (input and output), the used keys (assumed to be the same for
// input and output) and generates the parameters necessary to encode this map
// (`new_params`) and returns the extra literals that need to be performed in
// the caller.
// This function needs to be called per map

// new vars will be added to `evars`
//
// TODO: make sure that the new variable names are not duplicated, how do I
// get them?
// int g_var_eqs_maps_count = 0; // TODO: remove this counter, just for testing
// purposes to not duplicate names
inline Expr prepare_finite_maps_caller_callsite(Expr in_map, Expr map_keys,
                                                ExprVector &keys_used,
                                                ExprFactory &efac,
                                                ExprVector &new_params,
                                                Expr &out_map) {

  assert(keys_used.size() > 0); // if not, nothing to do? or return literals
                                // with true

  int count = 1;
  // TODO
  Expr BASE_IN_MAP_NAME = mkTerm<std::string>("map_in", efac);
  Expr BASE_OUT_MAP_NAME = mkTerm<std::string>("map_out", efac);
  Expr iTy = mk<INT_TY>(efac);

  ExprVector extra_lits, out_values;

  for (auto k : keys_used) {
    new_params.push_back(k);
    Expr vin = bind::mkConst(variant::variant(count, BASE_IN_MAP_NAME), iTy);
    new_params.push_back(vin);

    Expr vout = bind::mkConst(variant::variant(count, BASE_OUT_MAP_NAME), iTy);
    new_params.push_back(vout);

    extra_lits.push_back(
        mk<EQ>(vin, finite_map::get_map_lambda(in_map, map_keys, k)));
    out_values.push_back(vout);
    count++;
  }

  Expr out_map_keys;
  // TODO: out_map_keys is not necessary, we can pass it as a parameter instead
  // of outputing it from make_map_batch_values, now we are duplicating work
  out_map = finite_map::make_map_batch_values(keys_used, out_values, efac,
                                              out_map_keys);

  return mknary<AND>(extra_lits);
}

// TODO: review how heads are built
// Expr prepare_finite_map_head(Expr in_map, Expr out_map, Expr map_keys,
//                              ExprVector keys_used, ExprVector values,
//                              ExprFactory &efac) {
//   Expr call;
//   return call;
// }

} // namespace finite_map
} // namespace op
}