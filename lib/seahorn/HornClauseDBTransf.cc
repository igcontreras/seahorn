#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/Expr/Expr.hh"

#include "seahorn/FiniteMapTransf.hh"

namespace seahorn {
using namespace expr;

// Return a new Horn rule whose head only has variables
HornRule replaceNonVarsInHead(const HornRule &rule) {
  Expr h = rule.head();
  assert(bind::isFapp(h));
  ExprFactory &efac = h->efac();

  auto it = ++(h->args_begin());
  auto end = h->args_end();
  Expr new_body = mk<TRUE>(efac);
  ExprVector new_args, new_vars;
  unsigned int id = 0;
  for (; it != end; ++it) {
    Expr arg = *it;
    if (isOpX<GT>(arg) || isOpX<GEQ>(arg) || isOpX<LT>(arg) ||
        isOpX<LEQ>(arg) || isOpX<EQ>(arg) || isOpX<NEQ>(arg)) {
      std::string vname("VAR_");
      vname += boost::lexical_cast<std::string>(++id);
      Expr v = bind::intConst(mkTerm<std::string>(vname, efac));
      new_body = boolop::land(
          new_body,
          mk<OR>(mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(1UL), efac)), arg),
                 mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(0UL), efac)), mk<NEG>(arg))));
      new_args.push_back(v);
      new_vars.push_back(v);
    } else if (isOpX<PLUS>(arg) || isOpX<MINUS>(arg) || isOpX<MULT>(arg) ||
               isOpX<DIV>(arg) || isOpX<MPQ>(arg) || isOpX<MPZ>(arg)) {
      std::string vname("VAR_");
      vname += boost::lexical_cast<std::string>(++id);
      Expr v = bind::intConst(mkTerm<std::string>(vname, efac));
      new_body = boolop::land(new_body, mk<EQ>(v, arg));
      new_args.push_back(v);
      new_vars.push_back(v);
    } else {
      new_args.push_back(arg);
    }
  }
  Expr head = bind::fapp(*(h->args_begin()), new_args);
  Expr body = boolop::land(new_body, rule.body());

  boost::copy(rule.vars(), std::back_inserter(new_vars));
  HornRule new_rule(new_vars, head, body);
  return new_rule;
}

void normalizeHornClauseHeads(HornClauseDB &db) {
  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  for (auto rule : worklist) {
    HornRule new_rule = replaceNonVarsInHead(rule);
    db.removeRule(rule);
    db.addRule(new_rule);
  }
}

template <typename Set, typename Predicate> void erase_if(Set &s, Predicate shouldRemove) {
  for(auto it = s.begin(); it!=s.end();){
    if(shouldRemove(*it)){
      it = s.erase(it);
    }
    else {
      ++it;
    }
  }
}
// -- tdb is an empty db that will contain db after transformation
void removeFiniteMapsArgsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb) {

  ExprFactory &efac = tdb.getExprFactory();
  ExprMap predDeclTransf;

  for (auto predIt : db.getRelations()) {
    Expr predDecl = predIt;

    Expr newPredDecl;
    if (predDecl->arity() < 2) // just only return?, is this assumption correct?
      newPredDecl = predDecl;
    else{
      // create new relation declaration
      newPredDecl = finite_map::mkMapsDecl(predDecl, efac);

      if (newPredDecl != predDecl)
        predDeclTransf[predDecl] = newPredDecl;
    }
    tdb.registerRelation(newPredDecl); // register relation in transformed db
  }

  for (const auto rule : db.getRules()){
    const ExprVector &vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    DagVisitCache dvc; // same for all the clauses??
    FiniteMapArgsVisitor fmav(efac, allVars, predDeclTransf);
    Expr newRule = visit(fmav, rule.get(),dvc);

    erase_if(
        allVars, [](Expr expr) {
            return isOpX<FINITE_MAP_TY>(bind::rangeTy(bind::fname(expr)));
        });

    tdb.addRule(allVars, newRule);
  }
}

void removeFiniteMapsBodiesHornClausesTransf(HornClauseDB &db) {

  ExprFactory &efac = db.getExprFactory();

  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    DagVisitCache dvc; // same for all the clauses??
    FiniteMapBodyVisitor fmv(db.getExprFactory(), allVars);

    erase_if(
        allVars, [](Expr expr) {
            return isOpX<FINITE_MAP_TY>(bind::rangeTy(bind::fname(expr)));
        });

   HornRule new_rule(allVars, rule.head(), visit(fmv, rule.body(), dvc));

    db.removeRule(rule);
    db.addRule(new_rule);
  }
}

} // namespace seahorn
