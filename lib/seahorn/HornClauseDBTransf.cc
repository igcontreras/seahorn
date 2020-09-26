#include "seahorn/HornClauseDBTransf.hh"

#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/FiniteMapTransf.hh"

// to simplify
#include "seahorn/Expr/Smt/EZ3.hh"

#include "seahorn/Expr/TypeChecker.hh"

#include "seahorn/Support/SeaDebug.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
    FmapSimplify("horn-fmap-simp",
                 llvm::cl::desc("Simplify after removal of finite maps"),
                 llvm::cl::init(false));

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
                 mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(0UL), efac)),
                         mk<NEG>(arg))));
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

template <typename Set, typename Predicate>
void copy_if(Set &src, Set &dst, Predicate shouldCopy) {
  for (auto it : src)
    if (shouldCopy(it))
      dst.insert(it);
}

// -- tdb is an empty db that will contain db after transformation
void removeFiniteMapsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb,
                                       EZ3 &zctx) {
  ScopedStats _st_("HornFmaps");

  ExprFactory &efac = tdb.getExprFactory();
  ExprMap predDeclTransf;

  Stats::start("FiniteMapTransfArgs");
  // Remove Finite Maps arguments
  for (auto &predIt : db.getRelations()) {

    Expr newPredDecl;
    if (predIt->arity() < 2) // just return type?, is this assumption correct?
      newPredDecl = predIt;
    else {
      // create new relation declaration
      newPredDecl = finite_map::mkMapsDecl(predIt);

      if (newPredDecl != predIt)
        predDeclTransf[predIt] = newPredDecl;
    }
    tdb.registerRelation(newPredDecl); // register relation in transformed db
  }

  LOG("print_fmap_arg_clauses", errs() << "------- FMAPS CLAUSE DB ------\n";);

  TypeChecker tc;
  for (const auto &rule : db.getRules()) {
    const ExprVector &vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    DagVisitCache dvc; // TODO: same for all the clauses?
    FiniteMapArgsVisitor fmav(allVars, predDeclTransf, efac);

    Expr ruleE;
    if (isOpX<TRUE>(rule.body()))
      // HACK for the transformation (forcing not simplifying implication)
      ruleE = mk<IMPL>(rule.body(), rule.head());
    else
      ruleE = rule.get();

    LOG("print_fmap_arg_clauses", errs() << *ruleE << "\n\n";);

    Expr newRuleE = visit(fmav, ruleE, dvc);
    HornRule newRule(allVars, newRuleE);

    LOG(
        "fmap_check_types", errs() << "Transforming: " << *rule.get() << "\n";
        if (tc.typeOf(rule.get()) == sort::errorTy(efac)) {
          errs() << *tc.getErrorExp() << "\n";
        } errs()
        << "Transformed: " << *newRule.get() << "\n";
        if (tc.typeOf(newRule.get()) == sort::errorTy(efac)) {
          errs() << *tc.getErrorExp() << "\n";
        });

    tdb.addRule(newRule);
  }

  // copy queries
  for (auto &q : db.getQueries())
    tdb.addQuery(q);

  Stats::stop("FiniteMapTransfArgs");

  Stats::start("FiniteMapTransfBody");
  // Remove Finite Maps from Bodies
  std::vector<HornRule> worklist;
  boost::copy(tdb.getRules(), std::back_inserter(worklist));

  ZSimplifier<EZ3> zsimp(zctx);
  zsimp.params().set("pull_cheap_ite", true);
  zsimp.params().set("ite_extra_rules", true);
  zsimp.params().set("flat", false);
  zsimp.params().set("som", false);

  LOG("print_fmap_body_clauses",
      errs() << "------- FMAPS NO ARGS CLAUSE DB ------\n";);

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    DagVisitCache dvc;
    FiniteMapBodyVisitor fmv(allVars, efac, zsimp);

    Expr body = visit(fmv, rule.body(), dvc);

    ExprSet newVars;
    copy_if(allVars, newVars, [](Expr expr) { // not finite map
      return !bind::isFiniteMapConst(expr);
    });

    HornRule newRule(newVars, rule.head(), body);

    LOG(
        "fmap_check_types", errs() << "Transforming: " << *rule.get() << "\n";
        if (tc.typeOf(rule.get()) == sort::errorTy(efac)) {
          errs() << *tc.getErrorExp() << "\n";
        } errs()
        << "Transformed: " << *newRule.get() << "\n";
        if (tc.typeOf(newRule.get()) == sort::errorTy(efac)) {
          errs() << *tc.getErrorExp() << "\n";
        });
    LOG("print_fmap_body_clauses", errs() << *rule.get() << "\n\n";);

    tdb.removeRule(rule);
    tdb.addRule(newRule);
  }

  LOG("print_clauses", errs() << "------- TRANSFORMED CLAUSE DB ------\n";
      for (auto &cl
           : tdb.getRules()) cl.get()
          ->dump(););
  Stats::stop("FiniteMapTransfBody");

  if (FmapSimplify) {

    EZ3 z3(efac);

    std::vector<HornRule> worklist;
    boost::copy(tdb.getRules(), std::back_inserter(worklist));

    for (auto rule : worklist) {

      Expr simpBody = z3_simplify(z3, rule.body()); // run it on the body
      Expr simpRule = mk<IMPL>(rule.body(), rule.head());

      const ExprVector &rvars = rule.vars();
      ExprSet simpVars(rvars.begin(), rvars.end());

      tdb.removeRule(rule);
      tdb.addRule(simpVars, simpRule);
    }
  }
}

} // namespace seahorn
