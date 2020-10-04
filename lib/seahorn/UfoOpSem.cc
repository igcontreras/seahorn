// Symbolic execution (loosely) based on semantics used in UFO
#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include "seahorn/UfoOpSem.hh"

#include "seahorn/Support/IteratorExtras.hh"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/Stats.hh"

#include "seadsa/Global.hh"

// For fmaps, move to a new .cc file
#include "seahorn/Expr/ExprOpFiniteMap.hh"

using namespace seadsa;
namespace seahorn {
// counters for encoding with InterProcMem option
InterMemStats g_im_stats;
unsigned FmapsMaxKeys;
} // namespace seahorn

using namespace seahorn;
using namespace llvm;

static llvm::cl::opt<bool> GlobalConstraints(
    "horn-global-constraints",
    llvm::cl::desc("Maximize the use of global (i.e., unguarded) constraints"),
    cl::init(false));

static llvm::cl::opt<bool> ArrayGlobalConstraints(
    "horn-array-global-constraints",
    llvm::cl::desc("Extend global constraints to arrays"), cl::init(false));

static llvm::cl::opt<bool> StrictlyLinear(
    "horn-strictly-la",
    llvm::cl::desc("Generate strictly Linear Arithmetic constraints"),
    cl::init(true));

static llvm::cl::opt<bool>
    EnableDiv("horn-enable-div", llvm::cl::desc("Enable division constraints."),
              cl::init(true));

static llvm::cl::opt<bool> RewriteDiv(
    "horn-rewrite-div",
    llvm::cl::desc("Rewrite division constraints to multiplications."),
    cl::init(false));

static llvm::cl::opt<bool> EnableUniqueScalars(
    "horn-singleton-aliases",
    llvm::cl::desc("Treat singleton alias sets as scalar values"),
    cl::init(false));

static llvm::cl::opt<bool> InferMemSafety(
    "horn-use-mem-safety",
    llvm::cl::desc("Rely on memory safety assumptions such as "
                   "successful load/store imply validity of their arguments"),
    cl::init(true), cl::Hidden);

static llvm::cl::opt<bool> IgnoreCalloc(
    "horn-ignore-calloc",
    llvm::cl::desc(
        "Treat calloc same as malloc, ignore that memory is initialized"),
    cl::init(false), cl::Hidden);

static llvm::cl::opt<bool>
    IgnoreMemset("horn-ignore-memset",
                 llvm::cl::desc("Ignore that memset writes into a memory"),
                 cl::init(false), cl::Hidden);

static llvm::cl::opt<bool>
    UseWrite("horn-use-write",
             llvm::cl::desc("Write to store instead of havoc"), cl::init(false),
             cl::Hidden);

static llvm::cl::opt<unsigned, true> MaxKeys(
    "horn-fmap-max-keys",
    llvm::cl::desc("Maximum number of different keys allowed in a finite map"),
    llvm::cl::location(seahorn::FmapsMaxKeys), cl::init(1));

static const Value *extractUniqueScalar(CallSite &cs) {
  if (!EnableUniqueScalars)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(cs);
}

static const Value *extractUniqueScalar(const CallInst *ci) {
  if (!EnableUniqueScalars)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(ci);
}

static bool isShadowMem(const Value &V, const Value **out) {
  const Value *scalar;
  bool res = seahorn::shadow_dsa::isShadowMem(V, &scalar);
  if (EnableUniqueScalars && out)
    *out = scalar;
  return res;
}

namespace {
struct OpSemBase {
  SymStore &m_s;
  ExprFactory &m_efac;
  UfoOpSem &m_sem;
  ExprVector &m_side;

  Expr trueE;
  Expr falseE;
  Expr zeroE;
  Expr oneE;

  /// -- current read memory
  Expr m_inMem;
  /// -- current write memory
  Expr m_outMem;
  /// --- true if the current read/write is to unique memory location
  bool m_uniq;

  /// -- parameters for a function call
  ExprVector m_fparams;

  Expr m_activeLit;

  // -- input and output parameter regions for a function call
  ExprVector m_inRegions;
  ExprVector m_outRegions;

  OpSemBase(SymStore &s, UfoOpSem &sem, ExprVector &side)
      : m_s(s), m_efac(m_s.getExprFactory()), m_sem(sem), m_side(side) {
    trueE = mk<TRUE>(m_efac);
    falseE = mk<FALSE>(m_efac);
    zeroE = mkTerm<expr::mpz_class>(0UL, m_efac);
    oneE = mkTerm<expr::mpz_class>(1UL, m_efac);
    m_uniq = false;
    resetActiveLit();
    // -- first two arguments are reserved for error flag
    m_fparams.push_back(falseE);
    m_fparams.push_back(falseE);
    m_fparams.push_back(falseE);
  }
  Expr symb(const Value &I) { return m_sem.symb(I); }

  Expr read(const Value &v) {
    return m_sem.isTracked(v) ? m_s.read(symb(v)) : Expr(0);
  }

  Expr lookup(const Value &v) { return m_sem.lookup(m_s, v); }
  Expr havoc(const Value &v) {
    return m_sem.isTracked(v) ? m_s.havoc(symb(v)) : Expr(0);
  }
  void write(const Value &v, Expr val) {
    if (val && m_sem.isTracked(v))
      m_s.write(symb(v), val);
  }

  void resetActiveLit() { m_activeLit = trueE; }
  void setActiveLit(Expr act) { m_activeLit = act; }

  // -- add conditional side condition
  void addCondSide(Expr c) { side(c, true); }

  void side(Expr v, bool conditional = false) {
    if (!v)
      return;
    if (!GlobalConstraints || conditional)
      m_side.push_back(boolop::limp(m_activeLit, v));
    else
      m_side.push_back(v);
  }

  void bside(Expr lhs, Expr rhs, bool conditional = false) {
    if (lhs && rhs)
      side(mk<IFF>(lhs, rhs), conditional);
  }

  void side(Expr lhs, Expr rhs, bool conditional = false) {
    if (lhs && rhs)
      side(mk<EQ>(lhs, rhs), conditional);
  }
};

struct OpSemVisitor : public InstVisitor<OpSemVisitor>, OpSemBase {
  OpSemVisitor(SymStore &s, UfoOpSem &sem, ExprVector &side)
      : OpSemBase(s, sem, side) {}

  /// base case. if all else fails.
  void visitInstruction(Instruction &I) { havoc(I); }

  /// skip PHI nodes
  void visitPHINode(PHINode &I) { /* do nothing */
  }

  Expr geq(Expr op0, Expr op1) {
    if (op0 == op1)
      return trueE;
    if (isOpX<MPZ>(op0) && isOpX<MPZ>(op1))
      return getTerm<expr::mpz_class>(op0) >= getTerm<expr::mpz_class>(op1)
                 ? trueE
                 : falseE;

    return mk<GEQ>(op0, op1);
  }

  Expr lt(Expr op0, Expr op1) {
    if (op0 == op1)
      return falseE;
    if (isOpX<MPZ>(op0) && isOpX<MPZ>(op1))
      return getTerm<expr::mpz_class>(op0) < getTerm<expr::mpz_class>(op1)
                 ? trueE
                 : falseE;

    return mk<LT>(op0, op1);
  }

  Expr mkUnsignedLT(Expr op0, Expr op1) {
    using namespace expr::op::boolop;

    return lite(geq(op0, zeroE), lite(geq(op1, zeroE), lt(op0, op1), trueE),
                lite(lt(op1, zeroE), lt(op0, op1), falseE));
  }

  void visitCmpInst(CmpInst &I) {
    Expr lhs = havoc(I);

    const Value &v0 = *I.getOperand(0);
    const Value &v1 = *I.getOperand(1);

    Expr op0 = lookup(v0);
    Expr op1 = lookup(v1);

    if (!(op0 && op1))
      return;

    Expr rhs;

    switch (I.getPredicate()) {
    case CmpInst::ICMP_EQ:
      rhs = mk<EQ>(op0, op1);
      break;
    case CmpInst::ICMP_NE:
      rhs = mk<NEQ>(op0, op1);
      break;
    case CmpInst::ICMP_UGT:
      rhs = mkUnsignedLT(op1, op0);
      break;
    case CmpInst::ICMP_SGT:
      if (v0.getType()->isIntegerTy(1)) {
        if (isOpX<TRUE>(op1))
          // icmp sgt op0, i1 true  == !op0
          rhs = boolop::lneg(op0);
      } else
        rhs = mk<GT>(op0, op1);
      break;
    case CmpInst::ICMP_UGE:
      rhs = mk<ITE>(mk<EQ>(op0, op1), trueE, mkUnsignedLT(op1, op0));
      break;
    case CmpInst::ICMP_SGE:
      rhs = mk<GEQ>(op0, op1);
      break;
    case CmpInst::ICMP_ULT:
      rhs = mkUnsignedLT(op0, op1);
      break;
    case CmpInst::ICMP_SLT:
      rhs = mk<LT>(op0, op1);
      break;
    case CmpInst::ICMP_ULE:
      rhs = mk<ITE>(mk<EQ>(op0, op1), trueE, mkUnsignedLT(op0, op1));
      break;
    case CmpInst::ICMP_SLE:
      rhs = mk<LEQ>(op0, op1);
      break;
    default:
      rhs = nullptr;
      break;
    }

    if (UseWrite)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitSelectInst(SelectInst &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    Expr cond = lookup(*I.getCondition());
    Expr op0 = lookup(*I.getTrueValue());
    Expr op1 = lookup(*I.getFalseValue());

    if (cond && op0 && op1) {
      Expr rhs = mk<ITE>(cond, op0, op1);

      /* avoid creating nest ite expressions by always introducing fresh
       * constants */
      if (false && UseWrite)
        write(I, rhs);
      else
        side(lhs, rhs);
    }
  }

  void visitBinaryOperator(BinaryOperator &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);

    switch (I.getOpcode()) {
    case BinaryOperator::Add:
    case BinaryOperator::Sub:
    case BinaryOperator::Mul:
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
    case BinaryOperator::Shl:
    case BinaryOperator::AShr:
    case BinaryOperator::SRem:
    case BinaryOperator::URem:
      doArithmetic(lhs, I);
      break;

    case BinaryOperator::And:
    case BinaryOperator::Or:
    case BinaryOperator::Xor:
    case BinaryOperator::LShr:
      doLogic(lhs, I);
      break;
    default:
      break;
    }
  }

  void doBitLogic(Expr lhs, BinaryOperator &i) {
    const Value &v0 = *(i.getOperand(0));
    const Value &v1 = *(i.getOperand(1));

    Expr op0 = lookup(v0);
    Expr op1 = lookup(v1);
    if (!(op0 && op1))
      return;
    Expr res;

    Expr sixteen = mkTerm<expr::mpz_class>(16UL, m_efac);
    Expr thirtytwo = mkTerm<expr::mpz_class>(32UL, m_efac);
    Expr twoToSixteenMinusOne = mkTerm<expr::mpz_class>(65535UL, m_efac);
    switch (i.getOpcode()) {
    case BinaryOperator::And: {
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(i.getOperand(1))) {
        if (ci->getBitWidth() <= 64) {
          Expr rhs;
          if (isMask_32(ci->getZExtValue())) {
            uint64_t v = ci->getZExtValue();
            rhs = mk<MOD>(op0, mkTerm<expr::mpz_class>(
                                   (unsigned long int)(v + 1), m_efac));
          }

          if (UseWrite)
            write(i, rhs);
          else
            side(lhs, rhs);
          return;
        }
      }
      // other common cases
      ExprVector val;
      // 0 & x = 0
      val.push_back(mk<IMPL>(mk<EQ>(op0, zeroE), mk<EQ>(lhs, zeroE)));
      // x & 0 = 0
      val.push_back(mk<IMPL>(mk<EQ>(op1, zeroE), mk<EQ>(lhs, zeroE)));
      // 32 & 16 == 0
      if (op1 == sixteen)
        val.push_back(mk<IMPL>(mk<EQ>(op0, thirtytwo), mk<EQ>(lhs, zeroE)));
      // x & 65535 == x (if x <= 65535)
      if (op1 == twoToSixteenMinusOne)
        val.push_back(
            mk<IMPL>(mk<LEQ>(op0, twoToSixteenMinusOne), mk<EQ>(lhs, op0)));

      // val.push_back (mk<IMPL> (mk<AND> (mk<EQ> (op0, thirtytwo),
      //                                   mk<EQ> (op1, sixteen)),
      //                          mk<EQ> (lhs, zeroE)));

      res = mknary<AND>(val);
    } break;
    case BinaryOperator::Or:
      // 0 | x = x
      res = mk<AND>(mk<IMPL>(mk<EQ>(op0, zeroE), mk<EQ>(lhs, op1)),
                    mk<IMPL>(mk<EQ>(op1, zeroE), mk<EQ>(lhs, op0)));
      break;
    case BinaryOperator::LShr:
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(&v1))
        res = doLShr(lhs, op0, ci);
      break;
    default:
      break;
    }

    addCondSide(res);
  }

  Expr doLShr(Expr lhs, Expr op1, const ConstantInt *op2) {
    if (!EnableDiv)
      return Expr(nullptr);

    uint64_t shift = op2->getValue().getZExtValue();
    unsigned long factor = 1;
    for (unsigned long i = 0; i < shift; ++i)
      factor = factor * 2;
    Expr factorE = mkTerm<expr::mpz_class>(factor, m_efac);
    if (RewriteDiv)
      return mk<IMPL>(mk<GEQ>(op1, zeroE), mk<EQ>(mk<MULT>(lhs, factorE), op1));
    else
      return mk<IMPL>(mk<GEQ>(op1, zeroE), mk<EQ>(lhs, mk<DIV>(op1, factorE)));
  }

  void doLogic(Expr lhs, BinaryOperator &I) {
    const Value &v0 = *(I.getOperand(0));
    const Value &v1 = *(I.getOperand(1));

    // only Boolean logic is supported
    if (!(v0.getType()->isIntegerTy(1) && v1.getType()->isIntegerTy(1)))
      return doBitLogic(lhs, I);

    Expr op0 = lookup(v0);
    Expr op1 = lookup(v1);

    if (!(op0 && op1))
      return;

    Expr rhs;

    switch (I.getOpcode()) {
    case BinaryOperator::And:
      rhs = mk<AND>(op0, op1);
      break;
    case BinaryOperator::Or:
      rhs = mk<OR>(op0, op1);
      break;
    case BinaryOperator::Xor:
      rhs = mk<XOR>(op0, op1);
      break;
    case BinaryOperator::LShr:
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(&v1)) {
        Expr res = doLShr(lhs, op0, ci);
        side(res);
        return;
      }
    default:
      break;
    }

    if (UseWrite)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  Expr doLeftShift(Expr op1, const ConstantInt *op2) {
    uint64_t shift = op2->getValue().getZExtValue();
    unsigned long factor = 1;
    for (unsigned long i = 0; i < shift; ++i) {
      factor = factor * 2;
    }
    return mk<MULT>(op1, mkTerm<expr::mpz_class>(factor, m_efac));
  }

  Expr doAShr(Expr lhs, Expr op1, const ConstantInt *op2) {
    if (!EnableDiv)
      return Expr(nullptr);

    uint64_t shift = op2->getValue().getZExtValue();
    unsigned long factor = 1;
    for (unsigned long i = 0; i < shift; ++i)
      factor = factor * 2;
    Expr factorE = mkTerm<expr::mpz_class>(factor, m_efac);

    if (RewriteDiv)
      return mk<EQ>(mk<MULT>(lhs, factorE), op1);
    else
      return mk<EQ>(lhs, mk<DIV>(op1, factorE));
  }

  void doArithmetic(Expr lhs, BinaryOperator &I) {
    const Value &v1 = *I.getOperand(0);
    const Value &v2 = *I.getOperand(1);

    Expr op1 = lookup(v1);
    Expr op2 = lookup(v2);

    if (!(op1 && op2))
      return;

    Expr rhs;
    switch (I.getOpcode()) {
    case BinaryOperator::Add:
      rhs = mk<PLUS>(op1, op2);
      break;
    case BinaryOperator::Sub:
      rhs = mk<MINUS>(op1, op2);
      break;
    case BinaryOperator::Mul:
      // if StrictlyLinear, then require that at least one
      // argument is a constant
      if (!StrictlyLinear || isOpX<MPZ>(op1) || isOpX<MPZ>(op2) ||
          isOpX<MPQ>(op1) || isOpX<MPQ>(op2))
        rhs = mk<MULT>(op1, op2);
      break;
    case BinaryOperator::SDiv:
    case BinaryOperator::UDiv:
      // if StrictlyLinear then require that divisor is a constant
      if (EnableDiv &&
          (!StrictlyLinear || isOpX<MPZ>(op2) || isOpX<MPQ>(op2))) {
        if (RewriteDiv) {
          side(mk<MULT>(lhs, op2), op1, true);
          return;
        } else
          rhs = mk<DIV>(op1, op2);
      }
      break;
    case BinaryOperator::SRem:
    case BinaryOperator::URem:
      // if StrictlyLinear then require that divisor is a constant
      if (EnableDiv && (!StrictlyLinear || isOpX<MPZ>(op2) || isOpX<MPQ>(op2)))
        rhs = mk<REM>(op1, op2);
      break;
    case BinaryOperator::Shl:
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(&v2))
        rhs = doLeftShift(op1, ci);
      break;
    case BinaryOperator::AShr:
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(&v2)) {
        Expr res = doAShr(lhs, op1, ci);
        side(res, true);
        return;
      }
      break;
    default:
      break;
    }

    // -- always guard division
    if (EnableDiv && (I.getOpcode() == BinaryOperator::SDiv ||
                      I.getOpcode() == BinaryOperator::UDiv ||
                      I.getOpcode() == BinaryOperator::SRem ||
                      I.getOpcode() == BinaryOperator::URem ||
                      I.getOpcode() == BinaryOperator::AShr))
      side(lhs, rhs, true);
    else if (UseWrite)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitReturnInst(ReturnInst &I) {
    // -- skip return argument of main
    if (I.getParent()->getParent()->getName().equals("main"))
      return;

    if (I.getNumOperands() > 0)
      lookup(*I.getOperand(0));
  }

  void visitBranchInst(BranchInst &I) {
    if (I.isConditional())
      lookup(*I.getCondition());
  }

  void visitTruncInst(TruncInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));

    if (!op0)
      return;

    if (I.getType()->isIntegerTy(1)) {
      // truncation to 1 bit amounts to 'is_even' predicate.
      // We handle the two most common cases: 0 -> false, 1 -> true
      side(mk<IMPL>(mk<EQ>(op0, zeroE), mk<NEG>(lhs)));
      side(mk<IMPL>(mk<EQ>(op0, oneE), lhs));

    } else if (UseWrite)
      write(I, op0);
    else
      side(lhs, op0);
  }

  void visitZExtInst(ZExtInst &I) { doExtCast(I, false); }
  void visitSExtInst(SExtInst &I) { doExtCast(I, true); }

  void visitGetElementPtrInst(GetElementPtrInst &gep) {
    if (!m_sem.isTracked(gep))
      return;
    Expr lhs = havoc(gep);

    Expr op = m_sem.ptrArith(m_s, gep);
    if (op) {
      // XXX cannot use write because lhs is further constrained below
      side(lhs, op);
      if (!InferMemSafety)
        return;

      // -- extra constraints that exclude undefined behavior
      if (!gep.isInBounds() || gep.getPointerAddressSpace() != 0)
        return;
      if (Expr base = lookup(*gep.getPointerOperand()))
        // -- base > 0 -> lhs > 0
        addCondSide(mk<OR>(mk<LEQ>(base, zeroE), mk<GT>(lhs, zeroE)));
    }
  }

  void doExtCast(CastInst &I, bool is_signed = false) {
    Expr lhs = havoc(I);
    const Value &v0 = *I.getOperand(0);
    Expr op0 = lookup(v0);

    if (!op0)
      return;

    // sext maps (i1 1) to -1
    Expr one = mkTerm<expr::mpz_class>(is_signed ? -1L : 1L, m_efac);

    if (v0.getType()->isIntegerTy(1)) {
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(&v0))
        op0 = ci->isOne() ? one : zeroE;
      else
        op0 = mk<ITE>(op0, one, zeroE);
    }

    if (UseWrite)
      write(I, op0);
    else
      side(lhs, op0);
  }

  void visitCallSite(CallSite CS) {
    assert(CS.isCall());
    const Function *f = CS.getCalledFunction();

    Instruction &I = *CS.getInstruction();
    BasicBlock &BB = *I.getParent();

    // -- unknown/indirect function call
    if (!f) {
      // XXX Use DSA and/or Devirt to handle better
      assert(m_fparams.size() == 3);
      visitInstruction(I);
      return;
    }

    const Function &F = *f;
    const Function &PF = *I.getParent()->getParent();

    // skip intrinsic functions, except for memory-related ones
    if (F.isIntrinsic() && !isa<MemIntrinsic>(&I)) {
      assert(m_fparams.size() == 3);
      return;
    }

    if (F.getName().startswith("verifier.assume")) {
      if (isa<UndefValue>(CS.getArgument(0))) {
        WARN << "`undef` in assumption: " << I << " in BB: " << BB.getName()
             << "\n";
        return;
      }

      Expr c = lookup(*CS.getArgument(0));
      if (F.getName().equals("verifier.assume.not"))
        c = boolop::lneg(c);

      assert(m_fparams.size() == 3);
      // -- assumption is only active when error flag is false
      addCondSide(boolop::lor(m_s.read(m_sem.errorFlag(BB)), c));
    } else if (F.getName().equals("calloc") && m_inMem && m_outMem &&
               m_sem.isTracked(I)) {
      havoc(I);
      assert(m_fparams.size() == 3);
      if (IgnoreCalloc)
        m_side.push_back(mk<EQ>(m_outMem, m_inMem));
      else {
        // XXX This is potentially unsound if the corresponding DSA
        // XXX node corresponds to multiple allocation sites
        errs() << "WARNING: zero-initializing DSA node due to calloc()\n";
        // TODO: add assert
        if (m_uniq) {
          side(m_outMem, zeroE);
        } else {
          m_side.push_back(mk<EQ>(
              m_outMem, op::array::constArray(sort::intTy(m_efac), zeroE)));
        }
      }
    } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(&I)) {
      if (m_inMem && m_outMem && m_sem.isTracked(*(MSI->getDest()))) {
        assert(m_fparams.size() == 3);
        if (IgnoreMemset)
          m_side.push_back(mk<EQ>(m_outMem, m_inMem));
        else {
          if (const ConstantInt *c =
                  dyn_cast<const ConstantInt>(MSI->getValue())) {
            // XXX This is potentially unsound if the corresponding DSA
            // XXX node corresponds to multiple allocation sites
            Expr val =
                mkTerm<expr::mpz_class>(expr::toMpz(c->getValue()), m_efac);
            errs() << "WARNING: initializing DSA node due to memset()\n";
            // TODO: add assert
            if (m_uniq) {
              side(m_outMem, val);
            } else {
              m_side.push_back(mk<EQ>(
                  m_outMem, op::array::constArray(sort::intTy(m_efac), val)));
            }
          }
        }
      }
    } else if (MemCpyInst *MCI = dyn_cast<MemCpyInst>(&I)) {
      m_side.push_back(mk<EQ>(m_outMem, m_inMem));
    } else if (MemMoveInst *MMI = dyn_cast<MemMoveInst>(&I)) {
      m_side.push_back(mk<EQ>(m_outMem, m_inMem));
    }
    // else if (F.getName ().equals ("verifier.assert"))
    // {
    //   Expr ein = m_s.read (m_sem.errorFlag ());
    //   Expr eout = m_s.havoc (m_sem.errorFlag ());
    //   Expr cond = lookup (*CS.getArgument (0));
    //   m_side.push_back (boolop::limp (cond,
    //                                   mk<EQ> (ein, eout)));
    //   m_side.push_back (boolop::limp (boolop::lneg (cond), eout));
    // }
    // else if (F.getName ().equals ("verifier.error"))
    //   m_side.push_back (m_s.havoc (m_sem.errorFlag ()));
    else if (m_sem.hasFunctionInfo(F)) {

      // the first three parameters are common for all the encodings
      // enabled
      m_fparams[0] = m_activeLit; // activation literal
      // error flag in
      m_fparams[1] = (m_s.read(m_sem.errorFlag(BB)));
      // error flag out
      m_fparams[2] = (m_s.havoc(m_sem.errorFlag(BB)));

      CallSiteInfo csi(CS, m_fparams);
      m_sem.execCallSite(csi, m_side, m_s);

      // reseting parameter structures
      m_fparams.clear();
      m_fparams.push_back(falseE);
      m_fparams.push_back(falseE);
      m_fparams.push_back(falseE);

      m_inRegions.clear();
      m_outRegions.clear();
    } else if (F.getName().startswith("shadow.mem")) {
      if (!m_sem.isTracked(I))
        return;

      if (F.getName().equals("shadow.mem.init")) {
        Expr mem = m_s.havoc(symb(I));
        if (PF.getName().equals("main"))
          m_sem.execMemInit(CS, mem, m_side, m_s);
      } else if (F.getName().equals("shadow.mem.load")) {
        const Value &v = *CS.getArgument(1);
        m_inMem = m_s.read(symb(v));
        m_uniq = extractUniqueScalar(CS) != nullptr;
      } else if (F.getName().equals("shadow.mem.store")) {
        m_inMem = m_s.read(symb(*CS.getArgument(1)));
        m_outMem = m_s.havoc(symb(I));
        m_uniq = extractUniqueScalar(CS) != nullptr;
      } else if (F.getName().equals("shadow.mem.global.init")) {
        m_inMem = m_s.read(symb(*CS.getArgument(1)));
        m_outMem = m_s.havoc(symb(I));
        m_side.push_back(mk<EQ>(m_outMem, m_inMem));
      } else if (F.getName().equals("shadow.mem.arg.ref"))
        m_fparams.push_back(m_s.read(symb(*CS.getArgument(1))));
      else if (F.getName().equals("shadow.mem.arg.mod")) {
        auto in_par = m_s.read(symb(*CS.getArgument(1)));
        m_fparams.push_back(in_par);
        m_inRegions.push_back(in_par);
        auto out_par = m_s.havoc(symb(I));
        m_fparams.push_back(out_par);
        m_outRegions.push_back(out_par);
      } else if (F.getName().equals("shadow.mem.arg.new"))
        m_fparams.push_back(m_s.havoc(symb(I)));
      else if (!PF.getName().equals("main") &&
               F.getName().equals("shadow.mem.in")) {
        m_s.read(symb(*CS.getArgument(1)));
      } else if (!PF.getName().equals("main") &&
                 F.getName().equals("shadow.mem.out")) {
        m_s.read(symb(*CS.getArgument(1)));
      } else if (!PF.getName().equals("main") &&
                 F.getName().equals("shadow.mem.arg.init")) {
        // m_sem.execMemInit(CS, m_s.read(symb(I)), m_side, m_s);
        // regions initialized in main are global. We want them to
        // flow to the arguments
        /* do nothing */
      } else if (PF.getName().equals("main") &&
                 F.getName().equals("shadow.mem.arg.init")) {
        // initialize the keys of the regions in the main function
        m_sem.execMemInit(CS, m_s.read(symb(I)), m_side, m_s);
      }
    } else {
      if (m_fparams.size() > 3) {

        if (m_sem.isAbstracted(*f)) {
          assert(m_inRegions.size() && m_outRegions.size());
          for (unsigned i = 0; i < m_inRegions.size(); i++) {
            addCondSide(mk<EQ>(m_outRegions[i], m_inRegions[i]));
          }
          WARN << "abstracted (unsoundly) a call to function " << F.getName()
               << " by a noop";
        } else {
          WARN << "skipping a call to " << F.getName()
               << " (maybe a recursive call?)";
          for (unsigned i = 0; i < m_inRegions.size(); i++) { // for fmaps!!
            m_side.push_back(mk<EQ>(m_outRegions[i], m_inRegions[i]));
          }
        }

        m_fparams.resize(3);
        m_inRegions.clear();
        m_outRegions.clear();
      }

      visitInstruction(*CS.getInstruction());
    }
  }

  void visitAllocaInst(AllocaInst &I) {
    if (!m_sem.isTracked(I))
      return;

    // -- alloca always returns a non-zero address
    Expr lhs = havoc(I);
    side(mk<GT>(lhs, zeroE));
  }

  // TODO: which is the right place to put these functions? I also need them in
  // the UfoOpSem
  static bool returnsArray(Expr e) {
    if (isOpX<ITE>(e))
      return returnsArray(e->right());
    else
      return bind::isArrayConst(e) || isOpX<STORE>(e);
  }

  void visitLoadInst(LoadInst &I) {
    if (InferMemSafety) {
      Value *pop = I.getPointerOperand()->stripPointerCasts();
      // -- successful load through a gep implies that the base
      // -- address of the gep is not null
      if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(pop)) {
        Expr base = lookup(*gep->getPointerOperand());
        if (base)
          addCondSide(mk<GT>(base, zeroE));
      }
    }

    if (!m_sem.isTracked(I))
      return;

    // -- define (i.e., use) the value of the instruction
    Expr lhs = havoc(I);
    if (!m_inMem)
      return;

    if (m_uniq) {
      Expr rhs = m_inMem;
      if (I.getType()->isIntegerTy(1))
        // -- convert to Boolean
        rhs = mk<NEQ>(rhs, mkTerm(expr::mpz_class(), m_efac));

      if (UseWrite)
        write(I, rhs);
      else
        side(lhs, rhs);
    } else if (Expr op0 = lookup(*I.getPointerOperand())) {
      Expr rhs = nullptr;
      if (returnsArray(m_inMem))
        rhs = op::array::select(m_inMem, op0);
      else if (finite_map::returnsFiniteMap(m_inMem)) {
        rhs = op::finite_map::get(m_inMem, op0);
      }

      if (I.getType()->isIntegerTy(1))
        // -- convert to Boolean
        rhs = mk<NEQ>(rhs, mkTerm(expr::mpz_class(), m_efac));

      side(lhs, rhs, !ArrayGlobalConstraints);
    }

    m_inMem.reset();
  }

  void visitStoreInst(StoreInst &I) {
    if (InferMemSafety) {
      Value *pop = I.getPointerOperand()->stripPointerCasts();
      // -- successful load through a gep implies that the base
      // -- address of the gep is not null
      if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(pop)) {
        Expr base = lookup(*gep->getPointerOperand());
        if (base)
          addCondSide(mk<GT>(base, zeroE));
      }
    }

    if (!m_inMem || !m_outMem)
      return;
    else if (!m_sem.isTracked(*I.getOperand(0))) { // treated as noop
      m_side.push_back(mk<EQ>(m_outMem, m_inMem));
      return;
    }

    Expr act = GlobalConstraints ? trueE : m_activeLit;
    Expr v = lookup(*I.getOperand(0));
    if (v && I.getOperand(0)->getType()->isIntegerTy(1))
      // -- convert to int
      v = boolop::lite(v, mkTerm(expr::mpz_class(1UL), m_efac),
                       mkTerm(expr::mpz_class(), m_efac));
    if (m_uniq) {
      side(m_outMem, v);
    } else {
      Expr idx = lookup(*I.getPointerOperand());
      if (idx && v) {
        Expr store;
        if (finite_map::returnsFiniteMap(m_inMem))
          store = op::finite_map::set(m_inMem, idx, v);
        else {
          assert(returnsArray(m_inMem));
          store = op::array::store(m_inMem, idx, v);
        }
        side(m_outMem, store, !ArrayGlobalConstraints);
      } else { // treat unknown memory accesses as noop
        m_side.push_back(mk<EQ>(m_outMem, m_inMem));
      }
    }

    m_inMem.reset();
    m_outMem.reset();
  }

  void visitCastInst(CastInst &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    const Value &v0 = *I.getOperand(0);

    Expr u = lookup(v0);
    if (UseWrite)
      write(I, u);
    else
      side(lhs, u);
  }

  void initGlobals(const BasicBlock &BB) {
    const Function &F = *BB.getParent();
    if (&F.getEntryBlock() != &BB)
      return;
    if (!F.getName().equals("main"))
      return;

    const Module &M = *F.getParent();
    for (const GlobalVariable &g :
         boost::make_iterator_range(M.global_begin(), M.global_end()))
      if (m_sem.isTracked(g))
        havoc(g);
  }

  void visitBasicBlock(BasicBlock &BB) {
    /// -- check if globals need to be initialized
    initGlobals(BB);

    // read the error flag to make it live
    m_s.read(m_sem.errorFlag(BB));
  }
}; // OpSemVisitor

struct OpSemPhiVisitor : public InstVisitor<OpSemPhiVisitor>, OpSemBase {
  const BasicBlock &m_dst;

  OpSemPhiVisitor(SymStore &s, UfoOpSem &sem, ExprVector &side,
                  const BasicBlock &dst)
      : OpSemBase(s, sem, side), m_dst(dst) {}

  void visitBasicBlock(BasicBlock &BB) {
    // -- evaluate all phi-nodes atomically. First read all incoming
    // -- values, then update phi-nodes all together.
    ExprVector ops;

    auto curr = BB.begin();
    if (!isa<PHINode>(curr))
      return;

    for (; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      // skip phi nodes that are not tracked
      if (!m_sem.isTracked(*phi))
        continue;
      const Value &v = *phi->getIncomingValueForBlock(&m_dst);
      ops.push_back(lookup(v));
    }

    curr = BB.begin();
    for (unsigned i = 0; isa<PHINode>(curr); ++curr) {
      PHINode &phi = *cast<PHINode>(curr);
      if (!m_sem.isTracked(phi))
        continue;
      Expr lhs = havoc(phi);
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      Expr op0 = ops[i++];
      side(lhs, op0);
    }
  }
}; // OpSemPhiVisitor
} // namespace

namespace seahorn {
Expr UfoOpSem::errorFlag(const BasicBlock &BB) {
  // -- if BB belongs to a function that cannot fail, errorFlag is always false
  if (m_canFail && !m_canFail->canFail(BB.getParent()))
    return falseE;
  return this->LegacyOperationalSemantics::errorFlag(BB);
}

Expr UfoOpSem::memStart(unsigned id) {
  Expr sort = sort::intTy(m_efac);
  return shadow_dsa::memStartVar(id, sort);
}
Expr UfoOpSem::memEnd(unsigned id) {
  Expr sort = sort::intTy(m_efac);
  return shadow_dsa::memEndVar(id, sort);
}
void UfoOpSem::exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
                    Expr act) {
  OpSemVisitor v(s, *this, side);
  v.setActiveLit(act);
  v.visit(const_cast<BasicBlock &>(bb));
  v.resetActiveLit();
}

void UfoOpSem::execPhi(SymStore &s, const BasicBlock &bb,
                       const BasicBlock &from, ExprVector &side, Expr act) {
  // act is ignored since phi node only introduces a definition
  OpSemPhiVisitor v(s, *this, side, from);
  v.setActiveLit(act);
  v.visit(const_cast<BasicBlock &>(bb));
  v.resetActiveLit();
}

Expr UfoOpSem::ptrArith(SymStore &s, GetElementPtrInst &gep) {
  Value &base = *gep.getPointerOperand();
  Expr res = lookup(s, base);
  if (!res)
    return res;

  for (auto GTI = gep_type_begin(&gep), GTE = gep_type_end(&gep); GTI != GTE;
       ++GTI) {
    if (const StructType *st = GTI.getStructTypeOrNull()) {
      if (const ConstantInt *ci =
              dyn_cast<const ConstantInt>(GTI.getOperand())) {
        Expr off = mkTerm<expr::mpz_class>(
            (unsigned long)fieldOff(st, ci->getZExtValue()), m_efac);
        res = mk<PLUS>(res, off);
      } else {
        assert(false);
      }
    } else {
      // otherwise we have a sequential type like an array or vector.
      // Multiply the index by the size of the indexed type.
      Expr sz = mkTerm<expr::mpz_class>(
          (unsigned long)storageSize(GTI.getIndexedType()), m_efac);
      res = mk<PLUS>(res, mk<MULT>(lookup(s, *GTI.getOperand()), sz));
    }
  }
  return res;
}

unsigned UfoOpSem::storageSize(const llvm::Type *t) {
  return m_td->getTypeStoreSize(const_cast<Type *>(t));
}

unsigned UfoOpSem::fieldOff(const StructType *t, unsigned field) {
  return m_td->getStructLayout(const_cast<StructType *>(t))
      ->getElementOffset(field);
}

Expr UfoOpSem::symb(const Value &I) {
  if (isa<UndefValue>(&I))
    return Expr(0);
  // assert (!isa<UndefValue>(&I));

  // -- basic blocks are mapped to Bool constants
  if (const BasicBlock *bb = dyn_cast<const BasicBlock>(&I))
    return bind::boolConst(mkTerm<const BasicBlock *>(bb, m_efac));

  // -- constants are mapped to values
  if (const Constant *cv = dyn_cast<const Constant>(&I)) {
    if (const ConstantInt *c = dyn_cast<const ConstantInt>(&I)) {
      if (c->getType()->isIntegerTy(1))
        return c->isOne() ? mk<TRUE>(m_efac) : mk<FALSE>(m_efac);
      expr::mpz_class k = toMpz(c->getValue());
      return mkTerm<expr::mpz_class>(k, m_efac);
    } else if (cv->isNullValue() || isa<ConstantPointerNull>(&I))
      return mkTerm<expr::mpz_class>(0UL, m_efac);
    else if (const ConstantExpr *ce = dyn_cast<const ConstantExpr>(&I)) {
      // -- if this is a cast, and not into a Boolean, strip it
      // -- XXX handle Boolean casts if needed
      if (ce->isCast() &&
          (ce->getType()->isIntegerTy() || ce->getType()->isPointerTy()) &&
          !ce->getType()->isIntegerTy(1))

      {
        if (const ConstantInt *val =
                dyn_cast<const ConstantInt>(ce->getOperand(0))) {
          expr::mpz_class k = toMpz(val->getValue());
          return mkTerm<expr::mpz_class>(k, m_efac);
        }
        // -- strip cast
        else
          return symb(*ce->getOperand(0));
      }
    }
  }

  // -- everything else is mapped to a constant
  Expr v = mkTerm<const Value *>(&I, m_efac);

  const Value *scalar = nullptr;
  if (isShadowMem(I, &scalar)) {
    if (scalar)
      // -- create a constant with the name v[scalar]
      return bind::intConst(
          op::array::select(v, mkTerm<const Value *>(scalar, m_efac)));

    if (m_trackLvl >= MEM) {
      Expr intTy = sort::intTy(m_efac);
      Expr ty = sort::arrayTy(intTy, intTy);
      return bind::mkConst(v, ty);
    }
  }

  if (isTracked(I))
    return I.getType()->isIntegerTy(1) ? bind::boolConst(v) : bind::intConst(v);

  return Expr(0);
}

const Value &UfoOpSem::conc(Expr v) const {
  assert(isOpX<FAPP>(v));
  // name of the app
  Expr u = bind::fname(v);
  // name of the fdecl
  u = bind::fname(u);
  assert(isOpX<VALUE>(v));
  return *getTerm<const Value *>(v);
}

bool UfoOpSem::isTracked(const Value &v) const {
  const Value *scalar = nullptr;

  if (isa<UndefValue>(v))
    return false;

  // -- shadow values represent memory regions
  // -- only track them when memory is tracked
  if (isShadowMem(v, &scalar))
    return scalar != nullptr || m_trackLvl >= MEM;

  // -- a pointer
  if (v.getType()->isPointerTy()) {
    // -- XXX A hack because shadow.mem generates not well formed
    // -- bitcode that contains future references. A register that
    // -- is defined later is used to name a shadow region in the
    // -- beginning of the function. Perhaps there is a better
    // -- solution. For now, we just do not track anything that came
    // -- that way.
    if (v.hasOneUse())
      if (const CallInst *ci = dyn_cast<const CallInst>(*v.user_begin()))
        if (const Function *fn = ci->getCalledFunction())
          if (fn->getName().startswith("shadow.mem"))
            return false;

    return m_trackLvl >= PTR;
  }

  // -- always track integer registers
  return v.getType()->isIntegerTy();
}

bool UfoOpSem::isAbstracted(const Function &fn) {
  return (m_abs_funcs.count(&fn) > 0);
}

Expr UfoOpSem::lookup(SymStore &s, const Value &v) {
  Expr u = symb(v);
  // if u is defined it is either an fapp or a constant
  if (u)
    return bind::isFapp(u) ? s.read(u) : u;
  return Expr(0);
}

void UfoOpSem::execEdg(SymStore &s, const BasicBlock &src,
                       const BasicBlock &dst, ExprVector &side) {
  exec(s, src, side, trueE);
  execBr(s, src, dst, side, trueE);
  execPhi(s, dst, src, side, trueE);

  // an edge into a basic block that does not return includes the block itself
  const auto *term = dst.getTerminator();
  if (term && isa<const UnreachableInst>(term))
    exec(s, dst, side, trueE);
}

void UfoOpSem::execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                      ExprVector &side, Expr act) {
  // the branch condition
  if (const BranchInst *br = dyn_cast<const BranchInst>(src.getTerminator())) {
    if (br->isConditional()) {
      const Value &c = *br->getCondition();
      if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&c)) {
        if ((ci->isOne() && br->getSuccessor(0) != &dst) ||
            (ci->isZero() && br->getSuccessor(1) != &dst)) {
          side.clear();
          side.push_back(boolop::limp(act, s.read(errorFlag(src))));
        }
      } else if (Expr target = lookup(s, c)) {

        Expr cond = br->getSuccessor(0) == &dst ? target : mk<NEG>(target);
        cond = boolop::lor(s.read(errorFlag(src)), cond);
        cond = boolop::limp(act, cond);
        side.push_back(cond);
      }
    }
  }
}

// internal function only for debugging (avoids duplication of code)
static void printCS(const CallSiteInfo &csi, const FunctionInfo &fi) {
  errs() << "Call instruction: " << *csi.m_cs.getInstruction() << "\n";
  errs() << "Caller: " << *csi.m_cs.getCaller() << "\n";
  errs() << "Callee: " << *csi.m_cs.getCalledFunction() << "\n";
  // errs () << "Sum predicate: " << *fi.sumPred << "\n";
  errs() << "m_fparams.size: " << csi.m_fparams.size() << "\n";
  errs() << "Domain size: " << bind::domainSz(fi.sumPred) << "\n";
  errs() << "m_fparams\n";
  for (auto r : csi.m_fparams)
    errs() << *r << "\n";
  errs() << "regions: " << fi.regions.size() << " args: " << fi.args.size()
         << " globals: " << fi.globals.size() << " ret: " << fi.ret << "\n";
  errs() << "regions\n";
  for (auto r : fi.regions)
    errs() << *r << "\n";
  errs() << "args\n";
  for (auto r : fi.args)
    errs() << *r << "\n";
  errs() << "globals\n";
  for (auto r : fi.globals)
    errs() << *r << "\n";
  if (fi.ret)
    errs() << "ret: " << *fi.ret << "\n";
}

void UfoOpSem::execCallSite(CallSiteInfo &csi, ExprVector &side, SymStore &s) {

  const FunctionInfo &fi = getFunctionInfo(*csi.m_cs.getCalledFunction());

  Instruction &I = *csi.m_cs.getInstruction();

  for (const Argument *arg : fi.args)
    csi.m_fparams.push_back(
        s.read(symb(*csi.m_cs.getArgument(arg->getArgNo()))));
  for (const GlobalVariable *gv : fi.globals)
    csi.m_fparams.push_back(s.read(symb(*gv)));

  if (fi.ret)
    csi.m_fparams.push_back(s.havoc(symb(I)));

  LOG(
      "arg_error", if (csi.m_fparams.size() != bind::domainSz(fi.sumPred)) {
        printCS(csi, fi);
      });

  assert(csi.m_fparams.size() == bind::domainSz(fi.sumPred));
  side.push_back(bind::fapp(fi.sumPred, csi.m_fparams));
}

// ------------------------------------------------------------
// MemUfoOpSem

void MemUfoOpSem::execCallSite(CallSiteInfo &csi, ExprVector &side,
                               SymStore &s) {

  const FunctionInfo &fi = getFunctionInfo(*csi.m_cs.getCalledFunction());

  GlobalAnalysis &ga = m_shadowDsa->getDsaAnalysis();
  const Function *calleeF = csi.m_cs.getCalledFunction();
  const Function *callerF = csi.m_cs.getCaller();

  LOG("inter_mem", errs() << "callee: " << calleeF->getGlobalIdentifier();
      errs() << " caller: " << callerF->getGlobalIdentifier(); errs() << "\n";);

  if (!ga.hasSummaryGraph(*calleeF)) {
    UfoOpSem::execCallSite(csi, side, s);
    return;
  }
  processShadowMemsCallSite(csi);

  CallSite &CS = csi.m_cs;
  Graph &calleeG = ga.getSummaryGraph(*calleeF);
  NodeSet &unsafeNodesCaller =
      m_preproc->getSafeNodesCallerCS(CS.getInstruction());
  SimulationMapper &simMap = m_preproc->getSimulationCS(CS);

  unsigned init_params = g_im_stats.m_params_copied; // for statistics

  // generate literals that copy for arguments and global variables
  // this needs to be done before generating the literal for the call
  for (const Argument *arg : fi.args) {
    Expr argE = s.read(symb(*CS.getArgument(arg->getArgNo())));
    csi.m_fparams.push_back(argE);
    if (calleeG.hasCell(*arg)) { // checking that the argument is a pointer
      unsigned init_fields = g_im_stats.m_fields_copied;
      recVCGenMem(calleeG.getCell(*arg), argE, unsafeNodesCaller, simMap, side);
      LOG("inter_mem_counters", g_im_stats.m_n_params++;
          if (init_fields < g_im_stats.m_fields_copied)
              g_im_stats.m_params_copied++;);
    }
  }
  for (const GlobalVariable *gv : fi.globals) {
    Expr argE = s.read(symb(*gv));
    csi.m_fparams.push_back(argE);
    const Cell &c = calleeG.getCell(*gv);
    if (hasOrigMemSymbol(c, MemOpt::IN) || hasOrigMemSymbol(c, MemOpt::OUT)) {
      unsigned init_fields = g_im_stats.m_fields_copied;
      recVCGenMem(calleeG.getCell(*gv), argE, unsafeNodesCaller, simMap, side);
      LOG("inter_mem_counters", g_im_stats.m_n_gv++;
          if (init_fields < g_im_stats.m_fields_copied)
              g_im_stats.m_gv_copied++;);
    }
  }

  LOG("inter_mem_counters", g_im_stats.m_n_callsites++;
      if (init_params < g_im_stats.m_params_copied)
          g_im_stats.m_callsites_copied++;);

  Instruction &I = *csi.m_cs.getInstruction();

  if (fi.ret)
    csi.m_fparams.push_back(s.havoc(symb(I)));

  // place the new array name according to the literals generated for the copy
  for (auto it : m_tmprep_out) {
    const auto pair = it.getFirst();
    Node *n = const_cast<Node *>(pair.first);
    Cell c(n, pair.second);
    Expr origInA = getOrigMemSymbol(c, MemOpt::IN);
    Expr replaceOutA = it.getSecond();

    LOG("inter_mem", errs() << "Replacing by "; replaceOutA->dump();
        errs() << "\n");

    for (int i = 3; i < csi.m_fparams.size(); i++) { // we can skip the first 3
      if (csi.m_fparams[i] == origInA) {
        side.push_back(mk<EQ>(csi.m_fparams[i + 1], replaceOutA));
        auto it2 = m_rep_out.find(pair);
        assert(it2 != m_rep_out.end());
        csi.m_fparams[i + 1] = it2->getSecond();
        i++;
        break;
      }
    }
  }

  LOG(
      "arg_error", if (csi.m_fparams.size() != bind::domainSz(fi.sumPred)) {
        printCS(csi, fi);
      });

  assert(csi.m_fparams.size() == bind::domainSz(fi.sumPred));

  side.push_back(bind::fapp(fi.sumPred, csi.m_fparams));

  // reset for the next callsite
  m_orig_array_in.clear();
  m_orig_array_out.clear();
  m_rep_in.clear();
  m_rep_out.clear();
  m_tmprep_in.clear();
  m_tmprep_out.clear();
}

Expr MemUfoOpSem::getOrigMemSymbol(const Cell &c, MemOpt ao) {

  CellExprMap &map = getOrigMap(ao);

  auto it = map.find({c.getNode(), m_preproc->getOffset(c)});
  LOG("inter_mem", errs() << "--> getMemSymbol\n"
                          << " " << c.getNode() << " "
                          << m_preproc->getOffset(c) << "\n";);
  assert(it != map.end()); // there should be an entry for that always
  return it->getSecond();
}

// inline?
bool MemUfoOpSem::hasOrigMemSymbol(const Cell &c, MemOpt ao) {
  CellExprMap &map = getOrigMap(ao);

  return hasExprCell(map, c);
}

void MemUfoOpSem::addCIMemSymbol(CallInst *CI, Expr A, MemOpt ao) {

  auto opt_c = m_shadowDsa->getShadowMemCell(*CI);
  assert(opt_c.hasValue());
  addMemSymbol(opt_c.getValue(), A, ao);
}

void MemUfoOpSem::addMemSymbol(const Cell &c, Expr A, MemOpt ao) {
  CellExprMap &map = getOrigMap(ao);

  LOG("inter_mem", errs() << "<-- addMemSymbol " << *A << "\n"
                          << " " << c.getNode() << " "
                          << m_preproc->getOffset(c) << "\n";);
  map.insert({{c.getNode(), m_preproc->getOffset(c)}, A});
}

Expr MemUfoOpSem::arrayVariant(Expr origE) {
  assert(bind::isArrayConst(origE));
  Expr name = bind::fname(origE);
  Expr rTy = bind::rangeTy(name);

  return bind::mkConst(variant::variant(m_copy_count++, origE), rTy);
}

Expr MemUfoOpSem::getFreshMemSymbol(const Cell &c, MemOpt ao) {

  CellExprMap *map;
  if (ao == MemOpt::IN)
    map = &m_rep_in;
  else
    map = &m_rep_out;

  auto it = map->find({c.getNode(), m_preproc->getOffset(c)});
  if (it == map->end()) { // not copied yet
    Expr origE = getOrigMemSymbol(c, ao);
    Expr copyE = arrayVariant(origE);
    map->insert({{c.getNode(), m_preproc->getOffset(c)}, copyE});
    return copyE;
  } else
    return it->getSecond();
}

void MemUfoOpSem::newTmpMemSymbol(const Cell &c, Expr &currE, Expr &newE,
                                  MemOpt ao) {

  CellExprMap *map;
  if (ao == MemOpt::IN)
    map = &m_tmprep_in;
  else
    map = &m_tmprep_out;

  Expr origE = getOrigMemSymbol(c, MemOpt::IN);
  newE = arrayVariant(origE);

  auto it = map->find({c.getNode(), m_preproc->getOffset(c)});
  if (it == map->end()) {
    if (ao == MemOpt::IN) { // for the in arrays we need an empty array
      currE = newE;
      newE = arrayVariant(origE);
    } else {
      currE = origE;
    }
    map->insert({{c.getNode(), m_preproc->getOffset(c)}, newE});
  } else {
    currE = it->getSecond();
    map->erase({c.getNode(), m_preproc->getOffset(c)});
    map->insert({{c.getNode(), m_preproc->getOffset(c)}, newE});
  }
}

static Expr addOffset(Expr ptr, unsigned offset) {
  if (offset == 0)
    return ptr;

  return mk<PLUS>(ptr, mkTerm<expr::mpz_class>(offset, ptr->efac()));
}

void MemUfoOpSem::recVCGenMem(const Cell &c_callee, Expr ptr,
                              NodeSet &unsafeNodes, SimulationMapper &simMap,
                              ExprVector &side) {

  const Node *n_callee = c_callee.getNode();

  if (n_callee->size() == 0)
    // the array was created but from the bu graph we know that it is not
    // accessed
    return;

  if (n_callee->isArray()) {
    LOG("inter_mem_counters", g_im_stats.m_node_array++;);
    return;
  }

  const Cell &c_caller = simMap.get(c_callee);
  const Node *n_caller = c_caller.getNode();

  LOG("inter_mem_counters",
      if (n_callee->isOffsetCollapsed()) g_im_stats.m_node_ocollapsed++;);

  if (!m_preproc->isSafeNode(unsafeNodes, n_caller))
    return;
  // checking modification in the bu graph, which is more precise
  // than the previous approach
  if (n_callee->isModified() && !c_callee.getNode()->types().empty()) {

    for (auto field : c_callee.getNode()->types()) {
      unsigned offset = field.getFirst();

      Cell c_callee_field(c_callee, offset);
      Cell c_caller_field = simMap.get(c_callee_field);
      if (isMemScalar(c_caller_field)) // if the field is represented with a
                                       // scalar, skip the copy
        continue;

      // create a new name for that array if it was not created
      Expr copyA = getFreshMemSymbol(c_caller_field, MemOpt::OUT);
      Expr tmpA = nullptr, nextA = nullptr;
      newTmpMemSymbol(c_caller_field, tmpA, nextA, MemOpt::OUT);

      Expr dir = addOffset(ptr, offset);
      tmpA = op::array::store(tmpA, dir, op::array::select(copyA, dir));
      side.push_back(mk<EQ>(nextA, tmpA));
      LOG("inter_mem_counters", g_im_stats.m_fields_copied++;);
    }
  }
  LOG(
      "inter_mem_counters", if (!m_preproc->isSafeNode(unsafeNodes, n_caller)) {
        g_im_stats.m_node_unsafe++;
      });

  if (n_callee->getLinks().empty())
    return;

  // -- follow the links of the node
  for (auto &links : n_callee->getLinks()) {
    const Field &f = links.first;
    const Cell &next_c = *links.second;
    const Node *next_n = next_c.getNode();

    // obtain the name of the array that represents the field
    Expr origA = getOrigMemSymbol(Cell(c_caller, f.getOffset()), MemOpt::IN);

    Expr next_ptr;
    if (OpSemVisitor::returnsArray(origA)) {
      next_ptr = op::array::select(origA, addOffset(ptr, f.getOffset()));
    } else
      next_ptr = origA; // mem represented with a scalar

    recVCGenMem(next_c, next_ptr, unsafeNodes, simMap, side);
  }
}

// TODO: this is a generic version, in this semantics checking finite
// maps is not necessary, specialize in FMapUfoOpSem?
// -- returns true of the cell is encoded with a scalar
bool MemUfoOpSem::isMemScalar(const Cell &c) {

  if (!EnableUniqueScalars)
    return false;

  Expr memE;
  if (hasOrigMemSymbol(c, MemOpt::IN))
    memE = getOrigMemSymbol(c, MemOpt::IN);
  else if (hasOrigMemSymbol(c, MemOpt::OUT))
    memE = getOrigMemSymbol(c, MemOpt::OUT);
  else {
    assert(false && "cell without mem region expression");
    return false;
  }

  return !(OpSemVisitor::returnsArray(memE) ||
           finite_map::returnsFiniteMap(memE));
}

bool MemUfoOpSem::hasExprCell(const CellExprMap &nim, const Cell &c) {
  return nim.count({c.getNode(), m_preproc->getOffset(c)}) > 0;
}

Expr MemUfoOpSem::getExprCell(const CellExprMap &nim, const Cell &c) {
  auto it = nim.find({c.getNode(), m_preproc->getOffset(c)});
  assert(it != nim.end());
  return it->getSecond();
}

Expr MemUfoOpSem::getExprCell(const CellExprMap &nim, const Node *n,
                              unsigned o) {
  auto it = nim.find({n, o});
  assert(it != nim.end());
  return it->getSecond();
}

// -- stores the name(s) of the array(s) that represents every cell involved
// in the CallSite
void MemUfoOpSem::processShadowMemsCallSite(CallSiteInfo &csi) {

  unsigned i = csi.m_fparams.size() - 1;
  Instruction *I = csi.m_cs.getInstruction()->getPrevNode();

  // traversing backwards the "shadow.mem.arg." annotations
  while (I != nullptr) {
    CallInst *ci = nullptr;
    ci = dyn_cast<CallInst>(I);
    if (ci == nullptr)
      break;

    Function *f_callee = ci->getCalledFunction();
    if (f_callee == nullptr)
      break;

    if (f_callee->getName().equals("shadow.mem.arg.ref"))
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::IN);
    else if (f_callee->getName().equals("shadow.mem.arg.mod")) {
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::OUT);
      i--;
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::IN);
    } else if (f_callee->getName().equals("shadow.mem.arg.new"))
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::IN);
    else
      break;
    I = I->getPrevNode();
    i--;
  }
}

void InterMemStats::print() {
  outs() << "BRUNCH_STAT "
         << "NumParams"
         << " " << m_n_params << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCallSites"
         << " " << m_n_callsites << "\n";
  outs() << "BRUNCH_STAT "
         << "NumGlobalV"
         << " " << m_n_gv << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCopiedBytes"
         << " " << m_fields_copied << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCopiedParams"
         << " " << m_params_copied << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCopiedGlobalV"
         << " " << m_gv_copied << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCopiedCallSites"
         << " " << m_callsites_copied << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCalleeArrayNodes"
         << " " << m_node_array << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCalleeOffsetCollapsedNodes"
         << " " << m_node_ocollapsed << "\n";
  outs() << "BRUNCH_STAT "
         << "NumCalleeUnsafeNodes"
         << " " << m_node_unsafe << "\n";
}

void InterMemStats::copyTo(InterMemStats &ims) {
  ims.m_n_params = m_n_params;
  ims.m_n_callsites = m_n_callsites;
  ims.m_n_gv = m_n_gv;
  ims.m_fields_copied = m_fields_copied;
  ims.m_params_copied = m_params_copied;
  ims.m_gv_copied = m_gv_copied;
  ims.m_callsites_copied = m_callsites_copied;
  ims.m_node_array = m_node_array;
  ims.m_node_ocollapsed = m_node_ocollapsed;
  ims.m_node_unsafe = m_node_unsafe;
}

// TODO: Move to FMapUfoOpSem.cc?

Expr FMapUfoOpSem::symb(const Value &I) {

  const Value *scalar = nullptr;

  if (isShadowMem(I, &scalar)) {
    if (!scalar) {
      if (const Instruction *i = dyn_cast<const Instruction>(&I)) {
        const Function *F = i->getParent()->getParent();

        if (const CallInst *CI = dyn_cast<const CallInst>(&I)) {
          auto opt_c = m_shadowDsa->getShadowMemCell(*CI);
          assert(opt_c.hasValue());
          const Cell &c = opt_c.getValue();
          LOG("fmap_symb", errs() << "Variable of: " << F->getName() << "\n";
              errs() << "Instruction: " << *i << "\n");
          if (m_preproc->isSafeNodeFunc(*const_cast<Node *>(c.getNode()), F)) {
            unsigned nKs = m_preproc->getNumAccesses(c, F);
            if (nKs > 0 && nKs <= MaxKeys) { // may be safe but not accessed
              ExprVector &keys = m_preproc->getKeysCell(c, F);
              Expr intTy = sort::intTy(m_efac);
              Expr fmap = bind::mkConst(mkTerm<const Value *>(&I, m_efac),
                                        sort::finiteMapTy(intTy, keys));
              LOG("fmap_symb", errs() << *fmap->left(););
              return fmap;
            }
          }
        } else if (const PHINode *PI = dyn_cast<const PHINode>(&I)) {
          Value *vPI = PI->getIncomingValue(0);
          Expr incomingConst = symb(*vPI);
          return bind::mkConst(mkTerm<const Value *>(&I, m_efac),
                               bind::rangeTy(bind::name(incomingConst)));
        }
      }
    }
  } else if (const Instruction *i = dyn_cast<const Instruction>(&I)) {
    const Function *F = i->getParent()->getParent();
    GlobalAnalysis &ga = m_shadowDsa->getDsaAnalysis();
    if (ga.hasGraph(*F)) {
      Graph &g = ga.getGraph(*F);
      if (g.hasCell(I)) {
        const Cell &c = g.getCell(I);
        if (c.getNode()->size() > 0 || c.getNode()->isOffsetCollapsed()) {
          llvm::Optional<unsigned> opt_cellId = m_shadowDsa->getCellId(c);
          if (opt_cellId.hasValue())
            return finite_map::tagCell(UfoOpSem::symb(I), opt_cellId.getValue(),
                                       c.getRawOffset());
        }
      }
    }
  }
  return UfoOpSem::symb(I);
} // namespace seahorn

// for debugging
static bool checkArgs(Expr fapp) {

  if (fapp->arity() <= 3)
    return true;

  Expr fdecl = bind::name(fapp);

  auto arg_it = ++(fapp->args_begin()), t_it = ++(fdecl->args_begin());

  for (; arg_it != fapp->args_end(); arg_it++, t_it++) {
    Expr arg = *arg_it;
    if (bind::IsConst()(arg)) {
      Expr argTy = *t_it;
      if (!isOpX<FINITE_MAP_TY>(argTy)) {
        assert(bind::rangeTy(bind::fname(arg)) == argTy);
      } else {
        assert(arg->left()->right()->right()->arity() ==
               argTy->right()->arity());
      }
    }
  }
  return true;
}

void FMapUfoOpSem::execCallSite(CallSiteInfo &csi, ExprVector &side,
                                SymStore &s) {

  const Function *calleeF = csi.m_cs.getCalledFunction();

  const FunctionInfo &fi = getFunctionInfo(*calleeF);

  GlobalAnalysis &ga = m_shadowDsa->getDsaAnalysis();

  if (!ga.hasSummaryGraph(*calleeF)) {
    UfoOpSem::execCallSite(csi, side, s);
    return;
  }
  LOG("inter_mem_fmaps",
      errs() << "callee: " << calleeF->getName()
             << "\ncaller: " << csi.m_cs.getCaller()->getName() << "\n";);

  // associates cells in the caller graph with its exprs
  processShadowMemsCallSite(csi);

  CallSite &CS = csi.m_cs;
  Graph &calleeG = ga.getSummaryGraph(*calleeF);

  NodeSet &unsafeNodesCaller =
      m_preproc->getSafeNodesCallerCS(CS.getInstruction());
  SimulationMapper &simMap = m_preproc->getSimulationCS(CS);
  m_preproc->precomputeFiniteMapTypes(CS);
  m_csInst = CS.getInstruction();

  for (const Argument *arg : fi.args) {
    Expr argE = s.read(symb(*CS.getArgument(arg->getArgNo())));
    csi.m_fparams.push_back(argE);
    // TODO: add special case for null, the keys will mismatch
    if (calleeG.hasCell(*arg)) // checking that the argument is a pointer
      VCgenCell(calleeG.getCell(*arg), argE, unsafeNodesCaller, simMap,
                *calleeF);
  }

  for (const GlobalVariable *gv : fi.globals) {
    Expr argE = s.read(symb(*gv));
    csi.m_fparams.push_back(argE);
  }

  // Copying more than necessary, the keys and values that are not reachable
  // from the live globals could be replaced by fresh consts. However, to
  // preserve the same order, to avoid having many different contexts
  // depending of the globals that are live, we are copying everything
  for (auto &kv : calleeG.globals()) {
    const Cell &c = *kv.second;
    Cell cCaller = simMap.get(c);
    if (hasOrigMemSymbol(cCaller, MemOpt::IN) ||
        hasOrigMemSymbol(cCaller, MemOpt::OUT)) {
      Expr basePtr = s.read(symb(*kv.first));
      VCgenCell(c, basePtr, unsafeNodesCaller, simMap, *calleeF);
    }
  }

  if (fi.ret) {
    Expr retE = s.havoc(symb(*csi.m_cs.getInstruction()));
    csi.m_fparams.push_back(retE);
    if (calleeG.hasCell(*fi.ret)) {
      const Cell &c = calleeG.getCell(*fi.ret); // no
      if (c.getNode()->isModified() &&
          hasOrigMemSymbol(simMap.get(c), MemOpt::OUT))
        VCgenCell(c, retE, unsafeNodesCaller, simMap, *calleeF);
    }
  }

  ExprVector arrayStores; // copies are not directly added to `side` because we
                          // want them to be active only if the function is
  for (int i = 3; i < csi.m_fparams.size(); i++) {
    Expr param = csi.m_fparams[i];
    if (hasExprKeys(param)) { // parameter that is copied
      Expr fmap = m_replace[param];
      csi.m_fparams[i] = fmap;
      assert(fmap->left()->right()->right()->arity() ==
             getExprKeys(param).size());

      LOG("fmap_opsem", errs() << "\t" << *param << " : replaced by \n "
                               << "\t    " << *fmap << "\n";);
    } else if (finite_map::returnsFiniteMap(param) &&
               isOpX<ARRAY_TY>(fi.sumPred->arg(i + 1)))
    // +1 because fi.sumpPred->arg(0) is the function name
    {
      LOG("fmap-node",
          assert(false && "Node not expected")); // oversharing
      // -- the memory region does not exist in the bu graph of the callee but
      // is still passed (as an array)
      assert(m_exprCell.count(param) > 0); // initialized when processing the
                                           // shadow.mem annotations
      // -- create a fresh array (not reachable in the callee bu)
      csi.m_fparams[i] =
          bind::mkConst(variant::variant(0, param), fi.sumPred->arg(i + 1));
      if (i < csi.m_fparams.size()) {
        Expr nextParam = csi.m_fparams[i + 1];
        if (m_exprCell[param].first == m_exprCell[nextParam].first) {
          // -- add memOut = memIn (not accessed in this function)
          if (OpSemVisitor::returnsArray(nextParam))
            arrayStores.push_back(mk<EQ>(nextParam, param));
          else
            side.push_back(mk<EQ>(nextParam, param));
          i++;
          assert(isOpX<ARRAY_TY>(fi.sumPred->arg(i + 1)));
          csi.m_fparams[i] = bind::mkConst(variant::variant(0, nextParam),
                                           fi.sumPred->arg(i + 1));
        }
      }
    }
  }

  LOG(
      "arg_error", if (csi.m_fparams.size() != bind::domainSz(fi.sumPred)) {
        printCS(csi, fi);
      });

  // TODO: it is more efficient if the definitions appear before the callsite,
  // at least for the IN case

  assert(csi.m_fparams.size() == bind::domainSz(fi.sumPred));
  assert(checkArgs(bind::fapp(fi.sumPred, csi.m_fparams)));
  side.push_back(bind::fapp(fi.sumPred, csi.m_fparams));

  ExprMap extraDefs;

  // store back in caller variables
  for (auto kv : m_replace) {
    Expr param = kv.first;
    Expr fmap = kv.second;
    if (m_fmOut.count(param) > 0) { // if it is an output mem symbol
      Expr ks = finite_map::constrainKeys(kv.second, getExprKeys(param));
      Expr store = mk<EQ>(param, m_fmOut[param]);
      if (OpSemVisitor::returnsArray(param)) {
        arrayStores.push_back(store);
        extraDefs[fmap] = ks;
      } else
        extraDefs[fmap] = mk<AND>(ks, store);
    } else
      extraDefs[fmap] = mk<EQ>(
          fmap, finite_map::constFiniteMap(getExprKeys(param), m_fmapDefault,
                                           getExprValues(param)));
  }

  // add definitions in an ordered way
  ExprSet added; // stores the definitions already added

  for (auto kv : extraDefs) {
    recAddSortedDef(kv.first, kv.second, extraDefs, added, side);
  }

  if (arrayStores.size() > 0)
    side.push_back(boolop::limp(csi.m_fparams[0], boolop::land(arrayStores)));

  // reset for the next callsite
  m_orig_array_in.clear();
  m_orig_array_out.clear();
  m_replace.clear();
  m_fmKeys.clear();
  m_fmValues.clear();
  m_fmOut.clear();
  m_exprCell.clear();
}

void FMapUfoOpSem::recAddSortedDef(const Expr map, const Expr def,
                                   const ExprMap &defs, ExprSet &added,
                                   ExprVector &side) {

  if (added.count(map) > 0)
    return;

  added.insert(map); // mark now to avoid inserting it twice
  ExprSet deps;
  filter(
      def, [](Expr e) { return finite_map::returnsFiniteMap(e); },
      std::inserter(deps, deps.begin()));

  for (auto m_it : deps) {
    auto d_it = defs.find(map);
    if (d_it != defs.end()) // defined earlier
      continue;
    recAddSortedDef(m_it, d_it->second, defs, added, side);
  }
  side.push_back(def);
}

Expr FMapUfoOpSem::fmVariant(Expr e, const ExprVector &keys) {

  assert(keys.size() > 0);
  Expr cTy = bind::rangeTy(bind::fname(e));
  Expr vTy =
      bind::isArrayConst(e) ? sort::arrayValTy(cTy) : sort::finiteMapValTy(cTy);

  return bind::mkConst(variant::variant(m_copy_count++, e),
                       sort::finiteMapTy(vTy, keys));
}

void FMapUfoOpSem::VCgenCell(const Cell &cArgCallee, Expr basePtr,
                             const NodeSet &unsafeNodesCaller,
                             SimulationMapper &sm, const Function &F) {

  recVCGenMem(cArgCallee, basePtr, basePtr, unsafeNodesCaller, sm, F);
}

void FMapUfoOpSem::recVCGenMem(const Cell &c_callee, Expr basePtrIn,
                               Expr basePtrOut, const NodeSet &unsafeNodes,
                               SimulationMapper &simMap, const Function &F) {

  if (c_callee.getNode()->types().empty())
    return;

  assert(!bind::isArrayConst(basePtrOut) &&
         !bind::isFiniteMapConst(basePtrOut));

  assert(!bind::isArrayConst(basePtrIn) && !bind::isFiniteMapConst(basePtrIn));

  const Node *n_callee = c_callee.getNode();
  const Cell &c_caller = simMap.get(c_callee);
  const Node *n_caller = c_caller.getNode();

  if (!m_preproc->isSafeNode(unsafeNodes, n_caller))
    return;

  if (m_preproc->getNumCIAccessesCellSummary(c_callee, &F) <= MaxKeys) {
    // -- copy accessed fields of the node
    for (auto field : c_callee.getNode()->types()) {
      unsigned offset = field.getFirst();

      Cell c_callee_field(c_callee, offset);
      Cell c_caller_field = simMap.get(c_callee_field);

      // -- if the field is represented with a
      // scalar, or it has 0 accesses skip the copy
      if (isMemScalar(c_caller_field) ||
          m_preproc->getNumCIAccessesCellSummary(c_callee_field, &F) == 0)
        continue;

      if (hasOrigMemSymbol(c_caller_field, MemOpt::IN)) {
        // force creation of a new mem symbol for later
        getFreshMapSymbol(c_caller_field, c_callee_field, MemOpt::IN);
        addKeyVal(c_caller_field, basePtrIn, offset, MemOpt::IN);
      }
      if (hasOrigMemSymbol(c_caller_field, MemOpt::OUT)) {
        Expr readFrom =
            getFreshMapSymbol(c_caller_field, c_callee_field, MemOpt::OUT);
        storeVal(c_caller_field, readFrom, basePtrOut, offset);
      }
    }
  }

  if (n_callee->getLinks().empty())
    return;

  // -- follow the links of the node
  for (auto &links : n_callee->getLinks()) {
    const Field &f = links.first;
    const Cell &next_c = *links.second;
    const Node *next_n = next_c.getNode();

    const Cell nextCaller(c_caller, f.getOffset());

    Expr origIn = hasOrigMemSymbol(nextCaller, MemOpt::IN)
                      ? getOrigMemSymbol(nextCaller, MemOpt::IN)
                      : getOrigMemSymbol(nextCaller, MemOpt::OUT);
    Expr origOut = hasOrigMemSymbol(nextCaller, MemOpt::OUT)
                       ? getOrigMemSymbol(nextCaller, MemOpt::OUT)
                       : origIn;

    unsigned offset = f.getOffset();
    Expr nextPtrIn = memObtainValue(origIn, addOffset(basePtrIn, offset));
    Expr nextPtrOut = memObtainValue(origOut, addOffset(basePtrOut, offset));
    // out already copied in the fields loop
    recVCGenMem(next_c, nextPtrIn, nextPtrOut, unsafeNodes, simMap, F);
  }
}

// \brief obtains the value of an offset of an expr that represents a memory
// region (looking at the type)
Expr FMapUfoOpSem::memObtainValue(Expr mem, Expr offset) {

  if (OpSemVisitor::returnsArray(mem))
    return op::array::select(mem, offset);
  else if (finite_map::returnsFiniteMap(mem))
    return op::finite_map::get(mem, offset);
  else // mem represented as scalar
    return mem;
}

// \brief stores a value in an offset of an expr that represents a memory
// region (looking at the type)
Expr FMapUfoOpSem::memSetValue(Expr mem, Expr offset, Expr v) {

  if (OpSemVisitor::returnsArray(mem))
    // TODO: a = ite(old == new, a, store(a, idx, new)
    return op::array::store(mem, offset, v);
  else if (finite_map::returnsFiniteMap(mem))
    return op::finite_map::set(mem, offset, v);
  else {
    assert(false && "unexpected copy to scalar");
    return mk<EQ>(mem, v);
  }
}

// \brief if a cell is read in an offset, we store the offset's key and value
// to be included later in the definition of the new finite map (with is the
// same as copying them).
void FMapUfoOpSem::addKeyVal(Cell c, Expr basePtr, unsigned offset, MemOpt ao) {
  Expr orig = getOrigMemSymbol(c, ao);
  Expr dir = addOffset(basePtr, offset);
  getExprKeys(orig).push_back(dir);
  getExprValues(orig).push_back(memObtainValue(orig, dir));
}

// \brief if a cell is written in an offset, we need to create a new finite
// map variable for it, store the offset's key and value, and copy the value
// back to the original mem symbol in the caller (`m_fmOut`).
void FMapUfoOpSem::storeVal(Cell c, Expr readFrom, Expr basePtr,
                            unsigned offset) {

  Expr out = getOrigMemSymbol(c, MemOpt::OUT);
  Expr dir = addOffset(basePtr, offset);

  Expr origMem;
  if (hasOrigMemSymbol(c, MemOpt::IN)) // the cell is read and written
    origMem = getOrigMemSymbol(c, MemOpt::IN);
  else { // the cell is only written, we create empty mem region
    Expr origMemOut = arrayVariant(getOrigMemSymbol(c, MemOpt::OUT));
    origMem = arrayVariant(origMemOut);
  }

  // -- store in the original in mem if it is the first store or else in the
  //    previous term for storing
  Expr storeAt = (m_fmOut.count(out) == 0) ? origMem : m_fmOut[out];
  // LOG("inter_mem_fmaps", errs() << "Storing at: " << *storeAt
  //                               << "\n\t from: " << *readFrom << "\n";);
  Expr value = memObtainValue(readFrom, dir);

  m_fmOut[out] = memSetValue(storeAt, dir, value); // additional stores

  getExprKeys(out).push_back(dir); // for the definition
  getExprValues(out).push_back(bind::intConst(variant::variant(0, value)));
  // we don't care about this variable, it will
  // only appear once in the body, we are creating
  // this map definition only to unify the keys
  // later
}

Expr FMapUfoOpSem::getFreshMapSymbol(const Cell &cCaller, const Cell &cCallee,
                                     MemOpt ao) {

  Expr origE = getOrigMemSymbol(cCaller, ao);

  if (m_replace.count(origE) == 0) { // not copied yet
    Expr newE = fmVariant(origE, m_preproc->getKeysCellCS(cCallee, m_csInst));
    m_replace[origE] = newE;
    return newE;
  } else
    return m_replace[origE];
}

// differs from MemUfoOpSem in the 'shadow.mem.arg.new' -> change there
// (requires changing the vcgen)
void FMapUfoOpSem::processShadowMemsCallSite(CallSiteInfo &csi) {

  unsigned i = csi.m_fparams.size() - 1;
  Instruction *I = csi.m_cs.getInstruction()->getPrevNode();

  // traversing backwards the "shadow.mem.arg." annotations
  while (I != nullptr) {
    CallInst *ci = nullptr;
    ci = dyn_cast<CallInst>(I);
    if (ci == nullptr)
      break;

    Function *f_callee = ci->getCalledFunction();
    if (f_callee == nullptr)
      break;
    else if (f_callee->getName().equals("shadow.mem.arg.ref"))
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::IN);
    else if (f_callee->getName().equals("shadow.mem.arg.mod")) {
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::OUT);
      i--;
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::IN);
    } else if (f_callee->getName().equals("shadow.mem.arg.new"))
      addCIMemSymbol(ci, csi.m_fparams[i], MemOpt::OUT);
    else
      break;
    I = I->getPrevNode();
    i--;
  }
}

void FMapUfoOpSem::processInitShadowMemsFunction(Instruction *I,
                                                 CellExprMap &nim,
                                                 SymStore &s) {

  while (I != nullptr) {
    CallInst *ci = nullptr;
    ci = dyn_cast<CallInst>(I);
    if (ci == nullptr)
      break;

    Function *f_callee = ci->getCalledFunction();
    if (f_callee == nullptr)
      break;
    else if (f_callee->getName().equals("shadow.mem.arg.init") ||
             f_callee->getName().equals("shadow.mem.init")) {
      auto opt_c = m_shadowDsa->getShadowMemCell(*ci);
      assert(opt_c.hasValue());
      Expr memE = s.havoc(symb(*I)); // TODO: change to read?
      Cell &c = opt_c.getValue();
      nim.insert({{c.getNode(), m_preproc->getOffset(c)}, memE});
    } else
      break;
    I = I->getNextNode();
  }
}

void FMapUfoOpSem::storeSymInitInstruction(Instruction *I, CellExprMap &nim,
                                           Expr memE) {

  CallInst *ci = nullptr;
  ci = dyn_cast<CallInst>(I);
  assert(ci);
  auto opt_c = m_shadowDsa->getShadowMemCell(*ci);
  assert(opt_c.hasValue());
  Cell &c = opt_c.getValue();
  nim.insert({{c.getNode(), m_preproc->getOffset(c)}, memE});
}

void FMapUfoOpSem::execMemInit(CallSite &CS, Expr memE, ExprVector &side,
                               SymStore &s) {

  const Function &F = *CS.getCaller();
  CellExprMap &nim = getNodeSymFunction(F);
  // store sym of init instruction
  Instruction *I = CS.getInstruction();
  storeSymInitInstruction(I, nim, memE);

  // if it is the last init instruction
  I = I->getNextNode();
  CallInst *ci = dyn_cast<CallInst>(I);
  if (ci) {
    Function *f_callee = ci->getCalledFunction();
    if (f_callee && (f_callee->getName().equals("shadow.mem.arg.init") ||
                     f_callee->getName().equals("shadow.mem.init")))
      return;
  }
  // add the constraints after processing all shadow.mem.arg.init and
  // shadow.mem.init

  const FunctionInfo &fi = getFunctionInfo(F);

  CellKeysMap &ckm = getCellKeysFunction(F);
  ckm.clear();

  GlobalAnalysis &ga = m_shadowDsa->getDsaAnalysis();
  // obtain simulation
  SimulationMapper &sm = m_preproc->getSimulationF(&F);
  Graph &buG = ga.getSummaryGraph(F);
  Graph &sasG = ga.getGraph(F);
  NodeSet &safe = m_preproc->getSafeNodes(&F);

  for (const Argument &arg : F.args()) {
    if (buG.hasCell(arg)) { // checking that the argument is a pointer
      Expr argE = s.read(symb(arg));
      recCollectReachableKeys(buG.getCell(arg), F, argE, safe, sm, ckm, nim);
    }
  }
  // assign a key to every distinct cell of every memory region of main
  // starting from the globals, cache the results to be reused

  for (auto &kv : buG.globals()) {
    Expr argE = s.read(symb(*kv.first));
    const Cell &c = *kv.second;
    recCollectReachableKeys(c, F, argE, safe, sm, ckm, nim);
  }

  if (fi.ret) {
    Expr retE = s.read(symb(*CS.getInstruction()));
    if (buG.hasCell(*fi.ret)) {
      const Cell &c = buG.getCell(*fi.ret); // no
      recCollectReachableKeys(c, F, retE, safe, sm, ckm, nim);
    }
  }

  LOG("fmaps_mem_init",
      errs() << "--- adding inits for: " << F.getName() << "\n";);
  ExprMap defs;
  for (auto kv : ckm) {
    auto c = kv.first; // pair of node and offset
    const Node *n = c.first;
    unsigned offset = c.second;
    Expr memE = getExprCell(nim, n, offset);
    assert(kv.second.size() > 0); // more than one key
    defs[memE] = finite_map::constrainKeys(memE, kv.second);
    LOG("fmaps_mem_init",
        errs() << "def: " << *memE << ": " << *defs[memE] << "\n";);
  }

  // add definitions in an ordered way
  ExprSet added;
  for (auto kv : defs) {
    recAddSortedDef(kv.first, kv.second, defs, added, side);
  }
  LOG("fmaps_mem_init", errs()
                            << "--- end inits for: " << F.getName() << "\n";);
}

void FMapUfoOpSem::recCollectReachableKeys(const Cell &cBU, const Function &F,
                                           Expr basePtr, const NodeSet &safeNs,
                                           SimulationMapper &sm,
                                           CellKeysMap &ckm, CellExprMap &nim) {

  const Node *nBU = cBU.getNode();

  if (nBU->types().empty())
    return;

  const Cell &cSAS = sm.get(cBU);
  const Node *nSAS = cSAS.getNode();

  if (!m_preproc->isSafeNode(safeNs, nSAS))
    return;

  if (m_preproc->getNumAccesses(cSAS, &F) <= MaxKeys) {
    ExprVector &keysN = ckm[{
        cSAS.getNode(), m_preproc->getOffset(cSAS)}]; // creates the vector if
                                                      // it doesn't exist yet

    for (auto field : cBU.getNode()->types()) {
      unsigned offset = field.getFirst();
      Cell cBU_field(cBU, offset);
      Cell cSAS_field = sm.get(cBU_field);
      // -- if the field is represented with a
      // scalar, or it has 0 accesses skip the field
      if (m_preproc->getNumCIAccessesCellSummary(cBU_field, &F) == 0)
        continue;
      keysN.push_back(addOffset(basePtr, offset));
    }
  }

  if (nBU->getLinks().empty())
    return;

  // -- follow the links of the node
  for (auto &links : nBU->getLinks()) {
    const Field &f = links.first;
    const Cell &next_c = *links.second;
    const Node *next_n = next_c.getNode();
    const Cell nextSAS(cSAS, f.getOffset());

    if (!hasExprCell(nim, nextSAS))
      continue;

    Expr memS = getExprCell(nim, nextSAS);
    Expr nextPtr = memObtainValue(memS, addOffset(basePtr, f.getOffset()));
    recCollectReachableKeys(next_c, F, nextPtr, safeNs, sm, ckm, nim);
  }
}

void FMapUfoOpSem::addMemSymbol(const Cell &c, Expr A, MemOpt ao) {

  m_exprCell[A] = {c.getNode(), c.getOffset()};
  MemUfoOpSem::addMemSymbol(c, A, ao);
}

} // namespace seahorn
