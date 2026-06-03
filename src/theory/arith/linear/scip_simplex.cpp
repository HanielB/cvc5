/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision procedure for the real relaxation in linear arithmetic based on
 * the SCIP exact rational solver.
 */

#include "theory/arith/linear/scip_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/error_set.h"
#include "theory/arith/linear/linear_equality.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/arith/linear/tableau.h"
#include "util/statistics_registry.h"

#ifdef CVC5_USE_SCIP
#include <lpiexact/lpiexact.h>
#include <scip/def.h>
#include <scip/rational.h>
#ifndef CVC5_CLN_IMP
#include <scip/rationalgmp.h>
#endif /* CVC5_CLN_IMP */
#ifndef _WIN32
#include <fcntl.h>
#include <unistd.h>
#endif /* _WIN32 */
#endif /* CVC5_USE_SCIP */

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ScipSimplexDecisionProcedure::ScipSimplexDecisionProcedure(
    Env& env,
    LinearEqualityModule& linEq,
    ErrorSet& errors,
    RaiseConflict conflictChannel,
    RaiseBlackBoxConflict bbConflictChannel,
    TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_bbConflictChannel(bbConflictChannel),
      d_statistics(statisticsRegistry())
{
}

ScipSimplexDecisionProcedure::Statistics::Statistics(StatisticsRegistry& sr)
    : d_queueTime(sr.registerTimer("theory::arith::scip::queueTime")),
      d_conflicts(sr.registerInt("theory::arith::scip::conflicts")),
      d_scipTime(sr.registerTimer("theory::arith::scip::solveTime")),
      d_scipCalls(sr.registerInt("theory::arith::scip::calls")),
      d_scipSat(sr.registerInt("theory::arith::scip::sat")),
      d_scipUnsat(sr.registerInt("theory::arith::scip::unsat")),
      d_scipUnknown(sr.registerInt("theory::arith::scip::unknown")),
      d_subsetConflicts(sr.registerInt("theory::arith::scip::subsetConflicts")),
      d_fallbackConflicts(
          sr.registerInt("theory::arith::scip::fallbackConflicts")),
      d_auxSolves(sr.registerInt("theory::arith::scip::auxSolves"))
{
}

Result::Status ScipSimplexDecisionProcedure::findModel(
    CVC5_UNUSED bool exactResult)
{
  // Note that in contrast to the pivot-based procedures, SCIP always solves
  // the problem completely, i.e. exactResult does not limit the search.
  Assert(d_conflictVariables.empty());
  d_pivots = 0;

  if (d_errorSet.errorEmpty() && !d_errorSet.moreSignals())
  {
    Trace("arith::findModel") << "scipFindModel() trivial" << endl;
    return Result::SAT;
  }

  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if (processSignals())
  {
    d_conflictVariables.purge();
    Trace("arith::findModel") << "scipFindModel() early conflict" << endl;
    return Result::UNSAT;
  }
  else if (d_errorSet.errorEmpty())
  {
    Trace("arith::findModel") << "scipFindModel() fixed itself" << endl;
    return Result::SAT;
  }

  Trace("arith::findModel") << "scipFindModel() start non-trivial" << endl;

#ifdef CVC5_USE_SCIP
  return solveWithScip();
#else
  Unreachable() << "cvc5 was not compiled with SCIP support";
#endif
}

void ScipSimplexDecisionProcedure::collectAllBounds(
    ConstraintCPVec& bounds) const
{
  for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                    vend = d_variables.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    if (d_variables.hasLowerBound(v))
    {
      bounds.push_back(d_variables.getLowerBoundConstraint(v));
    }
    if (d_variables.hasUpperBound(v))
    {
      bounds.push_back(d_variables.getUpperBoundConstraint(v));
    }
  }
}

Result::Status ScipSimplexDecisionProcedure::raiseConflictOver(
    const ConstraintCPVec& bounds)
{
  // The conjunction of the given bound constraints (together with the
  // tableau equalities, which are definitional) is infeasible. Raise the
  // conjunction as a black box conflict.
  Assert(!bounds.empty());
  Node conflict = Constraint::externalExplainByAssertions(nodeManager(), bounds);
  Trace("arith::scip") << "scip conflict (" << bounds.size()
                       << " bounds): " << conflict << endl;
  d_bbConflictChannel.raiseConflict(conflict);
  return Result::UNSAT;
}

#if defined(CVC5_USE_SCIP) && !defined(CVC5_CLN_IMP)

namespace {

/** Converts a SCIP rational to a cvc5 Rational. Must not be infinite. */
Rational scipRationalToRational(SCIP_RATIONAL* r)
{
  Assert(!SCIPrationalIsAbsInfinity(r));
  return Rational(mpq_class(*SCIPrationalGetGMP(r)));
}

/**
 * Temporarily silences the standard output and error streams at the file
 * descriptor level. The underlying LP solver of SCIP (SoPlex) writes some
 * diagnostics directly to the standard streams, bypassing the message
 * handlers; such output must not pollute cvc5's output channels.
 */
class StreamSilencer
{
 public:
  StreamSilencer()
  {
#ifndef _WIN32
    std::cout.flush();
    std::cerr.flush();
    fflush(stdout);
    fflush(stderr);
    d_savedOut = dup(STDOUT_FILENO);
    d_savedErr = dup(STDERR_FILENO);
    int devNull = open("/dev/null", O_WRONLY);
    if (devNull >= 0)
    {
      dup2(devNull, STDOUT_FILENO);
      dup2(devNull, STDERR_FILENO);
      close(devNull);
    }
#endif /* _WIN32 */
  }

  ~StreamSilencer()
  {
#ifndef _WIN32
    fflush(stdout);
    fflush(stderr);
    if (d_savedOut >= 0)
    {
      dup2(d_savedOut, STDOUT_FILENO);
      close(d_savedOut);
    }
    if (d_savedErr >= 0)
    {
      dup2(d_savedErr, STDERR_FILENO);
      close(d_savedErr);
    }
#endif /* _WIN32 */
  }

 private:
  int d_savedOut = -1;
  int d_savedErr = -1;
};

/** RAII owner of an array of SCIP rationals. */
class ScipRationalArray
{
 public:
  ScipRationalArray(int size) : d_size(size)
  {
    if (SCIPrationalCreateArray(&d_array, size) != SCIP_OKAY)
    {
      d_array = nullptr;
    }
  }

  ~ScipRationalArray()
  {
    if (d_array != nullptr)
    {
      SCIPrationalFreeArray(&d_array, d_size);
    }
  }

  SCIP_RATIONAL** get() { return d_array; }
  SCIP_RATIONAL* operator[](int i) { return d_array[i]; }

 private:
  SCIP_RATIONAL** d_array = nullptr;
  int d_size;
};

}  // namespace

/**
 * RAII owner of an exact LP interface instance together with the rationals
 * created for it, and the maps attributing the LP columns and rows to the
 * arithmetic variables and bound constraints they encode.
 */
struct ScipSimplexProblem
{
  SCIP_LPIEXACT* d_lpi = nullptr;
  /** All created rationals (freed on destruction). */
  std::vector<SCIP_RATIONAL*> d_rats;

  /** The arithmetic variables of the encoded system. */
  std::vector<ArithVar> d_avars;
  /** Map from ArithVar to its LP column index. */
  std::vector<int> d_toCol;
  /** The column of the variable realizing the infinitesimal delta, or -1. */
  int d_deltaCol = -1;
  /** Whether any included bound is strict. */
  bool d_haveDelta = false;
  /** The number of LP columns. */
  int d_ncols = 0;
  /**
   * Per LP row, the asserted bound constraint it encodes, or NullConstraint
   * for the definitional tableau rows.
   */
  std::vector<ConstraintCP> d_rowOrigin;
  /**
   * Whether the last solve ended in an infeasible LP, for which a dual
   * Farkas ray is available.
   */
  bool d_lastWasFarkas = false;

  ~ScipSimplexProblem()
  {
    for (SCIP_RATIONAL*& r : d_rats)
    {
      if (r != nullptr)
      {
        SCIPrationalFree(&r);
      }
    }
    if (d_lpi != nullptr)
    {
      SCIPlpiExactFree(&d_lpi);
    }
  }

  /** Creates a rational owned by this problem, or nullptr on failure. */
  SCIP_RATIONAL* mkRat()
  {
    SCIP_RATIONAL* r = nullptr;
    if (SCIPrationalCreate(&r) != SCIP_OKAY)
    {
      return nullptr;
    }
    d_rats.push_back(r);
    return r;
  }

  /** Creates a rational with the value of the given cvc5 Rational. */
  SCIP_RATIONAL* mkRat(const Rational& q)
  {
    SCIP_RATIONAL* r = mkRat();
    if (r != nullptr)
    {
      SCIPrationalSetGMP(r, q.getValue().get_mpq_t());
    }
    return r;
  }
};

/** Evaluates to retval if a SCIP call fails. */
#define CVC5_SCIP_CALL_RET(x, retval)                                  \
  do                                                                   \
  {                                                                    \
    SCIP_RETCODE cvc5_scip_rc = (x);                                   \
    if (cvc5_scip_rc != SCIP_OKAY)                                     \
    {                                                                  \
      warning() << "SCIP call '" << #x << "' failed with return code " \
                << cvc5_scip_rc << std::endl;                          \
      return retval;                                                   \
    }                                                                  \
  } while (0)

/** Evaluates to retval if a rational could not be allocated. */
#define CVC5_SCIP_CHECK_RAT_RET(r, retval)                         \
  do                                                               \
  {                                                                \
    if ((r) == nullptr)                                            \
    {                                                              \
      warning() << "SCIP rational allocation failed" << std::endl; \
      return retval;                                               \
    }                                                              \
  } while (0)

#define CVC5_SCIP_CALL_FALSE(x) CVC5_SCIP_CALL_RET(x, false)
#define CVC5_SCIP_CHECK_RAT_FALSE(r) CVC5_SCIP_CHECK_RAT_RET(r, false)

bool ScipSimplexDecisionProcedure::buildLp(ScipSimplexProblem& p,
                                           const ConstraintCPVec* filter)
{
  // The bound constraints to include in the system.
  std::unordered_set<ConstraintCP> included;
  if (filter != nullptr)
  {
    included.insert(filter->begin(), filter->end());
  }
  auto isIncluded = [&included, filter](ConstraintCP c) {
    return filter == nullptr || included.find(c) != included.end();
  };

  // Collect the variables of the current system.
  ArithVar maxVar = 0;
  for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                    vend = d_variables.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    p.d_avars.push_back(v);
    maxVar = v > maxVar ? v : maxVar;
  }

  // Detect whether any included bound is strict, i.e. has a nonzero delta
  // component.
  for (ArithVar v : p.d_avars)
  {
    if ((d_variables.hasLowerBound(v)
         && isIncluded(d_variables.getLowerBoundConstraint(v))
         && !d_variables.getLowerBound(v).infinitesimalIsZero())
        || (d_variables.hasUpperBound(v)
            && isIncluded(d_variables.getUpperBoundConstraint(v))
            && !d_variables.getUpperBound(v).infinitesimalIsZero()))
    {
      p.d_haveDelta = true;
      break;
    }
  }

  CVC5_SCIP_CALL_FALSE(SCIPlpiExactCreate(
      &p.d_lpi, nullptr, "cvc5_linear_arith", SCIP_OBJSEN_MAXIMIZE));

  SCIP_RATIONAL* posInf = p.mkRat();
  CVC5_SCIP_CHECK_RAT_FALSE(posInf);
  SCIPrationalSetInfinity(posInf);
  SCIP_RATIONAL* negInf = p.mkRat();
  CVC5_SCIP_CHECK_RAT_FALSE(negInf);
  SCIPrationalSetNegInfinity(negInf);
  SCIP_RATIONAL* zero = p.mkRat();
  CVC5_SCIP_CHECK_RAT_FALSE(zero);
  SCIPrationalSetReal(zero, 0.0);
  SCIP_RATIONAL* one = p.mkRat();
  CVC5_SCIP_CHECK_RAT_FALSE(one);
  SCIPrationalSetReal(one, 1.0);

  // One free column per arithmetic variable, plus the delta column if any
  // included bound is strict. Delta realizes the infinitesimal of strict
  // bounds as an LP variable in [0,1] whose value is maximized (the only
  // nonzero objective coefficient): the delta-rational system is satisfiable
  // iff the exact maximum of delta is positive [cf. Dutertre and de Moura,
  // CAV 2006, Lemma 1]. Note that this LP solves the real relaxation:
  // integrality is enforced by the layer above this decision procedure.
  p.d_toCol.assign(maxVar + 1, -1);
  p.d_ncols = static_cast<int>(p.d_avars.size()) + (p.d_haveDelta ? 1 : 0);
  {
    std::vector<SCIP_RATIONAL*> obj(p.d_ncols, zero);
    std::vector<SCIP_RATIONAL*> lb(p.d_ncols, negInf);
    std::vector<SCIP_RATIONAL*> ub(p.d_ncols, posInf);
    int col = 0;
    for (ArithVar v : p.d_avars)
    {
      p.d_toCol[v] = col++;
    }
    if (p.d_haveDelta)
    {
      p.d_deltaCol = col;
      obj[col] = one;
      lb[col] = zero;
      ub[col] = one;
    }
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddCols(p.d_lpi,
                                             p.d_ncols,
                                             obj.data(),
                                             lb.data(),
                                             ub.data(),
                                             nullptr,
                                             0,
                                             nullptr,
                                             nullptr,
                                             nullptr));
  }

  // Translate the included variable bounds. All bounds are encoded as
  // explicit LP rows (not as column bounds) so that the dual Farkas ray
  // attributes infeasibility to individual bound constraints. A bound with
  // value c + k*delta on x becomes the row x {>=,<=} c (k = 0) or
  // x - k*delta {>=,<=} c (k != 0).
  int beg[1] = {0};
  for (ArithVar v : p.d_avars)
  {
    for (bool lower : {true, false})
    {
      if (lower ? !d_variables.hasLowerBound(v)
                : !d_variables.hasUpperBound(v))
      {
        continue;
      }
      ConstraintCP bc = lower ? d_variables.getLowerBoundConstraint(v)
                              : d_variables.getUpperBoundConstraint(v);
      if (!isIncluded(bc))
      {
        continue;
      }
      const DeltaRational& b = lower ? d_variables.getLowerBound(v)
                                     : d_variables.getUpperBound(v);
      SCIP_RATIONAL* c = p.mkRat(b.getNoninfinitesimalPart());
      CVC5_SCIP_CHECK_RAT_FALSE(c);
      int nnonz = 1;
      int ind[2] = {p.d_toCol[v], 0};
      SCIP_RATIONAL* val[2] = {one, nullptr};
      if (!b.infinitesimalIsZero())
      {
        // Strict bounds are expected to tighten: positive delta coefficient
        // on lower bounds, negative on upper bounds.
        Assert(b.infinitesimalSgn() == (lower ? 1 : -1));
        SCIP_RATIONAL* minusK = p.mkRat(-b.getInfinitesimalPart());
        CVC5_SCIP_CHECK_RAT_FALSE(minusK);
        ind[1] = p.d_deltaCol;
        val[1] = minusK;
        nnonz = 2;
      }
      SCIP_RATIONAL* lhs[1] = {lower ? c : negInf};
      SCIP_RATIONAL* rhs[1] = {lower ? posInf : c};
      CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddRows(
          p.d_lpi, 1, lhs, rhs, nullptr, nnonz, beg, ind, val));
      p.d_rowOrigin.push_back(bc);
    }
  }

  // Translate the tableau: for each basic variable b with row entries
  // (coeff_i, x_i), add the equality (sum_i coeff_i * x_i) - b = 0, where the
  // entry of b itself is skipped (cf. LinearEqualityModule::computeRowValue).
  for (Tableau::BasicIterator bi = d_tableau.beginBasic(),
                              bend = d_tableau.endBasic();
       bi != bend;
       ++bi)
  {
    ArithVar basic = *bi;
    std::vector<int> ind;
    std::vector<SCIP_RATIONAL*> val;
    ind.push_back(p.d_toCol[basic]);
    SCIP_RATIONAL* minusOne = p.mkRat(Rational(-1));
    CVC5_SCIP_CHECK_RAT_FALSE(minusOne);
    val.push_back(minusOne);
    for (Tableau::RowIterator ri = d_tableau.basicRowIterator(basic);
         !ri.atEnd();
         ++ri)
    {
      const Tableau::Entry& entry = *ri;
      ArithVar nb = entry.getColVar();
      if (nb == basic)
      {
        continue;
      }
      SCIP_RATIONAL* coeff = p.mkRat(entry.getCoefficient());
      CVC5_SCIP_CHECK_RAT_FALSE(coeff);
      ind.push_back(p.d_toCol[nb]);
      val.push_back(coeff);
    }
    SCIP_RATIONAL* lhs[1] = {zero};
    SCIP_RATIONAL* rhs[1] = {zero};
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddRows(p.d_lpi,
                                             1,
                                             lhs,
                                             rhs,
                                             nullptr,
                                             static_cast<int>(ind.size()),
                                             beg,
                                             ind.data(),
                                             val.data()));
    p.d_rowOrigin.push_back(NullConstraint);
  }

  return true;
}

#define CVC5_SCIP_CALL_UNKNOWN(x) \
  CVC5_SCIP_CALL_RET(x, ScipSolveResult::UNKNOWN)
#define CVC5_SCIP_CHECK_RAT_UNKNOWN(r) \
  CVC5_SCIP_CHECK_RAT_RET(r, ScipSolveResult::UNKNOWN)

ScipSimplexDecisionProcedure::ScipSolveResult
ScipSimplexDecisionProcedure::solveLp(ScipSimplexProblem& p)
{
  p.d_lastWasFarkas = false;
  // Solve. The standard streams are silenced during solving since SoPlex
  // writes some diagnostics directly to them.
  SCIP_RETCODE solveRc;
  {
    StreamSilencer silencer;
    solveRc = SCIPlpiExactSolveDual(p.d_lpi);
  }
  CVC5_SCIP_CALL_UNKNOWN(solveRc);

  if (SCIPlpiExactIsOptimal(p.d_lpi))
  {
    if (p.d_haveDelta)
    {
      // The strict system is satisfiable iff the optimum of delta is
      // positive.
      SCIP_RATIONAL* objval = p.mkRat();
      CVC5_SCIP_CHECK_RAT_UNKNOWN(objval);
      CVC5_SCIP_CALL_UNKNOWN(SCIPlpiExactGetObjval(p.d_lpi, objval));
      Trace("arith::scip") << "scip delta optimum positive: "
                           << (SCIPrationalIsPositive(objval) != 0) << endl;
      if (!SCIPrationalIsPositive(objval))
      {
        return ScipSolveResult::INFEASIBLE;
      }
    }
    return ScipSolveResult::FEASIBLE;
  }
  if (SCIPlpiExactIsPrimalInfeasible(p.d_lpi))
  {
    p.d_lastWasFarkas = SCIPlpiExactHasDualRay(p.d_lpi);
    return ScipSolveResult::INFEASIBLE;
  }
  Trace("arith::scip") << "scip lp inconclusive" << endl;
  return ScipSolveResult::UNKNOWN;
}

#define CVC5_SCIP_CALL(x) CVC5_SCIP_CALL_RET(x, Result::UNKNOWN)
#define CVC5_SCIP_CHECK_RAT(r) CVC5_SCIP_CHECK_RAT_RET(r, Result::UNKNOWN)

Result::Status ScipSimplexDecisionProcedure::importModel(ScipSimplexProblem& p)
{
  // Import the exact solution into the partial model by updating the
  // nonbasic variables; the values of the basic variables follow from the
  // tableau (cf. AttemptSolutionSDP::attempt).
  ScipRationalArray primsol(p.d_ncols);
  if (primsol.get() == nullptr)
  {
    return Result::UNKNOWN;
  }
  CVC5_SCIP_CALL(SCIPlpiExactGetSol(
      p.d_lpi, nullptr, primsol.get(), nullptr, nullptr, nullptr));
  for (ArithVar v : p.d_avars)
  {
    if (d_tableau.isBasic(v))
    {
      continue;
    }
    DeltaRational dr(scipRationalToRational(primsol[p.d_toCol[v]]));
    if (d_variables.getAssignment(v) != dr)
    {
      Trace("arith::scip") << "scip model: " << v << " <- " << dr << endl;
      d_linEq.update(v, dr);
    }
  }

  d_errorSet.reduceToSignals();
  if (processSignals())
  {
    // This should not happen for a correct SCIP model; handled defensively.
    d_conflictVariables.purge();
    Trace("arith::scip") << "scip model import found conflict" << endl;
    return Result::UNSAT;
  }
  else if (d_errorSet.errorEmpty())
  {
    return Result::SAT;
  }
  // The imported model did not satisfy all bounds; this indicates a
  // discrepancy between the LP encoding and the partial model. Be defensive
  // and give up rather than report an incorrect result.
  warning() << "SCIP model import left bound violations; returning unknown"
            << std::endl;
  d_errorSet.reduceToSignals();
  ++d_statistics.d_scipUnknown;
  return Result::UNKNOWN;
}

bool ScipSimplexDecisionProcedure::extractCandidates(
    ScipSimplexProblem& p, ConstraintCPVec& candidates)
{
  // The certificate of infeasibility is the exact dual Farkas ray if the LP
  // itself was infeasible. If instead the LP was optimal with a zero delta
  // maximum, the certificate is the exact optimal dual solution: it proves
  // the objective bound (max delta <= 0), and remains a valid such proof
  // when all rows with zero multiplier are dropped. Either way, the bound
  // rows in the support of the certificate form an infeasible subset of the
  // delta-rational system (together with the definitional tableau rows,
  // which are not part of explanations).
  int nrows = static_cast<int>(p.d_rowOrigin.size());
  ScipRationalArray duals(nrows);
  if (duals.get() == nullptr)
  {
    return false;
  }
  if (p.d_lastWasFarkas)
  {
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactGetDualfarkas(p.d_lpi, duals.get()));
  }
  else
  {
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactGetSol(
        p.d_lpi, nullptr, nullptr, duals.get(), nullptr, nullptr));
  }
  size_t nbounds = 0;
  for (int i = 0; i < nrows; ++i)
  {
    if (p.d_rowOrigin[i] == NullConstraint)
    {
      continue;
    }
    ++nbounds;
    if (!SCIPrationalIsZero(duals[i]))
    {
      candidates.push_back(p.d_rowOrigin[i]);
    }
  }
  Trace("arith::scip") << "scip dual certificate candidates: "
                       << candidates.size() << " of " << nbounds << " bounds"
                       << endl;
  return !candidates.empty() && candidates.size() < nbounds;
}

Result::Status ScipSimplexDecisionProcedure::raiseScipConflict(
    ScipSimplexProblem& p)
{
  ConstraintCPVec candidates;
  if (extractCandidates(p, candidates))
  {
    // The ray is exact, so its support is a genuine infeasible subset. In
    // assertion builds this is double-checked by an exact re-solve
    // restricted to the subset.
#ifdef CVC5_ASSERTIONS
    {
      ScipSimplexProblem pv;
      ++d_statistics.d_auxSolves;
      Assert(buildLp(pv, &candidates)
             && solveLp(pv) == ScipSolveResult::INFEASIBLE)
          << "SCIP conflict subset failed exact verification";
    }
#endif /* CVC5_ASSERTIONS */
    ++d_statistics.d_subsetConflicts;
    return raiseConflictOver(candidates);
  }

  // Fall back to the full bound set, which is infeasible by the main solve.
  ConstraintCPVec all;
  collectAllBounds(all);
  ++d_statistics.d_fallbackConflicts;
  return raiseConflictOver(all);
}

Result::Status ScipSimplexDecisionProcedure::solveWithScip()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_scipTime);
  ++d_statistics.d_scipCalls;

  ScipSimplexProblem p;
  if (!buildLp(p, nullptr))
  {
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }
  switch (solveLp(p))
  {
    case ScipSolveResult::FEASIBLE:
      ++d_statistics.d_scipSat;
      return importModel(p);
    case ScipSolveResult::INFEASIBLE:
      ++d_statistics.d_scipUnsat;
      return raiseScipConflict(p);
    case ScipSolveResult::UNKNOWN:
    default:
      ++d_statistics.d_scipUnknown;
      return Result::UNKNOWN;
  }
}

#undef CVC5_SCIP_CALL
#undef CVC5_SCIP_CHECK_RAT
#undef CVC5_SCIP_CALL_UNKNOWN
#undef CVC5_SCIP_CHECK_RAT_UNKNOWN
#undef CVC5_SCIP_CALL_FALSE
#undef CVC5_SCIP_CHECK_RAT_FALSE
#undef CVC5_SCIP_CALL_RET
#undef CVC5_SCIP_CHECK_RAT_RET

#elif defined(CVC5_USE_SCIP)

Result::Status ScipSimplexDecisionProcedure::solveWithScip()
{
  Unreachable()
      << "The SCIP-based simplex requires cvc5 to be built with GMP (not CLN)";
}

#endif /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
