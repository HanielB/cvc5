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
#include <scip/cons_exactlinear.h>
#include <scip/scip.h>
#include <scip/scip_exact.h>
#include <scip/scipdefplugins.h>
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
      d_coarseConflicts(sr.registerInt("theory::arith::scip::coarseConflicts"))
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

Result::Status ScipSimplexDecisionProcedure::raiseCoarseConflict(
    const std::vector<ArithVar>& vars)
{
  // The conjunction of all asserted bound constraints (together with the
  // tableau equalities, which are definitional) is infeasible. Raise the
  // conjunction as a black box conflict. This is sound but not minimal.
  ConstraintCPVec bounds;
  for (ArithVar v : vars)
  {
    if (d_variables.hasLowerBound(v))
    {
      bounds.push_back(d_variables.getLowerBoundConstraint(v));
    }
    if (d_variables.hasUpperBound(v))
    {
      bounds.push_back(d_variables.getUpperBoundConstraint(v));
    }
  }
  Assert(!bounds.empty());
  Node conflict = Constraint::externalExplainByAssertions(nodeManager(), bounds);
  Trace("arith::scip") << "scip coarse conflict: " << conflict << endl;
  d_bbConflictChannel.raiseConflict(conflict);
  ++d_statistics.d_coarseConflicts;
  return Result::UNSAT;
}

#if defined(CVC5_USE_SCIP) && !defined(CVC5_CLN_IMP)

namespace {

/**
 * RAII owner of a SCIP instance together with the variable handles and
 * rationals created for it.
 */
struct ScipProblem
{
  SCIP* d_scip = nullptr;
  std::vector<SCIP_VAR*> d_vars;
  std::vector<SCIP_RATIONAL*> d_rats;

  ~ScipProblem()
  {
    for (SCIP_VAR*& v : d_vars)
    {
      if (v != nullptr)
      {
        SCIPreleaseVar(d_scip, &v);
      }
    }
    for (SCIP_RATIONAL*& r : d_rats)
    {
      if (r != nullptr)
      {
        SCIPrationalFree(&r);
      }
    }
    if (d_scip != nullptr)
    {
      SCIPfree(&d_scip);
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

/** Converts a SCIP rational to a cvc5 Rational. Must not be infinite. */
Rational scipRationalToRational(SCIP_RATIONAL* r)
{
  Assert(!SCIPrationalIsAbsInfinity(r));
  return Rational(mpq_class(*SCIPrationalGetGMP(r)));
}

/**
 * Temporarily silences the standard output and error streams at the file
 * descriptor level. The underlying LP solver of SCIP (SoPlex) writes some
 * diagnostics directly to the standard streams, bypassing SCIP's message
 * handler; such output must not pollute cvc5's output channels.
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

}  // namespace

/** Returns Result::UNKNOWN if a SCIP call fails. */
#define CVC5_SCIP_CALL(x)                                                  \
  do                                                                       \
  {                                                                        \
    SCIP_RETCODE cvc5_scip_rc = (x);                                       \
    if (cvc5_scip_rc != SCIP_OKAY)                                         \
    {                                                                      \
      warning() << "SCIP call '" << #x << "' failed with return code "     \
                << cvc5_scip_rc << std::endl;                              \
      ++d_statistics.d_scipUnknown;                                        \
      return Result::UNKNOWN;                                              \
    }                                                                      \
  } while (0)

/** Returns Result::UNKNOWN if a rational could not be allocated. */
#define CVC5_SCIP_CHECK_RAT(r)               \
  do                                         \
  {                                          \
    if ((r) == nullptr)                      \
    {                                        \
      warning() << "SCIP rational allocation failed" << std::endl; \
      ++d_statistics.d_scipUnknown;          \
      return Result::UNKNOWN;                \
    }                                        \
  } while (0)

Result::Status ScipSimplexDecisionProcedure::solveWithScip()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_scipTime);
  ++d_statistics.d_scipCalls;

  // Collect the variables of the current system.
  std::vector<ArithVar> avars;
  ArithVar maxVar = 0;
  for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                    vend = d_variables.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    avars.push_back(v);
    maxVar = v > maxVar ? v : maxVar;
  }

  // Detect whether any bound is strict, i.e. has a nonzero delta component.
  bool haveDelta = false;
  for (ArithVar v : avars)
  {
    if ((d_variables.hasLowerBound(v)
         && !d_variables.getLowerBound(v).infinitesimalIsZero())
        || (d_variables.hasUpperBound(v)
            && !d_variables.getUpperBound(v).infinitesimalIsZero()))
    {
      haveDelta = true;
      break;
    }
  }

  ScipProblem p;
  CVC5_SCIP_CALL(SCIPcreate(&p.d_scip));
  SCIP* scip = p.d_scip;
  // silence all console output before doing anything else
  SCIPsetMessagehdlrQuiet(scip, TRUE);
  CVC5_SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));
  // Exact solving must be enabled before the problem is created.
  CVC5_SCIP_CALL(SCIPenableExactSolving(scip, TRUE));
  CVC5_SCIP_CALL(SCIPincludeDefaultPlugins(scip));
  CVC5_SCIP_CALL(SCIPcreateProbBasic(scip, "cvc5_linear_arith"));

  SCIP_RATIONAL* posInf = p.mkRat();
  CVC5_SCIP_CHECK_RAT(posInf);
  SCIPrationalSetInfinity(posInf);
  SCIP_RATIONAL* negInf = p.mkRat();
  CVC5_SCIP_CHECK_RAT(negInf);
  SCIPrationalSetNegInfinity(negInf);
  SCIP_RATIONAL* zero = p.mkRat();
  CVC5_SCIP_CHECK_RAT(zero);
  SCIPrationalSetReal(zero, 0.0);
  SCIP_RATIONAL* one = p.mkRat();
  CVC5_SCIP_CHECK_RAT(one);
  SCIPrationalSetReal(one, 1.0);

  // One continuous SCIP variable per arithmetic variable. Note that this
  // solves the real relaxation: integrality is enforced by the layer above
  // this decision procedure (branch and bound).
  std::vector<SCIP_VAR*> toScipVar(maxVar + 1, nullptr);
  for (ArithVar v : avars)
  {
    SCIP_VAR* sv = nullptr;
    std::string name = "v" + std::to_string(v);
    CVC5_SCIP_CALL(SCIPcreateVarBasic(scip,
                                      &sv,
                                      name.c_str(),
                                      -SCIPinfinity(scip),
                                      SCIPinfinity(scip),
                                      0.0,
                                      SCIP_VARTYPE_CONTINUOUS));
    p.d_vars.push_back(sv);
    // exact data must be attached before the variable is added
    CVC5_SCIP_CALL(SCIPaddVarExactData(scip, sv, negInf, posInf, zero));
    CVC5_SCIP_CALL(SCIPaddVar(scip, sv));
    toScipVar[v] = sv;
  }

  // The delta variable realizing the infinitesimal of strict bounds. The
  // delta-rational system is satisfiable iff the maximum of delta subject to
  // the constraints below is positive.
  SCIP_VAR* deltaVar = nullptr;
  if (haveDelta)
  {
    CVC5_SCIP_CALL(SCIPcreateVarBasic(
        scip, &deltaVar, "delta", 0.0, 1.0, 1.0, SCIP_VARTYPE_CONTINUOUS));
    p.d_vars.push_back(deltaVar);
    CVC5_SCIP_CALL(SCIPaddVarExactData(scip, deltaVar, zero, one, one));
    CVC5_SCIP_CALL(SCIPaddVar(scip, deltaVar));
    CVC5_SCIP_CALL(SCIPsetObjsense(scip, SCIP_OBJSENSE_MAXIMIZE));
  }

  // Translate the variable bounds. A bound with value c + k*delta on x is
  // direct (k = 0) or becomes the constraint x - k*delta {>=,<=} c.
  size_t consCount = 0;
  for (ArithVar v : avars)
  {
    for (bool lower : {true, false})
    {
      if (lower ? !d_variables.hasLowerBound(v)
                : !d_variables.hasUpperBound(v))
      {
        continue;
      }
      const DeltaRational& b = lower ? d_variables.getLowerBound(v)
                                     : d_variables.getUpperBound(v);
      SCIP_RATIONAL* c = p.mkRat(b.getNoninfinitesimalPart());
      CVC5_SCIP_CHECK_RAT(c);
      if (b.infinitesimalIsZero())
      {
        if (lower)
        {
          CVC5_SCIP_CALL(SCIPchgVarLbExact(scip, toScipVar[v], c));
        }
        else
        {
          CVC5_SCIP_CALL(SCIPchgVarUbExact(scip, toScipVar[v], c));
        }
        continue;
      }
      // Strict bounds are expected to tighten: positive delta coefficient on
      // lower bounds, negative on upper bounds.
      Assert(b.infinitesimalSgn() == (lower ? 1 : -1));
      SCIP_RATIONAL* minusK = p.mkRat(-b.getInfinitesimalPart());
      CVC5_SCIP_CHECK_RAT(minusK);
      SCIP_VAR* consVars[2] = {toScipVar[v], deltaVar};
      SCIP_RATIONAL* consVals[2] = {one, minusK};
      SCIP_CONS* cons = nullptr;
      std::string name = "b" + std::to_string(consCount++);
      CVC5_SCIP_CALL(SCIPcreateConsBasicExactLinear(scip,
                                                    &cons,
                                                    name.c_str(),
                                                    2,
                                                    consVars,
                                                    consVals,
                                                    lower ? c : negInf,
                                                    lower ? posInf : c));
      CVC5_SCIP_CALL(SCIPaddCons(scip, cons));
      CVC5_SCIP_CALL(SCIPreleaseCons(scip, &cons));
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
    std::vector<SCIP_VAR*> consVars;
    std::vector<SCIP_RATIONAL*> consVals;
    consVars.push_back(toScipVar[basic]);
    SCIP_RATIONAL* minusOne = p.mkRat(Rational(-1));
    CVC5_SCIP_CHECK_RAT(minusOne);
    consVals.push_back(minusOne);
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
      CVC5_SCIP_CHECK_RAT(coeff);
      consVars.push_back(toScipVar[nb]);
      consVals.push_back(coeff);
    }
    SCIP_CONS* cons = nullptr;
    std::string name = "r" + std::to_string(basic);
    CVC5_SCIP_CALL(SCIPcreateConsBasicExactLinear(scip,
                                                  &cons,
                                                  name.c_str(),
                                                  static_cast<int>(consVars.size()),
                                                  consVars.data(),
                                                  consVals.data(),
                                                  zero,
                                                  zero));
    CVC5_SCIP_CALL(SCIPaddCons(scip, cons));
    CVC5_SCIP_CALL(SCIPreleaseCons(scip, &cons));
  }

  // Solve. The standard streams are silenced during solving since SoPlex
  // writes some diagnostics directly to them.
  SCIP_RETCODE solveRc;
  {
    StreamSilencer silencer;
    solveRc = SCIPsolve(scip);
  }
  CVC5_SCIP_CALL(solveRc);
  SCIP_STATUS status = SCIPgetStatus(scip);
  Trace("arith::scip") << "scip status: " << status << endl;

  if (status == SCIP_STATUS_INFEASIBLE)
  {
    ++d_statistics.d_scipUnsat;
    return raiseCoarseConflict(avars);
  }
  if (status != SCIP_STATUS_OPTIMAL)
  {
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }

  SCIP_SOL* sol = SCIPgetBestSol(scip);
  Assert(sol != nullptr);

  if (haveDelta)
  {
    // The strict system is satisfiable iff the optimum of delta is positive.
    SCIP_RATIONAL* deltaVal = p.mkRat();
    CVC5_SCIP_CHECK_RAT(deltaVal);
    SCIPgetSolValExact(scip, sol, deltaVar, deltaVal);
    Trace("arith::scip") << "scip delta optimum positive: "
                         << (SCIPrationalIsPositive(deltaVal) != 0) << endl;
    if (!SCIPrationalIsPositive(deltaVal))
    {
      ++d_statistics.d_scipUnsat;
      return raiseCoarseConflict(avars);
    }
  }

  // Import the exact solution into the partial model by updating the
  // nonbasic variables; the values of the basic variables follow from the
  // tableau (cf. AttemptSolutionSDP::attempt).
  ++d_statistics.d_scipSat;
  SCIP_RATIONAL* val = p.mkRat();
  CVC5_SCIP_CHECK_RAT(val);
  for (ArithVar v : avars)
  {
    if (d_tableau.isBasic(v))
    {
      continue;
    }
    SCIPgetSolValExact(scip, sol, toScipVar[v], val);
    DeltaRational dr(scipRationalToRational(val));
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
  // discrepancy between the SCIP encoding and the partial model. Be
  // defensive and give up rather than report an incorrect result.
  warning() << "SCIP model import left bound violations; returning unknown"
            << std::endl;
  d_errorSet.reduceToSignals();
  ++d_statistics.d_scipUnknown;
  return Result::UNKNOWN;
}

#undef CVC5_SCIP_CALL
#undef CVC5_SCIP_CHECK_RAT

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
