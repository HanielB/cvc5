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

#include <algorithm>
#include <cstdio>
#include <fstream>
#include <map>
#include <sstream>
#include <unordered_map>

#include "base/output.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/error_set.h"
#include "theory/arith/linear/linear_equality.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/arith/linear/tableau.h"
#include "util/statistics_registry.h"

#ifdef CVC5_USE_SCIP
#include <lpiexact/lpiexact.h>
#include <scip/cons_exactlinear.h>
#include <scip/def.h>
#include <scip/rational.h>
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
    ConstraintDatabase& constraintDatabase,
    RaiseConflict conflictChannel,
    TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_constraintDatabase(constraintDatabase),
      d_statistics(statisticsRegistry())
{
}

ScipSimplexDecisionProcedure::Statistics::Statistics(StatisticsRegistry& sr)
    : d_queueTime(sr.registerTimer("theory::arith::scip::queueTime")),
      d_scipTime(sr.registerTimer("theory::arith::scip::solveTime")),
      d_scipCalls(sr.registerInt("theory::arith::scip::calls")),
      d_scipSat(sr.registerInt("theory::arith::scip::sat")),
      d_scipUnsat(sr.registerInt("theory::arith::scip::unsat")),
      d_scipUnknown(sr.registerInt("theory::arith::scip::unknown")),
      d_scipDeclined(sr.registerInt("theory::arith::scip::declined")),
      d_subsetConflicts(sr.registerInt("theory::arith::scip::subsetConflicts")),
      d_fallbackConflicts(
          sr.registerInt("theory::arith::scip::fallbackConflicts")),
      d_certTime(sr.registerTimer("theory::arith::scip::certTime")),
      d_auxSolves(sr.registerInt("theory::arith::scip::auxSolves")),
      d_lpRebuilds(sr.registerInt("theory::arith::scip::lpRebuilds")),
      d_lpRefreshes(sr.registerInt("theory::arith::scip::lpRefreshes")),
      d_modelImports(sr.registerInt("theory::arith::scip::modelImports")),
      d_probes(sr.registerInt("theory::arith::scip::probes")),
      d_probeTime(sr.registerTimer("theory::arith::scip::probeTime")),
      d_basisRows(sr.registerInt("theory::arith::scip::basisRows")),
      d_basisPropTime(sr.registerTimer("theory::arith::scip::basisPropTime")),
      d_propagatedAtoms(sr.registerInt("theory::arith::scip::propagatedAtoms")),
      d_mipCalls(sr.registerInt("theory::arith::scip::mipCalls")),
      d_mipSat(sr.registerInt("theory::arith::scip::mipSat")),
      d_mipUnsat(sr.registerInt("theory::arith::scip::mipUnsat")),
      d_mipUnknown(sr.registerInt("theory::arith::scip::mipUnknown")),
      d_mipDeclined(sr.registerInt("theory::arith::scip::mipDeclined")),
      d_mipTime(sr.registerTimer("theory::arith::scip::mipTime")),
      d_mipProofs(sr.registerInt("theory::arith::scip::mipProofs")),
      d_mipProofsFailed(sr.registerInt("theory::arith::scip::mipProofsFailed"))
{
}

Result::Status ScipSimplexDecisionProcedure::findModel(bool exactResult)
{
  // Note that in contrast to the pivot-based procedures, SCIP always solves
  // the problem completely, i.e. exactResult does not limit the search; it
  // only gates the bound probing for theory propagation (full effort only).
  Assert(d_conflictVariables.empty());
  d_pivots = 0;

  if (d_errorSet.errorEmpty() && !d_errorSet.moreSignals())
  {
    Trace("arith::findModel") << "scipFindModel() trivial" << endl;
    return Result::SAT;
  }

  // Consume the error-set signals without the row-based conflict checks the
  // pivot-based procedures perform here: every conflict of this procedure
  // is derived from a certificate of the LP. The SAT early returns below
  // and above are pure bookkeeping facts (the current assignment satisfies
  // all bounds) and hence remain.
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);
  drainSignals();

  if (d_errorSet.errorEmpty())
  {
    Trace("arith::findModel") << "scipFindModel() fixed itself" << endl;
    return Result::SAT;
  }

  Trace("arith::findModel") << "scipFindModel() start non-trivial" << endl;

#ifdef CVC5_USE_SCIP
  d_declined = false;
  Result::Status res = solveWithScip(exactResult);
  if (d_declined && d_fallback != nullptr)
  {
    // The check was declined: the problem contains a constant that cannot
    // be encoded exactly for SCIP, or no certificate was available for an
    // infeasible system (see the class documentation). Delegate the check
    // to the conventional procedure; the consumed signals are bookkeeping
    // only and the error set still holds the violated variables, from
    // which the fallback derives its verdict.
    Trace("arith::scip") << "scip declined; delegating to fallback" << endl;
    return d_fallback->findModel(exactResult);
  }
  return res;
#else
  Unreachable() << "cvc5 was not compiled with SCIP support";
#endif
}

Result::Status ScipSimplexDecisionProcedure::findIntegerModel()
{
#ifdef CVC5_USE_SCIP
  try
  {
    return solveIntegerWithScip();
  }
  catch (const std::exception& e)
  {
    // e.g. arithmetic failures within SCIP's solving machinery; the
    // conventional procedures proceed
    Trace("arith::scip") << "scip mip exception: " << e.what() << std::endl;
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
#else
  Unreachable() << "cvc5 was not compiled with SCIP support";
#endif
}

void ScipSimplexDecisionProcedure::drainSignals()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_queueTime);
  while (d_errorSet.moreSignals())
  {
    d_errorSet.popSignal();
  }
  d_errorSize = d_errorSet.errorSize();
}

#if defined(CVC5_USE_SCIP) && !defined(CVC5_CLN_IMP)

namespace {

/**
 * The floating-point infinity configured for full SCIP instances
 * (numerics/infinity). SCIP's default of 1e20 makes the floating-point
 * layers (e.g. bound propagation) treat solution values beyond it as
 * impossible, wrongly for the exact problem; raising it widens the
 * exactly solved range. It must stay below the infinity of the underlying
 * exact LP solver (1e100 for SoPlex), beyond which solves fail (soundly,
 * as an error). Note that the input-side coercion threshold of the
 * rational layer (see ScipScratchRationals::mkRat) is a separate, fixed
 * 1e20: SCIPrationalChgInfinity refuses to change it in this build.
 */
constexpr SCIP_Real scipMipInfinity = 1e96;

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

}  // namespace

/**
 * Owner of scratch SCIP rationals for the lifetime of an encoded problem,
 * with the conversion guard shared by all SCIP backends: SCIP's rational
 * layer coerces any value of absolute value at or above its infinity
 * threshold to infinity on construction, which would lose the distinction
 * between such constants (and thereby soundness); a coerced value is
 * reported by setting d_unencodable and returning null.
 */
struct ScipScratchRationals
{
  /** Scratch rationals, freed by freeScratch or on destruction. */
  std::vector<SCIP_RATIONAL*> d_rats;
  /** Whether a constant of the problem was not exactly encodable. */
  bool d_unencodable = false;

  ~ScipScratchRationals() { freeScratch(); }

  /** Creates a scratch rational owned by this pool, or nullptr. */
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

  /** Creates a scratch rational with the value of the given Rational. */
  SCIP_RATIONAL* mkRat(const Rational& q)
  {
    SCIP_RATIONAL* r = mkRat();
    if (r != nullptr)
    {
      SCIPrationalSetGMP(r, q.getValue().get_mpq_t());
      if (SCIPrationalIsAbsInfinity(r))
      {
        Trace("arith::scip") << "scip cannot encode constant " << q << endl;
        d_unencodable = true;
        return nullptr;
      }
    }
    return r;
  }

  /** Frees the scratch rationals. */
  void freeScratch()
  {
    for (SCIP_RATIONAL*& r : d_rats)
    {
      if (r != nullptr)
      {
        SCIPrationalFree(&r);
      }
    }
    d_rats.clear();
  }
};

/**
 * RAII owner of an exact LP interface instance together with the rationals
 * created for it, the maps attributing the LP columns and rows to the
 * arithmetic variables and bound constraints they encode, and a mirror of
 * the encoded tableau for detecting changes across calls.
 *
 * The LP layout is: column 0 is the delta column (realizing the
 * infinitesimal of strict bounds, maximized in [0,1]); columns 1.. encode
 * the arithmetic variables. Rows 0..numTabRows()-1 are the definitional
 * tableau equalities; the remaining rows encode the currently asserted
 * bound constraints and are replaced on every refresh.
 */
struct ScipSimplexProblem
{
  SCIP_LPIEXACT* d_lpi = nullptr;
  /** Cached constant rationals (freed on destruction). */
  SCIP_RATIONAL* d_posInf = nullptr;
  SCIP_RATIONAL* d_negInf = nullptr;
  SCIP_RATIONAL* d_zero = nullptr;
  SCIP_RATIONAL* d_one = nullptr;
  /** Scratch rationals (freed after each build or refresh) and the
   * encodability guard, see ScipScratchRationals. */
  ScipScratchRationals d_scratch;

  /** The arithmetic variables encoded so far. */
  std::vector<ArithVar> d_avars;
  /** Map from ArithVar to its LP column index (0 is the delta column). */
  std::vector<int> d_toCol;
  /** The number of LP columns, including the delta column. */
  int d_ncols = 0;

  /** Mirror of the encoded tableau: the basic variable per tableau row. */
  std::vector<ArithVar> d_tabBasics;
  /**
   * Mirror of the encoded tableau: per tableau row, the (variable,
   * coefficient) entries (excluding the basic variable), sorted by variable.
   */
  std::vector<std::vector<std::pair<ArithVar, Rational>>> d_tabRows;
  /** Per bound row (after the tableau rows), the encoded bound constraint. */
  std::vector<ConstraintCP> d_boundOrigin;
  /** Per bound row, whether it encodes a lower bound (lhs finite). */
  std::vector<bool> d_boundIsLower;

  /**
   * Whether the last solve ended in an infeasible LP, for which a dual
   * Farkas ray is available (as opposed to an optimal LP with zero delta
   * maximum, for which the optimal dual solution is the certificate).
   */
  bool d_lastWasFarkas = false;
  /** Reusable buffer for extracting primal solutions, sized d_primsolCap. */
  SCIP_RATIONAL** d_primsol = nullptr;
  int d_primsolCap = 0;
  /** Reusable buffer for basis inverse rows, sized d_binvCap. */
  SCIP_RATIONAL** d_binv = nullptr;
  int d_binvCap = 0;
  /** Reusable buffer for dual certificates, sized d_dualsCap. */
  SCIP_RATIONAL** d_duals = nullptr;
  int d_dualsCap = 0;

  int numTabRows() const { return static_cast<int>(d_tabBasics.size()); }
  int numRows() const
  {
    return numTabRows() + static_cast<int>(d_boundOrigin.size());
  }

  ~ScipSimplexProblem()
  {
    freeScratch();
    for (SCIP_RATIONAL** r : {&d_posInf, &d_negInf, &d_zero, &d_one})
    {
      if (*r != nullptr)
      {
        SCIPrationalFree(r);
      }
    }
    if (d_primsol != nullptr)
    {
      SCIPrationalFreeArray(&d_primsol, d_primsolCap);
    }
    if (d_binv != nullptr)
    {
      SCIPrationalFreeArray(&d_binv, d_binvCap);
    }
    if (d_duals != nullptr)
    {
      SCIPrationalFreeArray(&d_duals, d_dualsCap);
    }
    if (d_lpi != nullptr)
    {
      SCIPlpiExactFree(&d_lpi);
    }
  }

  /** Grows a rational buffer geometrically to capacity n, or nulls it. */
  static SCIP_RATIONAL** growBuffer(SCIP_RATIONAL**& buf, int& cap, int n)
  {
    if (cap < n)
    {
      if (buf != nullptr)
      {
        SCIPrationalFreeArray(&buf, cap);
        buf = nullptr;
      }
      int newCap = cap == 0 ? 16 : cap;
      while (newCap < n)
      {
        newCap *= 2;
      }
      if (SCIPrationalCreateArray(&buf, newCap) != SCIP_OKAY)
      {
        buf = nullptr;
        cap = 0;
        return nullptr;
      }
      cap = newCap;
    }
    return buf;
  }

  /** Returns the primal solution buffer with capacity for ncols, or null. */
  SCIP_RATIONAL** primsolBuffer(int ncols)
  {
    return growBuffer(d_primsol, d_primsolCap, ncols);
  }

  /** Returns the basis inverse row buffer with capacity for nrows, or null. */
  SCIP_RATIONAL** binvBuffer(int nrows)
  {
    return growBuffer(d_binv, d_binvCap, nrows);
  }

  /** Returns the dual certificate buffer with capacity for nrows, or null. */
  SCIP_RATIONAL** dualsBuffer(int nrows)
  {
    return growBuffer(d_duals, d_dualsCap, nrows);
  }

  /** Frees the scratch rationals. */
  void freeScratch() { d_scratch.freeScratch(); }

  /** Creates a scratch rational owned by this problem, or nullptr. */
  SCIP_RATIONAL* mkRat() { return d_scratch.mkRat(); }

  /** Creates a scratch rational with the value of the given Rational, or
   * nullptr (allocation failure or not exactly encodable, see
   * ScipScratchRationals::mkRat). */
  SCIP_RATIONAL* mkRat(const Rational& q) { return d_scratch.mkRat(q); }
};

/**
 * RAII owner of a full SCIP instance encoding the mixed-integer problem of
 * the current bounds, tableau, and variable integralities: the delta
 * variable (realizing the infinitesimal of strict bounds, maximized in
 * [0,1]) and one variable per arithmetic variable, with one exact linear
 * constraint per tableau equality and per asserted bound. In contrast to
 * the persistent LP instance, a MIP instance is built per check
 * (branch-and-bound state does not usefully carry over).
 */
struct ScipMipProblem
{
  SCIP* d_scip = nullptr;
  /** Scratch rationals (freed on destruction) and the encodability guard. */
  ScipScratchRationals d_scratch;
  /** Cached constant rationals (owned by the scratch pool). */
  SCIP_RATIONAL* d_posInf = nullptr;
  SCIP_RATIONAL* d_negInf = nullptr;
  SCIP_RATIONAL* d_zero = nullptr;
  SCIP_RATIONAL* d_one = nullptr;
  /** The delta variable. */
  SCIP_VAR* d_delta = nullptr;
  /** The arithmetic variables encoded. */
  std::vector<ArithVar> d_avars;
  /** Their SCIP variables (parallel to d_avars). */
  std::vector<SCIP_VAR*> d_vars;
  /** Map from ArithVar to its SCIP variable. */
  std::vector<SCIP_VAR*> d_toVar;
  /** Whether any strict bound (nonzero delta coefficient) was encoded. */
  bool d_anyStrict = false;
  /**
   * Per added constraint (in insertion order), the originating bound
   * constraint, or null for the definitional tableau equalities. Used to
   * resolve the constraint section of certificates.
   */
  std::vector<ConstraintCP> d_consOrigin;
  /** The certificate output file, when certification is enabled. */
  std::string d_certFile;

  /**
   * Releases the SCIP instance. The certificate file is only completed
   * and closed here, so this must precede reading it.
   */
  void freeScip()
  {
    if (d_scip != nullptr)
    {
      for (SCIP_VAR*& v : d_vars)
      {
        SCIPreleaseVar(d_scip, &v);
      }
      d_vars.clear();
      if (d_delta != nullptr)
      {
        SCIPreleaseVar(d_scip, &d_delta);
      }
      SCIPfree(&d_scip);
      d_scip = nullptr;
    }
  }

  ~ScipMipProblem() { freeScip(); }
};

ScipSimplexDecisionProcedure::~ScipSimplexDecisionProcedure() {}

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

/**
 * Evaluates to retval if a rational is null, i.e. could not be allocated
 * or, for the value of a constant of the problem, was not exactly
 * encodable (see ScipSimplexProblem::mkRat). The latter is an expected
 * condition (the call is declined), so no warning is emitted.
 */
#define CVC5_SCIP_CHECK_RAT_RET(r, retval)                              \
  do                                                                    \
  {                                                                     \
    if ((r) == nullptr)                                                 \
    {                                                                   \
      Trace("arith::scip") << "scip rational unavailable" << std::endl; \
      return retval;                                                    \
    }                                                                   \
  } while (0)

#define CVC5_SCIP_CALL_FALSE(x) CVC5_SCIP_CALL_RET(x, false)
#define CVC5_SCIP_CHECK_RAT_FALSE(r) CVC5_SCIP_CHECK_RAT_RET(r, false)

namespace {

/** Anonymous-namespace helpers shared by the problem constructions. */

/** Reads the (sorted) row content of a basic variable from the tableau. */
void readTableauRow(const Tableau& tableau,
                    ArithVar basic,
                    std::vector<std::pair<ArithVar, Rational>>& content)
{
  for (Tableau::RowIterator ri = tableau.basicRowIterator(basic); !ri.atEnd();
       ++ri)
  {
    const Tableau::Entry& entry = *ri;
    if (entry.getColVar() == basic)
    {
      continue;
    }
    content.emplace_back(entry.getColVar(), entry.getCoefficient());
  }
  std::sort(content.begin(),
            content.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
}

/**
 * Invokes f(bc, v, lower, b) for every currently asserted bound constraint
 * bc (restricted to those in filter, if non-null) on a variable v, where
 * lower selects the side and b is the delta-rational bound value (whose
 * infinitesimal is nonnegative for lower and nonpositive for upper bounds).
 * Returns false as soon as f does.
 */
template <typename F>
bool forEachAssertedBound(const ArithVariables& vars,
                          const ConstraintCPVec* filter,
                          F&& f)
{
  std::unordered_set<ConstraintCP> included;
  if (filter != nullptr)
  {
    included.insert(filter->begin(), filter->end());
  }
  for (ArithVariables::var_iterator vi = vars.var_begin(),
                                    vend = vars.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    for (bool lower : {true, false})
    {
      if (lower ? !vars.hasLowerBound(v) : !vars.hasUpperBound(v))
      {
        continue;
      }
      ConstraintCP bc = lower ? vars.getLowerBoundConstraint(v)
                              : vars.getUpperBoundConstraint(v);
      if (filter != nullptr && included.find(bc) == included.end())
      {
        continue;
      }
      const DeltaRational& b =
          lower ? vars.getLowerBound(v) : vars.getUpperBound(v);
      // Strict bounds are expected to tighten: positive delta coefficient
      // on lower bounds, negative on upper bounds.
      Assert(b.infinitesimalIsZero()
             || b.infinitesimalSgn() == (lower ? 1 : -1));
      if (!f(bc, v, lower, b))
      {
        return false;
      }
    }
  }
  return true;
}

}  // namespace

/**
 * Creates the LP interface of p with the delta column (column 0): bounds
 * [0,1] and the only nonzero objective coefficient, maximized. The
 * delta-rational system is satisfiable iff the exact maximum of delta is
 * positive [cf. Dutertre and de Moura, CAV 2006, Lemma 1]; when no strict
 * bound constrains delta, the maximum is trivially 1.
 */
static bool initLpi(ScipSimplexProblem& p,
                    const std::function<void(const char*)>& warn)
{
  if (SCIPlpiExactCreate(
          &p.d_lpi, nullptr, "cvc5_linear_arith", SCIP_OBJSEN_MAXIMIZE)
      != SCIP_OKAY)
  {
    warn("SCIPlpiExactCreate failed");
    return false;
  }
  for (SCIP_RATIONAL** r : {&p.d_posInf, &p.d_negInf, &p.d_zero, &p.d_one})
  {
    if (SCIPrationalCreate(r) != SCIP_OKAY)
    {
      warn("SCIP rational allocation failed");
      return false;
    }
  }
  SCIPrationalSetInfinity(p.d_posInf);
  SCIPrationalSetNegInfinity(p.d_negInf);
  SCIPrationalSetReal(p.d_zero, 0.0);
  SCIPrationalSetReal(p.d_one, 1.0);

  SCIP_RATIONAL* obj[1] = {p.d_one};
  SCIP_RATIONAL* lb[1] = {p.d_zero};
  SCIP_RATIONAL* ub[1] = {p.d_one};
  if (SCIPlpiExactAddCols(
          p.d_lpi, 1, obj, lb, ub, nullptr, 0, nullptr, nullptr, nullptr)
      != SCIP_OKAY)
  {
    warn("adding the delta column failed");
    return false;
  }
  p.d_ncols = 1;
  return true;
}

bool ScipSimplexDecisionProcedure::ensureLp()
{
  if (d_persistent != nullptr)
  {
    ScipSimplexProblem& p = *d_persistent;
    // Remove the bound rows of the previous call.
    if (!p.d_boundOrigin.empty())
    {
      if (SCIPlpiExactDelRows(p.d_lpi, p.numTabRows(), p.numRows() - 1)
          != SCIP_OKAY)
      {
        d_persistent.reset();
      }
      else
      {
        p.d_boundOrigin.clear();
        p.d_boundIsLower.clear();
      }
    }
  }
  if (d_persistent != nullptr)
  {
    // Extend the columns by new variables, and check the encoded tableau
    // against the mirror, appending new rows. On any mismatch (e.g. after a
    // tableau reset on restarts) rebuild from scratch.
    ScipSimplexProblem& p = *d_persistent;
    bool ok = true;
    for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                      vend = d_variables.var_end();
         ok && vi != vend;
         ++vi)
    {
      ArithVar v = *vi;
      if (v < p.d_toCol.size() && p.d_toCol[v] >= 0)
      {
        continue;
      }
      if (v >= p.d_toCol.size())
      {
        p.d_toCol.resize(v + 1, -1);
      }
      SCIP_RATIONAL* obj[1] = {p.d_zero};
      SCIP_RATIONAL* lb[1] = {p.d_negInf};
      SCIP_RATIONAL* ub[1] = {p.d_posInf};
      ok = SCIPlpiExactAddCols(p.d_lpi,
                               1,
                               obj,
                               lb,
                               ub,
                               nullptr,
                               0,
                               nullptr,
                               nullptr,
                               nullptr)
           == SCIP_OKAY;
      if (ok)
      {
        p.d_avars.push_back(v);
        p.d_toCol[v] = p.d_ncols++;
      }
    }
    size_t i = 0;
    int beg[1] = {0};
    for (Tableau::BasicIterator bi = d_tableau.beginBasic(),
                                bend = d_tableau.endBasic();
         ok && bi != bend;
         ++bi, ++i)
    {
      ArithVar basic = *bi;
      std::vector<std::pair<ArithVar, Rational>> content;
      readTableauRow(d_tableau, basic, content);
      if (i < p.d_tabBasics.size())
      {
        if (p.d_tabBasics[i] != basic || p.d_tabRows[i] != content)
        {
          ok = false;  // tableau changed; rebuild
        }
        continue;
      }
      // a new tableau row; append it (the bound rows are already deleted)
      std::vector<int> ind;
      std::vector<SCIP_RATIONAL*> val;
      ind.push_back(p.d_toCol[basic]);
      SCIP_RATIONAL* minusOne = p.mkRat(Rational(-1));
      ok = minusOne != nullptr;
      val.push_back(minusOne);
      for (const auto& [nb, coeff] : content)
      {
        SCIP_RATIONAL* c = p.mkRat(coeff);
        ok = ok && c != nullptr;
        ind.push_back(ok ? p.d_toCol[nb] : 0);
        val.push_back(c);
      }
      SCIP_RATIONAL* lhs[1] = {p.d_zero};
      SCIP_RATIONAL* rhs[1] = {p.d_zero};
      ok = ok
           && SCIPlpiExactAddRows(p.d_lpi,
                                  1,
                                  lhs,
                                  rhs,
                                  nullptr,
                                  static_cast<int>(ind.size()),
                                  beg,
                                  ind.data(),
                                  val.data())
                  == SCIP_OKAY;
      if (ok)
      {
        p.d_tabBasics.push_back(basic);
        p.d_tabRows.push_back(std::move(content));
      }
    }
    // fewer tableau rows than mirrored also means the tableau changed
    ok = ok && i == p.d_tabBasics.size();
    if (ok)
    {
      ok = addBoundRows(p, nullptr);
    }
    if (ok)
    {
      p.freeScratch();
      ++d_statistics.d_lpRefreshes;
      return true;
    }
    if (p.d_scratch.d_unencodable)
    {
      // A constant of the problem cannot be encoded exactly (see mkRat).
      // The instance is consistent up to the offending row (the mirrors are
      // updated in lockstep with successful additions), so it is kept for
      // future refreshes; the call is declined.
      p.d_scratch.d_unencodable = false;
      p.freeScratch();
      d_declined = true;
      return false;
    }
    Trace("arith::scip") << "scip lp refresh failed; rebuilding" << endl;
    d_persistent.reset();
  }

  d_persistent = std::make_unique<ScipSimplexProblem>();
  ++d_statistics.d_lpRebuilds;
  if (!buildLp(*d_persistent, nullptr))
  {
    if (d_persistent->d_scratch.d_unencodable && d_persistent->d_lpi != nullptr)
    {
      // As above: the partial instance is consistent; keep it and decline.
      d_persistent->d_scratch.d_unencodable = false;
      d_persistent->freeScratch();
      d_declined = true;
      return false;
    }
    d_persistent.reset();
    return false;
  }
  return true;
}

/**
 * Adds one row per included bound constraint. A bound with value
 * c + k*delta on x becomes the row x {>=,<=} c (k = 0) or
 * x - k*delta {>=,<=} c (k != 0). All bounds are encoded as explicit LP
 * rows (not as column bounds) so that the exact dual certificates attribute
 * infeasibility to individual bound constraints.
 */
bool ScipSimplexDecisionProcedure::addBoundRows(ScipSimplexProblem& p,
                                                const ConstraintCPVec* filter)
{
  int beg[1] = {0};
  return forEachAssertedBound(
      d_variables,
      filter,
      [&](ConstraintCP bc, ArithVar v, bool lower, const DeltaRational& b)
      {
        SCIP_RATIONAL* c = p.mkRat(b.getNoninfinitesimalPart());
        if (c == nullptr)
        {
          return false;
        }
        int nnonz = 1;
        int ind[2] = {p.d_toCol[v], 0};
        SCIP_RATIONAL* val[2] = {p.d_one, nullptr};
        if (!b.infinitesimalIsZero())
        {
          SCIP_RATIONAL* minusK = p.mkRat(-b.getInfinitesimalPart());
          if (minusK == nullptr)
          {
            return false;
          }
          ind[1] = 0;  // the delta column
          val[1] = minusK;
          nnonz = 2;
        }
        SCIP_RATIONAL* lhs[1] = {lower ? c : p.d_negInf};
        SCIP_RATIONAL* rhs[1] = {lower ? p.d_posInf : c};
        if (SCIPlpiExactAddRows(
                p.d_lpi, 1, lhs, rhs, nullptr, nnonz, beg, ind, val)
            != SCIP_OKAY)
        {
          warning() << "SCIP call 'SCIPlpiExactAddRows' failed" << std::endl;
          return false;
        }
        p.d_boundOrigin.push_back(bc);
        p.d_boundIsLower.push_back(lower);
        return true;
      });
}

bool ScipSimplexDecisionProcedure::buildLp(ScipSimplexProblem& p,
                                           const ConstraintCPVec* filter)
{
  auto warn = [this](const char* msg) { warning() << msg << std::endl; };
  if (!initLpi(p, warn))
  {
    return false;
  }

  // One free column per arithmetic variable. Note that this LP solves the
  // real relaxation: integrality is enforced by the layer above this
  // decision procedure.
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
  p.d_toCol.assign(maxVar + 1, -1);
  {
    int nvars = static_cast<int>(p.d_avars.size());
    std::vector<SCIP_RATIONAL*> obj(nvars, p.d_zero);
    std::vector<SCIP_RATIONAL*> lb(nvars, p.d_negInf);
    std::vector<SCIP_RATIONAL*> ub(nvars, p.d_posInf);
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddCols(p.d_lpi,
                                             nvars,
                                             obj.data(),
                                             lb.data(),
                                             ub.data(),
                                             nullptr,
                                             0,
                                             nullptr,
                                             nullptr,
                                             nullptr));
    for (ArithVar v : p.d_avars)
    {
      p.d_toCol[v] = p.d_ncols++;
    }
  }

  // Translate the tableau: for each basic variable b with row entries
  // (coeff_i, x_i), add the equality (sum_i coeff_i * x_i) - b = 0, where the
  // entry of b itself is skipped (cf. LinearEqualityModule::computeRowValue).
  int beg[1] = {0};
  for (Tableau::BasicIterator bi = d_tableau.beginBasic(),
                              bend = d_tableau.endBasic();
       bi != bend;
       ++bi)
  {
    ArithVar basic = *bi;
    std::vector<std::pair<ArithVar, Rational>> content;
    readTableauRow(d_tableau, basic, content);
    std::vector<int> ind;
    std::vector<SCIP_RATIONAL*> val;
    ind.push_back(p.d_toCol[basic]);
    SCIP_RATIONAL* minusOne = p.mkRat(Rational(-1));
    CVC5_SCIP_CHECK_RAT_FALSE(minusOne);
    val.push_back(minusOne);
    for (const auto& [nb, coeff] : content)
    {
      SCIP_RATIONAL* c = p.mkRat(coeff);
      CVC5_SCIP_CHECK_RAT_FALSE(c);
      ind.push_back(p.d_toCol[nb]);
      val.push_back(c);
    }
    SCIP_RATIONAL* lhs[1] = {p.d_zero};
    SCIP_RATIONAL* rhs[1] = {p.d_zero};
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddRows(p.d_lpi,
                                             1,
                                             lhs,
                                             rhs,
                                             nullptr,
                                             static_cast<int>(ind.size()),
                                             beg,
                                             ind.data(),
                                             val.data()));
    p.d_tabBasics.push_back(basic);
    p.d_tabRows.push_back(std::move(content));
  }

  if (!addBoundRows(p, filter))
  {
    return false;
  }
  p.freeScratch();
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
  // writes some diagnostics directly to them. Re-solving a persistent
  // instance warm-starts from the basis of the previous solve.
  SCIP_RETCODE solveRc;
  {
    StreamSilencer silencer;
    solveRc = SCIPlpiExactSolveDual(p.d_lpi);
  }
  CVC5_SCIP_CALL_UNKNOWN(solveRc);

  if (SCIPlpiExactIsOptimal(p.d_lpi))
  {
    // The delta-rational system is satisfiable iff the optimum of delta,
    // which is the objective value, is positive.
    SCIP_RATIONAL* objval = p.mkRat();
    CVC5_SCIP_CHECK_RAT_UNKNOWN(objval);
    CVC5_SCIP_CALL_UNKNOWN(SCIPlpiExactGetObjval(p.d_lpi, objval));
    Trace("arith::scip") << "scip delta optimum positive: "
                         << (SCIPrationalIsPositive(objval) != 0) << endl;
    if (!SCIPrationalIsPositive(objval))
    {
      return ScipSolveResult::INFEASIBLE;
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

bool ScipSimplexDecisionProcedure::importAssignment(
    const std::vector<ArithVar>& vars,
    const std::function<bool(ArithVar, DeltaRational&)>& valueOf)
{
  // Write the exact solution into the partial model by updating the
  // nonbasic variables; the values of the basic variables follow from the
  // tableau (cf. AttemptSolutionSDP::attempt).
  ++d_statistics.d_modelImports;
  for (ArithVar v : vars)
  {
    if (d_tableau.isBasic(v))
    {
      continue;
    }
    DeltaRational dr;
    if (!valueOf(v, dr))
    {
      return false;
    }
    if (d_variables.getAssignment(v) != dr)
    {
      Trace("arith::scip") << "scip model: " << v << " <- " << dr << endl;
      d_linEq.update(v, dr);
    }
  }
  return true;
}

bool ScipSimplexDecisionProcedure::importValues(ScipSimplexProblem& p)
{
  SCIP_RATIONAL** primsol = p.primsolBuffer(p.d_ncols);
  if (primsol == nullptr)
  {
    return false;
  }
  CVC5_SCIP_CALL_RET(
      SCIPlpiExactGetSol(p.d_lpi, nullptr, primsol, nullptr, nullptr, nullptr),
      false);
  return importAssignment(
      p.d_avars,
      [&p, primsol](ArithVar v, DeltaRational& dr)
      {
        dr = DeltaRational(scipRationalToRational(primsol[p.d_toCol[v]]));
        return true;
      });
}

Result::Status ScipSimplexDecisionProcedure::checkImportedModel()
{
  d_errorSet.reduceToSignals();
  drainSignals();
  if (d_errorSet.errorEmpty())
  {
    return Result::SAT;
  }
  // The imported model did not satisfy all bounds; this indicates a
  // discrepancy between the encoding and the partial model. Be defensive
  // and give up rather than report an incorrect result.
  warning() << "SCIP model import left bound violations; returning unknown"
            << std::endl;
  ++d_statistics.d_scipUnknown;
  return Result::UNKNOWN;
}

Result::Status ScipSimplexDecisionProcedure::importModel(ScipSimplexProblem& p)
{
  if (!importValues(p))
  {
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }
  return checkImportedModel();
}

bool ScipSimplexDecisionProcedure::extractCertificate(
    ScipSimplexProblem& p,
    ConstraintCPVec& constraints,
    std::vector<Rational>* coeffs)
{
  // The certificate of infeasibility is the exact dual Farkas ray if the LP
  // itself was infeasible. If instead the LP was optimal with a zero delta
  // maximum, the certificate is the exact optimal dual solution: it proves
  // the objective bound (max delta <= 0), and remains a valid such proof
  // when all rows with zero multiplier are dropped. Either way, the bound
  // rows in the support of the certificate form an infeasible subset of the
  // delta-rational system, with the multipliers as Farkas coefficients (the
  // definitional tableau rows may participate as well, but their multipliers
  // only perform the substitution of the row polynomials and are not part of
  // explanations). The multipliers are converted only when coeffs is given
  // (they are needed for proofs only); the certificate itself is read at
  // every conflict, as its support is what minimizes the conflict.
  TimerStat::CodeTimer codeTimer(d_statistics.d_certTime);
  int nrows = p.numRows();
  int ntab = p.numTabRows();
  SCIP_RATIONAL** duals = p.dualsBuffer(nrows);
  CVC5_SCIP_CHECK_RAT_FALSE(duals);
  if (p.d_lastWasFarkas)
  {
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactGetDualfarkas(p.d_lpi, duals));
  }
  else
  {
    CVC5_SCIP_CALL_FALSE(SCIPlpiExactGetSol(
        p.d_lpi, nullptr, nullptr, duals, nullptr, nullptr));
  }
  for (int i = ntab; i < nrows; ++i)
  {
    if (!SCIPrationalIsZero(duals[i]))
    {
      constraints.push_back(p.d_boundOrigin[i - ntab]);
      if (coeffs != nullptr)
      {
        coeffs->push_back(scipRationalToRational(duals[i]));
      }
    }
  }
  Trace("arith::scip") << "scip dual certificate: " << constraints.size()
                       << " of " << p.d_boundOrigin.size() << " bounds"
                       << endl;
  return !constraints.empty();
}

Result::Status ScipSimplexDecisionProcedure::raiseScipConflict(
    ScipSimplexProblem& p)
{
  // The Farkas coefficients are needed for the proof of the conflict only;
  // without proofs the conflict builder ignores them.
  bool produceProofs = options().smt.produceProofs;
  ConstraintCPVec constraints;
  std::vector<Rational> coeffs;
  if (extractCertificate(p, constraints, produceProofs ? &coeffs : nullptr)
      && constraints.size() >= 2)
  {
    // The certificate is exact, so its support is a genuine infeasible
    // subset. In assertion builds this is double-checked by an exact
    // re-solve restricted to the subset.
#ifdef CVC5_ASSERTIONS
    {
      ScipSimplexProblem pv;
      ++d_statistics.d_auxSolves;
      Assert(buildLp(pv, &constraints)
             && solveLp(pv) == ScipSolveResult::INFEASIBLE)
          << "SCIP conflict subset failed exact verification";
    }
#endif /* CVC5_ASSERTIONS */

    // Build a native Farkas conflict (carrying a Farkas proof when proofs
    // are enabled) through the conflict builder, mirroring the construction
    // in LinearEqualityModule::minimallyWeakConflict. The consequent must be
    // a constraint whose negation is not yet proven; it is added last.
    Assert(!d_conflictBuilder->underConstruction());
    const Rational one(1);
    size_t consequent = constraints.size();
    for (size_t i = constraints.size(); i-- > 0;)
    {
      if (!constraints[i]->negationHasProof())
      {
        consequent = i;
        break;
      }
    }
    if (consequent < constraints.size())
    {
      for (size_t i = 0; i < constraints.size(); ++i)
      {
        if (i != consequent)
        {
          d_conflictBuilder->addConstraint(constraints[i],
                                           produceProofs ? coeffs[i] : one);
        }
      }
      d_conflictBuilder->addConstraint(
          constraints[consequent], produceProofs ? coeffs[consequent] : one);
      d_conflictBuilder->makeLastConsequent();
      ConstraintCP conflicted = d_conflictBuilder->commitConflict(nodeManager());
      ++d_statistics.d_subsetConflicts;
      Trace("arith::scip") << "scip farkas conflict over "
                           << constraints.size() << " bounds" << endl;
      d_conflictChannel.raiseConflict(conflicted,
                                      InferenceId::ARITH_CONF_SIMPLEX);
      return Result::UNSAT;
    }
    d_conflictBuilder->reset();
  }

  // No usable certificate (possible, e.g., when the exact LP interface
  // cannot provide the dual values; never observed on regression corpora).
  // The system is infeasible, but rather than weaken to an unminimized
  // conflict, decline so that findModel delegates the check to the
  // conventional procedure, which re-derives a minimal conflict (with a
  // proof when proofs are enabled).
  Trace("arith::scip") << "scip conflict without certificate; declining"
                       << endl;
  ++d_statistics.d_fallbackConflicts;
  d_declined = true;
  return Result::UNKNOWN;
}

bool ScipSimplexDecisionProcedure::probeSolve(ScipSimplexProblem& p,
                                              Rational& value)
{
  ++d_statistics.d_probes;
  SCIP_RETCODE solveRc;
  {
    StreamSilencer silencer;
    solveRc = SCIPlpiExactSolveDual(p.d_lpi);
  }
  if (solveRc != SCIP_OKAY || !SCIPlpiExactIsOptimal(p.d_lpi))
  {
    return false;
  }
  SCIP_RATIONAL* objval = p.mkRat();
  if (objval == nullptr
      || SCIPlpiExactGetObjval(p.d_lpi, objval) != SCIP_OKAY
      || SCIPrationalIsAbsInfinity(objval))
  {
    return false;
  }
  value = scipRationalToRational(objval);
  return true;
}

void ScipSimplexDecisionProcedure::propagateFromLp(ScipSimplexProblem& p)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_probeTime);
  NodeManager* nm = nodeManager();
  bool produceProofs = options().smt.produceProofs;

  // The delta column leaves the objective for the duration of the probes
  // (restored below); each probe puts a single variable into the objective.
  int ind[1] = {0};
  SCIP_RATIONAL* objs[1] = {p.d_zero};
  if (SCIPlpiExactChgObj(p.d_lpi, 1, ind, objs) != SCIP_OKAY)
  {
    return;
  }
  SCIP_RATIONAL* minusOne = p.mkRat(Rational(-1));

  for (ArithVar v : p.d_avars)
  {
    if (!d_constraintDatabase.variableDatabaseIsSetup(v))
    {
      continue;
    }
    for (bool lower : {true, false})
    {
      // An atom can only be newly entailed if it holds in the LP model (the
      // current assignment, just imported) and is not already proven: check
      // the strongest atom on the model-value side of the variable.
      ConstraintType t = lower ? LowerBound : UpperBound;
      const DeltaRational& mv = d_variables.getAssignment(v);
      ConstraintP best = d_constraintDatabase.getBestImpliedBound(v, t, mv);
      if (best == NullConstraint || best->assertedToTheTheory()
          || best->hasProof() || !best->canBePropagated())
      {
        continue;
      }
      // Probe: the exact strongest implied bound of v is the optimum of
      // (maximize v) for upper bounds, and of (maximize -v), negated, for
      // lower bounds. The probe solves the closure (delta free in [0,1]),
      // so the derived bound is a sound non-strict bound of the
      // delta-rational system.
      ind[0] = p.d_toCol[v];
      objs[0] = lower ? minusOne : p.d_one;
      if (minusOne == nullptr
          || SCIPlpiExactChgObj(p.d_lpi, 1, ind, objs) != SCIP_OKAY)
      {
        break;
      }
      Rational b;
      // Note that the certificate must be consumed before the objective is
      // restored below, which invalidates the stored LP solution.
      if (probeSolve(p, b))
      {
        if (lower)
        {
          b = -b;
        }
        ConstraintP implied =
            d_constraintDatabase.getBestImpliedBound(v, t, DeltaRational(b));
        if (implied != NullConstraint && !implied->assertedToTheTheory()
            && !implied->hasProof() && implied->canBePropagated()
            && !implied->negationHasProof())
        {
          // The optimal dual solution of the probe is the Farkas derivation
          // of the bound: by dual feasibility, the multipliers y of the
          // bound rows satisfy (sum_r y_r * x_r) == objective == +/-v as
          // polynomials once the auxiliary variables are expanded by their
          // definitions (the tableau row multipliers perform exactly that
          // substitution). The antecedent coefficients are hence the raw
          // multipliers, and the implied (weaker) atom has coefficient -1
          // (upper probes, objective +v) or +1 (lower probes, objective
          // -v), making the polynomial sum of the proof zero (cf.
          // Constraint::wellFormedFarkasProof; coeffs[0] is for the implied
          // constraint as in rowImplicationCanBeApplied).
          p.d_lastWasFarkas = false;
          ConstraintCPVec antecedents;
          std::vector<Rational> dualCoeffs;
          if (extractCertificate(
                  p, antecedents, produceProofs ? &dualCoeffs : nullptr))
          {
            RationalVector coeffs;
            RationalVectorP coeffsP = nullptr;
            if (produceProofs)
            {
              coeffs.push_back(lower ? Rational(1) : Rational(-1));
              coeffs.insert(coeffs.end(), dualCoeffs.begin(), dualCoeffs.end());
              coeffsP = &coeffs;
            }
            implied->impliedByFarkas(nm, antecedents, coeffsP, false);
            implied->tryToPropagate();
            ++d_statistics.d_propagatedAtoms;
            Trace("arith::scip")
                << "scip propagated " << implied << " from probe "
                << (lower ? "lb " : "ub ") << v << " = " << b << " ("
                << antecedents.size() << " antecedents)" << endl;
          }
        }
      }
      // take the variable back out of the objective
      objs[0] = p.d_zero;
      if (SCIPlpiExactChgObj(p.d_lpi, 1, ind, objs) != SCIP_OKAY)
      {
        break;
      }
    }
  }

  // restore the delta objective
  ind[0] = 0;
  objs[0] = p.d_one;
  if (SCIPlpiExactChgObj(p.d_lpi, 1, ind, objs) != SCIP_OKAY)
  {
    // The LP would maximize a zero objective on the next solve, which is
    // sound but loses the strictness test; force a rebuild instead.
    warning() << "SCIP failed to restore the delta objective" << std::endl;
    d_persistent.reset();
  }
}

void ScipSimplexDecisionProcedure::propagateBasisRows(ScipSimplexProblem& p)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_basisPropTime);
  NodeManager* nm = nodeManager();
  bool produceProofs = options().smt.produceProofs;

  int nrows = p.numRows();
  int ntab = p.numTabRows();
  if (nrows == 0)
  {
    return;
  }

  // The basis status of columns and rows and the basis index map (which
  // column or row slack is basic in which basis row); plain int arrays.
  std::vector<int> cstat(p.d_ncols), rstat(nrows), bind(nrows);
  if (SCIPlpiExactGetBase(p.d_lpi, cstat.data(), rstat.data()) != SCIP_OKAY
      || SCIPlpiExactGetBasisInd(p.d_lpi, bind.data()) != SCIP_OKAY)
  {
    Trace("arith::scip") << "scip basis information unavailable" << endl;
    return;
  }
  std::vector<int> basisRowOfCol(p.d_ncols, -1);
  for (int k = 0; k < nrows; ++k)
  {
    if (bind[k] >= 0)
    {
      basisRowOfCol[bind[k]] = k;
    }
  }
  // Free nonbasic columns are pinned at zero; a basis row combining one
  // admits no entailed bound. Track them (other than delta, handled by its
  // own accumulator) so such rows can be skipped; typically there are none.
  std::vector<int> zeroColIndex(p.d_ncols, -1);
  size_t numZeroCols = 0;
  for (int c = 1; c < p.d_ncols; ++c)
  {
    if (cstat[c] == SCIP_BASESTAT_ZERO)
    {
      zeroColIndex[c] = static_cast<int>(numZeroCols++);
    }
  }

  for (ArithVar v : p.d_avars)
  {
    if (!d_constraintDatabase.variableDatabaseIsSetup(v))
    {
      continue;
    }
    // candidate pruning, as in the probe path, per side
    const DeltaRational& mv = d_variables.getAssignment(v);
    bool want[2];  // [0] = lower, [1] = upper
    for (bool lower : {true, false})
    {
      ConstraintP best = d_constraintDatabase.getBestImpliedBound(
          v, lower ? LowerBound : UpperBound, mv);
      want[lower ? 0 : 1] =
          best != NullConstraint && !best->assertedToTheTheory()
          && !best->hasProof() && best->canBePropagated();
    }
    if (!want[0] && !want[1])
    {
      continue;
    }
    int col = p.d_toCol[v];
    if (cstat[col] != SCIP_BASESTAT_BASIC || basisRowOfCol[col] < 0)
    {
      continue;
    }
    SCIP_RATIONAL** binv = p.binvBuffer(nrows);
    if (binv == nullptr)
    {
      return;
    }
    // Note that the sparsity arguments are mandatory (the exact LPI writes
    // them unconditionally), and on success only the listed entries of the
    // coefficient array are valid.
    std::vector<int> binvInds(nrows);
    int binvNnz = -1;
    if (SCIPlpiExactGetBInvRow(
            p.d_lpi, basisRowOfCol[col], binv, binvInds.data(), &binvNnz)
        != SCIP_OKAY)
    {
      Trace("arith::scip") << "scip basis inverse row unavailable" << endl;
      return;
    }
    // On success the result is packed: coefficient i (at the front of the
    // coefficient array) belongs to row binvInds[i]. A negative count means
    // a dense result, where coefficient r belongs to row r.
    bool binvPacked = binvNnz >= 0;
    if (!binvPacked)
    {
      binvNnz = nrows;
    }
    ++d_statistics.d_basisRows;

    // One scan of the basis inverse row: collect the antecedent bound rows
    // (nonbasic slacks at their finite side) with their exact coefficients
    // and the implied bounds per direction in DeltaRational arithmetic, and
    // accumulate the combination's coefficients on the delta column and on
    // any free nonbasic column (sparse dots binv * A_c over our own rows;
    // a nonzero entry on either invalidates the row).
    bool okRow = true;
    bool ok[2] = {want[0], want[1]};
    DeltaRational bound[2] = {DeltaRational(0), DeltaRational(0)};
    std::vector<std::pair<ConstraintCP, Rational>> ants;
    Rational deltaAcc(0);
    std::vector<Rational> zeroAcc(numZeroCols, Rational(0));
    for (int i = 0; okRow && i < binvNnz; ++i)
    {
      int r = binvPacked ? binvInds[i] : i;
      if (SCIPrationalIsZero(binv[i]))
      {
        continue;
      }
      // the representation coefficient of the row activity x_r in
      // v = sum_r a_r * x_r
      Rational a = scipRationalToRational(binv[i]);
      if (r < ntab)
      {
        // Definitional tableau row: its slack is fixed at zero (no value,
        // no antecedent), but the row's columns contribute to the dots.
        if (numZeroCols != 0)
        {
          int bc = p.d_toCol[p.d_tabBasics[r]];
          if (zeroColIndex[bc] >= 0)
          {
            zeroAcc[zeroColIndex[bc]] -= a;  // basic variable coefficient -1
          }
          for (const auto& [var, coeff] : p.d_tabRows[r])
          {
            int cc = p.d_toCol[var];
            if (zeroColIndex[cc] >= 0)
            {
              zeroAcc[zeroColIndex[cc]] += a * coeff;
            }
          }
        }
        continue;
      }
      size_t bidx = r - ntab;
      ConstraintCP origin = p.d_boundOrigin[bidx];
      bool rowLower = p.d_boundIsLower[bidx];
      const DeltaRational& value = origin->getValue();
      // dot contributions: A[r][delta] = -k for strict rows, A[r][col(x)] = 1
      if (!value.getInfinitesimalPart().isZero())
      {
        deltaAcc = deltaAcc - a * value.getInfinitesimalPart();
      }
      if (numZeroCols != 0)
      {
        int oc = p.d_toCol[origin->getVariable()];
        if (zeroColIndex[oc] >= 0)
        {
          zeroAcc[zeroColIndex[oc]] += a;
        }
      }
      if (rstat[r] == SCIP_BASESTAT_BASIC)
      {
        // the slack is inside the basis; not part of the representation
        continue;
      }
      // The nonbasic slack must sit at its (single) finite side.
      if (rstat[r]
          != (rowLower ? SCIP_BASESTAT_LOWER : SCIP_BASESTAT_UPPER))
      {
        okRow = false;
        break;
      }
      // Direction usability: an entry with coefficient a needs its upper
      // (lower) side finite for the upper (lower) implied bound of v when
      // a > 0, and vice versa.
      int sgn = a.sgn();
      Assert(sgn != 0);
      bool entryForUpper = (sgn > 0) ? !rowLower : rowLower;
      if (entryForUpper)
      {
        ok[0] = false;  // unusable for the lower bound of v
        if (ok[1])
        {
          bound[1] = bound[1] + value * a;
        }
      }
      else
      {
        ok[1] = false;
        if (ok[0])
        {
          bound[0] = bound[0] + value * a;
        }
      }
      ants.emplace_back(origin, a);
    }
    if (!okRow || (!ok[0] && !ok[1]) || ants.empty()
        || !deltaAcc.isZero())
    {
      continue;
    }
    if (std::any_of(zeroAcc.begin(), zeroAcc.end(), [](const Rational& q) {
          return !q.isZero();
        }))
    {
      continue;
    }

    for (bool lower : {true, false})
    {
      if (!ok[lower ? 0 : 1])
      {
        continue;
      }
      ConstraintType t = lower ? LowerBound : UpperBound;
      ConstraintP implied = d_constraintDatabase.getBestImpliedBound(
          v, t, bound[lower ? 0 : 1]);
      if (implied == NullConstraint || implied->assertedToTheTheory()
          || implied->hasProof() || !implied->canBePropagated()
          || implied->negationHasProof())
      {
        continue;
      }
      // Certificate by the basis identity: v == sum a_r * x_r over the
      // antecedent rows; the coefficient conventions are as in the probe
      // path (cf. Constraint::wellFormedFarkasProof).
      ConstraintCPVec antecedents;
      RationalVector coeffs;
      RationalVectorP coeffsP = nullptr;
      if (produceProofs)
      {
        coeffs.push_back(lower ? Rational(1) : Rational(-1));
      }
      for (const auto& [origin, a] : ants)
      {
        antecedents.push_back(origin);
        if (produceProofs)
        {
          coeffs.push_back(lower ? -a : a);
        }
      }
      if (produceProofs)
      {
        coeffsP = &coeffs;
      }
      implied->impliedByFarkas(nm, antecedents, coeffsP, false);
      implied->tryToPropagate();
      ++d_statistics.d_propagatedAtoms;
      Trace("arith::scip") << "scip propagated " << implied
                           << " from basis row of v" << v << " ("
                           << antecedents.size() << " antecedents)" << endl;
    }
  }
}

Result::Status ScipSimplexDecisionProcedure::solveWithScip(bool exactResult)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_scipTime);
  ++d_statistics.d_scipCalls;

  if (!ensureLp())
  {
    ++(d_declined ? d_statistics.d_scipDeclined : d_statistics.d_scipUnknown);
    return Result::UNKNOWN;
  }
  ScipSimplexProblem& p = *d_persistent;
  switch (solveLp(p))
  {
    case ScipSolveResult::FEASIBLE:
    {
      ++d_statistics.d_scipSat;
      Result::Status res = importModel(p);
      // Note that propagation below full effort is where it can get ahead
      // of the SAT solver's decisions (at full effort the trail is already
      // complete), but it is also performed much more often there; the
      // effort option selects the schedule.
      if (res == Result::SAT
          && options().arith.arithScipPropagation
                 != options::ArithScipPropagationMode::NONE
          && (exactResult
              || options().arith.arithScipPropagationEffort
                     == options::ArithScipPropagationEffort::ALL))
      {
        if (options().arith.arithScipPropagation
            == options::ArithScipPropagationMode::BASIS)
        {
          propagateBasisRows(p);
        }
        else
        {
          propagateFromLp(p);
        }
      }
      return res;
    }
    case ScipSolveResult::INFEASIBLE:
    {
      Result::Status res = raiseScipConflict(p);
      if (res == Result::UNSAT)
      {
        ++d_statistics.d_scipUnsat;
      }
      return res;
    }
    case ScipSolveResult::UNKNOWN:
    default:
      ++d_statistics.d_scipUnknown;
      return Result::UNKNOWN;
  }
}

namespace {

/**
 * Reconstructs a VIPR certificate of an infeasible (or zero-delta-
 * optimum) exact MIP solve into a cvc5 proof of the negation of the
 * conjunction of the participating bound constraints, using only
 * existing proof rules:
 * - lin steps (weighted sums of rows) become scaled sums
 *   (MACRO_ARITH_SCALE_SUM_UB), normalized by MACRO_SR_PRED_TRANSFORM;
 * - rnd steps (Chvatal-Gomory rounding) are the same scaled sums, with
 *   the rounding of the constant absorbed by the integer bound
 *   tightening the rewriter performs in the normalization;
 * - asm rows (branching assumptions) become assumptions, discharged by
 *   the uns steps: the two branch refutations are scoped on their
 *   assumptions, the negation of the one branch is rewritten into the
 *   other (the split being exhaustive over the integers), and the
 *   contradiction is concluded by CONTRA;
 * - the rows of the original problem become assumptions for the bound
 *   constraints (collected into the conflict) and rewrite-introductions
 *   for the definitional tableau equalities.
 * The delta column is translated away: by the delta encoding, a row
 * poly - k*delta >= c with k > 0 denotes the strict bound poly > c (and
 * correspondingly for upper bounds), which is exactly the strictness
 * semantics of the arithmetic proof calculus, so the delta coefficients
 * of combinations turn into the strictness of the derived atoms.
 *
 * The conclusion of every step is recomputed from the premises in exact
 * arithmetic (the rows stated in the certificate are used for shape
 * only), and every proof node is constructed with its expected
 * conclusion, so a checker validates each step; any failure aborts the
 * reconstruction and the check is treated as inconclusive, which is
 * sound.
 */
class ViprProofReconstructor
{
 public:
  ViprProofReconstructor(Env& env,
                         const ScipMipProblem& mp,
                         const ArithVariables& vars)
      : d_env(env), d_mp(mp), d_vars(vars)
  {
  }

  /**
   * Collects the support of the certificate: the bound constraints whose
   * rows are reachable from the final derivation through the premises.
   * This is a parse and a traversal only (no proof is built); it serves
   * the minimization of the trusted conflict when proofs are disabled.
   */
  bool collectSupport(const std::string& filename, ConstraintCPVec& support)
  {
    std::ifstream in(filename);
    if (!in || !parse(in) || d_rows.empty())
    {
      Trace("arith::scip::pf") << "vipr: parse failure" << std::endl;
      return false;
    }
    std::vector<bool> seen(d_rows.size(), false);
    std::vector<size_t> stack{d_rows.size() - 1};
    seen.back() = true;
    while (!stack.empty())
    {
      size_t idx = stack.back();
      stack.pop_back();
      const ViprRow& r = d_rows[idx];
      if (r.d_kind == ViprRow::CON)
      {
        if (idx < d_mp.d_consOrigin.size()
            && d_mp.d_consOrigin[idx] != NullConstraint)
        {
          support.push_back(d_mp.d_consOrigin[idx]);
        }
        continue;
      }
      if (r.d_kind == ViprRow::UNSUPPORTED)
      {
        // its premises are unknown; be conservative
        return false;
      }
      auto push = [&](int p) {
        if (p >= 0 && static_cast<size_t>(p) < idx && !seen[p])
        {
          seen[p] = true;
          stack.push_back(static_cast<size_t>(p));
        }
      };
      for (const auto& [pidx, mult] : r.d_premises)
      {
        push(pidx);
      }
      if (r.d_kind == ViprRow::UNS)
      {
        for (int u : r.d_uns)
        {
          push(u);
        }
      }
    }
    return !support.empty();
  }

  /** Runs the reconstruction; on success sets conflict and proof. */
  bool reconstruct(const std::string& filename,
                   Node& conflict,
                   std::shared_ptr<ProofNode>& proof)
  {
    std::ifstream in(filename);
    if (!in || !parse(in))
    {
      Trace("arith::scip::pf") << "vipr: parse failure" << std::endl;
      return false;
    }
    if (d_rows.empty())
    {
      return false;
    }
    // the certificate's final derivation establishes the contradiction
    std::shared_ptr<ProofNode> last = proveRow(d_rows.size() - 1);
    std::shared_ptr<ProofNode> falsePf = toFalse(last);
    if (falsePf == nullptr)
    {
      Trace("arith::scip::pf") << "vipr: no final contradiction" << std::endl;
      return false;
    }
    // the open assumptions must be exactly the bound constraint literals
    std::vector<Node> rawAssumptions;
    expr::getFreeAssumptions(falsePf.get(), rawAssumptions);
    std::vector<Node> assumptions;
    std::unordered_set<Node> seen;
    for (const Node& a : rawAssumptions)
    {
      if (d_assertionLits.find(a) == d_assertionLits.end())
      {
        Trace("arith::scip::pf")
            << "vipr: undischarged assumption " << a << std::endl;
        return false;
      }
      if (seen.insert(a).second)
      {
        assumptions.push_back(a);
      }
    }
    if (assumptions.empty())
    {
      return false;
    }
    NodeManager* nm = d_env.getNodeManager();
    Node conf = assumptions.size() == 1 ? assumptions[0]
                                        : nm->mkNode(Kind::AND, assumptions);
    std::shared_ptr<ProofNode> scoped =
        mkStep(ProofRule::SCOPE, {falsePf}, assumptions, conf.notNode());
    if (scoped == nullptr)
    {
      return false;
    }
    conflict = conf;
    proof = scoped;
    return true;
  }

 private:
  /** A row of the certificate, in its space (the delta column included). */
  struct ViprRow
  {
    enum Kind
    {
      CON,
      ASM,
      LIN,
      RND,
      UNS,
      UNSUPPORTED
    };
    Kind d_kind = CON;
    /** The relation: GEQ, LEQ or EQUAL. */
    cvc5::internal::Kind d_rel = cvc5::internal::Kind::GEQ;
    Rational d_rhs;
    /** Sparse left-hand side over the certificate's variable indices. */
    std::map<int, Rational> d_lhs;
    /** The premises (row index, multiplier) of lin and rnd steps. */
    std::vector<std::pair<int, Rational>> d_premises;
    /** The branch refutations and assumptions (i1 a1 i2 a2) of uns. */
    int d_uns[4] = {-1, -1, -1, -1};
  };

  /** Parses the certificate (cf. the VIPR format, version 1.0). */
  bool parse(std::istream& in)
  {
    std::string tok;
    auto expect = [&](const char* what) {
      return bool(in >> tok) && tok == what;
    };
    if (!expect("VER") || !(in >> tok))
    {
      return false;
    }
    size_t nvars = 0;
    if (!expect("VAR") || !(in >> nvars))
    {
      return false;
    }
    // map the variable names back: "delta" and "v<arithvar>", with the
    // "t_" prefix of SCIP's transformed problem
    d_varTerm.resize(nvars);
    d_isDelta.assign(nvars, false);
    for (size_t i = 0; i < nvars; ++i)
    {
      if (!(in >> tok))
      {
        return false;
      }
      std::string name = tok.rfind("t_", 0) == 0 ? tok.substr(2) : tok;
      if (name == "delta")
      {
        d_isDelta[i] = true;
      }
      else if (name.size() > 1 && name[0] == 'v')
      {
        ArithVar v =
            static_cast<ArithVar>(std::stoul(name.substr(1), nullptr, 10));
        if (!d_vars.hasNode(v))
        {
          return false;
        }
        d_varTerm[i] = d_vars.asNode(v);
      }
      else
      {
        return false;
      }
    }
    size_t nint = 0;
    if (!expect("INT") || !(in >> nint))
    {
      return false;
    }
    for (size_t i = 0; i < nint; ++i)
    {
      if (!(in >> tok))
      {
        return false;
      }
    }
    // the objective: a sparse row (our encoding maximizes delta)
    if (!expect("OBJ") || !(in >> tok))
    {
      return false;
    }
    if (!parseSparse(in, d_objRow))
    {
      return false;
    }
    size_t ncons = 0, nbounded = 0;
    if (!expect("CON") || !(in >> ncons) || !(in >> nbounded))
    {
      return false;
    }
    d_rows.resize(ncons);
    for (size_t i = 0; i < ncons; ++i)
    {
      if (!parseRowBody(in, d_rows[i]))
      {
        return false;
      }
      d_rows[i].d_kind = ViprRow::CON;
    }
    // RTP infeas, or RTP range <l> <u>
    if (!expect("RTP") || !(in >> tok))
    {
      return false;
    }
    if (tok == "range")
    {
      if (!(in >> tok) || !(in >> tok))
      {
        return false;
      }
    }
    // solutions: a name and a sparse row each
    size_t nsol = 0;
    if (!expect("SOL") || !(in >> nsol))
    {
      return false;
    }
    for (size_t i = 0; i < nsol; ++i)
    {
      ViprRow ignored;
      if (!(in >> tok) || !parseSparse(in, ignored.d_lhs))
      {
        return false;
      }
    }
    size_t nder = 0;
    if (!expect("DER") || !(in >> nder))
    {
      return false;
    }
    d_rows.reserve(ncons + nder);
    for (size_t i = 0; i < nder; ++i)
    {
      ViprRow r;
      if (!parseRowBody(in, r) || !parseDerivation(in, r))
      {
        return false;
      }
      d_rows.push_back(std::move(r));
    }
    return true;
  }

  /** Parses "<nnz> (<idx> <coef>)*" or "OBJ" into a sparse vector. */
  bool parseSparse(std::istream& in, std::map<int, Rational>& lhs)
  {
    std::string tok;
    if (!(in >> tok))
    {
      return false;
    }
    if (tok == "OBJ")
    {
      lhs = d_objRow;
      return true;
    }
    size_t nnz;
    Rational coef;
    try
    {
      nnz = std::stoul(tok, nullptr, 10);
      for (size_t i = 0; i < nnz; ++i)
      {
        int idx;
        if (!(in >> idx) || !(in >> tok))
        {
          return false;
        }
        lhs[idx] += Rational(tok.c_str());
      }
    }
    catch (...)
    {
      return false;
    }
    return true;
  }

  /** Parses "<name> <sense> <rhs>" followed by the sparse row. */
  bool parseRowBody(std::istream& in, ViprRow& r)
  {
    std::string name, sense, rhs;
    if (!(in >> name) || !(in >> sense) || !(in >> rhs))
    {
      return false;
    }
    if (sense == "G")
    {
      r.d_rel = Kind::GEQ;
    }
    else if (sense == "L")
    {
      r.d_rel = Kind::LEQ;
    }
    else if (sense == "E")
    {
      r.d_rel = Kind::EQUAL;
    }
    else
    {
      return false;
    }
    try
    {
      r.d_rhs = Rational(rhs.c_str());
    }
    catch (...)
    {
      return false;
    }
    return parseSparse(in, r.d_lhs);
  }

  /** Parses "{ <rule> ... } <maxidx>" of a derivation. */
  bool parseDerivation(std::istream& in, ViprRow& r)
  {
    std::string tok;
    if (!(in >> tok) || tok != "{" || !(in >> tok))
    {
      return false;
    }
    bool supported = true;
    if (tok == "asm")
    {
      r.d_kind = ViprRow::ASM;
    }
    else if (tok == "lin" || tok == "rnd")
    {
      r.d_kind = tok == "lin" ? ViprRow::LIN : ViprRow::RND;
      size_t n = 0;
      if (!(in >> tok))
      {
        return false;
      }
      if (tok == "weak")
      {
        // weakly dominated combinations are not reconstructed; the row
        // is only rejected if some needed derivation depends on it
        supported = false;
      }
      else
      {
        try
        {
          n = std::stoul(tok, nullptr, 10);
        }
        catch (...)
        {
          return false;
        }
        for (size_t i = 0; i < n; ++i)
        {
          int idx;
          if (!(in >> idx) || !(in >> tok))
          {
            return false;
          }
          try
          {
            r.d_premises.emplace_back(idx, Rational(tok.c_str()));
          }
          catch (...)
          {
            return false;
          }
        }
      }
    }
    else if (tok == "uns")
    {
      r.d_kind = ViprRow::UNS;
      for (int& u : r.d_uns)
      {
        if (!(in >> u))
        {
          return false;
        }
      }
    }
    else
    {
      supported = false;
    }
    // skip to the matching closing brace (nested braces possible)
    int depth = 1;
    while (depth > 0)
    {
      if (!(in >> tok))
      {
        return false;
      }
      if (tok == "{")
      {
        ++depth;
      }
      else if (tok == "}")
      {
        --depth;
      }
      else if (!supported)
      {
        continue;
      }
      else if (depth == 1 && r.d_kind != ViprRow::UNSUPPORTED && tok != "}")
      {
        // unexpected trailing tokens within a supported rule
        supported = false;
      }
    }
    if (!supported)
    {
      r.d_kind = ViprRow::UNSUPPORTED;
      r.d_premises.clear();
    }
    // the trailing hint (the largest premise index, or -1)
    return bool(in >> tok);
  }

  /** The arithmetic type of the non-delta part of a row. */
  TypeNode rowType(const ViprRow& r)
  {
    NodeManager* nm = d_env.getNodeManager();
    for (const auto& [idx, coef] : r.d_lhs)
    {
      if (!d_isDelta[idx]
          && (d_varTerm[idx].getType().isReal() || !coef.isIntegral()))
      {
        return nm->realType();
      }
    }
    return nm->integerType();
  }

  /**
   * The cvc5 atom of a row: the delta column is dropped, with a nonzero
   * delta coefficient turning the relation strict (see above), and
   * fractional constants over integer polynomials are tightened (which
   * the rewriter justifies in the normalization steps). With forceEqual
   * the relation is an equality (for the two bound rows of an asserted
   * equality constraint, whose literal proves both at once).
   */
  Node atomOf(const ViprRow& r, bool forceEqual = false)
  {
    NodeManager* nm = d_env.getNodeManager();
    Rational deltaCoef(0);
    std::vector<Node> sum;
    TypeNode tn = rowType(r);
    bool real = tn.isReal();
    for (const auto& [idx, coef] : r.d_lhs)
    {
      if (coef.isZero())
      {
        continue;
      }
      if (d_isDelta[idx])
      {
        deltaCoef = coef;
        continue;
      }
      Node c = real ? nm->mkConstReal(coef) : nm->mkConstInt(coef);
      sum.push_back(coef.isOne() ? d_varTerm[idx]
                                 : nm->mkNode(Kind::MULT, c, d_varTerm[idx]));
    }
    Node poly;
    if (sum.empty())
    {
      poly = real ? nm->mkConstReal(Rational(0)) : nm->mkConstInt(Rational(0));
    }
    else if (sum.size() == 1)
    {
      poly = sum[0];
    }
    else
    {
      poly = nm->mkNode(Kind::ADD, sum);
    }
    Kind rel = forceEqual ? Kind::EQUAL : r.d_rel;
    if (!deltaCoef.isZero())
    {
      if (forceEqual)
      {
        return Node::null();  // equality constraints are never strict
      }
      if (rel == Kind::GEQ && deltaCoef.sgn() < 0)
      {
        rel = Kind::GT;
      }
      else if (rel == Kind::LEQ && deltaCoef.sgn() > 0)
      {
        rel = Kind::LT;
      }
      else if (!sum.empty())
      {
        // a delta coefficient that weakens the relation: unexpected on
        // the reconstructed paths
        return Node::null();
      }
      // pure delta rows (the delta bounds) keep their relation; they
      // translate to valid constant facts (e.g. 0 >= 0)
    }
    Rational rhs = r.d_rhs;
    if (!real && !rhs.isIntegral())
    {
      // tighten to the integer bound (justified by the rewriter)
      switch (rel)
      {
        case Kind::GEQ: rhs = Rational(rhs.ceiling()); break;
        case Kind::GT:
          rhs = Rational(rhs.floor() + 1);
          rel = Kind::GEQ;
          break;
        case Kind::LEQ: rhs = Rational(rhs.floor()); break;
        case Kind::LT:
          rhs = Rational(rhs.ceiling() - 1);
          rel = Kind::LEQ;
          break;
        default: return Node::null();  // fractional integer equality
      }
    }
    Node c = real ? nm->mkConstReal(rhs) : nm->mkConstInt(rhs);
    return nm->mkNode(rel, poly, c);
  }

  /**
   * Creates a checked proof node, or null. The step is pre-validated
   * with the non-aborting checker entry (constructing a mismatched node
   * would fail fatally); a null result aborts the reconstruction.
   */
  std::shared_ptr<ProofNode> mkStep(
      ProofRule rule,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      Node expected)
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    ProofChecker* pc = pnm->getChecker();
    if (pc != nullptr)
    {
      std::vector<Node> cres;
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        cres.push_back(c->getResult());
      }
      Node res = pc->checkDebug(rule, cres, args, expected, "arith::scip::pf");
      if (res.isNull())
      {
        Trace("arith::scip::pf") << "vipr: failed step " << rule << " for "
                                 << expected << std::endl;
        return nullptr;
      }
    }
    return pnm->mkNode(rule, children, args, expected);
  }

  /** A proof of target from pf, justified by rewriting. */
  std::shared_ptr<ProofNode> transform(std::shared_ptr<ProofNode> pf,
                                       Node target)
  {
    if (pf == nullptr || target.isNull())
    {
      return nullptr;
    }
    if (pf->getResult() == target)
    {
      return pf;
    }
    return mkStep(
        ProofRule::MACRO_SR_PRED_TRANSFORM, {pf}, {target}, target);
  }

  /** A proof of false from a proof of an absurd constant atom. */
  std::shared_ptr<ProofNode> toFalse(std::shared_ptr<ProofNode> pf)
  {
    if (pf == nullptr)
    {
      return nullptr;
    }
    Node f = d_env.getNodeManager()->mkConst(false);
    return transform(pf, f);
  }

  /** Proves the row of the given index, memoized. */
  std::shared_ptr<ProofNode> proveRow(size_t idx)
  {
    if (idx >= d_rows.size())
    {
      return nullptr;
    }
    auto it = d_proofs.find(idx);
    if (it != d_proofs.end())
    {
      return it->second;
    }
    std::shared_ptr<ProofNode> pf = proveRowInternal(idx);
    d_proofs[idx] = pf;
    return pf;
  }

  std::shared_ptr<ProofNode> proveRowInternal(size_t idx)
  {
    NodeManager* nm = d_env.getNodeManager();
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    ViprRow& r = d_rows[idx];
    switch (r.d_kind)
    {
      case ViprRow::CON:
      {
        ConstraintCP bc = idx < d_mp.d_consOrigin.size()
                              ? d_mp.d_consOrigin[idx]
                              : NullConstraint;
        if (bc == NullConstraint)
        {
          // a definitional tableau equality, or a delta bound: valid
          Node atom = atomOf(r);
          if (atom.isNull())
          {
            return nullptr;
          }
          return mkStep(ProofRule::MACRO_SR_PRED_INTRO, {}, {atom}, atom);
        }
        // A bound constraint: an assumption, normalized to the row atom.
        // The two bound rows of an asserted equality both carry the
        // equality atom (a valid summand of any sign).
        Node atom = atomOf(r, bc->getType() == Equality);
        if (atom.isNull())
        {
          return nullptr;
        }
        Node lit = Constraint::externalExplainByAssertions(
            nm, ConstraintCPVec{bc});
        d_assertionLits.insert(lit);
        return transform(pnm->mkAssume(lit), atom);
      }
      case ViprRow::ASM:
      {
        Node atom = atomOf(r);
        if (atom.isNull())
        {
          return nullptr;
        }
        return pnm->mkAssume(atom);
      }
      case ViprRow::LIN:
      case ViprRow::RND:
      {
        return proveCombination(idx);
      }
      case ViprRow::UNS:
      {
        return proveUnsplit(idx);
      }
      default: return nullptr;
    }
  }

  /** Proves a lin or rnd row: a checked scaled sum of the premises. */
  std::shared_ptr<ProofNode> proveCombination(size_t idx)
  {
    NodeManager* nm = d_env.getNodeManager();
    ViprRow& r = d_rows[idx];
    // recompute the combination in the certificate's space (the delta
    // column flows through and lands in the strictness of the atom)
    ViprRow comb;
    comb.d_rel = r.d_rel == Kind::EQUAL ? Kind::GEQ : r.d_rel;
    if (r.d_rel == Kind::EQUAL)
    {
      return nullptr;  // combinations concluding equalities: unsupported
    }
    comb.d_rhs = Rational(0);
    bool conclLower = r.d_rel == Kind::LEQ;
    std::vector<std::shared_ptr<ProofNode>> children;
    std::vector<Node> scalars;
    std::vector<Node> premiseAtoms;
    for (const auto& [pidx, mult] : r.d_premises)
    {
      if (mult.isZero())
      {
        continue;
      }
      if (pidx < 0 || static_cast<size_t>(pidx) >= idx)
      {
        return nullptr;
      }
      std::shared_ptr<ProofNode> ppf = proveRow(pidx);
      if (ppf == nullptr)
      {
        return nullptr;
      }
      const ViprRow& prow = d_rows[pidx];
      // sign conditions of a valid combination
      if ((prow.d_rel == Kind::GEQ && (conclLower ? mult.sgn() > 0 : false))
          || (prow.d_rel == Kind::LEQ
              && (conclLower ? false : mult.sgn() > 0)))
      {
        // a >= premise with positive multiplier cannot support a <=
        // conclusion and vice versa
        return nullptr;
      }
      for (const auto& [vi, coef] : prow.d_lhs)
      {
        comb.d_lhs[vi] += mult * coef;
      }
      comb.d_rhs += mult * prow.d_rhs;
      // the scaled-sum rule works in upper-bound space: >= premises
      // need negative scalars and <= premises positive ones
      Rational k = conclLower ? mult : -mult;
      Node atom = ppf->getResult();
      Kind ak = atom.getKind();
      if (ak == Kind::NOT || atom.getNumChildren() != 2
          || !atom[1].isConst())
      {
        return nullptr;
      }
      if ((ak == Kind::GEQ || ak == Kind::GT) && k.sgn() > 0)
      {
        return nullptr;
      }
      if ((ak == Kind::LEQ || ak == Kind::LT) && k.sgn() < 0)
      {
        return nullptr;
      }
      // the scalar's type follows the premise terms (cf. the checker)
      bool real = atom[0].getType().isReal() || atom[1].getType().isReal();
      Node kn = real || !k.isIntegral() ? nm->mkConstReal(k)
                                        : nm->mkConstInt(k);
      children.push_back(ppf);
      scalars.push_back(kn);
      premiseAtoms.push_back(atom);
    }
    if (children.empty())
    {
      return nullptr;
    }
    Node target = atomOf(comb);
    if (target.isNull())
    {
      return nullptr;
    }
    if (children.size() == 1)
    {
      // a pure scaling: the normal forms agree
      return transform(children[0], target);
    }
    // replicate the conclusion the checker computes for the scaled sum
    bool strict = false;
    NodeBuilder leftSum(nm, Kind::ADD);
    NodeBuilder rightSum(nm, Kind::ADD);
    for (size_t i = 0; i < children.size(); ++i)
    {
      Kind ak = premiseAtoms[i].getKind();
      strict = strict || ak == Kind::GT || ak == Kind::LT;
      Rational k = scalars[i].getConst<Rational>();
      if (k.isOne())
      {
        leftSum << premiseAtoms[i][0];
        rightSum << premiseAtoms[i][1];
      }
      else
      {
        leftSum << nm->mkNode(Kind::MULT, scalars[i], premiseAtoms[i][0]);
        rightSum << nm->mkNode(Kind::MULT, scalars[i], premiseAtoms[i][1]);
      }
    }
    Node sum = nm->mkNode(strict ? Kind::LT : Kind::LEQ,
                          leftSum.constructNode(),
                          rightSum.constructNode());
    std::shared_ptr<ProofNode> pf = mkStep(
        ProofRule::MACRO_ARITH_SCALE_SUM_UB, children, scalars, sum);
    pf = transform(pf, target);
    if (pf != nullptr)
    {
      // downstream steps use the recomputed row
      comb.d_kind = r.d_kind;
      d_rows[idx] = std::move(comb);
    }
    return pf;
  }

  /** Proves false from an unsplitting step (a branch resolution). */
  std::shared_ptr<ProofNode> proveUnsplit(size_t idx)
  {
    const ViprRow& r = d_rows[idx];
    int i1 = r.d_uns[0], a1 = r.d_uns[1], i2 = r.d_uns[2], a2 = r.d_uns[3];
    if (i1 < 0 || a1 < 0 || i2 < 0 || a2 < 0
        || static_cast<size_t>(std::max(std::max(i1, a1), std::max(i2, a2)))
               >= idx
        || d_rows[a1].d_kind != ViprRow::ASM
        || d_rows[a2].d_kind != ViprRow::ASM)
    {
      return nullptr;
    }
    // both branches must refute; their assumptions are exhaustive over
    // the integers (x <= k and x >= k+1), so the negation of the one
    // rewrites into the other
    std::shared_ptr<ProofNode> f1 = toFalse(proveRow(i1));
    std::shared_ptr<ProofNode> f2 = toFalse(proveRow(i2));
    Node atom1 = atomOf(d_rows[a1]);
    Node atom2 = atomOf(d_rows[a2]);
    if (f1 == nullptr || f2 == nullptr || atom1.isNull() || atom2.isNull())
    {
      return nullptr;
    }
    std::shared_ptr<ProofNode> s1 =
        mkStep(ProofRule::SCOPE, {f1}, {atom1}, atom1.notNode());
    std::shared_ptr<ProofNode> s2 =
        mkStep(ProofRule::SCOPE, {f2}, {atom2}, atom2.notNode());
    if (s1 == nullptr || s2 == nullptr)
    {
      return nullptr;
    }
    std::shared_ptr<ProofNode> t = transform(s1, atom2);
    if (t == nullptr)
    {
      return nullptr;
    }
    Node f = d_env.getNodeManager()->mkConst(false);
    return mkStep(ProofRule::CONTRA, {t, s2}, {}, f);
  }

  Env& d_env;
  const ScipMipProblem& d_mp;
  const ArithVariables& d_vars;
  /** The terms of the certificate's variables (null for delta). */
  std::vector<Node> d_varTerm;
  std::vector<bool> d_isDelta;
  /** The objective row (the delta variable, in our encoding). */
  std::map<int, Rational> d_objRow;
  /** All rows: the problem constraints, then the derivations. */
  std::vector<ViprRow> d_rows;
  /** Memoized proofs per row index. */
  std::map<size_t, std::shared_ptr<ProofNode>> d_proofs;
  /** The assumption literals of the used bound constraints. */
  std::unordered_set<Node> d_assertionLits;
};

}  // namespace

bool ScipSimplexDecisionProcedure::reconstructMipProof(
    const ScipMipProblem& mp, const std::string& filename)
{
  ViprProofReconstructor rec(d_env, mp, d_variables);
  Node conflict;
  std::shared_ptr<ProofNode> proof;
  if (!rec.reconstruct(filename, conflict, proof))
  {
    return false;
  }
  d_mipConflict = conflict;
  d_mipProof = proof;
  return true;
}

namespace {

/** The branch-and-bound node budget of one integer (MIP) check. */
constexpr SCIP_Longint scipMipNodeLimit = 10000;
/**
 * The wall-clock budget of one integer (MIP) check, in seconds. The
 * checks repeat across the full-effort rounds of a solve, so this also
 * bounds the slowdown such rounds can accumulate, as well as the window
 * in which an expiring cvc5 time limit can only abort the process hard
 * (the limit cannot interrupt SCIP cooperatively).
 */
constexpr SCIP_Real scipMipTimeLimit = 2.0;

}  // namespace

bool ScipSimplexDecisionProcedure::buildMip(ScipMipProblem& mp)
{
  CVC5_SCIP_CALL_FALSE(SCIPcreate(&mp.d_scip));
  CVC5_SCIP_CALL_FALSE(SCIPincludeDefaultPlugins(mp.d_scip));
  SCIPsetMessagehdlrQuiet(mp.d_scip, TRUE);
  // Exact solving must be enabled before the problem is created.
  CVC5_SCIP_CALL_FALSE(SCIPenableExactSolving(mp.d_scip, TRUE));
  if (!mp.d_certFile.empty())
  {
    // With proofs the certificate of the solve is requested, to be
    // reconstructed into a cvc5 proof on infeasible outcomes.
    CVC5_SCIP_CALL_FALSE(SCIPsetStringParam(
        mp.d_scip, "certificate/filename", mp.d_certFile.c_str()));
  }
  {
    // The parameter change attempts to reassert the rational layer's
    // threshold, printing a note directly to the error stream.
    StreamSilencer silencer;
    CVC5_SCIP_CALL_FALSE(
        SCIPsetRealParam(mp.d_scip, "numerics/infinity", scipMipInfinity));
  }
  // Presolve derives infeasibility from solution values crossing the
  // floating-point infinity, which is wrong for the exact problem; without
  // presolve the exact LP layer instead rejects such solves (an error,
  // turned into UNKNOWN below), which is sound.
  CVC5_SCIP_CALL_FALSE(
      SCIPsetIntParam(mp.d_scip, "presolving/maxrounds", 0));
  CVC5_SCIP_CALL_FALSE(
      SCIPsetLongintParam(mp.d_scip, "limits/nodes", scipMipNodeLimit));
  CVC5_SCIP_CALL_FALSE(
      SCIPsetRealParam(mp.d_scip, "limits/time", scipMipTimeLimit));
  CVC5_SCIP_CALL_FALSE(SCIPcreateProbBasic(mp.d_scip, "cvc5_linear_arith"));
  CVC5_SCIP_CALL_FALSE(SCIPsetObjsense(mp.d_scip, SCIP_OBJSENSE_MAXIMIZE));

  mp.d_posInf = mp.d_scratch.mkRat();
  mp.d_negInf = mp.d_scratch.mkRat();
  mp.d_zero = mp.d_scratch.mkRat();
  mp.d_one = mp.d_scratch.mkRat();
  CVC5_SCIP_CHECK_RAT_FALSE(mp.d_posInf);
  CVC5_SCIP_CHECK_RAT_FALSE(mp.d_negInf);
  CVC5_SCIP_CHECK_RAT_FALSE(mp.d_zero);
  CVC5_SCIP_CHECK_RAT_FALSE(mp.d_one);
  SCIPrationalSetInfinity(mp.d_posInf);
  SCIPrationalSetNegInfinity(mp.d_negInf);
  SCIPrationalSetReal(mp.d_zero, 0.0);
  SCIPrationalSetReal(mp.d_one, 1.0);

  // the delta variable, maximized in [0,1]
  CVC5_SCIP_CALL_FALSE(SCIPcreateVarBasic(
      mp.d_scip, &mp.d_delta, "delta", 0.0, 1.0, 1.0,
      SCIP_VARTYPE_CONTINUOUS));
  CVC5_SCIP_CALL_FALSE(SCIPaddVarExactData(
      mp.d_scip, mp.d_delta, mp.d_zero, mp.d_one, mp.d_one));
  CVC5_SCIP_CALL_FALSE(SCIPaddVar(mp.d_scip, mp.d_delta));

  // one free variable per arithmetic variable, integral per its type
  char name[32];
  for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                    vend = d_variables.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    snprintf(name, sizeof(name), "v%u", static_cast<unsigned>(v));
    SCIP_VAR* var = nullptr;
    CVC5_SCIP_CALL_FALSE(
        SCIPcreateVarBasic(mp.d_scip,
                           &var,
                           name,
                           -SCIPinfinity(mp.d_scip),
                           SCIPinfinity(mp.d_scip),
                           0.0,
                           d_variables.isInteger(v)
                               ? SCIP_VARTYPE_INTEGER
                               : SCIP_VARTYPE_CONTINUOUS));
    // owned (and released) via d_vars from here on
    mp.d_avars.push_back(v);
    mp.d_vars.push_back(var);
    if (v >= mp.d_toVar.size())
    {
      mp.d_toVar.resize(v + 1, nullptr);
    }
    mp.d_toVar[v] = var;
    CVC5_SCIP_CALL_FALSE(SCIPaddVarExactData(
        mp.d_scip, var, mp.d_negInf, mp.d_posInf, mp.d_zero));
    CVC5_SCIP_CALL_FALSE(SCIPaddVar(mp.d_scip, var));
  }

  // the tableau equalities: (sum_i coeff_i * x_i) - b = 0 per basic b
  std::vector<SCIP_VAR*> cvars;
  std::vector<SCIP_RATIONAL*> cvals;
  SCIP_RATIONAL* minusOne = mp.d_scratch.mkRat(Rational(-1));
  CVC5_SCIP_CHECK_RAT_FALSE(minusOne);
  size_t consIdx = 0;
  for (Tableau::BasicIterator bi = d_tableau.beginBasic(),
                              bend = d_tableau.endBasic();
       bi != bend;
       ++bi, ++consIdx)
  {
    ArithVar basic = *bi;
    std::vector<std::pair<ArithVar, Rational>> content;
    readTableauRow(d_tableau, basic, content);
    cvars.clear();
    cvals.clear();
    cvars.push_back(mp.d_toVar[basic]);
    cvals.push_back(minusOne);
    for (const auto& [nb, coeff] : content)
    {
      SCIP_RATIONAL* c = mp.d_scratch.mkRat(coeff);
      CVC5_SCIP_CHECK_RAT_FALSE(c);
      cvars.push_back(mp.d_toVar[nb]);
      cvals.push_back(c);
    }
    snprintf(name, sizeof(name), "t%zu", consIdx);
    SCIP_CONS* cons = nullptr;
    CVC5_SCIP_CALL_FALSE(
        SCIPcreateConsBasicExactLinear(mp.d_scip,
                                       &cons,
                                       name,
                                       static_cast<int>(cvars.size()),
                                       cvars.data(),
                                       cvals.data(),
                                       mp.d_zero,
                                       mp.d_zero));
    CVC5_SCIP_CALL_FALSE(SCIPaddCons(mp.d_scip, cons));
    CVC5_SCIP_CALL_FALSE(SCIPreleaseCons(mp.d_scip, &cons));
    mp.d_consOrigin.push_back(NullConstraint);
  }

  // the asserted bounds, sharing the traversal of the LP construction
  return forEachAssertedBound(
      d_variables,
      nullptr,
      [&](ConstraintCP bc, ArithVar v, bool lower, const DeltaRational& b)
      {
        SCIP_RATIONAL* c = mp.d_scratch.mkRat(b.getNoninfinitesimalPart());
        if (c == nullptr)
        {
          return false;
        }
        cvars.clear();
        cvals.clear();
        cvars.push_back(mp.d_toVar[v]);
        cvals.push_back(mp.d_one);
        if (!b.infinitesimalIsZero())
        {
          SCIP_RATIONAL* minusK = mp.d_scratch.mkRat(-b.getInfinitesimalPart());
          if (minusK == nullptr)
          {
            return false;
          }
          mp.d_anyStrict = true;
          cvars.push_back(mp.d_delta);
          cvals.push_back(minusK);
        }
        snprintf(name, sizeof(name), "b%zu", consIdx++);
        SCIP_CONS* cons = nullptr;
        if (SCIPcreateConsBasicExactLinear(mp.d_scip,
                                           &cons,
                                           name,
                                           static_cast<int>(cvars.size()),
                                           cvars.data(),
                                           cvals.data(),
                                           lower ? c : mp.d_negInf,
                                           lower ? mp.d_posInf : c)
                != SCIP_OKAY
            || SCIPaddCons(mp.d_scip, cons) != SCIP_OKAY
            || SCIPreleaseCons(mp.d_scip, &cons) != SCIP_OKAY)
        {
          warning() << "SCIP exact constraint creation failed" << std::endl;
          return false;
        }
        mp.d_consOrigin.push_back(bc);
        return true;
      });
}

Result::Status ScipSimplexDecisionProcedure::solveIntegerWithScip()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_mipTime);
  ++d_statistics.d_mipCalls;
  d_mipConflict = Node::null();
  d_mipProof = nullptr;

  ScipMipProblem mp;
  bool produceProofs = options().smt.produceProofs;
  {
    // Request the certificate (SCIP only streams certificates to files):
    // on infeasible outcomes it is reconstructed into a proof (with
    // proofs), or its support minimizes the trusted conflict (without).
    const char* tmpdir = getenv("TMPDIR");
    mp.d_certFile = std::string(tmpdir != nullptr ? tmpdir : "/tmp")
                    + "/cvc5_scip_cert_"
#ifndef _WIN32
                    + std::to_string(getpid()) + "_"
#endif
                    + std::to_string(++d_mipCertCounter) + ".vipr";
  }
  // on return, remove the certificate files (SCIP writes a transformed-
  // and an original-space file)
  struct CertCleanup
  {
    const std::string& d_f;
    ~CertCleanup()
    {
      if (!d_f.empty())
      {
        std::remove(d_f.c_str());
        std::remove((d_f + "_ori").c_str());
      }
    }
  } cleanup{mp.d_certFile};

  if (!buildMip(mp))
  {
    ++(mp.d_scratch.d_unencodable ? d_statistics.d_mipDeclined
                                  : d_statistics.d_mipUnknown);
    return Result::UNKNOWN;
  }
  SCIP_RETCODE rc;
  {
    StreamSilencer silencer;
    rc = SCIPsolve(mp.d_scip);
  }
  if (rc != SCIP_OKAY)
  {
    // e.g. the exact LP layer rejects solves whose values cross the
    // floating-point infinity
    Trace("arith::scip") << "scip mip solve failed (" << rc << ")" << endl;
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
  // concludes an established infeasibility per the proof discipline:
  // without proofs the exact verdict is trusted, with the conflict
  // minimized to the certificate's support; with proofs the certificate
  // is reconstructed into a cvc5 proof, and failing that the check is
  // inconclusive (which is sound)
  auto concludeUnsat = [&]() -> Result::Status {
    // the certificate file is only completed when the instance is
    // released (its solution and status are no longer needed here)
    std::string certFile = mp.d_certFile;
    mp.freeScip();
    if (produceProofs)
    {
      if (!reconstructMipProof(mp, certFile))
      {
        ++d_statistics.d_mipProofsFailed;
        ++d_statistics.d_mipUnknown;
        return Result::UNKNOWN;
      }
      ++d_statistics.d_mipProofs;
    }
    else
    {
      ViprProofReconstructor rec(d_env, mp, d_variables);
      ConstraintCPVec support;
      if (rec.collectSupport(certFile, support))
      {
        d_mipConflict =
            Constraint::externalExplainByAssertions(nodeManager(), support);
      }
      // on failure d_mipConflict stays null; the caller falls back to
      // the conflict over all asserted bounds
    }
    ++d_statistics.d_mipUnsat;
    return Result::UNSAT;
  };
  SCIP_STATUS status = SCIPgetStatus(mp.d_scip);
  if (status == SCIP_STATUS_INFEASIBLE)
  {
    return concludeUnsat();
  }
  if (status != SCIP_STATUS_OPTIMAL)
  {
    Trace("arith::scip") << "scip mip without outcome (status " << status
                         << ")" << endl;
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
  SCIP_SOL* sol = SCIPgetBestSol(mp.d_scip);
  SCIP_RATIONAL* val = mp.d_scratch.mkRat();
  if (sol == nullptr || val == nullptr)
  {
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
  if (mp.d_anyStrict)
  {
    // satisfiable with delta = 0 only: some strict bound is violated by
    // every solution of the closure [cf. the delta encoding of the LP]
    SCIPgetSolValExact(mp.d_scip, sol, mp.d_delta, val);
    if (SCIPrationalIsZero(val))
    {
      return concludeUnsat();
    }
  }
  if (!logicInfo().isLinear())
  {
    // Under the nonlinear extension this layer sees a linear abstraction:
    // infeasibility transfers (handled above), but the abstraction's
    // models are merely candidate points for the model-based refinement,
    // which is built around the small steps of the conventional branching
    // and diverges on the unbiased vertices found here. Leave the model
    // search to the conventional machinery (the backoff of the caller
    // bounds the cost of these outcome-less solves).
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
  // Extract and validate the full solution before any of it is written: a
  // partial import would leave an inconsistent assignment behind. The
  // values of the basic variables follow via the tableau, whose
  // equalities the solution satisfies.
  std::unordered_map<ArithVar, DeltaRational> values;
  for (size_t i = 0; i < mp.d_avars.size(); ++i)
  {
    SCIPgetSolValExact(mp.d_scip, sol, mp.d_vars[i], val);
    if (SCIPrationalIsAbsInfinity(val))
    {
      // the value was coerced on extraction
      ++d_statistics.d_mipUnknown;
      return Result::UNKNOWN;
    }
    values.emplace(mp.d_avars[i], DeltaRational(scipRationalToRational(val)));
  }
  bool imported = importAssignment(
      mp.d_avars,
      [&values](ArithVar v, DeltaRational& dr)
      {
        dr = values[v];
        return true;
      });
  if (!imported)
  {
    ++d_statistics.d_mipUnknown;
    return Result::UNKNOWN;
  }
  Result::Status res = checkImportedModel();
  ++(res == Result::SAT ? d_statistics.d_mipSat : d_statistics.d_mipUnknown);
  return res;
}

#undef CVC5_SCIP_CALL
#undef CVC5_SCIP_CHECK_RAT
#undef CVC5_SCIP_CALL_UNKNOWN
#undef CVC5_SCIP_CHECK_RAT_UNKNOWN
#undef CVC5_SCIP_CALL_FALSE
#undef CVC5_SCIP_CHECK_RAT_FALSE
#undef CVC5_SCIP_CALL_RET
#undef CVC5_SCIP_CHECK_RAT_RET

#else /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

/** Stub so that the persistent instance member can be destructed. */
struct ScipSimplexProblem
{
};

ScipSimplexDecisionProcedure::~ScipSimplexDecisionProcedure() {}

#ifdef CVC5_USE_SCIP
Result::Status ScipSimplexDecisionProcedure::solveWithScip(
    CVC5_UNUSED bool exactResult)
{
  Unreachable()
      << "The SCIP-based simplex requires cvc5 to be built with GMP (not CLN)";
}

Result::Status ScipSimplexDecisionProcedure::solveIntegerWithScip()
{
  Unreachable()
      << "The SCIP-based simplex requires cvc5 to be built with GMP (not CLN)";
}
#endif /* CVC5_USE_SCIP */

#endif /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
