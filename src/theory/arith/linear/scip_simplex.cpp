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

#include "base/output.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
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
    ConstraintDatabase& constraintDatabase,
    RaiseConflict conflictChannel,
    RaiseBlackBoxConflict bbConflictChannel,
    TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_constraintDatabase(constraintDatabase),
      d_bbConflictChannel(bbConflictChannel),
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
      d_auxSolves(sr.registerInt("theory::arith::scip::auxSolves")),
      d_lpRebuilds(sr.registerInt("theory::arith::scip::lpRebuilds")),
      d_lpRefreshes(sr.registerInt("theory::arith::scip::lpRefreshes")),
      d_modelImports(sr.registerInt("theory::arith::scip::modelImports")),
      d_probes(sr.registerInt("theory::arith::scip::probes")),
      d_probeTime(sr.registerTimer("theory::arith::scip::probeTime")),
      d_basisRows(sr.registerInt("theory::arith::scip::basisRows")),
      d_basisPropTime(sr.registerTimer("theory::arith::scip::basisPropTime")),
      d_propagatedAtoms(sr.registerInt("theory::arith::scip::propagatedAtoms"))
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
    // The problem contains a constant that cannot be encoded exactly for
    // SCIP (see the class documentation). Delegate the check to the
    // conventional procedure; the consumed signals are bookkeeping only
    // and the error set still holds the violated variables, from which
    // the fallback derives its verdict.
    Trace("arith::scip") << "scip declined; delegating to fallback" << endl;
    return d_fallback->findModel(exactResult);
  }
  return res;
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

void ScipSimplexDecisionProcedure::drainSignals()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_queueTime);
  while (d_errorSet.moreSignals())
  {
    d_errorSet.popSignal();
  }
  d_errorSize = d_errorSet.errorSize();
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
  /** Scratch rationals, freed after each build or refresh. */
  std::vector<SCIP_RATIONAL*> d_rats;

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

  /** Creates a scratch rational owned by this problem, or nullptr. */
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

  /**
   * Creates a scratch rational with the value of the given Rational.
   * SCIP's rational layer coerces any value of absolute value at or above
   * its infinity threshold to infinity on construction, which would lose
   * the distinction between such constants (and thereby soundness). A
   * coerced value is reported by setting d_unencodable and returning null.
   */
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

  /** Whether a constant of the problem was not exactly encodable. */
  bool d_unencodable = false;
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

/** Anonymous-namespace helpers for the LP construction. */

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
    if (p.d_unencodable)
    {
      // A constant of the problem cannot be encoded exactly (see mkRat).
      // The instance is consistent up to the offending row (the mirrors are
      // updated in lockstep with successful additions), so it is kept for
      // future refreshes; the call is declined.
      p.d_unencodable = false;
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
    if (d_persistent->d_unencodable && d_persistent->d_lpi != nullptr)
    {
      // As above: the partial instance is consistent; keep it and decline.
      d_persistent->d_unencodable = false;
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
  std::unordered_set<ConstraintCP> included;
  if (filter != nullptr)
  {
    included.insert(filter->begin(), filter->end());
  }
  int beg[1] = {0};
  for (ArithVariables::var_iterator vi = d_variables.var_begin(),
                                    vend = d_variables.var_end();
       vi != vend;
       ++vi)
  {
    ArithVar v = *vi;
    for (bool lower : {true, false})
    {
      if (lower ? !d_variables.hasLowerBound(v)
                : !d_variables.hasUpperBound(v))
      {
        continue;
      }
      ConstraintCP bc = lower ? d_variables.getLowerBoundConstraint(v)
                              : d_variables.getUpperBoundConstraint(v);
      if (filter != nullptr && included.find(bc) == included.end())
      {
        continue;
      }
      const DeltaRational& b = lower ? d_variables.getLowerBound(v)
                                     : d_variables.getUpperBound(v);
      SCIP_RATIONAL* c = p.mkRat(b.getNoninfinitesimalPart());
      CVC5_SCIP_CHECK_RAT_FALSE(c);
      int nnonz = 1;
      int ind[2] = {p.d_toCol[v], 0};
      SCIP_RATIONAL* val[2] = {p.d_one, nullptr};
      if (!b.infinitesimalIsZero())
      {
        // Strict bounds are expected to tighten: positive delta coefficient
        // on lower bounds, negative on upper bounds.
        Assert(b.infinitesimalSgn() == (lower ? 1 : -1));
        SCIP_RATIONAL* minusK = p.mkRat(-b.getInfinitesimalPart());
        CVC5_SCIP_CHECK_RAT_FALSE(minusK);
        ind[1] = 0;  // the delta column
        val[1] = minusK;
        nnonz = 2;
      }
      SCIP_RATIONAL* lhs[1] = {lower ? c : p.d_negInf};
      SCIP_RATIONAL* rhs[1] = {lower ? p.d_posInf : c};
      CVC5_SCIP_CALL_FALSE(SCIPlpiExactAddRows(
          p.d_lpi, 1, lhs, rhs, nullptr, nnonz, beg, ind, val));
      p.d_boundOrigin.push_back(bc);
      p.d_boundIsLower.push_back(lower);
    }
  }
  return true;
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

bool ScipSimplexDecisionProcedure::importValues(ScipSimplexProblem& p)
{
  // Write the exact solution into the partial model by updating the
  // nonbasic variables; the values of the basic variables follow from the
  // tableau (cf. AttemptSolutionSDP::attempt).
  ++d_statistics.d_modelImports;
  SCIP_RATIONAL** primsol = p.primsolBuffer(p.d_ncols);
  if (primsol == nullptr)
  {
    return false;
  }
  CVC5_SCIP_CALL_RET(
      SCIPlpiExactGetSol(p.d_lpi, nullptr, primsol, nullptr, nullptr, nullptr),
      false);
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
  return true;
}

Result::Status ScipSimplexDecisionProcedure::importModel(ScipSimplexProblem& p)
{
  if (!importValues(p))
  {
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }

  d_errorSet.reduceToSignals();
  drainSignals();
  if (d_errorSet.errorEmpty())
  {
    return Result::SAT;
  }
  // The imported model did not satisfy all bounds; this indicates a
  // discrepancy between the LP encoding and the partial model. Be defensive
  // and give up rather than report an incorrect result.
  warning() << "SCIP model import left bound violations; returning unknown"
            << std::endl;
  ++d_statistics.d_scipUnknown;
  return Result::UNKNOWN;
}

bool ScipSimplexDecisionProcedure::extractCertificate(
    ScipSimplexProblem& p,
    ConstraintCPVec& constraints,
    std::vector<Rational>& coeffs)
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
  // explanations).
  int nrows = p.numRows();
  int ntab = p.numTabRows();
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
  for (int i = ntab; i < nrows; ++i)
  {
    if (!SCIPrationalIsZero(duals[i]))
    {
      constraints.push_back(p.d_boundOrigin[i - ntab]);
      coeffs.push_back(scipRationalToRational(duals[i]));
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
  ConstraintCPVec constraints;
  std::vector<Rational> coeffs;
  if (extractCertificate(p, constraints, coeffs) && constraints.size() >= 2)
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
          d_conflictBuilder->addConstraint(constraints[i], coeffs[i]);
        }
      }
      d_conflictBuilder->addConstraint(constraints[consequent],
                                       coeffs[consequent]);
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

  if (options().smt.produceProofs)
  {
    // Without a certificate no proof-carrying conflict can be built. Give
    // up on this check; reporting unknown is sound.
    warning() << "The SCIP-based simplex found an infeasible system but no "
                 "certificate for it; giving up on this check"
              << std::endl;
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }

  // Fall back to a black box conflict over the full bound set, which is
  // infeasible by the main solve.
  ConstraintCPVec all;
  collectAllBounds(all);
  ++d_statistics.d_fallbackConflicts;
  return raiseConflictOver(all);
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
          if (extractCertificate(p, antecedents, dualCoeffs))
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
#endif /* CVC5_USE_SCIP */

#endif /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
