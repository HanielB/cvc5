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
      d_scipTime(sr.registerTimer("theory::arith::scip::solveTime")),
      d_scipCalls(sr.registerInt("theory::arith::scip::calls")),
      d_scipSat(sr.registerInt("theory::arith::scip::sat")),
      d_scipUnsat(sr.registerInt("theory::arith::scip::unsat")),
      d_scipUnknown(sr.registerInt("theory::arith::scip::unknown")),
      d_subsetConflicts(sr.registerInt("theory::arith::scip::subsetConflicts")),
      d_fallbackConflicts(
          sr.registerInt("theory::arith::scip::fallbackConflicts")),
      d_auxSolves(sr.registerInt("theory::arith::scip::auxSolves")),
      d_lpRebuilds(sr.registerInt("theory::arith::scip::lpRebuilds")),
      d_lpRefreshes(sr.registerInt("theory::arith::scip::lpRefreshes")),
      d_modelImports(sr.registerInt("theory::arith::scip::modelImports"))
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

  /**
   * Whether the last solve ended in an infeasible LP, for which a dual
   * Farkas ray is available (as opposed to an optimal LP with zero delta
   * maximum, for which the optimal dual solution is the certificate).
   */
  bool d_lastWasFarkas = false;
  /** Reusable buffer for extracting primal solutions, sized d_primsolCap. */
  SCIP_RATIONAL** d_primsol = nullptr;
  int d_primsolCap = 0;

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
    if (d_lpi != nullptr)
    {
      SCIPlpiExactFree(&d_lpi);
    }
  }

  /** Returns the primal solution buffer with capacity for ncols, or null. */
  SCIP_RATIONAL** primsolBuffer(int ncols)
  {
    if (d_primsolCap < ncols)
    {
      if (d_primsol != nullptr)
      {
        SCIPrationalFreeArray(&d_primsol, d_primsolCap);
        d_primsol = nullptr;
      }
      // grow geometrically to amortize reallocation
      int cap = d_primsolCap == 0 ? 16 : d_primsolCap;
      while (cap < ncols)
      {
        cap *= 2;
      }
      if (SCIPrationalCreateArray(&d_primsol, cap) != SCIP_OKAY)
      {
        d_primsol = nullptr;
        d_primsolCap = 0;
        return nullptr;
      }
      d_primsolCap = cap;
    }
    return d_primsol;
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

  /** Creates a scratch rational with the value of the given Rational. */
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
    Trace("arith::scip") << "scip lp refresh failed; rebuilding" << endl;
    d_persistent.reset();
  }

  d_persistent = std::make_unique<ScipSimplexProblem>();
  ++d_statistics.d_lpRebuilds;
  if (!buildLp(*d_persistent, nullptr))
  {
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

Result::Status ScipSimplexDecisionProcedure::solveWithScip()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_scipTime);
  ++d_statistics.d_scipCalls;

  if (!ensureLp())
  {
    ++d_statistics.d_scipUnknown;
    return Result::UNKNOWN;
  }
  ScipSimplexProblem& p = *d_persistent;
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

#else /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

/** Stub so that the persistent instance member can be destructed. */
struct ScipSimplexProblem
{
};

ScipSimplexDecisionProcedure::~ScipSimplexDecisionProcedure() {}

#ifdef CVC5_USE_SCIP
Result::Status ScipSimplexDecisionProcedure::solveWithScip()
{
  Unreachable()
      << "The SCIP-based simplex requires cvc5 to be built with GMP (not CLN)";
}
#endif /* CVC5_USE_SCIP */

#endif /* CVC5_USE_SCIP && !CVC5_CLN_IMP */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
