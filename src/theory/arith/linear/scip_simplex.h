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

#include "cvc5_private.h"

#pragma once

#include "theory/arith/linear/simplex.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

struct ScipSimplexProblem;

/**
 * A drop-in alternative to the simplex decision procedures that delegates
 * the satisfiability check of the real relaxation (the variable bounds
 * together with the linear equalities of the tableau) to the SCIP exact
 * rational solver (https://www.scipopt.org, SCIP >= 10 with exact solving).
 *
 * Strict bounds arrive at this level encoded as delta-rationals c + k*delta
 * (see delta_rational.h). They are translated for SCIP by realizing delta as
 * an explicit LP variable in [0, 1] whose value is maximized: a bound
 * c + k*delta on variable x becomes the constraint x - k*delta {>=,<=} c, and
 * the delta-rational system is satisfiable iff the exact optimum of delta is
 * positive [cf. Dutertre and de Moura, CAV 2006, Lemma 1].
 *
 * On SAT, the exact rational solution is imported into the partial model by
 * updating the nonbasic variables (basic variables follow via the tableau).
 * On UNSAT, a (currently coarse) black box conflict over the asserted bound
 * constraints is raised; deriving minimal Farkas conflicts from SCIP's exact
 * dual certificate is planned.
 *
 * Only available in builds configured with --scip; the option
 * --use-scip-simplex guards selection of this procedure.
 */
class ScipSimplexDecisionProcedure : public SimplexDecisionProcedure
{
 public:
  ScipSimplexDecisionProcedure(Env& env,
                               LinearEqualityModule& linEq,
                               ErrorSet& errors,
                               RaiseConflict conflictChannel,
                               RaiseBlackBoxConflict bbConflictChannel,
                               TempVarMalloc tvmalloc);

  Result::Status findModel(bool exactResult) override;

 private:
  /** The outcome of one exact LP solve, see solveLp. */
  enum class ScipSolveResult
  {
    /** A (delta-)satisfying assignment exists. */
    FEASIBLE,
    /** The system, including the strictness of bounds, is infeasible. */
    INFEASIBLE,
    /** SCIP failed or was inconclusive. */
    UNKNOWN
  };

  /**
   * Translates the current bounds and tableau into an exact LP, solves it
   * via SCIP's exact LP interface, and imports the result (model or
   * conflict). Only defined in builds with SCIP support.
   */
  Result::Status solveWithScip();

  /**
   * Builds the exact LP into p: one free column per arithmetic variable
   * (plus the delta column if any included bound is strict), one row per
   * included bound constraint (all bounds if filter is null), and one row
   * per tableau equality. The objective maximizes delta if present, so that
   * the delta-rational system is satisfiable iff the exact optimum of delta
   * is positive. Returns false on failure.
   */
  bool buildLp(ScipSimplexProblem& p, const ConstraintCPVec* filter);

  /**
   * Solves the exact LP of p and classifies the outcome, including the test
   * whether the delta optimum is positive when strict bounds are present.
   */
  ScipSolveResult solveLp(ScipSimplexProblem& p);

  /**
   * Imports the exact solution of a feasible solve into the partial model by
   * updating the nonbasic variables. Returns SAT on success.
   */
  Result::Status importModel(ScipSimplexProblem& p);

  /**
   * Computes, raises and returns the conflict for an infeasible solve. The
   * exact dual certificate of the LP identifies the subset of the bound
   * constraints participating in the infeasibility. Falls back to the full
   * bound set if no usable certificate is obtained.
   */
  Result::Status raiseScipConflict(ScipSimplexProblem& p);

  /**
   * Extracts the conflict subset from the exact dual certificate of the
   * last solve of p: the bound rows with nonzero multiplier in the dual
   * Farkas ray (infeasible LP), or in the optimal dual solution (optimal LP
   * whose delta maximum is zero, for which the dual solution proves the
   * objective bound). Returns false if no proper subset was obtained.
   */
  bool extractCandidates(ScipSimplexProblem& p, ConstraintCPVec& candidates);

  /**
   * Raises a black box conflict consisting of the conjunction of the given
   * bound constraints. This is sound whenever the given bounds together with
   * the tableau equalities are infeasible, but carries no proof.
   */
  Result::Status raiseConflictOver(const ConstraintCPVec& bounds);

  /** Collects all currently asserted bound constraints. */
  void collectAllBounds(ConstraintCPVec& bounds) const;

  /** Channel for raising node-based (black box) conflicts. */
  RaiseBlackBoxConflict d_bbConflictChannel;

  bool processSignals()
  {
    TimerStat& timer = d_statistics.d_queueTime;
    IntStat& conflictStat = d_statistics.d_conflicts;
    return standardProcessSignals(timer, conflictStat);
  }

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics
  {
   public:
    TimerStat d_queueTime;
    IntStat d_conflicts;
    TimerStat d_scipTime;
    IntStat d_scipCalls;
    IntStat d_scipSat;
    IntStat d_scipUnsat;
    IntStat d_scipUnknown;
    /** Conflicts raised over a verified minimal candidate subset. */
    IntStat d_subsetConflicts;
    /** Conflicts raised over the full bound set (no usable subset). */
    IntStat d_fallbackConflicts;
    /** Additional exact solves for harvesting duals and verification. */
    IntStat d_auxSolves;

    Statistics(StatisticsRegistry& sr);
  } d_statistics;
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
