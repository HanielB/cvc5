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
  /**
   * Translates the current bounds and tableau into a SCIP exact problem,
   * solves it, and imports the result (model or conflict). Only defined in
   * builds with SCIP support.
   */
  Result::Status solveWithScip();

  /**
   * Raises a black box conflict consisting of the conjunction of all
   * currently asserted bound constraints of the given variables. This is
   * sound whenever the conjunction of bounds and tableau equalities is
   * infeasible, but not minimal.
   */
  Result::Status raiseCoarseConflict(const std::vector<ArithVar>& vars);

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
    IntStat d_coarseConflicts;

    Statistics(StatisticsRegistry& sr);
  } d_statistics;
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
