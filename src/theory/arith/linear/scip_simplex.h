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

#include <cstdint>
#include <memory>

#include "theory/arith/linear/simplex.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class ConstraintDatabase;
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
                               ConstraintDatabase& constraintDatabase,
                               RaiseConflict conflictChannel,
                               RaiseBlackBoxConflict bbConflictChannel,
                               TempVarMalloc tvmalloc);
  ~ScipSimplexDecisionProcedure();

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
   *
   * Note that the model of a feasible solve is imported eagerly at every
   * effort: the materialized assignment is what allows the cheap
   * assignment-based preamble (and the assertion-time bookkeeping) to
   * answer subsequent checks without an LP solve. An experiment deferring
   * the import below full effort caused an order-of-magnitude regression
   * (every new-fact batch forced an LP re-solve) and interacted unsoundly
   * with the integer layer, which branches on assignment values.
   *
   * On feasible full-effort checks (exactResult), theory propagation by
   * exact objective probing is performed when enabled (see
   * propagateFromLp).
   */
  Result::Status solveWithScip(bool exactResult);

  /**
   * Theory propagation by exact bound probing (objective-based bound
   * tightening) on the just-solved feasible LP of p: for each variable
   * with an unassigned atom that holds in the LP model (a necessary
   * condition for entailment), the exact strongest implied bound is
   * computed by re-solving the LP with the variable as the (maximized or
   * minimized) objective, warm-started from the previous basis. The
   * strongest existing atom entailed by that bound (per
   * ConstraintDatabase::getBestImpliedBound) is then marked as implied,
   * with the optimal dual solution of the probe providing the antecedent
   * bound constraints and exact Farkas coefficients, and is enqueued for
   * propagation (Constraint::tryToPropagate); the existing machinery emits
   * it and builds its explanation lazily on demand.
   */
  void propagateFromLp(ScipSimplexProblem& p);

  /**
   * Solves the LP of p (warm-started) for the current objective and
   * returns true if it is optimal with finite optimum, storing the exact
   * optimum in value.
   */
  bool probeSolve(ScipSimplexProblem& p, Rational& value);

  /**
   * Builds the exact LP into p from scratch: the delta column and one free
   * column per arithmetic variable, one row per tableau equality, and one
   * row per included bound constraint (all bounds if filter is null). The
   * objective maximizes delta in [0,1], so that the delta-rational system
   * is satisfiable iff the exact optimum of delta is positive (delta is
   * unconstrained, with optimum 1, when no included bound is strict).
   * Returns false on failure.
   */
  bool buildLp(ScipSimplexProblem& p, const ConstraintCPVec* filter);

  /**
   * Ensures that the persistent LP instance reflects the current bounds and
   * tableau, building or incrementally refreshing it: columns and tableau
   * rows persist across calls (verified against a mirror, with a full
   * rebuild on any mismatch, e.g. after tableau resets), while the bound
   * rows are replaced on every call. Re-solving the persistent instance
   * warm-starts from the previous basis. Returns false on failure.
   */
  bool ensureLp();

  /**
   * Adds one LP row per bound constraint in filter (all bounds if filter is
   * null) to p. Returns false on failure.
   */
  bool addBoundRows(ScipSimplexProblem& p, const ConstraintCPVec* filter);

  /**
   * Solves the exact LP of p and classifies the outcome, including the test
   * whether the delta optimum is positive when strict bounds are present.
   */
  ScipSolveResult solveLp(ScipSimplexProblem& p);

  /**
   * Writes the exact solution of a feasible solve into the partial model by
   * updating the nonbasic variables (the basic variables follow via the
   * tableau). Returns false on failure.
   */
  bool importValues(ScipSimplexProblem& p);

  /**
   * Imports the exact solution of a feasible solve into the partial model
   * (importValues) and processes the resulting signals. Returns SAT on
   * success. Only used within a check.
   */
  Result::Status importModel(ScipSimplexProblem& p);

  /**
   * Bookkeeping-only counterpart of processSignals: consumes all error-set
   * signals without performing the row-based conflict checks, leaving any
   * infeasibility to be detected by the LP.
   */
  void drainSignals();

  /**
   * Computes, raises and returns the conflict for an infeasible solve. The
   * exact dual certificate of the LP identifies the participating bound
   * constraints together with their Farkas coefficients, from which a
   * native Farkas conflict (with a proof, if proofs are enabled) is built
   * via the conflict builder. Falls back to a black box conflict over the
   * full bound set if no certificate is obtained (or, with proofs, gives
   * up and returns UNKNOWN, which is sound).
   */
  Result::Status raiseScipConflict(ScipSimplexProblem& p);

  /**
   * Extracts the conflict certificate from the exact dual values of the
   * last solve of p: the bound rows with nonzero multiplier in the dual
   * Farkas ray (infeasible LP), or in the optimal dual solution (optimal LP
   * whose delta maximum is zero, for which the dual solution proves the
   * objective bound), together with those exact multipliers. Returns false
   * if no certificate was obtained.
   */
  bool extractCertificate(ScipSimplexProblem& p,
                          ConstraintCPVec& constraints,
                          std::vector<Rational>& coeffs);

  /**
   * Raises a black box conflict consisting of the conjunction of the given
   * bound constraints. This is sound whenever the given bounds together with
   * the tableau equalities are infeasible, but carries no proof.
   */
  Result::Status raiseConflictOver(const ConstraintCPVec& bounds);

  /** Collects all currently asserted bound constraints. */
  void collectAllBounds(ConstraintCPVec& bounds) const;

  /** The database of constraints (atoms), for matching propagations. */
  ConstraintDatabase& d_constraintDatabase;
  /** Channel for raising node-based (black box) conflicts. */
  RaiseBlackBoxConflict d_bbConflictChannel;

  /** The persistent LP instance, lazily created by ensureLp. */
  std::unique_ptr<ScipSimplexProblem> d_persistent;

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics
  {
   public:
    /** Time spent consuming error-set signals (see drainSignals). */
    TimerStat d_queueTime;
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
    /** Full (re)builds of the persistent LP instance. */
    IntStat d_lpRebuilds;
    /** Incremental refreshes of the persistent LP instance. */
    IntStat d_lpRefreshes;
    /** Materialized model imports. */
    IntStat d_modelImports;
    /** Bound probes (LP re-solves with a variable objective). */
    IntStat d_probes;
    /** Time spent in bound probing and propagation. */
    TimerStat d_probeTime;
    /** Atoms propagated from probe results. */
    IntStat d_propagatedAtoms;

    Statistics(StatisticsRegistry& sr);
  } d_statistics;
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
