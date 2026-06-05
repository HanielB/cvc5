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
#include <functional>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "theory/arith/linear/simplex.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class ProofNode;

namespace theory {
namespace arith::linear {

class ConstraintDatabase;
struct ScipSimplexProblem;
struct ScipMipProblem;

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
 * On UNSAT, the exact dual certificate of the LP identifies the
 * participating bound constraints (the minimized conflict) and their Farkas
 * coefficients (its proof, when proofs are enabled), from which a native
 * Farkas conflict is raised.
 *
 * SCIP's rational layer coerces any value of absolute value >= its infinity
 * threshold (1e20 by default) to infinity at construction, which would make
 * distinct huge constants indistinguishable in the LP (and unsound). Every
 * constant is therefore checked when it is translated; if any constant of
 * the problem is not exactly encodable, the call is declined and delegated
 * to the conventional simplex procedure registered via setFallback. A call
 * is likewise declined when an infeasible solve yields no usable
 * certificate, leaving the conflict to the fallback procedure.
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
                               TempVarMalloc tvmalloc);
  ~ScipSimplexDecisionProcedure();

  Result::Status findModel(bool exactResult) override;

  /**
   * Decides the satisfiability of the current bounds and tableau together
   * with the integrality of the integer variables, by a budgeted solve of
   * the corresponding exact mixed-integer program (strict bounds realized
   * by the maximized delta variable, as for the relaxation). Intended at
   * full effort when the relaxation is satisfiable but the assignment is
   * not integral.
   *
   * Returns SAT after writing an exact integral solution into the partial
   * model (verified against the bounds like any import); UNSAT when the
   * MIP is infeasible or its delta maximum is zero, which SCIP established
   * by exact reasoning (without proofs the caller trusts this; with proofs
   * SCIP's certificate is reconstructed into a cvc5 proof, available
   * together with the corresponding conflict via mipConflict/mipProof);
   * and UNKNOWN when the problem was not exactly encodable, the budget was
   * exhausted, SCIP failed, or the certificate could not be reconstructed,
   * in which case the conventional integer machinery should proceed.
   */
  Result::Status findIntegerModel();

  /**
   * The conflict of the last infeasible integer check: the conjunction
   * of the bound constraints in the support of SCIP's certificate (null
   * if it could not be collected; the caller then weakens to all
   * asserted bounds).
   */
  const Node& mipConflict() const { return d_mipConflict; }

  /** The reconstructed proof of the negation of mipConflict() (proof
   * mode only; null otherwise). */
  std::shared_ptr<ProofNode> mipProof() const { return d_mipProof; }

  /**
   * The branching assumptions of the certificate of the last infeasible
   * integer check, as (variable, branch value) pairs: emitting the
   * corresponding branch lemmas makes SCIP's case structure reusable by
   * the SAT solver (see TheoryArithPrivate::scipSolveInteger).
   */
  const std::vector<std::pair<ArithVar, Rational>>& mipSplits() const
  {
    return d_mipSplits;
  }

  /**
   * Registers the procedure to which findModel delegates declined checks
   * (see the class documentation).
   */
  void setFallback(SimplexDecisionProcedure* fallback)
  {
    d_fallback = fallback;
  }

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
   * Theory propagation from the optimal basis of the just-solved feasible
   * LP of p, as a by-product of the feasibility check: no additional LP
   * solves are performed and the stored solution and basis remain valid.
   * For each candidate variable (same atom-based pruning as the probe
   * path) that is basic, the exact row of the basis inverse
   * (SCIPlpiExactGetBInvRow) expresses it as an affine combination of
   * nonbasic bound-row slacks sitting at their bounds, yielding implied
   * bounds in DeltaRational arithmetic (strictness included) together
   * with their Farkas certificate (the row coefficients). Rows whose
   * combination involves the delta column or a nonbasic free column are
   * skipped. This has the strength of one-row bound inference, on SCIP's
   * final basis.
   */
  void propagateBasisRows(ScipSimplexProblem& p);

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
   * Builds the exact mixed-integer program into mp: the delta variable and
   * one variable per arithmetic variable (integral per its type), with the
   * tableau equalities and the asserted bounds as exact linear constraints
   * (sharing the traversal of the LP construction). Returns false on
   * failure.
   */
  bool buildMip(ScipMipProblem& mp);

  /**
   * The body of findIntegerModel. Only defined in builds with SCIP
   * support.
   */
  Result::Status solveIntegerWithScip();

  /**
   * Reconstructs the VIPR certificate of an infeasible exact MIP solve
   * (written to filename) into a cvc5 proof, setting d_mipConflict and
   * d_mipProof on success. See the documentation in the implementation
   * for the translation. Returns false if the certificate could not be
   * reconstructed (the check is then treated as inconclusive).
   */
  bool reconstructMipProof(const ScipMipProblem& mp,
                           const std::string& filename);

  /**
   * Writes an exact assignment into the partial model by updating the
   * nonbasic variables among vars (the basic variables follow via the
   * tableau), querying each value through valueOf. Shared by the model
   * imports of the SCIP backends. Returns false on failure.
   */
  bool importAssignment(
      const std::vector<ArithVar>& vars,
      const std::function<bool(ArithVar, DeltaRational&)>& valueOf);

  /**
   * Writes the exact solution of a feasible solve into the partial model
   * (importAssignment over the LP columns). Returns false on failure.
   */
  bool importValues(ScipSimplexProblem& p);

  /**
   * Processes the signals of a just-imported assignment: SAT if the
   * assignment satisfies all bounds, and a defensive UNKNOWN otherwise.
   * Only used within a check.
   */
  Result::Status checkImportedModel();

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
   * constraints (the minimized conflict) together with their Farkas
   * coefficients, from which a native Farkas conflict (with a proof, if
   * proofs are enabled) is built via the conflict builder. If no usable
   * certificate is obtained, the call is declined (returning UNKNOWN) and
   * findModel delegates the check to the fallback procedure.
   */
  Result::Status raiseScipConflict(ScipSimplexProblem& p);

  /**
   * Extracts the conflict certificate from the exact dual values of the
   * last solve of p: the bound rows with nonzero multiplier in the dual
   * Farkas ray (infeasible LP), or in the optimal dual solution (optimal LP
   * whose delta maximum is zero, for which the dual solution proves the
   * objective bound). The multipliers are converted into coeffs only if it
   * is non-null (they are needed for proofs only). Returns false if no
   * certificate was obtained.
   */
  bool extractCertificate(ScipSimplexProblem& p,
                          ConstraintCPVec& constraints,
                          std::vector<Rational>* coeffs);

  /** The database of constraints (atoms), for matching propagations. */
  ConstraintDatabase& d_constraintDatabase;

  /** The persistent LP instance, lazily created by ensureLp. */
  std::unique_ptr<ScipSimplexProblem> d_persistent;

  /** The conflict of the last infeasible integer check, see mipConflict. */
  Node d_mipConflict;
  /** The proof of the negation of d_mipConflict, see mipProof. */
  std::shared_ptr<ProofNode> d_mipProof;
  /** The splits of the last infeasible integer check, see mipSplits. */
  std::vector<std::pair<ArithVar, Rational>> d_mipSplits;
  /** Counter for unique certificate file names. */
  size_t d_mipCertCounter = 0;

  /** The procedure to delegate declined checks to, see setFallback. */
  SimplexDecisionProcedure* d_fallback = nullptr;
  /**
   * Whether the last call was declined (problem not encodable, or no
   * certificate for an infeasible solve), see setFallback.
   */
  bool d_declined = false;

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
    /** Calls declined as not exactly encodable (delegated to fallback). */
    IntStat d_scipDeclined;
    /** Conflicts raised over a verified minimal candidate subset. */
    IntStat d_subsetConflicts;
    /** Infeasible checks declined to the fallback (no usable certificate). */
    IntStat d_fallbackConflicts;
    /** Time spent extracting conflict certificates. */
    TimerStat d_certTime;
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
    /** Basis inverse rows read for by-product propagation. */
    IntStat d_basisRows;
    /** Time spent in basis-row propagation. */
    TimerStat d_basisPropTime;
    /** Atoms propagated (probe or basis mode). */
    IntStat d_propagatedAtoms;
    /** Integer (MIP) checks, see findIntegerModel. */
    IntStat d_mipCalls;
    /** Integer checks concluded satisfiable (model imported). */
    IntStat d_mipSat;
    /** Integer checks established infeasible. */
    IntStat d_mipUnsat;
    /** Integer checks without an outcome (budget, failures). */
    IntStat d_mipUnknown;
    /** Integer checks declined as not exactly encodable. */
    IntStat d_mipDeclined;
    /** Time spent in integer (MIP) checks. */
    TimerStat d_mipTime;
    /** Certificates reconstructed into proofs (proof mode). */
    IntStat d_mipProofs;
    /** Certificates whose reconstruction failed (proof mode). */
    IntStat d_mipProofsFailed;

    Statistics(StatisticsRegistry& sr);
  } d_statistics;
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
