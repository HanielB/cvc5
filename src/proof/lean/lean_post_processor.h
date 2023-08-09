/*********************                                                        */
/*! \file lean_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN_POST_PROCESSOR_H
#define CVC4__PROOF__LEAN_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "proof/lean/lean_node_converter.h"
#include "proof/lean/lean_rules.h"
#include "proof/proof_node_updater.h"
#include "rewriter/rewrite_db.h"

namespace cvc5::internal {

namespace proof {

/**
 * A callback class used by the Lean convereter for post-processing proof nodes
 * by replacing internal rules by the rules in the Lean calculus.
 */
class LeanProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  LeanProofPostprocessCallback(LeanNodeConverter& lnc,
                               rewriter::RewriteDb* rdb);
  /**
   * Initialize, called once for each new ProofNode to process. This
   * initializes static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Update the proof node iff has the LEAN_RULE id. */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

  /** New assumptions added during post-processing
   *
   * Currently these are the rewrite steps used in the proof and holes
   * THEORY_LEMMA, PREPROCESS.
   *
   * These assumptions are added as arguments of the outer scope so that they
   * are properly printed.
   */
  std::unordered_set<Node> d_newRewriteAssumptions;
  std::unordered_set<Node> d_newHoleAssumptions;
  std::unordered_set<Node> d_newAssumptionsCollected;

 protected:
  /** The node converter */
  LeanNodeConverter& d_lnc;

  rewriter::RewriteDb* d_rdb;

  /** Placeholder for the empty clause */
  Node d_empty;
  /** True and false nodes. Cached since used frequently during processing. */
  Node d_true;
  Node d_false;

  /**
   * Recall the Lean rule:
   *  Children: (P1 ... Pn)
   *  Arguments: (id, Q, A1, ..., Am)
   *  ---------------------
   *  Conclusion: (Q)
   *  The id argument is a LeanRule, as defined in proof/lean/lean_rules.h
   *  This allows us to specify which rule in the Lean calculus the current rule
   *  corresponds to.
   * addLeanStep encapsulates translation boilerplate by adding id and Q to
   * arguments, and children and args are passed along verbatim.
   */
  void addLeanStep(Node res,
                   LeanRule rule,
                   Node convertedResult,
                   const std::vector<Node>& children,
                   const std::vector<Node>& args,
                   CDProof& cdp);

  Node getLastDiff(Node clause, Node pivot);
  Node getLastDiffs(Node clause, Node pivot1, Node pivot2);
  Node getSingletonPosition(Node clause,
                            size_t pos,
                            const std::vector<Node>& pivots);
  void buildTransitivyChain(Node conclusion,
                            const std::vector<Node>& links,
                            CDProof* cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Lean calculus.
 */
class LeanProofPostprocess : protected EnvObj
{
 public:
  LeanProofPostprocess(Env& env,
                       LeanNodeConverter& lnc,
                       rewriter::RewriteDb* rdb);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<LeanProofPostprocessCallback> d_cb;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
