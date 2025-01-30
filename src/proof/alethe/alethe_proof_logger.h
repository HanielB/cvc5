/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe proof logger utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_LOGGER_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_LOGGER_H

#include "proof/alethe/alethe_let_binding.h"
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_post_processor.h"
#include "proof/alethe/alethe_printer.h"
#include "smt/proof_logger.h"

namespace cvc5::internal {

/**
 * The implementation of a proof logger for Alethe proofs
 */
class AletheProofLogger : public ProofLogger
{
 public:
  /** */
  AletheProofLogger(Env& env,
                    std::ostream& out,
                    smt::PfManager* pm,
                    smt::Assertions& as,
                    smt::ProofPostprocess* ppp);
  ~AletheProofLogger();
  /** Log preprocessing input */
  void logCnfPreprocessInputs(const std::vector<Node>& inputs) override;
  /** Log preprocessing input proof */
  void logCnfPreprocessInputProofs(
      std::vector<std::shared_ptr<ProofNode>>& pfns) override;
  /** Log theory lemma */
  void logTheoryLemma(const Node& n) override;
  /** Log theory lemma proof */
  void logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn) override;
  /** Log SAT refutation */
  void logSatRefutation() override;
  /** Log SAT refutation proof */
  void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn) override;

  /** Translate the proof node to Alethe and print it. */
  void printPfNodeAlethe(std::shared_ptr<ProofNode> pfn, bool inner = false);

 private:
  /** The output stream */
  std::ostream& d_out;
  /** Pointer to the proof manager, for connecting proofs to inputsw */
  smt::PfManager* d_pm;
  /** Pointer to the proof node manager */
  ProofNodeManager* d_pnm;
  /** Reference to the assertions of SMT solver */
  smt::Assertions& d_as;
  /** Pointer to the proof post-processor */
  smt::ProofPostprocess* d_ppp;
  /** The node converter, used for printing */
  proof::AletheNodeConverter d_anc;
  /** The Alethe proof post processor */
  proof::AletheProofPostprocess d_appproc;
  /** The proof printer */
  proof::AletheProofPrinter d_apprinter;
  /** The preprocessing proof we were notified of, which we may have created */
  std::shared_ptr<ProofNode> d_ppProof;
  /**
   * The list of theory lemma proofs we were notified of, which we may have
   * created.
   */
  std::vector<std::shared_ptr<ProofNode>> d_lemmaPfs;

  /** Whether there was an error for some logged proof. */
  bool d_hadError;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */
