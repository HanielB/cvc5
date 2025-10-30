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
namespace proof {

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
  void logTheoryLemma(
      const Node& n,
      theory::InferenceId id = theory::InferenceId::NONE) override;
  /** Log theory lemma proof */
  void logTheoryLemmaProof(
      std::shared_ptr<ProofNode>& pfn,
      theory::InferenceId id = theory::InferenceId::NONE) override;
  /** Log SAT refutation */
  void logSatRefutation() override;
  void logSatLearnedClausePremises(const Node& n, const std::vector<Node>& premises) override;

  /** Log SAT refutation proof */
  void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn) override;

 private:

  /** Translate the proof node to Alethe, if possible. */
  bool processPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                           bool inner,
                           bool finalStep,
                           std::string& error);

  /** Translate the proof node to Alethe and print it, if successful
   * translation. */
  bool printPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                         bool inner = false,
                         bool finalStep = false);

  bool printPfNodesAlethe(std::vector<std::shared_ptr<ProofNode>>& pfns,
                          const std::vector<Node>& assumptions);

  void printPreprocessingProof(std::vector<std::shared_ptr<ProofNode>>& pfns);

  void collectPreprocessedClauses(std::vector<std::shared_ptr<ProofNode>>& clauses);
  void buildPreproccessingClausesMap();

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
  /** The list of translated preprocessing proofs we were notified of */
  std::map<Node, std::shared_ptr<ProofNode>> d_ppPfs;
  /** The list of translated theory lemma proofs we were notified of */
  std::map<Node, std::shared_ptr<ProofNode>> d_lemmaPfs;
  /** The list of translated SAT clause proofs we were notified of */
  std::map<Node, std::shared_ptr<ProofNode>> d_satClausePfs;

  /** Logged lemmas. Used to avoid logging repeated lemmas. */
  std::unordered_set<Node> d_lemmas;

  bool d_multPPClauses;

  /** Whether there was an error for some logged proof. */
  bool d_hadError;
  /** The cl operator. */
  Node d_cl;


};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */
