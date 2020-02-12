/*********************                                                        */
/*! \file veriT_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof to be output in the veriT proof format.
 **/

#include "cvc4_private.h"

#include "expr/node.h"
#include "proof/new_proof.h"
#include "theory/theory.h"

#ifndef CVC4__VERIT_PROOF_H
#define CVC4__VERIT_PROOF_H

namespace CVC4 {

class VeritProofStep : public ProofStep
{
 public:
  VeritProofStep(unsigned id, NewProofRule rule);
  ~VeritProofStep() override {}

  void addPremises(std::vector<unsigned>& reasons);
  void addPremises(unsigned reason);
  void addConclusion(Node conclusion);
  void addConclusion(std::vector<Node>& conclusion);

  const std::vector<Node>& getConclusion() const;
  const std::vector<unsigned>& getPremises() const;

 private:
  // invariant: given n + 1 nodes, the first are to be negated in a cluase, while
  // the last one is not
  std::vector<Node> d_conclusion;
  std::vector<unsigned> d_premises;
};

class VeritProof : public NewProof
{
 public:
  ~VeritProof() override {}
  void toStream(std::ostream& out) const override;
  void addProofStep(NewProofRule rule) override;

  void addProofStep(NewProofRule rule,
                    std::vector<unsigned>& reasons,
                    Node conclusion);

  void addProofStep(NewProofRule rule,
                    Node conclusion);

  void addToLastProofStep(Node conclusion);
  void addToLastProofStep(std::vector<unsigned>& reasons, Node conclusion);

  void addTheoryProof(theory::EqProof* proof);

  const std::vector<VeritProofStep>& getProofSteps() const;

 private:
  unsigned getNextId() { return d_nextId++; }

  unsigned processTheoryProof(theory::EqProof* proof);
  /** traverse proof recursively and for every congruence rule with a non-null
   * conclusion, flatten all congruence application in children with nullary
   * conclusions */
  // void flattenBinCongs(theory::EqProof* proof,
  //                      std::vector<theory::EqProof*>& premises);

  void printStep(std::ostream& out, VeritProofStep* s) const;

  std::vector<VeritProofStep> d_proofSteps;

};

}  // namespace CVC4

#endif /* CVC4__VERIT_PROOF_H */
