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

#ifndef CVC4__VERIT_PROOF_H
#define CVC4__VERIT_PROOF_H

namespace CVC4 {

class VeritProofStep : ProofStep
{
 public:
  ~VeritProofStep() override {}
  Node getConclusion() const;
  const std::vector<unsigned>& getPremises() const;

 private:
  Node d_conclusion;
  std::vector<unsigned> d_premises;
};

class VeritProof : public NewProof
{
 public:
  VeritProof() {}
  ~VeritProof() override {}
  void toStream(std::ostream& out) const override;
  void addProofStep(VeritProofStep s);
  const std::vector<VeritProofStep>& getProofSteps() const;

 private:
  void printStep(std::ostream& out, VeritProofStep* s) const;

  std::vector<VeritProofStep> d_proofSteps;

};

}  // namespace CVC4

#endif /* CVC4__VERIT_PROOF_H */
