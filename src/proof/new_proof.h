/*********************                                                        */
/*! \file new_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#include "expr/node.h"

#ifndef CVC4__NEW_PROOF_H
#define CVC4__NEW_PROOF_H

#include <iosfwd>

namespace CVC4 {

enum NewProofRule {
  RULE_INPUT,
  RULE_RESOLUTION,
  RULE_REFLEXIVITY,
  RULE_SYMMETRY,
  RULE_TRANSITIVITY,
  RULE_CONGRUENCE,
};/* enum ProofRules */

class ProofStep
{
 public:
  ~ProofStep() {}

  const unsigned getId() { return d_id; }
  const NewProofRule getRule() { return d_rule; }
  Node getConclusion() { return d_conclusion; }
  const std::vector<unsigned>& getPremises() const { return d_premises; }

 private:
  unsigned d_id;
  NewProofRule d_rule;
  Node d_conclusion;
  std::vector<unsigned> d_premises;
}; /* class ProofStep */


/* This will contain the step lists, basically. Then the actual proofs will have
   more information. */
class NewProof
{
 public:
  ~NewProof() {}
  void toStream(std::ostream& out);

  void addProofStep(ProofStep s);

  const std::vector<ProofStep>& getProofSteps() const { return d_proofSteps; }

 private:
  std::vector<ProofStep> d_proofSteps;

  int d_nextId;

  int getNextId() { return d_nextId++; }
}; /* class NewProof */


std::ostream& operator<<(std::ostream& out, CVC4::NewProofRule r)
{
  switch (r)
  {
    case RULE_INPUT: out << "input"; break;
    case RULE_RESOLUTION: out << "resolution"; break;
    case RULE_REFLEXIVITY: out << "reflexivity"; break;
    case RULE_SYMMETRY: out << "symmetry"; break;
    case RULE_TRANSITIVITY: out << "transitivity"; break;
    case RULE_CONGRUENCE: out << "congruence"; break;
    default: out << "ProofRule Unknown! [" << unsigned(r) << "]";
  }

  return out;
}

}/* CVC4 namespace */

#endif /* CVC4__PROOF_H */
