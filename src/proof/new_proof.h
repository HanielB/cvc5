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

#include "cvc4_public.h"

#ifndef CVC4__NEW_PROOF_H
#define CVC4__NEW_PROOF_H

#include <iosfwd>

namespace CVC4 {

enum NewProofRule
{
  RULE_INPUT,
  RULE_RESOLUTION,
  RULE_REFLEXIVITY,
  RULE_SYMMETRY,
  RULE_TRANSITIVITY,
  RULE_CONGRUENCE,
  RULE_PURE_EQ,
  RULE_CONSTANTS
}; /* enum ProofRules */

class ProofStep
{
 public:
  virtual ~ProofStep() {}
  unsigned getId() const { return d_id; }
  NewProofRule getRule() const { return d_rule; }

 protected:
  unsigned d_id;
  NewProofRule d_rule;
}; /* class ProofStep */

/* This will contain the step lists, basically. Then the actual proofs will have
   more information. */
class CVC4_PUBLIC NewProof
{
 public:
  virtual ~NewProof() {}
  virtual void toStream(std::ostream& out) const = 0;
  virtual void addProofStep(NewProofRule rule) = 0;

 protected:
  int d_nextId;
  // int getNextId();
}; /* class NewProof */

inline std::ostream& operator<<(std::ostream& out, NewProofRule r)
{
  switch (r)
  {
    case RULE_INPUT: out << "input"; break;
    case RULE_RESOLUTION: out << "resolution"; break;
    case RULE_REFLEXIVITY: out << "reflexivity"; break;
    case RULE_SYMMETRY: out << "symmetry"; break;
    case RULE_TRANSITIVITY: out << "transitivity"; break;
    case RULE_CONGRUENCE: out << "congruence"; break;
    case RULE_PURE_EQ: out << "pure_eq"; break;
    case RULE_CONSTANTS: out << "constants"; break;

    default: out << "ProofRule Unknown! [" << unsigned(r) << "]";
  }

  return out;
}


}  // namespace CVC4

#endif /* CVC4__NEW_PROOF_H */
