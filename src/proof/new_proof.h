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
  RULE_CONSTANTS,
  RULE_PREPROCESSING,
  RULE_PREPROCESSING_REWRITE,
  RULE_PREPROCESSING_THEORY,
  RULE_PREPROCESSING_ITE_REMOVAL,
  RULE_THEORY_LEMMA,
  RULE_CNF_AND,
  RULE_CNF_NOT_OR,
  RULE_CNF_AND_POS,
  RULE_CNF_AND_NEG,
  RULE_CNF_OR,
  RULE_CNF_NOT_AND,
  RULE_CNF_OR_POS,
  RULE_CNF_OR_NEG,
  RULE_CNF_XOR1,
  RULE_CNF_XOR2,
  RULE_CNF_NOT_XOR1,
  RULE_CNF_NOT_XOR2,
  RULE_CNF_XOR_POS1,
  RULE_CNF_XOR_POS2,
  RULE_CNF_XOR_NEG1,
  RULE_CNF_XOR_NEG2,
  RULE_CNF_IMPLIES,
  RULE_CNF_NOT_IMPLIES1,
  RULE_CNF_NOT_IMPLIES2,
  RULE_CNF_IMPLIES_POS,
  RULE_CNF_IMPLIES_NEG1,
  RULE_CNF_IMPLIES_NEG2,
  RULE_CNF_EQUIV1,
  RULE_CNF_EQUIV2,
  RULE_CNF_NOT_EQUIV1,
  RULE_CNF_NOT_EQUIV2,
  RULE_CNF_EQUIV_POS1,
  RULE_CNF_EQUIV_POS2,
  RULE_CNF_EQUIV_NEG1,
  RULE_CNF_EQUIV_NEG2,
  RULE_CNF_ITE1,
  RULE_CNF_ITE2,
  RULE_CNF_NOT_ITE1,
  RULE_CNF_NOT_ITE2,
  RULE_CNF_ITE_POS1,
  RULE_CNF_ITE_POS2,
  /* NOT [IF A THEN B ELSE C] OR B OR C */
  RULE_CNF_ITE_POS3,
  RULE_CNF_ITE_NEG1,
  RULE_CNF_ITE_NEG2,
  /* [IF A THEN B ELSE C] OR NOT B OR NOT C */
  RULE_CNF_ITE_NEG3,
  RULE_UNDEF
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
  virtual unsigned addProofStep(NewProofRule rule) = 0;
  virtual void finishProof() = 0;

 protected:
  unsigned d_nextId;

}; /* class NewProof */

}  // namespace CVC4

#endif /* CVC4__NEW_PROOF_H */
