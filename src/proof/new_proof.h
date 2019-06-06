/*********************                                                        */
/*! \file proof.h
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

enum ProofRule {
  RULE_INPUT,
  RULE_RESOLUTION,
  RULE_REFLEXIVITY,
  RULE_SYMMETRY,
  RULE_TRANSITIVITY,
  RULE_CONGRUENCE,
};/* enum ProofRules */

class NewProof
{
 public:
  virtual ~NewProof() {}
  virtual void toStream(std::ostream& out) const = 0;

 private:
  unsigned d_id;
  ProofRule d_rule;
  Node d_conclusion;
  std::vector<unsigned> d_premises;
}; /* class NewProof */

}/* CVC4 namespace */

#endif /* CVC4__PROOF_H */
