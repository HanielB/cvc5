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
  RULE_FACTORING,
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
  RULE_SIMP_IFF,
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
  // "{(equiv formula (and formula (ite_def_1 ... ite_def_n)))}"
  RULE_ITE_INTRO,
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

inline std::ostream& operator<<(std::ostream& out, NewProofRule r)
{
  switch (r)
  {
    case RULE_INPUT: out << "input"; break;
    case RULE_RESOLUTION: out << "resolution"; break;
    case RULE_FACTORING: out << "factoring"; break;
    case RULE_REFLEXIVITY: out << "reflexivity"; break;
    case RULE_SYMMETRY: out << "symmetry"; break;
    case RULE_TRANSITIVITY: out << "transitivity"; break;
    case RULE_CONGRUENCE: out << "congruence"; break;
    case RULE_PURE_EQ: out << "pure_eq"; break;
    case RULE_CONSTANTS: out << "constants"; break;
    case RULE_PREPROCESSING: out << "preprocessing"; break;
    case RULE_PREPROCESSING_REWRITE: out << "preprocessing_rewrite"; break;
    case RULE_PREPROCESSING_THEORY: out << "preprocessing_theory"; break;
    case RULE_ITE_INTRO: out << "ite_intro"; break;
    case RULE_PREPROCESSING_ITE_REMOVAL:
      out << "preprocessing_ite_removal";
      break;
    case RULE_CNF_AND: out << "cnf_and"; break;
    case RULE_CNF_NOT_OR: out << "cnf_not_or"; break;
    case RULE_CNF_AND_POS: out << "cnf_and_pos"; break;
    case RULE_CNF_AND_NEG: out << "cnf_and_neg"; break;
    case RULE_CNF_OR: out << "cnf_or"; break;
    case RULE_CNF_NOT_AND: out << "cnf_not_and"; break;
    case RULE_CNF_OR_POS: out << "cnf_or_pos"; break;
    case RULE_CNF_OR_NEG: out << "cnf_or_neg"; break;
    case RULE_CNF_XOR1: out << "cnf_xor1"; break;
    case RULE_CNF_XOR2: out << "cnf_xor2"; break;
    case RULE_CNF_NOT_XOR1: out << "cnf_not_xor1"; break;
    case RULE_CNF_NOT_XOR2: out << "cnf_not_xor2"; break;
    case RULE_CNF_XOR_POS1: out << "cnf_xor_pos1"; break;
    case RULE_CNF_XOR_POS2: out << "cnf_xor_pos2"; break;
    case RULE_CNF_XOR_NEG1: out << "cnf_xor_neg1"; break;
    case RULE_CNF_XOR_NEG2: out << "cnf_xor_neg2"; break;
    case RULE_CNF_IMPLIES: out << "cnf_implies"; break;
    case RULE_CNF_NOT_IMPLIES1: out << "cnf_not_implies1"; break;
    case RULE_CNF_NOT_IMPLIES2: out << "cnf_not_implies2"; break;
    case RULE_CNF_IMPLIES_POS: out << "cnf_implies_pos"; break;
    case RULE_CNF_IMPLIES_NEG1: out << "cnf_implies_neg1"; break;
    case RULE_CNF_IMPLIES_NEG2: out << "cnf_implies_neg2"; break;
    case RULE_CNF_EQUIV1: out << "cnf_equiv1"; break;
    case RULE_CNF_EQUIV2: out << "cnf_equiv2"; break;
    case RULE_CNF_NOT_EQUIV1: out << "cnf_not_equiv1"; break;
    case RULE_CNF_NOT_EQUIV2: out << "cnf_not_equiv2"; break;
    case RULE_CNF_EQUIV_POS1: out << "cnf_equiv_pos1"; break;
    case RULE_CNF_EQUIV_POS2: out << "cnf_equiv_pos2"; break;
    case RULE_CNF_EQUIV_NEG1: out << "cnf_equiv_neg1"; break;
    case RULE_CNF_EQUIV_NEG2: out << "cnf_equiv_neg2"; break;
    case RULE_CNF_ITE1: out << "cnf_ite1"; break;
    case RULE_CNF_ITE2: out << "cnf_ite2"; break;
    case RULE_CNF_NOT_ITE1: out << "cnf_not_ite1"; break;
    case RULE_CNF_NOT_ITE2: out << "cnf_not_ite2"; break;
    case RULE_CNF_ITE_POS1: out << "cnf_ite_pos1"; break;
    case RULE_CNF_ITE_POS2: out << "cnf_ite_pos2"; break;
    case RULE_CNF_ITE_POS3: out << "cnf_ite_pos3"; break;
    case RULE_CNF_ITE_NEG1: out << "cnf_ite_neg1"; break;
    case RULE_CNF_ITE_NEG2: out << "cnf_ite_neg2"; break;
    case RULE_CNF_ITE_NEG3: out << "cnf_ite_neg3"; break;

    case RULE_UNDEF: out << "undef"; break;

    default: out << "ProofRule Unknown! [" << static_cast<unsigned>(r) << "]";
  }
  return out;
}

}  // namespace CVC4

#endif /* CVC4__NEW_PROOF_H */
