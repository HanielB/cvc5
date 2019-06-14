/*********************                                                        */
/*! \file veriT_proof.cpp
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

#include "proof/verit_proof.h"

#include "proof/new_proof.h"
#include "proof/new_proof_manager.h"

namespace CVC4 {

void VeritProof::toStream(std::ostream& out)
{
  for (ProofStep s : getProofSteps())
  {
    printStep(out, &s);
  }
}

void VeritProof::printStep(std::ostream& out, ProofStep* s)
{
  // out << "(set .c" << s->getId() << " (";// << step->getRule();
  // std::vector<unsigned> premises = s->getPremises();
  // if (!premises.empty())
  // {
  //   out << " :clauses (";
  //   for (unsigned i = 0, size = premises.size(); i < size; ++i)
  //   {
  //     out << ".c" << (i < size -1? " " : "");
  //   }
  //   out << ")";
  // }
  // out << " :conclusion " << s->getConclusion();
  // out << ")";
}

}  // namespace CVC4
