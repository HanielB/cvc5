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

VeritProofStep::VeritProofStep(unsigned id, NewProofRule rule)
{
  d_id = id;
  d_rule = rule;
}

void VeritProofStep::addPremises(std::vector<unsigned>& reasons)
{
  d_premises = reasons;
}

void VeritProofStep::addConclusion(Node conclusion)
{
  d_conclusion = conclusion;
}

Node VeritProofStep::getConclusion() const { return d_conclusion; }

const std::vector<unsigned>& VeritProofStep::getPremises() const
{
  return d_premises;
}

const std::vector<VeritProofStep>& VeritProof::getProofSteps() const
{
  return d_proofSteps;
};

void VeritProof::toStream(std::ostream& out) const
{
  out << "VERIT PROOF!!!!!!!!!!!!!!!!!!!!\n";
  for (VeritProofStep s : getProofSteps())
  {
    printStep(out, &s);
  }
}

void VeritProof::addProofStep(NewProofRule rule)
{
  switch (rule)
  {
    case RULE_INPUT:
    case RULE_RESOLUTION:
    case RULE_REFLEXIVITY:
    case RULE_SYMMETRY:
    case RULE_TRANSITIVITY:
    case RULE_CONGRUENCE:
    {
      unsigned id = getNextId();
      Debug("newproof:pm") << "VeritProof::addProfStep: adding proof step with "
                           << id// << " " << rule
                           << "\n";
      d_proofSteps.push_back(VeritProofStep(id, rule));
      break;
    }
    default:
      Debug("newproof:pm") << "VeritProof::addProfStep: unrecognized rule (or "
                              "non-simple rule)\n";
  }
}

void VeritProof::addProofStep(NewProofRule rule, Node conclusion)
{
  switch (rule)
  {
    case RULE_INPUT:
    case RULE_RESOLUTION:
    case RULE_REFLEXIVITY:
    case RULE_SYMMETRY:
    case RULE_TRANSITIVITY:
    case RULE_CONGRUENCE:
    {
      unsigned id = getNextId();
      Debug("newproof:pm") << "VeritProof::addProfStep: adding proof step with "
                           << id << " " << rule
                           << " " << conclusion << "\n";
      VeritProofStep vtproofstep = VeritProofStep(id, rule);
      vtproofstep.addConclusion(conclusion);
      d_proofSteps.push_back(vtproofstep);
      break;
    }
    default:
      Debug("newproof:pm") << "VeritProof::addProfStep: unrecognized rule (or "
                              "non-simple rule)\n";
  }
}

void VeritProof::addProofStep(NewProofRule rule,
                              std::vector<unsigned>& reasons,
                              Node conclusion)
{
  switch (rule)
  {
    case RULE_INPUT:
    case RULE_RESOLUTION:
    case RULE_REFLEXIVITY:
    case RULE_SYMMETRY:
    case RULE_TRANSITIVITY:
    case RULE_CONGRUENCE:
    {
      unsigned id = getNextId();
      Debug("newproof:pm") << "VeritProof::addProfStep: adding proof step with "
                           << id << " " << rule
                           << " " //<< reasons << " "
                           << conclusion << "\n";
      VeritProofStep vtproofstep = VeritProofStep(id, rule);
      vtproofstep.addPremises(reasons);
      vtproofstep.addConclusion(conclusion);
      d_proofSteps.push_back(vtproofstep);
      break;
    }
    default:
      Debug("newproof:pm") << "VeritProof::addProfStep: unrecognized rule (or "
                              "non-simple rule)\n";
  }
}

void VeritProof::addToLastProofStep(Node conclusion)
{
  Debug("newproof:pm")
      << "VeritProof::addToLastProfStep: adding to last proof step with id "
      << d_proofSteps.back().getId() << " " << d_proofSteps.back().getRule()
      << "\n";
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::addToLastProofStep(std::vector<unsigned>& reasons,
                                    Node conclusion)
{
  Debug("newproof:pm")
      << "VeritProof::addToLastProfStep: adding to last proof step with id "
      << d_proofSteps.back().getId() << " " << d_proofSteps.back().getRule()
      << "\n";
  d_proofSteps.back().addPremises(reasons);
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::addTheoryProof(unsigned id, theory::EqProof* proof)
{
  NewRule r = NewProofManager::convert(proof->d_id);
  if (!d_children.empty())
  {

    if (!d_node.isNull())
    {
      os << std::endl;
      for (unsigned i = 0; i < tb + 1; i++)
      {
        os << "  ";
      }
      os << d_node;
    }
    for (unsigned i = 0; i < d_children.size(); i++)
    {
      if (i > 0 || !d_node.isNull())
      {
        os << ",";
      }
      os << std::endl;
      d_children[i]->debug_print(os, tb + 1, prettyPrinter);
    }
  }
  os << ")" << std::endl;


}

void VeritProof::addTheoryProof(theory::EqProof* proof)
{
  unsigned id = getNextId();
  // TODO traverse the proof bottom up (just as it has been constructed). Anything
  // that has more than one level must be turned into a resolution of
  // clauses. The (valid) clauses are always the conclusion and the conclusions
  // of the premises.
  d_proofSteps.back().addPremises(reasons);
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::printStep(std::ostream& out, VeritProofStep* s) const
{
  out << "(set .c" << s->getId() << " (" << s->getRule();
  const std::vector<unsigned>& premises = s->getPremises();
  if (!premises.empty())
  {
    out << " :clauses (";
    for (unsigned i = 0, size = premises.size(); i < size; ++i)
    {
      out << ".c" << (i < size -1? " " : "");
    }
    out << ")";
  }
  out << " :conclusion " << s->getConclusion();
  out << ")\n";
}

}  // namespace CVC4
