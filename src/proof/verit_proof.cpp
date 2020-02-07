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

void VeritProofStep::addPremises(unsigned reason)
{
  d_premises.push_back(reason);
}

void VeritProofStep::addConclusion(Node conclusion)
{
  d_conclusion.push_back(conclusion);
}

void VeritProofStep::addConclusion(std::vector<Node>& conclusion)
{
  d_conclusion.insert(d_conclusion.end(), conclusion.begin(), conclusion.end());
}

const std::vector<Node>& VeritProofStep::getConclusion() const
{
  return d_conclusion;
}

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
      Debug("newproof::pm")
          << "VeritProof::addProfStep: adding proof step with id/rule: " << id
          << " / " << rule << "\n";
      d_proofSteps.push_back(VeritProofStep(id, rule));
      break;
    }
    default:
      Debug("newproof::pm") << "VeritProof::addProfStep: unrecognized rule (or "
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
      Debug("newproof::pm")
          << "VeritProof::addProfStep: adding proof step with id/rule: " << id
          << " / " << rule << " " << conclusion << "\n";
      VeritProofStep vtproofstep = VeritProofStep(id, rule);
      vtproofstep.addConclusion(conclusion);
      d_proofSteps.push_back(vtproofstep);
      break;
    }
    default:
      Debug("newproof::pm") << "VeritProof::addProfStep: unrecognized rule (or "
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
      Debug("newproof::pm")
          << "VeritProof::addProfStep: adding proof step with id/rule: " << id
          << " / " << rule << " "  //<< reasons << " "
          << conclusion << "\n";
      VeritProofStep vtproofstep = VeritProofStep(id, rule);
      vtproofstep.addPremises(reasons);
      vtproofstep.addConclusion(conclusion);
      d_proofSteps.push_back(vtproofstep);
      break;
    }
    default:
      Debug("newproof::pm") << "VeritProof::addProfStep: unrecognized rule (or "
                               "non-simple rule)\n";
  }
}

void VeritProof::addToLastProofStep(Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToLastProfStep: adding to last "
                           "proof step with id/rule: "
                        << d_proofSteps.back().getId() << " / "
                        << d_proofSteps.back().getRule() << "\n";
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::addToLastProofStep(std::vector<unsigned>& reasons,
                                    Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToLastProfStep: adding to last "
                           "proof step with id/rule: "
                        << d_proofSteps.back().getId() << " / "
                        << d_proofSteps.back().getRule() << "\n";
  d_proofSteps.back().addPremises(reasons);
  d_proofSteps.back().addConclusion(conclusion);
}

// recursive call for building the proof

unsigned VeritProof::processTheoryProof(theory::EqProof* proof)
{
  // add proof step for valid clause
  unsigned current_id = getNextId();
  d_proofSteps.push_back(
      VeritProofStep(current_id, NewProofManager::convert(proof->d_id)));
  unsigned i, size = proof->d_children.size();
  std::vector<Node> child_proofs_conclusions, child_proofs_leafs;
  for (i = 0; i < size; ++i)
  {
    child_proofs_conclusions.push_back(proof->d_children[i]->d_node);
  }
  d_proofSteps.back().addConclusion(child_proofs_conclusions);
  d_proofSteps.back().addConclusion(proof->d_node);
  // recursively process proofs that have premises
  unsigned child_id, next_id;
  for (i = 0; i < size; ++i)
  {
    if (!proof->d_children[i]->d_children.empty())
    {
      child_id = processTheoryProof(proof->d_children[i].get());
      // add resolution step between current proof step and resulting proof step
      // from processing child proof
      next_id = getNextId();
      // child proof is not a unit clause
      AlwaysAssert(d_proofSteps[child_id].getConclusion().size() > 1);
      // TODO make sure the invariant that the id corresponds to the proof step
      // in the table is always respected
      child_proofs_leafs.insert(
          child_proofs_leafs.end(),
          d_proofSteps[child_id].getConclusion().begin(),
          d_proofSteps[child_id].getConclusion().end() - 1);
      d_proofSteps.push_back(VeritProofStep(next_id, RULE_RESOLUTION));
      d_proofSteps.back().addPremises(child_id);
      d_proofSteps.back().addPremises(current_id);
      // current leafs - child_conclusion i + child_conclusions i+1.. +
      // proof->d_node
      d_proofSteps.back().addConclusion(child_proofs_leafs);
      for (unsigned j = i + 1; j < size; ++j)
      {
        d_proofSteps.back().addConclusion(child_proofs_conclusions[j]);
      }
      d_proofSteps.back().addConclusion(proof->d_node);
      // make last added clause the current clause
      current_id = next_id;
    }
    else
    {
      child_proofs_leafs.push_back(child_proofs_conclusions[i]);
    }
  }
  return current_id;
}

void VeritProof::addTheoryProof(theory::EqProof* proof)
{
  Debug("newproof::pm") << "VeritProof::addTheoryProof:\n";
  if (Debug.isOn("newproof::pm"))
  {
    proof->debug_print("newproof::pm", 1);
  }
  // TODO traverse the proof bottom up (just as it has been constructed).
  // Anything that has more than one level must be turned into a resolution of
  // clauses. The (valid) clauses are always the conclusion and the conclusions
  // of the premises.
  processTheoryProof(proof);
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
      out << ".c" << i << (i < size - 1 ? " " : "");
    }
    out << ")";
  }
  out << " :conclusion " << s->getConclusion();
  out << ")\n";
}

}  // namespace CVC4
