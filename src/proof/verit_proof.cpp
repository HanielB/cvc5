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
void flattenBinCongs(theory::EqProof* proof);

void flattenBinCongs2(theory::EqProof* proof,
                      std::vector<std::shared_ptr<theory::EqProof>>& premises)
{
  if (Debug.isOn("newproof::pm-flattening"))
  {
    Debug("newproof::pm-flattening") << "flattenBinCongs2::\tFlattenning proof:\n";
    proof->debug_print("newproof::pm-flattening");
    Debug("newproof::pm-flattening") << "===\n";
  }
  unsigned i, size = proof->d_children.size();
  if (proof->d_id == theory::MERGED_THROUGH_CONGRUENCE
      && proof->d_node.isNull())
  {
    for (i = 0; i < size; ++i)
    {
      Debug("newproof::pm-flattening") << push;
      flattenBinCongs2(proof->d_children[i].get(), premises);
      Debug("newproof::pm-flattening") << pop;
    }
    return;
  }
  Debug("newproof::pm-flattening")
      << "flattenBinCongs2::\tNot flat-amenable proof, recurse\n";
  std::shared_ptr<theory::EqProof> pb = std::make_shared<theory::EqProof>();
  pb->d_node = proof->d_node;
  pb->d_id = proof->d_id;
  pb->d_children = proof->d_children;

  flattenBinCongs(pb.get());
  premises.push_back(pb);
}

void flattenBinCongs(theory::EqProof* proof)
{
  if (Debug.isOn("newproof::pm-flattening"))
  {
    Debug("newproof::pm-flattening") << "flattenBinCongs::\tFlattenning proof:\n";
    proof->debug_print("newproof::pm-flattening");
    Debug("newproof::pm-flattening") << "===\n";
  }
  unsigned i, size = proof->d_children.size();
  if (proof->d_id == theory::MERGED_THROUGH_EQUALITY
      || proof->d_id == theory::MERGED_THROUGH_REFLEXIVITY
      || proof->d_id == theory::MERGED_THROUGH_CONSTANTS)
  {
    Debug("newproof::pm-flattening") << "flattenBinCongs::\treturn as is\n";
    return;
  }
  if (proof->d_id == theory::MERGED_THROUGH_TRANS)
  {
    for (i = 0; i < size; ++i)
    {
      Debug("newproof::pm-flattening") << push;
      Debug("newproof::pm-flattening")
          << "flattenBinCongs::\trecurse on child " << i << "\n";
      flattenBinCongs(proof->d_children[i].get());
      Debug("newproof::pm-flattening") << pop;
    }
    return;
  }
  if (proof->d_id == theory::MERGED_THROUGH_CONGRUENCE)
  {
    Assert(!proof->d_node.isNull());
    std::vector<std::shared_ptr<theory::EqProof>> premises;
    for (i = 0; i < size; ++i)
    {
      Debug("newproof::pm-flattening") << push;
      Debug("newproof::pm-flattening")
          << "flattenBinCongs::\trecurse on child " << i << "\n";
      flattenBinCongs2(proof->d_children[i].get(), premises);
      Debug("newproof::pm-flattening") << pop;
    }
    Debug("newproof::pm-flattening")
        << "flattenBinCongs::\trebuild proof from new premises\n";
    proof->d_children.clear();
    proof->d_children.insert(
        proof->d_children.end(), premises.begin(), premises.end());
    if (Debug.isOn("newproof::pm-flattening"))
    {
      proof->debug_print("newproof::pm-flattening");
      Debug("newproof::pm-flattening") << "===\n";
    }
    return;
  }
  // not sure what to do if thing is NUMBER_OF_MERGE_REASONS
  Assert(false);
}

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
    Assert(!proof->d_children[i]->d_node.isNull());
    child_proofs_conclusions.push_back(proof->d_children[i]->d_node);
  }
  d_proofSteps.back().addConclusion(child_proofs_conclusions);
  d_proofSteps.back().addConclusion(proof->d_node);
  // recursively process proofs that have premises
  unsigned child_id, next_id;
  for (i = 0; i < size; ++i)
  {
    // If premise is self justified, no step is required. As a rule of thumb
    // this only applies for inputs
    if (NewProofManager::isSelfJustified(proof->d_children[i]->d_id))
    {
      Assert(proof->d_children[i]->d_children.empty());
      child_proofs_leafs.push_back(child_proofs_conclusions[i]);
      continue;
    }
    child_id = processTheoryProof(proof->d_children[i].get());
    // add resolution step between current proof step and resulting proof step
    // from processing child proof
    next_id = getNextId();
    // TODO make sure the invariant that the id corresponds to the proof step
    // in the table is always respected
    child_proofs_leafs.insert(child_proofs_leafs.end(),
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
  std::vector<theory::EqProof*> premises;
  flattenBinCongs(proof);
  if (Debug.isOn("newproof::pm"))
  {
    Debug("newproof::pm") << "After flattenning:\n";
    proof->debug_print("newproof::pm", 1);
    Debug("newproof::pm") << "===\n";
  }
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
      out << ".c" << premises[i] << (i < size - 1 ? " " : "");
    }
    out << ")";
  }
  const std::vector<Node>& conclusion = s->getConclusion();
  Assert(!conclusion.empty());
  out << " :conclusion (";
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    if (i < size - 1)
    {
      out << "(not " << conclusion[i] << ") ";
    }
    else
    {
      out << conclusion[i];
    }
  }
  out << ")\n";
}

}  // namespace CVC4
