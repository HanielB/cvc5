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

VeritProofStep::VeritProofStep(unsigned id) { d_id = id; }

VeritProofStep::VeritProofStep(unsigned id, NewProofRule rule)
{
  d_id = id;
  d_rule = rule;
}

void VeritProofStep::addRule(NewProofRule rule) { d_rule = rule; }

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
  for (VeritProofStep s : getProofSteps())
  {
    printStep(out, &s);
  }
}

ClauseId VeritProof::addProofStep()
{
  ClauseId id;
  id = getNextId();
  d_proofSteps.push_back(VeritProofStep(id));
  return id;
}

ClauseId VeritProof::addProofStep(NewProofRule rule)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "VeritProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << "\n";
  d_proofSteps.push_back(VeritProofStep(id, rule));
  return id;
}

ClauseId VeritProof::addProofStep(NewProofRule rule, Node conclusion)
{
  ClauseId id;
  Debug("newproof::pm")
      << "VeritProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " " << conclusion << "\n";
  VeritProofStep vtproofstep = VeritProofStep(id, rule);
  vtproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(vtproofstep);
  return id;
}

ClauseId VeritProof::addProofStep(NewProofRule rule,
                                  std::vector<unsigned>& reasons,
                                  Node conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "VeritProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " "  //<< reasons << " "
      << conclusion << "\n";
  VeritProofStep vtproofstep = VeritProofStep(id, rule);
  vtproofstep.addPremises(reasons);
  vtproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(vtproofstep);
  return id;
}

ClauseId VeritProof::addProofStep(NewProofRule rule,
                                  std::vector<unsigned>& reasons,
                                  std::vector<Node>& conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "VeritProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " "  //<< reasons << " "
      << conclusion << "\n";
  VeritProofStep vtproofstep = VeritProofStep(id, rule);
  vtproofstep.addPremises(reasons);
  vtproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(vtproofstep);
  return id;
}

void VeritProof::addToLastProofStep(Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToLastProofStep "
                        << d_proofSteps.back().getId()
                        << " ["
                        // << d_proofSteps.back().getRule() << "] conclusion "
                        << "] conclusion " << conclusion << "\n";
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::addToLastProofStep(std::vector<unsigned>& reasons,
                                    Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToLastProofStep "
                        << d_proofSteps.back().getId() << " ["
                        // << d_proofSteps.back().getRule()
                        << "] reasons, and conclusion " << conclusion << "\n";
  d_proofSteps.back().addPremises(reasons);
  d_proofSteps.back().addConclusion(conclusion);
}

void VeritProof::addToProofStep(ClauseId id, Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToProofStep " << id << " ["
                        // << d_proofSteps[id].getRule() << "] conclusion "
                        << "] conclusion "
                        << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addConclusion(conclusion);
}

void VeritProof::addToProofStep(ClauseId id, NewProofRule rule, Node conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToProofStep " << id << " [" << rule
                        << "] conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addConclusion(conclusion);
}

void VeritProof::addToProofStep(ClauseId id,
                                NewProofRule rule,
                                std::vector<Node>& conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToProofStep " << id << " [" << rule
                        << "] conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addConclusion(conclusion);
}

void VeritProof::addToProofStep(ClauseId id,
                                NewProofRule rule,
                                std::vector<ClauseId>& reasons,
                                std::vector<Node>& conclusion)
{
  Debug("newproof::pm") << "VeritProof::addToProofStep " << id << " [" << rule
                        << "], reasons, conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addPremises(reasons);
  d_proofSteps[id].addConclusion(conclusion);
}

// // recursive call for building the proof
// void flattenBinCongs(theory::EqProof* proof);

// void flattenBinCongs2(theory::EqProof* proof,
//                       std::vector<std::shared_ptr<theory::EqProof>>& premises)
// {
//   if (Debug.isOn("newproof::pm-flattening"))
//   {
//     Debug("newproof::pm-flattening")
//         << "flattenBinCongs2::\tFlattenning proof:\n";
//     proof->debug_print("newproof::pm-flattening");
//     Debug("newproof::pm-flattening") << "===\n";
//   }
//   unsigned i, size = proof->d_children.size();
//   if (proof->d_id == theory::MERGED_THROUGH_CONGRUENCE
//       && proof->d_node.isNull())
//   {
//     for (i = 0; i < size; ++i)
//     {
//       Debug("newproof::pm-flattening") << push;
//       flattenBinCongs2(proof->d_children[i].get(), premises);
//       Debug("newproof::pm-flattening") << pop;
//     }
//     return;
//   }
//   Debug("newproof::pm-flattening")
//       << "flattenBinCongs2::\tNot flat-amenable proof, recurse\n";
//   std::shared_ptr<theory::EqProof> pb = std::make_shared<theory::EqProof>();
//   pb->d_node = proof->d_node;
//   pb->d_id = proof->d_id;
//   pb->d_children = proof->d_children;

//   flattenBinCongs(pb.get());
//   premises.push_back(pb);
// }

// void flattenBinCongs(theory::EqProof* proof)
// {
//   if (Debug.isOn("newproof::pm-flattening"))
//   {
//     Debug("newproof::pm-flattening")
//         << "flattenBinCongs::\tFlattenning proof:\n";
//     proof->debug_print("newproof::pm-flattening");
//     Debug("newproof::pm-flattening") << "===\n";
//   }
//   unsigned i, size = proof->d_children.size();
//   if (proof->d_id == theory::MERGED_THROUGH_EQUALITY
//       || proof->d_id == theory::MERGED_THROUGH_REFLEXIVITY
//       || proof->d_id == theory::MERGED_THROUGH_CONSTANTS)
//   {
//     Debug("newproof::pm-flattening") << "flattenBinCongs::\treturn as is\n";
//     return;
//   }
//   if (proof->d_id == theory::MERGED_THROUGH_TRANS)
//   {
//     for (i = 0; i < size; ++i)
//     {
//       Debug("newproof::pm-flattening") << push;
//       Debug("newproof::pm-flattening")
//           << "flattenBinCongs::\trecurse on child " << i << "\n";
//       flattenBinCongs(proof->d_children[i].get());
//       Debug("newproof::pm-flattening") << pop;
//     }
//     return;
//   }
//   if (proof->d_id == theory::MERGED_THROUGH_CONGRUENCE)
//   {
//     Assert(!proof->d_node.isNull());
//     std::vector<std::shared_ptr<theory::EqProof>> premises;
//     for (i = 0; i < size; ++i)
//     {
//       Debug("newproof::pm-flattening") << push;
//       Debug("newproof::pm-flattening")
//           << "flattenBinCongs::\trecurse on child " << i << "\n";
//       flattenBinCongs2(proof->d_children[i].get(), premises);
//       Debug("newproof::pm-flattening") << pop;
//     }
//     Debug("newproof::pm-flattening")
//         << "flattenBinCongs::\trebuild proof from new premises\n";
//     proof->d_children.clear();
//     proof->d_children.insert(
//         proof->d_children.end(), premises.begin(), premises.end());
//     if (Debug.isOn("newproof::pm-flattening"))
//     {
//       proof->debug_print("newproof::pm-flattening");
//       Debug("newproof::pm-flattening") << "===\n";
//     }
//     return;
//   }
//   // not sure what to do if thing is NUMBER_OF_MERGE_REASONS
//   Assert(false);
// }

ClauseId VeritProof::processTheoryProof(theory::EqProof* proof)
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
    child_proofs_conclusions.push_back(proof->d_children[i]->d_node.negate());
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

ClauseId VeritProof::addTheoryProof(theory::EqProof* proof)
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
  proof->flattenBinCongs();
  if (Debug.isOn("newproof::pm"))
  {
    Debug("newproof::pm") << "After flattenning:\n";
    proof->debug_print("newproof::pm", 1);
    Debug("newproof::pm") << "===\n";
  }
  return processTheoryProof(proof);
}

void VeritProof::printStep(std::ostream& out, VeritProofStep* s) const
{
  out << "(set .c" << s->getId() << " (";
  printRule(out, s->getRule());
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
  if (conclusion.empty())
  {
    out << " :no_conclusion))\n";
    return;
  }
  out << " :conclusion (";
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    if (conclusion[i].isNull())
    {
      continue;
    }
    out << conclusion[i] << (i < size - 1 ? " " : "");
  }
  out << ")))\n";
}

void VeritProof::printRule(std::ostream& out, NewProofRule r) const
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
    case RULE_PREPROCESSING: out << "preprocessing"; break;
    case RULE_PREPROCESSING_REWRITE: out << "preprocessing_rewrite"; break;
    case RULE_PREPROCESSING_THEORY: out << "preprocessing_theory"; break;
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

    default: out << "ProofRule Unknown! [" << static_cast<unsigned>(r) << "]";
  }
}

}  // namespace CVC4
