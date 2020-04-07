/*********************                                                        */
/*! \file lean_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof to be output in the Lean proof format.
 **/

#include "proof/lean_proof.h"

#include "proof/new_proof.h"
#include "proof/new_proof_manager.h"

namespace CVC4 {

LeanProofStep::LeanProofStep(unsigned id, NewProofRule rule)
{
  d_id = id;
  d_rule = rule;
}

void LeanProofStep::addRule(NewProofRule rule) { d_rule = rule; }

void LeanProofStep::addArgs(std::vector<Node>& args)
{
  d_args.insert(d_args.end(), args.begin(), args.end());
}

void LeanProofStep::addArg(Node arg)
{
  d_args.push_back(arg);
}

void LeanProofStep::addUnsignedArgs(std::vector<unsigned>& uargs)
{
  d_unsigned_args = uargs;
}

void LeanProofStep::addUnsignedArg(unsigned uarg)
{
  d_unsigned_args.push_back(uarg);
}

void LeanProofStep::addPremises(std::vector<unsigned>& reasons)
{
  d_premises.insert(d_premises.end(), reasons.begin(), reasons.end());
}

void LeanProofStep::addPremise(unsigned reason)
{
  d_premises.push_back(reason);
}

void LeanProofStep::addConclusion(Node conclusion)
{
  d_conclusion.push_back(conclusion);
}

void LeanProofStep::addConclusion(std::vector<Node>& conclusion)
{
  d_conclusion.insert(d_conclusion.end(), conclusion.begin(), conclusion.end());
}

const std::vector<Node>& LeanProofStep::getConclusion() const
{
  return d_conclusion;
}

Node LeanProofStep::getLastConclusion() const
{
  return d_conclusion.empty() ? Node::null()
                              : d_conclusion[d_conclusion.size() - 1];
}

const std::vector<Node>& LeanProofStep::getArgs() const { return d_args; }

const std::vector<unsigned>& LeanProofStep::getUnsignedArgs() const
{
  return d_unsigned_args;
}

const std::vector<unsigned>& LeanProofStep::getPremises() const
{
  return d_premises;
}

const std::vector<LeanProofStep>& LeanProof::getProofSteps() const
{
  return d_proofSteps;
};

ClauseId LeanProof::addProofStep()
{
  ClauseId id;
  id = getNextId();
  d_proofSteps.push_back(LeanProofStep(id));
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << "\n";
  d_proofSteps.push_back(LeanProofStep(id, rule));
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule,
                                 std::vector<Node>& conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " " << conclusion << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(leanproofstep);
  Assert(rule != RULE_INPUT);
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule, Node conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " " << conclusion << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(leanproofstep);
  if (rule == RULE_INPUT)
  {
    d_inputs.push_back(std::vector<Node>());
    d_inputs.back().push_back(conclusion);
  }
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule, Node conclusion, Node arg)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << ", conclusion " << conclusion << ", arg " << arg
      << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addConclusion(conclusion);
  leanproofstep.addArg(arg);
  d_proofSteps.push_back(leanproofstep);
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule,
                                  std::vector<unsigned>& reasons,
                                  Node conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " "  //<< reasons << " "
      << conclusion << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addPremises(reasons);
  leanproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(leanproofstep);
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule,
                                  std::vector<unsigned>& reasons,
                                  std::vector<Node>& conclusion)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " "  //<< reasons << " "
      << conclusion << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addPremises(reasons);
  leanproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(leanproofstep);
  return id;
}

ClauseId LeanProof::addProofStep(NewProofRule rule,
                                  std::vector<unsigned>& reasons,
                                 std::vector<Node>& conclusion,
                                 unsigned u_arg)
{
  ClauseId id;
  id = getNextId();
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << rule << " "  //<< reasons << " "
      << conclusion << "\n";
  LeanProofStep leanproofstep = LeanProofStep(id, rule);
  leanproofstep.addPremises(reasons);
  leanproofstep.addConclusion(conclusion);
  leanproofstep.addUnsignedArg(u_arg);
  d_proofSteps.push_back(leanproofstep);
  return id;
}

ClauseId LeanProof::addResSteps(std::vector<Resolution>& reasons,
                                Node conclusion)
{
  std::vector<Node> conclusion_vector{conclusion};
  return addResSteps(reasons, conclusion_vector);
}

ClauseId LeanProof::addResSteps(std::vector<Resolution>& reasons,
                                std::vector<Node>& conclusion)
{
  ClauseId id;
  id = getNextId();
  LeanProofStep leanproofstep = LeanProofStep(id, RULE_RESOLUTION);
  if (Debug.isOn("leanpf::res"))
  {
    Debug("leanpf::res") << "LeanProof::addResStep: building res chain with";
    for (unsigned i = 0, size = reasons.size(); i < size; ++i)
    {
      if (i > 0)
      {
        Debug("leanpf::res") << " [" << (!reasons[i].d_sign ? "~" : "")
                             << reasons[i].d_piv << "]";
      }
      Debug("leanpf::res") << " " << reasons[i].d_id;
    }
    Debug("leanpf::res") << "\n";
  }
  // build chain and add pivots
  leanproofstep.addPremise(reasons[0].d_id);
  for (unsigned i = 1, size = reasons.size(); i < size; ++i)
  {
    Assert(reasons[i].d_piv != Node::null());
    Node piv;
    // sign = 0 means "negative", otherwise "positive"
    //
    // the pivots are the literals of the clause in the left being resolved. The
    // sign indicate if they are negative or positive literals
    if (!reasons[i].d_sign)
    {
      piv = reasons[i].d_piv.negate();
    }
    else
    {
      piv = reasons[i].d_piv;
    }
    Debug("leanpf::res") << "LeanProof::addResStep: adding res step from "
                         << reasons[i - 1].d_id << "/" << reasons[i].d_id
                         << " and piv / sign: " << piv << " / "
                         << reasons[i].d_sign << "\n";
    leanproofstep.addPremise(reasons[i].d_id);
    leanproofstep.addArg(piv);
    leanproofstep.addUnsignedArg(reasons[i].d_sign);
  }
  leanproofstep.addConclusion(conclusion);
  d_proofSteps.push_back(leanproofstep);
  // yield id last resolution
  return id;
}

ClauseId LeanProof::addResStepsBin(std::vector<Resolution>& reasons,
                                Node conclusion)
{
  ClauseId id;
  if (Debug.isOn("leanpf::res"))
  {
    Debug("leanpf::res") << "LeanProof::addResStep: building res chain with";
    for (unsigned i = 0, size = reasons.size(); i < size; ++i)
    {
      Debug("leanpf::res") << " " << reasons[i].d_id;
    }
    Debug("leanpf::res") << "\n";
  }
  for (unsigned i = 1, size = reasons.size(); i < size; ++i)
  {
    Assert(reasons[i].d_piv != Node::null());
    id = getNextId();
    LeanProofStep leanproofstep = LeanProofStep(id, RULE_RESOLUTION);
    // if negative, invert order
    unsigned fst, snd;
    Node piv;
    if (!reasons[i].d_sign)
    {
      fst = i;
      snd = i - 1;
      piv = reasons[i].d_piv.negate();
    }
    else
    {
      fst = i - 1;
      snd = i;
      piv = reasons[i].d_piv;
    }
    Debug("leanpf::res") << "LeanProof::addResStep: adding res step from "
                          << reasons[fst].d_id << "/" << reasons[snd].d_id
                          << " and piv / sign: " << piv << " / "
                          << reasons[i].d_sign << "\n";
    leanproofstep.addPremise(reasons[fst].d_id);
    leanproofstep.addPremise(reasons[snd].d_id);
    leanproofstep.addArg(piv);
    // compute conclusion only if this is not the last res step
    if (i == size - 1)
    {
      leanproofstep.addConclusion(conclusion);
    }
    else
    {
      // remove pivot from first clause and its negation from the second
      std::vector<Node> transient;
      const std::vector<Node>& c1 = d_proofSteps[reasons[fst].d_id].getConclusion();

      const std::vector<Node>& c2 = d_proofSteps[reasons[snd].d_id].getConclusion();
      Debug("leanpf::res")
          << "LeanProof::addResStep: bulting conclusion from " << c1
          << "\nLeanProof::addResStep: bulting conclusion from " << c2 << "\n";
      for (unsigned j = 0, size_c1 = c1.size(); j < size_c1; ++j)
      {
        if (c1[j] == piv)
        {
          continue;
        }
        transient.push_back(c1[j]);
      }
      Node notPiv = piv.negate();
      for (unsigned j = 0, size_c2 = c2.size(); j < size_c2; ++j)
      {
        if (c2[j] == notPiv)
        {
          continue;
        }
        transient.push_back(c2[j]);
      }
      leanproofstep.addConclusion(transient);
      // update reason to be used in next resolution, with the clause built here
      reasons[i].d_id = id;
    }
    d_proofSteps.push_back(leanproofstep);
  }
  // yield id last resolution
  return id;
}

ClauseId LeanProof::addIteIntroProofStep(Node conclusion)
{
  ClauseId id;
  id = getNextId();
  LeanProofStep leanproofstep = LeanProofStep(id, RULE_ITE_INTRO);
  leanproofstep.addConclusion(conclusion);
  // get ite term being defined. Conclusion NECESSARILY of the form
  //   ITE c (= t @ite) (= e @ite)
  // modulo equality symmetry
  Assert(conclusion.getKind() == kind::ITE);
  Assert(conclusion[1].getKind() == kind::EQUAL);
  Node iteConst;
  if (d_IteConst.find(conclusion[1][0]) != d_IteConst.end())
  {
    iteConst = conclusion[1][0];
  }
  else
  {
    Assert(d_IteConst.find(conclusion[1][1]) != d_IteConst.end());
    iteConst = conclusion[1][1];
  }
  Debug("newproof::pm")
      << "LeanProof::addProofStep: adding proof step with id/rule: " << id
      << " / " << RULE_ITE_INTRO << ", conclusion " << conclusion << ", arg "
      << iteConst << "\n";
  leanproofstep.addArg(iteConst);
  d_proofSteps.push_back(leanproofstep);
  return id;
}

void LeanProof::addToLastProofStep(Node conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToLastProofStep "
                        << d_proofSteps.back().getId() << " ["
                        << d_proofSteps.back().getRule() << "] conclusion "
                        << conclusion << "\n";
  d_proofSteps.back().addConclusion(conclusion);
  if (d_proofSteps.back().getRule() == RULE_INPUT)
  {
    d_inputs.push_back(std::vector<Node>());
    d_inputs.back().push_back(conclusion);
  }
}

void LeanProof::addToLastProofStep(std::vector<unsigned>& reasons,
                                    Node conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToLastProofStep "
                        << d_proofSteps.back().getId() << " ["
                        << d_proofSteps.back().getRule()
                        << "] reasons, and conclusion " << conclusion << "\n";
  d_proofSteps.back().addPremises(reasons);
  d_proofSteps.back().addConclusion(conclusion);
}

void LeanProof::addToProofStep(ClauseId id, Node conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToProofStep " << id << " ["
                        << d_proofSteps[id].getRule() << "] conclusion "
                        << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addConclusion(conclusion);
  if (d_proofSteps[id].getRule() == RULE_INPUT)
  {
    d_inputs.push_back(std::vector<Node>());
    d_inputs.back().push_back(conclusion);
  }
}

void LeanProof::addToProofStep(ClauseId id, NewProofRule rule, Node conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToProofStep " << id << " [" << rule
                        << "] conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addConclusion(conclusion);
  if (rule == RULE_INPUT)
  {
    d_inputs.push_back(std::vector<Node>());
    d_inputs.back().push_back(conclusion);
  }
}

void LeanProof::addToProofStep(ClauseId id,
                                NewProofRule rule,
                                std::vector<Node>& conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToProofStep " << id << " [" << rule
                        << "] conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addConclusion(conclusion);
  if (rule == RULE_INPUT)
  {
    d_inputs.push_back(std::vector<Node>());
    d_inputs.back().insert(
        d_inputs.back().end(), conclusion.begin(), conclusion.end());
  }
}

void LeanProof::addToProofStep(ClauseId id,
                                NewProofRule rule,
                                std::vector<ClauseId>& reasons,
                                std::vector<Node>& conclusion)
{
  Debug("newproof::pm") << "LeanProof::addToProofStep " << id << " [" << rule
                        << "], reasons, conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addPremises(reasons);
  d_proofSteps[id].addConclusion(conclusion);
}

void LeanProof::addToProofStep(ClauseId id,
                               NewProofRule rule,
                               std::vector<ClauseId>& reasons,
                               std::vector<Node>& conclusion,
                               unsigned ith)
{
  Debug("newproof::pm") << "LeanProof::addToProofStep " << id << " [" << rule
                        << "], reasons, ith " << ith << ", conclusion "
                        << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addPremises(reasons);
  d_proofSteps[id].addConclusion(conclusion);
  d_proofSteps[id].addUnsignedArg(ith);
}

void LeanProof::addToCnfProofStep(ClauseId id,
                                  NewProofRule rule,
                                  std::vector<Node>& conclusion,
                                  unsigned ith)
{
  Debug("newproof::pm") << "LeanProof::addToCnfProofStep " << id << " [" << rule
                        << "] conclusion " << conclusion << "\n";
  Assert(id >= 0 && id < d_proofSteps.size());
  d_proofSteps[id].addRule(rule);
  d_proofSteps[id].addConclusion(conclusion);
  switch (rule)
  {
      // collect args: list of terms in the AND / OR and the position of the
      // conjunct / disjunct derived, which is the last node (or its negation)
      // in the conclusion
    case RULE_CNF_AND_POS:
    {
      Assert(conclusion.size() == 2);
      Assert(conclusion[0].getKind() == kind::NOT);
      Assert(conclusion[0][0].getKind() == kind::AND);
      Assert(ith >= 0 && ith < conclusion[0][0].getNumChildren());
      std::vector<Node> args;
      args.insert(args.end(), conclusion[0][0].begin(), conclusion[0][0].end());
      d_proofSteps[id].addArgs(args);
      d_proofSteps[id].addUnsignedArg(ith);
      break;
    }
    case RULE_CNF_OR_NEG:
    {
      Assert(conclusion.size() == 2);
      Assert(conclusion[0].getKind() == kind::OR);
      Assert(ith >= 0 && ith < conclusion[0].getNumChildren());
      std::vector<Node> args;
      args.insert(args.end(), conclusion[0].begin(), conclusion[0].end());
      d_proofSteps[id].addArgs(args);
      d_proofSteps[id].addUnsignedArg(ith);
      break;
    }
    case RULE_CNF_AND_NEG:
    {
      Assert(conclusion[0].getKind() == kind::AND);
      std::vector<Node> args;
      args.insert(args.end(), conclusion[0].begin(), conclusion[0].end());
      d_proofSteps[id].addArgs(args);
      break;
    }
    case RULE_CNF_OR_POS:
    case RULE_CNF_XOR_POS1:
    case RULE_CNF_XOR_POS2:
    case RULE_CNF_XOR_NEG1:
    case RULE_CNF_XOR_NEG2:
    case RULE_CNF_IMPLIES_POS:
    case RULE_CNF_IMPLIES_NEG1:
    case RULE_CNF_IMPLIES_NEG2:
    case RULE_CNF_EQUIV_POS1:
    case RULE_CNF_EQUIV_POS2:
    case RULE_CNF_EQUIV_NEG1:
    case RULE_CNF_EQUIV_NEG2:
    case RULE_CNF_ITE_POS1:
    case RULE_CNF_ITE_POS2:
    case RULE_CNF_ITE_POS3:
    case RULE_CNF_ITE_NEG1:
    case RULE_CNF_ITE_NEG2:
    case RULE_CNF_ITE_NEG3:
    default: {
    }
  }
}

ClauseId LeanProof::maybeAddIffToEqStep(ClauseId id)
{
  // check if repated literals in conclusion. Does so by building a conclusion
  // without repetitions (last copy is kept)
  const std::vector<Node>& conclusion = d_proofSteps[id].getConclusion();
  std::vector<Node> simp_iff_conclusion;
  bool changed = false;
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    Assert(i == size - 1 || conclusion[i].getKind() == kind::NOT);
    Node lit = i < size - 1 ? conclusion[i][0] : conclusion[i];
    Assert(lit.getKind() == kind::EQUAL);
    if (lit[0].getType().isBoolean())
    {
      changed = true;
      unsigned j = lit[0].getKind() == kind::CONST_BOOLEAN ? 1 : 0;
      // I wonder if I don't have to check if lit[1 - j] is not true or false...
      simp_iff_conclusion.push_back(i < size - 1 ? lit[j].negate() : lit[j]);
    }
    else
    {
      simp_iff_conclusion.push_back(conclusion[i]);
    }
  }
  // if no change, stop
  if (!changed)
  {
    return id;
  }
  // create simp_iff step
  ClauseId simp_iff_id = getNextId();
  Debug("leanpf::th")
      << "LeanProof::maybeAddIffToEqStep: adding simp_iff step from " << id
      << " to " << simp_iff_id << "\n";
  d_proofSteps.push_back(LeanProofStep(simp_iff_id, RULE_SIMP_IFF));
  d_proofSteps[simp_iff_id].addPremise(id);
  d_proofSteps[simp_iff_id].addConclusion(simp_iff_conclusion);
  return simp_iff_id;
}

ClauseId LeanProof::maybeAddFactoringStep(ClauseId id)
{
  // check if repated literals in conclusion. Does so by building a conclusion
  // without repetitions (last copy is kept)
  const std::vector<Node>& conclusion = d_proofSteps[id].getConclusion();
  std::vector<Node> fact_conclusion;
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    bool repeated = false;
    for (unsigned j = i + 1; j < size; ++j)
    {
      if (conclusion[i] == conclusion[j])
      {
        repeated = true;
        break;
      }
    }
    // didn't find a copy
    if (!repeated)
    {
      fact_conclusion.push_back(conclusion[i]);
    }
  }
  // if same size, no copies
  if (fact_conclusion.size() == conclusion.size())
  {
    return id;
  }
  // create factoring step
  ClauseId fact_id = getNextId();
  Debug("leanpf::th")
      << "LeanProof::maybeAddFatoringStep: adding factoing step from " << id
      << " to " << fact_id << "\n";
  d_proofSteps.push_back(LeanProofStep(fact_id, RULE_FACTORING));
  d_proofSteps[fact_id].addPremise(id);
  d_proofSteps[fact_id].addConclusion(fact_conclusion);
  return fact_id;
}

void LeanProof::maybeRebuildConclusion(theory::EqProof* proof)
{
  Assert(proof->d_node.getKind() == kind::EQUAL);
  unsigned n_premises = proof->d_children.size();
  // first test if there is any SELF JUSTIFIED input premise so that
  //  ti1 = ti2 and f ... ti2 ... = f ... ti1 ...
  std::set<unsigned> wrong_order;
  for (unsigned i = 0; i < n_premises; ++i)
  {
    Assert(proof->d_children[i]->d_node.getKind() == kind::EQUAL);
    if (NewProofManager::isSelfJustified(proof->d_children[i]->d_id)
        && proof->d_children[i]->d_node[0] != proof->d_node[0][i])
    {
      wrong_order.insert(i);
    }
  }
  if (wrong_order.empty())
  {
    return;
  }
  // otherwise create f ... ti1 ... = f ... ti2 ... for each i in wrong_order
  Debug("leanpf::th") << "LeanProof::maybeRebuild conclusion: reordering "
                      << wrong_order.size() << " arguments in " << proof->d_node
                      << "\n";
  unsigned size = proof->d_node[0].getNumChildren();
  Assert(size == proof->d_node[1].getNumChildren());
  std::vector<Node> args0, args1;
  Assert(proof->d_node[0].getKind() == kind::APPLY_UF);
  Assert(proof->d_node[1].getKind() == kind::APPLY_UF);
  args0.push_back(proof->d_node[0].getOperator());
  args1.push_back(proof->d_node[1].getOperator());
  for (unsigned i = 0; i < size; ++i)
  {
    // if index has to be ordered, add arguments in opposite order
    if (wrong_order.count(i))
    {
      args0.push_back(proof->d_node[1][i]);
      args1.push_back(proof->d_node[0][i]);
    }
    else
    {
      args0.push_back(proof->d_node[0][i]);
      args1.push_back(proof->d_node[1][i]);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  proof->d_node = nm->mkNode(kind::EQUAL,
                             nm->mkNode(kind::APPLY_UF, args0),
                             nm->mkNode(kind::APPLY_UF, args1));
  Debug("leanpf::th")
      << "LeanProof::maybeRebuild conclusion: created new conclusion "
      << proof->d_node << "\n";
}

ClauseId LeanProof::maybeAddSymmStep(ClauseId id, Node eq, Node t1)
{
  Debug("leanpf::th") << "LeanProof::maybeAddSymmStep: testing if equal: "
                      << eq[0] << ", " << t1 << "\n";
  if (eq[0] == t1)
  {
    return ClauseIdUndef;
  }
  Debug("leanpf::th")
      << "LeanProof::maybeAddSymmStep: adding symmetry step to fixmismatch ("
      << t1 << " should be first arg of " << eq << "\n";
  NodeManager* nm = NodeManager::currentNM();
  // create symmetry step
  ClauseId symm_id = getNextId();
  d_proofSteps.push_back(LeanProofStep(symm_id, RULE_SYMMETRY));
  Node symm_eq = nm->mkNode(kind::EQUAL, eq[1], eq[0]);
  std::vector<Node> clause({eq.negate(), symm_eq});
  d_proofSteps[symm_id].addConclusion(clause);
  // add resolution step between eq's justification and symmetry step
  ClauseId res_id = getNextId();
  d_proofSteps.push_back(LeanProofStep(res_id, RULE_RESOLUTION));
  d_proofSteps[res_id].addPremise(id);
  d_proofSteps[res_id].addPremise(symm_id);
  // pivot is the original equality with positive sign
  d_proofSteps[res_id].addArg(eq);
  d_proofSteps[res_id].addUnsignedArg(1);
  // conclusion is the symm_eq
  std::vector<Node> premises_of_id;
  premises_of_id.insert(premises_of_id.end(),
                        d_proofSteps[id].getConclusion().begin(),
                        d_proofSteps[id].getConclusion().end() - 1);
  d_proofSteps[res_id].addConclusion(premises_of_id);
  d_proofSteps[res_id].addConclusion(nm->mkNode(kind::EQUAL, eq[1], eq[0]));
  return res_id;
}

ClauseId LeanProof::processTheoryProof(theory::EqProof* proof)
{
  Debug("leanpf::th") << "LeanProof::processTheoryProof: processing:\n";
  proof->debug_print("leanpf::th", 1);
  // add proof step for valid clause
  unsigned current_id = getNextId();
  NewProofRule r = NewProofManager::convert(proof->d_id);
  d_proofSteps.push_back(LeanProofStep(current_id, r));
  unsigned i, size = proof->d_children.size();
  std::vector<Node> original_proof_conclusion, original_proof_leafs;
  // premises or conclusion may be in wrong order, check and swap if necessary
  if (r == RULE_TRANSITIVITY)
  {
    Assert(size == 2);
    Debug("leanpf::th")
        << "LeanProof::processTheoryProof: check transitive conclusion "
        << proof->d_node << "\n";
    // first check is for not being in a weird a = b ^ b = a -> a = a case
    // other checks are for first term of conclusion not coming from first literal
    if (proof->d_node[0] != proof->d_node[1]
        && proof->d_node[0] != proof->d_children[0]->d_node[0]
        && proof->d_node[0] != proof->d_children[0]->d_node[1])
    {
      // swap children
      std::vector<std::shared_ptr<theory::EqProof>> tmp;
      tmp.push_back(proof->d_children[1]);
      tmp.push_back(proof->d_children[0]);
      proof->d_children.clear();
      proof->d_children.insert(proof->d_children.end(), tmp.begin(), tmp.end());
      Debug("leanpf::th") << "LeanProof::processTheoryProof: reordering "
                             "transitivity step, obtaining: ";
      proof->debug_print("leanpf::th", 1);
    }
  }
  if (r == RULE_CONGRUENCE)
  {
    maybeRebuildConclusion(proof);
    // add extra information for printing: operator, arguments of first app (app
    // is given) and argumenst of second app)
    d_proofSteps[current_id].addArg(proof->d_node[0].getOperator());
    d_proofSteps[current_id].addArg(proof->d_node[0]);
    d_proofSteps[current_id].addArg(proof->d_node[1]);
  }
  // recursively process proofs that have premises
  std::vector<Resolution> resolutions;
  resolutions.push_back(Resolution(current_id));
  unsigned child_id;
  for (i = 0; i < size; ++i)
  {
    Debug("leanpf::th") << "LeanProof::processTheoryProof: recursively "
                            "processing child proofs with premises\n";
    Debug("leanpf::th") << "LeanProof::processTheoryProof: premise ["
                        << proof->d_children[i]->d_id
                        << "], conclusion: " << proof->d_children[i]->d_node
                        << "\n";
    // If premise is self justified, no step is required. As a rule of thumb
    // this only applies for inputs
    if (NewProofManager::isSelfJustified(proof->d_children[i]->d_id))
    {
      Assert(proof->d_children[i]->d_children.empty());
      Debug("leanpf::th")
          << "LeanProof::processTheoryProof: premise self justified\n";
      original_proof_leafs.push_back(proof->d_children[i]->d_node.negate());
      original_proof_conclusion.push_back(
          proof->d_children[i]->d_node.negate());
      continue;
    }
    child_id = processTheoryProof(proof->d_children[i].get());
    // leafs accumulate
    original_proof_leafs.insert(
        original_proof_leafs.begin(),
        d_proofSteps[child_id].getConclusion().begin(),
        d_proofSteps[child_id].getConclusion().end() - 1);
    Debug("leanpf::th")
        << "LeanProof::processTheoryProof: after processing; premise ["
        << proof->d_children[i]->d_id
        << "], conclusion: " << proof->d_children[i]->d_node << "\n";
    Node piv, maybeSymmConclusion;
    Debug("leanpf::th")
        << "LeanProof::processTheoryProof: check if need symm steps\n";
    // add symmetry ordering steps if necessary
    ClauseId maybeSymmId = ClauseIdUndef;
    if (r == RULE_CONGRUENCE)
    {
      // piv                            -> equality I'd add as premise
      // proof->d_node[0][i]            -> ith arg of first cong application
      maybeSymmId = maybeAddSymmStep(
          child_id, proof->d_children[i]->d_node, proof->d_node[0][i]);
    }
    else if (r == RULE_TRANSITIVITY)
    {
      // piv                            -> equality I'd add as premise
      // proof->d_node[i]               -> ith arg of transitivity conclusion
      maybeSymmId = maybeAddSymmStep(
          child_id, proof->d_children[i]->d_node, proof->d_node[i]);
    }
    // update resolution and conclusion of proof step
    if (maybeSymmId != ClauseIdUndef)
    {
      Assert(!d_proofSteps[maybeSymmId].getLastConclusion().isNull());
      piv = d_proofSteps[maybeSymmId].getLastConclusion();
      original_proof_conclusion.push_back(piv.negate());
      child_id = maybeSymmId;
    }
    else
    {
      piv = proof->d_children[i]->d_node;
      original_proof_conclusion.push_back(
          proof->d_children[i]->d_node.negate());
    }
    // add resolution step between current proof step and resulting proof step
    // from processing child proof. Pivot is always that conclusion (module
    // symmetry) negated and is always negative
    Resolution res(child_id, piv, 3);
    resolutions.push_back(res);
    Debug("leanpf::th") << "LeanProof::proccessTheoryPRoof: add res step: "
                        << child_id << " [" << piv << "]\n";
  }
  d_proofSteps[current_id].addConclusion(original_proof_conclusion);
  d_proofSteps[current_id].addConclusion(proof->d_node);
  // build resolution chain
  if (resolutions.size() > 1)
  {
    Debug("leanpf::th") << "LeanProof::processTheoryProof: build res proof\n";
    original_proof_leafs.push_back(proof->d_node);
    current_id = addResSteps(resolutions, original_proof_leafs);
  }
  Debug("leanpf::th") << "LeanProof::processTheoryProof: id of proof "
                      << current_id << "\n";
  return current_id;
}

ClauseId LeanProof::addTheoryProof(theory::EqProof* proof)
{
  Debug("leanpf::th") << "LeanProof::addTheoryProof:\n";
  if (Debug.isOn("leanpf::th"))
  {
    proof->debug_print("leanpf::th", 1);
  }
  // TODO traverse the proof bottom up (just as it has been constructed).
  // Anything that has more than one level must be turned into a resolution of
  // clauses. The (valid) clauses are always the conclusion and the conclusions
  // of the premises.
  std::vector<theory::EqProof*> premises;
  proof->flattenBinCongs();
  if (Debug.isOn("leanpf::th"))
  {
    Debug("leanpf::th") << "After flattenning:\n";
    proof->debug_print("leanpf::th", 1);
    Debug("leanpf::th") << "===\n";
  }
  ClauseId id = processTheoryProof(proof);
  // if conclusion has repeated literals, factor it
  return maybeAddIffToEqStep(maybeAddFactoringStep(id));
}

void LeanProof::bind(Node term)
{
  Debug("leanpf::bind") << "Binding " << term << "\n";
  auto it = d_letMap.find(term);
  if (it != d_letMap.end())
  {
    it->second.increment();
    Debug("leanpf::bind") << "\t found in let map with id " << it->second.id
                          << "\n";
    return;
  }
  // whether term is an ite const placeholder
  auto it_iteconst = d_IteConst.find(term);
  if (it_iteconst != d_IteConst.end())
  {
    Debug("leanpf::bind") << "\t is ite const\n";
    // if the ite it stands for will has not been previously bound, bind it
    auto it_letmap = d_letMap.find(it_iteconst->second);
    if (it_letmap == d_letMap.end())
    {
      bind(it_iteconst->second);
      it_letmap = d_letMap.find(it_iteconst->second);
    }
    // make the ite const placeholder be printed as the let term of the ite it
    // stands for
    it_letmap->second.increment();
    Debug("leanpf::bind") << "\t mapping to id " << it_letmap->second.id << "\n";
    d_letMap[term] = it_letmap->second;
    return;
  }

  for (const Node& child : term)
  {
    bind(child);
  }

  unsigned newId = ProofLetCount::newId();
  ProofLetCount letCount(newId);
  d_letMap[term] = letCount;
  // put constants first
  if (term.getNumChildren() == 0)
  {
    d_letOrder.insert(d_letOrder.begin(), NewLetOrderElement(term, newId));
  }
  else
  {
    d_letOrder.push_back(NewLetOrderElement(term, newId));
  }
}

void LeanProof::finishProof()
{
  // TODO clean steps, like pruning and merging

  // collect terms
  for (LeanProofStep s : getProofSteps())
  {
    collectTerms(&s);
  }
  // build let map from terms in steps
  for (const Node& term : d_terms)
  {
    bind(term);
  }
}

void LeanProof::notifyIte(Node src, Node dest)
{
  Assert(d_IteConst.find(src) == d_IteConst.end());
  d_IteConst[src] = dest;
}

void LeanProof::collectTerms(Node n)
{
  Debug("leanpf::collect") << "Collecting " << n << "\n";
  if (d_terms.count(n))
  {
    Debug("leanpf::collect") << "\talrealdy collected\n";
    return;
  }
  TypeNode tn = n.getType();
  // ignore interpreted constants
  // TODO HB will need to add cases for other theories
  if (n.getKind() == kind::CONST_BOOLEAN)
  {
    Debug("leanpf::collect") << "\tignoring Boolean constant\n";
    return;
  }
  // collect fresh uninterpreted sorts
  if (tn.isSort() && !d_sorts.count(tn))
  {
    Debug("leanpf::collect")
        << "\tcollecting uninterpreted sort " << tn << "\n";
    d_sorts.insert(tn);
    std::stringstream ss;
    ss << "letSort" << d_sortDefs.size();
    d_sortDefs[tn] = ss.str();
  }
  Debug("leanpf::collect") << "\tterm will be added\n";
  // if function application, collect the function
  if (n.getKind() == kind::APPLY_UF)
  {
    collectTerms(n.getOperator());
  }
  // collect children
  for (const Node& child : n)
  {
    collectTerms(child);
  }
  // add term
  d_terms.insert(n);
}

void LeanProof::collectTerms(LeanProofStep* s)
{
  const std::vector<Node>& conclusion = s->getConclusion();
  if (conclusion.empty())
  {
    return;
  }
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    if (conclusion[i].isNull())
    {
      continue;
    }
    collectTerms(conclusion[i]);
  }
}

void LeanProof::printStep(std::ostream& out,
                          std::ostream& main,
                          LeanProofStep* s) const
{
  std::stringstream judgment;
  // a final step is a resolution with a conclusion that is the empty clause
  bool isFinal = s->getRule() == RULE_RESOLUTION;
  // start printing step judgment
  const std::vector<Node>& conclusion = s->getConclusion();
  Assert(!conclusion.empty()) << "Invalid step, no conclusion\n";
  judgment << "th_holds ([";
  for (unsigned i = 0, size = conclusion.size(); i < size; ++i)
  {
    if (conclusion[i].isNull())
    {
      continue;
    }
    isFinal = false;
    printTerm(judgment, conclusion[i]);
    judgment << (i < size - 1 ? ", " : "");
  }
  judgment << "]),";
  if (s->getRule() != RULE_INPUT)
  {
    judgment << " from ";
    printRule(judgment, s);
    if (!isFinal)
    {
      judgment << ",";
    }
  }
  if (isFinal)
  {
    main << "show ";
  }
  else
  {
    if (s->getRule() == RULE_INPUT)
    {
      main << "assume s";
    }
    else
    {
      main << "have s";
    }
    main << s->getId() << " : ";
  }
  main << judgment.str() << "\n";
}

inline void LeanProof::printPremises(
    std::ostream& out, const std::vector<ClauseId>& premises) const
{
  for (unsigned i = 0, size = premises.size(); i < size; ++i)
  {
    out << "s" << premises[i] << (i < size - 1 ? " " : "");
  }
}

void LeanProof::printRule(std::ostream& out, LeanProofStep* s) const
{
  switch (s->getRule())
  {
    case RULE_RESOLUTION:
    {
      const std::vector<unsigned>& premises = s->getPremises();
      const std::vector<Node>& args = s->getArgs();
      const std::vector<unsigned>& uargs = s->getUnsignedArgs();
      unsigned arg_i = 0;
      std::stringstream prev, next;
      prev << "s" << premises[0];
      // uarg[i] = 0 -> r1 prev next
      // uarg[i] = 1 -> r0 prev next
      // uarg[i] = 2 -> r1 next prev
      // uarg[i] = 3 -> r0 next prev
      for (unsigned i = 1, size = premises.size(); i < size; ++i)
      {
        // if sign is negative (0), then pivot occurs negatively in first clause
        // and positively in the second. If sign is positive (1) it's the other
        // way around. The resolution rule to be used is chosed accordingly
        // next << "uargs [" << arg_i << "] " << uargs[arg_i] << " ";
        next << (uargs[arg_i] % 2 ? "R0 " : "R1 ");
        if (uargs[arg_i] < 2)
        {
          // next << "first ";
          next << prev.str() << " s" << premises[i] << " ";
        }
        else
        {
          // next << "second ";
          next << "s" << premises[i] << " " << prev.str() << " ";
        }
        printTerm(next, args[arg_i++]);
        if (i < size - 1)
        {
          prev.str("");
          prev << "(" << next.str() << ")";
          next.str("");
        }
      }
      out << next.str();
      break;
    }
    case RULE_FACTORING:
    {
      out << "factoring ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_REFLEXIVITY:
    {
      out << "smtrefl";
      Assert(!s->getLastConclusion().isNull());
      out << (s->getLastConclusion()[0].getType().isBoolean() ? "_p" : "");
      break;
    }
    case RULE_SYMMETRY:
    {
      out << "smtsymm";
      Assert(!s->getLastConclusion().isNull());
      out << (s->getLastConclusion()[0].getType().isBoolean() ? "_p" : "");
      break;
    }
    case RULE_TRANSITIVITY:
    {
      out << "smttrans";
      Assert(!s->getLastConclusion().isNull());
      out << (s->getLastConclusion()[0].getType().isBoolean() ? "_p" : "");
      break;
    }
    case RULE_CONGRUENCE:
    {
      out << "@smtcongn";
      Assert(!s->getLastConclusion().isNull());
      out << (s->getLastConclusion()[0].getType().isBoolean() ? "_p " : " ");
      const std::vector<Node>& args = s->getArgs();
      Assert(args.size() == 3);
      printTerm(out, args[0]);
      out << " ";
      printTermList(out, args[1]);
      out << " ";
      printTermList(out, args[2]);
      break;
    }
    case RULE_SIMP_IFF:
    {
      out << "simp_iff ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_PURE_EQ: out << "pure_eq"; break;
    case RULE_CONSTANTS: out << "constants"; break;
    case RULE_PREPROCESSING:
    case RULE_PREPROCESSING_REWRITE:
    case RULE_PREPROCESSING_THEORY:
    case RULE_PREPROCESSING_ITE_REMOVAL:
    {
      out << "trust ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_ITE_INTRO:
    {
      out << "@ite_intro ";
      const std::vector<Node>& args = s->getArgs();
      Assert(args.size() == 1);
      printTerm(out, args[0]);
      break;
    }
    case RULE_CNF_AND:
    {
      out << "cnf_and ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_NOT_OR:
    {
      out << "cnf_not_or ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_AND_POS:
    {
      out << "@cnf_and_pos ";
      printTermList(out, s->getArgs());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_OR_NEG:
    {
      out << "@cnf_or_neg ";
      printTermList(out, s->getArgs());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_AND_NEG:
    {
      out << "@cnf_and_neg_n ";
      printTermList(out, s->getArgs());
      break;
    }
    case RULE_CNF_OR:
    {
      out << "cnf_or ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_CNF_NOT_AND:
    {
      out << "cnf_not_and ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_CNF_OR_POS:
    {
      out << "cnf_or_pos_n ";
      break;
    }
    case RULE_CNF_XOR1:
    case RULE_CNF_XOR2:
    {
      out << "cnf_xor ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_NOT_XOR1:
    case RULE_CNF_NOT_XOR2:
    {
      out << "cnf_not_xor ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_XOR_POS1: out << "cnf_xor_pos_0"; break;
    case RULE_CNF_XOR_POS2: out << "cnf_xor_pos_1"; break;
    case RULE_CNF_XOR_NEG1: out << "cnf_xor_neg_0"; break;
    case RULE_CNF_XOR_NEG2: out << "cnf_xor_neg_1"; break;
    case RULE_CNF_IMPLIES:
    {
      out << "cnf_implies ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_CNF_NOT_IMPLIES1:
    case RULE_CNF_NOT_IMPLIES2:
    {
      out << "cnf_not_implies ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_IMPLIES_POS: out << "cnf_implies_pos"; break;
    case RULE_CNF_IMPLIES_NEG1: out << "cnf_implies_neg_0"; break;
    case RULE_CNF_IMPLIES_NEG2: out << "cnf_implies_neg_1"; break;
    case RULE_CNF_EQUIV1:
    case RULE_CNF_EQUIV2:
    {
      out << "cnf_iff ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_NOT_EQUIV1:
    case RULE_CNF_NOT_EQUIV2:
    {
      out << "cnf_not_iff ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_EQUIV_POS1: out << "cnf_iff_pos_0"; break;
    case RULE_CNF_EQUIV_POS2: out << "cnf_iff_pos_1"; break;
    case RULE_CNF_EQUIV_NEG1: out << "cnf_iff_neg_0"; break;
    case RULE_CNF_EQUIV_NEG2: out << "cnf_iff_neg_1"; break;
    case RULE_CNF_ITE1:
    case RULE_CNF_ITE2:
    {
      out << "cnf_ite ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_NOT_ITE1:
    case RULE_CNF_NOT_ITE2:
    {
      out << "cnf_not_ite ";
      printPremises(out, s->getPremises());
      Assert(!s->getUnsignedArgs().empty());
      out << " " << s->getUnsignedArgs()[0];
      break;
    }
    case RULE_CNF_ITE_POS1: out << "cnf_ite_pos_0"; break;
    case RULE_CNF_ITE_POS2: out << "cnf_ite_pos_1"; break;
    case RULE_CNF_ITE_POS3: out << "cnf_ite_pos_2"; break;
    case RULE_CNF_ITE_NEG1: out << "cnf_ite_neg_0"; break;
    case RULE_CNF_ITE_NEG2: out << "cnf_ite_neg_1"; break;
    case RULE_CNF_ITE_NEG3: out << "cnf_ite_neg_2"; break;

    case RULE_UNDEF: out << "undef"; break;

    default:
      out << "ProofRule Unknown! [" << static_cast<unsigned>(s->getRule())
          << "]";
  }
}

void LeanProof::printSortDecl(std::ostream& out, TypeNode sort) const
{
  Assert(d_sortDefs.find(sort) != d_sortDefs.end());
  std::unordered_map<TypeNode, std::string, TypeNodeHashFunction>::
      const_iterator it = d_sortDefs.find(sort);
  out << "@[simp] def " << it->second << " := ";
  Assert(!sort.isFunction());
  out << "atom \"" << sort << "\"\n";
}

void LeanProof::printSort(std::ostream& out, TypeNode sort) const
{
  // functional sort
  if (sort.isFunction())
  {
    out << "(mkArrowN [";
    // print each arg sort
    unsigned size = sort.getNumChildren();
    for (unsigned i = 0, n_arg_types = size - 1; i < n_arg_types; ++i)
    {
      printSort(out, sort[i]);
      out << ", ";
    }
    // print return sort
    printSort(out, sort[size - 1]);
    out << "])";
    return;
  }
  // boolean sort
  if (sort.isBoolean())
  {
    out << "boolsort";
    return;
  }
  // TODO HB will need to add cases for other theories

  // uninterpreted sort
  Assert(d_sortDefs.find(sort) != d_sortDefs.end());
  std::unordered_map<TypeNode, std::string, TypeNodeHashFunction>::
      const_iterator it = d_sortDefs.find(sort);
  out << it->second;
}

void LeanProof::printConstant(std::ostream& out, Node n, bool decl) const
{
  Debug("leanpf::print") << "Printing constant " << (decl ? "[decl] " : "")
                         << n << "\n";
  TypeNode tn = n.getType();
  if (n.getKind() == kind::CONST_BOOLEAN)
  {
    if (tn.isBoolean())
    {
      out << (n.getConst<bool>() ? "top" : "bot") << (decl? "\n" : "");
    }
    // TODO HB will need to add cases for other theories
    else
    {
      Assert(false)
          << "Should not be explicitly printing a non-interpreted constant\n";
    }
    return;
  }
  // if I got here then I'm declaring an uninterpreted constant
  out << "const \"" << n << "\" ";
  std::unordered_map<TypeNode, std::string, TypeNodeHashFunction>::
      const_iterator it = d_sortDefs.find(tn);
  // uninterpreted constant
  if (it != d_sortDefs.end())
  {
    out << it->second << "\n";
  }
  // proposotion
  else if (tn.isBoolean())
  {
    out << "boolsort\n";
  }
  // uninterpreted function
  else if (tn.isFunction())
  {
    printSort(out, tn);
    out << "\n";
  }
  else
  {
    // interpreted constant, nothing to declare
    // TODO HB This will change for BV constants
  }
}

inline void LeanProof::printTermList(std::ostream& out, Node n) const
{
  out << "[";
  for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    printTerm(out, n[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

inline void LeanProof::printTermList(std::ostream& out,
                                     const std::vector<Node>& n) const
{
  out << "[";
  for (unsigned i = 0, size = n.size(); i < size; ++i)
  {
    printTerm(out, n[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanProof::printTerm(std::ostream& out, Node n, bool decl) const
{
  Debug("leanpf::print") << "Printing term " << (decl ? "[decl] " : "") << n
                         << "\n";
  std::unordered_map<Node, ProofLetCount, NodeHashFunction>::const_iterator it =
      d_letMap.find(n);
  if (!decl && it != d_letMap.end())
  {
    // print let and return
    out << "let" << it->second.id;
    return;
  }
  Debug("leanpf::print") << "Term not on letmap\n";
  unsigned n_args = n.getNumChildren();
  // printing constant symbol
  if (n_args == 0)
  {
    printConstant(out, n, decl);
    return;
  }
  // printing applications / formulas
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  switch (k)
  {
    case kind::APPLY_UF:
    {
      out << "mkAppN ";
      Node op = n.getOperator();
      printTerm(out, op);
      out << " ";
      printTermList(out, n);
      break;
    }

    case kind::EQUAL:
    {
      out << (n[0].getType().isBoolean() ? "mkIff " : "mkEq ");
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }

    case kind::DISTINCT:
    {
      out << "mkDistinct ";
      printTermList(out, n);
      break;
    }

    case kind::OR:
    {
      out << "mkOrN ";
      printTermList(out, n);
      break;
    }
    case kind::AND:
    {
      out << "mkAndN ";
      printTermList(out, n);
      break;
    }
    case kind::IMPLIES:
    {
      out << "mkImplies ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::NOT:
    {
      out << "mkNot ";
      printTerm(out, n[0]);
      break;
    }
    case kind::ITE:
    {
      out << "mkIte ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      out << " ";
      printTerm(out, n[2]);
      break;
    }

    default: Unhandled() << " " << k;
  }
  if (decl)
  {
    out << "\n";
  }
}

void LeanProof::toStream(std::ostream& out) const
{
  // print preamble
  out << "import sigs.hb_smt\nopen smt\nopen smt.sort smt.term\n\n";
  // print sorts
  for (const TypeNode& sort : d_sorts)
  {
    printSortDecl(out, sort);
  }
  // print terms
  for (unsigned i = 0, size = d_letOrder.size(); i < size; ++i)
  {
    Node curr = d_letOrder[i].d_n;
    unsigned letId = d_letOrder[i].d_id;
    Assert(d_letMap.find(curr) != d_letMap.end());
    out << "@[simp] def let" << letId << " := ";
    printTerm(out, curr, true);
  }
  out << std::endl;
  // print subproofs and steps of main proof (cnf / resolution / conclusions of
  // subproofs)
  std::stringstream main;
  std::stringstream steps;
  for (LeanProofStep s : getProofSteps())
  {
    printStep(main, steps, &s);
  }
  // print main theorem preamble
  out << main.str() << "noncomputable theorem main :\n\t";
  for (unsigned i = 0, size_i = d_inputs.size(); i < size_i; ++i)
  {
    out << "th_holds ([";
    for (unsigned j = 0, size_j = d_inputs[i].size(); j < size_j; ++j)
    {
      printTerm(out, d_inputs[i][j]);
      out << (j < size_j - 1 ? ", " : "");
    }
    out << "]) -> ";
  }
  out << "th_holds([]) :=\n";
  out << steps.str();
}

}  // namespace CVC4
