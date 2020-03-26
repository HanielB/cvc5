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

LeanProofStep::LeanProofStep(unsigned id) { d_id = id; }

LeanProofStep::LeanProofStep(unsigned id, NewProofRule rule)
{
  d_id = id;
  d_rule = rule;
}

void LeanProofStep::addRule(NewProofRule rule) { d_rule = rule; }

void LeanProofStep::addArgs(std::vector<Node>& args)
{
  d_args = args;
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
  d_premises = reasons;
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

ClauseId LeanProof::addProofStep(NewProofRule rule, Node conclusion)
{
  ClauseId id;
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

ClauseId LeanProof::addResSteps(std::vector<Resolution>& reasons,
                                Node conclusion)
{
  ClauseId id;
  if (Debug.isOn("newproof::pm"))
  {
    Debug("newproof::pm") << "LeanProof::addResStep: building res chain with";
    for (unsigned i = 0, size = reasons.size(); i < size; ++i)
    {
      Debug("newproof::pm") << " " << reasons[i].d_id;
    }
    Debug("newproof::pm") << "\n";
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
    Debug("newproof::pm") << "LeanProof::addResStep: adding res step from "
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

ClauseId LeanProof::maybeAddSymmStep(ClauseId id, Node eq, Node t1)
{
  if (eq[0] == t1)
  {
    return ClauseIdUndef;
  }
  NodeManager* nm = NodeManager::currentNM();
  // create symmetry step
  ClauseId symm_id = getNextId();
  d_proofSteps.push_back(LeanProofStep(symm_id, RULE_SYMMETRY));
  Node symm_eq = nm->mkNode(kind::EQUAL, eq[0], eq[1]);
  std::vector<Node> clause({eq.negate(), symm_eq});
  d_proofSteps[symm_id].addConclusion(clause);
  // add resolution step between eq's justification and symmetry step
  ClauseId res_id = getNextId();
  d_proofSteps.push_back(LeanProofStep(res_id, RULE_RESOLUTION));
  d_proofSteps[res_id].addPremise(id);
  d_proofSteps[res_id].addPremise(symm_id);
  // pivot is the original equality
  d_proofSteps[res_id].addArg(eq);
  // conclusion is the symm_eq
  d_proofSteps[res_id].addConclusion(eq);
  return res_id;
}


ClauseId LeanProof::processTheoryProof(theory::EqProof* proof)
{
  // add proof step for valid clause
  unsigned current_id = getNextId();
  NewProofRule r = NewProofManager::convert(proof->d_id);
  d_proofSteps.push_back(LeanProofStep(current_id, r));
  unsigned i, size = proof->d_children.size();
  std::vector<Node> child_proofs_conclusions, child_proofs_leafs;
  // premises may be in wrong order, check and swap if necessary
  if (r == RULE_TRANSITIVITY)
  {
    Assert(size == 2);
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
    }
  }
  for (i = 0; i < size; ++i)
  {
    Assert(!proof->d_children[i]->d_node.isNull());
    child_proofs_conclusions.push_back(proof->d_children[i]->d_node.negate());
  }
  d_proofSteps[current_id].addConclusion(child_proofs_conclusions);
  d_proofSteps[current_id].addConclusion(proof->d_node);
  // add extra information for printing: operator, arguments of first app (app
  // is given) and argumenst of second app)
  if (r == RULE_CONGRUENCE)
  {
    d_proofSteps[current_id].addArg(proof->d_node[0].getOperator());
    d_proofSteps[current_id].addArg(proof->d_node[0]);
    d_proofSteps[current_id].addArg(proof->d_node[1]);
  }
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
    // add symmetry ordering steps if necessary
    if (r == RULE_CONGRUENCE)
    {
      // child_proofs_conclusions[i][0] -> equality I'd add as premise
      // proof->d_node[0][i]            -> ith arg of first cong application
      ClauseId symm_subproof = maybeAddSymmStep(
          child_id, child_proofs_conclusions[i][0], proof->d_node[0][i]);
      child_id = symm_subproof != ClauseIdUndef ? symm_subproof : child_id;
    }
    else if (r == RULE_TRANSITIVITY)
    {

    }
    // add resolution step between current proof step and resulting proof step
    // from processing child proof
    next_id = getNextId();
    // TODO make sure the invariant that the id corresponds to the proof step
    // in the table is always respected
    child_proofs_leafs.insert(child_proofs_leafs.end(),
                              d_proofSteps[child_id].getConclusion().begin(),
                              d_proofSteps[child_id].getConclusion().end() - 1);
    d_proofSteps.push_back(LeanProofStep(next_id, RULE_RESOLUTION));
    d_proofSteps[next_id].addPremise(child_id);
    d_proofSteps[next_id].addPremise(current_id);
    // pivot is the negation of the literal being justified
    d_proofSteps[next_id].addArg(child_proofs_conclusions[i][0]);
    // current leafs - child_conclusion i + child_conclusions i+1.. +
    // proof->d_node
    d_proofSteps[next_id].addConclusion(child_proofs_leafs);
    for (unsigned j = i + 1; j < size; ++j)
    {
      d_proofSteps[next_id].addConclusion(child_proofs_conclusions[j]);
    }
    d_proofSteps[next_id].addConclusion(proof->d_node);
    // make last added clause the current clause
    current_id = next_id;
  }
  return current_id;
}

ClauseId LeanProof::addTheoryProof(theory::EqProof* proof)
{
  Debug("newproof::pm") << "LeanProof::addTheoryProof:\n";
  if (Debug.isOn("newproof::pm"))
  {
    proof->debug_print("newproof::pm", 1);
  }
  // TODO traverse the proof bottom up (just as it has been constructed).
  // Anything that has more than one level must be turned into a resolution of
  // clauses. The (valid) clauses are always the conclusion and the conclusions
  // of the premises.
  std::vector<theory::EqProof*> premises;
  proof->flattenBinCongs();
  if (Debug.isOn("newproof::pm"))
  {
    Debug("newproof::pm") << "After flattenning:\n";
    proof->debug_print("newproof::pm", 1);
    Debug("newproof::pm") << "===\n";
  }
  return processTheoryProof(proof);
}

void LeanProof::bind(Node term)
{
  auto it = d_letMap.find(term);
  if (it != d_letMap.end())
  {
    // TODO HB check this
    it->second.increment();
    return;
  }

  for (const Node& child : term)
  {
    bind(child);
  }

  // Special case: chain operators. If we have and(a,b,c), it will be printed
  // as and(a,and(b,c)).
  // The subterm and(b,c) may repeat elsewhere, so we need to bind it, too.
  //
  // TODO this has to be extended to APPLY_UF as well

  // Kind k = term.getKind();
  // if ((k == kind::OR || k == kind::AND) && term.getNumChildren() > 2)
  // {
  //   Node curr = term[term.getNumChildren() - 1];
  //   for (int i = term.getNumChildren() - 2; i >= 0; --i)
  //   {
  //     // TODO I absolutely hate building these terms. Don't wanna do this.
  //     And
  //     // this is not feasible for APPLY_UF, since I'd have to actually use
  //     // HO_APPLY. So just change this.
  //     NodeBuilder<> builder(k);
  //     builder << term[i];
  //     builder << curr;
  //     curr = builder;
  //     bind(curr);
  //   }
  // }
  // else
  {
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

void LeanProof::collectTerms(Node n)
{
  if (d_terms.count(n))
  {
    return;
  }
  TypeNode tn = n.getType();
  // ignore interpreted constants
  // TODO HB will need to add cases for other theories
  if (tn.isBoolean() && n.getNumChildren() == 0)
  {
    return;
  }
  // collect uninterpreted sorts
  if (tn.isSort())
  {
    d_sorts.insert(tn);
    std::stringstream ss;
    ss << "letSort" << d_sortDefs.size();
    d_sortDefs[tn] = ss.str();
  }
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
      out << "fo_R ";
      printPremises(out, s->getPremises());
      out << " ";
      const std::vector<Node>& args = s->getArgs();
      Assert(args.size() == 1);
      printTerm(out, args[0]);
      break;
    }
    case RULE_REFLEXIVITY: out << "smtrefl"; break;
    case RULE_SYMMETRY: out << "smtsymm"; break;
    case RULE_TRANSITIVITY: out << "smttrans"; break;
    case RULE_CONGRUENCE:
    {
      out << "@smtcongn ";
      const std::vector<Node>& args = s->getArgs();
      Assert(args.size() == 3);
      printTerm(out, args[0]);
      out << " ";
      printTermList(out, args[1]);
      out << " ";
      printTermList(out, args[2]);
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
    case RULE_CNF_AND: out << "cnf_and"; break;
    case RULE_CNF_NOT_OR: out << "cnf_not_or"; break;
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
    case RULE_CNF_OR: out << "cnf_or"; break;
    case RULE_CNF_NOT_AND: out << "cnf_not_and"; break;
    case RULE_CNF_OR_POS: out << "cnf_or_pos"; break;
    case RULE_CNF_XOR1: out << "cnf_xor1"; break;
    case RULE_CNF_XOR2: out << "cnf_xor2"; break;
    case RULE_CNF_NOT_XOR1: out << "cnf_not_xor1"; break;
    case RULE_CNF_NOT_XOR2: out << "cnf_not_xor2"; break;
    case RULE_CNF_XOR_POS1: out << "cnf_xor_pos1"; break;
    case RULE_CNF_XOR_POS2: out << "cnf_xor_pos2"; break;
    case RULE_CNF_XOR_NEG1: out << "cnf_xor_neg1"; break;
    case RULE_CNF_XOR_NEG2: out << "cnf_xor_neg2"; break;
    case RULE_CNF_IMPLIES:
    {
      out << "cnf_implies ";
      printPremises(out, s->getPremises());
      break;
    }
    case RULE_CNF_NOT_IMPLIES1: out << "cnf_not_implies_0"; break;
    case RULE_CNF_NOT_IMPLIES2: out << "cnf_not_implies_1"; break;
    case RULE_CNF_IMPLIES_POS: out << "cnf_implies_pos"; break;
    case RULE_CNF_IMPLIES_NEG1: out << "cnf_implies_neg_0"; break;
    case RULE_CNF_IMPLIES_NEG2: out << "cnf_implies_neg_1"; break;
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
  TypeNode tn = n.getType();
  if (!decl)
  {
    if (tn.isBoolean())
    {
      out << (n.getConst<bool>() ? "mytop" : "mybot");
    }
    // TODO HB will need to add cases for other theories
    else
    {
      Assert(false)
          << "Should not be explicitly printing a non-interpreted constant\n";
    }
    return;
  }
  out << "const \"" << n << "\" ";
  std::unordered_map<TypeNode, std::string, TypeNodeHashFunction>::
      const_iterator it = d_sortDefs.find(tn);
  if (it != d_sortDefs.end())
  {
    out << it->second << "\n";
  }
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
  std::unordered_map<Node, ProofLetCount, NodeHashFunction>::const_iterator it =
      d_letMap.find(n);
  if (!decl && it != d_letMap.end())
  {
    // print let and return
    out << "let" << it->second.id;
    return;
  }
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
      out << (tn.isBoolean() ? "mkPappN " : "mkAppN ");
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
      Unhandled() << k;
      break;
    }

    default: Unhandled() << k;
  }
  if (decl)
  {
    out << "\n";
  }
}

void LeanProof::toStream(std::ostream& out) const
{
  // print preamble
  out << "import sigs.mysmt\nopen mysmt\nopen mysmt.sort mysmt.myterm "
         "mysmt.myformula\n\n";
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
    auto it = d_letMap.find(curr);
    Assert(it != d_letMap.end());
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
