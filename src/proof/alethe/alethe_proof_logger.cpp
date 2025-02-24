/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe proof logger utility.
 */

#include "proof/alethe/alethe_proof_logger.h"

#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "smt/proof_manager.h"
#include "util/string.h"

namespace cvc5::internal {
namespace proof {

AletheProofLogger::AletheProofLogger(Env& env,
                                     std::ostream& out,
                                     smt::PfManager* pm,
                                     smt::Assertions& as,
                                     smt::ProofPostprocess* ppp)
    : ProofLogger(env),
      d_out(out),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_ppp(ppp),
      d_anc(nodeManager(), options().proof.proofAletheDefineSkolems),
      d_appproc(env, d_anc),
      d_apprinter(env, d_anc)
{
  d_hadError = false;
  d_multPPClauses = false;
  Trace("alethe-pf-log-debug") << "Make Alethe proof logger" << std::endl;
  if (env.getLogicInfo().isHigherOrder())
  {
    Trace("alethe-pf-log-debug") << "..HOL; ignore everything" << std::endl;
    out << "(error \"Proof unsupported by Alethe: contains higher-order "
           "elements\")";
    d_hadError = true;
  }
}

AletheProofLogger::~AletheProofLogger() {}

bool AletheProofLogger::processPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                                            bool inner,
                                            bool finalStep,
                                            std::string& error)
{
  if (inner)
  {
    if (d_appproc.processInnerProof(pfn, finalStep))
    {
      return true;
    }
    error = d_appproc.getError();
    return false;
  }
  if (d_appproc.process(pfn))
  {
    return true;
  }
  error = d_appproc.getError();
  return false;
}

bool AletheProofLogger::printPfNodesAlethe(
    std::vector<std::shared_ptr<ProofNode>>& pfns,
    const std::vector<Node>& assumptions)
{
  options::ProofCheckMode oldMode = options().proof.proofCheck;
  d_pnm->getChecker()->setProofCheckMode(options::ProofCheckMode::NONE);
  bool success = d_appproc.processInnerProofs(pfns, assumptions);
  if (success)
  {
    for (const std::shared_ptr<ProofNode>& pfn : pfns)
    {
      d_apprinter.printProofNode(d_out, pfn);
    }
  }
  else
  {
    d_out << "(error " << d_appproc.getError() << ")";
  }
  d_pnm->getChecker()->setProofCheckMode(oldMode);
  return success;
}

bool AletheProofLogger::printPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                                          bool inner,
                                          bool finalStep)
{
  options::ProofCheckMode oldMode = options().proof.proofCheck;
  d_pnm->getChecker()->setProofCheckMode(options::ProofCheckMode::NONE);
  std::map<Node, std::string> assertionNames;
  std::string error;
  bool success = processPfNodeAlethe(pfn, inner, finalStep, error);
  if (inner)
  {
    if (success)
    {
      d_apprinter.printProofNode(d_out, pfn);
    }
    else
    {
      d_out << "(error " << error << ")";
    }
  }
  else
  {
    if (success)
    {
      d_apprinter.print(d_out, pfn, assertionNames);
    }
    else
    {
      d_out << "(error " << error << ")";
    }
  }
  d_pnm->getChecker()->setProofCheckMode(oldMode);
  return success;
}

void AletheProofLogger::logCnfPreprocessInputs(const std::vector<Node>& inputs)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof start"
                         << std::endl;
  CDProof cdp(d_env);
  Node conc = nodeManager()->mkAnd(inputs);
  cdp.addTrustedStep(conc, TrustId::PREPROCESSED_INPUT, inputs, {});
  std::shared_ptr<ProofNode> pfn = cdp.getProofFor(conc);
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
  printPfNodeAlethe(d_ppProof);
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof end"
                         << std::endl;
}

void AletheProofLogger::printPreprocessingProof(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
    d_multPPClauses = pfns.size() > 1;
    std::shared_ptr<ProofNode> pfn =
        pfns.size() == 1 ? pfns[0]
                         : d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
    ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
    d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
    Assert(d_ppProof->getRule() == ProofRule::SCOPE
           && d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
    std::shared_ptr<ProofNode> definitionsScope = d_ppProof;
    std::shared_ptr<ProofNode> assumptionsScope = d_ppProof->getChildren()[0];
    std::vector<Node> assumptions{definitionsScope->getArguments().begin(),
                                  definitionsScope->getArguments().end()};
    assumptions.insert(assumptions.end(),
                       assumptionsScope->getArguments().begin(),
                       assumptionsScope->getArguments().end());
    // Sanitize original assumptions
    std::vector<Node> sanitizedAssumptions;
    for (const Node& a : assumptions)
    {
      Node conv = d_anc.maybeConvert(a, true);
      if (conv.isNull())
      {
        d_hadError = true;
        d_out << "(error " << d_anc.getError() << ")";
        break;
      }
      // avoid repeated assumptions
      if (std::find(
              sanitizedAssumptions.begin(), sanitizedAssumptions.end(), conv)
          == sanitizedAssumptions.end())
      {
        sanitizedAssumptions.push_back(conv);
      }
    }
    if (!d_hadError)
    {
      std::map<Node, std::string> assertionNames;
      d_apprinter.printInitialAssumptions(
          d_out, sanitizedAssumptions, assertionNames, true);
      // not process and print each preprocessing proof. They should connect to
      // the assumptions
      Trace("alethe-pf-log")
          << "; log: reprocess again the inputs to save them for later printing"
          << std::endl;
      std::shared_ptr<ProofNode> ppBody =
          d_ppProof->getChildren()[0]->getChildren()[0];
      if (!printPfNodeAlethe(ppBody, true, false))
      {
        d_hadError = true;
      }

      // d_hadError = !printPfNodesAlethe(pfns, assumptions);
      // d_ppPfs.insert(d_ppPfs.end(), pfns.begin(), pfns.end());

      // for (const std::shared_ptr<ProofNode>& pf : pfns)
      // {
      //   context::CDHashMap<ProofNode*, std::string>::const_iterator pfIt =
      //       d_apprinter.getPfMap()->find(pf.get());
      //   if (pfIt != d_apprinter.getPfMap()->end())
      //   {
      //     Trace("alethe-pf-log") << "\thas in map step for preprocessing of "
      //                            << pf->getResult() << "\n";
      //   }
      // }
    }
}

void AletheProofLogger::logCnfPreprocessInputProofs(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof start"
                         << std::endl;
  // if the assertions are empty, we do nothing. We will answer sat.
  if (!pfns.empty() && !options().proof.proofLogLazyPreProcessing)
  {
    printPreprocessingProof(pfns);
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof end"
                         << std::endl;
}

void AletheProofLogger::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log theory lemma proof start "
                         << pfn->getResult() << std::endl;
  d_lemmaPfs.emplace_back(pfn);
  printPfNodeAlethe(pfn, true);
  Trace("alethe-pf-log") << "; log theory lemma proof end" << std::endl;
}

void AletheProofLogger::logTheoryLemma(const Node& n)
{
  if (d_hadError)
  {
    return;
  }
  if (d_lemmas.count(n))
  {
    Trace("alethe-pf-log") << "; log theory lemma no-op (repeated lemma) " << n
                           << std::endl;
    return;
  }
  d_lemmas.insert(n);
  Trace("alethe-pf-log") << "; log theory lemma start " << n << std::endl;
  // create Alethe step directly. No need to go via the post-processor.
  std::vector<Node> args{nodeManager()->mkConstInt(
      Rational(static_cast<uint32_t>(AletheRule::HOLE)))};
  args.push_back(n);
  Node conclusion = d_anc.maybeConvert(n);
  if (conclusion.isNull())
  {
    d_hadError = true;
    d_out << "(error " << d_anc.getError() << ")";
    return;
  }
  args.push_back(conclusion);
  args.push_back(nodeManager()->mkConst(String("THEORY_LEMMA")));
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkNode(ProofRule::ALETHE_RULE, {}, args, n);
  d_lemmaPfs.emplace_back(ptl);

  d_apprinter.printProofNode(d_out, ptl, true);
  // d_out << conclusion << "\n";
  Trace("alethe-pf-log") << "; log theory lemma end" << std::endl;
}

void AletheProofLogger::logSatRefutation()
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises{d_ppPfs.begin(),
                                                   d_ppPfs.end()};
  if (Configuration::isAssertionBuild())
  {
    // make sure that each of these premises is present in the preprocessing
    // proof and was therefore printed
    Assert(d_ppProof->getRule() == ProofRule::SCOPE);
    Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
    std::shared_ptr<ProofNode> ppBody =
        d_ppProof->getChildren()[0]->getChildren()[0];
    // we ignore the translated AND_INTRO step and rather directly get the
    // proofs for the clauses
    for (const std::shared_ptr<ProofNode>& ppPf : d_ppPfs)
    {
      Node n = ppPf->getResult();
      // Traverse the proof node to find a subproof concluding n.
      Assert(expr::getSubproofFor(n, ppBody))
          << "Could not find " << n << std::endl;
    }
  }
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  printPfNodeAlethe(psr, true, true);
  Trace("alethe-pf-log") << "; log SAT refutation end" << std::endl;
}

void AletheProofLogger::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log SAT refutation proof start" << std::endl;
  Assert(d_ppProof->getRule() == ProofRule::SCOPE);
  Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
  std::shared_ptr<ProofNode> ppBody =
      d_ppProof->getChildren()[0]->getChildren()[0];
  std::vector<std::shared_ptr<ProofNode>> premises;
  if (d_multPPClauses)
  {
    // get the premises of the and_intro rule
    Assert(getAletheRule(ppBody->getArguments()[0]) == AletheRule::AND_INTRO);
    const std::vector<std::shared_ptr<ProofNode>>& pfChildren =
        ppBody->getChildren();
    premises.insert(premises.end(), pfChildren.begin(), pfChildren.end());
  }
  else
  {
    premises.push_back(ppBody);
  }

  // std::vector<std::shared_ptr<ProofNode>> premises{ppBody};
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  printPfNodeAlethe(psr, true, true);
  Trace("alethe-pf-log") << "; log SAT refutation proof end" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
