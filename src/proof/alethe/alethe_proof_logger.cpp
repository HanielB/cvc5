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

bool AletheProofLogger::printPfNodeAlethe(std::shared_ptr<ProofNode> pfn,
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
  std::shared_ptr<ProofNode> pfn;
  if (!pfns.empty())
  {
    pfn = pfns.size() == 1 ? pfns[0] : d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
    ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
    d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
    d_hadError = !printPfNodeAlethe(d_ppProof);
    if (!d_hadError)
    {
      // save the translated proofs of the given preprocessing clauses
      for (std::shared_ptr<ProofNode>& pf : pfns)
      {
        std::string error;
        bool success = processPfNodeAlethe(pf, true, false, error);
        Assert(success);
        d_ppPfs.push_back(pf);
      }
    }
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
  Trace("alethe-pf-log") << "; log theory lemma start " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  d_lemmaPfs.emplace_back(ptl);
  d_hadError = !printPfNodeAlethe(ptl, true);
  Trace("alethe-pf-log") << "; log theory lemma end" << std::endl;
}

void AletheProofLogger::logSatRefutation()
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises{d_ppPfs.begin(), d_ppPfs.end()};
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
      Assert(expr::getSubproofFor(n, ppBody)) << "Could not find " << n << std::endl;
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
  Trace("alethe-pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises{d_ppPfs.begin(), d_ppPfs.end()};
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  printPfNodeAlethe(psr, true, true);
  Trace("alethe-pf-log") << "; log SAT refutation end" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
