/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the proof manager for the PropPfManager.
 */

#include "prop/prop_proof_manager.h"

#include "expr/skolem_manager.h"
#include "options/main_options.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "prop/prop_proof_manager.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "smt/env.h"
#include "util/string.h"

namespace cvc5::internal {
namespace prop {

PropPfManager::PropPfManager(Env& env,
                             context::UserContext* userContext,
                             CDCLTSatSolver* satSolver,
                             ProofCnfStream* cnfProof)
    : EnvObj(env),
      d_propProofs(userContext),
      d_pfpp(new ProofPostprocess(env, cnfProof)),
      d_satSolver(satSolver),
      d_assertions(userContext),
      d_proofCnfStream(cnfProof)
{
  // add trivial assumption. This is so that we can check the that the prop
  // engine's proof is closed, as the SAT solver's refutation proof may use True
  // as an assumption even when True is not given as an assumption. An example
  // is when a propagated literal has an empty explanation (i.e., it is a valid
  // literal), which leads to adding True as its explanation, since for creating
  // a learned clause we need at least two literals.
  d_assertions.push_back(NodeManager::currentNM()->mkConst(true));
}

void PropPfManager::registerAssertion(Node assertion)
{
  d_assertions.push_back(assertion);
}

void PropPfManager::checkProof(const context::CDList<Node>& assumptions,
                               const context::CDList<Node>& assertions)
{
  Trace("sat-proof") << "PropPfManager::checkProof: Checking if resolution "
                        "proof of false is closed\n";
  std::shared_ptr<ProofNode> conflictProof = getProof(assumptions, false);
  Assert(conflictProof);
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  // add given assertions d_assertions
  for (const Node& assertion : assertions)
  {
    d_assertions.push_back(assertion);
  }
  std::vector<Node> avec{d_assertions.begin(), d_assertions.end()};
  pfnEnsureClosedWrt(options(),
                     conflictProof.get(),
                     avec,
                     "sat-proof",
                     "PropPfManager::checkProof");
}

std::vector<Node> PropPfManager::getUnsatCoreLemmas(
    const context::CDList<Node>& assumptions)
{
  std::vector<Node> usedLemmas;
  std::vector<Node> allLemmas = d_proofCnfStream->getLemmaClauses();
  std::shared_ptr<ProofNode> satPf = getProof(assumptions, false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  for (const Node& lemma : allLemmas)
  {
    if (std::find(satLeaves.begin(), satLeaves.end(), lemma) != satLeaves.end())
    {
      usedLemmas.push_back(lemma);
    }
  }
  return usedLemmas;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getProofLeaves(
    const context::CDList<Node>& assumptions, modes::ProofComponent pc)
{
  Trace("sat-proof") << "PropPfManager::getProofLeaves: Getting " << pc
                     << " component proofs\n";
  std::vector<Node> fassumps;
  Assert(pc == modes::ProofComponent::THEORY_LEMMAS
         || pc == modes::ProofComponent::PREPROCESS);
  std::vector<std::shared_ptr<ProofNode>> pfs =
      pc == modes::ProofComponent::THEORY_LEMMAS
          ? d_proofCnfStream->getLemmaClausesProofs()
          : d_proofCnfStream->getInputClausesProofs();
  std::shared_ptr<ProofNode> satPf = getProof(assumptions, false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  std::vector<std::shared_ptr<ProofNode>> usedPfs;
  for (const std::shared_ptr<ProofNode>& pf : pfs)
  {
    Node proven = pf->getResult();
    if (std::find(satLeaves.begin(), satLeaves.end(), proven) != satLeaves.end())
    {
      usedPfs.push_back(pf);
    }
  }
  return usedPfs;
}

std::shared_ptr<ProofNode> PropPfManager::getProof(
    const context::CDList<Node>& assumptions, bool connectCnf)
{
  auto it = d_propProofs.find(connectCnf);
  if (it != d_propProofs.end())
  {
    return it->second;
  }
  // retrieve the SAT solver's refutation proof
  Trace("sat-proof") << "PropPfManager::getProof: Getting proof of false\n";
  std::unordered_set<Node> cset(assumptions.begin(), assumptions.end());
  Trace("cnf-input") << "#assumptions=" << cset.size() << std::endl;

  bool hasFalseAssert = false;
  bool computeClauses = d_satSolver->needsMinimizeClausesForGetProof();
  if (computeClauses)
  {
    std::vector<Node> minAssumptions;
    std::vector<SatLiteral> unsatAssumptions;
    d_satSolver->getUnsatAssumptions(unsatAssumptions);
    for (const Node& nc : cset)
    {
      if (nc.isConst())
      {
        if (nc.getConst<bool>())
        {
          // never include true
          continue;
        }
        else
        {
          hasFalseAssert = true;
          Trace("cnf-input") << "...found false assumption" << std::endl;
          // if false exists, take it only
          minAssumptions.clear();
          minAssumptions.push_back(nc);
          break;
        }
      }
      else if (d_proofCnfStream->hasLiteral(nc))
      {
        SatLiteral il = d_proofCnfStream->getLiteral(nc);
        if (std::find(unsatAssumptions.begin(), unsatAssumptions.end(), il)
            == unsatAssumptions.end())
        {
          continue;
        }
      }
      minAssumptions.push_back(nc);
    }
    cset.clear();
    cset.insert(minAssumptions.begin(), minAssumptions.end());
    Trace("cnf-input") << "#assumptions (min)=" << cset.size() << std::endl;
  }
  std::vector<Node> inputs = d_proofCnfStream->getInputClauses();
  Trace("cnf-input") << "#input=" << inputs.size() << std::endl;
  std::vector<Node> lemmas = d_proofCnfStream->getLemmaClauses();
  Trace("cnf-input") << "#lemmas=" << lemmas.size() << std::endl;
  if (!hasFalseAssert)
  {
    cset.insert(inputs.begin(), inputs.end());
    cset.insert(lemmas.begin(), lemmas.end());
  }

  // the set of clauses to pass to SAT solver for getProof
  std::vector<Node> clauses;
  // output for dimacs file
  std::stringstream dumpDimacs;
  bool alreadyDumpDimacs = false;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* skm = nm->getSkolemManager();
  TypeNode bt = nm->booleanType();

  // go back and minimize assumptions if option is set and SAT solver uses it.
  // we don't do this if we found false as a (preprocessed) input formula
  if (computeClauses && !hasFalseAssert && options().proof.satProofMinDimacs)
  {
    Trace("cnf-input-min") << "Make cadical..." << std::endl;
    CDCLTSatSolver* csm = SatSolverFactory::createCadical(
        d_env, statisticsRegistry(), d_env.getResourceManager());
    NullRegistrar nreg;
    context::Context nctx;
    CnfStream csms(d_env, csm, &nreg, &nctx);
    Trace("cnf-input-min") << "Get literals..." << std::endl;
    std::vector<SatLiteral> csma;
    std::map<SatLiteral, Node> litToNode;
    std::map<SatLiteral, Node> litToNodeAbs;
    TypeNode ft = nm->mkFunctionType({bt}, bt);
    // Function used to ensure that subformulas are not treated by CNF below.
    Node litOf = skm->mkDummySkolem("litOf", ft);
    for (const Node& c : cset)
    {
      Node ca = c;
      std::vector<SatLiteral> satClause;
      std::vector<Node> lits;
      if (c.getKind() == Kind::OR)
      {
        lits.insert(lits.end(), c.begin(), c.end());
      }
      else
      {
        lits.push_back(c);
      }
      // For each literal l in the current clause, if it has Boolean
      // substructure, we replace it with (litOf l), which will be treated as a
      // literal. We do this since we require that the clause be treated
      // verbatim by the SAT solver, otherwise the unsat core will not include
      // the necessary clauses (e.g. it will skip those corresponding to CNF
      // conversion).
      std::vector<Node> cls;
      bool childChanged = false;
      for (const Node& cl : lits)
      {
        bool negated = cl.getKind() == Kind::NOT;
        Node cla = negated ? cl[0] : cl;
        if (d_env.theoryOf(cla) == theory::THEORY_BOOL && !cla.isVar())
        {
          Node k = nm->mkNode(Kind::APPLY_UF, {litOf, cla});
          cls.push_back(negated ? k.notNode() : k);
          childChanged = true;
        }
        else
        {
          cls.push_back(cl);
        }
      }
      if (childChanged)
      {
        ca = nm->mkOr(cls);
      }
      Trace("cnf-input-min-assert") << "Assert: " << ca << std::endl;
      csms.ensureLiteral(ca);
      SatLiteral lit = csms.getLiteral(ca);
      csma.emplace_back(lit);
      litToNode[lit] = c;
      litToNodeAbs[lit] = ca;
    }
    Trace("cnf-input-min") << "Solve under " << csma.size() << " assumptions..."
                           << std::endl;
    SatValue res = csm->solve(csma);
    if (res == SAT_VALUE_FALSE)
    {
      // we successfully reproved the input
      Trace("cnf-input-min") << "...got unsat" << std::endl;
      std::vector<SatLiteral> uassumptions;
      csm->getUnsatAssumptions(uassumptions);
      Trace("cnf-input-min")
          << "...#unsat assumptions=" << uassumptions.size() << std::endl;
      std::vector<Node> aclauses;
      for (const SatLiteral& lit : uassumptions)
      {
        Assert(litToNode.find(lit) != litToNode.end());
        Trace("cnf-input-min-result")
            << "assert: " << litToNode[lit] << std::endl;
        clauses.emplace_back(litToNode[lit]);
        aclauses.emplace_back(litToNodeAbs[lit]);
      }
      alreadyDumpDimacs = true;
      csms.dumpDimacs(dumpDimacs, aclauses);
    }
    else
    {
      // should never happen, if it does, we revert to the entire input
      Trace("cnf-input-min") << "...got sat" << std::endl;
      Assert(false) << "Failed to minimize DIMACS";
      clauses.insert(clauses.end(), cset.begin(), cset.end());
    }
    delete csm;
  }
  else
  {
    clauses.insert(clauses.end(), cset.begin(), cset.end());
  }

  std::shared_ptr<ProofNode> conflictProof;
  if (!options().proof.markLemmasDimacs && hasFalseAssert)
  {
    Assert(clauses.size() == 1 && clauses[0].isConst()
           && !clauses[0].getConst<bool>());
    conflictProof = d_env.getProofNodeManager()->mkAssume(clauses[0]);
  }
  else if (!options().proof.markLemmasDimacs)
  {
    conflictProof = d_satSolver->getProof(clauses);
  }
  else
  {
    std::vector<Node> args;
    std::stringstream dinputFile;
    dinputFile << options().driver.filename << ".drat_input.cnf";
    Node dfile = nm->mkConst(String(dinputFile.str()));
    args.push_back(dfile);

    // we will print a dimacs of inputs + lemmas, where lemmas are preceded by
    // @ti. The proof step will have as arguments the name of the dimacs file
    // and a set of equalities between the @ti's and the respective lemmas, as
    // nodes

    // TODO print the DIMACs
    //
    // will need to use void CnfStream::dumpDimacs, but a version that adds the
    // t marker in front
    std::fstream dout(dinputFile.str(), std::ios::out);
    d_proofCnfStream->dumpDimacs(dout, inputs, lemmas);
    dout.close();
    args.push_back(lemmas.size() > 1 ? nm->mkNode(Kind::AND, lemmas)
                                     : lemmas[0]);
    // build the proof node
    CDProof cdp(d_env);
    Node falseNode = nm->mkConst(false);
    cdp.addStep(falseNode, ProofRule::SAT_LEMMAS_EXTERNAL_PROVE, inputs, args);
    conflictProof = cdp.getProofFor(falseNode);
  }
  if (!options().proof.markLemmasDimacs)
  {  // if DRAT, must dump dimacs
    ProofRule r = conflictProof->getRule();
    if (r == ProofRule::DRAT_REFUTATION || r == ProofRule::SAT_EXTERNAL_PROVE)
    {
      std::stringstream dinputFile;
      dinputFile
          << conflictProof->getArguments()[0].getConst<String>().toString();
      std::fstream dout(dinputFile.str(), std::ios::out);
      if (alreadyDumpDimacs)
      {
        dout << dumpDimacs.str();
      }
      else
      {
        d_proofCnfStream->dumpDimacs(dout, clauses);
      }
      dout.close();
    }
  }
  Assert(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
    Trace("sat-proof")
        << "PropPfManager::getProof: Connecting with CNF proof\n";
  }
  if (!connectCnf)
  {
    // if the sat proof was previously connected to the cnf, then the
    // assumptions will have been updated and we'll not have the expected
    // behavior here (i.e., the sat proof with the clauses given to the SAT
    // solver as leaves). In this case we will build a new proof node in which
    // we will erase the connected proofs (via overwriting them with
    // assumptions). This will be done in a cloned proof node so we do not alter
    // what is stored in d_propProofs.
    if (d_propProofs.find(true) != d_propProofs.end())
    {
      CDProof cdp(d_env);
      // get the clauses added to the SAT solver and add them as assumptions
      std::vector<Node> allAssumptions{inputs.begin(), inputs.end()};
      allAssumptions.insert(allAssumptions.end(), lemmas.begin(), lemmas.end());
      for (const Node& a : allAssumptions)
      {
        cdp.addStep(a, ProofRule::ASSUME, {}, {a});
      }
      // add the sat proof copying the proof nodes but not overwriting the
      // assumption clauses
      cdp.addProof(conflictProof, CDPOverwrite::NEVER, true);
      conflictProof = cdp.getProof(NodeManager::currentNM()->mkConst(false));
    }
    d_propProofs[connectCnf] = conflictProof;
    return conflictProof;
  }
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: new free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: assertions are:\n";
    for (const Node& a : d_assertions)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
  }
  d_propProofs[connectCnf] = conflictProof;
  return conflictProof;
}

}  // namespace prop
}  // namespace cvc5::internal
