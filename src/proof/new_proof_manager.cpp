/*********************                                                        */
/*! \file new_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A new manager for Proofs
 **/

#include "proof/new_proof_manager.h"

#include "base/check.h"
#include "context/context.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/theory_proof.h"
#include "proof/verit_proof.h"
#include "prop/minisat/core/Solver.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "smt_util/node_visitor.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"

namespace CVC4 {

NewProofManager::NewProofManager(ProofFormat format) : d_format(format)
{
  // TODO change
  if (format == LFSC)
  {
    d_proof.reset(new VeritProof());
    return;
  }
  // default
  d_proof.reset(new VeritProof());
}

NewProofManager::~NewProofManager() {}

NewProofManager* NewProofManager::currentPM()
{
  return smt::currentNewProofManager();
}

NewProof& NewProofManager::getProof() { return *(currentPM()->d_proof); }

SkolemizationManager* NewProofManager::getSkolemizationManager()
{
  Assert(options::proof() || options::unsatCores());
  return &(currentPM()->d_skolemizationManager);
}

void NewProofManager::addAssertion(Node formula)
{
  Debug("newproof::pm") << "NewProofManager::addAssertion: " << formula
                        << std::endl;
  ClauseId id = d_proof.get()->addProofStep(RULE_INPUT);
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToLastProofStep(formula);
  }
  d_assertionToClauseId[formula] = id;
}

inline void NewProofManager::printLit(const Minisat::Solver::TLit lit)
{
  Debug("newproof::sat") << (Minisat::sign(lit) ? "-" : "")
                         << Minisat::var(lit) + 1 << " ";
}

inline void NewProofManager::printClause(const Minisat::Solver::TClause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    Debug("newproof::sat") << (Minisat::sign(clause[i]) ? "-" : "")
                           << Minisat::var(clause[i]) + 1 << " ";
    if (Debug.isOn("newproof::sat::cnf"))
    {
      prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
      Assert(d_satLitToNode.find(satLit) != d_satLitToNode.end());
      Debug("newproof::sat::cnf") << "[" << d_satLitToNode[satLit] << "] ";
    }
  }
}

void NewProofManager::addLitDef(prop::SatLiteral lit, Node litNode)
{
  Debug("newproof::sat") << "NewProofManager::addLitDef: lit/def: " << lit
                         << " / " << litNode << "\n";
  d_satLitToNode[lit] = litNode;
}

void NewProofManager::addClauseDef(ClauseId clause,
                                   Node clauseNode,
                                   Node clauseNodeDef)
{
  Debug("newproof::sat")
      << "NewProofManager::addClauseDef: clause/assertion/def: " << clause
      << " / " << clauseNode << " / " << clauseNodeDef << "\n";
  // I guess they have to be synched
  Assert(d_clauseToNode.find(clause) == d_clauseToNode.end()
         || d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end());

  // We can add the same clause from different assertions.  In this
  // case we keep the first assertion. For example asserting a /\ b
  // and then b /\ c where b is an atom, would assert b twice (note
  // that since b is top level, it is not cached by the CnfStream)
  //
  // For definitions the first is kept
  //
  // HB Need to grok the above
  if (d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end())
  {
    Debug("newproof::sat") << "NewProofManager::addClauseDef: clause " << clause
                           << " already had node  " << d_clauseToNode[clause]
                           << " and def  " << d_clauseToNodeDef[clause] << "\n";
    return;
  }
  d_clauseToNode[clause] = clauseNode;
  d_clauseToNodeDef[clause] = clauseNodeDef;
}

void NewProofManager::addClauseDef(ClauseId clause, Node clauseNodeDef)
{
  Debug("newproof::sat") << "NewProofManager::addClauseDef: clause/def: "
                         << clause << " / " << clauseNodeDef << "\n";
  // For definitions the first is kept
  if (d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end())
  {
    Debug("newproof::sat") << "NewProofManager::addClauseDef: clause " << clause
                           << " already had def " << d_clauseToNodeDef[clause]
                           << "\n";
    return;
  }
  d_clauseToNodeDef[clause] = clauseNodeDef;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TLit lit,
                                         NewProofRule reason,
                                         Node litNodeDef)
{
  ClauseId id;
  int intLit = toInt(lit);
  auto it = d_litToClauseId.find(intLit);
  if (it != d_litToClauseId.end())
  {
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << it->second << ", TLit: ";
      printLit(lit);
      Debug("newproof::sat") << " already registered\n";
    }
    return it->second;
  }
  Assert(d_clauseIdToLit.find(intLit) == d_clauseIdToLit.end());
  if (!litNodeDef.isNull())
  {
    addLitDef(toSatLiteral<Minisat::Solver>(lit), litNodeDef);
  }
  else
  {
    // if I'm not giving a definition I must have saved this at some previous
    // point
    prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
    Assert(d_satLitToNode.find(satLit) != d_satLitToNode.end());
    litNodeDef = d_satLitToNode[satLit];
    Debug("newproof::sat::cnf")
        << "NewProofManager::registerClause: TLit def " << litNodeDef << "\n";
  }
  // create connection step between original assertion and result of
  // preprocessing
  if (reason == RULE_INPUT)
  {
    Assert(d_assertionToClauseId.find(litNodeDef)
           != d_assertionToClauseId.end());
    Assert(d_format == VERIT);
    std::vector<ClauseId> reasons{d_assertionToClauseId[litNodeDef]};
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep(RULE_PREPROCESSING, reasons, litNodeDef);
  }
  else if (reason == RULE_THEORY_LEMMA)
  {
    Assert(d_format == VERIT);
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    // since this is a theory lemma I may already have a proof for it, in which
    // case it will now be built
    auto itt = d_satLitToTheoryProof.find(toSatLiteral<Minisat::Solver>(lit));
    if (itt != d_satLitToTheoryProof.end())
    {
      id = vtproof->addTheoryProof(itt->second);
    }
    else
    {
      id = vtproof->addProofStep(UNDEF, litNodeDef);
    }
  }
  else
  {
    // placeholder
    id = nextId();
  }
  d_litToClauseId[intLit] = id;
  d_clauseIdToLit[id] = intLit;

  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TLit: ";
    printLit(lit);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TClause& clause,
                                         NewProofRule reason,
                                         Node clauseNodeDef)
{
  ClauseId id;
  if (clause.proofId() != 0)
  {
    id = clause.proofId();
    Assert(d_clauseIdToClause.find(id) != d_clauseIdToClause.end());
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << id << ", TClause: ";
      printClause(clause);
      Debug("newproof::sat") << " already registered\n";
    }
    return id;
  }
  if (clauseNodeDef.isNull())
  {
    // if I'm not giving a definition then all literals must have been previous
    // defined. Use that to build a definition
    std::vector<Node> children;
    for (unsigned i = 0, size = clause.size(); i < size; ++i)
    {
      prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
      Assert(d_satLitToNode.find(satLit) != d_satLitToNode.end());
      children.push_back(d_satLitToNode[satLit]);
    }
    clauseNodeDef = NodeManager::currentNM()->mkNode(kind::OR, children);
  }
  if (reason == RULE_THEORY_LEMMA)
  {
    Assert(d_format == VERIT);
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    // the propagated literal is always at the first position in the clause
    // TODO HB How to assert this?
    prop::SatLiteral lit = toSatLiteral<Minisat::Solver>(clause[0]);
    // since this is a theory lemma I may already have a proof for it, in which
    // case it will now be built
    auto itt = d_satLitToTheoryProof.find(lit);
    if (itt != d_satLitToTheoryProof.end())
    {
      id = vtproof->addTheoryProof(itt->second);
    }
    else
    {
      // build clause if need be
      id = vtproof->addProofStep(UNDEF, clauseNodeDef);
    }
  }
  else
  {
    // placeholder
    id = nextId();
    Assert(false) << "NewProofManager::registerClause can't handle non-unit "
                     "clause - RULE_LEMMA yet\n";
  }
  clause.setProofId(id);
  d_clauseIdToClause[id] = &clause;
  // now define it
  addClauseDef(id, clauseNodeDef);
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TClause: ";
    printClause(clause);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

void NewProofManager::startResChain(Minisat::Solver::TClause& start)
{
  Assert(start.proofId() != 0);
  ClauseId id = start.proofId();
  Debug("newproof::sat") << "NewProofManager::startResChain " << id << "\n";
  // TODO what should I add here? Who is "start"???
}

void NewProofManager::addResolutionStep(Minisat::Solver::TLit lit,
                                        Minisat::Solver::TClause& clause,
                                        bool sign)
{
  ClauseId id = registerClause(clause);
  Debug("newproof::sat") << "NewProofManager::addResolutionStep: (" << id
                         << ", " << toInt(lit) << ", " << sign << ")\n";
  d_resolution.push_back(Resolution(registerClause(clause), lit, sign));
}

void NewProofManager::endResChain(Minisat::Solver::TLit lit)
{
  Assert(d_litToClauseId.find(toInt(lit)) != d_litToClauseId.end());
  endResChain(d_litToClauseId[toInt(lit)]);
}

// id is the conclusion
void NewProofManager::endResChain(ClauseId id)
{
  Debug("newproof::sat") << "NewProofManager::endResChain " << id << "\n";
  Assert(d_resolution.size() > 0);
  Debug("newproof::sat") << "========\n"
                         << "set .c" << id << "(resolution :clauses (";
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    Debug("newproof::sat") << ".c" << d_resolution[i].d_id;
    if (i < size - 1)
    {
      Debug("newproof::sat") << " ";
    }
  }
  Debug("newproof::sat") << "========\n";

  // saving for later printing
  d_resolutions.push_back(std::vector<Resolution>());
  d_resolutions.back().insert(
      d_resolutions.back().end(), d_resolution.begin(), d_resolution.end());
  // clearing
  d_resolution.clear();
}

void NewProofManager::finalizeProof()
{
  // TODO dunno why
  // Assert(conflict_clause != Minisat::Solver::TCRef_Undef);

  // this is used in the case that storeUnitConflict is not immediately suceeded
  // by finalizeProof
  // Assert(conflict_clause != Minisat::Solver::TCRef_Lazy);

  // last added clause is the conflicting one

  Assert(d_format == VERIT);
  VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
  ClauseId conflict_id = vtproof->getId() - 1;
  d_resolution.push_back(Resolution(conflict_id));
  // retrive clause
  std::vector<Minisat::Solver::TLit> conflict_clause;
  auto it = d_clauseIdToClause.find(conflict_id);
  if (it != d_clauseIdToClause.end())
  {
    for (unsigned i = 0, size = it->second->size(); i < size; ++i)
    {
      conflict_clause.push_back((*it->second)[i]);
    }
  }
  else
  {
    Assert(d_clauseIdToLit.find(conflict_id) != d_clauseIdToLit.end());
    conflict_clause.push_back(Minisat::toLit(d_clauseIdToLit[conflict_id]));
  }
  Debug("newproof::sat") << "NewProofManager::finalizeProof: conflict_id: "
                         << conflict_id << "\n";
  for (unsigned i = 0, size = conflict_clause.size(); i < size; ++i)
  {
    // since this clause is conflicting, I must be able to resolve away each of
    // its literal. The negation of each literal must then have been previously
    // derived
    Minisat::Solver::TLit lit = ~conflict_clause[i];
    // get justification for ~lit
    if (d_litToClauseId.find(toInt(lit)) != d_litToClauseId.end())
    {
      ClauseId id = d_litToClauseId[toInt(lit)];
      for (unsigned j = 0, size = d_resolutions.size(); j < size; ++j)
      {
        // this is the conclusion I think???
        if (id == d_resolutions[j].back().d_id)
        {
          Debug("newproof::sat")
              << "NewProofManager::finalizeProof:\t lit "
              << (Minisat::sign(lit) ? "-" : "") << Minisat::var(lit) + 1
              << " justified by " << id << "\n";
          break;
        }
      }
      // ClauseId res_id = resolveUnit(~lit);
      d_resolution.push_back(Resolution(id, lit, !Minisat::sign(lit)));
    }
    else
    {
      Debug("newproof::sat") << "NewProofManager::finalizeProof:\t lit ";
      printLit(lit);
      Debug("newproof::sat") << " is unknown\n";
      Assert(false);
    }
  }

  std::vector<ClauseId> reasons;
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    reasons.push_back(d_resolution[i].d_id);
  }
  vtproof->addProofStep(RULE_RESOLUTION, reasons, Node::null());

  d_resolution.clear();
}

void NewProofManager::queueTheoryProof(prop::SatLiteral lit,
                                       theory::EqProof* proof)
{
  Assert(d_satLitToTheoryProof.find(lit) == d_satLitToTheoryProof.end());
  d_satLitToTheoryProof[lit] = proof;
}

void NewProofManager::setLogic(const LogicInfo& logic) { d_logic = logic; }

NewProofManager::NewProofManagerStatistics::NewProofManagerStatistics()
    : d_proofProductionTime("proof::NewProofManager::proofProductionTime")
{
  smtStatisticsRegistry()->registerStat(&d_proofProductionTime);
}

NewProofManager::NewProofManagerStatistics::~NewProofManagerStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_proofProductionTime);
}

}  // namespace CVC4
