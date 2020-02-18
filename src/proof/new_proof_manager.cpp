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

#include "prop/minisat/core/Solver.h"

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
  d_proof.get()->addProofStep(RULE_INPUT);
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToLastProofStep(formula);
  }
}

void NewProofManager::addAssertionWeird(Node formula) {}

void NewProofManager::addUnknown(Node formula) {}

void NewProofManager::printClause(Minisat::Solver::TClause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    Debug("newproof::sat") << (Minisat::sign(clause[i]) ? "-" : "")
                           << Minisat::var(clause[i]) + 1 << " ";
    if (Debug.isOn("newproof::sat::cnf"))
    {
      // prop::SatLiteral satLit = prop::SatLiteral(
      //     prop::SatVariable(Minisat::var(clause[i]), Minisat::sign(clause[i])));
      prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);

      Assert(d_satLitToNode.find(satLit) != d_satLitToNode.end());
      Debug("newproof::sat::cnf") << "[" << d_satLitToNode[satLit] << "] ";
    }
  }
}

void NewProofManager::addLitDef(prop::SatLiteral lit, Node litNode)
{
  Debug("newproof::sat") << "NewProofManager::addLittDef: lit/def: " << lit
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
                                         Node litNodeDef)
{
  ClauseId id;
  int intLit = toInt(lit);
  auto it = d_litToClauseId.find(intLit);
  if (it != d_litToClauseId.end())
  {
    id = it->second;
    Debug("newproof::sat") << "NewProofManager::registerClause: TLit: "
                           << intLit << " already registered to id: " << id
                           << "\n";
  }
  else
  {
    Assert(d_clauseIdToLit.find(intLit) == d_clauseIdToLit.end());
    id = nextId();
    d_litToClauseId[intLit] = id;
    d_clauseIdToLit[id] = intLit;
    Debug("newproof::sat") << "NewProofManager::registerClause: TLit: "
                           << intLit << " id: " << id << "\n";
  }
  if (!litNodeDef.isNull())
  {
    addClauseDef(id, litNodeDef);
  }
  return id;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TClause& clause,
                                         Node clauseNodeDef)
{
  // Assert(clause != Minisat::Solver::TClause_Undef);
  ClauseId id;
  auto it = d_clauseToClauseId.find(clause);
  if (it != d_clauseToClauseId.end())
  {
    id = it->second;
    Debug("newproof::sat") << "NewProofManager::registerClause: Clause: ";
    printClause(clause);
    Debug("newproof::sat") << "already registered to id: " << id << "\n";
  }
  else
  {
    id = nextId();
    d_clauseToClauseId[clause] = id;
    // d_clauseIdToClause[id] = clause;
    Debug("newproof::sat") << "NewProofManager::registerClause: Clause: ";
    printClause(clause);
    Debug("newproof::sat") << "id: " << id << "\n";
  }
  if (!clauseNodeDef.isNull())
  {
    addClauseDef(id, clauseNodeDef);
  }
  return id;
}

ClauseId NewProofManager::getClauseIdForClause(Minisat::Solver::TClause& clause)
{
  Assert(d_clauseToClauseId.find(clause) != d_clauseToClauseId.end());
  return d_clauseToClauseId[clause];
}

// void NewProofManager::updateCRef(Minisat::Solver::TCRef oldref,
//                                  Minisat::Solver::TCRef newref)
// {
//   ClauseId id = getClauseIdForClause(oldref);
//   d_clauseIdToClause[id] = newref;
//   d_clauseToClauseId[newref] = id;
//   // delete old reference from map
//   d_clauseToClauseId.erase(oldref);
// }

void NewProofManager::startResChain(Minisat::Solver::TClause& start)
{
  ClauseId id = getClauseIdForClause(start);
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
  d_resolution.push_back(
      ResStep<Minisat::Solver>(lit, registerClause(clause), sign));
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
    Debug("newproof::sat") << ".c" << d_resolution[i].id;
    if (i < size - 1)
    {
      Debug("newproof::sat") << " ";
    }
  }
  Debug("newproof::sat") << "========\n";

  // saving for later printing
  d_resolutions.push_back(std::vector<ResStep<Minisat::Solver>>());
  d_resolutions.back().insert(
      d_resolutions.back().end(), d_resolution.begin(), d_resolution.end());
  // clearing
  d_resolution.clear();
}

void NewProofManager::finalizeProof(Minisat::Solver::TClause& conflict_clause)
{
  // TODO dunno why
  // Assert(conflict_clause != Minisat::Solver::TCRef_Undef);

  // this is used in the case that storeUnitConflict is not immediately suceeded
  // by finalizeProof
  // Assert(conflict_clause != Minisat::Solver::TCRef_Lazy);

  ClauseId conflict_id = registerClause(conflict_clause);
  Debug("newproof::sat") << "NewProofManager::finalizeProof: conflict_id: "
                         << conflict_id << "\n";
  for (int i = 0; i < conflict_clause.size(); ++i)
  {
    Minisat::Solver::TLit lit = conflict_clause[i];
    // get justification for ~lit
    if (d_litToClauseId.find(toInt(lit)) != d_litToClauseId.end())
    {
      ClauseId id = d_litToClauseId[toInt(lit)];
      for (unsigned j = 0, size = d_resolutions.size(); j < size; ++j)
      {
        // this is the conclusion I think???
        if (id == d_resolutions[j].back().id)
        {
          Debug("newproof::sat")
              << "NewProofManager::finalizeProof:\t lit "
              << (Minisat::sign(lit) ? "-" : "") << Minisat::var(lit) + 1
              << " justified by " << id << "\n";
          break;
        }
      }
      // ClauseId res_id = resolveUnit(~lit);
      d_resolution.push_back(
          ResStep<Minisat::Solver>(lit, id, !Minisat::sign(lit)));
    }
    else
    {
      Debug("newproof::sat")
          << "NewProofManager::finalizeProof:\t lit "
          << (Minisat::sign(lit) ? "-" : "") << Minisat::var(lit) + 1
          << " must be input or lemma\n";
    }
  }

  Debug("newproof::sat") << "========\n"
                         << "(set .c" << nextId() << " (resolution :clauses (";
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    Debug("newproof::sat") << ".c" << d_resolution[i].id;
    if (i < size - 1)
    {
      Debug("newproof::sat") << " ";
    }
  }
  Debug("newproof::sat") << ") :conclusion ())\n";
  Debug("newproof::sat") << "========\n";
  d_resolution.clear();
}

void NewProofManager::addTheoryProof(theory::EqProof* proof)
{
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addTheoryProof(proof);
  }
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
