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

NewProofManager::~NewProofManager() {
}

NewProofManager* NewProofManager::currentPM() {
  return smt::currentNewProofManager();
}

NewProof& NewProofManager::getProof()
{
  return *(currentPM()->d_proof);
}

SkolemizationManager* NewProofManager::getSkolemizationManager() {
  Assert (options::proof() || options::unsatCores());
  return &(currentPM()->d_skolemizationManager);
}

void NewProofManager::addAssertion(Node formula)
{
  Debug("newproof::pm") << "NewProofManager::addAssertion: " << formula << std::endl;
  d_proof.get()->addProofStep(RULE_INPUT);
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToLastProofStep(formula);
  }
}

void NewProofManager::addAssertionWeird(Node formula) {}

void NewProofManager::addUnknown(Node formula) {}

void NewProofManager::addSatDef(ClauseId clause,
                                Node clauseNode,
                                Node clauseNodeDef)
{
  Debug("newproof::sat") << "NewProofManager::addSatDef: clause/assertion/def: "
                         << clause << " / " << clauseNode << " / "
                         << clauseNodeDef << "\n";
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
    Debug("newproof::sat") << "NewProofManager::addSatDef: clause " << clause
                           << " already had node  " << d_clauseToNode[clause]
                           << " and def  " << d_clauseToNodeDef[clause] << "\n";
    return;
  }
  d_clauseToNode[clause] = clauseNode;
  d_clauseToNodeDef[clause] = clauseNodeDef;
}

void NewProofManager::addTheoryProof(theory::EqProof *proof)
{
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addTheoryProof(proof);
  }
}

void NewProofManager::setLogic(const LogicInfo& logic) {
  d_logic = logic;
}

NewProofManager::NewProofManagerStatistics::NewProofManagerStatistics()
    : d_proofProductionTime("proof::NewProofManager::proofProductionTime")
{
  smtStatisticsRegistry()->registerStat(&d_proofProductionTime);
}

NewProofManager::NewProofManagerStatistics::~NewProofManagerStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_proofProductionTime);
}

} /* CVC4  namespace */
