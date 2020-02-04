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
  Debug("newproof:pm") << "assert: " << formula << std::endl;
  d_proof.get()->addProofStep(RULE_INPUT);
  if (d_format == VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToLastProofStep(formula);
  }
}

void NewProofManager::addAssertionWeird(Node formula) {}

void NewProofManager::addUnknown(Node formula) {}

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
