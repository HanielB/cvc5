/*********************                                                        */
/*! \file proof_manager.h
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

#include "cvc4_private.h"

#ifndef CVC4__NEW_PROOF_MANAGER_H
#define CVC4__NEW_PROOF_MANAGER_H

#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "proof/clause_id.h"
#include "proof/proof.h"
#include "proof/proof_utils.h"
#include "proof/skolemization_manager.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "new_proof.h"
#include "util/statistics_registry.h"

namespace CVC4 {

// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace BVMinisat {
  class Solver;
}/* BVMinisat namespace */

namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class SmtEngine;

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
}/* CVC4::prop namespace */


typedef std::unordered_map<ClauseId, prop::SatClause*> IdToSatClause;
typedef std::unordered_map<Node, std::vector<Node>, NodeHashFunction> NodeToNodes;
typedef std::unordered_set<ClauseId> IdHashSet;

// TODO There should be a proof manager for each proof format. Many of the
// things that were part of the old proof manager are totally only LFSC
// dependent
class NewProofManager {
protected:
  LogicInfo d_logic;

public:
  NewProofManager(ProofFormat format = VERIT);
  ~NewProofManager();

  static NewProofManager* currentPM();

  // getting proof
  const std::vector<NewProof>& getProof() const;

  static SkolemizationManager *getSkolemizationManager();

  /** Add input **/
  void addAssertion(Node formula);

  int getNextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);

  const std::string getLogic() const { return d_logic.getLogicString(); }

  LogicInfo & getLogicInfo() { return d_logic; }

  TimerStat* getProofProductionTime() { return &d_stats.d_proofProductionTime; }

 private:
  SkolemizationManager d_skolemizationManager;

  int d_nextId;

  std::vector<NewProof> d_proof;

  ProofFormat d_format;

  struct NewProofManagerStatistics
  {
    NewProofManagerStatistics();
    ~NewProofManagerStatistics();

    /**
     * Time spent producing proofs (i.e. generating the proof from the logging
     * information)
     */
    TimerStat d_proofProductionTime;
  }; /* struct ProofManagerStatistics */

  NewProofManagerStatistics d_stats;

};/* class ProofManager */

}/* CVC4 namespace */

#endif /* CVC4__NEW_PROOF_MANAGER_H */
