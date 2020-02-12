/*********************                                                        */
/*! \file new_proof_manager.h
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
#include "theory/theory.h"
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
  static NewProof& getProof();

  static SkolemizationManager *getSkolemizationManager();

  static NewProofRule convert(theory::MergeReasonType reason)
  {
    NewProofRule newreason;
    switch (reason)
    {
      case theory::MERGED_THROUGH_CONGRUENCE:
        newreason = RULE_CONGRUENCE;
        break;
      case theory::MERGED_THROUGH_EQUALITY: newreason = RULE_PURE_EQ; break;
      case theory::MERGED_THROUGH_REFLEXIVITY:
        newreason = RULE_REFLEXIVITY;
        break;
      case theory::MERGED_THROUGH_CONSTANTS: newreason = RULE_CONSTANTS; break;
      default:  // MERGED_THROUGH_TRANS:
        newreason = RULE_TRANSITIVITY;
        break;
    }
    return newreason;
  }

  /** Proof requires no proof step. As a rule of thumb this applies only for
   * inputs.
   */
  static bool isSelfJustified(theory::MergeReasonType reason)
  {
    return reason == theory::MERGED_THROUGH_EQUALITY;
  }

  /* ------------ BEGIN Registering proof steps ------------ */

  /** Add input **/
  void addAssertion(Node formula);
  /** Add input (but in a weird way) **/
  void addAssertionWeird(Node formula);
  /** Add a result of an unknown preprocessing step **/
  void addUnknown(Node formula);

  void addTheoryProof(theory::EqProof* proof);

  /* ------------ END Registering proof steps ------------ */

  void setLogic(const LogicInfo& logic);

  const std::string getLogic() const { return d_logic.getLogicString(); }

  LogicInfo & getLogicInfo() { return d_logic; }

  TimerStat* getProofProductionTime() { return &d_stats.d_proofProductionTime; }

 private:
  SkolemizationManager d_skolemizationManager;

  std::unique_ptr<NewProof> d_proof;

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
