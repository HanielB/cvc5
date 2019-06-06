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

const ClauseId ClauseIdEmpty(-1);
const ClauseId ClauseIdUndef(-2);
const ClauseId ClauseIdError(-3);

template <class Solver> class TSatProof;
typedef TSatProof<CVC4::Minisat::Solver> CoreSatProof;

class CnfProof;
class TheoryProofEngine;
class TheoryProof;
class UFProof;

template <class Solver> class LFSCSatProof;
typedef TSatProof<CVC4::Minisat::Solver> CoreSatProof;

class LFSCCnfProof;
class LFSCTheoryProofEngine;
class LFSCUFProof;
class LFSCRewriterProof;

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
}/* CVC4::prop namespace */

// different proof modes
enum ProofFormat {
  LFSC,
  VERIT,
  LEAN
};/* enum ProofFormat */

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

  static ProofManager* currentPM();

  // getting various proofs
  static const Proof& getProof();

  static SkolemizationManager *getSkolemizationManager();

  /** Add input **/
  void addAssertion(Expr formula);

  int getNextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);

  const std::string getLogic() const { return d_logic.getLogicString(); }

  LogicInfo & getLogicInfo() { return d_logic; }

  TimerStat* getProofProductionTime() { return &d_stats.d_proofProductionTime; }

 private:
  std::map<Node, std::string> d_inputFormulaToName;

  SkolemizationManager d_skolemizationManager;

  int d_nextId;

  std::map<unsigned, NewProof> d_proof;

  ProofFormat d_format;

  struct ProofManagerStatistics
  {
    ProofManagerStatistics();
    ~ProofManagerStatistics();

    /**
     * Time spent producing proofs (i.e. generating the proof from the logging
     * information)
     */
    TimerStat d_proofProductionTime;
  }; /* struct ProofManagerStatistics */

  ProofManagerStatistics d_stats;

};/* class ProofManager */

}/* CVC4 namespace */

#endif /* CVC4__NEW_PROOF_MANAGER_H */
