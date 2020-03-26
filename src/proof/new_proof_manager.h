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
#include "new_proof.h"
#include "proof/proof.h"
#include "proof/proof_utils.h"
#include "proof/sat_proof.h"
#include "proof/skolemization_manager.h"
#include "prop/minisat/core/Solver.h"
#include "prop/sat_solver_types.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "util/statistics_registry.h"

namespace CVC4 {

// forward declarations
namespace Minisat {
class Solver;
}  // namespace Minisat

namespace prop {
class CnfStream;
}  // namespace prop

class SmtEngine;

namespace prop {
typedef uint64_t SatVariable;
class SatLiteral;
typedef std::vector<SatLiteral> SatClause;
}  // namespace prop

class Resolution
{
 public:
  // clause being resolved with another clause using the pivot with the given
  // sign
  ClauseId d_id;
  Node d_piv;
  bool d_sign;

  Resolution(ClauseId id, Node piv = Node::null(), bool sign = false)
      : d_id(id), d_piv(piv), d_sign(sign)
  {
  }
};

class NewProofManager
{
 protected:
  LogicInfo d_logic;

 public:
  NewProofManager(options::ProofFormatMode format);
  ~NewProofManager();

  static NewProofManager* currentPM();

  // getting proof
  NewProof& getProof();

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

  /* ------------ BEGIN Defining maps between SAT / solver info ------------ */

  void addLitDef(prop::SatLiteral lit, Node litNode);
  void addClauseDef(ClauseId clause, Node clauseNodeDef);
  void addClauseDef(ClauseId clause, Node clauseNode, Node clauseNodeDef);

  ClauseId registerClause(Minisat::Solver::TLit lit);

  ClauseId registerClause(Minisat::Solver::TLit lit,
                          NewProofRule reason,
                          Node litNodeDef = Node::null());

  ClauseId registerClause(Minisat::Solver::TClause& clause);

  ClauseId registerClause(Minisat::Solver::TClause& clause,
                          NewProofRule reason,
                          Node clauseNodeDef = Node::null());

  void startResChain(Minisat::Solver::TClause& start);
  void addResolutionStep(Minisat::Solver::TLit lit,
                         Minisat::Solver::TClause& clause,
                         bool sign);
  void endResChain(Minisat::Solver::TLit lit);
  void endResChain(ClauseId id);

  /** The id of the proof step that explains this literal */
  ClauseId justifyLit(Minisat::Solver::TLit lit);

  void finalizeProof(ClauseId conflict_id);
  void finalizeProof();
  void finalizeProof(Minisat::Solver::TLit lit);

  inline void printLit(const Minisat::Solver::TLit lit);
  inline void printClause(const Minisat::Solver::TClause& clause);

  /* ------------ END Defining maps between SAT / solver info ------------ */

  /* ------------ BEGIN Registering proof steps ------------ */

  /** Add input **/
  void addInputAssertion(Node formula);

  /** Associate subformula of input assertion which is directly derived from CNF
   * transformat with the ID of its justification
   *
   * This is used for example with stuff like A ^ B being an input, then
   *   A ^ B -> A
   *   A ^ B -> ¬B
   * being added during CNF transformation without intermediary definitions
   * being added (not yet, at least) added for A, ¬B.
   */
  void addInputSubAssertion(Node formula, ClauseId id);

  /* General proof step. For now used for preprocessing only */
  void addAssertionProofStep(Node src, Node dest, NewProofRule rule);

  // create conclusion in which clauseNodes are CNF-derived from src, according
  // to rule. The id might be undefined (in which case a new proof step is
  // created) or not (in which case the valid clause is added to the proofstep
  // already created that has that id)
  ClauseId addCnfProofStep(NewProofRule rule,
                           ClauseId id,
                           Node src,
                           std::vector<Node>& clauseNodes);

  // as above, but retrieves the clauseNodes from clause first
  ClauseId addCnfProofStep(NewProofRule rule,
                           ClauseId id,
                           Node src,
                           prop::SatClause clause);

  // not sure what this is about. It does not create proof steps. It may update
  // the clause id of a given literal.
  ClauseId addCnfProofStep(prop::SatLiteral lit, ClauseId id);

  // create a valid clause according to rule. The given id corresponds to a
  // previously created proof step, therefore it's always defined
  //
  // the ith value, if given, will be position of the literal being derived from
  // an n-ary transformation
  void addDefCnfProofStep(NewProofRule rule,
                          ClauseId id,
                          prop::SatClause clause,
                          unsigned ith = -1);

  void queueTheoryProof(prop::SatLiteral lit, theory::EqProof* proof);

  /* ------------ END Registering proof steps ------------ */

  unsigned nextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);

  const std::string getLogic() const { return d_logic.getLogicString(); }

  LogicInfo& getLogicInfo() { return d_logic; }

  TimerStat* getProofProductionTime() { return &d_stats.d_proofProductionTime; }

  void setSatSolver(Minisat::Solver* solver) { d_solver = solver; }

 private:
  /* pointer to core SAT solver */
  Minisat::Solver* d_solver;

  std::unique_ptr<NewProof> d_proof;

  /** maps SAT literals to the nodes they correspond to */
  std::map<prop::SatLiteral, Node> d_litToNode;

  /** maps SAT literals that have been propagated by theories to the proof of
   * why they could have been propagated */
  std::map<prop::SatLiteral, theory::EqProof*> d_litToTheoryProof;

  /** maps clauses to the nodes they correspond to */
  std::map<Node, ClauseId> d_assertionToClauseId;

  std::map<ClauseId, Node> d_clauseToNode;
  std::map<ClauseId, Node> d_clauseToNodeDef;

  std::map<ClauseId, Minisat::Solver::TClause*> d_clauseIdToClause;

  std::map<prop::SatLiteral, ClauseId> d_litToClauseId;
  std::map<ClauseId, prop::SatLiteral> d_clauseIdToLit;

  std::vector<Resolution> d_resolution;

  std::vector<std::vector<Resolution>> d_resolutions;

  options::ProofFormatMode d_format;

  unsigned d_nextId;

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

}; /* class ProofManager */

}  // namespace CVC4

#endif /* CVC4__NEW_PROOF_MANAGER_H */
