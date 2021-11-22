/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Manager of proofs for optimized clauses
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__OPT_CLAUSE_MANAGER_H
#define CVC5__PROP__OPT_CLAUSE_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"

#include "proof/proof.h"

namespace cvc5 {
namespace prop {

/**
 * A manager for the proofs of clauses that are stored in the SAT solver in a
 * context level below the one in which its proof is generated.
 *
 * Due to the above when popping the context in which the proof was generated
 * the respective clause, if ever needed in a subsequent (lower than generated)
 * context, would be proofless. To prevent the issue, this manager allows, for a
 * given context, storing a proof in a given level and, when the the respective
 * context pops, proofs of level no greater than the new one are reinserted in
 * proof marked to be notified.
 */
class OptimizedClausesManager : context::ContextNotifyObj
{
 public:
  OptimizedClausesManager(
      context::Context* context,
      CDProof* parentProof,
      std::map<int, std::vector<std::shared_ptr<ProofNode>>>& optProofs);

 private:
  void contextNotifyPop() override;

  context::Context* d_context;
  std::map<int, std::vector<std::shared_ptr<ProofNode>>>& d_optProofs;
  CDProof* d_parentProof;
};

}  // namespace prop
}  // namespace cvc5

#endif /* CVC5__PROP__OPT_CLAUSE_MANAGER_H */
