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
 * The proof-producing CNF stream.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__OPT_CLAUSE_MANAGER_H
#define CVC5__PROP__OPT_CLAUSE_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "prop/sat_proof_manager.h"

namespace cvc5 {
namespace prop {

class ProofCnfStream;
class SatProofManager;

class OptimizedClausseManager : context::ContextNotifyObj
{
  friend ProofCnfStream;
  friend SatProofManager;

 public:
  OptimizedClausesManager(
      context::Context* context,
      std::map<int, std::vector<std::shared_ptr<ProofNode>>>& optProofs,
      LazyCDProof* parentProof)
      : context::ContextNotifyObj(context),
        d_context(context),
        d_optProofs(optProofs),
        d_parentProof(parentProof)
  {
  }

 protected:
  void contextNotifyPop() override
  {
    int newLvl = d_context->getLevel();
    Trace("cnf") << "contextNotifyPop: called with lvl " << newLvl << "\n"
                 << push;
    // the increment is handled inside the loop, so that we can erase as we go
    for (auto it = d_optProofs.cbegin(); it != d_optProofs.cend();)
    {
      if (it->first <= newLvl)
      {
        Trace("cnf") << "Should re-add pfs of [" << it->first << "]:\n";
        for (const auto& pf : it->second)
        {
          Node processedPropgation = pf->getResult();
          Trace("cnf") << "\t- " << processedPropgation << "\n\t\t{" << pf
                       << "} " << *pf.get() << "\n";
          // Note that this proof may have already been added in a previous
          // pop. For example, if a proof associated with level 1 was added
          // when going down from 2 to 1, but then we went up to 2 again, when
          // we go back to 1 the proof will still be there. Note that if say
          // we had a proof of level 1 that was added at level 2 when we were
          // going down from 3, we'd still need to add it again when going to
          // level 1, since it'd be popped in that case.
          if (!d_parentProof->hasStep(processedPropgation))
          {
            d_parentProof->addProof(pf);
          }
          else
          {
            Trace("cnf") << "\t..skipped since already added\n";
          }
        }
        ++it;
        continue;
      }
      Trace("cnf") << "Should remove from map pfs of [" << it->first << "]:\n";
      for (const auto& pf : it->second)
      {
        Trace("cnf") << "\t- " << pf->getResult() << "\n";
      }
      it = d_optProofs.erase(it);
    }
    Trace("cnf") << pop;
  }

  context::Context* d_context;
  std::map<int, std::vector<std::shared_ptr<ProofNode>>>& d_optProofs;
  LazyCDProof* d_parentProof;
};

#endif /* CVC5__PROP__OPT_CLAUSE_MANAGER_H */
