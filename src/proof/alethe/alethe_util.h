/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for Alethe proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE_ALETHE_UTIL_H
#define CVC5__PROOF__ALETHE_ALETHE_UTIL_H

#include <vector>

#include "expr/node.h"
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace proof {

/** Clause represented as an S-EXPR
 *
 * @return Whether there was an error when creating a step (due to a failed term
 * conversion).
 */
bool addAletheStepFromClause(AletheRule rule,
                             Node res,
                             const std::vector<Node>& conclusionLits,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args,
                             CDProof& cdp,
                             NodeManager* nm,
                             proof::AletheNodeConverter* anc,
                             bool ensureChildren = false);

bool addAletheStep(AletheRule rule,
                   Node res,
                   Node conclusion,
                   const std::vector<Node>& children,
                   const std::vector<Node>& args,
                   CDProof& cdp,
                   NodeManager* nm,
                   proof::AletheNodeConverter* anc,
                   bool ensureChildren = false);

}  // namespace proof
}  // namespace cvc5::internal

#endif
