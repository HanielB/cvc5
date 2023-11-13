/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict-based instantiation (using CCFV)
 */

#include "cvc5_private.h"

#ifndef CONFLICT_INST
#define CONFLICT_INST

#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ConflictInst : public QuantifiersModule
{
public:
 ConflictInst(Env& env,
              QuantifiersState& qs,
              QuantifiersInferenceManager& qim,
              QuantifiersRegistry& qr,
              TermRegistry& tr);

  /** needs check */
  bool needsCheck(Theory::Effort level) override;
  /** check
   *
   * This method attempts to construct a conflicting instance using CCFV.
   *
   * If such an instance exists, then it makes a call to
   * Instantiation::addInstantiation.
   */
  void check(Theory::Effort level, QEffort quant_e) override;
  /** Identify this module */
  std::string identify() const override { return "ConflictInst"; }

};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
