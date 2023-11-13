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
 * Implementation of conflict-based instantiation (using CCFV)
 */

#include "theory/quantifiers/conflict_instantiation.h"

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ConflictInst::ConflictInst(Env& env,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

bool ConflictInst::needsCheck(Theory::Effort level)
{
  return level == Theory::EFFORT_FULL;
}

void ConflictInst::check(Theory::Effort level, QEffort quant_e)
{
  FirstOrderModel* fm = d_treg.getModel();
  size_t nquant = fm->getNumAssertedQuantifiers();
  // for each quantified formula
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    // check quantified formulas that are active, not owned by other modules,
    // and, for now, that are disjunctions of literals
    if (!d_qreg.hasOwnership(q, this) || !fm->isQuantifierActive(q)
        || q[1].getKind() != Kind::OR)
    {
      continue;
    }
    std::vector<Node> negQuantLits;
    for (const Node& n: q[1])
    {
      bool notNode = n.getKind() == Kind::NOT;
      Kind k = notNode ? n[0].getKind() : n.getKind();
      if (!TermUtil::isBoolConnective(k))
      {
        break;
      }
      negQuantLits.push_back(notNode? n[0] : n.notNode());
    }
    if (negQuantLits.size() != q[1].getNumChildren())
    {
      continue;
    }
    Trace("conflict-inst") << "Checking quantified formula " << q
                           << " with negated lits\n\t.. " << negQuantLits
                           << "\n";

      /** get term database */
    TermDb* tdb = getTermDatabase();
    // TODO call CCFV module from here. The term database has the information
    // needed from E and the set of negated quantified literals will be L.
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
