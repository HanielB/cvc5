/*********************                                                        */
/*! \file inst_arrays_eqrange.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Handles equality range as quantified formulas through instantiation
 **/

#include "theory/quantifiers/inst_arrays_eqrange.h"

#include "options/arrays_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

namespace CVC4 {

using namespace kind;
using namespace context;

namespace theory {

using namespace inst;

namespace quantifiers {

InstArraysEqrange::InstArraysEqrange(QuantifiersEngine* qe)
    : QuantifiersModule(qe)
{
}

bool InstArraysEqrange::needsCheck(Theory::Effort e)
{
  return options::arraysEqrangeAsQuant() && e == Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstArraysEqrange::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

bool InstArraysEqrange::isEqrange(Node q)
{
  return false;
}

void InstArraysEqrange::checkOwnership(Node q)
{
  Assert(!isEqRange(q) || d_quantEngine->getOwner(q) == NULL);
  if (d_quantEngine->getOwner(q) == NULL && isEqrange(q))
  {
    // take full ownership of the quantified formula
    d_quantEngine->setOwner(q, this);
    d_claimed_quants.insert(q);
  }
}

void InstArraysEqrange::check(Theory::Effort e, QEffort quant_e)
{
  Trace("eqrange-as-quant")
      << "---InstArraysEqrange, effort = " << e << "---\n";

  for (const Node& q : d_claimed_quants)
  {
    if (!d_quantEngine->getModel()->isQuantifierActive(q))
    {
      continue;
    }
    Trace("eqrange-as-quant") << "Checking " << q << "\n";
    // getting model
    FirstOrderModel* fm = d_quantEngine->getModel();
    // get relevant indices for arrays (from master equality engine)
    // check with values
    // add instance if failed
  }
}

bool InstArraysEqrange::checkCompleteFor(Node q)
{
  return d_claimed_quants.find(q) == d_claimed_quants.end();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
