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
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/bv/theory_bv_utils.h"

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

bool InstArraysEqrange::isEqrangeQuant(Node q)
{
  // compute attributes
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);
  Trace("eqrange-as-quant")
      << "Quant is eqrange? " << (qa.d_eqrange ? "true" : "false") << "\n";
  return qa.d_eqrange;
}

void InstArraysEqrange::checkOwnership(Node q)
{
  Trace("eqrange-as-quant") << "InstEqrange: checking ownership :" << q << "\n";
  Assert(!isEqRange(q) || d_quantEngine->getOwner(q) == NULL);
  if (d_quantEngine->getOwner(q) == NULL && isEqrangeQuant(q))
  {
    Trace("eqrange-as-quant") << "InstArraysEqrange taking full ownership\n";
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
    Trace("eqrange-as-quant") << "...checking " << q << "\n";
    // getting bounds
    Node var = q[0][0];
    unsigned size = theory::bv::utils::getSize(var);
    Node lb = theory::bv::utils::mkZero(size),
         ub = theory::bv::utils::mkOnes(size);
    for (unsigned i = 0, size = q[1].getNumChildren(); i < size; ++i)
    {
      Node n = q[1][i];
      Kind k = n.getKind();
      Assert(k == EQUAL || k == BITVECTOR_UGT || k == BITVECTOR_ULT);
      if (k == BITVECTOR_ULT)
      {
        lb = n[0] == var? n[1] : n[0];
      }
      else if (k == BITVECTOR_UGT)
      {
        ub = n[0] == var? n[1] : n[0];
      }
    }
    // getting model
    FirstOrderModel* fm = d_quantEngine->getModel();
    Trace("eqrange-as-quant")
        << "......bound values: lb: " << lb << " = " << fm->getValue(lb)
        << ", ub: " << ub << " = " << fm->getValue(ub) << "\n";
    // get relevant indices for arrays (from master equality engine)

    // check with values
    // add instance if failed
  }
}

bool InstArraysEqrange::checkCompleteFor(Node q)
{
  Trace("eqrange-as-quant")
      << "InstArraysEqrange : complete for " << q << "\n... "
      << (d_claimed_quants.find(q) != d_claimed_quants.end()) << "\n";
  return d_claimed_quants.find(q) != d_claimed_quants.end();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
