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
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
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
  NodeManager* nm = NodeManager::currentNM();
  TermDb* db = d_quantEngine->getTermDatabase();
  FirstOrderModel* fm = d_quantEngine->getModel();
  for (const Node& q : d_claimed_quants)
  {
    if (!d_quantEngine->getModel()->isQuantifierActive(q))
    {
      continue;
    }
    Trace("eqrange-as-quant") << "...checking " << q << "\n";
    // getting bounds and arrays
    Node var = q[0][0];
    unsigned size = theory::bv::utils::getSize(var);
    Node lb = theory::bv::utils::mkZero(size),
         ub = theory::bv::utils::mkOnes(size);
    Node a1, a2;
    for (unsigned i = 0, size = q[1].getNumChildren(); i < size; ++i)
    {
      Node n = q[1][i];
      Kind k = n.getKind();
      Assert(k == EQUAL || k == BITVECTOR_UGT || k == BITVECTOR_ULT);
      if (k == BITVECTOR_ULT)
      {
        lb = n[0] == var ? n[1] : n[0];
      }
      else if (k == BITVECTOR_UGT)
      {
        ub = n[0] == var ? n[1] : n[0];
      }
      else
      {
        // assert they are arrays
        a1 = n[0][0];
        a2 = n[1][0];
      }
    }
    Trace("eqrange-as-quant")
        << "......arrays: " << a1 << " | " << a2
        << "\n......bound values: lb: " << fm->getValue(lb)
        << ", ub: " << fm->getValue(ub) << "\n";
    // get relevant indices for arrays (from master equality engine)
    std::unordered_set<Node, NodeHashFunction> indices;
    Trace("eqrange-as-quant") << "...selects and stores:\n";
    for (unsigned k = 0, numOps = db->getNumOperators(); k < numOps; ++k)
    {
      bool store = false, select = false;
      Node op = db->getOperator(k);
      // parametric ops are stored as an apps (so we can identify their type)
      if (op.hasOperator())
      {
        Node actual_op = op.getOperator();
        if (actual_op == nm->operatorOf(SELECT))
        {
          select = true;
        }
        else if (actual_op == nm->operatorOf(STORE))
        {
          store = true;
        }
        else
        {
          continue;
        }
      }
      else
      {
        continue;
      }
      for (unsigned i = 0, size = db->getNumGroundTerms(op); i < size; ++i)
      {
        Node app = db->getGroundTerm(op, i);
        Trace("eqrange-as-quant") << app << "\n";
        if ((select || store) && (app[0] == a1 || app[0] == a2))
        {
          indices.insert(app[1]);
          Trace("eqrange-as-quant") << "...adding index " << app[1] << "\n";
        }
      }
    }
    // check with values
    BitVector lb_value = fm->getValue(lb).getConst<BitVector>(),
              ub_value = fm->getValue(ub).getConst<BitVector>();
    for (const Node& index : indices)
    {
      BitVector index_value = fm->getValue(index).getConst<BitVector>();
      Trace("eqrange-as-quant") << "...index :" << index_value << "\n";
      if (index_value.unsignedLessThan(lb_value)
          || ub_value.unsignedLessThan(index_value))
      {
        Trace("eqrange-as-quant")
            << "......out of bounds : "
            << (index_value.unsignedLessThan(lb_value) ? "smaller\n"
                                                       : "bigger\n");
        continue;
      }
      Trace("eqrange-as-quant") << "...test for : " << index_value << "\n";
      Node e1 = nm->mkNode(SELECT, a1, index);
      Node e2 = nm->mkNode(SELECT, a2, index);
      Trace("eqrange-as-quant")
          << "...test for : " << e1 << " = " << fm->getValue(e1)
          << "\n...test for : " << e2 << " = " << fm->getValue(e2) << "\n";
      // add instance if failed
      if (fm->getValue(e1) != fm->getValue(e2))
      {
        std::vector<Node> terms;
        terms.push_back(index);
        if (d_quantEngine->getInstantiate()->addInstantiation(q, terms))
        {
          Trace("eqrange-as-quant") << "...adding instance for " << index << "\n";
        }
      }
    }
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
