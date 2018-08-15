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
  if (q[0].getNumChildren() > 1 || !q[0][0].getType().isBitVector())
  {
    return false;
  }
  Node var = q[0][0];
  unsigned size = theory::bv::utils::getSize(var);
  bool set_lb = false, set_ub = false, set_arrays = false;
  QuantInfo qi;
  for (const Node& n : q[1])
  {
    Kind k = n.getKind();
    if (k != EQUAL && k != BITVECTOR_UGT && k != BITVECTOR_ULT)
    {
      return false;
    }
    if (k == BITVECTOR_ULT)
    {
      qi.lb = n[0] == var ? n[1] : n[0];
      set_lb = true;
    }
    else if (k == BITVECTOR_UGT)
    {
      qi.ub = n[0] == var ? n[1] : n[0];
      set_ub = true;
    }
    else
    {
      // assign arrays from equality
      qi.a1 = n[0][0];
      qi.a2 = n[1][0];
      set_arrays = true;
    }
  }
  if (!set_lb && !set_ub && !set_arrays)
  {
    return false;
  }
  // if bounds not set, assign beginning/end of interval
  if (!set_lb)
  {
    qi.lb = theory::bv::utils::mkZero(size);
  }
  if (!set_ub)
  {
    qi.ub = theory::bv::utils::mkOnes(size);
  }
  d_quant_to_info[q] = qi;
  return true;
}

void InstArraysEqrange::registerQuantifier(Node q)
{
  if (isEqrangeQuant(q))
  {
    Trace("eqrange-inst-debug") << "InstArraysEqrange : claiming " << q << "\n";
    d_claimed_quants.insert(q);
  }
}

void InstArraysEqrange::checkOwnership(Node q)
{
  if (d_quantEngine->getOwner(q) == NULL && options::ownEqrangeQuant()
      && isEqrangeQuant(q))
  {
    Trace("eqrange-inst-debug") << "InstArraysEqrange taking full ownership\n";
    d_quantEngine->setOwner(q, this);
  }
}

void InstArraysEqrange::check(Theory::Effort e, QEffort quant_e)
{
  Trace("eqrange-inst") << "---InstArraysEqrange, effort = " << e << "---\n";
  NodeManager* nm = NodeManager::currentNM();
  TermDb* db = d_quantEngine->getTermDatabase();
  FirstOrderModel* fm = d_quantEngine->getModel();
  for (const Node& q : d_claimed_quants)
  {
    if (!d_quantEngine->getModel()->isQuantifierActive(q))
    {
      continue;
    }
    Trace("eqrange-inst") << "...checking " << q << "\n";
    Assert(d_quant_to_info.find(q) != d_quant_to_info.end());
    QuantInfo qi = d_quant_to_info[q];
    // get relevant indices for arrays (from master equality engine)
    std::unordered_set<Node, NodeHashFunction> indices;
    Trace("eqrange-inst-index") << "...selects and stores:\n";
    for (unsigned k = 0, numOps = db->getNumOperators(); k < numOps; ++k)
    {
      bool store = false, select = false;
      Node op = db->getOperator(k);
      Trace("eqrange-inst-index") << "...testing op: " << op << "\n";
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
        Trace("eqrange-inst-index") << "......app: " << app << "\n";
        if ((select || store) && (app[0] == qi.a1 || app[0] == qi.a2))
        {
          indices.insert(app[1]);
          Trace("eqrange-inst-index") << "...adding index " << app[1] << "\n";
        }
      }
    }
    // check with values
    BitVector lb_value = fm->getValue(qi.lb).getConst<BitVector>(),
              ub_value = fm->getValue(qi.ub).getConst<BitVector>();
    for (const Node& index : indices)
    {
      BitVector index_value = fm->getValue(index).getConst<BitVector>();
      Trace("eqrange-inst-index") << "...index :" << index_value << "\n";
      if (index_value.unsignedLessThan(lb_value)
          || ub_value.unsignedLessThan(index_value))
      {
        Trace("eqrange-inst-index")
            << "......out of bounds : "
            << (index_value.unsignedLessThan(lb_value) ? "smaller\n"
                                                       : "bigger\n");
        continue;
      }
      Trace("eqrange-inst-index") << "...test for : " << index_value << "\n";
      Node e1 = nm->mkNode(SELECT, qi.a1, index);
      Node e2 = nm->mkNode(SELECT, qi.a2, index);
      Trace("eqrange-inst-index")
          << "...test for : " << e1 << " = " << fm->getValue(e1)
          << "\n...test for : " << e2 << " = " << fm->getValue(e2) << "\n\n";
      // add instance if failed
      if (fm->getValue(e1) != fm->getValue(e2))
      {
        std::vector<Node> terms;
        terms.push_back(index);
        if (d_quantEngine->getInstantiate()->addInstantiation(q, terms))
        {
          Trace("eqrange-inst") << "...adding instance for " << index << "\n";
        }
      }
    }
  }
}

bool InstArraysEqrange::checkCompleteFor(Node q)
{
  Trace("eqrange-inst") << "InstArraysEqrange : "
                        << (d_claimed_quants.find(q) != d_claimed_quants.end()
                                ? ""
                                : "not")
                        << "complete for " << q << "\n";
  return d_claimed_quants.find(q) != d_claimed_quants.end();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
