/*********************                                                        */
/*! \file inst_arrays_eqrange.h
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

#include "cvc4_private.h"

#ifndef __CVC4__INST_ARRAYS_EQRANGE_H
#define __CVC4__INST_ARRAYS_EQRANGE_H

#include "context/context.h"
#include "context/context_mm.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Instantiation for arrays eqrange
 */
class InstArraysEqrange : public QuantifiersModule
{
 public:
  InstArraysEqrange(QuantifiersEngine* qe);
  ~InstArraysEqrange() {}
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  QEffort needsModel(Theory::Effort e) override;
  void checkOwnership(Node q) override;
  /** Check.
   *
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  bool checkCompleteFor(Node q) override;
  /** Identify. */
  std::string identify() const override
  {
    return std::string("InstArraysEqrange");
  }

 private:
  /** whether q = forall x : (bv sz). (or [(x > lb) (x < ub)] (= a[x] b[x]))) */
  bool isEqrangeQuant(Node q);
  std::unordered_set<Node, NodeHashFunction> d_claimed_quants;
  struct QuantInfo
  {
    /** lower bound */
    Node lb;
    /** upper bound */
    Node ub;
    /** arrays */
    Node a1;
    Node a2;
  }
  std::map<Node, QuantInfo> d_quant_to_info;
}; /* class InstArraysEqrange */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
