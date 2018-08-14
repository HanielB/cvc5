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

/** Instantiation strategy for arrays equality range
 *
 * For quantifiers representing arrays equality within a range, this module
 * determines if there is an index within the range on which the respective
 * arrays are different, introducing instantiations is such a case. If no
 * instance can be derived, then the quantifier is true in the current model.
 */
class InstArraysEqrange : public QuantifiersModule
{
 public:
  InstArraysEqrange(QuantifiersEngine* qe);
  ~InstArraysEqrange() {}
  /** Lets quantifier engine knows this module needs a last effort check. */
  bool needsCheck(Theory::Effort e) override;
  /** Lets quantifier engine knows this module needs a model */
  QEffort needsModel(Theory::Effort e) override;
  /** Register eqrange quantifiers */
  void registerQuantifier(Node q) override;
  /** Takes ownership of eqrange quantifiers depending on option */
  void checkOwnership(Node q) override;
  /** Check
   *
   * Determines whether, for each currently asserted claimed quantifier, there
   * exists an index within the respective quantifier's bounds on which its
   * arrays differ
   *
   * The check is based on the model values of the bounds, arrays and indices.
   *
   * An instance is added with the respective index when the arrays differ
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Returns true for claimed quantifiers */
  bool checkCompleteFor(Node q) override;
  /** Identify. */
  std::string identify() const override
  {
    return std::string("InstArraysEqrange");
  }

 private:
  /** whether q = forall x : (bv sz). (or [(x > lb) (x < ub)] (= a[x] b[x]))) */
  bool isEqrangeQuant(Node q);
  /** set of claimed quantifiers */
  std::unordered_set<Node, NodeHashFunction> d_claimed_quants;
  /** Bounds and arrays associated with each eqrange quantifier  */
  struct QuantInfo
  {
    /** lower bound */
    Node lb;
    /** upper bound */
    Node ub;
    /** arrays */
    Node a1;
    Node a2;
  };
  /** map from claimed quantifiers to bound/array information */
  std::map<Node, QuantInfo> d_quant_to_info;
}; /* class InstArraysEqrange */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
