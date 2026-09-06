/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for Alethe let binding
 */
#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE_LET_BINDING_H
#define CVC5__PROOF__ALETHE_LET_BINDING_H

#include "printer/let_binding.h"

namespace cvc5::internal {

namespace proof {

/** The Alethe-specific let binder.
 *
 * Differently from the regular let binder, where all letified subterms are
 * replaced by a fresh variable, the Alethe let binder replaces the first
 * occurrence of a term n (first visited on a post-order traversal) by a fresh
 * variable whose name is "(! n :named v)", in which `v` is another fresh
 * variable. The subsequent occurrences of `n` are replaced by `v`.
 */
class AletheLetBinding : public LetBinding
{
 public:
  AletheLetBinding(uint32_t thresh);

  /**
   * Convert n based on the state of the let binding.
   *
   * The conversion is done as summarized as above, but the name of the fresh
   * variable `v` is prefixed by `prefix`.
   *
   * @param n The node to convert
   * @param prefix The prefix of variables to convert
   * @return the converted node.
   */
  Node convert(NodeManager* nm, Node n, const std::string& prefix);

 private:
  /** The set of terms that have already been "decleared", i.e., already had
   * their first occurrence replaced. */
  std::unordered_set<Node> d_declared;
  /** The free bound variables of n, sorted, counting the converted choice
   * terms as binders. Cached in d_freeVars. */
  const std::vector<Node>& freeVars(TNode n);
  std::unordered_map<Node, std::vector<Node>> d_freeVars;
  /**
   * The key under which an occurrence of n is converted when the binders
   * enclosing it in the converted term bind the variables in `bound`: n
   * itself if none of its free variables is among them, otherwise an
   * s-expression pairing n with the captured variables. Occurrences with
   * different keys have different conversions (see convert).
   */
  Node keyOf(NodeManager* nm, TNode n, const std::vector<Node>& bound);
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHE_LET_BINDING_H */
