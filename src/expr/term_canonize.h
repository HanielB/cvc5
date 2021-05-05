/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for constructing canonical terms.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__TERM_CANONIZE_H
#define CVC5__EXPR__TERM_CANONIZE_H

#include <map>
#include "expr/node.h"

namespace cvc5 {

class ProofNodeManager;
class TConvProofGenerator;

namespace theory {
class TrustNode;
}

namespace expr {

/** TermCanonize
 *
 * This class contains utilities for canonizing terms with respect to
 * free variables (which are of kind BOUND_VARIABLE). For example, this
 * class infers that terms like f(BOUND_VARIABLE_1) and f(BOUND_VARIABLE_2)
 * are effectively the same term.
 */
class TermCanonize
{
 public:
  TermCanonize(ProofNodeManager* pnm = nullptr, bool hoVar = false);
  ~TermCanonize();

  /** Maps operators to an identifier, useful for ordering. */
  int getIdForOperator(Node op);
  /** Maps types to an identifier, useful for ordering. */
  int getIdForType(TypeNode t);
  /** get term order
   *
   * Returns true if a <= b in the term ordering used by this class. The
   * term order is determined by the leftmost position in a and b whose
   * operators o_a and o_b are distinct at that position. Then a <= b iff
   * getIdForOperator( o_a ) <= getIdForOperator( o_b ).
   */
  bool getTermOrder(Node a, Node b);
  /** get canonical free variable #i of type tn */
  Node getCanonicalFreeVar(TypeNode tn, unsigned i);
  /** get canonical term
   *
   * This returns a canonical (alpha-equivalent) version of n, where
   * bound variables in n may be replaced by other ones, and arguments of
   * commutative operators of n may be sorted (if apply_torder is true). If
   * doHoVar is true, we also canonicalize bound variables that occur in
   * operators.
   *
   * In detail, we replace bound variables in n so the the leftmost occurrence
   * of a bound variable for type T is the first canonical free variable for T,
   * the second leftmost is the second, and so on, for each type T.
   */
  Node getCanonicalTerm(TNode n,
                             bool applyTOrder = false,
                             bool doHoVar = true);

  /**
   * As above but stores in the given map the substitution performed by the
   * canonizer and yields a proof node. */
  theory::TrustNode getCanonicalTerm(TNode n,
                                     std::map<Node, Node>& subs,
                                     bool applyTOrder = false,
                                     bool doHoVar = true);

 private:
  /** the number of ids we have allocated for operators */
  int d_op_id_count;
  /** map from operators to id */
  std::map<Node, int> d_op_id;
  /** the number of ids we have allocated for types */
  int d_typ_id_count;
  /** map from type to id */
  std::map<TypeNode, int> d_typ_id;
  /** free variables for each type */
  std::map<TypeNode, std::vector<Node> > d_cn_free_var;
  /**
   * Map from each free variable above to their index in their respective vector
   */
  std::map<Node, size_t> d_fvIndex;
  /**
   * Return the range of the free variable in the above map, or 0 if it does not
   * exist.
   */
  size_t getIndexForFreeVariable(Node v) const;

  /** Are proofs enabled for this object? */
  bool isProofEnabled() const;

  /** The proof generator of the transformations done by this class. */
  std::unique_ptr<TConvProofGenerator> d_tcpg;
};

}  // namespace expr
}  // namespace cvc5

#endif /* CVC5__EXPR__TERM_CANONIZE_H */
