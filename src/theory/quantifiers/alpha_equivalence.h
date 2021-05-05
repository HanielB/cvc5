/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Paul Meng
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alpha equivalence checking.
 */

#include "cvc5_private.h"

#ifndef CVC5__ALPHA_EQUIVALENCE_H
#define CVC5__ALPHA_EQUIVALENCE_H

#include "expr/lazy_proof.h"
#include "theory/quantifiers/quant_util.h"

#include "expr/term_canonize.h"

namespace cvc5 {

// class ProofNodeManager;
// class LazyCDProof;

namespace expr {
class TermCanonize;
}

namespace theory {

class TrustNode;

namespace quantifiers {

/**
 * This trie stores a trie for each multi-set of types. For each term t
 * registered to this node, we store t in the appropriate
 * AlphaEquivalenceTypeNode trie. For example, if t contains 2 free variables of
 * type T1 and 3 free variables of type T2, then it is stored at
 * d_children[T1][2].d_children[T2][3].
 */
class AlphaEquivalenceTypeNode {
public:
 /** children of this node */
 std::map<std::pair<TypeNode, size_t>, AlphaEquivalenceTypeNode> d_children;
 /**
  * map from canonized quantifier bodies to a quantified formula whose
  * canonized body is that term.
  */
 std::map<Node, Node> d_quant;

 /** register node
  *
  * This registers term q to this trie. The term t is the canonical form of
  * q, typs/typCount represent a multi-set of types of free variables in t.
  */
 Node registerNode(Node q,
                   Node t,
                   const std::vector<TypeNode>& typs,
                   const std::map<TypeNode, size_t>& typCount);
};

/**
 * Stores a database of quantified formulas, which computes alpha-equivalence.
 */
class AlphaEquivalenceDb
{
 public:
  AlphaEquivalenceDb(expr::TermCanonize* tc,
                     ProofNodeManager* pnm,
                     bool sortCommChildren);
  /** adds quantified formula q to this database
   *
   * This function returns a quantified formula q' that is alpha-equivalent to
   * q. If q' != q, then q' was previously added to this database via a call
   * to addTerm.
   */
  TrustNode addTerm(Node q);
  /** maps quantifiers to their canonical forms */
  std::map<Node, Node> d_canon;
  /** maps quantifiers to the substitution used to canonize them */
  std::map<Node, std::map<Node, Node>> d_canonization;

 private:
  /** a trie per # of variables per type */
  AlphaEquivalenceTypeNode d_ae_typ_trie;
  /** pointer to the term canonize utility */
  expr::TermCanonize* d_tc;
  /** whether to sort children of commutative operators during canonization. */
  bool d_sortCommutativeOpChildren;
  /**
   * A LazyCDProof storing alpha equivalence steps.
   */
  std::unique_ptr<LazyCDProof> d_proof;
  /** Are proofs enabled for this object? */
  bool isProofEnabled() const;
};

/**
 * A quantifiers module that computes reductions based on alpha-equivalence,
 * using the above utilities.
 */
class AlphaEquivalence
{
 public:
  AlphaEquivalence(ProofNodeManager* pnm = nullptr);
  /** reduce quantifier
   *
   * If non-null, its return value is a trust node containing the lemma
   * justifying why q is reducible.  This lemma is of the form ( q = q' ) where
   * q' is a quantified formula that was previously registered to this class via
   * a call to reduceQuantifier, and q and q' are alpha-equivalent.
   */
  TrustNode reduceQuantifier(Node q);

 private:
  /** a term canonizer */
  std::unique_ptr<expr::TermCanonize> d_termCanon;
  /** the database of quantified formulas registered to this class */
  AlphaEquivalenceDb d_aedb;
};

}
}
}  // namespace cvc5

#endif
