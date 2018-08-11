/*********************                                                        */
/*! \file eqrange_to_quant.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The EqrangeToQuant preprocessing pass
 **
 ** Converts the eqrange predicate into its axiomatization
 **/

#include "preprocessing/passes/eqrange_to_quant.h"

#include <string>

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

EqrangeToQuant::EqrangeToQuant(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "eqrange-to-quant"){};

Node EqrangeToQuant::eqrangeToQuantInternal(TNode n, NodeMap& cache)
{
  Trace("eqrange-as-quant-debug") << "Convert : " << n << "\n";
  NodeMap::iterator find = cache.find(n);
  if (find != cache.end())
  {
    return (*find).second;
  }
  Node ret = n;
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (k == kind::EQ_RANGE)
  {
    // bounds are of bitvector type
    Assert(n[2].getType().isBitVector() && n[3].getType().isBitVector());
    // mk bound var list
    Node index = nm->mkBoundVar(n[2].getType());
    Node bvl = nm->mkNode(kind::BOUND_VAR_LIST, index);
    // mk quantified formula
    // forall i. i < lb v i > ub v a[i] = b[i]
    std::vector<Node> body;
    body.push_back(nm->mkNode(kind::BITVECTOR_ULT, index, n[2]));
    Trace("eqrange-as-quant-debug")
        << "...built i < lb : " << body.back() << "\n";
    body.push_back(nm->mkNode(kind::BITVECTOR_UGT, index, n[3]));
    Trace("eqrange-as-quant-debug")
        << "...built i > ub : " << body.back() << "\n";
    body.push_back(nm->mkNode(kind::EQUAL,
                              nm->mkNode(kind::SELECT, n[0], index),
                              nm->mkNode(kind::SELECT, n[1], index)));
    Trace("eqrange-as-quant-debug")
        << "...built a[i] = b[i] : " << body.back() << "\n";
    ret = nm->mkNode(kind::FORALL, bvl, nm->mkNode(kind::OR, body));
  }
  else
  {
    bool childChanged = false;
    std::vector<Node> children;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      Node nc = eqrangeToQuantInternal(n[i], cache);
      childChanged = childChanged || nc != n[i];
      children.push_back(nc);
    }
    if (childChanged)
    {
      ret = nm->mkNode(k, children);
    }
  }
  Trace("eqrange-as-quant-debug") << "Converted : " << ret << "\n";
  cache[n] = ret;
  return ret;
}

PreprocessingPassResult EqrangeToQuant::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, eqrangeToQuantInternal((*assertionsToPreprocess)[i], cache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
