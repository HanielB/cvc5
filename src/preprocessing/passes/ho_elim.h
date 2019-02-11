/*********************                                                        */
/*! \file ho_elim.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The HoElim preprocessing pass
 **
 ** Eliminates higher-order constraints.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H
#define __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class HoElim : public PreprocessingPass
{
 public:
  HoElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** eliminate all higher-order constraints in n, return the result */
  Node eliminateHo(Node n);
  /** map to ho_apply for each sort */
  std::map<TypeNode, Node> d_hoApplyUf;
  /** map to uninterpreted sort for each function sort */
  std::map<TypeNode, TypeNode> d_ftypeMap;
  /** visited */
  std::unordered_map<TNode, Node, TNodeHashFunction> d_visited;
  std::unordered_map<TNode, Node, TNodeHashFunction> d_visited_op;
  /** map from functions that are used in a first-order context */
  std::unordered_set<TNode, TNodeHashFunction> d_foFun;

  /** get ho apply app for sort */
  Node getHoApplyUf(TypeNode tn);
  Node getHoApplyUf(TypeNode tn, TypeNode tna, TypeNode tnr);
  /** get uninterpreted sort for function sort */
  TypeNode getUSort(TypeNode tn);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H */
