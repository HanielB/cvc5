/*********************                                                        */
/*! \file ho_elim.cpp
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

#include "preprocessing/passes/ho_elim.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

HoElim::HoElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ho-elim"){};

Node HoElim::eliminateHo(Node n) { return n; }

PreprocessingPassResult HoElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node res = eliminateHo(prev);
    if (res != prev)
    {
      assertionsToPreprocess->replace(i, res);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
