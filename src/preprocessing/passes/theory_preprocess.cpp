/*********************                                                        */
/*! \file theory_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryPreprocess preprocessing pass
 **
 ** Calls Theory::preprocess(...) on every assertion of the formula.
 **/

#include "preprocessing/passes/theory_preprocess.h"

#include "options/proof_options.h"
#include "proof/new_proof.h"
#include "proof/new_proof_manager.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

TheoryPreprocess::TheoryPreprocess(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "theory-preprocess"){};

PreprocessingPassResult TheoryPreprocess::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  te->preprocessStart();
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    TNode a = (*assertionsToPreprocess)[i];
    Assert(Rewriter::rewrite(a) == a);
    assertionsToPreprocess->replace(i, te->preprocess(a));
    a = (*assertionsToPreprocess)[i];
    if (CVC4::options::newProofs())
    {
      if (a != (*assertionsToPreprocess)[i])
      {
        NewProofManager::currentPM()->addAssertionProofStep(
            a, (*assertionsToPreprocess)[i], RULE_PREPROCESSING_THEORY);
      }
    }
    Assert(Rewriter::rewrite(a) == a);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
