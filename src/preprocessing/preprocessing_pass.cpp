/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass super class.
 */

#include "preprocessing/preprocessing_pass.h"

#include <unordered_map>
#include <unordered_set>

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "theory/trust_substitutions.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {

namespace {
/**
 * The preprocessing passes whose dependencies are tracked when only the
 * dependencies of preprocessed formulas are tracked (--proof-log-no-pp). These
 * are the passes whose new assertions are valid (e.g., definitional lemmas) and
 * whose rewritten assertions are implied by the original ones (and such valid
 * assertions), as well as the passes that notify their other dependencies
 * (non-clausal simplification and the substitutions it adds). The assertions
 * added or replaced by other passes conservatively depend on all input
 * formulas.
 */
const std::unordered_set<std::string> s_depsTrackedPasses = {
    "apply-substs",
    "bv-eager-atoms",
    "distinct-elim",
    "ext-rew-pre",
    "ff-disjunctive-bit",
    "ite-removal",
    "non-clausal-simp",
    "quantifiers-preprocess",
    "rewrite",
    "static-learning",
    "static-rewrite",
    "strings-eager-pp",
    "theory-preprocess",
};
}  // namespace

PreprocessingPassResult PreprocessingPass::apply(
    AssertionPipeline* assertionsToPreprocess)
{
  TimerStat::CodeTimer codeTimer(d_timer);
  Trace("preprocessing") << "PRE " << d_name << std::endl;
  verbose(2) << d_name << "..." << std::endl;
  assertionsToPreprocess->setDepsOnAllInputs(s_depsTrackedPasses.find(d_name)
                                             == s_depsTrackedPasses.end());
  PreprocessingPassResult result = applyInternal(assertionsToPreprocess);
  assertionsToPreprocess->setDepsOnAllInputs(false);
  Trace("preprocessing") << "POST " << d_name << std::endl;
  return result;
}

void PreprocessingPass::addSubstitutions(
    AssertionPipeline* assertionsToPreprocess, theory::TrustSubstitutionMap& tm)
{
  const std::unordered_map<Node, Node> subs = tm.get().getSubstitutions();
  for (const std::pair<const Node, Node>& s : subs)
  {
    if (s.first.getKind() == Kind::SKOLEM)
    {
      assertionsToPreprocess->removeIteSkolem(s.first);
    }
  }
  d_preprocContext->addSubstitutions(tm);
}

PreprocessingPass::PreprocessingPass(PreprocessingPassContext* preprocContext,
                                     const std::string& name)
    : EnvObj(preprocContext->getEnv()),
      d_preprocContext(preprocContext),
      d_name(name),
      d_timer(statisticsRegistry().registerTimer("preprocessing::" + name))
{
}

PreprocessingPass::~PreprocessingPass() {}

}  // namespace preprocessing
}  // namespace cvc5::internal
