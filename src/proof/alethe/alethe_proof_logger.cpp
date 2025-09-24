/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe proof logger utility.
 */

#include "proof/alethe/alethe_proof_logger.h"

#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "smt/proof_manager.h"
#include "util/string.h"

namespace cvc5::internal {
namespace proof {

AletheProofLogger::AletheProofLogger(Env& env,
                                     std::ostream& out,
                                     smt::PfManager* pm,
                                     smt::Assertions& as,
                                     smt::ProofPostprocess* ppp)
    : ProofLogger(env),
      d_out(out),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_ppp(ppp),
      d_anc(nodeManager(), options().proof.proofAletheDefineSkolems),
      d_appproc(env, d_anc),
      d_apprinter(env, d_anc)
{
  d_hadError = false;
  d_multPPClauses = false;
  Trace("alethe-pf-log-debug") << "Make Alethe proof logger" << std::endl;
  if (env.getLogicInfo().isHigherOrder())
  {
    Trace("alethe-pf-log-debug") << "..HOL; ignore everything" << std::endl;
    out << "(error \"Proof unsupported by Alethe: contains higher-order "
           "elements\")";
    d_hadError = true;
  }
}

AletheProofLogger::~AletheProofLogger() {}

bool AletheProofLogger::processPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                                            bool inner,
                                            bool finalStep,
                                            std::string& error)
{
  if (inner)
  {
    if (d_appproc.processInnerProof(pfn, finalStep))
    {
      return true;
    }
    error = d_appproc.getError();
    return false;
  }
  if (d_appproc.process(pfn))
  {
    return true;
  }
  error = d_appproc.getError();
  return false;
}

bool AletheProofLogger::printPfNodesAlethe(
    std::vector<std::shared_ptr<ProofNode>>& pfns,
    const std::vector<Node>& assumptions)
{
  options::ProofCheckMode oldMode = options().proof.proofCheck;
  d_pnm->getChecker()->setProofCheckMode(options::ProofCheckMode::NONE);
  bool success = d_appproc.processInnerProofs(pfns, assumptions);
  if (success)
  {
    for (const std::shared_ptr<ProofNode>& pfn : pfns)
    {
      d_apprinter.printProofNode(d_out, pfn);
    }
  }
  else
  {
    d_out << "(error " << d_appproc.getError() << ")";
  }
  d_pnm->getChecker()->setProofCheckMode(oldMode);
  return success;
}

bool AletheProofLogger::printPfNodeAlethe(std::shared_ptr<ProofNode>& pfn,
                                          bool inner,
                                          bool finalStep)
{
  options::ProofCheckMode oldMode = options().proof.proofCheck;
  d_pnm->getChecker()->setProofCheckMode(options::ProofCheckMode::NONE);
  std::map<Node, std::string> assertionNames;
  std::string error;
  bool success = processPfNodeAlethe(pfn, inner, finalStep, error);
  if (inner)
  {
    if (success)
    {
      d_apprinter.printProofNode(d_out, pfn);
    }
    else
    {
      d_out << "(error " << error << ")";
    }
  }
  else
  {
    if (success)
    {
      d_apprinter.print(d_out, pfn, assertionNames);
    }
    else
    {
      d_out << "(error " << error << ")";
    }
  }
  d_pnm->getChecker()->setProofCheckMode(oldMode);
  return success;
}

void AletheProofLogger::logCnfPreprocessInputs(const std::vector<Node>& inputs)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof start"
                         << std::endl;
  CDProof cdp(d_env);
  Node conc = nodeManager()->mkAnd(inputs);
  cdp.addTrustedStep(conc, TrustId::PREPROCESSED_INPUT, inputs, {});
  std::shared_ptr<ProofNode> pfn = cdp.getProofFor(conc);
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
  printPfNodeAlethe(d_ppProof);
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof end"
                         << std::endl;
}

void AletheProofLogger::printPreprocessingProof(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
    d_multPPClauses = pfns.size() > 1;
    std::shared_ptr<ProofNode> pfn =
        pfns.size() == 1 ? pfns[0]
                         : d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
    ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
    d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
    Assert(d_ppProof->getRule() == ProofRule::SCOPE
           && d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
    std::shared_ptr<ProofNode> definitionsScope = d_ppProof;
    std::shared_ptr<ProofNode> assumptionsScope = d_ppProof->getChildren()[0];
    std::vector<Node> assumptions{definitionsScope->getArguments().begin(),
                                  definitionsScope->getArguments().end()};
    assumptions.insert(assumptions.end(),
                       assumptionsScope->getArguments().begin(),
                       assumptionsScope->getArguments().end());
    // Sanitize original assumptions
    std::vector<Node> sanitizedAssumptions;
    for (const Node& a : assumptions)
    {
      Node conv = d_anc.maybeConvert(a, true);
      if (conv.isNull())
      {
        d_hadError = true;
        d_out << "(error " << d_anc.getError() << ")";
        break;
      }
      // avoid repeated assumptions
      if (std::find(
              sanitizedAssumptions.begin(), sanitizedAssumptions.end(), conv)
          == sanitizedAssumptions.end())
      {
        sanitizedAssumptions.push_back(conv);
      }
    }
    if (!d_hadError)
    {
      std::map<Node, std::string> assertionNames;
      d_apprinter.printInitialAssumptions(
          d_out, sanitizedAssumptions, assertionNames, true);
      // not process and print each preprocessing proof. They should connect to
      // the assumptions
      Trace("alethe-pf-log")
          << "; log: reprocess again the inputs to save them for later printing"
          << std::endl;
      std::shared_ptr<ProofNode> ppBody =
          d_ppProof->getChildren()[0]->getChildren()[0];
      if (!printPfNodeAlethe(ppBody, true, false))
      {
        d_hadError = true;
      }

      // d_hadError = !printPfNodesAlethe(pfns, assumptions);
      // d_ppPfs.insert(d_ppPfs.end(), pfns.begin(), pfns.end());

      // for (const std::shared_ptr<ProofNode>& pf : pfns)
      // {
      //   context::CDHashMap<ProofNode*, std::string>::const_iterator pfIt =
      //       d_apprinter.getPfMap()->find(pf.get());
      //   if (pfIt != d_apprinter.getPfMap()->end())
      //   {
      //     Trace("alethe-pf-log") << "\thas in map step for preprocessing of "
      //                            << pf->getResult() << "\n";
      //   }
      // }
    }
}

void AletheProofLogger::logCnfPreprocessInputProofs(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof start"
                         << std::endl;
  // if the assertions are empty, we do nothing. We will answer sat.
  if (!pfns.empty() && !options().proof.proofLogLazyPreProcessing)
  {
    printPreprocessingProof(pfns);
  }
  Trace("alethe-pf-log") << "; log: cnf preprocess input proof end"
                         << std::endl;
}

void AletheProofLogger::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log theory lemma proof start "
                         << pfn->getResult() << std::endl;
  d_lemmaPfs.emplace_back(pfn);
  printPfNodeAlethe(pfn, true);
  Trace("alethe-pf-log") << "; log theory lemma proof end" << std::endl;
}

std::unordered_map<theory::InferenceId, std::string> s_infIdToStr = {
    {theory::InferenceId::NONE, "none"},
    {theory::InferenceId::INPUT, "core"},
    {theory::InferenceId::EQ_CONSTANT_MERGE, "core"},
    {theory::InferenceId::COMBINATION_SPLIT, "core"},
    {theory::InferenceId::CONFLICT_REWRITE_LIT, "core"},
    {theory::InferenceId::EXPLAINED_PROPAGATION, "core"},
    {theory::InferenceId::THEORY_PP_SKOLEM_LEM, "core"},
    {theory::InferenceId::EXTT_SIMPLIFY, "ext-theory"},
    {theory::InferenceId::ARITH_BLACK_BOX, "arith"},
    {theory::InferenceId::ARITH_CONF_EQ, "arith"},
    {theory::InferenceId::ARITH_CONF_LOWER, "arith"},
    {theory::InferenceId::ARITH_CONF_TRICHOTOMY, "arith"},
    {theory::InferenceId::ARITH_CONF_UPPER, "arith"},
    {theory::InferenceId::ARITH_CONF_SIMPLEX, "arith"},
    {theory::InferenceId::ARITH_CONF_SOI_SIMPLEX, "arith"},
    {theory::InferenceId::ARITH_CONF_FACT_QUEUE, "arith"},
    {theory::InferenceId::ARITH_CONF_BRANCH_CUT, "arith"},
    {theory::InferenceId::ARITH_CONF_REPLAY_ASSERT, "arith"},
    {theory::InferenceId::ARITH_CONF_REPLAY_LOG, "arith"},
    {theory::InferenceId::ARITH_CONF_REPLAY_LOG_REC, "arith"},
    {theory::InferenceId::ARITH_CONF_UNATE_PROP, "arith"},
    {theory::InferenceId::ARITH_SPLIT_DEQ, "arith"},
    {theory::InferenceId::ARITH_TIGHTEN_CEIL, "arith"},
    {theory::InferenceId::ARITH_TIGHTEN_FLOOR, "arith"},
    {theory::InferenceId::ARITH_APPROX_CUT, "arith"},
    {theory::InferenceId::ARITH_BB_LEMMA, "arith"},
    {theory::InferenceId::ARITH_DIO_CUT, "arith"},
    {theory::InferenceId::ARITH_DIO_DECOMPOSITION, "arith"},
    {theory::InferenceId::ARITH_UNATE, "arith"},
    {theory::InferenceId::ARITH_ROW_IMPL, "arith"},
    {theory::InferenceId::ARITH_SPLIT_FOR_NL_MODEL, "arith"},
    {theory::InferenceId::ARITH_DEMAND_RESTART, "arith"},
    {theory::InferenceId::ARITH_PP_ELIM_OPERATORS, "arith"},
    {theory::InferenceId::ARITH_PP_ELIM_OPERATORS_LEMMA, "arith"},
    {theory::InferenceId::ARITH_NL_CONGRUENCE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_SHARED_TERM_SPLIT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_CM_QUADRATIC_EQ, "nl-arith"},
    {theory::InferenceId::ARITH_NL_SPLIT_ZERO, "nl-arith"},
    {theory::InferenceId::ARITH_NL_SIGN, "nl-arith"},
    {theory::InferenceId::ARITH_NL_COMPARISON, "nl-arith"},
    {theory::InferenceId::ARITH_NL_INFER_BOUNDS, "nl-arith"},
    {theory::InferenceId::ARITH_NL_INFER_BOUNDS_NT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_FACTOR, "nl-arith"},
    {theory::InferenceId::ARITH_NL_RES_INFER_BOUNDS, "nl-arith"},
    {theory::InferenceId::ARITH_NL_TANGENT_PLANE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_SINE_SYMM, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_SINE_BOUNDARY_REDUCE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_PURIFY_ARG, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_PURIFY_ARG_PHASE_SHIFT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_INIT_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_PI_BOUND, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_MONOTONICITY, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_TANGENT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_T_SECANT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_IAND_INIT_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_IAND_VALUE_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_IAND_SUM_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_IAND_BITWISE_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_POW2_INIT_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_POW2_VALUE_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_POW2_MONOTONE_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_POW2_TRIVIAL_CASE_REFINE, "nl-arith"},
    {theory::InferenceId::ARITH_NL_COVERING_CONFLICT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL, "nl-arith"},
    {theory::InferenceId::ARITH_NL_ICP_CONFLICT, "nl-arith"},
    {theory::InferenceId::ARITH_NL_ICP_PROPAGATION, "nl-arith"},
    {theory::InferenceId::FF_LEMMA, "finite-fields"},
    {theory::InferenceId::ARRAYS_EXT, "arrays"},
    {theory::InferenceId::ARRAYS_READ_OVER_WRITE, "arrays"},
    {theory::InferenceId::ARRAYS_READ_OVER_WRITE_1, "arrays"},
    {theory::InferenceId::ARRAYS_READ_OVER_WRITE_CONTRA, "arrays"},
    {theory::InferenceId::ARRAYS_CONST_ARRAY_DEFAULT, "arrays"},
    {theory::InferenceId::ARRAYS_EQ_TAUTOLOGY, "arrays"},
    {theory::InferenceId::BV_BITBLAST_CONFLICT, "bv"},
    {theory::InferenceId::BV_BITBLAST_INTERNAL_EAGER_LEMMA, "bv"},
    {theory::InferenceId::BV_BITBLAST_INTERNAL_BITBLAST_LEMMA, "bv"},
    {theory::InferenceId::BV_LAYERED_CONFLICT, "bv"},
    {theory::InferenceId::BV_LAYERED_LEMMA, "bv"},
    {theory::InferenceId::BV_EXTF_LEMMA, "bv"},
    {theory::InferenceId::BV_EXTF_COLLAPSE, "bv"},
    {theory::InferenceId::DATATYPES_PURIFY, "datatypes"},
    {theory::InferenceId::DATATYPES_UNIF, "datatypes"},
    {theory::InferenceId::DATATYPES_INST, "datatypes"},
    {theory::InferenceId::DATATYPES_SPLIT, "datatypes"},
    {theory::InferenceId::DATATYPES_BINARY_SPLIT, "datatypes"},
    {theory::InferenceId::DATATYPES_LABEL_EXH, "datatypes"},
    {theory::InferenceId::DATATYPES_COLLAPSE_SEL, "datatypes"},
    {theory::InferenceId::DATATYPES_CLASH_CONFLICT, "datatypes"},
    {theory::InferenceId::DATATYPES_TESTER_CONFLICT, "datatypes"},
    {theory::InferenceId::DATATYPES_TESTER_MERGE_CONFLICT, "datatypes"},
    {theory::InferenceId::DATATYPES_BISIMILAR, "datatypes"},
    {theory::InferenceId::DATATYPES_REC_SINGLETON_EQ, "datatypes"},
    {theory::InferenceId::DATATYPES_REC_SINGLETON_FORCE_DEQ, "datatypes"},
    {theory::InferenceId::DATATYPES_CYCLE, "datatypes"},
    {theory::InferenceId::DATATYPES_SIZE_POS, "datatypes"},
    {theory::InferenceId::DATATYPES_HEIGHT_ZERO, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_SYM_BREAK, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_CDEP_SYM_BREAK, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_ENUM_SYM_BREAK, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_SIMPLE_SYM_BREAK, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_FAIR_SIZE, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_FAIR_SIZE_CONFLICT, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_VAR_AGNOSTIC, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_SIZE_CORRECTION, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_VALUE_CORRECTION, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_MT_BOUND, "datatypes"},
    {theory::InferenceId::DATATYPES_SYGUS_MT_POS, "datatypes"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_SIMPLE, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_MT, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_MTL, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_HO, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_VAR_GEN, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_E_MATCHING_RELATIONAL, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_CBQI_CONFLICT, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_CBQI_PROP, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_SUB_CONFLICT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SUB_UC, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_FMF_EXH, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_FMF_FMC, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_FMF_FMC_EXH, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_CEGQI, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_SYQI, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_MBQI, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_MBQI_ENUM, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_ENUM, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_POOL, "quant"},
    {theory::InferenceId::QUANTIFIERS_INST_POOL_TUPLE, "quant"},
    {theory::InferenceId::QUANTIFIERS_BINT_PROXY, "quant"},
    {theory::InferenceId::QUANTIFIERS_BINT_MIN_NG, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_CEX, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_CEX_AUX, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_NESTED_QE, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_CEX_DEP, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_VTS_LB_DELTA, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_VTS_UB_DELTA, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_VTS_LB_INF, "quant"},
    {theory::InferenceId::QUANTIFIERS_ORACLE_INTERFACE, "quant"},
    {theory::InferenceId::QUANTIFIERS_ORACLE_PURIFY_SUBS, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYQI_CEX, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYQI_EVAL_UNFOLD, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_ENUM_ACTIVE_GUARD_SPLIT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_ACTIVE_GEN_EXCLUDE_CURRENT,
     "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_STREAM_EXCLUDE_CURRENT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_INC_EXCLUDE_CURRENT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_SC_EXCLUDE_CURRENT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_NO_VERIFY_EXCLUDE_CURRENT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_REPEAT_CEX_EXCLUDE_CURRENT,
     "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_EXAMPLE_INFER_CONTRA, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_SI_INFEASIBLE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_INTER_ENUM_SB, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_SEPARATION, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_FAIR_SIZE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_REM_OPS, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_ENUM_SB, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_DOMAIN, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_COND_EXCLUDE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_UNIF_PI_REFINEMENT, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_CEGIS_UCL_SYM_BREAK, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_CEGIS_UCL_EXCLUDE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_REPAIR_CONST_EXCLUDE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_CEGIS_REFINE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_CEGIS_REFINE_SAMPLE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_REFINE_EVAL, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_EVAL_UNFOLD, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_PBE_EXCLUDE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_PBE_CONSTRUCT_SOL, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_COMPLETE_ENUM, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_SC_INFEASIBLE, "quant"},
    {theory::InferenceId::QUANTIFIERS_SYGUS_NO_WF_GRAMMAR, "quant"},
    {theory::InferenceId::QUANTIFIERS_DSPLIT, "quant"},
    {theory::InferenceId::QUANTIFIERS_CONJ_GEN_SPLIT, "quant"},
    {theory::InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM, "quant"},
    {theory::InferenceId::QUANTIFIERS_SKOLEMIZE, "quant"},
    {theory::InferenceId::QUANTIFIERS_REDUCE_ALPHA_EQ, "quant"},
    {theory::InferenceId::QUANTIFIERS_HO_MATCH_PRED, "quant"},
    {theory::InferenceId::QUANTIFIERS_HO_PURIFY, "quant"},
    {theory::InferenceId::QUANTIFIERS_PARTIAL_TRIGGER_REDUCE, "quant"},
    {theory::InferenceId::QUANTIFIERS_GT_PURIFY, "quant"},
    {theory::InferenceId::QUANTIFIERS_TDB_DEQ_CONG, "quant"},
    {theory::InferenceId::QUANTIFIERS_CEGQI_WITNESS, "quant"},
    {theory::InferenceId::STRINGS_I_NORM_S, "str"},
    {theory::InferenceId::STRINGS_I_CONST_MERGE, "str"},
    {theory::InferenceId::STRINGS_I_CONST_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_I_NORM, "str"},
    {theory::InferenceId::STRINGS_UNIT_SPLIT, "str"},
    {theory::InferenceId::STRINGS_UNIT_INJ_OOB, "str"},
    {theory::InferenceId::STRINGS_UNIT_INJ, "str"},
    {theory::InferenceId::STRINGS_UNIT_CONST_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_UNIT_INJ_DEQ, "str"},
    {theory::InferenceId::STRINGS_CARD_SP, "str"},
    {theory::InferenceId::STRINGS_CARDINALITY, "str"},
    {theory::InferenceId::STRINGS_I_CYCLE_E, "str"},
    {theory::InferenceId::STRINGS_I_CYCLE, "str"},
    {theory::InferenceId::STRINGS_F_CONST, "str"},
    {theory::InferenceId::STRINGS_F_UNIFY, "str"},
    {theory::InferenceId::STRINGS_F_ENDPOINT_EMP, "str"},
    {theory::InferenceId::STRINGS_F_ENDPOINT_EQ, "str"},
    {theory::InferenceId::STRINGS_F_NCTN, "str"},
    {theory::InferenceId::STRINGS_N_EQ_CONF, "str"},
    {theory::InferenceId::STRINGS_N_ENDPOINT_EMP, "str"},
    {theory::InferenceId::STRINGS_N_UNIFY, "str"},
    {theory::InferenceId::STRINGS_N_ENDPOINT_EQ, "str"},
    {theory::InferenceId::STRINGS_N_CONST, "str"},
    {theory::InferenceId::STRINGS_INFER_EMP, "str"},
    {theory::InferenceId::STRINGS_SSPLIT_CST_PROP, "str"},
    {theory::InferenceId::STRINGS_SSPLIT_VAR_PROP, "str"},
    {theory::InferenceId::STRINGS_LEN_SPLIT, "str"},
    {theory::InferenceId::STRINGS_LEN_SPLIT_EMP, "str"},
    {theory::InferenceId::STRINGS_SSPLIT_CST, "str"},
    {theory::InferenceId::STRINGS_SSPLIT_VAR, "str"},
    {theory::InferenceId::STRINGS_FLOOP, "str"},
    {theory::InferenceId::STRINGS_FLOOP_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_NORMAL_FORM, "str"},
    {theory::InferenceId::STRINGS_N_NCTN, "str"},
    {theory::InferenceId::STRINGS_LEN_NORM, "str"},
    {theory::InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT, "str"},
    {theory::InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT, "str"},
    {theory::InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT, "str"},
    {theory::InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT, "str"},
    {theory::InferenceId::STRINGS_DEQ_STRINGS_EQ, "str"},
    {theory::InferenceId::STRINGS_DEQ_LENS_EQ, "str"},
    {theory::InferenceId::STRINGS_DEQ_NORM_EMP, "str"},
    {theory::InferenceId::STRINGS_DEQ_LENGTH_SP, "str"},
    {theory::InferenceId::STRINGS_DEQ_EXTENSIONALITY, "str"},
    {theory::InferenceId::STRINGS_CODE_PROXY, "str"},
    {theory::InferenceId::STRINGS_CODE_INJ, "str"},
    {theory::InferenceId::STRINGS_ARRAY_UPDATE_UNIT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_UPDATE_CONCAT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_UPDATE_CONCAT_INVERSE, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_UNIT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_CONCAT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_EXTRACT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_UPDATE, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_TERM_FROM_UPDATE, "str"},
    {theory::InferenceId::STRINGS_ARRAY_UPDATE_BOUND, "str"},
    {theory::InferenceId::STRINGS_ARRAY_EQ_SPLIT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_UPDATE_WITH_UNIT, "str"},
    {theory::InferenceId::STRINGS_ARRAY_NTH_REV, "str"},
    {theory::InferenceId::STRINGS_RE_NF_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_RE_UNFOLD_POS, "str"},
    {theory::InferenceId::STRINGS_RE_UNFOLD_NEG, "str"},
    {theory::InferenceId::STRINGS_RE_INTER_INCLUDE, "str"},
    {theory::InferenceId::STRINGS_RE_INTER_CONF, "str"},
    {theory::InferenceId::STRINGS_RE_INTER_INFER, "str"},
    {theory::InferenceId::STRINGS_RE_DELTA, "str"},
    {theory::InferenceId::STRINGS_RE_DELTA_CONF, "str"},
    {theory::InferenceId::STRINGS_RE_DERIVE, "str"},
    {theory::InferenceId::STRINGS_EXTF, "str"},
    {theory::InferenceId::STRINGS_EXTF_N, "str"},
    {theory::InferenceId::STRINGS_EXTF_D, "str"},
    {theory::InferenceId::STRINGS_EXTF_D_N, "str"},
    {theory::InferenceId::STRINGS_EXTF_EQ_REW, "str"},
    {theory::InferenceId::STRINGS_CTN_TRANS, "str"},
    {theory::InferenceId::STRINGS_CTN_DECOMPOSE, "str"},
    {theory::InferenceId::STRINGS_CTN_NEG_EQUAL, "str"},
    {theory::InferenceId::STRINGS_CTN_POS, "str"},
    {theory::InferenceId::STRINGS_REDUCTION, "str"},
    {theory::InferenceId::STRINGS_PREFIX_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_PREFIX_CONFLICT_MIN, "str"},
    {theory::InferenceId::STRINGS_ARITH_BOUND_CONFLICT, "str"},
    {theory::InferenceId::STRINGS_REGISTER_TERM_ATOMIC, "str"},
    {theory::InferenceId::STRINGS_REGISTER_TERM, "str"},
    {theory::InferenceId::STRINGS_CMI_SPLIT, "str"},
    {theory::InferenceId::STRINGS_CONST_SEQ_PURIFY, "str"},
    {theory::InferenceId::STRINGS_RE_EQ_ELIM_EQUIV, "str"},
    {theory::InferenceId::UF_BREAK_SYMMETRY, "uf"},
    {theory::InferenceId::UF_CARD_CLIQUE, "uf"},
    {theory::InferenceId::UF_CARD_COMBINED, "uf"},
    {theory::InferenceId::UF_CARD_ENFORCE_NEGATIVE, "uf"},
    {theory::InferenceId::UF_CARD_EQUIV, "uf"},
    {theory::InferenceId::UF_CARD_MONOTONE_COMBINED, "uf"},
    {theory::InferenceId::UF_CARD_SIMPLE_CONFLICT, "uf"},
    {theory::InferenceId::UF_CARD_SPLIT, "uf"},
    {theory::InferenceId::UF_HO_CG_SPLIT, "uf"},
    {theory::InferenceId::UF_HO_APP_ENCODE, "uf"},
    {theory::InferenceId::UF_HO_APP_CONV_SKOLEM, "uf"},
    {theory::InferenceId::UF_HO_EXTENSIONALITY, "uf"},
    {theory::InferenceId::UF_HO_MODEL_APP_ENCODE, "uf"},
    {theory::InferenceId::UF_HO_MODEL_EXTENSIONALITY, "uf"},
    {theory::InferenceId::UF_HO_LAMBDA_UNIV_EQ, "uf"},
    {theory::InferenceId::UF_HO_LAMBDA_APP_REDUCE, "uf"},
    {theory::InferenceId::UF_HO_LAMBDA_LAZY_LIFT, "uf"},
    {theory::InferenceId::UF_ARITH_BV_CONV_REDUCTION, "uf"},
    {theory::InferenceId::UF_ARITH_BV_CONV_VALUE_REFINE, "uf"},
};

void AletheProofLogger::logTheoryLemma(const Node& n, theory::InferenceId id)
{
  if (d_hadError)
  {
    return;
  }
  if (d_lemmas.count(n))
  {
    Trace("alethe-pf-log") << "; log theory lemma no-op (repeated lemma) " << n
                           << std::endl;
    return;
  }
  d_lemmas.insert(n);
  Trace("alethe-pf-log") << "; log theory lemma start " << n << std::endl;
  Trace("alethe-pf-log") << "id: " << id << std::endl;
  // create Alethe step directly. No need to go via the post-processor.
  std::vector<Node> args{nodeManager()->mkConstInt(
      Rational(static_cast<uint32_t>(AletheRule::HOLE)))};
  args.push_back(n);
  Node conclusion = d_anc.maybeConvert(n);
  if (conclusion.isNull())
  {
    d_hadError = true;
    d_out << "(error " << d_anc.getError() << ")";
    return;
  }
  args.push_back(conclusion);
  args.push_back(nodeManager()->mkConst(String("THEORY_LEMMA")));
  auto it = s_infIdToStr.find(id);
  args.push_back(nodeManager()->mkConst(String(it == s_infIdToStr.end()? "other" : it->second)));
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkNode(ProofRule::ALETHE_RULE, {}, args, n);
  d_lemmaPfs.emplace_back(ptl);

  d_apprinter.printProofNode(d_out, ptl, true);
  // d_out << conclusion << "\n";
  Trace("alethe-pf-log") << "; log theory lemma end" << std::endl;
}

void AletheProofLogger::logSatRefutation()
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises{d_ppPfs.begin(),
                                                   d_ppPfs.end()};
  if (Configuration::isAssertionBuild())
  {
    // make sure that each of these premises is present in the preprocessing
    // proof and was therefore printed
    Assert(d_ppProof->getRule() == ProofRule::SCOPE);
    Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
    std::shared_ptr<ProofNode> ppBody =
        d_ppProof->getChildren()[0]->getChildren()[0];
    // we ignore the translated AND_INTRO step and rather directly get the
    // proofs for the clauses
    for (const std::shared_ptr<ProofNode>& ppPf : d_ppPfs)
    {
      Node n = ppPf->getResult();
      // Traverse the proof node to find a subproof concluding n.
      Assert(expr::getSubproofFor(n, ppBody))
          << "Could not find " << n << std::endl;
    }
  }
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  printPfNodeAlethe(psr, true, true);
  Trace("alethe-pf-log") << "; log SAT refutation end" << std::endl;
}

void AletheProofLogger::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn)
{
  if (d_hadError)
  {
    return;
  }
  Trace("alethe-pf-log") << "; log SAT refutation proof start" << std::endl;
  Assert(d_ppProof->getRule() == ProofRule::SCOPE);
  Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
  std::shared_ptr<ProofNode> ppBody =
      d_ppProof->getChildren()[0]->getChildren()[0];
  std::vector<std::shared_ptr<ProofNode>> premises;
  if (d_multPPClauses)
  {
    // get the premises of the and_intro rule
    Assert(getAletheRule(ppBody->getArguments()[0]) == AletheRule::AND_INTRO);
    const std::vector<std::shared_ptr<ProofNode>>& pfChildren =
        ppBody->getChildren();
    premises.insert(premises.end(), pfChildren.begin(), pfChildren.end());
  }
  else
  {
    premises.push_back(ppBody);
  }

  // std::vector<std::shared_ptr<ProofNode>> premises{ppBody};
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  printPfNodeAlethe(psr, true, true);
  Trace("alethe-pf-log") << "; log SAT refutation proof end" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
