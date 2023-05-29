/*********************                                                        */
/*! \file lean_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lean post processor
 **/

#include "proof/lean/lean_post_processor.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "proof/lazy_proof.h"
#include "proof/lean/lean_rules.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {

namespace proof {

std::unordered_map<PfRule, LeanRule, PfRuleHashFunction> s_pfRuleToLeanRule = {
    {PfRule::EQ_RESOLVE, LeanRule::EQ_RESOLVE},
    {PfRule::AND_ELIM, LeanRule::AND_ELIM},
    {PfRule::NOT_OR_ELIM, LeanRule::NOT_OR_ELIM},
    {PfRule::NOT_AND, LeanRule::NOT_AND},
    {PfRule::REFL, LeanRule::REFL},
    {PfRule::THEORY_REWRITE, LeanRule::TH_TRUST_VALID},
    {PfRule::NOT_IMPLIES_ELIM1, LeanRule::NOT_IMPLIES1},
    {PfRule::NOT_IMPLIES_ELIM2, LeanRule::NOT_IMPLIES2},
    {PfRule::MODUS_PONENS, LeanRule::MODUS_PONENS},
    {PfRule::PREPROCESS, LeanRule::TH_TRUST_VALID},
    {PfRule::TRUE_INTRO, LeanRule::TRUE_INTRO},
    {PfRule::TRUE_ELIM, LeanRule::TRUE_ELIM},
    {PfRule::FALSE_INTRO, LeanRule::FALSE_INTRO},
    {PfRule::FALSE_ELIM, LeanRule::FALSE_ELIM},
    {PfRule::EQUIV_ELIM1, LeanRule::EQUIV_ELIM1},
    {PfRule::EQUIV_ELIM2, LeanRule::EQUIV_ELIM2},
    {PfRule::NOT_EQUIV_ELIM1, LeanRule::NOT_EQUIV_ELIM1},
    {PfRule::NOT_EQUIV_ELIM2, LeanRule::NOT_EQUIV_ELIM2},
    {PfRule::XOR_ELIM1, LeanRule::XOR_ELIM1},
    {PfRule::XOR_ELIM2, LeanRule::XOR_ELIM2},
    {PfRule::NOT_XOR_ELIM1, LeanRule::NOT_XOR_ELIM1},
    {PfRule::NOT_XOR_ELIM2, LeanRule::NOT_XOR_ELIM2},
    {PfRule::ITE_ELIM1, LeanRule::ITE_ELIM1},
    {PfRule::ITE_ELIM2, LeanRule::ITE_ELIM2},
    {PfRule::NOT_ITE_ELIM1, LeanRule::NOT_ITE_ELIM1},
    {PfRule::NOT_ITE_ELIM2, LeanRule::NOT_ITE_ELIM2},
    {PfRule::CNF_IMPLIES_POS, LeanRule::CNF_IMPLIES_POS},
    {PfRule::CNF_IMPLIES_NEG1, LeanRule::CNF_IMPLIES_NEG1},
    {PfRule::CNF_IMPLIES_NEG2, LeanRule::CNF_IMPLIES_NEG2},
    {PfRule::CNF_EQUIV_POS1, LeanRule::CNF_EQUIV_POS1},
    {PfRule::CNF_EQUIV_POS2, LeanRule::CNF_EQUIV_POS2},
    {PfRule::CNF_EQUIV_NEG1, LeanRule::CNF_EQUIV_NEG1},
    {PfRule::CNF_EQUIV_NEG2, LeanRule::CNF_EQUIV_NEG2},
    {PfRule::CNF_XOR_POS1, LeanRule::CNF_XOR_POS1},
    {PfRule::CNF_XOR_POS2, LeanRule::CNF_XOR_POS2},
    {PfRule::CNF_XOR_NEG1, LeanRule::CNF_XOR_NEG1},
    {PfRule::CNF_XOR_NEG2, LeanRule::CNF_XOR_NEG2},
    {PfRule::CNF_ITE_POS1, LeanRule::CNF_ITE_POS1},
    {PfRule::CNF_ITE_POS2, LeanRule::CNF_ITE_POS2},
    {PfRule::CNF_ITE_POS3, LeanRule::CNF_ITE_POS3},
    {PfRule::CNF_ITE_NEG1, LeanRule::CNF_ITE_NEG1},
    {PfRule::CNF_ITE_NEG2, LeanRule::CNF_ITE_NEG2},
    {PfRule::CNF_ITE_NEG3, LeanRule::CNF_ITE_NEG3},
    {PfRule::NOT_NOT_ELIM, LeanRule::NOT_NOT_ELIM},
    {PfRule::ARRAYS_READ_OVER_WRITE, LeanRule::READ_OVER_WRITE},
    {PfRule::ARRAYS_READ_OVER_WRITE_CONTRA, LeanRule::READ_OVER_WRITE_CONTRA},
    {PfRule::ARRAYS_READ_OVER_WRITE_1, LeanRule::READ_OVER_WRITE_ID},
    {PfRule::ARRAYS_EXT, LeanRule::ARRAY_EXT},
    {PfRule::SKOLEM_INTRO, LeanRule::SKOLEM_INTRO},
    {PfRule::ARITH_SUM_UB, LeanRule::SUM_BOUNDS},
    {PfRule::ARITH_MULT_POS, LeanRule::ARITH_MULT_POS},
    {PfRule::ARITH_MULT_NEG, LeanRule::ARITH_MULT_NEG},
    {PfRule::ARITH_TRICHOTOMY, LeanRule::TRICHOTOMY},
    {PfRule::INT_TIGHT_UB, LeanRule::INT_TIGHT_UB},
    {PfRule::INT_TIGHT_LB, LeanRule::INT_TIGHT_LB},
};

LeanProofPostprocess::LeanProofPostprocess(Env& env, LeanNodeConverter& lnc)
    : EnvObj(env),
      d_cb(new LeanProofPostprocessCallback(lnc))
{
}

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    LeanNodeConverter& lnc)
    : d_lnc(lnc)
{
  NodeManager* nm = NodeManager::currentNM();
  d_empty = d_lnc.convert(nm->mkNode(kind::SEXPR));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void LeanProofPostprocessCallback::addLeanStep(
    Node res,
    LeanRule rule,
    Node convertedResult,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> leanArgs = {
      NodeManager::currentNM()->mkConstInt(Rational(static_cast<uint32_t>(rule))),
      res,
      convertedResult};
  leanArgs.insert(leanArgs.end(), args.begin(), args.end());
  bool success CVC5_UNUSED =
      cdp.addStep(res, PfRule::LEAN_RULE, children, leanArgs);
  Assert(success);
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LEAN_RULE && pn->getRule() != PfRule::ASSUME;
};

Node LeanProofPostprocessCallback::getLastDiff(Node clause, Node pivot)
{
  for (size_t size = clause.getNumChildren(), i = size; i > 0; --i)
  {
    if (clause[i - 1] != pivot)
    {
      return clause[i - 1];
    }
  }
  return Node::null();
}

Node LeanProofPostprocessCallback::getLastDiffs(Node clause,
                                                Node pivot1,
                                                Node pivot2)
{
  for (size_t size = clause.getNumChildren(), i = size; i > 0; --i)
  {
    if (clause[i - 1] != pivot1 && clause[i - 1] != pivot2)
    {
      return clause[i - 1];
    }
  }
  return Node::null();
}


Node LeanProofPostprocessCallback::getSingletonPosition(
    Node clause, size_t pos, const std::vector<Node>& pivots)
{
  NodeManager* nm = NodeManager::currentNM();
  if (clause.getKind() != kind::OR
      || (pivots[2 * (pos - 1)] == d_false && pivots[2 * (pos - 1) + 1] == clause))
  {
    return nm->mkConstInt(Rational(0));
  }
  if (clause[clause.getNumChildren() - 1].getKind() == kind::OR)
  {
    return nm->mkConstInt(Rational(clause.getNumChildren() - 1));
  }
  return nm->mkConstInt(Rational(-1));
}

void LeanProofPostprocessCallback::buildTransitivyChain(
    Node conclusion, const std::vector<Node>& links, CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cur = links[0];
  // it's important to go the route of creating exotic intermediary terms to
  // guarantee that they will not clash with other terms from the proof
  TypeNode tn = conclusion[0].getType();
  Node op = d_lnc.mkInternalSymbol("Eq", nm->mkFunctionType({tn, tn}, tn));
  for (size_t i = 1, size = links.size(); i < size - 1; ++i)
  {
    Node newCur = nm->mkNode(kind::APPLY_UF, op, links[i][0], links[i][1]);
    addLeanStep(
        newCur, LeanRule::TRANS_PARTIAL, d_empty, {cur, links[i]}, {}, *cdp);
    cur = newCur;
  }
  addLeanStep(conclusion,
              LeanRule::TRANS,
              d_lnc.convert(conclusion),
              {cur, links.back()},
              {},
              *cdp);
}

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  Trace("test-lean") << "Updating rule " << id << ": " << res << "\n.."
                     << children.size() << " children: " << children << "\n.."
                     << args.size() << " args: " << args << "\n";
  NodeManager* nm = NodeManager::currentNM();
  switch (id)
  {
    // create clausal conclusion. Shortcut if before scope
    case PfRule::IMPLIES_ELIM:
    {
      // regular case, just turn conclusion into clause
      addLeanStep(
          res, LeanRule::IMPLIES_ELIM, d_lnc.convert(res), children, {}, *cdp);
      break;
    }
    // create clausal conclusion
    case PfRule::SCOPE:
    {
      bool negation = false;
      // new result is an or with all assumptions negated and the original
      // conclusion
      std::vector<Node> newResChildren;
      std::vector<Node> newArgs;
      for (const Node& n : args)
      {
        newResChildren.push_back(n.notNode());
        newArgs.push_back(d_lnc.convert(n));
      }
      if (res.getKind() == kind::NOT)
      {
        negation = true;
        newResChildren.push_back(d_false);
      }
      else
      {
        Assert(res.getKind() == kind::IMPLIES || res.getKind() == kind::OR);
        newResChildren.push_back(res[1]);
      }
      Node newRes = nm->mkNode(kind::OR, newResChildren);
      addLeanStep(newRes,
                  LeanRule::SCOPE,
                  d_lnc.convert(newRes),
                  children,
                  newArgs,
                  *cdp);
      // add a lifting step from the OR above to the original conclusion. It
      // takes as arguments the number of assumptions and subproof conclusion
      newArgs.clear();
      if (!negation)
      {
        newArgs.push_back(nm->mkConstInt(Rational(args.size())));
      }
      addLeanStep(
          res,
          negation ? LeanRule::LIFT_OR_N_TO_NEG : LeanRule::LIFT_OR_N_TO_IMP,
          d_lnc.convert(res),
          {newRes},
          newArgs,
          *cdp);
      break;
    }
    // only the rule changes and can be described with a pure mapping
    case PfRule::EQ_RESOLVE:
    case PfRule::NOT_IMPLIES_ELIM1:
    case PfRule::NOT_IMPLIES_ELIM2:
    case PfRule::TRUE_INTRO:
    case PfRule::TRUE_ELIM:
    case PfRule::FALSE_INTRO:
    case PfRule::FALSE_ELIM:
    case PfRule::MODUS_PONENS:
    case PfRule::NOT_NOT_ELIM:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {},
                  *cdp);
      break;
    }
    case PfRule::REFL:
    {
      addLeanStep(
          res,
          LeanRule::REFL,
          d_lnc.convert(res),
          children,
          {},
          *cdp);
      break;
    }
    case PfRule::NOT_OR_ELIM:
    case PfRule::AND_ELIM:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  args,
                  *cdp);
      break;
    }
    case PfRule::CONTRA:
    {
      addLeanStep(res, LeanRule::CONTRADICTION, d_empty, children, {}, *cdp);
      break;
    }
    // minor reasoning to clean args
    case PfRule::TRUST_FLATTENING_REWRITE:
    case PfRule::THEORY_REWRITE:
    case PfRule::EVALUATE:
    {
      d_newRewriteAssumptions.insert(d_lnc.convert(res));
      // Make this an assumption
      cdp->addStep(res, PfRule::ASSUME, {}, {res}, false, CDPOverwrite::ALWAYS);
      break;
    }
    case PfRule::PREPROCESS:
    case PfRule::THEORY_PREPROCESS:
    case PfRule::THEORY_LEMMA:
    case PfRule::TRUST_SUBS:
    case PfRule::TRUST_SUBS_MAP:
    case PfRule::TRUST_SUBS_EQ:
    {
      d_newHoleAssumptions.insert(d_lnc.convert(res));
      // Make this an assumption
      cdp->addStep(res, PfRule::ASSUME, {}, {res}, false, CDPOverwrite::ALWAYS);
      break;
    }
    case PfRule::ARRAYS_READ_OVER_WRITE:
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
    case PfRule::ARRAYS_READ_OVER_WRITE_1:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {},
                  *cdp);
      break;
    }
    // retrieve witness form
    case PfRule::ARRAYS_EXT:
    {
      // The skolem is res[0][0][1]
      Node k = res[0][0][1];
      Node var = SkolemManager::getWitnessForm(k)[0][0];
      Trace("test-lean") << "skolem " << k << " has witness form "
                         << SkolemManager::getWitnessForm(k) << ", its ID is "
                         << var.getId() << "\n";
      // arguments will be the id of the variable and its sort
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {nm->mkConstInt(Rational(var.getId())),
                   nm->mkBoundVar(var.getType().getName(), nm->sExprType())},
                  *cdp);
      break;
    }
    // We handle this as a reflexivity step since the original form of the
    // skolem at res[0] is res[1]
    case PfRule::SKOLEM_INTRO:
    {
      AlwaysAssert(res[1] == SkolemManager::getOriginalForm(res[0]));
      Trace("test-lean") << "skolem " << res[0] << ", kind " << res[0].getKind()
                         << ", has original form "
                         << SkolemManager::getOriginalForm(res[1]) << "\n";
      Node newRes = res[1].eqNode(res[1]);
      addLeanStep(res, LeanRule::REFL, d_lnc.convert(newRes), {}, {}, *cdp);
      break;
    }
    case PfRule::REMOVE_TERM_FORMULA_AXIOM:
    {
      AlwaysAssert(res.getKind() == kind::ITE)
          << "Only support removal of ITEs\n";
      addLeanStep(res, LeanRule::ITE_INTRO, d_lnc.convert(res), {}, {}, *cdp);
      break;
    }
    // Quantifiers
    case PfRule::INSTANTIATE:
    {
      // We need to stratify the instantiation. For each variable in the bound
      // var list of the quantifier (which is necessarily being instantiated) we
      // will create a step. Only the last is not a partial one.
      //
      // We instantiate from the first variable up.
      Node quant = children[0];
      Node currPremise = quant;
      std::vector<Node> bVars{quant[0].begin(), quant[0].end()};
      std::vector<Node> currInstVars;
      std::vector<Node> currInstTerms;
      // the body of the lambda is the quant body with all the previously
      // instantiated variables replaced by the respective terms
      Node lambdaBody = quant[1];
      size_t i = 0;
      for (size_t size = quant[0].getNumChildren(); i < size - 1; ++i)
      {
        Node currVar = quant[0][i];
        Node currTerm = args[i];
        Node ithBVars =
            nm->mkNode(kind::BOUND_VAR_LIST,
                       std::vector<Node>{bVars.begin() + i + 1, bVars.end()});
        Node currLambda =
            nm->mkNode(kind::LAMBDA,
                       nm->mkNode(kind::BOUND_VAR_LIST, currVar),
                       nm->mkNode(kind::FORALL, ithBVars, lambdaBody));
        // create a unique placeholder for the partial instantiation and add the
        // step
        Node newConclusion = nm->mkNode(kind::SEXPR, quant, currLambda);
        addLeanStep(
            newConclusion,
            LeanRule::INST_FORALL_PARTIAL,
            newConclusion,
            {currPremise},
            {d_lnc.convert(nm->mkNode(kind::SEXPR, currLambda, currTerm))},
            *cdp);
        currPremise = newConclusion;
        // Add the instantiated variable to the substitution and update the
        // lambda body
        currInstVars.push_back(currVar);
        currInstTerms.push_back(currTerm);
        lambdaBody = quant[1].substitute(currInstVars.begin(),
                                         currInstVars.end(),
                                         currInstTerms.begin(),
                                         currInstTerms.end());
      }
      // the last step is such that all but the last variable has been
      // instantiated. The instantiated body will have no free variables but the
      // variable in the lambda
      Node currLambda =
          nm->mkNode(kind::LAMBDA,
                     nm->mkNode(kind::BOUND_VAR_LIST, quant[0][i]),
                     lambdaBody);
      addLeanStep(res,
                  LeanRule::INST_FORALL,
                  d_lnc.convert(res),
                  {currPremise},
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, currLambda, args[i]))},
                  *cdp);
      break;
    }
    case PfRule::SKOLEMIZE:
    {
      // We need to stratify the skolemization. For each variable in the bound
      // var list of the quantifier (which is necessarily being skolemized) we
      // will create a step. Only the last is not a partial one.
      //
      // We skolemize from the first variable up, accumulate the skolemization
      // steps and do a transitivity chain.
      //
      // if the skolemization is of a negated forall, we add a conversion step
      // to work on an existential
      Node quant;
      std::vector<Node> skolemSteps;
      if (children[0].getKind() == kind::EXISTS)
      {
        quant = children[0];
      }
      else
      {
        quant = nm->mkNode(
            kind::EXISTS, children[0][0][0], children[0][0][1].notNode());
        skolemSteps.push_back(children[0].eqNode(quant));
        // Make this an assumption
        d_newHoleAssumptions.insert(d_lnc.convert(skolemSteps.back()));
        cdp->addStep(skolemSteps.back(),
                     PfRule::ASSUME,
                     {},
                     {skolemSteps.back()},
                     false,
                     CDPOverwrite::ALWAYS);
      }
      // the body of the lambda is the quant body with all the previously
      // skolemized variables replaced by the respective epsilon terms
      Node lambdaBody = quant[1];
      std::vector<Node> bVars{quant[0].begin(), quant[0].end()};
      std::vector<Node> currSkoVars;
      std::vector<Node> currSkoEpsilons;
      size_t i = 0;
      for (size_t size = quant[0].getNumChildren(); i < size; ++i)
      {
        Node currVar = quant[0][i];
        Node currLambda;
        if (i < size - 1)
        {
          Node ithBVars =
              nm->mkNode(kind::BOUND_VAR_LIST,
                         std::vector<Node>{bVars.begin() + i + 1, bVars.end()});
          currLambda =
              nm->mkNode(kind::LAMBDA,
                         nm->mkNode(kind::BOUND_VAR_LIST, currVar),
                         nm->mkNode(kind::EXISTS, ithBVars, lambdaBody));
        }
        else
        {
          currLambda = nm->mkNode(kind::LAMBDA,
                                  nm->mkNode(kind::BOUND_VAR_LIST, currVar),
                                  lambdaBody);
        }
        // create a unique placeholder for the partial instantiation and add the
        // step
        Node newConclusion = nm->mkNode(kind::SEXPR, quant, currLambda);
        addLeanStep(newConclusion,
                    LeanRule::SKOLEMIZE_PARTIAL,
                    newConclusion,
                    {},
                    {d_lnc.convert(currLambda)},
                    *cdp);
        skolemSteps.push_back(newConclusion);
        // create the choice for the next round if there is a next round
        if (i == size)
        {
          continue;
        }
        // Map the skolemized variable in the substitution with its epsilon term
        // and update the lambda body
        Node currEpsilon = nm->mkNode(kind::WITNESS,
                                      nm->mkNode(kind::BOUND_VAR_LIST, currVar),
                                      lambdaBody);
        currSkoVars.push_back(currVar);
        currSkoEpsilons.push_back(currEpsilon);
        lambdaBody = quant[1].substitute(currSkoVars.begin(),
                                         currSkoVars.end(),
                                         currSkoEpsilons.begin(),
                                         currSkoEpsilons.end());
      }
      // A chain of the skolemization equalities will give us the skolemized
      // formula. A transitivity chain will equate that to the premise.
      Node equiv = children[0].eqNode(res);
      // build the chain
      buildTransitivyChain(equiv, skolemSteps, cdp);
      // do equality resolution between the premise and the equiv to have the
      // original skolemized formula as the conclusion
      addLeanStep(res,
                  LeanRule::EQ_RESOLVE,
                  d_lnc.convert(res),
                  {children[0], equiv},
                  {},
                  *cdp);
      break;
    }
    // Arith
    case PfRule::ARITH_MULT_POS:
    case PfRule::ARITH_MULT_NEG:
    {
      Assert(args.size() == 2);
      Node op = args[1];
      uint32_t typeId;
      switch (op.getKind())
      {
        case Kind::LT:     typeId = 0; break;
        case Kind::LEQ:    typeId = 1; break;
        case Kind::GT:     typeId = 2; break;
        case Kind::GEQ:    typeId = 3; break;
        case Kind::EQUAL:  typeId = 4; break;
        /* unknown operator in arithMultPos/Neg (throw?) */
        default:
        {
          Unreachable() << "Unexpected operator kind in "
                        << s_pfRuleToLeanRule.at(id) << "\n";
          typeId = -1;
          break;
        }
      }
      Node m = args[0];
      Node l = args[1][0];
      Node r = args[1][1];
      Node argsList =
        nm->mkNode(kind::SEXPR, l, r, m);
      std::vector<Node> newArgs { d_lnc.convert(argsList),
                                  nm->mkConstInt(Rational(typeId)) };
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  newArgs,
                  *cdp);
      break;
    }
    case PfRule::ARITH_SUM_UB:
    case PfRule::INT_TIGHT_UB:
    case PfRule::INT_TIGHT_LB:
    {
      std::vector<Node> newArgs;
      for (const Node& a : args)
      {
        newArgs.push_back(d_lnc.convert(a));
      }
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  newArgs,
                  *cdp);
      break;
    }
    case PfRule::ARITH_TRICHOTOMY:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {},
                  *cdp);
      break;
    }
    // BV
    case PfRule::BV_BITBLAST_STEP:
    {
      Kind k = res[0].getKind();
      switch (k)
      {
        case kind::CONST_BITVECTOR:
        {
          addLeanStep(
              res, LeanRule::BITBLAST_VAL, d_lnc.convert(res), {}, {}, *cdp);
          break;
        }
        case kind::VARIABLE:
        case kind::SKOLEM:
        {
          addLeanStep(res,
                      LeanRule::BITBLAST_VAR,
                      d_lnc.convert(res),
                      {},
                      // the size of the bv is the number of children of the
                      // bitblasted term
                      {nm->mkConstInt(Rational(res[1].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_ULT:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          // if one of the bitblasted terms is the resulting of bitblasting a
          // constant, the rule is different. This is because cvc5 hardcodes
          // simplifications during the bitblasting (like conjunction with
          // Boolean constants, equalities with Boolean constants being
          // eliminated etc). A bitblasted term is the result of bitblasting a
          // constant if its children are Boolean constants.
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(
              res,
              hasValue ? LeanRule::BITBLAST_ULT_VAL : LeanRule::BITBLAST_ULT,
              d_lnc.convert(res),
              {},
              // the size of the bv is the number of children of the
              // bitblasted term
              {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
              *cdp);
          break;
        }
        case kind::EQUAL:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(
              res,
              hasValue ? LeanRule::BITBLAST_EQ_VAL : LeanRule::BITBLAST_EQ,
              d_lnc.convert(res),
              {},
              {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
              *cdp);
          break;
        }
        case kind::BITVECTOR_AND:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(
              res,
              hasValue ? LeanRule::BITBLAST_AND_VAL : LeanRule::BITBLAST_AND,
              d_lnc.convert(res),
              {},
              {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
              *cdp);
          break;
        }
        case kind::BITVECTOR_ADD:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          addLeanStep(res,
                      LeanRule::BITBLAST_ADD,
                      d_lnc.convert(res),
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_CONCAT:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          addLeanStep(res,
                      LeanRule::BITBLAST_CONCAT,
                      d_lnc.convert(res),
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren())),
                       nm->mkConstInt(Rational(res[0][1].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_EXTRACT:
        {
          // argument must be a bitblasted term
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM);
          std::vector<Node> newArgs{
              nm->mkConstInt(Rational(res[0][0].getNumChildren()))};
          addLeanStep(res,
                      LeanRule::BITBLAST_EXTRACT,
                      d_lnc.convert(res),
                      {},
                      newArgs,
                      *cdp);
          break;
        }
        default:
        {
          Trace("test-lean") << "unhandled bitblasting kind " << k << "\n";
          addLeanStep(res, LeanRule::UNKNOWN, d_empty, children, args, *cdp);
        }
      }
      break;
    }
    case PfRule::NOT_AND:
    {
      // build as an argument a list of the literals in the conjunction, i.e.,
      // the children the AND under the NOT in the premise
      Assert(children.size() == 1 && children[0].getKind() == kind::NOT
             && children[0][0].getKind() == kind::AND);
      std::vector<Node> lits{children[0][0].begin(), children[0][0].end()};
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, lits))},
                  *cdp);
      break;
    }
    case PfRule::CNF_IMPLIES_POS:
    case PfRule::CNF_IMPLIES_NEG1:
    case PfRule::CNF_IMPLIES_NEG2:
    case PfRule::CNF_EQUIV_POS1:
    case PfRule::CNF_EQUIV_POS2:
    case PfRule::CNF_EQUIV_NEG1:
    case PfRule::CNF_EQUIV_NEG2:
    case PfRule::CNF_XOR_POS1:
    case PfRule::CNF_XOR_POS2:
    case PfRule::CNF_XOR_NEG1:
    case PfRule::CNF_XOR_NEG2:
    case PfRule::CNF_ITE_POS1:
    case PfRule::CNF_ITE_POS2:
    case PfRule::CNF_ITE_POS3:
    case PfRule::CNF_ITE_NEG1:
    case PfRule::CNF_ITE_NEG2:
    case PfRule::CNF_ITE_NEG3:
    case PfRule::EQUIV_ELIM1:
    case PfRule::EQUIV_ELIM2:
    case PfRule::NOT_EQUIV_ELIM1:
    case PfRule::NOT_EQUIV_ELIM2:
    case PfRule::XOR_ELIM1:
    case PfRule::XOR_ELIM2:
    case PfRule::NOT_XOR_ELIM1:
    case PfRule::NOT_XOR_ELIM2:
    case PfRule::ITE_ELIM1:
    case PfRule::ITE_ELIM2:
    case PfRule::NOT_ITE_ELIM1:
    case PfRule::NOT_ITE_ELIM2:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  children,
                  {},
                  *cdp);
      break;
    }
    // minor reasoning to pick the rule
    case PfRule::SYMM:
    {
      addLeanStep(
          res,
          res.getKind() == kind::EQUAL ? LeanRule::SYMM : LeanRule::NEG_SYMM,
          d_lnc.convert(res),
          children,
          {},
          *cdp);
      break;
    }
    //-------------- bigger conversions
    case PfRule::HO_CONG:
    {
      Unreachable() << "Higher-order congruence not supported yet\n";
      break;
    }
    // break down CONG chain
    case PfRule::CONG:
    {
      Kind k = res[0].getKind();
      if (res[0].isClosure())
      {
        // For now no proper support
        d_newHoleAssumptions.insert(d_lnc.convert(res));
        // Make this an assumption
        cdp->addStep(
            res, PfRule::ASSUME, {}, {res}, false, CDPOverwrite::ALWAYS);
        break;
      }
      size_t nchildren = children.size();
      Node eqNode = ProofRuleChecker::mkKindNode(kind::EQUAL);
      // We have a hard coded handling of ITE
      if (k == kind::ITE)
      {
        addLeanStep(
            res, LeanRule::CONG_ITE, d_lnc.convert(res), children, {}, *cdp);
        break;
      }
      Node op, opConverted;
      op = args.size() == 2 ? args[1] : args[0];
      opConverted = d_lnc.mkPrintableOp(op);
      // Are we doing congruence of an n-ary operator with more than two
      // arguments? If so, notice that op is a binary operator and we must apply
      // congruence in a special way.
      //
      // special case: some kinds are n-ary but expect operators which are not,
      // so we handle them in a regular manner below
      bool isNary = NodeManager::isNAryKind(k) && k != kind::APPLY_UF
                    && k != kind::APPLY_CONSTRUCTOR && k != kind::APPLY_SELECTOR
                    && k != kind::APPLY_TESTER;
      if (isNary && nchildren > 2)
      {
        if (k == kind::ADD)
        {
          // state equality between the addition of the last two children
          Node addLefts = nm->mkNode(kind::SEXPR,
                                     op,
                                     children[nchildren - 2][0],
                                     children[nchildren - 1][0]);
          Node addRights = nm->mkNode(kind::SEXPR,
                                      op,
                                      children[nchildren - 2][1],
                                      children[nchildren - 1][1]);
          Node currEq = nm->mkNode(kind::SEXPR, eqNode, addLefts, addRights);
          addLeanStep(currEq,
                      LeanRule::CONG_ADD_PARTIAL,
                      d_empty,
                      {children[nchildren - 2], children[nchildren - 1]},
                      {},
                      *cdp);
          // use cong_add to derive equality between the addition of each
          // children and what is accumulated in currEq
          for (size_t i = 2; i < nchildren; ++i)
          {
            size_t j = nchildren - i - 1;
            if (j == 0)
            {
              addLeanStep(res,
                          LeanRule::CONG_ADD,
                          d_lnc.convert(res),
                          {children[j], currEq},
                          {},
                          *cdp);
            }
            else
            {
              Node add1 = nm->mkNode(kind::SEXPR, op, children[j][0], currEq[0]);
              Node add2 = nm->mkNode(kind::SEXPR, op, children[j][1], currEq[1]);
              Node nxtEq = nm->mkNode(kind::SEXPR, eqNode, add1, add2);
              addLeanStep(nxtEq,
                          LeanRule::CONG_ADD_PARTIAL,
                          d_empty,
                          {children[j], currEq},
                          {},
                          *cdp);
              currEq = nxtEq;
            }
          }
          break;
        }
        // add internal refl step for operator. For now not using congrArg in this case
        Node opEq = nm->mkNode(kind::SEXPR,
                               d_lnc.mkPrintableOp(kind::EQUAL),
                               opConverted,
                               opConverted);
        addLeanStep(opEq, LeanRule::REFL, opEq, {}, {}, *cdp);
        // start with the last argument
        Node currEq = children[nchildren - 1];
        for (size_t i = 1; i < nchildren; ++i)
        {
          size_t j = nchildren - i - 1;
          // build equality of partial apps of argument j. We add the index as
          // part of the node to guarantee that there is no ambiguity with
          // applications that have repeated arguments
          std::vector<Node> argAppEqChildren{
              eqNode,
              nm->mkConstInt(Rational(i)),
              nm->mkNode(kind::SEXPR, op, children[j][0]),
              nm->mkNode(kind::SEXPR, op, children[j][1])};
          Node argAppEq = nm->mkNode(kind::SEXPR, argAppEqChildren);
          // add step that justify equality of partial apps
          addLeanStep(argAppEq,
                      LeanRule::CONG_PARTIAL,
                      d_empty,
                      {opEq, children[j]},
                      {},
                      *cdp);
          // last case, we add a CONG step to the original conclusion
          if (j == 0)
          {
            addLeanStep(res,
                        LeanRule::CONG,
                        d_lnc.convert(res),
                        {argAppEq, currEq},
                        {},
                        *cdp);
          }
          else
          {
            // build equality of full app with argument j and previous equality
            // in chain
            Node nextEq =
                nm->mkNode(kind::SEXPR,
                           eqNode,
                           nm->mkNode(kind::SEXPR, argAppEq, currEq[0]),
                           nm->mkNode(kind::SEXPR, argAppEq, currEq[1]));
            addLeanStep(nextEq,
                        LeanRule::CONG_PARTIAL,
                        d_empty,
                        {argAppEq, currEq},
                        {},
                        *cdp);
            currEq = nextEq;
          }
        }
        break;
      }
      // regular congruence over non-nary, non-closures
      //
      // add internal steps
      Node curL = op;
      Node curR = op;
      // The first step is a CONG_ARG, taking the operator as an argument and a
      // single premise. If there is only one children, this is the only step
      if (nchildren == 1)
      {
        addLeanStep(res,
                    LeanRule::CONG_ARG,
                    d_lnc.convert(res),
                    {children[0]},
                    {d_lnc.convert(nm->mkNode(kind::SEXPR, opConverted))},
                    *cdp);
        break;
      }
      Node currEq = nm->mkNode(kind::SEXPR, eqNode, curL, curR);
      addLeanStep(currEq,
                  LeanRule::CONG_ARG_PARTIAL,
                  d_empty,
                  {children[0]},
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, opConverted))},
                  *cdp);
      for (size_t i = 1; i < nchildren - 1; ++i)
      {
        curL = nm->mkNode(kind::SEXPR, currEq, children[i][0]);
        curR = nm->mkNode(kind::SEXPR, currEq, children[i][0]);
        Node nextEq = nm->mkNode(kind::SEXPR, eqNode, curL, curR);
        addLeanStep(nextEq,
                    LeanRule::CONG_PARTIAL,
                    d_empty,
                    {currEq, children[i]},
                    {},
                    *cdp);
        Trace("test-lean") << "..cong internal: " << nextEq << " from "
                           << currEq << ", " << children[i] << "\n";
        currEq = nextEq;
      }
      addLeanStep(res,
                  LeanRule::CONG,
                  d_lnc.convert(res),
                  {currEq, children.back()},
                  {},
                  *cdp);
      break;
    }
    case PfRule::TRANS:
    {
      buildTransitivyChain(res, children, cdp);
      break;
    }
    case PfRule::AND_INTRO:
    {
      size_t size = children.size();
      Node cur = children[size - 1], first = children[0];
      for (size_t i = 1; i < size - 1; ++i)
      {
        size_t j = size - i - 1;
        Node newCur = nm->mkNode(kind::AND, children[j], cur);
        addLeanStep(newCur,
                    LeanRule::AND_INTRO_PARTIAL,
                    d_empty,
                    {
                        children[j],
                        cur,
                    },
                    {},
                    *cdp);
        cur = newCur;
      }
      addLeanStep(
          res, LeanRule::AND_INTRO, d_lnc.convert(res), {first, cur}, {}, *cdp);
      break;
    }
    //-------- clausal rules
    case PfRule::RESOLUTION:
    case PfRule::CHAIN_RESOLUTION:
    {
      Trace("test-lean") << push;
      Node cur = children[0], curLastLit;
      Node minusOne = nm->mkConstInt(Rational(-1)),
           zero = nm->mkConstInt(Rational(0));
      size_t numCurLits = 0;
      std::vector<Node> singletons{minusOne, minusOne};
      std::vector<bool> ithPremiseSingleton(children.size());
      // Whether child 0 is a singleton list. The first child is used as an OR
      // non-singleton clause if it is not equal to its pivot L_1. Since it's
      // the first clause in the resolution it can only be equal to the pivot in
      // the case the polarity is true.
      Trace("test-lean") << "\t\ttesting args[0,1] " << args[0] << ", "
                         << args[1] << ", child 0 " << children[0] << "\n";
      if (children[0].getKind() != kind::OR
          || (args[0] == d_true && children[0] == args[1]))
      {
        singletons[0] = zero;
        curLastLit = children[0];
        numCurLits = 1;
        ithPremiseSingleton[0] = true;
      }
      else
      {
        ithPremiseSingleton[0] = false;
        numCurLits = children[0].getNumChildren();
        curLastLit = children[0][numCurLits - 1];
        if (curLastLit.getKind() == kind::OR)
        {
          singletons[0] = nm->mkConstInt(Rational(numCurLits - 1));
        }
      }
      // For all other children C_i the procedure is simliar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a [(or F1 ... Fn)] node. The same is
      // true if it isn't the pivot element.
      for (size_t i = 1, size = children.size(); i < size; ++i)
      {
        Trace("test-lean") << "\t\ttesting args[" << 2 * (i - 1) << ","
                           << 2 * (i - 1) + 1 << "] " << args[2 * (i - 1)]
                           << ", " << args[2 * (i - 1) + 1] << ", child " << i
                           << " " << children[i] << "\n";
        singletons[1] = getSingletonPosition(children[i], i, args);
        ithPremiseSingleton[i] = singletons[1] == zero;
        if (i < size - 1)
        {
          // create a (unique) placeholder for the resulting binary
          // resolution. The placeholder is [res, i, pol, pivot], where pol and
          // pivot are relative to this part of the chain resolution
          Node pol = args[(i - 1) * 2];
          std::vector<Node> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
                                    d_lnc.mkList(singletons)};
          std::vector<Node> curChildren{
              res, nm->mkConstInt(Rational(i)), pol, curArgs[0]};
          Node newCur = nm->mkNode(kind::SEXPR, curChildren);
          Trace("test-lean")
              << "..res [internal] " << i << " has singleton premises "
              << singletons << "\n";
          addLeanStep(newCur,
                      pol.getConst<bool>() ? LeanRule::R0_PARTIAL
                                           : LeanRule::R1_PARTIAL,
                      d_empty,
                      {cur, children[i]},
                      curArgs,
                      *cdp);
          cur = newCur;
          size_t pivotIndex = 2 * (i - 1);
          // if the second premise is singleton, the new last current literal
          // will be:
          // - if the current last lit is not the pivot, it'll be the new last
          // - otherwise it'll be the first non-pivot literal in a previous
          // premise
          if (ithPremiseSingleton[i])
          {
            // Note that since this is an internal resolution we cannot have
            // that both premises are singletons
            Assert(numCurLits > 1);
            // we only update if curLastLit cannot remain the same
            if (curLastLit
                == (args[pivotIndex] == d_true
                        ? args[pivotIndex + 1]
                        : args[pivotIndex + 1].notNode()))
            {
              // search in a previous premise for the last current literal. For
              // each j-th previous premise, we look, from last to first, at the
              // literals that are different from the polarity (j-1)-th pivot
              // and the !polarity (j-2)-th pivot. We ignore singleton premises
              size_t j;
              for (j = i; j > 0; --j)
              {
                if (ithPremiseSingleton[j - 1])
                {
                  continue;
                }
                uint64_t curPivotIndex, prevPivotIndex;
                Node curPivot, prevPivot, diffLit;
                curPivotIndex = 2 * (j - 1);
                curPivot = args[curPivotIndex] == d_true
                               ? args[curPivotIndex]
                               : args[curPivotIndex].notNode();
                // we also exclude the previous res pivot if there was one,
                // which is always the case except for the first premise
                if (j > 1)
                {
                  prevPivotIndex = 2 * (j - 2);
                  prevPivot = args[prevPivotIndex] == d_true
                                  ? args[prevPivotIndex].notNode()
                                  : args[prevPivotIndex];
                  diffLit = getLastDiffs(children[j - 1], curPivot, prevPivot);
                }
                else
                {
                  diffLit = getLastDiff(children[j - 1], curPivot);
                }
                if (!diffLit.isNull())
                {
                  curLastLit = diffLit;
                  break;
                }
              }
            }
          }
          else
          {
            curLastLit = getLastDiff(children[i],
                                     args[pivotIndex] == d_true
                                         ? args[pivotIndex + 1].notNode()
                                         : args[pivotIndex + 1]);
          }
          // The number of literals in working clause is what we had before,
          // plus the literals in the new premise, minus the two literals
          // removed from it and the new premise.
          numCurLits =
              numCurLits
              + (ithPremiseSingleton[i] ? 1 : children[i].getNumChildren()) - 2;
          // if the number of current literals is one, then singletons[0] == 0,
          // otherwise it's != -1 if its last current literal is an OR,
          // otherwise it's -1
          singletons[0] = numCurLits == 1
                              ? zero
                              : (curLastLit.getKind() == kind::OR
                                     ? nm->mkConstInt(Rational(numCurLits - 1))
                                     : minusOne);
          // reset next child to be computed whether singleton
          singletons[1] = minusOne;
        }
      }
      size_t i = children.size() - 1;
      Trace("test-lean") << "..res [final] " << i << " has singleton premises "
                         << singletons << "\n";
      std::vector<Node> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
                                d_lnc.mkList(singletons)};
      addLeanStep(
          res,
          args[(i - 1) * 2].getConst<bool>() ? LeanRule::R0 : LeanRule::R1,
          d_lnc.convert(res),
          {cur, children.back()},
          curArgs,
          *cdp);
      Trace("test-lean") << pop;
      break;
    }
    case PfRule::REORDERING:
    {
      Assert(res.getNumChildren() == children[0].getNumChildren());
      size_t size = res.getNumChildren();
      Node singleton = nm->mkConstInt(Rational(
          children[0][size - 1].getKind() == kind::OR ? int(size - 1) : (-1)));
      // for each literal in the resulting clause, get its position in the
      // premise
      std::vector<Node> pos;

      for (const Node& resLit : res)
      {
        for (size_t i = 0; i < size; ++i)
        {
          if (children[0][i] == resLit)
          {
            // don't convert the numbers since naturals should be
            // printed as is
            pos.push_back(nm->mkConstInt(Rational(i)));
          }
        }
      }
      // turn conclusion into clause
      addLeanStep(res,
                  LeanRule::REORDER,
                  d_lnc.convert(res),
                  children,
                  {d_lnc.mkList(pos), singleton},
                  *cdp);
      break;
    }
    case PfRule::FACTORING:
    {
      // as an argument we pass whether the suffix of the factoring clause is a
      // singleton *repeated* literal. This is marked by a number as in
      // resolution.
      Node singleton,
          lastPremiseLit = children[0][children[0].getNumChildren() - 1];
      // For the last premise literal to be a singleton repeated literal, either
      // it is equal to the result (in which case the premise was just n
      // occurrences of it), or the end of the original clause is different from
      // the end of the resulting one. In principle we'd need to add the
      // singleton information only for OR nodes, so we could avoid this test if
      // the result is not an OR node. However given the presence of
      // purification boolean variables which can stand for OR nodes (and could
      // thus be ambiguous in the final step, with the purification remove), we
      // do the general test.
      if (lastPremiseLit == res
          || (res.getKind() == kind::OR
              && lastPremiseLit != res[res.getNumChildren() - 1]))
      {
        // last lit must be repeated
        Assert(std::find(children[0].begin(), children[0].end(), lastPremiseLit)
               != children[0].end());
        singleton = nm->mkConstInt(Rational(children[0].getNumChildren() - 1));
      }
      else
      {
        singleton = nm->mkConstInt(Rational(- 1));
      }
      addLeanStep(
          res, LeanRule::FACTORING, d_lnc.convert(res), children, {singleton}, *cdp);
      break;
    }
    case PfRule::CNF_AND_POS:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_AND_POS,
                  d_lnc.convert(res),
                  children,
                  // don't convert second argument since naturals should be
                  // printed as is
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs)), args[1]},
                  *cdp);
      break;
    }
    case PfRule::CNF_AND_NEG:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_AND_NEG,
                  d_lnc.convert(res),
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs))},
                  *cdp);
      break;
    }
    case PfRule::CNF_OR_POS:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_OR_POS,
                  d_lnc.convert(res),
                  children,
                  // don't convert second argument since naturals should be
                  // printed as is
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs))},
                  *cdp);
      break;
    }
    case PfRule::CNF_OR_NEG:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_OR_NEG,
                  d_lnc.convert(res),
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs)), args[1]},
                  *cdp);
      break;
    }
    default:
    {
      Trace("test-lean") << "Unhandled rule " << id << "\n";
      std::stringstream ss;
      ss << id;
      Node newVar = nm->mkBoundVar(ss.str(), nm->sExprType());
      std::vector<Node> newArgs{newVar};
      newArgs.insert(newArgs.end(), args.begin(), args.end());
      addLeanStep(res, LeanRule::UNKNOWN, d_empty, children, newArgs, *cdp);
    }
  };
  return true;
}

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
  updater.process(pf);
  // The resulting proof is the one under the original scope.  Since our
  // processing of scope converts it into two rules (scope and
  // lifnOrNToImp/lifnOrNToNeg), we wil exclude this outer one. Furthermore, we
  // will add new assumptions as arguments of that scope. This is done by
  // rebuilding the proof node but with different arguments. We do not care
  // about the original conclusion, so this is fine
  CDProof cdp(
      d_env, nullptr, "LeanProofPostprocess::CDProofForNewAssumptions", false);
  std::shared_ptr<ProofNode> scopePf = pf->getChildren()[0];
  Node res = pf->getResult();
  const std::vector<std::shared_ptr<ProofNode>>& childrenPfs =
      scopePf->getChildren();
  Assert(childrenPfs.size() == 1);
  cdp.addProof(childrenPfs[0]);
  const std::vector<Node> args = scopePf->getArguments();
  std::vector<Node> newArgs{args[0], args[1], args[2]};
  NodeManager* nm = NodeManager::currentNM();
  newArgs.push_back(nm->mkConstInt(Rational(d_cb->d_newHoleAssumptions.size())));
  Trace("test")
      << newArgs.back().getConst<Rational>().getNumerator().toUnsignedInt()
      << "\n";
  for (const Node& a : d_cb->d_newHoleAssumptions)
  {
    newArgs.push_back(a);
  }
  newArgs.push_back(nm->mkConstInt(Rational(d_cb->d_newRewriteAssumptions.size())));
  Trace("test")
      << newArgs.back().getConst<Rational>().getNumerator().toUnsignedInt()
      << "\n";
  for (const Node& a : d_cb->d_newRewriteAssumptions)
  {
    newArgs.push_back(a);
  }
  newArgs.insert(newArgs.end(), args.begin() + 3, args.end());
  cdp.addStep(res, PfRule::LEAN_RULE, {childrenPfs[0]->getResult()}, newArgs);
  d_env.getProofNodeManager()->updateNode(pf.get(), cdp.getProofFor(res).get());
};

}  // namespace proof
}  // namespace cvc5::internal
