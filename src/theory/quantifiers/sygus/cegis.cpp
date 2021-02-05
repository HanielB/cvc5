/*********************                                                        */
/*! \file cegis.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cegis
 **/

#include "theory/quantifiers/sygus/cegis.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/sygus/example_min_eval.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Cegis::Cegis(QuantifiersEngine* qe, SynthConjecture* p)
    : SygusModule(qe, p),
      d_eval_unfold(nullptr),
      d_usingSymCons(false),
      d_usingSymConsGround(false)
{
  d_eval_unfold = qe->getTermDatabaseSygus()->getEvalUnfold();
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool Cegis::initialize(Node conj,
                       Node n,
                       const std::vector<Node>& candidates,
                       std::vector<Node>& lemmas)
{
  d_base_body = n;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
    }
    d_base_body = d_base_body[0][1];
  }

  // assign the cegis sampler if applicable
  if (options::cegisSample() != options::CegisSampleMode::NONE)
  {
    Trace("cegis-sample") << "Initialize sampler for " << d_base_body << "..."
                          << std::endl;
    TypeNode bt = d_base_body.getType();
    d_cegis_sampler.initialize(bt, d_base_vars, options::sygusSamples());
  }
  return processInitialize(conj, n, candidates, lemmas);
}

bool Cegis::processInitialize(Node conj,
                              Node n,
                              const std::vector<Node>& candidates,
                              std::vector<Node>& lemmas)
{
  Trace("cegis") << "Initialize cegis..." << std::endl;
  unsigned csize = candidates.size();
  // The role of enumerators is to be either the single solution or part of
  // a solution involving multiple enumerators.
  EnumeratorRole erole =
      csize == 1 ? ROLE_ENUM_SINGLE_SOLUTION : ROLE_ENUM_MULTI_SOLUTION;
  // initialize an enumerator for each candidate
  std::vector<bool> hasAnyConst(csize, false);
  for (unsigned i = 0; i < csize; i++)
  {
    Trace("cegis") << "...register enumerator " << candidates[i];
    // We use symbolic constants if we are doing repair constants or if the
    // grammar construction was not simple.
    if (options::sygusRepairConstMode() != options::SygusRepairConstMode::NONE
        || options::sygusGrammarConsMode()
               != options::SygusGrammarConsMode::SIMPLE)
    {
      TypeNode ctn = candidates[i].getType();
      d_tds->registerSygusType(ctn);
      SygusTypeInfo& cti = d_tds->getTypeInfo(ctn);
      if (cti.hasSubtermSymbolicCons())
      {
        // remember that we are using symbolic constructors
        d_usingSymCons = true;
        // mark the candidate that is using it
        hasAnyConst[i] = true;
        Trace("cegis") << " (using symbolic constructors)";
      }
    }
    if (options::sygusRepairConstMode() == options::SygusRepairConstMode::ENUM
        && d_usingSymCons && d_parent->isGround())
    {
      d_usingSymConsGround = true;
      Trace("cegis") << " with ground conjecture and eval unfold handling.";
    }
    Trace("cegis") << std::endl;
    d_tds->registerEnumerator(candidates[i], candidates[i], d_parent, erole);
  }
  // collect all applications of function-to-sythesize. Each will be an
  // application head. Also have the points

  if (d_usingSymConsGround)
  {
    std::map<Node, Node> cache;
    // get candidates that symbolic constants in their sygus type
    std::vector<Node> symbCandidates;
    for (unsigned i = 0; i < csize; ++i)
    {
      if (hasAnyConst[i])
      {
        symbCandidates.push_back(candidates[i]);
      }
    }
    Node pConj = purifyLemma(n, symbCandidates, false, cache);
    if (Trace.isOn("cegis"))
    {
      Trace("cegis") << "Symbolic candidates:\n";
      for (const auto& cand : symbCandidates)
      {
        Trace("cegis") << "...candidate: " << cand << "\n";
        for (const auto& hd : d_candToEvalHds[cand])
        {
          Trace("cegis") << "......hd: " << hd << ", " << d_hdToPt[hd] << "\n";
        }
      }
    }
    // could not purify
    if (pConj.isNull())
    {
      d_usingSymConsGround = false;
    }
    else
    {
      pConj = Rewriter::rewrite(pConj.negate());
      Trace("cegis") << "groundSymConst::purified conjecture : " << pConj
                     << "\n";
      d_purifiedLemma = pConj;
      lemmas.push_back(pConj);
      // save original conjecture (negation of given one) as refinement lemma
      addRefinementLemma(d_tds->getExtRewriter()->extendedRewrite(n.negate()));
    }
  }
  return true;
}

Node Cegis::purifyLemma(Node n,
                        const std::vector<Node>& candidates,
                        bool ensureConst,
                        std::map<Node, Node>& cache)
{
  Trace("cegis-purify") << "PurifyLemma : " << n << "\n";
  std::map<Node, Node>::const_iterator it0 = cache.find(n);
  if (it0 != cache.end())
  {
    Trace("cegis-purify-debug") << "... already visited " << n << "\n";
    return it0->second;
  }
  // Recurse
  unsigned size = n.getNumChildren();
  Kind k = n.getKind();
  // We retrive model value now because purified node may not have a value
  Node nv = n;
  // Whether application of a function-to-synthesize
  bool fapp = k == kind::DT_SYGUS_EVAL;
  bool acFapp = false;
  if (fapp)
  {
    // if we are ensuring constants, we cannot do it for function applications,
    // so we give up
    if (ensureConst)
    {
      return Node::null();
    }
    // Whether application of a anyConst function-to-synthesize
    acFapp = std::find(candidates.begin(), candidates.end(), n[0])
             != candidates.end();
  }
  // Travese to purify
  bool childChanged = false;
  std::vector<Node> children;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0; i < size; ++i)
  {
    if (i == 0 && fapp)
    {
      children.push_back(n[i]);
      continue;
    }
    // Arguments of anyConst functions need to be constant
    Node child = purifyLemma(n[i], candidates, ensureConst || acFapp, cache);
    if (child.isNull())
    {
      return Node::null();
    }
    children.push_back(child);
    childChanged = childChanged || child != n[i];
  }
  Node nb;
  if (childChanged)
  {
    AlwaysAssert(!acFapp);
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      Trace("cegis-purify-debug") << "Node " << n << " is parameterized\n";
      children.insert(children.begin(), n.getOperator());
    }
    if (Trace.isOn("cegis-purify-debug"))
    {
      Trace("cegis-purify-debug")
          << "...rebuilding " << n << " with kind " << k << " and children:\n";
      for (const Node& child : children)
      {
        Trace("cegis-purify-debug") << "...... " << child << "\n";
      }
    }
    nb = NodeManager::currentNM()->mkNode(k, children);
    Trace("cegis-purify") << "PurifyLemma : transformed " << n << " into " << nb
                          << "\n";
  }
  else
  {
    nb = n;
  }
  // Map to point enumerator every unification function-to-synthesize
  if (acFapp)
  {
    Node np;
    // Build purified head with fresh skolem, of the builtin type, and replace
    std::stringstream ss;
    ss << nb[0] << "_" << d_candToHdCount[nb[0]]++;
    TypeNode ctn = nb[0].getType();
    SygusTypeInfo& cti = d_tds->getTypeInfo(ctn);

    Node newF = nm->mkSkolem(ss.str(),
                              cti.getBuiltinType(),
                              "head of anyConst synth-fun app",
                              NodeManager::SKOLEM_EXACT_NAME);
    // Adds new enumerator to map from candidate
    Trace("cegis-purify") << "...new enum " << newF << " for candidate "
                          << nb[0] << "\n";
    d_candToEvalHds[nb[0]].push_back(newF);
    Assert(d_evalToHd.find(n) == d_evalToHd.end());
    d_evalToHd[n] = newF;
    // Maps new enumerator to its respective tuple of arguments
    d_hdToPt[newF] = std::vector<Node>(++children.begin(), children.end());
    if (Trace.isOn("cegis-purify-debug"))
    {
      Trace("cegis-purify-debug") << "...[" << newF << "] --> ( ";
      for (const Node& pt_i : d_hdToPt[newF])
      {
        Trace("cegis-purify-debug") << pt_i << " ";
      }
      Trace("cegis-purify-debug") << ")\n";
    }
    // replace original fApp by newF skolem
    Trace("cegis-purify") << "PurifyLemma : purified head and transformed "
                          << nb << " into " << newF << "\n";
    nb = newF;
  }
  nb = Rewriter::rewrite(nb);
  // everything under an anyConst of function-to-synthesize app must be reduced
  // to a concrete constant
  Assert(!ensureConst || nb.isConst());
  Trace("cegis-purify-debug") << "... caching [" << n << "] = " << nb << "\n";
  cache[n] = nb;
  return nb;
}

void Cegis::getRelCandidateHds(Node n, std::map<Node, std::vector<Node>>& relCandHds)
{
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> visit{n};
  Node cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.count(cur))
    {
      continue;
    }
    visited.insert(cur);
    if (cur.getKind() == kind::DT_SYGUS_EVAL)
    {
      auto it = d_evalToHd.find(cur);
      if (it != d_evalToHd.end())
      {
        relCandHds[cur[0]].push_back(it->second);
        // candidates is applied over constants, can ignore children
        continue;
      }
    }
    for (const auto& child : cur)
    {
      visit.push_back(child);
    }
  }while (!visit.empty());
}

void Cegis::getTermList(const std::vector<Node>& candidates,
                        std::vector<Node>& enums)
{
  enums.insert(enums.end(), candidates.begin(), candidates.end());
}

bool Cegis::addEvalLemmas(const std::vector<Node>& candidates,
                          const std::vector<Node>& candidate_values,
                          std::vector<Node>& lems)
{
  // First, decide if this call will apply "conjecture-specific refinement".
  // In other words, in some settings, the following method will identify and
  // block a class of solutions {candidates -> S} that generalizes the current
  // one (given by {candidates -> candidate_values}), such that for each
  // candidate_values' in S, we have that {candidates -> candidate_values'} is
  // also not a solution for the given conjecture. We may not
  // apply this form of refinement if any (relevant) enumerator in candidates is
  // "actively generated" (see TermDbSygs::isPassiveEnumerator), since its
  // model values are themselves interpreted as classes of solutions.
  bool doGen = true;
  for (const Node& v : candidates)
  {
    // if it is relevant to refinement
    if (d_refinement_lemma_vars.find(v) != d_refinement_lemma_vars.end())
    {
      if (!d_tds->isPassiveEnumerator(v))
      {
        doGen = false;
        break;
      }
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  bool addedEvalLemmas = false;
  // Refinement evaluation should not be done for grammars with symbolic
  // constructors, unless the conjecture is ground
  if (!d_usingSymCons || d_usingSymConsGround)
  {
    Trace("sygus-engine") << "  *** Do refinement lemma evaluation"
                          << (doGen ? " with conjecture-specific refinement"
                                    : "")
                          << "..." << std::endl;
    // see if any refinement lemma is refuted by evaluation
    if (doGen)
    {
      std::vector<Node> cre_lems;
      getRefinementEvalLemmas(candidates, candidate_values, cre_lems);
      if (!cre_lems.empty())
      {
        lems.insert(lems.end(), cre_lems.begin(), cre_lems.end());
        addedEvalLemmas = true;
        if (Trace.isOn("cegqi-lemma"))
        {
          for (const Node& lem : cre_lems)
          {
            Trace("cegqi-lemma")
                << "Cegqi::Lemma : ref evaluation : " << lem << std::endl;
          }
        }
        /* we could, but do not return here. experimentally, it is better to
          add the lemmas below as well, in parallel. */
      }
    }
    else
    {
      // just check whether the refinement lemmas are satisfied, fail if not
      if (checkRefinementEvalLemmas(candidates, candidate_values))
      {
        Trace("sygus-engine") << "...(actively enumerated) candidate failed "
                                 "refinement lemma evaluation."
                              << std::endl;
        return true;
      }
    }
  }
  // we only do evaluation unfolding for passive enumerators and, for now, if we
  // are not handling a ground conjecture with symbolic constants
  bool doEvalUnfold =
      !d_usingSymConsGround
      && ((doGen && options::sygusEvalUnfold()) || d_usingSymCons);
  if (doEvalUnfold)
  {
    Trace("sygus-engine") << "  *** Do evaluation unfolding..." << std::endl;
    std::vector<Node> eager_terms, eager_vals, eager_exps;
    for (unsigned i = 0, size = candidates.size(); i < size; ++i)
    {
      Trace("cegqi-debug") << "  register " << candidates[i] << " -> "
                           << candidate_values[i] << std::endl;
      d_eval_unfold->registerModelValue(candidates[i],
                                        candidate_values[i],
                                        eager_terms,
                                        eager_vals,
                                        eager_exps);
    }
    Trace("cegqi-debug") << "...produced " << eager_terms.size()
                         << " evaluation unfold lemmas.\n";
    for (unsigned i = 0, size = eager_terms.size(); i < size; ++i)
    {
      Node lem = nm->mkNode(
          OR, eager_exps[i].negate(), eager_terms[i].eqNode(eager_vals[i]));
      lems.push_back(lem);
      addedEvalLemmas = true;
      Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation unfold : " << lem
                           << std::endl;
    }
  }
  return addedEvalLemmas;
}

Node Cegis::getRefinementLemmaFormula()
  {
  std::vector<Node> conj;
  conj.insert(
      conj.end(), d_refinement_lemmas.begin(), d_refinement_lemmas.end());
  // get the propagated values
  for (unsigned i = 0, nprops = d_rl_eval_hds.size(); i < nprops; i++)
  {
    conj.push_back(d_rl_eval_hds[i].eqNode(d_rl_vals[i]));
  }
  // make the formula
  NodeManager* nm = NodeManager::currentNM();
  Node ret;
  if (conj.empty())
  {
    ret = nm->mkConst(true);
  }
  else
  {
    ret = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
  }
  return ret;
}

bool Cegis::constructCandidates(const std::vector<Node>& enums,
                                const std::vector<Node>& enum_values,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& candidate_values,
                                std::vector<Node>& lems)
{
  if (Trace.isOn("cegis"))
  {
    Trace("cegis") << "  Enumerators :\n";
    for (unsigned i = 0, size = enums.size(); i < size; ++i)
    {
      Trace("cegis") << "    " << enums[i] << " -> ";
      TermDbSygus::toStreamSygus("cegis", enum_values[i]);
      Trace("cegis") << "\n";
      if (d_usingSymConsGround)
      {
        Trace("cegis") << "  ...heads :\n";
        for (const Node& hd : d_candToEvalHds[enums[i]])
        {
          Trace("cegis") << "      " << hd << " -> "
                         << d_parent->getModelValue(hd) << "\n";
        }
      }
    }
  }
  // if we are using a subsolver to repair constants
  if (d_usingSymCons
           && options::sygusRepairConstMode()
                  == options::SygusRepairConstMode::SUBSOLVER)
  {
    SygusRepairConst* src = d_parent->getRepairConst();
    Assert(src != nullptr);
    // check if any enum_values have symbolic terms that must be repaired
    bool mustRepair = false;
    for (const Node& c : enum_values)
    {
      if (SygusRepairConst::mustRepair(c))
      {
        mustRepair = true;
        break;
      }
    }
    Trace("cegis") << "...must repair is: " << mustRepair << std::endl;
    // if the solution contains a subterm that must be repaired
    if (mustRepair)
    {
      std::vector<Node> fail_cvs = enum_values;
      Assert(candidates.size() == fail_cvs.size());
      // try to solve entire problem?
      if (src->repairSolution(candidates, fail_cvs, candidate_values))
      {
        return true;
      }
      Node rl = getRefinementLemmaFormula();
      // try to solve for the refinement lemmas only
      bool ret =
          src->repairSolution(rl, candidates, fail_cvs, candidate_values);
      // Even if ret is true, we will exclude the skeleton as well; this means
      // that we have one chance to repair each skeleton. It is possible however
      // that we might want to repair the same skeleton multiple times.
      std::vector<Node> exp;
      for (unsigned i = 0, size = enums.size(); i < size; i++)
      {
        d_tds->getExplain()->getExplanationForEquality(
            enums[i], enum_values[i], exp);
      }
      Assert(!exp.empty());
      NodeManager* nm = NodeManager::currentNM();
      Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
      // must guard it
      expn = nm->mkNode(OR, d_parent->getGuard().negate(), expn.negate());
      lems.push_back(expn);
      return ret;
    }
  }

  // evaluate on refinement lemmas
  bool addedEvalLemmas = addEvalLemmas(enums, enum_values, lems);

  // if we are in the special case of repairing constants via the enumerator and
  // with a ground conjecture, we generate evaluation unfolding lemmas that
  // determine the values the heads should have when the solution has the
  // current shope, which will guide the enumerator in discarding this candidate
  // or repairing the constants it depends on
  if (d_usingSymConsGround && addedEvalLemmas)
  {
    NodeManager* nm = NodeManager::currentNM();
    Trace("cegis-lemma") << "  EvalLemmas : " << lems << "\n";
    std::map<Node, std::vector<Node>> relCandHds;
    for (const auto& lem : lems)
    {
      auto it = d_refLemmaToRelCandHds.find(lem);
      // compute applications and add to map
      if (it == d_refLemmaToRelCandHds.end())
      {
        std::map<Node, std::vector<Node>> lemRelCandHds;
        getRelCandidateHds(lem, lemRelCandHds);
        d_refLemmaToRelCandHds[lem] = lemRelCandHds;
        it = d_refLemmaToRelCandHds.find(lem);
      }
      relCandHds.insert(it->second.begin(), it->second.end());
    }
    if (Trace.isOn("cegis"))
    {
      Trace("cegis") << "  Relevant candidates : [ ";
      for (const auto& pair : relCandHds)
      {
        Trace("cegis") << pair.first << ": " << pair.second << "";
      }
      Trace("cegis") << "]\n";
    }
    lems.clear();
    // For each enumerator, equality with model value
    std::vector<Node> enumsExp;
    std::vector<Node> hdsExp;
    std::vector<Node> hdsUnfold;
    std::map<Node, Node> enumToValue;
    SygusEvalUnfold* evUnfold = d_tds->getEvalUnfold();
    // map enum to value
    for (size_t i = 0, size = enums.size(); i < size; ++i)
    {
      enumToValue[enums[i]] = enum_values[i];
    }
    // Go through the relevant candidates
    for (const auto& p : relCandHds)
    {
      Node e = p.first;
      Node enumExp =
          d_tds->getExplain()->getExplanationForEquality(e, enumToValue[e]);
      // get model values of heads. Note however that if there is an anyconst in
      // the enum value, we have to be smart, e.g.
      //
      //   is-any-constant(d) => f1 = d.0 ^ f2 = d.0 ^ f6 = d.0
      for (const Node& hd : p.second)
      {
        // build (DT_SYGUS_EVAL enums[i] pt0 ... ptn), in which pti corresponds
        // to the point of hd. This will be unfolded so that we get the proper
        // value for this head in the case that enum_values[i] (retrieved by the
        // unfolding method from enumToValue) contains anyconst
        std::vector<Node> evalChildren{e};
        auto itPt = d_hdToPt.find(hd);
        AlwaysAssert(itPt != d_hdToPt.end());
        evalChildren.insert(
            evalChildren.end(), itPt->second.begin(), itPt->second.end());
        Node eval = nm->mkNode(kind::DT_SYGUS_EVAL, evalChildren);
        // placeholder. The method has to be called with fourth argument true
        // (track_exp in the signature) because only in this mode the model
        // value is retrieved from the second argument.
        std::vector<Node> tmpExp;
        eval = evUnfold->unfold(eval, enumToValue, tmpExp, true, true);
        Trace("cegis-unfold") << "  ...unfolded hd " << hd
                              << " to : " << Rewriter::rewrite(eval) << "\n";
        hdsUnfold.push_back(eval);
        hdsExp.push_back(hd.eqNode(eval));
      }
      // check if heads values lead to false
      AlwaysAssert(d_refinement_lemmas.size() == 1);
      Node tmp = d_purifiedLemma.substitute(
          p.second.begin(), p.second.end(), hdsUnfold.begin(), hdsUnfold.end());
      Trace("cegis-unfold") << "Lemma to rewrite: " << tmp << "\n";
      Trace("cegis-unfold")
          << "Lemma rewritten: "
          << d_tds->getExtRewriter()->extendedRewrite(tmp) << "\n";
      if (d_tds->getExtRewriter()->extendedRewrite(tmp) == d_false)
      {
        Trace("cegis") << "...Blocking skeleton\n";
        lems.push_back(enumExp.negate());
      }
      else
      {  // build lemma
        std::vector<Node> children{
            enumExp.negate(),
            hdsExp.size() > 1 ? nm->mkNode(kind::AND, hdsExp) : hdsExp[0]};
        lems.push_back(nm->mkNode(kind::OR, children));
      }
      Trace("cegis-lemma") << "  Lemma: " << lems.back() << "\n";
    }
    return false;
  }

  // try to construct candidates
  if (!processConstructCandidates(enums,
                                  enum_values,
                                  candidates,
                                  candidate_values,
                                  !addedEvalLemmas,
                                  lems))
  {
    return false;
  }

  if (options::cegisSample() != options::CegisSampleMode::NONE && lems.empty())
  {
    // if we didn't add a lemma, trying sampling to add a refinement lemma
    // that immediately refutes the candidate we just constructed
    if (sampleAddRefinementLemma(candidates, candidate_values, lems))
    {
      candidate_values.clear();
      // restart (should be guaranteed to add evaluation lemmas on this call)
      return constructCandidates(
          enums, enum_values, candidates, candidate_values, lems);
    }
  }
  return true;
}

bool Cegis::processConstructCandidates(const std::vector<Node>& enums,
                                       const std::vector<Node>& enum_values,
                                       const std::vector<Node>& candidates,
                                       std::vector<Node>& candidate_values,
                                       bool satisfiedRl,
                                       std::vector<Node>& lems)
{
  if (satisfiedRl)
  {
    candidate_values.insert(
        candidate_values.end(), enum_values.begin(), enum_values.end());
    return true;
  }
  return false;
}

void Cegis::addRefinementLemma(Node lem)
{
  Trace("cegis-rl") << "Cegis::addRefinementLemma: " << lem << std::endl;
  d_refinement_lemmas.push_back(lem);
  // apply existing substitution
  Node slem = lem;
  if (!d_rl_eval_hds.empty())
  {
    slem = lem.substitute(d_rl_eval_hds.begin(),
                          d_rl_eval_hds.end(),
                          d_rl_vals.begin(),
                          d_rl_vals.end());
  }
  // rewrite with extended rewriter
  slem = d_tds->getExtRewriter()->extendedRewrite(slem);
  // collect all variables in slem
  expr::getSymbols(slem, d_refinement_lemma_vars);
  std::vector<Node> waiting;
  waiting.push_back(lem);
  unsigned wcounter = 0;
  // while we are not done adding lemmas
  while (wcounter < waiting.size())
  {
    // add the conjunct, possibly propagating
    addRefinementLemmaConjunct(wcounter, waiting);
    wcounter++;
  }
}

void Cegis::addRefinementLemmaConjunct(unsigned wcounter,
                                       std::vector<Node>& waiting)
{
  Node lem = waiting[wcounter];
  lem = Rewriter::rewrite(lem);
  // apply substitution and rewrite if applicable
  if (lem.isConst())
  {
    if (!lem.getConst<bool>())
    {
      // conjecture is infeasible
    }
    else
    {
      return;
    }
  }
  // break into conjunctions
  if (lem.getKind() == AND)
  {
    for (const Node& lc : lem)
    {
      waiting.push_back(lc);
    }
    return;
  }
  // does this correspond to a substitution?
  NodeManager* nm = NodeManager::currentNM();
  TNode term;
  TNode val;
  if (lem.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (lem[i].isConst() && d_tds->isEvaluationPoint(lem[1 - i]))
      {
        term = lem[1 - i];
        val = lem[i];
        break;
      }
    }
  }
  else
  {
    term = lem.getKind() == NOT ? lem[0] : lem;
    // predicate case: the conjunct is a (negated) evaluation point
    if (d_tds->isEvaluationPoint(term))
    {
      val = nm->mkConst(lem.getKind() != NOT);
    }
  }
  if (!val.isNull())
  {
    if (d_refinement_lemma_unit.find(lem) != d_refinement_lemma_unit.end())
    {
      // already added
      return;
    }
    Trace("cegis-rl") << "* cegis-rl: propagate: " << term << " -> " << val
                      << std::endl;
    d_rl_eval_hds.push_back(term);
    d_rl_vals.push_back(val);
    d_refinement_lemma_unit.insert(lem);

    // apply to waiting lemmas beyond this one
    for (unsigned i = wcounter + 1, size = waiting.size(); i < size; i++)
    {
      waiting[i] = waiting[i].substitute(term, val);
    }
    // apply to all existing refinement lemmas
    std::vector<Node> to_rem;
    for (const Node& rl : d_refinement_lemma_conj)
    {
      Node srl = rl.substitute(term, val);
      if (srl != rl)
      {
        Trace("cegis-rl") << "* cegis-rl: replace: " << rl << " -> " << srl
                          << std::endl;
        waiting.push_back(srl);
        to_rem.push_back(rl);
      }
    }
    for (const Node& tr : to_rem)
    {
      d_refinement_lemma_conj.erase(tr);
    }
  }
  else
  {
    if (Trace.isOn("cegis-rl"))
    {
      if (d_refinement_lemma_conj.find(lem) == d_refinement_lemma_conj.end())
      {
        Trace("cegis-rl") << "cegis-rl: add: " << lem << std::endl;
      }
    }
    d_refinement_lemma_conj.insert(lem);
  }
}

void Cegis::registerRefinementLemma(const std::vector<Node>& vars,
                                    Node lem,
                                    std::vector<Node>& lems)
{
  Assert(!d_usingSymConsGround);
  addRefinementLemma(lem);
  // Make the refinement lemma and add it to lems.
  // This lemma is guarded by the parent's guard, which has the semantics
  // "this conjecture has a solution", hence this lemma states:
  // if the parent conjecture has a solution, it satisfies the specification
  // for the given concrete point.
  Node rlem =
      NodeManager::currentNM()->mkNode(OR, d_parent->getGuard().negate(), lem);
  lems.push_back(rlem);
}

bool Cegis::usingRepairConst() { return true; }
bool Cegis::getRefinementEvalLemmas(const std::vector<Node>& vs,
                                    const std::vector<Node>& ms,
                                    std::vector<Node>& lems)
{
  Trace("sygus-cref-eval") << "Cref eval : conjecture has "
                           << d_refinement_lemma_unit.size() << " unit and "
                           << d_refinement_lemma_conj.size()
                           << " non-unit refinement lemma conjunctions."
                           << std::endl;
  Assert(vs.size() == ms.size());

  NodeManager* nm = NodeManager::currentNM();

  Node nfalse = nm->mkConst(false);
  Node neg_guard = d_parent->getGuard().negate();
  bool ret = false;

  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<Node, NodeHashFunction>& rlemmas =
        r == 0 ? d_refinement_lemma_unit : d_refinement_lemma_conj;
    for (const Node& lem : rlemmas)
    {
      Assert(!lem.isNull());
      std::map<Node, Node> visited;
      std::map<Node, std::vector<Node> > exp;
      EvalSygusInvarianceTest vsit;
      Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lem
                               << " against current model." << std::endl;
      Trace("sygus-cref-eval2") << "Check refinement lemma conjunct " << lem
                                << " against current model." << std::endl;
      Node cre_lem;
      Node lemcs = lem.substitute(vs.begin(), vs.end(), ms.begin(), ms.end());
      Trace("sygus-cref-eval2")
          << "...under substitution it is : " << lemcs << std::endl;
      Node lemcsu = vsit.doEvaluateWithUnfolding(d_tds, lemcs);
      Trace("sygus-cref-eval2")
          << "...after unfolding is : " << lemcsu << std::endl;
      if (lemcsu.isConst() && !lemcsu.getConst<bool>())
      {
        ret = true;
        // lemma will be built in custom way outside. Just store the refinement
        // lemma TODO use the invariance test etc below to optimize the
        // functions that were actually relevant for the conflict
        if (d_usingSymConsGround)
        {
          lems.push_back(lem);
          continue;
        }
        std::vector<Node> msu;
        std::vector<Node> mexp;
        msu.insert(msu.end(), ms.begin(), ms.end());
        std::map<TypeNode, int> var_count;
        for (unsigned k = 0; k < vs.size(); k++)
        {
          vsit.setUpdatedTerm(msu[k]);
          msu[k] = vs[k];
          // substitute for everything except this
          Node sconj =
              lem.substitute(vs.begin(), vs.end(), msu.begin(), msu.end());
          vsit.init(sconj, vs[k], nfalse);
          // get minimal explanation for this
          Node ut = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "  compute min explain of : " << vs[k] << " = " << ut
              << std::endl;
          d_tds->getExplain()->getExplanationFor(
              vs[k], ut, mexp, vsit, var_count, false);
          Trace("sygus-cref-eval2-debug") << "exp now: " << mexp << std::endl;
          msu[k] = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "updated term : " << msu[k] << std::endl;
        }
        if (!mexp.empty())
        {
          Node en = mexp.size() == 1 ? mexp[0] : nm->mkNode(kind::AND, mexp);
          cre_lem = nm->mkNode(kind::OR, en.negate(), neg_guard);
        }
        else
        {
          cre_lem = neg_guard;
        }
        if (std::find(lems.begin(), lems.end(), cre_lem) == lems.end())
        {
          Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem
                                   << std::endl;
          lems.push_back(cre_lem);
        }
      }
    }
    if (!lems.empty())
    {
      break;
    }
  }
  return ret;
}

bool Cegis::checkRefinementEvalLemmas(const std::vector<Node>& vs,
                                      const std::vector<Node>& ms)
{
  // Maybe we already evaluated some terms in refinement lemmas.
  // In particular, the example eval cache for f may have some evaluations
  // cached, which we add to evalVisited and pass to the evaluator below.
  std::unordered_map<Node, Node, NodeHashFunction> evalVisited;
  ExampleInfer* ei = d_parent->getExampleInfer();
  for (unsigned i = 0, vsize = vs.size(); i < vsize; i++)
  {
    Node f = vs[i];
    ExampleEvalCache* eec = d_parent->getExampleEvalCache(f);
    if (eec != nullptr)
    {
      // get the results we obtained through the example evaluation utility
      std::vector<Node> vsProc;
      std::vector<Node> msProc;
      Node bmsi = d_tds->sygusToBuiltin(ms[i]);
      ei->getExampleTerms(f, vsProc);
      eec->evaluateVec(bmsi, msProc);
      Assert(vsProc.size() == msProc.size());
      for (unsigned j = 0, psize = vsProc.size(); j < psize; j++)
      {
        evalVisited[vsProc[j]] = msProc[j];
        Assert(vsProc[j].getType().isComparableTo(msProc[j].getType()));
      }
    }
  }

  Evaluator* eval = d_tds->getEvaluator();
  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<Node, NodeHashFunction>& rlemmas =
        r == 0 ? d_refinement_lemma_unit : d_refinement_lemma_conj;
    for (const Node& lem : rlemmas)
    {
      // We may have computed the evaluation of some function applications
      // via example-based symmetry breaking, stored in evalVisited.
      Node lemcsu = eval->eval(lem, vs, ms, evalVisited);
      if (lemcsu.isConst() && !lemcsu.getConst<bool>())
      {
        return true;
      }
    }
  }
  return false;
}

bool Cegis::sampleAddRefinementLemma(const std::vector<Node>& candidates,
                                     const std::vector<Node>& vals,
                                     std::vector<Node>& lems)
{
  Trace("sygus-engine") << "  *** Do sample add refinement..." << std::endl;
  if (Trace.isOn("cegis-sample"))
  {
    Trace("cegis-sample") << "Check sampling for candidate solution"
                          << std::endl;
    for (unsigned i = 0, size = vals.size(); i < size; i++)
    {
      Trace("cegis-sample") << "  " << candidates[i] << " -> " << vals[i]
                            << std::endl;
    }
  }
  Assert(vals.size() == candidates.size());
  Node sbody = d_base_body.substitute(
      candidates.begin(), candidates.end(), vals.begin(), vals.end());
  Trace("cegis-sample-debug2") << "Sample " << sbody << std::endl;
  // do eager rewriting
  sbody = Rewriter::rewrite(sbody);
  Trace("cegis-sample") << "Sample (after rewriting): " << sbody << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = d_cegis_sampler.getNumSamplePoints(); i < size;
       i++)
  {
    if (d_cegis_sample_refine.find(i) == d_cegis_sample_refine.end())
    {
      Node ev = d_cegis_sampler.evaluate(sbody, i);
      Trace("cegis-sample-debug") << "...evaluate point #" << i << " to " << ev
                                  << std::endl;
      Assert(ev.isConst());
      Assert(ev.getType().isBoolean());
      if (!ev.getConst<bool>())
      {
        Trace("cegis-sample-debug") << "...false for point #" << i << std::endl;
        // mark this as a CEGIS point (no longer sampled)
        d_cegis_sample_refine.insert(i);
        std::vector<Node> pt;
        d_cegis_sampler.getSamplePoint(i, pt);
        Assert(d_base_vars.size() == pt.size());
        Node rlem = d_base_body.substitute(
            d_base_vars.begin(), d_base_vars.end(), pt.begin(), pt.end());
        rlem = Rewriter::rewrite(rlem);
        if (std::find(
                d_refinement_lemmas.begin(), d_refinement_lemmas.end(), rlem)
            == d_refinement_lemmas.end())
        {
          if (Trace.isOn("cegis-sample"))
          {
            Trace("cegis-sample") << "   false for point #" << i << " : ";
            for (const Node& cn : pt)
            {
              Trace("cegis-sample") << cn << " ";
            }
            Trace("cegis-sample") << std::endl;
          }
          Trace("sygus-engine") << "  *** Refine by sampling" << std::endl;
          addRefinementLemma(rlem);
          // if trust, we are not interested in sending out refinement lemmas
          if (options::cegisSample() != options::CegisSampleMode::TRUST)
          {
            Node lem = nm->mkNode(OR, d_parent->getGuard().negate(), rlem);
            lems.push_back(lem);
          }
          return true;
        }
        else
        {
          Trace("cegis-sample-debug") << "...duplicate." << std::endl;
        }
      }
    }
  }
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
