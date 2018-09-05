/*********************                                                        */
/*! \file sygus_unif_rl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif_rl
 **/

#include "theory/quantifiers/sygus/sygus_unif_rl.h"

#include <math.h>

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnifRl::SygusUnifRl(CegConjecture* p) : d_parent(p) {}
SygusUnifRl::~SygusUnifRl() {}
void SygusUnifRl::initializeCandidate(
    QuantifiersEngine* qe,
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  // initialize
  std::vector<Node> all_enums;
  SygusUnif::initializeCandidate(qe, f, all_enums, strategy_lemmas);
  // based on the strategy inferred for each function, determine if we are
  // using a unification strategy that is compatible our approach.
  StrategyRestrictions restrictions;
  if (options::sygusBoolIteReturnConst())
  {
    restrictions.d_iteReturnBoolConst = true;
  }
  // register the strategy
  registerStrategy(f, enums, restrictions.d_unused_strategies);
  d_strategy[f].staticLearnRedundantOps(strategy_lemmas, restrictions);
  // Copy candidates and check whether CegisUnif for any of them
  if (d_unif_candidates.find(f) != d_unif_candidates.end())
  {
    d_hd_to_pt[f].clear();
    d_cand_to_eval_hds[f].clear();
    d_cand_to_hd_count[f] = 0;
  }
}

void SygusUnifRl::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  // we do not use notify enumeration
  Assert(false);
}

Node SygusUnifRl::purifyLemma(Node n,
                              bool ensureConst,
                              std::vector<Node>& model_guards,
                              BoolNodePairMap& cache)
{
  Trace("sygus-unif-rl-purify") << "PurifyLemma : " << n << "\n";
  BoolNodePairMap::const_iterator it = cache.find(BoolNodePair(ensureConst, n));
  if (it != cache.end())
  {
    Trace("sygus-unif-rl-purify-debug") << "... already visited " << n << "\n";
    return it->second;
  }
  // Recurse
  unsigned size = n.getNumChildren();
  Kind k = n.getKind();
  // We retrive model value now because purified node may not have a value
  Node nv = n;
  // Whether application of a function-to-synthesize
  bool fapp = (n.getKind() == DT_SYGUS_EVAL);
  bool u_fapp = false;
  bool nu_fapp = false;
  if (fapp)
  {
    Assert(std::find(d_candidates.begin(), d_candidates.end(), n[0])
           != d_candidates.end());
    // Whether application of a (non-)unification function-to-synthesize
    u_fapp = usingUnif(n[0]);
    nu_fapp = !usingUnif(n[0]);
    // get model value of non-top level applications of functions-to-synthesize
    // occurring under a unification function-to-synthesize
    if (ensureConst)
    {
      std::map<Node, Node>::iterator it = d_cand_to_sol.find(n[0]);
      // if function-to-synthesize, retrieve its built solution to replace in
      // the application before computing the model value
      AlwaysAssert(!u_fapp || it != d_cand_to_sol.end());
      if (it != d_cand_to_sol.end())
      {
        TNode cand = n[0];
        Node tmp = n.substitute(cand, it->second);
        nv = d_tds->evaluateWithUnfolding(tmp);
        Trace("sygus-unif-rl-purify") << "PurifyLemma : model value for " << tmp
                                      << " is " << nv << "\n";
      }
      else
      {
        nv = d_parent->getModelValue(n);
        Trace("sygus-unif-rl-purify") << "PurifyLemma : model value for " << n
                                      << " is " << nv << "\n";
      }
      Assert(n != nv);
    }
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
    // Arguments of non-unif functions do not need to be constant
    Node child = purifyLemma(
        n[i], !nu_fapp && (ensureConst || u_fapp), model_guards, cache);
    children.push_back(child);
    childChanged = childChanged || child != n[i];
  }
  Node nb;
  if (childChanged)
  {
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      Trace("sygus-unif-rl-purify-debug") << "Node " << n
                                          << " is parameterized\n";
      children.insert(children.begin(), n.getOperator());
    }
    if (Trace.isOn("sygus-unif-rl-purify-debug"))
    {
      Trace("sygus-unif-rl-purify-debug")
          << "...rebuilding " << n << " with kind " << k << " and children:\n";
      for (const Node& child : children)
      {
        Trace("sygus-unif-rl-purify-debug") << "...... " << child << "\n";
      }
    }
    nb = NodeManager::currentNM()->mkNode(k, children);
    Trace("sygus-unif-rl-purify") << "PurifyLemma : transformed " << n
                                  << " into " << nb << "\n";
  }
  else
  {
    nb = n;
  }
  // Map to point enumerator every unification function-to-synthesize
  if (u_fapp)
  {
    Node np;
    std::map<Node, Node>::const_iterator it = d_app_to_purified.find(nb);
    if (it == d_app_to_purified.end())
    {
      // Build purified head with fresh skolem and recreate node
      std::stringstream ss;
      ss << nb[0] << "_" << d_cand_to_hd_count[nb[0]]++;
      Node new_f = nm->mkSkolem(ss.str(),
                                nb[0].getType(),
                                "head of unif evaluation point",
                                NodeManager::SKOLEM_EXACT_NAME);
      // Adds new enumerator to map from candidate
      Trace("sygus-unif-rl-purify") << "...new enum " << new_f
                                    << " for candidate " << nb[0] << "\n";
      d_cand_to_eval_hds[nb[0]].push_back(new_f);
      // Maps new enumerator to its respective tuple of arguments
      d_hd_to_pt[new_f] =
          std::vector<Node>(children.begin() + 1, children.end());
      if (Trace.isOn("sygus-unif-rl-purify-debug"))
      {
        Trace("sygus-unif-rl-purify-debug") << "...[" << new_f << "] --> ( ";
        for (const Node& pt_i : d_hd_to_pt[new_f])
        {
          Trace("sygus-unif-rl-purify-debug") << pt_i << " ";
        }
        Trace("sygus-unif-rl-purify-debug") << ")\n";
      }
      // replace first child and rebulid node
      Assert(children.size() > 0);
      children[0] = new_f;
      Trace("sygus-unif-rl-purify-debug") << "Make sygus eval app " << children
                                          << std::endl;
      np = nm->mkNode(DT_SYGUS_EVAL, children);
      d_app_to_purified[nb] = np;
    }
    else
    {
      np = it->second;
    }
    Trace("sygus-unif-rl-purify")
        << "PurifyLemma : purified head and transformed " << nb << " into "
        << np << "\n";
    nb = np;
  }
  // Add equality between purified fapp and model value
  if (ensureConst && fapp)
  {
    model_guards.push_back(
        NodeManager::currentNM()->mkNode(EQUAL, nv, nb).negate());
    nb = nv;
    Trace("sygus-unif-rl-purify") << "PurifyLemma : adding model eq "
                                  << model_guards.back() << "\n";
  }
  nb = Rewriter::rewrite(nb);
  // every non-top level application of function-to-synthesize must be reduced
  // to a concrete constant
  Assert(!ensureConst || nb.isConst());
  Trace("sygus-unif-rl-purify-debug") << "... caching [" << n << "] = " << nb
                                      << "\n";
  cache[BoolNodePair(ensureConst, n)] = nb;
  return nb;
}

Node SygusUnifRl::addRefLemma(Node lemma,
                              std::map<Node, std::vector<Node>>& eval_hds)
{
  Trace("sygus-unif-rl-purify") << "Registering lemma at SygusUnif : " << lemma
                                << "\n";
  std::vector<Node> model_guards;
  BoolNodePairMap cache;
  // cache previous sizes
  std::map<Node, unsigned> prev_n_eval_hds;
  for (const std::pair<const Node, std::vector<Node>>& cp : d_cand_to_eval_hds)
  {
    prev_n_eval_hds[cp.first] = cp.second.size();
  }

  // Make the purified lemma which will guide the unification utility.
  Node plem = purifyLemma(lemma, false, model_guards, cache);
  if (!model_guards.empty())
  {
    model_guards.push_back(plem);
    plem = NodeManager::currentNM()->mkNode(OR, model_guards);
  }
  plem = Rewriter::rewrite(plem);
  Trace("sygus-unif-rl-purify") << "Purified lemma : " << plem << "\n";

  Trace("sygus-unif-rl-purify") << "Collect new evaluation points...\n";
  for (const std::pair<const Node, std::vector<Node>>& cp : d_cand_to_eval_hds)
  {
    Node c = cp.first;
    unsigned prevn = 0;
    std::map<Node, unsigned>::iterator itp = prev_n_eval_hds.find(c);
    if (itp != prev_n_eval_hds.end())
    {
      prevn = itp->second;
    }
    for (unsigned j = prevn, size = cp.second.size(); j < size; j++)
    {
      eval_hds[c].push_back(cp.second[j]);
      // Add new point to respective decision trees
      Assert(d_cand_cenums.find(c) != d_cand_cenums.end());
      for (const Node& cenum : d_cand_cenums[c])
      {
        Assert(d_cenum_to_stratpt.find(cenum) != d_cenum_to_stratpt.end());
        for (const Node& stratpt : d_cenum_to_stratpt[cenum])
        {
          Assert(d_stratpt_to_dt.find(stratpt) != d_stratpt_to_dt.end());
          Trace("sygus-unif-rl-dt") << "Register point with head "
                                    << cp.second[j] << " to strategy point "
                                    << stratpt << "\n";
          // Register new point from new head
          d_stratpt_to_dt[stratpt].d_hds.push_back(cp.second[j]);
        }
      }
    }
  }

  return plem;
}

void SygusUnifRl::initializeConstructSol() {}
void SygusUnifRl::initializeConstructSolFor(Node f) {}
bool SygusUnifRl::constructSolution(std::vector<Node>& sols,
                                    std::vector<Node>& lemmas)
{
  initializeConstructSol();
  bool successful = true;
  for (const Node& c : d_candidates)
  {
    if (!usingUnif(c))
    {
      Node v = d_parent->getModelValue(c);
      sols.push_back(v);
      continue;
    }
    initializeConstructSolFor(c);
    Node v = constructSol(
        c, d_strategy[c].getRootEnumerator(), role_equal, 0, lemmas);
    if (v.isNull())
    {
      // we continue trying to build solutions to accumulate potentitial
      // separation conditions from other decision trees
      successful = false;
      continue;
    }
    sols.push_back(v);
    d_cand_to_sol[c] = v;
  }
  return successful;
}

Node SygusUnifRl::constructSol(
    Node f, Node e, NodeRole nrole, int ind, std::vector<Node>& lemmas)
{
  indent("sygus-unif-sol", ind);
  Trace("sygus-unif-sol") << "ConstructSol: SygusRL : " << e << std::endl;
  // retrieve strategy information
  TypeNode etn = e.getType();
  EnumTypeInfo& tinfo = d_strategy[f].getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  if (nrole != role_equal)
  {
    return Node::null();
  }
  // is there a decision tree strategy?
  std::map<Node, DecisionTreeInfo>::iterator itd = d_stratpt_to_dt.find(e);
  // for now only considering simple case of sole "ITE(cond, e, e)" strategy
  if (itd == d_stratpt_to_dt.end())
  {
    return Node::null();
  }
  indent("sygus-unif-sol", ind);
  Trace("sygus-unif-sol") << "...it has a decision tree strategy.\n";
  // whether empty set of points
  if (d_cand_to_eval_hds[f].empty())
  {
    Trace("sygus-unif-sol") << "...... no points, return root enum value "
                            << d_parent->getModelValue(e) << "\n";
    return d_parent->getModelValue(e);
  }
  EnumTypeInfoStrat* etis = snode.d_strats[itd->second.getStrategyIndex()];
  Node sol = itd->second.buildSol(etis->d_cons, lemmas);
  Assert(options::sygusUnifCondIndependent() || !sol.isNull()
         || !lemmas.empty());
  return sol;
}

bool SygusUnifRl::usingUnif(Node f) const
{
  return d_unif_candidates.find(f) != d_unif_candidates.end();
}

Node SygusUnifRl::getConditionForEvaluationPoint(Node e) const
{
  std::map<Node, DecisionTreeInfo>::const_iterator it = d_stratpt_to_dt.find(e);
  Assert(it != d_stratpt_to_dt.end());
  return it->second.getConditionEnumerator();
}

void SygusUnifRl::setConditions(Node e,
                                Node guard,
                                const std::vector<Node>& enums,
                                const std::vector<Node>& conds)
{
  std::map<Node, DecisionTreeInfo>::iterator it = d_stratpt_to_dt.find(e);
  Assert(it != d_stratpt_to_dt.end());
  // set the conditions for the appropriate tree
  it->second.setConditions(guard, enums, conds);
}

void SygusUnifRl::setEntailed(Node e, Node hd)
{
  std::map<Node, DecisionTreeInfo>::iterator it = d_stratpt_to_dt.find(e);
  Assert(it != d_stratpt_to_dt.end());
  // set hd as entailed for the appropriate tree
  Assert(std::find(it->second.d_hds_entailed.begin(),
                   it->second.d_hds_entailed.end(),
                   hd)
         == it->second.d_hds_entailed.end());
  it->second.d_hds_entailed.push_back(hd);
}

std::vector<Node> SygusUnifRl::getEvalPointHeads(Node c)
{
  std::map<Node, std::vector<Node>>::iterator it = d_cand_to_eval_hds.find(c);
  if (it == d_cand_to_eval_hds.end())
  {
    return std::vector<Node>();
  }
  return it->second;
}

void SygusUnifRl::registerStrategy(
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::unordered_set<unsigned>>& unused_strats)
{
  if (Trace.isOn("sygus-unif-rl-strat"))
  {
    Trace("sygus-unif-rl-strat") << "Strategy for " << f
                                 << " is : " << std::endl;
    d_strategy[f].debugPrint("sygus-unif-rl-strat");
  }
  Trace("sygus-unif-rl-strat") << "Register..." << std::endl;
  Node e = d_strategy[f].getRootEnumerator();
  std::map<Node, std::map<NodeRole, bool>> visited;
  registerStrategyNode(f, e, role_equal, visited, enums, unused_strats);
}

void SygusUnifRl::registerStrategyNode(
    Node f,
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool>>& visited,
    std::vector<Node>& enums,
    std::map<Node, std::unordered_set<unsigned>>& unused_strats)
{
  Trace("sygus-unif-rl-strat") << "  register node " << e << std::endl;
  if (visited[e].find(nrole) != visited[e].end())
  {
    return;
  }
  visited[e][nrole] = true;
  TypeNode etn = e.getType();
  EnumTypeInfo& tinfo = d_strategy[f].getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
  {
    EnumTypeInfoStrat* etis = snode.d_strats[j];
    StrategyType strat = etis->d_this;
    // is this a simple recursive ITE strategy?
    bool success = false;
    if (strat == strat_ITE && nrole == role_equal)
    {
      success = true;
      for (unsigned c = 1; c <= 2; c++)
      {
        std::pair<Node, NodeRole> child = etis->d_cenum[c];
        if (child.first != e || child.second != nrole)
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        Node cond = etis->d_cenum[0].first;
        Assert(etis->d_cenum[0].second == role_ite_condition);
        Trace("sygus-unif-rl-strat")
            << "  ...detected recursive ITE strategy, condition enumerator : "
            << cond << std::endl;
        // indicate that we will be enumerating values for cond
        registerConditionalEnumerator(f, e, cond, j);
        // we will be using a strategy for e
        enums.push_back(e);
      }
    }
    if (!success)
    {
      unused_strats[e].insert(j);
    }
    // TODO: recurse? for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
  }
}

void SygusUnifRl::registerConditionalEnumerator(Node f,
                                                Node e,
                                                Node cond,
                                                unsigned strategy_index)
{
  // only allow one decision tree per strategy point
  if (d_stratpt_to_dt.find(e) != d_stratpt_to_dt.end())
  {
    return;
  }
  // we will do unification for this candidate
  d_unif_candidates.insert(f);
  // add to the list of all conditional enumerators
  if (std::find(d_cond_enums.begin(), d_cond_enums.end(), cond)
      == d_cond_enums.end())
  {
    d_cond_enums.push_back(cond);
    d_cand_cenums[f].push_back(cond);
    d_cenum_to_stratpt[cond].clear();
  }
  // register that this strategy node has a decision tree construction
  d_stratpt_to_dt[e].initialize(cond, this, &d_strategy[f], strategy_index);
  // associate conditional enumerator with strategy node
  d_cenum_to_stratpt[cond].push_back(e);
}

void SygusUnifRl::DecisionTreeInfo::initialize(Node cond_enum,
                                               SygusUnifRl* unif,
                                               SygusUnifStrategy* strategy,
                                               unsigned strategy_index)
{
  d_cond_enum = cond_enum;
  d_unif = unif;
  d_strategy = strategy;
  d_strategy_index = strategy_index;
  // Retrieve template
  EnumInfo& eiv = d_strategy->getEnumInfo(d_cond_enum);
  d_template = NodePair(eiv.d_template, eiv.d_template_arg);
  // Initialize classifier
  d_pt_sep.initialize(this);
}

void SygusUnifRl::DecisionTreeInfo::setConditions(
    Node guard, const std::vector<Node>& enums, const std::vector<Node>& conds)
{
  Assert(enums.size() == conds.size());
  // set the guard
  d_guard = guard;
  // clear old condition values
  d_enums.clear();
  d_conds.clear();
  // set new condition values
  d_enums.insert(d_enums.end(), enums.begin(), enums.end());
  d_conds.insert(d_conds.end(), conds.begin(), conds.end());
  // add to condition pool
  if (options::sygusUnifCondIndependent() || options::sygusUnifCondPool())
  {
    if (Trace.isOn("sygus-unif-cond-pool"))
    {
      for (const Node& condv : conds)
      {
        if (d_cond_mvs.find(condv) == d_cond_mvs.end())
        {
          Trace("sygus-unif-cond-pool")
              << "  ...adding to condition pool : "
              << d_unif->d_tds->sygusToBuiltin(condv, condv.getType()) << "\n";
        }
      }
    }
    d_cond_mvs.insert(conds.begin(), conds.end());
  }
}

unsigned SygusUnifRl::DecisionTreeInfo::getStrategyIndex() const
{
  return d_strategy_index;
}

Node SygusUnifRl::DecisionTreeInfo::buildSol(Node cons,
                                             std::vector<Node>& lemmas)
{
  if (!d_template.first.isNull())
  {
    Trace("sygus-unif-sol") << "...templated conditions unsupported\n";
    return Node::null();
  }
  Trace("sygus-unif-sol") << "Decision::buildSol with " << d_hds.size()
                          << " evaluation heads and " << d_conds.size()
                          << " conditions..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // model values for evaluation heads
  std::map<Node, Node> hd_mv;
  // reset the trie
  d_pt_sep.d_trie.clear();
  // set initial backtrack size for when repairing trie with condition pool
  d_exp_backtrack_size = -1;
  // the current explanation of why there has not yet been a separation conflict
  std::vector<Node> exp;
  // is the above explanation ready to be sent out as a lemma?
  bool exp_conflict = false;
  // the index of the head we are considering
  unsigned hd_counter = 0;
  // the index of the condition we are considering
  unsigned c_counter = 0;
  // do we need to resolve a separation conflict?
  bool needs_sep_resolve = false;
  if (options::sygusUnifCondIndependent())
  {
    // add conditions
    d_conds.clear();
    d_conds.insert(d_conds.end(), d_cond_mvs.begin(), d_cond_mvs.end());
    unsigned num_conds = d_conds.size();
    for (unsigned i = 0; i < num_conds; ++i)
    {
      d_pt_sep.d_trie.addClassifier(&d_pt_sep, i);
    }
    // add heads
    for (const Node& e : d_hds)
    {
      Node v = d_unif->d_parent->getModelValue(e);
      hd_mv[e] = v;
      Node er = d_pt_sep.d_trie.add(e, &d_pt_sep, num_conds);
      // are we in conflict?
      if (er == e)
      {
        // new separation class, no conflict
        continue;
      }
      Assert(hd_mv.find(er) != hd_mv.end());
      // merged into separation class with same model value, no conflict
      if (hd_mv[e] == hd_mv[er])
      {
        continue;
      }
      // conflict. Explanation?
      Trace("sygus-unif-sol") << "  ...can't separate " << e << " from " << er
                              << std::endl;
      return Node::null();
    }
    Trace("sygus-unif-sol") << "...ready to build solution from DT\n";
    return d_pt_sep.extractSol(cons, hd_mv);
  }
  // This loop simultaneously builds the solution in terms of a lazy trie
  // (LazyTrieMulti), and checks whether a separation conflict exists. We
  // enforce that the separation conflicts we encounter while building
  // this solution are resolved, in order, by the condition enumerators.
  // If not, then we add a (conflict) lemma stating that the current model
  // value of the condition enumerator must be different. We also call this
  // a "separation lemma".
  //
  // As a simple example, say we have:
  //   evalution heads: (eval e1 0 0), (eval e2 1 2)
  //   conditions: c1
  // where M(e1) = x, M(e2) = y, and M(c1) = x>1. After adding e1 and e2, we are
  // in conflict since { e1, e2 } form a separation class, M(e1)!=M(e2), and
  // M(c1) does not separate e1 and e2 since:
  //   (x>1){x->0,y->0} = (x>1){x->1,y->2} = false
  // Hence, we would fail to build a solution in this case, and instead send a
  // separation lemma of the form:
  //   ~( e1 != e2 ^ c1 = [x<1] )
  //
  // Say we have:
  //   evalution heads: (eval e1 0 0), (eval e2 1 2), (eval e3 1 3)
  //   conditions: c1 c2
  // where M(e1) = x, M(e2) = y, M(e3) = x+1, M(c1) = x>0 and M(c2) = x<0.
  // After adding e1 and e2, { e1, e2 } form a separation class, M(e1)!=M(e2),
  // but M(c1) separates e1 and e2 since
  //   (x>0){x->0,y->0} = false, and
  //   (x>1){x->1,y->2} = true
  // Hence, we get new separation classes { e1 } and { e2 }, and afterwards
  // add e3. We then get { e2, e3 } as a separation class, which is also a
  // conflict since M(e2)!=M(e3). We check if M(c2) resolves this conflict.
  // It does not, since (x<1){x->0,y->0} = (x<1){x->1,y->2} = false. Hence,
  // we get a separation lemma:
  //  ~( c1 = [x>1] ^ e2 != e3 ^ c2 = [x<1] )
  //
  // Say we have:
  //   evalution heads: (eval e1 0 0), (eval e2 1 2), (eval e3 1 3)
  //   conditions: c1
  // where M(e1) = x, M(e2) = x, M(e3) = y, M(c1) = x>0.
  // After adding e1 and e2, we have separation class { e1, e2 }. This is not a
  // conflict since M(e1)=M(e2). We then add e3, obtaining separation class
  // { e1, e2, e3 }, which is in conflict since M(e3)!=M(e1), and the condition
  // c1 does not separate e3 and the representative of this class, e1. Hence we
  // get a separation lemma of the form:
  //  ~( e1 = e2 ^ e1 != e3 ^ c1 = [x>0] )
  //
  // It also may be the case that we exhaust the pool of condition enumerators.
  // Say we have:
  //   evalution heads: (eval e1 0 0), (eval e2 1 2), (eval e3 1 3)
  //   conditions: c1
  // where M(e1) = x, M(e2) = x, M(e3) = y, M(c1) = y>0. After adding e1, e2,
  // and e3, we have a separation class { e1, e2, e3 } that is in conflict
  // since M(e3)!=M(e1). We add the condition c1, which separates into new
  // equivalence classes { e1 }, { e2, e3 }. We are still in separation conflict
  // since M(e3)!=M(e2). However, we do not have any further conditions to use
  // to resolve this conflict. Thus, we add the separation lemma:
  //  ~( e1 = e2 ^ e1 != e3 ^ e2 != e3 ^ c1 = [y>0] ^ G_1 )
  // where G_1 is a guard stating that we use at most 1 condition.
  Node e;
  Node er;
  while (hd_counter < d_hds.size() || needs_sep_resolve)
  {
    if (!needs_sep_resolve)
    {
      // add the head to the trie
      e = d_hds[hd_counter];
      Node v = d_unif->d_parent->getModelValue(e);
      addHeadValuePool(e, v);
      hd_mv[e] = v;
      if (Trace.isOn("sygus-unif-sol"))
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, hd_mv[e]);
        Trace("sygus-unif-sol")
            << "  add evaluation head (" << hd_counter << "/" << d_hds.size()
            << "): " << e << " -> " << ss.str() << std::endl;
      }
      hd_counter++;
      // get the representative of the trie
      er = d_pt_sep.d_trie.add(e, &d_pt_sep, c_counter);
      Trace("sygus-unif-sol") << "  ...separation class " << er << std::endl;
      // are we in conflict?
      if (er == e)
      {
        // new separation class, no conflict
        continue;
      }
      Assert(hd_mv.find(er) != hd_mv.end());
      if (hd_mv[e] == hd_mv[er])
      {
        // merged into separation class with same model value, no conflict
        // add to explanation
        // this states that it mattered that (er = e) at the time that e was
        // added to the trie. Notice that er and e may become separated later,
        // but to ensure the overall invariant, this equality must persist in
        // the explanation.
        if (!options::sygusUnifRetPool())
        {
          exp.push_back(er.eqNode(e));
        }
        else
        {
          // e = er is a sufficient condition for (ev er pt_er) = (ev e pt_er)
          exp.push_back(makeEvalExp(er, e, d_unif->d_hd_to_pt[er], lemmas));
        }
        Trace("sygus-unif-sol") << "  ...equal model values\n";
        Trace("sygus-unif-sol") << "  ...add to explanation " << exp.back()
                                << "\n";
        continue;
      }
    }
    // must include in the explanation that we hit a conflict at this point in
    // the construction
    if (!options::sygusUnifRetPool())
    {
      exp.push_back(e.eqNode(er).negate());
    }
    else
    {
      Trace("sygus-unif-sol-debug") << "  ...try merge " << e << " with " << er
                                    << "\n";
      // try repairing model to solve separation conflict
      //
      // the function will also include in the explanation an equality between
      // the new element and the representative if the merge is succesfull or a
      // disequality between the new element and the respective element of the
      // separation class that it was incompatible with the construction
      Node common_value = mergeHeadValuePools(
          e, d_pt_sep.d_trie.d_rep_to_class[er], exp, lemmas);
      if (!common_value.isNull())
      {
        // update model value of all members of separation class
        for (const Node& e : d_pt_sep.d_trie.d_rep_to_class[er])
        {
          hd_mv[e] = common_value;
        }
        needs_sep_resolve = exp_conflict = false;
        continue;
      }
    }
    // we are in separation conflict, does the next condition resolve this?
    //
    // we try to pick a condition to add to our trie. We add to the explanation
    // that the respective condition enumerator is equal to the respective value
    //
    // If we can't pick a condition then we have have exhausted our condition
    // pool. If so, we are in conflict and this conflict depends on the guard.
    if (!pickCondition(c_counter, er, e, exp))
    {
      // truncated separation lemma
      Assert(!d_guard.isNull());
      exp.push_back(d_guard);
      exp_conflict = true;
      break;
    }
    // cache the separation class
    std::vector<Node> prev_sep_c = d_pt_sep.d_trie.d_rep_to_class[er];
    // add new classifier
    d_pt_sep.d_trie.addClassifier(&d_pt_sep, c_counter);
    c_counter++;
    std::map<Node, std::vector<Node>>::iterator itr =
        d_pt_sep.d_trie.d_rep_to_class.find(e);
    // since e is last in its separation class, if it becomes a representative,
    // then it is separated from all values in prev_sep_c
    if (itr != d_pt_sep.d_trie.d_rep_to_class.end())
    {
      Trace("sygus-unif-sol") << "  ...resolves separation conflict with all\n";
      needs_sep_resolve = false;
      continue;
    }
    itr = d_pt_sep.d_trie.d_rep_to_class.find(er);
    // since er is first in its separation class, it remains a representative
    Assert(itr != d_pt_sep.d_trie.d_rep_to_class.end());
    // is e still in the separation class of er?
    if (std::find(itr->second.begin(), itr->second.end(), e)
        != itr->second.end())
    {
      Trace("sygus-unif-sol")
          << "  ...does not resolve separation conflict with current\n";
      // the condition does not separate e and er
      // this violates the invariant that the i^th conditional enumerator
      // resolves the i^th separation conflict
      exp_conflict = true;
      break;
    }
    Trace("sygus-unif-sol") << "  ...resolves separation conflict between " << e
                            << " and " << er << ", but not all\n";
    // find the new term to resolve a separation
    Node new_er = Node::null();
    // scan the previous list and find the representative of the class that e is
    // now in
    for (unsigned i = 0, size = prev_sep_c.size(); i < size; i++)
    {
      Node check_er = prev_sep_c[i];
      if (check_er != er && check_er != e)
      {
        itr = d_pt_sep.d_trie.d_rep_to_class.find(check_er);
        if (itr != d_pt_sep.d_trie.d_rep_to_class.end())
        {
          if (std::find(itr->second.begin(), itr->second.end(), e)
              != itr->second.end())
          {
            new_er = check_er;
            break;
          }
        }
      }
    }
    // should find exactly one
    Assert(!new_er.isNull());
    er = new_er;
    needs_sep_resolve = true;
    Trace("sygus-unif-sol") << "  ...now try separating " << e << " from " << er
                            << std::endl;
  }
  if (exp_conflict)
  {
    // A condition value from the pool was used at some point, discard all
    // explanations after that point
    if (options::sygusUnifCondPool() && d_exp_backtrack_size != -1)
    {
      Assert(static_cast<unsigned>(d_exp_backtrack_size) < exp.size());
      exp.resize(d_exp_backtrack_size);
    }
    Node lemma = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
    lemma = lemma.negate();
    Trace("sygus-unif-sol") << "  ......conflict is " << lemma << std::endl;
    lemmas.push_back(lemma);
    return Node::null();
  }
  Trace("sygus-unif-sol") << "...ready to build solution from DT\n";
  return d_pt_sep.extractSol(cons, hd_mv);
}

Node SygusUnifRl::DecisionTreeInfo::PointSeparator::extractSol(
    Node cons, std::map<Node, Node>& hd_mv)
{
  // rebuild decision tree using heuristic learning
  if (options::sygusUnifBooleanHeuristicDt())
  {
    recomputeSolHeuristically(hd_mv);
  }
  // Traverse trie and build ITE with cons
  NodeManager* nm = NodeManager::currentNM();
  std::map<IndTriePair, Node> cache;
  std::map<IndTriePair, Node>::iterator it;
  std::vector<IndTriePair> visit;
  unsigned index = 0;
  LazyTrie* trie;
  IndTriePair root = IndTriePair(0, &d_trie.d_trie);
  visit.push_back(root);
  while (!visit.empty())
  {
    index = visit.back().first;
    trie = visit.back().second;
    visit.pop_back();
    IndTriePair cur = IndTriePair(index, trie);
    it = cache.find(cur);
    // traverse children so results are saved to build node for parent
    if (it == cache.end())
    {
      // leaf
      if (trie->d_children.empty())
      {
        Assert(hd_mv.find(trie->d_lazy_child) != hd_mv.end());
        cache[cur] = hd_mv[trie->d_lazy_child];
        Trace("sygus-unif-sol-debug") << "......leaf, build "
                                      << d_dt->d_unif->d_tds->sygusToBuiltin(
                                             cache[cur], cache[cur].getType())
                                      << "\n";
        continue;
      }
      cache[cur] = Node::null();
      visit.push_back(cur);
      for (std::pair<const Node, LazyTrie>& p_nt : trie->d_children)
      {
        visit.push_back(IndTriePair(index + 1, &p_nt.second));
      }
      continue;
    }
    // retrieve terms of children and build result
    Assert(it->second.isNull());
    Assert(trie->d_children.size() == 1 || trie->d_children.size() == 2);
    std::vector<Node> children(4);
    children[0] = cons;
    children[1] = d_dt->d_conds[index];
    unsigned i = 0;
    for (std::pair<const Node, LazyTrie>& p_nt : trie->d_children)
    {
      i = p_nt.first.getConst<bool>() ? 2 : 3;
      Assert(cache.find(IndTriePair(index + 1, &p_nt.second)) != cache.end());
      children[i] = cache[IndTriePair(index + 1, &p_nt.second)];
      Assert(!children[i].isNull());
    }
    // condition is useless or result children are equal, no no need for ITE
    if (trie->d_children.size() == 1 || children[2] == children[3])
    {
      cache[cur] = children[i];
      Trace("sygus-unif-sol-debug")
          << "......no need for cond "
          << d_dt->d_unif->d_tds->sygusToBuiltin(d_dt->d_conds[index],
                                                 d_dt->d_conds[index].getType())
          << ", build "
          << d_dt->d_unif->d_tds->sygusToBuiltin(cache[cur],
                                                 cache[cur].getType())
          << "\n";
      continue;
    }
    Assert(trie->d_children.size() == 2);
    cache[cur] = nm->mkNode(APPLY_CONSTRUCTOR, children);
    Trace("sygus-unif-sol-debug")
        << "......build node "
        << d_dt->d_unif->d_tds->sygusToBuiltin(cache[cur], cache[cur].getType())
        << "\n";
  }
  Assert(cache.find(root) != cache.end());
  Assert(!cache.find(root)->second.isNull());
  return cache[root];
}

void SygusUnifRl::DecisionTreeInfo::PointSeparator::recomputeSolHeuristically(
    std::map<Node, Node>& hd_mv)
{
  // reset the trie
  d_trie.clear();
  // TODO workaround and not really sure this is the last condition, since I put
  // a set here. Maybe make d_cond_mvs into a vector
  Node backup_last_cond = d_dt->d_conds.back();
  d_dt->d_conds.clear();
  for (const Node& e : d_dt->d_hds)
  {
    d_trie.add(e, this, 0);
  }
  // init vector of conds
  std::vector<Node> conds;
  conds.insert(conds.end(), d_dt->d_cond_mvs.begin(), d_dt->d_cond_mvs.end());

  // recursively build trie by picking best condition for respective points
  buildDt(d_dt->d_hds, conds, hd_mv, 1);
  // if no condition was added (i.e. points are already classified), use last
  // condition as candidate
  if (d_dt->d_conds.empty())
  {
    Trace("sygus-unif-dt") << "......using last condition "
                           << d_dt->d_unif->d_tds->sygusToBuiltin(
                                  backup_last_cond, backup_last_cond.getType())
                           << " as candidate\n";
    d_dt->d_conds.push_back(backup_last_cond);
    d_trie.addClassifier(this, d_dt->d_conds.size() - 1);
  }
}

void SygusUnifRl::DecisionTreeInfo::PointSeparator::buildDt(
    std::vector<Node>& pts,
    std::vector<Node> conds,
    std::map<Node, Node>& hd_mv, int ind)
{
  // test if fully classified
  if (pts.size() < 2)
  {
    indent("sygus-unif-dt", ind);
    Trace("sygus-unif-dt") << "..set fully classified: " << (pts.empty() ? "empty" : "unary")
                           << "\n";
    return;
  }
  Node v1 = hd_mv[pts[0]];
  unsigned i = 1, size = pts.size();
  for (; i < size; ++i)
  {
    if (hd_mv[pts[i]] != v1)
    {
      break;
    }
  }
  if (i == size)
  {
    indent("sygus-unif-dt", ind);
    Trace("sygus-unif-dt") << "..set fully classified: " << pts.size() << " "
                           << (d_dt->d_unif->d_tds->sygusToBuiltin(v1,
                                                                   v1.getType())
                                       == d_true
                                   ? "good"
                                   : "bad")
                           << " points\n";
    return;
  }
  // pick condition to further classify
  double maxgain = -1;
  unsigned picked_cond = 0;
  std::vector<std::pair<std::vector<Node>, std::vector<Node>>> splits;
  double current_set_entropy = getEntropy(pts, hd_mv, ind);
  for (unsigned i = 0, size = conds.size(); i < size; ++i)
  {
    std::pair<std::vector<Node>, std::vector<Node>> split =
        evaluateCond(pts, conds[i]);
    splits.push_back(split);
    Assert(pts.size() == split.first.size() + split.second.size());
    double gain =
        current_set_entropy
        - (split.first.size() * getEntropy(split.first, hd_mv, ind)
           + split.second.size() * getEntropy(split.second, hd_mv, ind))
              / pts.size();
    indent("sygus-unif-dt-debug", ind);
    Trace("sygus-unif-dt-debug") << "..gain of "
                           << d_dt->d_unif->d_tds->sygusToBuiltin(
                                  conds[i], conds[i].getType())
                           << " is " << gain << "\n";
    if (gain > maxgain)
    {
      maxgain = gain;
      picked_cond = i;
    }
  }
  // add picked condition
  indent("sygus-unif-dt", ind);
  Trace("sygus-unif-dt") << "..picked condition "
                         << d_dt->d_unif->d_tds->sygusToBuiltin(
                                conds[picked_cond],
                                conds[picked_cond].getType())
                         << "\n";
  d_dt->d_conds.push_back(conds[picked_cond]);
  conds.erase(conds.begin() + picked_cond);
  d_trie.addClassifier(this, d_dt->d_conds.size() - 1);
  // recurse
  buildDt(splits[picked_cond].first, conds, hd_mv,ind+1);
  buildDt(splits[picked_cond].second, conds, hd_mv,ind+1);
}

std::pair<std::vector<Node>, std::vector<Node>>
SygusUnifRl::DecisionTreeInfo::PointSeparator::evaluateCond(
    std::vector<Node>& pts, Node cond)
{
  std::vector<Node> good, bad;
  for (const Node& pt : pts)
  {
    if (computeCond(cond, pt) == d_true)
    {
      good.push_back(pt);
      continue;
    }
    Assert(computeCond(cond, pt) == d_false);
    bad.push_back(pt);
  }
  return std::pair<std::vector<Node>, std::vector<Node>>(good, bad);
}

double SygusUnifRl::DecisionTreeInfo::PointSeparator::getEntropy(
    const std::vector<Node>& pts, std::map<Node, Node>& hd_mv, int ind)
{
  double p = 0, n = 0;
  double u_p = 0, u_n = 0, i_p = 0, i_n = 0;
  std::vector<Node> pts_u_p, pts_u_n, pts_i_p, pts_i_n;
  // get number of good and bad points
  for (const Node& e : pts)
  {
    if (d_dt->d_unif->d_tds->sygusToBuiltin(hd_mv[e]) == d_true)
    {
      p++;
      if (Trace.isOn("sygus-unif-dt-debug"))
      {
        if (std::find(
                d_dt->d_hds_entailed.begin(), d_dt->d_hds_entailed.end(), e)
            == d_dt->d_hds_entailed.end())
        {
          i_p++;
          pts_i_p.push_back(e);
        }
        else
        {
          u_p++;
          pts_u_p.push_back(e);
        }
      }
      continue;
    }
    Assert(d_dt->d_unif->d_tds->sygusToBuiltin(hd_mv[e]) == d_false);
    n++;
    if (Trace.isOn("sygus-unif-dt-debug"))
    {
      if (std::find(d_dt->d_hds_entailed.begin(), d_dt->d_hds_entailed.end(), e)
          == d_dt->d_hds_entailed.end())
      {
        i_n++;
        pts_i_n.push_back(e);
      }
      else
      {
        u_n++;
        pts_u_n.push_back(e);
      }
    }
  }
  if (Trace.isOn("sygus-unif-dt-debug"))
  {
    indent("sygus-unif-dt-debug", ind + 2);
    Trace("sygus-unif-dt-debug")
        << "split was G : " << u_p << " | B : " << u_n << " | I_+ : " << i_p
        << " | I_- : " << i_n << "\n";
    if (!pts_u_p.empty())
    {
      indent("sygus-unif-dt-debug", ind + 2);
      Trace("sygus-unif-dt-debug") << "..  G : " << pts_u_p << "\n";
    }
    if (!pts_u_n.empty())
    {
      indent("sygus-unif-dt-debug", ind + 2);
      Trace("sygus-unif-dt-debug") << "..  B : " << pts_u_n << "\n";
    }
    if (!pts_i_p.empty())
    {
      indent("sygus-unif-dt-debug", ind + 2);
      Trace("sygus-unif-dt-debug") << "..I_+ : " << pts_i_p << "\n";
    }
    if (!pts_i_n.empty())
    {
      indent("sygus-unif-dt-debug", ind + 2);
      Trace("sygus-unif-dt-debug") << "..I_- : " << pts_i_n << "\n";
    }
  }
  return p == 0 || n == 0 ? 0 : ((-p / (p + n)) * log2(p / (p + n)))
                                    - ((n / (p + n)) * log2(n / (p + n)));
}

Node SygusUnifRl::DecisionTreeInfo::repairConditionToSeparate(Node cv,
                                                              Node e1,
                                                              Node e2)
{
  if (!options::sygusUnifRepairCond() && !SygusRepairConst::mustRepair(cv))
  {
    return cv;
  }
  NodeManager* nm = NodeManager::currentNM();
  // repair condition
  SygusRepairConst src(d_unif->d_qe);
  Node t[2];
  for (unsigned i = 0; i < 2; i++)
  {
    Node ei = i == 0 ? e1 : e2;
    std::map<Node, std::vector<Node>>::iterator it =
        d_unif->d_hd_to_pt.find(ei);
    Assert(it != d_unif->d_hd_to_pt.end());
    std::vector<Node> children;
    children.push_back(cv);
    children.insert(children.end(), it->second.begin(), it->second.end());
    t[i] = nm->mkNode(DT_SYGUS_EVAL, children);
  }
  Node deq = t[0].eqNode(t[1]).negate();
  Trace("sygus-unif-sol") << "Try to repair to satisfy : " << deq << std::endl;
  std::vector<Node> values;
  values.push_back(cv);
  src.initialize(deq, values);
  std::vector<Node> repair_values;
  if (src.repairValues(values, repair_values))
  {
    Assert(repair_values.size() == 1);
    Node cvr = repair_values[0];
    if (Trace.isOn("sygus-unif-sol"))
    {
      Trace("sygus-unif-sol") << "Repaired ";
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, cv);
      Trace("sygus-unif-sol") << ss.str() << " to ";
      std::stringstream ssr;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ssr, cvr);
      Trace("sygus-unif-sol") << ssr.str() << " to separate points:\n";
      for (unsigned i = 0; i < 2; i++)
      {
        Node ei = i == 0 ? e1 : e2;
        std::map<Node, std::vector<Node>>::iterator it =
            d_unif->d_hd_to_pt.find(ei);
        Trace("sygus-unif-sol") << "  " << it->second << std::endl;
      }
    }
    return cvr;
  }
  Trace("sygus-unif-sol") << "...failed." << std::endl;
  return cv;
}

bool SygusUnifRl::DecisionTreeInfo::pickCondition(unsigned c_counter,
                                                  Node e1,
                                                  Node e2,
                                                  std::vector<Node>& exp)
{
  bool has_enum_cv = c_counter < d_enums.size();
  bool pickedCond = has_enum_cv;
  // try enumerated condition, if any
  if (has_enum_cv)
  {
    Node ce = d_enums[c_counter];
    Node cv = d_conds[c_counter];
    Assert(ce.getType() == cv.getType());
    if (Trace.isOn("sygus-unif-sol"))
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, cv);
      Trace("sygus-unif-sol") << "  add condition (" << c_counter << "/"
                              << d_conds.size() << "): " << ce << " -> "
                              << ss.str() << std::endl;
    }
    cv = repairConditionToSeparate(cv, e1, e2);
    d_conds[c_counter] = cv;
    // add to explanation
    // c_exp is a conjunction of testers applied to shared selector chains
    Node c_exp = d_unif->d_tds->getExplain()->getExplanationForEquality(ce, cv);
    exp.push_back(c_exp);
  }
  // if (repaired) condition, if any, still does not separate heads, try
  // condition pool
  if (options::sygusUnifCondPool()
      && (!has_enum_cv
          || d_pt_sep.evaluate(e1, c_counter)
                 == d_pt_sep.evaluate(e2, c_counter))
      && pickConditionFromPool(c_counter, e1, e2))
  {
    // set the index if not already set
    if (d_exp_backtrack_size == -1)
    {
      // set to index of the condition enum being equal to the respectively
      // failed model value, to be computed below in c_exp
      d_exp_backtrack_size = exp.size();
    }
    pickedCond = true;
  }
  return pickedCond;
}

bool SygusUnifRl::DecisionTreeInfo::pickConditionFromPool(unsigned c_counter,
                                                          Node e1,
                                                          Node e2)
{
  if (Trace.isOn("sygus-unif-cond-pool-debug"))
  {
    Trace("sygus-unif-cond-pool-debug")
        << "  ...try separating " << e1 << d_unif->d_hd_to_pt[e1] << " | " << e2
        << d_unif->d_hd_to_pt[e2] << " with pool";
    for (const Node& condv : d_cond_mvs)
    {
      Trace("sygus-unif-cond-pool-debug")
          << " " << d_unif->d_tds->sygusToBuiltin(condv, condv.getType());
    }
    Trace("sygus-unif-cond-pool-debug") << "\n";
  }
  // increase number of conditions if necessary
  Assert(c_counter <= d_conds.size());
  if (c_counter == d_conds.size())
  {
    d_conds.resize(c_counter + 1);
  }
  for (const Node& cond : d_cond_mvs)
  {
    d_conds[c_counter] = cond;
    if (d_pt_sep.evaluate(e1, c_counter) != d_pt_sep.evaluate(e2, c_counter))
    {
      Trace("sygus-unif-cond-pool")
          << "  ...picked from pool "
          << d_unif->d_tds->sygusToBuiltin(cond, cond.getType())
          << " to separate " << e1;
      Trace("sygus-unif-cond-pool-debug") << d_unif->d_hd_to_pt[e1];
      Trace("sygus-unif-cond-pool") << " | " << e2;
      Trace("sygus-unif-cond-pool-debug") << d_unif->d_hd_to_pt[e2];
      Trace("sygus-unif-cond-pool") << "\n";
      return true;
    }
  }
  return false;
}

void SygusUnifRl::DecisionTreeInfo::addHeadValuePool(Node hd, Node hdv)
{
  if (!options::sygusUnifRetPool())
  {
    return;
  }
  TypeNode tn = hd.getType();
  Node builtin_hdv = d_unif->d_tds->sygusToBuiltin(hdv, tn);
  // compute the result hdv on hd's point
  d_hd_appCurrEval[hd] =
      d_unif->d_tds->evaluateBuiltin(tn, builtin_hdv, d_unif->d_hd_to_pt[hd]);
  // if new value, add to hd's pool and all other hd pools
  if (d_hd_mvs.find(hdv) != d_hd_mvs.end())
  {
    return;
  }
  d_hd_mvs.insert(hdv);
  // add value to each head of type tn, including input hd
  Trace("sygus-unif-sol-debug") << "  ...new pool value: " << builtin_hdv
                                << "\n";
  for (const Node& hdi : d_hds)
  {
    Node res = d_unif->d_tds->evaluateBuiltin(
        tn, builtin_hdv, d_unif->d_hd_to_pt[hdi]);
    if (Trace.isOn("sygus-unif-sol-debug"))
    {
      Trace("sygus-unif-sol-debug") << "  ......" << hdi
                                    << d_unif->d_hd_to_pt[hdi] << " --> "
                                    << "[" << res << "] = [";
      for (const Node& v : d_hd_equiv_mvs[hdi][res])
      {
        Trace("sygus-unif-sol-debug") << " "
                                      << d_unif->d_tds->sygusToBuiltin(v, tn);
      }
      Trace("sygus-unif-sol-debug") << " ] <+ " << builtin_hdv << "\n";
    }
    d_hd_equiv_mvs[hdi][res].insert(hdv);
  }
}

Node SygusUnifRl::DecisionTreeInfo::mergeHeadValuePools(
    Node hd,
    const std::vector<Node>& hds,
    std::vector<Node>& exp,
    std::vector<Node>& lemmas)
{
  std::set<Node> merged_pool = d_hd_equiv_mvs[hd][d_hd_appCurrEval[hd]];
  for (const Node& hdi : hds)
  {
    std::set<Node> next_pool;
    set_intersection(merged_pool.begin(),
                     merged_pool.end(),
                     d_hd_equiv_mvs[hdi][d_hd_appCurrEval[hdi]].begin(),
                     d_hd_equiv_mvs[hdi][d_hd_appCurrEval[hdi]].end(),
                     std::inserter(next_pool, next_pool.begin()));
    Trace("sygus-unif-sol-debug2")
        << "...... to merge : " << merged_pool << "\n...... with\n...... "
        << d_hd_equiv_mvs[hdi][d_hd_appCurrEval[hdi]]
        << "\n...... yields\n...... " << next_pool << "\n";
    merged_pool.clear();
    merged_pool = next_pool;
    if (merged_pool.empty())
    {
      exp.push_back(
          makeEvalExp(hdi, hd, d_unif->d_hd_to_pt[hdi], lemmas, false));
      Trace("sygus-unif-sol-debug") << "  ......couldn't merge " << hd
                                    << " with " << hdi << "\n";
      Trace("sygus-unif-sol-debug") << "  ...add to explanation " << exp.back()
                                    << "\n";
      return Node::null();
    }
  }
  // add to explanation equalities of repaired heads and their original
  // model values
  exp.push_back(makeEvalExp(hds[0], hd, d_unif->d_hd_to_pt[hds[0]], lemmas));
  Trace("sygus-unif-sol") << "  ...common value "
                          << d_unif->d_tds->sygusToBuiltin(
                                 *merged_pool.begin(),
                                 merged_pool.begin()->getType())
                          << "\n  ...add to explanation " << exp.back() << "\n";
  return *merged_pool.begin();
}

Node SygusUnifRl::DecisionTreeInfo::makeEvalExp(Node e1,
                                                Node e2,
                                                const std::vector<Node>& pt_e1,
                                                std::vector<Node>& lemmas,
                                                bool equal)
{
  NodeManager* nm = NodeManager::currentNM();
  // build (ev e1 pt_e1)
  Node ev_e1;
  std::vector<Node> e1_children;
  e1_children.push_back(e1);
  e1_children.insert(e1_children.end(), pt_e1.begin(), pt_e1.end());
  ev_e1 = nm->mkNode(DT_SYGUS_EVAL, e1_children);
  // build (ev e2 pt_e1)
  Node ev_e2;
  std::vector<Node> e2_children;
  e2_children.push_back(e2);
  e2_children.insert(e2_children.end(), pt_e1.begin(), pt_e1.end());
  ev_e2 = nm->mkNode(DT_SYGUS_EVAL, e2_children);
  // when creating equalities, add unfolding lemmas to new evaluation point
  // based on e2's equivalent values modulo return value
  if (equal)
  {
    Node adhoc_ev_eq = nm->mkNode(EQUAL, ev_e2, d_hd_appCurrEval[e1]);
    for (const Node& e2_mv : d_hd_equiv_mvs[e2][d_hd_appCurrEval[e2]])
    {
      Node exp =
          d_unif->d_tds->getExplain()->getExplanationForEquality(e2, e2_mv);
      Node unfold_lemma = nm->mkNode(OR, exp.negate(), adhoc_ev_eq);
      // TODO improve this
      // if fresh lemma, add it
      if (d_adhoc_unfolding_lemmas.find(unfold_lemma)
          == d_adhoc_unfolding_lemmas.end())
      {
        d_adhoc_unfolding_lemmas.insert(unfold_lemma);
        lemmas.push_back(unfold_lemma);
        Trace("sygus-unif-sol-debug")
            << "......adhoc unfolding lemma: "
            << nm->mkNode(OR,
                          nm->mkNode(EQUAL,
                                     e2,
                                     d_unif->d_tds->sygusToBuiltin(
                                         e2_mv, e2_mv.getType()))
                              .negate(),
                          adhoc_ev_eq)
            << "\n";
      }
    }
  }
  // create equality
  Node eq = nm->mkNode(EQUAL, ev_e1, ev_e2);
  return equal ? eq : eq.negate();
}

void SygusUnifRl::DecisionTreeInfo::PointSeparator::initialize(
    DecisionTreeInfo* dt)
{
  d_dt = dt;
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Node SygusUnifRl::DecisionTreeInfo::PointSeparator::evaluate(Node n,
                                                             unsigned index)
{
  Assert(index < d_dt->d_conds.size());
  // Retrieve respective built_in condition
  Node cond = d_dt->d_conds[index];
  return computeCond(cond, n);
}

Node SygusUnifRl::DecisionTreeInfo::PointSeparator::computeCond(Node cond,
                                                                Node hd)
{
  std::pair<Node, Node> cond_hd = std::pair<Node, Node>(cond, hd);
  std::map<std::pair<Node, Node>, Node>::iterator it =
      d_eval_cond_hd.find(cond_hd);
  if (it != d_eval_cond_hd.end())
  {
    return it->second;
  }
  TypeNode tn = cond.getType();
  Node builtin_cond = d_dt->d_unif->d_tds->sygusToBuiltin(cond, tn);
  // Retrieve evaluation point
  Assert(d_dt->d_unif->d_hd_to_pt.find(hd) != d_dt->d_unif->d_hd_to_pt.end());
  std::vector<Node> pt = d_dt->d_unif->d_hd_to_pt[hd];
  // compute the result
  if (Trace.isOn("sygus-unif-rl-sep"))
  {
    Trace("sygus-unif-rl-sep") << "Evaluate cond " << builtin_cond << " on pt "
                               << hd << " ( ";
    for (const Node& pti : pt)
    {
      Trace("sygus-unif-rl-sep") << pti << " ";
    }
    Trace("sygus-unif-rl-sep") << ")\n";
  }
  Node res = d_dt->d_unif->d_tds->evaluateBuiltin(tn, builtin_cond, pt);
  Trace("sygus-unif-rl-sep") << "...got res = " << res << "\n";
  // If condition is templated, recompute result accordingly
  Node templ = d_dt->d_template.first;
  TNode templ_var = d_dt->d_template.second;
  if (!templ.isNull())
  {
    res = templ.substitute(templ_var, res);
    res = Rewriter::rewrite(res);
    Trace("sygus-unif-rl-sep") << "...after template res = " << res
                               << std::endl;
  }
  Assert(res.isConst());
  d_eval_cond_hd[cond_hd] = res;
  return res;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
