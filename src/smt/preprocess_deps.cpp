/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the tracking of the input formulas that preprocessed
 * formulas depend on.
 */

#include "smt/preprocess_deps.h"

#include <algorithm>
#include <iterator>

#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace smt {

PreprocessDeps::PreprocessDeps(Env& env)
    : EnvObj(env),
      d_hasSubsSource(false),
      d_subsSource(ALL),
      d_allSet(std::make_shared<const std::vector<DepId>>()),
      d_emptySet(std::make_shared<const std::vector<DepId>>()),
      d_numFormulas(
          statisticsRegistry().registerInt("smt::PreprocessDeps::numFormulas")),
      d_numUnknown(
          statisticsRegistry().registerInt("smt::PreprocessDeps::numUnknown"))
{
  // the node depending on all inputs
  mkNodeInternal(DepNode());
  d_deps[ALL] = d_allSet;
}

PreprocessDeps::~PreprocessDeps() {}

PreprocessDeps::DepId PreprocessDeps::mkNodeInternal(DepNode&& dn)
{
  DepId id = static_cast<DepId>(d_nodes.size());
  d_nodes.emplace_back(std::move(dn));
  d_deps.emplace_back(nullptr);
  d_inputFormula.emplace_back();
  return id;
}

PreprocessDeps::DepId PreprocessDeps::registerFormula(const Node& n,
                                                      DepNode&& dn)
{
  Assert(d_formulaIds.find(n) == d_formulaIds.end());
  DepId id = mkNodeInternal(std::move(dn));
  d_formulaIds[n] = id;
  ++d_numFormulas;
  return id;
}

void PreprocessDeps::notifyInput(const Node& n)
{
  if (d_formulaIds.find(n) != d_formulaIds.end())
  {
    return;
  }
  Trace("pp-deps") << "PreprocessDeps::notifyInput: " << n << std::endl;
  DepNode dn;
  dn.d_isInput = true;
  DepId id = registerFormula(n, std::move(dn));
  d_inputFormula[id] = n;
  d_inputs.push_back(id);
}

void PreprocessDeps::notifyNewAssert(const Node& n,
                                     std::vector<DepId>&& premises)
{
  if (d_formulaIds.find(n) != d_formulaIds.end())
  {
    return;
  }
  Trace("pp-deps") << "PreprocessDeps::notifyNewAssert: " << n << " from "
                   << premises.size() << " premises" << std::endl;
  DepNode dn;
  dn.d_premises = std::move(premises);
  registerFormula(n, std::move(dn));
}

void PreprocessDeps::notifyPreprocessed(const Node& n, const Node& np, bool all)
{
  std::unordered_map<Node, std::vector<SubsPrefix>>::iterator its =
      d_subsApply.find(np);
  std::vector<SubsPrefix> subs;
  if (its != d_subsApply.end())
  {
    subs = std::move(its->second);
    d_subsApply.erase(its);
  }
  if (d_formulaIds.find(np) != d_formulaIds.end())
  {
    return;
  }
  Trace("pp-deps") << "PreprocessDeps::notifyPreprocessed: " << n << " to "
                   << np << (all ? " (all)" : "") << std::endl;
  DepNode dn;
  dn.d_premises.push_back(getId(n));
  if (all)
  {
    dn.d_premises.push_back(ALL);
    ++d_numUnknown;
  }
  dn.d_subs = std::move(subs);
  registerFormula(np, std::move(dn));
}

PreprocessDeps::DepId PreprocessDeps::getId(const Node& n)
{
  std::unordered_map<Node, DepId>::const_iterator it = d_formulaIds.find(n);
  if (it != d_formulaIds.end())
  {
    return it->second;
  }
  Trace("pp-deps") << "PreprocessDeps::getId: unknown formula " << n
                   << ", assume it depends on all inputs" << std::endl;
  ++d_numUnknown;
  DepNode dn;
  dn.d_premises.push_back(ALL);
  return registerFormula(n, std::move(dn));
}

PreprocessDeps::DepId PreprocessDeps::mkNode(std::vector<DepId>&& premises)
{
  DepNode dn;
  dn.d_premises = std::move(premises);
  return mkNodeInternal(std::move(dn));
}

PreprocessDeps::DepId PreprocessDeps::mkNode(std::vector<DepId>&& premises,
                                             size_t m)
{
  Assert(m < d_maps.size());
  DepNode dn;
  dn.d_premises = std::move(premises);
  dn.d_subs.emplace_back(m, d_maps[m].d_sources.size());
  return mkNodeInternal(std::move(dn));
}

size_t PreprocessDeps::registerSubstitutionMap()
{
  d_maps.emplace_back();
  return d_maps.size() - 1;
}

void PreprocessDeps::setSubstitutionSource(const Node& n)
{
  setSubstitutionSource(getId(n));
}

void PreprocessDeps::setSubstitutionSource(DepId id)
{
  d_hasSubsSource = true;
  d_subsSource = id;
}

void PreprocessDeps::clearSubstitutionSource() { d_hasSubsSource = false; }

void PreprocessDeps::notifySubstitution(size_t m, const Node& hint)
{
  Assert(m < d_maps.size());
  DepId src = ALL;
  if (d_hasSubsSource)
  {
    src = d_subsSource;
  }
  else
  {
    std::unordered_map<Node, DepId>::const_iterator it =
        hint.isNull() ? d_formulaIds.end() : d_formulaIds.find(hint);
    if (it != d_formulaIds.end())
    {
      src = it->second;
    }
    else
    {
      ++d_numUnknown;
    }
  }
  Trace("pp-deps") << "PreprocessDeps::notifySubstitution: map " << m << " #"
                   << d_maps[m].d_sources.size() << " from " << src
                   << std::endl;
  d_maps[m].d_sources.push_back(src);
}

void PreprocessDeps::notifySubstitutionsUnknown(size_t m, size_t n)
{
  Assert(m < d_maps.size());
  d_numUnknown += n;
  d_maps[m].d_sources.insert(d_maps[m].d_sources.end(), n, ALL);
}

void PreprocessDeps::notifySubstitutionsMerged(size_t dst, size_t src)
{
  Assert(dst < d_maps.size() && src < d_maps.size() && dst != src);
  const std::vector<DepId>& srcs = d_maps[src].d_sources;
  d_maps[dst].d_sources.insert(
      d_maps[dst].d_sources.end(), srcs.begin(), srcs.end());
}

void PreprocessDeps::notifySubstitutionApply(size_t m, const Node& np)
{
  Assert(m < d_maps.size());
  d_subsApply[np].emplace_back(m, d_maps[m].d_sources.size());
}

bool PreprocessDeps::isInput(const Node& n) const
{
  std::unordered_map<Node, DepId>::const_iterator it = d_formulaIds.find(n);
  return it != d_formulaIds.end() && d_nodes[it->second].d_isInput;
}

size_t PreprocessDeps::getPrefixStart(const SubsMap& sm, size_t size) const
{
  std::map<size_t, DepSet>::const_iterator it =
      sm.d_prefixDeps.upper_bound(size);
  return it == sm.d_prefixDeps.begin() ? 0 : std::prev(it)->first;
}

PreprocessDeps::DepSet PreprocessDeps::compute(DepId root)
{
  // Iterative post-order traversal. Note that the premises of a node, as well
  // as the sources of the substitutions it depends on, were created before it,
  // hence the graph is acyclic.
  std::vector<std::pair<DepId, bool>> visit{{root, false}};
  while (!visit.empty())
  {
    std::pair<DepId, bool>& cur = visit.back();
    DepId id = cur.first;
    if (d_deps[id] != nullptr)
    {
      visit.pop_back();
      continue;
    }
    if (cur.second)
    {
      visit.pop_back();
      d_deps[id] = combine(id);
      continue;
    }
    cur.second = true;
    const DepNode& dn = d_nodes[id];
    for (DepId p : dn.d_premises)
    {
      if (d_deps[p] == nullptr)
      {
        visit.emplace_back(p, false);
      }
    }
    for (const SubsPrefix& sp : dn.d_subs)
    {
      // only the sources after the longest cached prefix are needed
      const SubsMap& sm = d_maps[sp.first];
      for (size_t i = getPrefixStart(sm, sp.second); i < sp.second; ++i)
      {
        if (d_deps[sm.d_sources[i]] == nullptr)
        {
          visit.emplace_back(sm.d_sources[i], false);
        }
      }
    }
  }
  return d_deps[root];
}

PreprocessDeps::DepSet PreprocessDeps::combine(DepId id)
{
  const DepNode& dn = d_nodes[id];
  if (dn.d_isInput)
  {
    return std::make_shared<const std::vector<DepId>>(1, id);
  }
  std::vector<DepSet> sets;
  for (DepId p : dn.d_premises)
  {
    Assert(d_deps[p] != nullptr);
    sets.push_back(d_deps[p]);
  }
  for (const SubsPrefix& sp : dn.d_subs)
  {
    if (sp.second == 0)
    {
      continue;
    }
    SubsMap& sm = d_maps[sp.first];
    std::map<size_t, DepSet>::iterator it = sm.d_prefixDeps.find(sp.second);
    if (it == sm.d_prefixDeps.end())
    {
      // extend the longest cached prefix
      size_t start = getPrefixStart(sm, sp.second);
      std::vector<DepSet> psets;
      if (start > 0)
      {
        psets.push_back(sm.d_prefixDeps[start]);
      }
      for (size_t i = start; i < sp.second; ++i)
      {
        Assert(d_deps[sm.d_sources[i]] != nullptr);
        psets.push_back(d_deps[sm.d_sources[i]]);
      }
      it = sm.d_prefixDeps.emplace(sp.second, merge(psets)).first;
    }
    sets.push_back(it->second);
  }
  return merge(sets);
}

PreprocessDeps::DepSet PreprocessDeps::merge(const std::vector<DepSet>& sets)
{
  DepSet single;
  size_t total = 0;
  for (const DepSet& s : sets)
  {
    if (s == d_allSet)
    {
      return d_allSet;
    }
    if (!s->empty())
    {
      single = s;
      total += s->size();
    }
  }
  if (total == 0)
  {
    return d_emptySet;
  }
  if (total == single->size())
  {
    // only one non-empty set, share it
    return single;
  }
  std::vector<DepId> res;
  res.reserve(total);
  for (const DepSet& s : sets)
  {
    res.insert(res.end(), s->begin(), s->end());
  }
  std::sort(res.begin(), res.end());
  res.erase(std::unique(res.begin(), res.end()), res.end());
  return std::make_shared<const std::vector<DepId>>(std::move(res));
}

std::vector<Node> PreprocessDeps::getDependencies(const Node& n)
{
  std::vector<Node> res;
  std::unordered_map<Node, DepId>::const_iterator it = d_formulaIds.find(n);
  if (it == d_formulaIds.end())
  {
    return res;
  }
  DepSet ds = compute(it->second);
  const std::vector<DepId>& ids = ds == d_allSet ? d_inputs : *ds;
  for (DepId id : ids)
  {
    res.push_back(d_inputFormula[id]);
  }
  return res;
}

std::shared_ptr<ProofNode> PreprocessDeps::getProofFor(Node f)
{
  std::unordered_map<Node, DepId>::const_iterator it = d_formulaIds.find(f);
  if (it == d_formulaIds.end() || d_nodes[it->second].d_isInput)
  {
    // an input formula or a formula not from preprocessing, e.g., a scoped
    // assumption
    return nullptr;
  }
  std::vector<Node> deps = getDependencies(f);
  Trace("pp-deps") << "PreprocessDeps::getProofFor: " << f << " depends on "
                   << deps << std::endl;
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  std::vector<std::shared_ptr<ProofNode>> children;
  for (const Node& d : deps)
  {
    children.push_back(pnm->mkAssume(d));
  }
  return pnm->mkTrustedNode(TrustId::PREPROCESS_DEPS, children, {}, f);
}

std::string PreprocessDeps::identify() const { return "PreprocessDeps"; }

bool PreprocessDeps::isDepsStep(const ProofNode* pn)
{
  TrustId tid;
  return pn->getRule() == ProofRule::TRUST
         && getTrustId(pn->getArguments()[0], tid)
         && tid == TrustId::PREPROCESS_DEPS;
}

}  // namespace smt
}  // namespace cvc5::internal
