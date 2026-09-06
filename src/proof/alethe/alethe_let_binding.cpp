/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The implementation of the module for Alethe let binding.
 */

#include "proof/alethe/alethe_let_binding.h"

#include "expr/node_algorithm.h"

#include <algorithm>

#include <sstream>

namespace cvc5::internal {

namespace proof {

// Binders are traversed so that closed subterms occurring under them can be
// shared: a term with no free bound variable may be named at its first
// occurrence, be it under a binder, and referenced by name anywhere after,
// while terms mentioning bound variables are never shared (see sharedId).
AletheLetBinding::AletheLetBinding(uint32_t thresh)
    : LetBinding("let", thresh, true)
{
}

uint32_t AletheLetBinding::sharedId(TNode n)
{
  uint32_t id = getId(n);
  return (id > 0 && isOpen(n)) ? 0 : id;
}

bool AletheLetBinding::isOpen(TNode n)
{
  auto itc = d_open.find(n);
  if (itc != d_open.end())
  {
    return itc->second;
  }
  // The free bound variables of each subterm, computed bottom-up. Besides
  // cvc5's closures, the converted choice terms, applications of the choice
  // operator to a bound variable list and a body, bind their variables.
  auto boundList = [](TNode t) -> TNode {
    if (t.isClosure())
    {
      return t[0];
    }
    if (t.getKind() == Kind::APPLY_UF && t.getNumChildren() == 2
        && t[0].getKind() == Kind::BOUND_VAR_LIST)
    {
      return t[0];
    }
    return TNode::null();
  };
  std::unordered_map<TNode, std::vector<Node>> freeVars;
  std::vector<TNode> visit{n};
  while (!visit.empty())
  {
    TNode cur = visit.back();
    if (freeVars.find(cur) != freeVars.end())
    {
      visit.pop_back();
      continue;
    }
    auto ito = d_open.find(cur);
    if (cur.getKind() == Kind::BOUND_VARIABLE)
    {
      freeVars[cur] = {cur};
      visit.pop_back();
      continue;
    }
    if (cur.getKind() == Kind::BOUND_VAR_LIST || cur.getNumChildren() == 0
        || (ito != d_open.end() && !ito->second))
    {
      freeVars[cur] = {};
      visit.pop_back();
      continue;
    }
    bool ready = true;
    for (const Node& c : cur)
    {
      if (freeVars.find(c) == freeVars.end())
      {
        if (ready)
        {
          ready = false;
        }
        visit.push_back(c);
      }
    }
    if (!ready)
    {
      continue;
    }
    visit.pop_back();
    std::vector<Node> fv;
    for (const Node& c : cur)
    {
      const std::vector<Node>& cfv = freeVars[c];
      fv.insert(fv.end(), cfv.begin(), cfv.end());
    }
    TNode bl = boundList(cur);
    if (!bl.isNull())
    {
      fv.erase(std::remove_if(fv.begin(),
                              fv.end(),
                              [&bl](const Node& v) {
                                return std::find(bl.begin(), bl.end(), v)
                                       != bl.end();
                              }),
               fv.end());
    }
    std::sort(fv.begin(), fv.end());
    fv.erase(std::unique(fv.begin(), fv.end()), fv.end());
    d_open[cur] = !fv.empty();
    freeVars[cur] = std::move(fv);
  }
  return d_open[n];
}

Node AletheLetBinding::convert(NodeManager* nm,
                               Node n,
                               const std::string& prefix)
{
  if (d_letMap.empty())
  {
    return n;
  }
  // A shared term is declared, (! t :named @p_i), at its first occurrence in
  // the whole proof and referenced by name afterwards. The declaration is
  // confined to that first occurrence: the parent and child position at
  // which a term is first reached record where its declaring conversion
  // (declaredValue) is used; every other occurrence uses its plain
  // conversion (visited), the name. A term that is itself not shared but
  // whose conversion embeds a declaration of a descendant (a "carrier")
  // needs the same treatment, since it may be shared in the term DAG and
  // otherwise would re-embed the declaration at each of its occurrences.
  std::unordered_map<TNode, size_t> firstPosition;
  std::unordered_map<TNode, TNode> parentOf;
  std::unordered_map<TNode, Node> declaredValue;
  std::unordered_set<TNode> declaresAtParent;
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  // the traversal stack carries, with each term, the parent and the child
  // position through which it is reached, so that a term's first reach in
  // pre-order — its first occurrence in the printed term — is recorded
  struct Entry
  {
    TNode d_node;
    TNode d_parent;
    size_t d_pos;
  };
  std::vector<Entry> visit;
  TNode cur;
  visit.push_back({n, TNode::null(), 0});
  do
  {
    Entry entry = visit.back();
    cur = entry.d_node;
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (!entry.d_parent.isNull() && parentOf.find(cur) == parentOf.end())
      {
        parentOf[cur] = entry.d_parent;
        firstPosition[cur] = entry.d_pos;
      }
      uint32_t id = sharedId(cur);
      // do not letify partially applied terms, which may have been generated
      // during RARE elaboration.
      if (cur.getKind() == Kind::HO_APPLY && cur.getType().isFunction())
      {
        visited[cur] = cur;
        continue;
      }
      if (id > 0)
      {
        Trace("alethe-printer-share")
            << "Node " << cur << " has id " << id << "\n";
        // already declared, in this or a previous conversion: use the name
        if (d_declared.find(cur) != d_declared.end())
        {
          std::stringstream ss;
          ss << prefix << id;
          visited[cur] = NodeManager::mkBoundVar(ss.str(), cur.getType());
          Trace("alethe-printer-share")
              << "\tdeclared, use var " << visited[cur] << "\n";
          continue;
        }
        // this occurrence, the first, declares it
        d_declared.insert(cur);
        declaresAtParent.insert(cur);
      }
      visited[cur] = Node::null();
      visit.push_back(entry);
      // children are added in reverse order, so that they are visited left
      // to right
      for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
      {
        visit.push_back({cur[size - i - 1], cur, size - i - 1});
      }
    }
    else if (it->second.isNull())
    {
      // post-visit: build the plain conversion and, if some child is
      // declared here, the declaring one
      std::vector<Node> plain, declaring;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        plain.push_back(cur.getOperator());
        declaring.push_back(cur.getOperator());
      }
      bool declaresChild = false;
      bool childChanged = false;
      for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
      {
        it = visited.find(cur[i]);
        Assert(it != visited.end() && !it->second.isNull())
            << "With input " << n << " did not find for term " << cur
            << " its child " << cur[i] << "\n";
        childChanged = childChanged || cur[i] != it->second;
        plain.push_back(it->second);
        if (declaresAtParent.count(cur[i]) && parentOf[cur[i]] == cur
            && firstPosition[cur[i]] == i)
        {
          Assert(declaredValue.find(cur[i]) != declaredValue.end());
          declaring.push_back(declaredValue[cur[i]]);
          declaresChild = true;
          continue;
        }
        declaring.push_back(it->second);
      }
      Node ret = childChanged ? nm->mkNode(cur.getKind(), plain) : Node(cur);
      Node retDeclaring =
          declaresChild ? nm->mkNode(cur.getKind(), declaring) : ret;
      uint32_t id = sharedId(cur);
      if (id > 0)
      {
        // declare the (declaring) conversion; later occurrences use the name
        std::stringstream ss, ssVar;
        ss << "(! ";
        options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
        options::ioutils::applyDagThresh(ss, 0);
        options::ioutils::applyPrintArithLitToken(ss, true);
        options::ioutils::applyFlattenHOChains(ss, true);
        retDeclaring.toStream(ss);
        ssVar << prefix << id;
        ss << " :named " << ssVar.str() << ")";
        Node declaration =
            NodeManager::mkRawSymbol(ss.str(), retDeclaring.getType());
        declaredValue[cur] = declaration;
        visited[cur] = NodeManager::mkBoundVar(ssVar.str(), cur.getType());
        continue;
      }
      if (declaresChild)
      {
        // a carrier: its first occurrence embeds the declaration
        declaredValue[cur] = retDeclaring;
        declaresAtParent.insert(cur);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  auto itd = declaredValue.find(n);
  return itd != declaredValue.end() ? itd->second : visited[n];
}

}  // namespace proof
}  // namespace cvc5::internal
