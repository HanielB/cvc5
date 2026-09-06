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

// Binders are traversed so that subterms occurring under them can be shared.
// A term may be named at an occurrence where none of its free variables is
// bound by a binder enclosing the occurrence in the converted term (its free
// variables are then in scope, e.g. bound by an anchor of the subproof being
// printed), and referenced by name at every such occurrence after. At the
// occurrences under a binder capturing one of its variables it is printed in
// full, since the name would not denote the same term there (see convert).
AletheLetBinding::AletheLetBinding(uint32_t thresh)
    : LetBinding("let", thresh, true)
{
}

// The variables bound by t, if it is a binder: cvc5's closures, and the
// converted choice terms, applications of the choice operator to a bound
// variable list and a body.
static TNode boundList(TNode t)
{
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
}

const std::vector<Node>& AletheLetBinding::freeVars(TNode n)
{
  auto itc = d_freeVars.find(n);
  if (itc != d_freeVars.end())
  {
    return itc->second;
  }
  // computed bottom-up, removing at each binder the variables it binds
  std::vector<TNode> visit{n};
  while (!visit.empty())
  {
    TNode cur = visit.back();
    if (d_freeVars.find(cur) != d_freeVars.end())
    {
      visit.pop_back();
      continue;
    }
    if (cur.getKind() == Kind::BOUND_VARIABLE)
    {
      d_freeVars[cur] = {cur};
      visit.pop_back();
      continue;
    }
    if (cur.getKind() == Kind::BOUND_VAR_LIST || cur.getNumChildren() == 0)
    {
      d_freeVars[cur] = {};
      visit.pop_back();
      continue;
    }
    bool ready = true;
    for (const Node& c : cur)
    {
      if (d_freeVars.find(c) == d_freeVars.end())
      {
        ready = false;
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
      const std::vector<Node>& cfv = d_freeVars[c];
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
    d_freeVars[cur] = std::move(fv);
  }
  return d_freeVars[n];
}

Node AletheLetBinding::keyOf(NodeManager* nm,
                             TNode n,
                             const std::vector<Node>& bound)
{
  if (bound.empty())
  {
    return n;
  }
  const std::vector<Node>& fv = freeVars(n);
  std::vector<Node> captured{n};
  for (const Node& v : fv)
  {
    if (std::find(bound.begin(), bound.end(), v) != bound.end())
    {
      captured.push_back(v);
    }
  }
  return captured.size() == 1 ? Node(n) : nm->mkNode(Kind::SEXPR, captured);
}

Node AletheLetBinding::convert(NodeManager* nm,
                               Node n,
                               const std::string& prefix)
{
  if (d_letMap.empty())
  {
    return n;
  }
  using BoundVars = std::shared_ptr<const std::vector<Node>>;
  // A shared term is declared, (! t :named @p_i), at its first occurrence in
  // the whole proof at which it may be named, and referenced by name at the
  // such occurrences afterwards. An occurrence is converted under a key
  // (keyOf): the term itself when none of its free variables is bound by a
  // binder enclosing the occurrence, in which case it may be named; a pairing
  // of the term with the captured variables otherwise, in which case it is
  // printed in full (its subterms may still be named). The conversion of a
  // key is the same wherever it occurs, since the keys of the children are
  // determined by the key of the parent.
  //
  // The declaration is confined to the first occurrence: the parent key and
  // child position at which a key is first reached record where its
  // declaring conversion (declaredValue) is used; every other occurrence uses
  // its plain conversion (visited), the name. A term that is itself not
  // named but whose conversion embeds a declaration of a descendant (a
  // "carrier") needs the same treatment, since it may be shared in the term
  // DAG and otherwise would re-embed the declaration at each of its
  // occurrences.
  std::unordered_map<Node, size_t> firstPosition;
  std::unordered_map<Node, Node> parentOf;
  std::unordered_map<Node, Node> declaredValue;
  std::unordered_set<Node> declaresAtParent;
  std::unordered_map<Node, Node> visited;
  std::unordered_map<Node, Node>::iterator it;
  // the traversal stack carries, with each term, the key of the parent and
  // the child position through which it is reached, so that a key's first
  // reach in pre-order — its first occurrence in the printed term — is
  // recorded, and the variables bound by the enclosing binders; when
  // re-pushed for its post-visit an entry also carries its own key and the
  // bound variables of its children
  struct Entry
  {
    TNode d_node;
    Node d_parentKey;
    size_t d_pos;
    BoundVars d_bound;
    Node d_key;
    BoundVars d_childBound;
  };
  std::vector<Entry> visit;
  BoundVars noBound = std::make_shared<const std::vector<Node>>();
  TNode cur;
  visit.push_back({n, Node::null(), 0, noBound, Node::null(), nullptr});
  do
  {
    Entry entry = visit.back();
    cur = entry.d_node;
    visit.pop_back();
    if (entry.d_key.isNull())
    {
      Node key = keyOf(nm, cur, *entry.d_bound);
      it = visited.find(key);
      if (it != visited.end())
      {
        continue;
      }
      if (!entry.d_parentKey.isNull()
          && parentOf.find(key) == parentOf.end())
      {
        parentOf[key] = entry.d_parentKey;
        firstPosition[key] = entry.d_pos;
      }
      // do not letify partially applied terms, which may have been generated
      // during RARE elaboration.
      if (cur.getKind() == Kind::HO_APPLY && cur.getType().isFunction())
      {
        visited[key] = cur;
        continue;
      }
      // nameable here iff no free variable is captured, i.e. key == cur
      uint32_t id = key == cur ? getId(cur) : 0;
      if (id > 0)
      {
        Trace("alethe-printer-share")
            << "Node " << cur << " has id " << id << "\n";
        // already declared, in this or a previous conversion: use the name
        if (d_declared.find(cur) != d_declared.end())
        {
          std::stringstream ss;
          ss << prefix << id;
          visited[key] = NodeManager::mkBoundVar(ss.str(), cur.getType());
          Trace("alethe-printer-share")
              << "\tdeclared, use var " << visited[key] << "\n";
          continue;
        }
        // this occurrence, the first, declares it
        d_declared.insert(cur);
        declaresAtParent.insert(key);
      }
      visited[key] = Node::null();
      TNode bl = boundList(cur);
      BoundVars childBound = entry.d_bound;
      if (!bl.isNull())
      {
        std::vector<Node> vars(entry.d_bound->begin(), entry.d_bound->end());
        vars.insert(vars.end(), bl.begin(), bl.end());
        childBound = std::make_shared<const std::vector<Node>>(std::move(vars));
      }
      entry.d_key = key;
      entry.d_childBound = childBound;
      visit.push_back(entry);
      // children are added in reverse order, so that they are visited left
      // to right
      for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
      {
        visit.push_back({cur[size - i - 1],
                         key,
                         size - i - 1,
                         childBound,
                         Node::null(),
                         nullptr});
      }
      continue;
    }
    // post-visit: build the plain conversion and, if some child is declared
    // here, the declaring one
    const Node& key = entry.d_key;
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
      Node childKey = keyOf(nm, cur[i], *entry.d_childBound);
      it = visited.find(childKey);
      Assert(it != visited.end() && !it->second.isNull())
          << "With input " << n << " did not find for term " << cur
          << " its child " << cur[i] << "\n";
      childChanged = childChanged || cur[i] != it->second;
      plain.push_back(it->second);
      if (declaresAtParent.count(childKey) && parentOf[childKey] == key
          && firstPosition[childKey] == i)
      {
        Assert(declaredValue.find(childKey) != declaredValue.end());
        declaring.push_back(declaredValue[childKey]);
        declaresChild = true;
        continue;
      }
      declaring.push_back(it->second);
    }
    Node ret = childChanged ? nm->mkNode(cur.getKind(), plain) : Node(cur);
    Node retDeclaring =
        declaresChild ? nm->mkNode(cur.getKind(), declaring) : ret;
    if (declaresAtParent.count(key) && key == cur && getId(cur) > 0)
    {
      // declare the (declaring) conversion; later occurrences use the name
      std::stringstream ss, ssVar;
      ss << "(! ";
      options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
      options::ioutils::applyDagThresh(ss, 0);
      options::ioutils::applyPrintArithLitToken(ss, true);
      options::ioutils::applyFlattenHOChains(ss, true);
      retDeclaring.toStream(ss);
      ssVar << prefix << getId(cur);
      ss << " :named " << ssVar.str() << ")";
      Node declaration =
          NodeManager::mkRawSymbol(ss.str(), retDeclaring.getType());
      declaredValue[key] = declaration;
      visited[key] = NodeManager::mkBoundVar(ssVar.str(), cur.getType());
      continue;
    }
    if (declaresChild)
    {
      // a carrier: its first occurrence embeds the declaration
      declaredValue[key] = retDeclaring;
      declaresAtParent.insert(key);
    }
    visited[key] = ret;
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  auto itd = declaredValue.find(n);
  return itd != declaredValue.end() ? itd->second : visited[n];
}

}  // namespace proof
}  // namespace cvc5::internal
