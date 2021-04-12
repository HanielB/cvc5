/*********************                                                        */
/*! \file term_canonize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term canonize.
 **/

#include "expr/term_canonize.h"

#include <sstream>

#include "expr/proof_node_manager.h"
#include "expr/term_conversion_proof_generator.h"

#include "theory/builtin/proof_checker.h"
#include "theory/trust_node.h"
// TODO #1216: move the code in this include
#include "theory/quantifiers/term_util.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace expr {

TermCanonize::TermCanonize(ProofNodeManager* pnm, bool hoVar)
    : d_op_id_count(0),
      d_typ_id_count(0),
      d_tcpg(pnm ? new TConvProofGenerator(pnm,
                                           nullptr,
                                           TConvPolicy::FIXPOINT,
                                           TConvCachePolicy::NEVER,
                                           "TermCanonizer::TConvProofGenerator",
                                           nullptr,
                                           true)
                 : nullptr)
{
}

TermCanonize::~TermCanonize() {}

int TermCanonize::getIdForOperator(Node op)
{
  std::map<Node, int>::iterator it = d_op_id.find(op);
  if (it == d_op_id.end())
  {
    d_op_id[op] = d_op_id_count;
    d_op_id_count++;
    return d_op_id[op];
  }
  return it->second;
}

int TermCanonize::getIdForType(TypeNode t)
{
  std::map<TypeNode, int>::iterator it = d_typ_id.find(t);
  if (it == d_typ_id.end())
  {
    d_typ_id[t] = d_typ_id_count;
    d_typ_id_count++;
    return d_typ_id[t];
  }
  return it->second;
}

bool TermCanonize::getTermOrder(Node a, Node b)
{
  if (a.getKind() == BOUND_VARIABLE)
  {
    if (b.getKind() == BOUND_VARIABLE)
    {
      return getIndexForFreeVariable(a) < getIndexForFreeVariable(b);
    }
    return true;
  }
  if (b.getKind() != BOUND_VARIABLE)
  {
    Node aop = a.hasOperator() ? a.getOperator() : a;
    Node bop = b.hasOperator() ? b.getOperator() : b;
    Trace("aeq-debug2") << a << "...op..." << aop << std::endl;
    Trace("aeq-debug2") << b << "...op..." << bop << std::endl;
    if (aop == bop)
    {
      if (a.getNumChildren() == b.getNumChildren())
      {
        for (unsigned i = 0, size = a.getNumChildren(); i < size; i++)
        {
          if (a[i] != b[i])
          {
            // first distinct child determines the ordering
            return getTermOrder(a[i], b[i]);
          }
        }
      }
      else
      {
        return aop.getNumChildren() < bop.getNumChildren();
      }
    }
    else
    {
      return getIdForOperator(aop) < getIdForOperator(bop);
    }
  }
  return false;
}

Node TermCanonize::getCanonicalFreeVar(TypeNode tn, unsigned i)
{
  Assert(!tn.isNull());
  NodeManager* nm = NodeManager::currentNM();
  while (d_cn_free_var[tn].size() <= i)
  {
    std::stringstream oss;
    oss << tn;
    std::string typ_name = oss.str();
    while (typ_name[0] == '(')
    {
      typ_name.erase(typ_name.begin());
    }
    std::stringstream os;
    os << typ_name[0] << i;
    Node x = nm->mkBoundVar(os.str().c_str(), tn);
    d_fvIndex[x] = d_cn_free_var[tn].size();
    d_cn_free_var[tn].push_back(x);
  }
  return d_cn_free_var[tn][i];
}

size_t TermCanonize::getIndexForFreeVariable(Node v) const
{
  std::map<Node, size_t>::const_iterator it = d_fvIndex.find(v);
  if (it == d_fvIndex.end())
  {
    return 0;
  }
  return it->second;
}

struct sortTermOrder
{
  TermCanonize* d_tu;
  bool operator()(Node i, Node j) { return d_tu->getTermOrder(i, j); }
};

theory::TrustNode TermCanonize::getCanonicalTerm(TNode n,
                                                 std::map<Node, Node>& subs,
                                                 bool applyTOrder,
                                                 bool doHoVar)
{
  // counter for creating canonical variables per type
  std::map<TypeNode, unsigned> varCount;
  // visiting stuff
  std::vector<TNode> visit{n};
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  TNode cur;
  NodeManager* nm = NodeManager::currentNM();
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      Trace("canon-term-debug") << "Get canonical term for " << cur << "\n";
      if (cur.getKind() == BOUND_VARIABLE)
      {
        TypeNode tn = cur.getType();
        // allocate variable
        unsigned vn = varCount[tn];
        varCount[tn]++;
        Node fv = getCanonicalFreeVar(tn, vn);
        visited[cur] = fv;
        subs[cur] = fv;
        Trace("canon-term-debug") << "...allocate variable.\n";
        if (isProofEnabled())
        {
          // substitutions are pre-rewrites
          d_tcpg->addRewriteStep(
              cur, fv, PfRule::ASSUME, {}, {cur.eqNode(fv)}, true);
        }
      }
      else if (cur.getNumChildren() > 0)
      {
        visit.push_back(cur);
        // collect children
        Trace("canon-term-debug") << "Collect children\n";
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          Node op = cur.getOperator();
          if (doHoVar)
          {
            visit.push_back(op);
          }
          else
          {
            visited[op] = op;
          }
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else
      {
        visited[cur] = cur;
      }
    }
    else if (it->second.isNull())
    {
      // post-visit, rebuild
      Trace("canon-term-debug") << "Post-visit " << cur << "\n";
      bool changed = false;
      std::vector<Node> cchildren;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        Node op = cur.getOperator();
        Assert(visited.find(op) != visited.end());
        cchildren.push_back(visited[op]);
        changed = cchildren.back() != op;
      }
      for (const Node& cn : cur)
      {
        Assert(visited.find(cn) != visited.end());
        Node ccn = visited[cn];
        cchildren.push_back(ccn);
        changed |= ccn != cn;
      }
      std::vector<Node> origCchildren;
      // if applicable, first sort by term order
      if (applyTOrder && theory::quantifiers::TermUtil::isComm(cur.getKind()))
      {
        Trace("canon-term-debug") << "Sort based on commutative operator "
                                  << cur.getKind() << std::endl;
        if (isProofEnabled())
        {
          origCchildren.insert(
              origCchildren.end(), cchildren.begin(), cchildren.end());
        }
        sortTermOrder sto;
        sto.d_tu = this;
        std::sort(cchildren.begin(), cchildren.end(), sto);
        changed = true;
      }
      // now make canonical
      Node res = cur;
      if (changed)
      {
        Trace("canon-term-debug") << "Make canonical children" << std::endl;
        Trace("canon-term-debug")
            << "...constructing for " << cur << "." << std::endl;
        res = nm->mkNode(cur.getKind(), cchildren);
        Trace("canon-term-debug")
            << "...constructed " << res << " for " << cur << "." << std::endl;
        // check if orderd changed, in which case add a rewrite
        if (isProofEnabled() && !origCchildren.empty())
        {
          Node prev = nm->mkNode(cur.getKind(), origCchildren);
          if (prev != res)
          {
            d_tcpg->addRewriteStep(
                prev,
                res,
                PfRule::THEORY_REWRITE,
                {},
                {prev.eqNode(res),
                 theory::builtin::BuiltinProofRuleChecker::mkTheoryIdNode(
                     theory::THEORY_BUILTIN),
                 mkMethodId(theory::MethodId::RW_REWRITE_THEORY_POST)});
          }
        }
      }
      AlwaysAssert(!res.isNull());
      visited[cur] = res;
    }
  } while (!visit.empty());
  AlwaysAssert(!visited[n].isNull());
  return theory::TrustNode::mkTrustRewrite(n, visited[n], d_tcpg.get());
}

Node TermCanonize::getCanonicalTerm(TNode n, bool applyTOrder, bool doHoVar)
{
  std::map<Node, Node> subs;
  theory::TrustNode trn = getCanonicalTerm(n, subs, applyTOrder, doHoVar);
  AlwaysAssert(!trn.isNull());
  return trn.getNode();
}

bool TermCanonize::isProofEnabled() const { return d_tcpg != nullptr; }

}  // namespace expr
}  // namespace cvc5
