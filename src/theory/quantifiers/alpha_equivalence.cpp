/*********************                                                        */
/*! \file alpha_equivalence.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Alpha equivalence checking
 **
 **/

#include "theory/quantifiers/alpha_equivalence.h"

#include "expr/lazy_proof.h"
#include "expr/term_canonize.h"
#include "theory/builtin/proof_checker.h"
#include "theory/quantifiers_engine.h"
#include "theory/trust_node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

struct sortTypeOrder
{
  expr::TermCanonize* d_tu;
  bool operator()(TypeNode i, TypeNode j)
  {
    return d_tu->getIdForType(i) < d_tu->getIdForType(j);
  }
};

void getBoundVariables(TNode n, std::vector<Node>& vs)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    std::unordered_set<TNode, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (cur.getKind() == kind::BOUND_VARIABLE)
      {
        vs.push_back(cur);
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      visited.insert(cur);
    }
  } while (!visit.empty());
}

Node AlphaEquivalenceTypeNode::registerNode(
    Node q,
    Node t,
    const std::vector<TypeNode>& typs,
    const std::map<TypeNode, size_t>& typCount)
{
  AlphaEquivalenceTypeNode* aetn = this;
  size_t index = 0;
  while (index < typs.size())
  {
    TypeNode curr = typs[index];
    auto it = typCount.find(curr);
    Assert(it != typCount.end());
    Trace("aeq-debug") << "[" << curr << " " << it->second << "] ";
    std::pair<TypeNode, size_t> key(curr, it->second);
    aetn = &(aetn->d_children[key]);
    index = index + 1;
  }
  Trace("aeq-debug") << " : ";
  std::map<Node, Node>::iterator it = aetn->d_quant.find(t);
  if (it != aetn->d_quant.end())
  {
    return it->second;
  }
  aetn->d_quant[t] = q;
  return q;
}

AlphaEquivalenceDb::AlphaEquivalenceDb(expr::TermCanonize* tc,
                                       ProofNodeManager* pnm,
                                       bool sortCommChildren)
    : d_tc(tc),
      d_sortCommutativeOpChildren(sortCommChildren),
      d_proof(pnm ? new LazyCDProof(pnm) : nullptr)
{
}

TrustNode AlphaEquivalenceDb::addTerm(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  NodeManager* nm = NodeManager::currentNM();
  Trace("aeq") << "Alpha equivalence : register " << q << std::endl;
  // construct canonical quantified formula
  // the full renaming done by the canonizer
  std::map<Node, Node> subs;
  TrustNode trn =
      d_tc->getCanonicalTerm(q[1], subs, d_sortCommutativeOpChildren);
  Node t = trn.getNode();
  Trace("aeq") << "  canonical form: " << t << std::endl;
  if (isProofEnabled())
  {
    d_canonization[q] = subs;
  }
  // if (isProofEnabled())
  // {
  //   Node rw = trn.getProven();
  //   d_proof->addLazyStep(rw, trn.getGenerator());
  //   if (!subs.empty())
  //   {
  //     std::vector<Node> bvars1, bvars2, renaming;
  //     Trace("aeq") << "  subs: \n";
  //     for (const auto& p : subs)
  //     {
  //       Trace("aeq") << "    " << p.first << " -> " << p.second << "\n";
  //       bvars1.push_back(p.first);
  //       bvars2.push_back(p.second);
  //       renaming.push_back(p.first.eqNode(p.second));
  //     }
  //     // now scope
  //     Node conclusionScope = nm->mkNode(kind::IMPLIES, nm->mkAnd(renaming),
  //     rw); Trace("aeq") << "ConclusionScope: " << conclusionScope << "\n";
  //     d_proof->addStep(conclusionScope, PfRule::SCOPE, {rw}, renaming);
  //     std::vector<Node> topVarPrefixCanon;
  //     for (const Node& v : q[0])
  //     {
  //       topVarPrefixCanon.push_back(subs[v]);
  //     }
  //     // now alpha-equiv
  //     Node canonQ = nm->mkNode(
  //         kind::FORALL, nm->mkNode(kind::BOUND_VAR_LIST, topVarPrefixCanon),
  //         t);
  //     d_canon[q] = canonQ;
  //     std::vector<Node> args{q, canonQ};
  //     args.insert(args.end(), bvars1.begin(), bvars1.end());
  //     args.insert(args.end(), bvars2.begin(), bvars2.end());
  //     d_proof->addStep(
  //         q.eqNode(canonQ), PfRule::ALPHA_EQUIV, {conclusionScope}, args);
  //   }
  //   else
  //   {
  //     d_proof->addStep(q.eqNode(q), PfRule::REFL, {}, {q});
  //   }
  // }
  // compute variable type counts
  std::map<TypeNode, size_t> typCount;
  std::vector<TypeNode> typs;
  for (unsigned i = 0; i < q[0].getNumChildren(); i++)
  {
    TypeNode tn = q[0][i].getType();
    typCount[tn]++;
    if (std::find(typs.begin(), typs.end(), tn) == typs.end())
    {
      typs.push_back(tn);
    }
  }
  sortTypeOrder sto;
  sto.d_tu = d_tc;
  std::sort(typs.begin(), typs.end(), sto);
  Trace("aeq-debug") << "  ";
  Node ret = d_ae_typ_trie.registerNode(q, t, typs, typCount);
  Trace("aeq") << "  ...result : " << ret << std::endl;
  if (ret == q || !isProofEnabled())
  {
    return TrustNode::mkTrustLemma(q.eqNode(ret), nullptr);
  }
  // build substitution from q to ret based on their canonizations
  Assert(d_canonization.find(q) != d_canonization.end());
  Assert(d_canonization.find(ret) != d_canonization.end());
  Node concAlpha;
  if (!d_canonization[q].empty())
  {
    std::vector<Node> bvars1, bvars2, renaming;
    Trace("aeq") << "Renaming: \n";
    for (const auto& pQ : d_canonization[q])
    {
      // q{x->w}, ret{y->w} : {x->y}
      bvars1.push_back(pQ.first);
      // go through ret's map and find key whose value is w
      bool found = false;
      for (const auto& pRet : d_canonization[ret])
      {
        if (pRet.second == pQ.second)
        {
          bvars2.push_back(pRet.first);
          renaming.push_back(pQ.first.eqNode(pRet.first));
          found = true;
        }
      }
      Assert(found);
      Trace("aeq") << "    " << renaming.back()[0] << " -> "
                   << renaming.back()[1] << "\n";
    }
    // build MACRO_SR_PRED_INTRO step between the bodies of q and ret, justified
    // by the renaming
    Node conclusionRw = q[1].eqNode(ret[1]);
    Trace("aeq") << "ConclusionRw: " << conclusionRw << "\n";
    d_proof->addStep(
        conclusionRw,
        PfRule::MACRO_SR_PRED_INTRO,
        renaming,
        {conclusionRw,
         // need extended rewriter because of ordering of equalities
         mkMethodId(MethodId::SB_DEFAULT),
         mkMethodId(MethodId::RW_EXT_REWRITE)});
    // build scope step
    Node conclusionScope =
        nm->mkNode(kind::IMPLIES, nm->mkAnd(renaming), conclusionRw);
    Trace("aeq") << "ConclusionScope: " << conclusionScope << "\n";
    d_proof->addStep(conclusionScope, PfRule::SCOPE, {conclusionRw}, renaming);
    // build alpha-equiv step between q and the body of ret with the prefix as
    // determined by the substitution. We don't use ret directly because of it
    // possibly having a different prefix order than q, see below
    Node canonRet = nm->mkNode(
        kind::FORALL, nm->mkNode(kind::BOUND_VAR_LIST, bvars2), ret[1]);
    std::vector<Node> args{q, canonRet};
    args.insert(args.end(), bvars1.begin(), bvars1.end());
    args.insert(args.end(), bvars2.begin(), bvars2.end());
    concAlpha = q.eqNode(canonRet);
    d_proof->addStep(concAlpha, PfRule::ALPHA_EQUIV, {conclusionScope}, args);
    // we may have the issue that the canonized quantifiers differ on the order
    // of their variable prefix, so we need to add an in-between step for the
    // transitivity proof. So for example, for an alpha-equivalence connection
    // of
    // (\ x1x2. F1) and (\ y2y1. F2):
    //
    //  ---------------------- alpha   ------------------------ cong
    //  ----------------------- alpha
    //  (= (\ x1x2. F1) (\ z1z2. F'))  (= (\ z1z2. F') (\ z2z1. F')) (= (\ z1z1.
    //  F') (\ y2y1. F2))
    // -------------------------------------------------------------------------------------
    // TRANS
    //            (= (\ x1x2. F1) (\ y2y1. F2))
    if (ret[0] != canonRet[0])
    {
      // --------------------------- THEORY_REWRITE  ------- RFL
      // (= (BVL z1 z2) (BVL z2 z1))                 F' = F'
      // --------------------------------------------------- CONG
      //        (= (\ z1z2. F') (\ z2z1. F'))
      Node eqBvl = canonRet[0].eqNode(ret[0]);
      d_proof->addStep(
          eqBvl,
          PfRule::THEORY_REWRITE,
          {},
          {eqBvl,
           theory::builtin::BuiltinProofRuleChecker::mkTheoryIdNode(
               theory::THEORY_BUILTIN),
           mkMethodId(theory::MethodId::RW_REWRITE_THEORY_POST)});
      Node eqRefl = canonRet[1].eqNode(ret[1]);
      d_proof->addStep(eqRefl, PfRule::REFL, {}, {ret[1]});
      Node eqReorder = canonRet.eqNode(ret);
      d_proof->addStep(eqReorder,
                       PfRule::CONG,
                       {eqBvl, eqRefl},
                       {ProofRuleChecker::mkKindNode(kind::FORALL)});
      // add a trans step
      Node newConc = q.eqNode(ret);
      d_proof->addStep(newConc, PfRule::TRANS, {concAlpha, eqReorder}, {});
      concAlpha = newConc;
    }
  }
  else
  {
    concAlpha = q.eqNode(ret);
    d_proof->addStep(q.eqNode(q), PfRule::REFL, {}, {q});
  }
  return TrustNode::mkTrustLemma(concAlpha, d_proof.get());
}

bool AlphaEquivalenceDb::isProofEnabled() const { return d_proof != nullptr; }

AlphaEquivalence::AlphaEquivalence(ProofNodeManager* pnm)
    : d_termCanon(new expr::TermCanonize(pnm, true)),
      d_aedb(d_termCanon.get(), pnm, true)
{
}

TrustNode AlphaEquivalence::reduceQuantifier(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  TrustNode trn = d_aedb.addTerm(q);
  Node lem = trn.getProven();
  if (lem[0] == lem[1])
  {
    return TrustNode::null();
  }
  // lemma ( q <=> d_aedb.addTerm(q) )
  // Notice that we infer this equivalence regardless of whether q or ret
  // have annotations (e.g. user patterns, names, etc.).
  Trace("alpha-eq") << "Alpha equivalent : " << std::endl;
  Trace("alpha-eq") << "  {" << lem[0].getId() << "} " << lem[0] << std::endl;
  Trace("alpha-eq") << "  {" << lem[1].getId() << "} " << lem[1] << std::endl;
  if (q.getNumChildren() == 3)
  {
    Notice() << "Ignoring annotated quantified formula based on alpha "
                "equivalence: "
             << q << std::endl;
  }
  return trn;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
