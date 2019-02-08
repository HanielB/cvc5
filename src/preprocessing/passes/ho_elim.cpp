/*********************                                                        */
/*! \file ho_elim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The HoElim preprocessing pass
 **
 ** Eliminates higher-order constraints.
 **/

#include "preprocessing/passes/ho_elim.h"

#include "theory/uf/theory_uf_rewriter.h"
#include "options/quantifiers_options.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

HoElim::HoElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ho-elim"){};

Node HoElim::eliminateHo(Node n) {
  Trace("ho-elim-assert") << "Ho-elim assertion: " << n << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::map< Node, Node > preReplace;
  std::map< Node, Node >::iterator itr;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = d_visited.find(cur);

    if (it == d_visited.end()) {
      if( cur.isVar() )
      {
        TypeNode tn = cur.getType();
        Node ret = cur;
        if( tn.isFunction() )
        {
          TypeNode ut = getUSort(tn);
          ret = nm->mkSkolem("k",ut);
        }
        d_visited[cur] = ret;
      }
      else
      {
        d_visited[cur] = Node::null();
        if( cur.getKind()==APPLY_UF ){
          // convert apply uf with variable arguments eagerly to ho apply chains, so they are processed uniformly.
          // if we are not using hoElimPartial, we uniformly eliminate all
          if( cur.getOperator().getKind()==BOUND_VARIABLE || !options::hoElimPartial() ){
            visit.push_back(cur);
            Node newCur = theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(cur);
            preReplace[cur] = newCur;
            cur = newCur;
            d_visited[cur] = Node::null();
          }else{
            d_foFun.insert(cur.getOperator());
          }
        }
        visit.push_back(cur);
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      itr = preReplace.find(cur);
      if( itr!=preReplace.end() ){
        d_visited[cur] = d_visited[itr->second];
      }else{
        bool childChanged = false;
        std::vector<Node> children;
        std::vector<TypeNode> childrent;
        bool typeChanged = false;
        for (const Node& cn : ret) {
          it = d_visited.find(cn);
          Assert(it != d_visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
          TypeNode ct = it->second.getType();
          childrent.push_back(ct);
          typeChanged = typeChanged || ct!=cn.getType();
        }
        if (ret.getMetaKind() == metakind::PARAMETERIZED) {
          // child of an argument changed type, must change type
          Node op = ret.getOperator();
          Node retOp = op;
          if( typeChanged ){
            std::unordered_map<TNode, Node, TNodeHashFunction>::iterator ito = d_visited_op.find(op);
            if( ito==d_visited_op.end() ){
              TypeNode newFType = nm->mkFunctionType(childrent,cur.getType());
              retOp = nm->mkSkolem("rf",newFType);
              d_visited_op[op] = retOp;
            }else{
              retOp = ito->second;
            }
          }
          children.push_back(retOp);
        }
        // process ho apply 
        if( ret.getKind()==HO_APPLY )
        {
          Node hoa = getHoApplyUf(ret[0].getType(),ret[1].getType(),ret.getType());
          std::vector< Node > hchildren;
          hchildren.push_back(hoa);
          hchildren.push_back(children[0]);
          hchildren.push_back(children[1]);
          ret = nm->mkNode(APPLY_UF,hchildren);
        }
        else if (childChanged) {
          ret = nm->mkNode(ret.getKind(), children);
        }
        d_visited[cur] = ret;
      }
    }
  } while (!visit.empty());
  Assert(d_visited.find(n) != d_visited.end());
  Assert(!d_visited.find(n)->second.isNull());
  Trace("ho-elim-assert") << "...got : " << d_visited[n] << std::endl;
  return d_visited[n];
}

PreprocessingPassResult HoElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node res = eliminateHo(prev);
    if (res != prev)
    {
      assertionsToPreprocess->replace(i, res);
    }
  }
  std::vector< Node > axioms;
    NodeManager * nm = NodeManager::currentNM();
  // extensionality 
  for(const std::pair< TypeNode, Node >& hoa : d_hoApplyUf )
  {
    TypeNode ft = hoa.first;
    TypeNode uf = getUSort(ft);
    TypeNode ut = getUSort(ft[0]);
    Node h = hoa.second;
    // extensionality
    Node x = nm->mkBoundVar("x",uf);
    Node y = nm->mkBoundVar("y",uf);
    Node z = nm->mkBoundVar("z",ut);
    Node eq = nm->mkNode(APPLY_UF,h,x,z).eqNode(nm->mkNode(APPLY_UF,h,y,z));
    Node antec = nm->mkNode(FORALL,nm->mkNode(BOUND_VAR_LIST,z),eq);
    Node conc = x.eqNode(y);
    Node ax = nm->mkNode(FORALL,nm->mkNode(BOUND_VAR_LIST,x,y),nm->mkNode(OR,antec.negate(),conc));
    axioms.push_back(ax);
    Trace("ho-elim-assert") << "...ext axiom : " << ax << std::endl;
  }
  // for all functions that are in both higher order and first-order
  // contexts, we axiomatize the correspondence
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator ith;
  for( const TNode f : d_foFun )
  {
    ith = d_visited.find(f);
    if( ith!=d_visited.end() )
    {
      // it may have changed types (if it has a function type as an argument)
      Node rf = f;
      std::unordered_map<TNode, Node, TNodeHashFunction>::iterator ito = d_visited_op.find(f);
      if( ito!=d_visited_op.end() )
      {
        rf = ito->second;
      }
      std::vector< TypeNode > argTypes = rf.getType().getArgTypes();
      std::vector< Node > vars;
      for( unsigned i=0, size=argTypes.size(); i<size; i++ )
      {
        Node v = nm->mkBoundVar(argTypes[i]);
        vars.push_back(v);
      }
    }
  }
 
  return PreprocessingPassResult::NO_CONFLICT;
}

Node HoElim::getHoApplyUf(TypeNode tnf, TypeNode tna, TypeNode tnr)
{
  Assert( tnf.isFunction() );
  std::map< TypeNode, Node >::iterator it = d_hoApplyUf.find(tnf);
  if( it==d_hoApplyUf.end() )
  {
    NodeManager * nm = NodeManager::currentNM();
    TypeNode tf = getUSort(tnf);
    TypeNode ta = getUSort(tna);
    TypeNode tr = getUSort(tnr);
    
    std::vector< TypeNode > hoTypeArgs;
    hoTypeArgs.push_back(tf);
    hoTypeArgs.push_back(ta);
    TypeNode tnh = nm->mkFunctionType(hoTypeArgs,tr);
    Node k = NodeManager::currentNM()->mkSkolem("ho",tnh);
    d_hoApplyUf[tnf] = k;
    return k;
  }
  return it->second;
}

TypeNode HoElim::getUSort(TypeNode tn)
{
  if( !tn.isFunction() ){
    return tn;
  }
  std::map< TypeNode, TypeNode >::iterator it = d_ftypeMap.find(tn);
  if( it==d_ftypeMap.end() )
  {
    TypeNode s = NodeManager::currentNM()->mkSort("u");
    d_ftypeMap[tn] = s;
    return s;
  }
  return it->second;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
