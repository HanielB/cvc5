/*********************                                                        */
/*! \file theory_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory::booleans::BoolProofRuleChecker
 **
 ** Black box testing of CVC4::theory::booleans::BoolProofRuleChecker
 **/

#include <cxxtest/TestSuite.h>

// Used in some of the tests
#include <sstream>
#include <vector>

#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_rule.h"
#include "smt/proof_manager.h"
#include "smt/smt_engine.h"
#include "theory/booleans/proof_checker.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::smt;

class BoolProofCheckerBlack : public CxxTest::TestSuite
{
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  ProofChecker* d_checker;

 public:
  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em, &opts);
    d_smt->setOption("dag-thresh", "0");
    d_smt->setOption("proof-new", "true");
    d_smt->finishInit();
    // make a proof checker for booleans
    booleans::BoolProofRuleChecker* bpfc = new booleans::BoolProofRuleChecker();
    d_checker = d_smt->getPfManager()->getProofNodeManager()->getChecker();
    bpfc->registerTo(d_checker);
    delete bpfc;
  }

  void tearDown() override
  {
    delete d_smt;
    delete d_em;
  }

  void testChainResolution()
  {
    /* check that

        l0 v l0 v l0 v l1 v l2    ~l0     ~l1
        ---------------------------------------CHAIN_RES_{true, l0, true, l1}
                    l0 v l0 v l2
    */
    Node l0 = d_nm->mkVar("l0", d_nm->booleanType());
    Node l1 = d_nm->mkVar("l1", d_nm->booleanType());
    Node l2 = d_nm->mkVar("l2", d_nm->booleanType());
    Node l3 = d_nm->mkVar("l3", d_nm->booleanType());

    std::vector<Node> c1Nodes{l0, l0, l0, l1, l2};
    Node c1 = d_nm->mkNode(kind::OR, c1Nodes);
    Node c2 = l0.notNode();
    Node c3 = l1.notNode();

    // chain resolution with pivots l0, l1
    std::vector<Node> resNodes{l0, l0, l2};
    Node res = d_nm->mkNode(kind::OR, resNodes);

    std::vector<Node> children{c1, c2, c3};
    std::vector<Node> args{d_nm->mkConst(true), l0, d_nm->mkConst(true), l1};
    Node resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);

    /* check that

        l0 v l0 v l0 v ~l1 v l2    ~l0     l1
        ---------------------------------------CHAIN_RES_{true, l0, false, l1}
                    l0 v l0 v l2
    */
    c1Nodes.clear();
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l1.notNode());
    c1Nodes.push_back(l2);

    children.clear();
    children.push_back(d_nm->mkNode(kind::OR, c1Nodes));
    children.push_back(l0.notNode());
    children.push_back(l1);

    args.clear();
    args.push_back(d_nm->mkConst(true));
    args.push_back(l0);
    args.push_back(d_nm->mkConst(false));
    args.push_back(l1);
    resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);

    /* check that

      l0 v l0 v l2 v ~l3   ~l0 v ~l3   l3
      ------------------------------------CHAIN_RES_{true, l0, false, l3}
          l0 v l2 v ~l3
    */
    c1Nodes.clear();
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l0);
    c1Nodes.push_back(l2);
    c1Nodes.push_back(l3.notNode());

    std::vector<Node> c2Nodes{l0.notNode(), l3.notNode()};

    children.clear();
    children.push_back(d_nm->mkNode(kind::OR, c1Nodes));
    children.push_back(d_nm->mkNode(kind::OR, c2Nodes));
    children.push_back(l3);

    args.clear();
    args.push_back(d_nm->mkConst(true));
    args.push_back(l0);
    args.push_back(d_nm->mkConst(false));
    args.push_back(l3);

    resNodes.clear();
    resNodes.push_back(l0);
    resNodes.push_back(l2);
    resNodes.push_back(l3.notNode());
    res = d_nm->mkNode(kind::OR, resNodes);

    resChecker = d_checker->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
    TS_ASSERT(res == resChecker);

// add test for

// chain_res for 2, a
//   ~6, ~9 : (or (not (or a (and b c))) (not (and (or a b) (or a c))))
//   {0} [9] 9, ~7, ~8 : {0} [(and (or a b) (or a c))] (or (and (or a b) (or a c)) (not (or a b)) (not (or a c)))
//   {0} [6] 6, ~5 : {0} [(or a (and b c))] (or (or a (and b c)) (not (and b c)))
//   {0} [8] 8, ~4 : {0} [(or a c)] (or (or a c) (not c))
//   {0} [5] 5, ~3, ~4 : {0} [(and b c)] (or (and b c) (not b) (not c))
//   {0} [4] 2, 4 : {0} [c] (or a c)
//   {0} [7] 7, ~3 : {0} [(or a b)] (or (or a b) (not b))
//   {0} [3] 2, 3 : {0} [b] (or a b)

  }
};
