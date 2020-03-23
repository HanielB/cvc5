/*********************                                                        */
/*! \file cnf_stream.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/
#include "prop/cnf_stream.h"

#include <queue>

#include "base/check.h"
#include "base/output.h"
#include "expr/expr.h"
#include "expr/node.h"
#include "options/bv_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "prop/minisat/minisat.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "smt/command.h"
#include "smt/smt_engine_scope.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(SatSolver* satSolver, Registrar* registrar,
                     context::Context* context, bool fullLitToNodeMap,
                     std::string name)
    : d_satSolver(satSolver),
      d_booleanVariables(context),
      d_nodeToLiteralMap(context),
      d_literalToNodeMap(context),
      d_fullLitToNodeMap(fullLitToNodeMap),
      d_convertAndAssertCounter(0),
      d_registrar(registrar),
      d_name(name),
      d_cnfProof(NULL),
      d_removable(false) {
}

TseitinCnfStream::TseitinCnfStream(SatSolver* satSolver, Registrar* registrar,
                                   context::Context* context,
                                   bool fullLitToNodeMap, std::string name)
  : CnfStream(satSolver, registrar, context, fullLitToNodeMap, name)
{}

ClauseId CnfStream::assertClause(TNode node, SatClause& c)
{
  Debug("cnf") << "Inserting into stream " << c << " node = " << node << endl;
  if(Dump.isOn("clauses")) {
    if(c.size() == 1) {
      Dump("clauses") << AssertCommand(Expr(getNode(c[0]).toExpr()));
    } else {
      Assert(c.size() > 1);
      NodeBuilder<> b(kind::OR);
      for(unsigned i = 0; i < c.size(); ++i) {
        b << getNode(c[i]);
      }
      Node n = b;
      Dump("clauses") << AssertCommand(Expr(n.toExpr()));
    }
  }

  if (PROOF_ON() && d_cnfProof)
  {
    d_cnfProof->pushCurrentDefinition(node);
  }

  ClauseId clause_id = d_satSolver->addClause(c, d_removable);
  // nothing to store (no clause was added)
  if (clause_id == ClauseIdUndef)
  {
    return clause_id;
  }

  if (PROOF_ON() && d_cnfProof)
  {
    if (clause_id != ClauseIdError)
    {
      d_cnfProof->registerConvertedClause(clause_id);
    }
    d_cnfProof->popCurrentDefinition();
  };
  return clause_id;
}

ClauseId CnfStream::assertClause(TNode node, SatLiteral a) {
  SatClause clause(1);
  clause[0] = a;
  return assertClause(node, clause);
}

ClauseId CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b)
{
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  return assertClause(node, clause);
}

ClauseId CnfStream::assertClause(TNode node,
                                 SatLiteral a,
                                 SatLiteral b,
                                 SatLiteral c)
{
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  return assertClause(node, clause);
}

bool CnfStream::hasLiteral(TNode n) const {
  NodeToLiteralMap::const_iterator find = d_nodeToLiteralMap.find(n);
  return find != d_nodeToLiteralMap.end();
}

void TseitinCnfStream::ensureLiteral(TNode n, bool noPreregistration) {
  // These are not removable and have no proof ID
  d_removable = false;

  Debug("cnf") << "ensureLiteral(" << n << ")" << endl;
  if(hasLiteral(n)) {
    SatLiteral lit = getLiteral(n);
    if(!d_literalToNodeMap.contains(lit)){
      // Store backward-mappings
      d_literalToNodeMap.insert(lit, n);
      d_literalToNodeMap.insert(~lit, n.notNode());
    }
    return;
  }

  AlwaysAssertArgument(
      n.getType().isBoolean(),
      n,
      "CnfStream::ensureLiteral() requires a node of Boolean type.\n"
      "got node: %s\n"
      "its type: %s\n",
      n.toString().c_str(),
      n.getType().toString().c_str());

  bool negated CVC4_UNUSED = false;
  SatLiteral lit;

  if(n.getKind() == kind::NOT) {
    negated = true;
    n = n[0];
  }

  if( theory::Theory::theoryOf(n) == theory::THEORY_BOOL &&
      !n.isVar() ) {
    // If we were called with something other than a theory atom (or
    // Boolean variable), we get a SatLiteral that is definitionally
    // equal to it.
    //
    // We are setting the current assertion to be null. This is because `toCNF`
    // may add clauses to the SAT solver and we look up the current assertion
    // in that case. Setting it to null ensures that the assertion stack is
    // non-empty and that we are not associating a bogus assertion with the
    // clause. This should be ok because we use the mapping back to assertions
    // for clauses from input assertions only.
    PROOF(if (d_cnfProof) { d_cnfProof->pushCurrentAssertion(Node::null()); });

    lit = toCNF(n, false);

    PROOF(if (d_cnfProof) { d_cnfProof->popCurrentAssertion(); });

    // Store backward-mappings
    // These may already exist
    d_literalToNodeMap.insert_safe(lit, n);
    d_literalToNodeMap.insert_safe(~lit, n.notNode());
  } else {
    // We have a theory atom or variable.
    lit = convertAtom(n, noPreregistration);
  }

  Assert(hasLiteral(n) && getNode(lit) == n);
  Debug("ensureLiteral") << "CnfStream::ensureLiteral(): out lit is " << lit << std::endl;
}

SatLiteral CnfStream::newLiteral(TNode node, bool isTheoryAtom, bool preRegister, bool canEliminate) {
  Debug("cnf") << d_name << "::newLiteral(" << node << ", " << isTheoryAtom << ")" << endl;
  Assert(node.getKind() != kind::NOT);

  // Get the literal for this node
  SatLiteral lit;
  if (!hasLiteral(node)) {
    // If no literal, we'll make one
    if (node.getKind() == kind::CONST_BOOLEAN) {
      if (node.getConst<bool>()) {
        lit = SatLiteral(d_satSolver->trueVar());
      } else {
        lit = SatLiteral(d_satSolver->falseVar());
      }
    } else {
      lit = SatLiteral(d_satSolver->newVar(isTheoryAtom, preRegister, canEliminate));
    }
    d_nodeToLiteralMap.insert(node, lit);
    d_nodeToLiteralMap.insert(node.notNode(), ~lit);
    NEWPROOF({
      NewProofManager* pm = NewProofManager::currentPM();
      pm->addLitDef(lit, node);
      pm->addLitDef(~lit, node.notNode());
    })
  } else {
    lit = getLiteral(node);
  }

  // If it's a theory literal, need to store it for back queries
  if ( isTheoryAtom || d_fullLitToNodeMap || (Dump.isOn("clauses")) ) {
    d_literalToNodeMap.insert_safe(lit, node);
    d_literalToNodeMap.insert_safe(~lit, node.notNode());
  }

  // If a theory literal, we pre-register it
  if (preRegister) {
    // In case we are re-entered due to lemmas, save our state
    bool backupRemovable = d_removable;
    // Should be fine since cnfProof current assertion is stack based.
    d_registrar->preRegister(node);
    d_removable = backupRemovable;
  }

  // Here, you can have it
  Debug("cnf") << "newLiteral(" << node << ") => " << lit << endl;

  return lit;
}

TNode CnfStream::getNode(const SatLiteral& literal) {
  Debug("cnf") << "getNode(" << literal << ")" << endl;
  Debug("cnf") << "getNode(" << literal << ") => " << d_literalToNodeMap[literal] << endl;
  return d_literalToNodeMap[literal];
}

void CnfStream::getBooleanVariables(std::vector<TNode>& outputVariables) const {
  context::CDList<TNode>::const_iterator it, it_end;
  for (it = d_booleanVariables.begin(); it != d_booleanVariables.end(); ++ it) {
    outputVariables.push_back(*it);
  }
}

void CnfStream::setProof(CnfProof* proof) {
  Assert(d_cnfProof == NULL);
  d_cnfProof = proof;
}

SatLiteral CnfStream::convertAtom(TNode node, bool noPreregistration) {
  Debug("cnf") << "convertAtom(" << node << ")" << endl;

  Assert(!hasLiteral(node)) << "atom already mapped!";

  bool theoryLiteral = false;
  bool canEliminate = true;
  bool preRegister = false;

  // Is this a variable add it to the list
  if (node.isVar() && node.getKind()!=BOOLEAN_TERM_VARIABLE) {
    d_booleanVariables.push_back(node);
  } else {
    theoryLiteral = true;
    canEliminate = false;
    preRegister = !noPreregistration;
  }

  // Make a new literal (variables are not considered theory literals)
  SatLiteral lit = newLiteral(node, theoryLiteral, preRegister, canEliminate);
  // Return the resulting literal
  return lit;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  Assert(!node.isNull()) << "CnfStream: can't getLiteral() of null node";

  Assert(d_nodeToLiteralMap.contains(node))
      << "Literal not in the CNF Cache: " << node << "\n";

  SatLiteral literal = d_nodeToLiteralMap[node];
  Debug("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal << std::endl;
  return literal;
}

SatLiteral TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!hasLiteral(xorNode)) << "Atom already mapped!";
  Assert(xorNode.getKind() == XOR) << "Expecting an XOR expression!";
  Assert(xorNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteral(xorNode);

  ClauseId id = assertClause(xorNode.negate(), a, b, ~xorLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~xorLit;
      clause[1] = a;
      clause[2] = b;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR_POS1, id, xorNode, clause);
    }
  });
  id = assertClause(xorNode.negate(), ~a, ~b, ~xorLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~xorLit;
      clause[1] = ~a;
      clause[2] = ~b;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR_POS2, id, xorNode, clause);
    }
  });
  id = assertClause(xorNode, a, ~b, xorLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = xorLit;
      clause[1] = a;
      clause[2] = ~b;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR_NEG1, id, xorNode, clause);
    }
  });
  id = assertClause(xorNode, ~a, b, xorLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = xorLit;
      clause[1] = ~a;
      clause[2] = b;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR_NEG2, id, xorNode, clause);
    }
  });

  return xorLit;
}

SatLiteral TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!hasLiteral(orNode)) << "Atom already mapped!";
  Assert(orNode.getKind() == OR) << "Expecting an OR expression!";
  Assert(orNode.getNumChildren() > 1) << "Expecting more then 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";

  // Number of children
  unsigned n_children = orNode.getNumChildren();

  // Transform all the children first
  TNode::const_iterator node_it = orNode.begin();
  TNode::const_iterator node_it_end = orNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral orLit = newLiteral(orNode);

  ClauseId id;
  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for (unsigned i = 0; i < n_children; ++i)
  {
    id = assertClause(orNode, orLit, ~clause[i]);
    NEWPROOF({
      if (id != ClauseIdUndef)
      {
        SatClause proof_clause(2);
        proof_clause[0] = orLit;
        proof_clause[1] = ~clause[i];
        NewProofManager::currentPM()->addDefCnfProofStep(
            RULE_CNF_OR_NEG, id, proof_clause);
      }
    });
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  id = assertClause(orNode.negate(), clause);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause proof_clause(n_children + 1);
      proof_clause[0] = ~orLit;
      for (unsigned i = 0; i < n_children; ++i)
      {
        proof_clause[i + 1] = clause[i];
      }
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_OR_POS, id, proof_clause);
    }
  });

  // Return the literal
  return orLit;
}

SatLiteral TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!hasLiteral(andNode)) << "Atom already mapped!";
  Assert(andNode.getKind() == AND) << "Expecting an AND expression!";
  Assert(andNode.getNumChildren() > 1) << "Expecting more than 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";

  // Number of children
  unsigned n_children = andNode.getNumChildren();

  // Transform all the children first (remembering the negation)
  TNode::const_iterator node_it = andNode.begin();
  TNode::const_iterator node_it_end = andNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = ~toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral andLit = newLiteral(andNode);

  ClauseId id;
  // lit -> (a_1 & a_2 & a_3 & ... & a_n)
  // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
  // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
  for (unsigned i = 0; i < n_children; ++i)
  {
    id = assertClause(andNode.negate(), ~andLit, ~clause[i]);
    NEWPROOF({
      if (id != ClauseIdUndef)
      {
        SatClause proof_clause(2);
        proof_clause[0] = ~andLit;
        proof_clause[1] = clause[i];
        NewProofManager::currentPM()->addDefCnfProofStep(
            RULE_CNF_AND_POS, id, proof_clause);
      }
    });
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  id = assertClause(andNode, clause);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause proof_clause(n_children + 1);
      proof_clause[0] = andLit;
      for (unsigned i = 0; i < n_children; ++i)
      {
        proof_clause[i+1] = clause[i];
      }
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_AND_NEG, id, proof_clause);
    }
  });

  return andLit;
}

SatLiteral TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!hasLiteral(impliesNode)) << "Atom already mapped!";
  Assert(impliesNode.getKind() == IMPLIES)
      << "Expecting an IMPLIES expression!";
  Assert(impliesNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  ClauseId id = assertClause(impliesNode.negate(), ~impliesLit, ~a, b);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~impliesLit;
      clause[1] = ~a;
      clause[2] = b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_IMPLIES_POS, id, clause);
    }
  });

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  id = assertClause(impliesNode, a, impliesLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(2);
      clause[0] = impliesLit;
      clause[1] = a;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_IMPLIES_NEG1, id, clause);
    }
  });
  id = assertClause(impliesNode, ~b, impliesLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(2);
      clause[0] = impliesLit;
      clause[1] = ~b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_IMPLIES_NEG2, id, clause);
    }
  });
  return impliesLit;
}


SatLiteral TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!hasLiteral(iffNode)) << "Atom already mapped!";
  Assert(iffNode.getKind() == EQUAL) << "Expecting an EQUAL expression!";
  Assert(iffNode.getNumChildren() == 2) << "Expecting exactly 2 children!";

  Debug("cnf") << "handleIff(" << iffNode << ")" << endl;

  // Convert the children to CNF
  SatLiteral a = toCNF(iffNode[0]);
  SatLiteral b = toCNF(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  ClauseId id = assertClause(iffNode.negate(), ~a, b, ~iffLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~iffLit;
      clause[1] = ~a;
      clause[1] = b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_EQUIV_POS2, id, clause);
    }
  });
  id = assertClause(iffNode.negate(), a, ~b, ~iffLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~iffLit;
      clause[1] = a;
      clause[1] = ~b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_EQUIV_POS1, id, clause);
    }
  });
  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  id = assertClause(iffNode, ~a, ~b, iffLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = iffLit;
      clause[1] = ~a;
      clause[1] = ~b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_EQUIV_NEG1, id, clause);
    }
  });
  id = assertClause(iffNode, a, b, iffLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = iffLit;
      clause[1] = a;
      clause[1] = b;
      NewProofManager::currentPM()->addDefCnfProofStep(
          RULE_CNF_EQUIV_NEG2, id, clause);
    }
  });

  return iffLit;
}


SatLiteral TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!hasLiteral(notNode)) << "Atom already mapped!";
  Assert(notNode.getKind() == NOT) << "Expecting a NOT expression!";
  Assert(notNode.getNumChildren() == 1) << "Expecting exactly 1 child!";

  SatLiteral notLit = ~toCNF(notNode[0]);

  return notLit;
}

SatLiteral TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(iteNode.getKind() == ITE);
  Assert(iteNode.getNumChildren() == 3);
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";

  Debug("cnf") << "handleIte(" << iteNode[0] << " " << iteNode[1] << " " << iteNode[2] << ")" << endl;

  SatLiteral condLit = toCNF(iteNode[0]);
  SatLiteral thenLit = toCNF(iteNode[1]);
  SatLiteral elseLit = toCNF(iteNode[2]);

  SatLiteral iteLit = newLiteral(iteNode);

  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  ClauseId id = assertClause(iteNode.negate(), ~iteLit, thenLit, elseLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~iteLit;
      clause[1] = thenLit;
      clause[2] = elseLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_POS3, id, iteNode, clause);
    }
  });
  id = assertClause(iteNode.negate(), ~iteLit, ~condLit, thenLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~iteLit;
      clause[1] = ~condLit;
      clause[2] = thenLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_POS2, id, iteNode, clause);
    }
  });
  id = assertClause(iteNode.negate(), ~iteLit, condLit, elseLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = ~iteLit;
      clause[1] = condLit;
      clause[2] = elseLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_POS1, id, iteNode, clause);
    }
  });

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  id = assertClause(iteNode, iteLit, ~thenLit, ~elseLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = iteLit;
      clause[1] = ~thenLit;
      clause[2] = ~elseLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_NEG3, id, iteNode, clause);
    }
  });
  id = assertClause(iteNode, iteLit, ~condLit, ~thenLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = iteLit;
      clause[1] = ~condLit;
      clause[2] = ~thenLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_NEG2, id, iteNode, clause);
    }
  });
  id = assertClause(iteNode, iteLit, condLit, ~elseLit);
  NEWPROOF({
    if (id != ClauseIdUndef)
    {
      SatClause clause(3);
      clause[0] = iteLit;
      clause[1] = condLit;
      clause[2] = ~elseLit;
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_ITE_NEG1, id, iteNode, clause);
    }
  });

  return iteLit;
}


SatLiteral TseitinCnfStream::toCNF(TNode node, bool negated) {
  Debug("cnf") << "toCNF(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  SatLiteral nodeLit;
  Node negatedNode = node.notNode();

  // If the non-negated node has already been translated, get the translation
  if(hasLiteral(node)) {
    Debug("cnf") << "toCNF(): already translated" << endl;
    nodeLit = getLiteral(node);
  } else {
    // Handle each Boolean operator case
    switch(node.getKind()) {
    case NOT:
      nodeLit = handleNot(node);
      break;
    case XOR:
      nodeLit = handleXor(node);
      break;
    case ITE:
      nodeLit = handleIte(node);
      break;
    case IMPLIES:
      nodeLit = handleImplies(node);
      break;
    case OR:
      nodeLit = handleOr(node);
      break;
    case AND:
      nodeLit = handleAnd(node);
      break;
    case EQUAL:
      if(node[0].getType().isBoolean()) {
        nodeLit = handleIff(node);
      } else {
        nodeLit = convertAtom(node);
      }
      break;
    default:
      {
        nodeLit = convertAtom(node);
      }
      break;
    }
  }

  // Return the appropriate (negated) literal
  if (!negated) return nodeLit;
  else return ~nodeLit;
}

void TseitinCnfStream::convertAndAssertAnd(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertAnd: Assertion " << node
      << ", pol: " << negated << "\n";
  Assert(node.getKind() == AND);
  if (!negated) {
    // If the node is a conjunction, we handle each conjunct separately
    for (TNode::const_iterator conjunct = node.begin(), node_end = node.end();
         conjunct != node_end;
         ++conjunct)
    {
      PROOF(if (d_cnfProof) d_cnfProof->setCnfDependence(*conjunct, node););
      // (n_1 ^ ... ^ n_m => n_i)
      //
      // Berofe converting each n_i, create proof step ~(n_1 ^ ... ^ n_m) v
      // n_i. The respective proof step will be the id associated with
      // sub-assertion n_i
      NEWPROOF({
        std::vector<Node> clauseNodes{*conjunct};
        NewProofManager* pm = NewProofManager::currentPM();
        ClauseId id =
            pm->addCnfProofStep(RULE_CNF_AND, ClauseIdUndef, node, clauseNodes);
        pm->addInputSubAssertion(*conjunct, id);
      });
      convertAndAssert(*conjunct, false);
    }
  } else {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, true);
    }
    Assert(disjunct == node.end());
    ClauseId id = assertClause(node.negate(), clause);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_NOT_AND, id, node, clause);
    });
  }
}

void TseitinCnfStream::convertAndAssertOr(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertOr: Assertion " << node
      << ", pol: " << negated << "\n";
  Assert(node.getKind() == OR);
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, false);
    }
    Assert(disjunct == node.end());
    ClauseId id = assertClause(node, clause);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_OR, id, node, clause);
    });
  } else {
    // If the node is a conjunction, we handle each conjunct separately
    for (TNode::const_iterator conjunct = node.begin(), node_end = node.end();
         conjunct != node_end;
         ++conjunct)
    {
      PROOF(if (d_cnfProof) d_cnfProof->setCnfDependence((*conjunct).negate(),
                                                         node.negate()););
      // ~(n_1 v ... v n_m) => ~n_i
      //
      // Berofe converting each ~n_i, create proof step (n_1 v ... v n_m) v
      // ~n_i. The respective proof step will be the id associated with
      // sub-assertion ~n_i
      NEWPROOF({
        Node not_conjunct = (*conjunct).negate();
        std::vector<Node> clauseNodes{not_conjunct};
        NewProofManager* pm = NewProofManager::currentPM();
        ClauseId id = pm->addCnfProofStep(
            RULE_CNF_NOT_OR, ClauseIdUndef, node, clauseNodes);
        pm->addInputSubAssertion(not_conjunct, id);
      });
      convertAndAssert(*conjunct, true);
    }
  }
}

void TseitinCnfStream::convertAndAssertXor(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertXor: Assertion " << node
      << ", pol: " << negated << "\n";
  if (!negated) {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    ClauseId id = assertClause(node, clause1);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR2, id, node, clause1);
    });
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    id = assertClause(node, clause2);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_XOR1, id, node, clause2);
    });
  } else {
    // !(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    ClauseId id = assertClause(node.negate(), clause1);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_NOT_XOR2, id, node, clause1);
    });
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    id = assertClause(node.negate(), clause2);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_NOT_XOR1, id, node, clause2);
    });
  }
}

void TseitinCnfStream::convertAndAssertIff(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertIff: Assertion " << node
      << ", pol: " << negated << "\n";
  if (!negated) {
    // p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    ClauseId id = assertClause(node, clause1);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_EQUIV1, id, node, clause1);
    });
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    id = assertClause(node, clause2);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_EQUIV2, id, node, clause2);
    });
  } else {
    // !(p <=> q) is the same as p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    ClauseId id = assertClause(node.negate(), clause1);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_NOT_EQUIV2, id, node, clause1);
    });
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    id = assertClause(node.negate(), clause2);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_EQUIV1, id, node, clause2);
    });
  }
}

void TseitinCnfStream::convertAndAssertImplies(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertImplies: Assertion " << node
      << ", pol: " << negated << "\n";
  if (!negated) {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    ClauseId id = assertClause(node, clause);
    NEWPROOF({
      Assert(id != ClauseIdUndef);
      NewProofManager::currentPM()->addCnfProofStep(
          RULE_CNF_IMPLIES, id, node, clause);
    });
  } else {// Construct the
    PROOF(if (d_cnfProof) d_cnfProof->setCnfDependence(node[0], node.negate()););
    PROOF(if (d_cnfProof) d_cnfProof->setCnfDependence(node[1].negate(), node.negate()););
    // !(p => q) is the same as (p && ~q)
    //
    // Berofe converting p, create proof step !(p => q) v p. The respective
    // proof step will be the id associated with sub-assertion p
    NEWPROOF({
      std::vector<Node> clauseNodes{node[0]};
      NewProofManager* pm = NewProofManager::currentPM();
      ClauseId id = pm->addCnfProofStep(
          RULE_CNF_NOT_IMPLIES1, ClauseIdUndef, node, clauseNodes);
      pm->addInputSubAssertion(node[0], id);
    });
    convertAndAssert(node[0], false);

    // Berofe converting ~q, create proof step !(p => q) v ~q. The respective
    // proof step will be the id associated with sub-assertion ~q
    // Second handle !(p => q) v ~q
    NEWPROOF({
      Node not_q = node[1].negate();
      std::vector<Node> clauseNodes{not_q};
      NewProofManager* pm = NewProofManager::currentPM();
      ClauseId id = pm->addCnfProofStep(
          RULE_CNF_NOT_IMPLIES2, ClauseIdUndef, node, clauseNodes);
      pm->addInputSubAssertion(not_q, id);
    });
    convertAndAssert(node[1], true);
  }
}

void TseitinCnfStream::convertAndAssertIte(TNode node, bool negated) {
  Debug("newproof::sat::cnf")
      << "TseitinCnfStream::convertAndAssertIte: Assertion " << node
      << ", pol: " << negated << "\n";
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r)
  Node nnode = node;
  if( negated ){
    nnode = node.negate();
  }
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  ClauseId id = assertClause(nnode, clause1);
  NEWPROOF({
    Assert(id != ClauseIdUndef);
    NewProofManager::currentPM()->addCnfProofStep(
        RULE_CNF_ITE2, id, node, clause1);
  });
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  id = assertClause(nnode, clause2);
  NEWPROOF({
    Assert(id != ClauseIdUndef);
    NewProofManager::currentPM()->addCnfProofStep(
        RULE_CNF_ITE1, id, node, clause2);
  });
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void TseitinCnfStream::convertAndAssert(TNode node,
                                        bool removable,
                                        bool negated,
                                        ProofRule proof_id,
                                        TNode from) {
  Debug("cnf") << "convertAndAssert(" << node
               << ", removable = " << (removable ? "true" : "false")
               << ", negated = " << (negated ? "true" : "false") << ")" << endl;
  d_removable = removable;
  PROOF
    (if (d_cnfProof) {
      Node assertion = negated ? node.notNode() : (Node)node;
      Node from_assertion = negated? from.notNode() : (Node) from;

      if (proof_id != RULE_INVALID) {
        d_cnfProof->pushCurrentAssertion(from.isNull() ? assertion : from_assertion);
        d_cnfProof->registerAssertion(from.isNull() ? assertion : from_assertion, proof_id);
      }
      else {
        d_cnfProof->pushCurrentAssertion(assertion);
        d_cnfProof->registerAssertion(assertion, proof_id);
      }
    });

  convertAndAssert(node, negated);
  PROOF
    (if (d_cnfProof) {
      d_cnfProof->popCurrentAssertion();
    });
}

void TseitinCnfStream::convertAndAssert(TNode node, bool negated) {
  Debug("cnf") << "convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  if (d_convertAndAssertCounter % ResourceManager::getFrequencyCount() == 0) {
    NodeManager::currentResourceManager()->spendResource(
        ResourceManager::Resource::CnfStep);
    d_convertAndAssertCounter = 0;
  }
  ++d_convertAndAssertCounter;

  switch(node.getKind()) {
  case AND:
    convertAndAssertAnd(node, negated);
    break;
  case OR:
    convertAndAssertOr(node, negated);
    break;
  case XOR:
    convertAndAssertXor(node, negated);
    break;
  case IMPLIES:
    convertAndAssertImplies(node, negated);
    break;
  case ITE:
    convertAndAssertIte(node, negated);
    break;
  case NOT:
    convertAndAssert(node[0], !negated);
    break;
  case EQUAL:
    if( node[0].getType().isBoolean() ){
      convertAndAssertIff(node, negated);
      break;
    }
    CVC4_FALLTHROUGH;
  default:
  {
    Node nnode = node;
    if( negated ){
      nnode = node.negate();
    }
    // Literals to clauses, atoms and polarity to the SAT solver
    SatLiteral lit = toCNF(node, negated);
    ClauseId id = assertClause(nnode, lit);
    NEWPROOF({
      Debug("newproof::sat::cnf")
          << "TseitinCnfStream::convertAndAssert: Assertion " << node
          << " is a literal, id: " << id << ", pol: " << negated << "\n";
      NewProofManager::currentPM()->addCnfProofStep(lit, id);
    });
  }
    break;
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
