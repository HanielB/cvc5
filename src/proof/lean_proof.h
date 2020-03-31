/*********************                                                        */
/*! \file lean_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof to be output in the Lean proof format.
 **/

#include "cvc4_private.h"
#include "expr/node.h"
#include "proof/new_proof.h"
#include "proof/new_proof_manager.h"
#include "theory/theory.h"

#ifndef CVC4__LEAN_PROOF_H
#define CVC4__LEAN_PROOF_H

namespace CVC4 {

class LeanProofStep : public ProofStep
{
 public:
  LeanProofStep(ClauseId id, NewProofRule rule = RULE_UNDEF);
  ~LeanProofStep() override {}

  void addRule(NewProofRule rule);
  void addPremises(std::vector<ClauseId>& reasons);
  void addPremise(ClauseId reason);
  void addArg(Node arg);
  void addArgs(std::vector<Node>& args);
  void addUnsignedArg(unsigned uarg);
  void addUnsignedArgs(std::vector<unsigned>& uargs);
  void addConclusion(Node conclusion);
  void addConclusion(std::vector<Node>& conclusion);

  const std::vector<Node>& getConclusion() const;
  const std::vector<Node>& getArgs() const;
  const std::vector<unsigned>& getUnsignedArgs() const;
  const std::vector<ClauseId>& getPremises() const;

 private:
  std::vector<Node> d_conclusion;
  std::vector<Node> d_args;
  std::vector<unsigned> d_unsigned_args;
  std::vector<ClauseId> d_premises;
};

class LeanProof : public NewProof
{
 public:
  ~LeanProof() override {}
  void toStream(std::ostream& out) const override;

  void finishProof() override;

  ClauseId addProofStep(NewProofRule rule) override;
  ClauseId addProofStep();

  ClauseId addProofStep(NewProofRule rule,
                        std::vector<ClauseId>& reasons,
                        Node conclusion);
  ClauseId addProofStep(NewProofRule rule,
                        std::vector<ClauseId>& reasons,
                        std::vector<Node>& conclusion);
  ClauseId addProofStep(NewProofRule rule,
                        std::vector<ClauseId>& reasons,
                        std::vector<Node>& conclusion,
                        unsigned u_arg);
  ClauseId addProofStep(NewProofRule rule,
                        std::vector<ClauseId>& reasons,
                        std::vector<Node>& args,
                        std::vector<Node>& conclusion);
  ClauseId addProofStep(NewProofRule rule, Node conclusion);
  ClauseId addProofStep(NewProofRule rule, Node conclusion, Node arg);

  ClauseId addResSteps(std::vector<Resolution>& reasons, Node conclusion);

  // Transform resolution chain into a series of binary resolutions with
  // *explicit* conclusions
  //
  // This is problematic when we reach conflicts with clauses that have not had
  // their proof steps defined yet
  //
  // Another issue for that is having to compute the intermediate clauses and
  // this can be problematic with pivots for example containing ITE skolems
  ClauseId addResStepsBin(std::vector<Resolution>& reasons, Node conclusion);

  ClauseId addIteIntroProofStep(Node conclusion);

  // add to last created proof step
  void addToLastProofStep(Node conclusion);
  void addToLastProofStep(std::vector<ClauseId>& reasons, Node conclusion);
  void addToLastProofStep(std::vector<ClauseId>& reasons,
                          std::vector<Node>& args,
                          Node conclusion);

  // add to proof step of the given id
  void addToProofStep(ClauseId id, Node conclusion);
  void addToProofStep(ClauseId id, NewProofRule rule, Node conclusion);
  void addToProofStep(ClauseId id,
                      NewProofRule rule,
                      std::vector<Node>& conclusion);
  void addToProofStep(ClauseId id,
                      NewProofRule rule,
                      std::vector<ClauseId>& reasons,
                      std::vector<Node>& conclusion);
  void addToProofStep(ClauseId id,
                      NewProofRule rule,
                      std::vector<ClauseId>& reasons,
                      std::vector<Node>& args,
                      std::vector<Node>& conclusion);

  // as above but specific for CNF rules, in particular those that without
  // premises
  //
  // the ith value is position of the literal being derived from an n-ary
  // transformation. If none, ith = -1
  void addToCnfProofStep(ClauseId id,
                         NewProofRule rule,
                         std::vector<Node>& conclusion,
                         unsigned ith);

  ClauseId addTheoryProof(theory::EqProof* proof);

  const std::vector<LeanProofStep>& getProofSteps() const;

  ClauseId getId() { return d_nextId; }

  // allows a node to me marked as an ITE place holder, so that it is not
  // printed in the proof, with the ITE term it represens being printed instead
  void notifyIte(Node src, Node dest);

 private:
  ClauseId getNextId() { return d_nextId++; }

  // adds a symmetry step if eq is t2 = t1, in which id is the justification for
  // t1 = t2 which will be resolved against. Otherwise returns undef id
  ClauseId maybeAddSymmStep(ClauseId id, Node eq, Node t1);

  ClauseId maybeAddFactoringStep(ClauseId id);

  ClauseId processTheoryProof(theory::EqProof* proof);

  void printPremises(std::ostream& out, const std::vector<ClauseId>& premises) const;
  void printRule(std::ostream& out, LeanProofStep* s) const;
  void printStep(std::ostream& main,
                 std::ostream& steps,
                 LeanProofStep* s) const;
  void printSortDecl(std::ostream& out, TypeNode sort) const;
  void printSort(std::ostream& out, TypeNode sort) const;
  void printTerm(std::ostream& out, Node n, bool decl = false) const;
  void printTermList(std::ostream& out, Node n) const;
  void printTermList(std::ostream& out, const std::vector<Node>& n) const;
  void printConstant(std::ostream& out, Node n, bool decl = false) const;

  void collectTerms(Node n);
  void collectTerms(LeanProofStep* s);

  void bind(Node term);

  std::vector<LeanProofStep> d_proofSteps;

  std::vector<std::vector<Node>> d_inputs;
  std::unordered_set<Node, NodeHashFunction> d_terms;
  std::unordered_set<TypeNode, TypeNodeHashFunction> d_sorts;
  std::unordered_map<TypeNode, std::string, TypeNodeHashFunction> d_sortDefs;
  std::unordered_map<Node, ProofLetCount, NodeHashFunction> d_letMap;
  NewBindings d_letOrder;
  std::unordered_map<Node, Node, NodeHashFunction> d_IteConst;
};

}  // namespace CVC4

#endif /* CVC4__LEAN_PROOF_H */
