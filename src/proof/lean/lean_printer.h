/*********************                                                        */
/*! \file lean_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN_PROOF_PRINTER_H
#define CVC4__PROOF__LEAN_PROOF_PRINTER_H

#include <iostream>
#include <sstream>
#include <string>

#include "expr/node_algorithm.h"
#include "printer/let_binding.h"
#include "proof/lean/lean_node_converter.h"
#include "proof/lean/lean_rules.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_updater.h"

namespace cvc5::internal {

class CDProof;

namespace proof {

class LeanLetUpdaterPfCallback : public ProofNodeUpdaterCallback
{
 public:
  LeanLetUpdaterPfCallback(LetBinding& lbind,
                           std::map<Node, Node>& skMap,
                           std::set<LeanRule>& letRules);
  ~LeanLetUpdaterPfCallback();

  /** Update let map according to terms in step pn. */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

 protected:
  LetBinding& d_lbind;
  std::map<Node, Node> d_skMap;
  std::set<LeanRule> d_letRules;
};

class LeanPrinter : protected EnvObj
{
 public:
  LeanPrinter(Env& env, LeanNodeConverter& lnc);
  ~LeanPrinter();

  /**
   * Print the full proof of assertions => false by pfn.
   */
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  void printSort(std::ostream& out, TypeNode tn);
  void printTerm(std::ostream& out, TNode n, bool letTop = true);

  void printLetList(std::ostream& out);

  /**
   * For each proof node, the final Lean output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the Lean proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
  void printProof(std::ostream& out,
                  size_t& id,
                  uint64_t offset,
                  std::shared_ptr<ProofNode> pfn,
                  std::map<const ProofNode*, size_t>& pfMap,
                  std::map<Node, size_t>& pfAssumpMap,
                  bool firstScope = false);

  void printOffset(std::ostream& out, uint64_t offset) const;

  void printStepId(std::ostream& out,
                   const ProofNode* pfn,
                   const std::map<const ProofNode*, size_t>& pfMap,
                   const std::map<Node, size_t>& pfAssumpMap);

  void cleanSymbols(std::string& s);

  Node d_false;

  std::set<LeanRule> d_letRules;
  /** Tactic rules and whether they are n-ary */
  std::map<LeanRule, bool> d_tacticRules;

  LetBinding d_lbind;

  std::map<Node, Node> d_skMap;

  LeanNodeConverter& d_lnc;

  std::unique_ptr<LeanLetUpdaterPfCallback> d_cb;
  size_t d_nNewAssumptions[2];
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
