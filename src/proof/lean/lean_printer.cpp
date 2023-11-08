/*********************                                                        */
/*! \file lean_printer.cpp
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

#include "proof/lean/lean_printer.h"

#include <iostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/printer_options.h"
#include "proof/lean/lean_node_converter.h"
#include "proof/lean/lean_rules.h"
#include "util/string.h"

namespace cvc5::internal {

namespace proof {

LeanLetUpdaterPfCallback::LeanLetUpdaterPfCallback(LetBinding& lbind,
                                                   std::map<Node, Node>& skMap,
                                                   std::set<LeanRule>& letRules)
    : d_lbind(lbind), d_skMap(skMap), d_letRules(letRules)
{
}

LeanLetUpdaterPfCallback::~LeanLetUpdaterPfCallback() {}

bool LeanLetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                            const std::vector<Node>& fa,
                                            bool& continueUpdate)
{
  const std::vector<Node>& args = pn->getArguments();
  // Letification done on the converted terms (thus from the converted
  // conclusion) and potentially on arguments, which means to ignore the first
  // two arguments (which are the Lean rule id and the original conclusion).
  //
  // Also, ignore conclusions of partial steps
  size_t i = d_letRules.find(getLeanRule(args[0])) == d_letRules.end() ? 2 : 3;
  for (size_t size = args.size(); i < size; ++i)
  {
    Trace("lean-printer") << "Process " << args[i] << "\n";
    // We do not process directly "lists", which we use only to aggregate
    // arguments. We assume that s-expressions as *proof node arguments* with a
    // raw symbol as first argument are all of the form ([ ... ]).
    //
    // Note that we could be sure of the shape if we were to print into a string
    // the argument (as we do e.g. in printTerm), then check if its first
    // positions are "([". This is alike to what is done in cleanSymbols to
    // normalize the printed stuff.
    if (args[i].getKind() == kind::SEXPR && args[i].getNumChildren() > 0
        && args[i][0].getKind() == kind::RAW_SYMBOL)
    {
      for (const auto& arg : args[i])
      {
        d_lbind.process(arg);
      }
      continue;
    }
    d_lbind.process(args[i]);
  }
  // no update to be made
  return false;
}

LeanPrinter::LeanPrinter(Env& env, LeanNodeConverter& lnc)
    : EnvObj(env),
      d_letRules({
          LeanRule::R0_PARTIAL,
          LeanRule::R1_PARTIAL,
          LeanRule::BIND_PARTIAL,
          LeanRule::BIND_LAMBDA_PARTIAL,
          LeanRule::TRANS_PARTIAL,
          LeanRule::AND_INTRO_PARTIAL,
          LeanRule::INST_FORALL_PARTIAL,
          LeanRule::SKOLEMIZE_PARTIAL,
      }),
      d_tacticRules({
          {LeanRule::R0, false},
          {LeanRule::R0_PARTIAL, false},
          {LeanRule::R1, false},
          {LeanRule::R1_PARTIAL, false},
          {LeanRule::REORDER, false},
          {LeanRule::FACTORING, false},
          {LeanRule::LIFT_OR_N_TO_IMP, false},
          {LeanRule::LIFT_OR_N_TO_NEG, false},
          {LeanRule::TH_TRUST_VALID, false},
          {LeanRule::AND_ELIM, false},
          {LeanRule::NOT_OR_ELIM, false},
          {LeanRule::SUM_BOUNDS, true},
          {LeanRule::SMT_CONG, true},
          {LeanRule::TRICHOTOMY, false},
          {LeanRule::INT_TIGHT_UB, false},
          {LeanRule::INT_TIGHT_LB, false},
          {LeanRule::ARITH_MULT_POS, false},
          {LeanRule::ARITH_MULT_NEG, false},
          {LeanRule::ARITH_MULT_SIGN, false},
          {LeanRule::RARE_REWRITE, false},
      }),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1
                                          : 0),
      d_lnc(lnc),
      d_cb(new LeanLetUpdaterPfCallback(d_lbind, d_skMap, d_letRules))
{
  d_false = NodeManager::currentNM()->mkConst(false);
}
LeanPrinter::~LeanPrinter() {}

void LeanPrinter::cleanSymbols(std::string& s)
{
  size_t startPos = 0;
  while ((startPos = s.find("|__LEAN_TMP", startPos)) != std::string::npos)
  {
    Unreachable();
    // stuff is "|__LEAN_TMP$WHATICARE|", so it's needed to kill one after
    // this prefix as well, which after the first replacement is just one after
    // startPos
    s.replace(startPos, 11, "");
    s.replace(startPos + 1, 1, "");
  }
  // also account for cases of like numbers which do not get wrapped if the
  // prefix was used
  startPos = 0;
  while ((startPos = s.find("__LEAN_TMP", startPos)) != std::string::npos)
  {
    // stuff is "__LEAN_TMP$WHATICARE", so just kill prefix
    s.replace(startPos, 10, "");
  }
  // also kill trailing spaces after "[" and before "," or "]"
  startPos = 0;
  while ((startPos = s.find("[ ", startPos)) != std::string::npos)
  {
    s.replace(startPos + 1, 1, "");
  }
  startPos = 0;
  while ((startPos = s.find(" ]", startPos)) != std::string::npos
         || (startPos = s.find(" ,", startPos)) != std::string::npos)
  {
    s.replace(startPos, 1, "");
  }
  startPos = 0;
  while ((startPos = s.find(" ,", startPos)) != std::string::npos)
  {
    s.replace(startPos, 1, "");
  }
  // If first symbols are "([", remove first and last symbols
  if (s.find("([", 0) == 0)
  {
    s.replace(0, 1, "");
    s.replace(s.size() - 1, 1, "");
  }
}

void LeanPrinter::printOffset(std::ostream& out, uint64_t offset) const
{
  for (uint64_t i = 0; i < offset; ++i)
  {
    out << "  ";
  }
}

void LeanPrinter::printSort(std::ostream& out, TypeNode tn)
{
  // must clean indexed symbols
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  d_lnc.typeAsNode(tn).toStream(ss);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s;
}

void LeanPrinter::printTerm(std::ostream& out, TNode n, bool letTop)
{
  // must clean indexed symbols
  std::stringstream ss;
  Node nc = d_lbind.convert(n, "let", letTop);
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  nc.toStream(ss);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s << (letTop ? "" : "\n");
}

void LeanPrinter::printLetList(std::ostream& out)
{
  std::vector<Node> letList;
  d_lbind.letify(letList);
  for (TNode n : letList)
  {
    size_t id = d_lbind.getId(n);

    out << "  let let" << id << " := ";
    printTerm(out, n, false);
  }
}

void LeanPrinter::printStepId(std::ostream& out,
                              const ProofNode* pfn,
                              const std::map<const ProofNode*, size_t>& pfMap,
                              const std::map<Node, size_t>& pfAssumpMap)
{
  out << "lean_";
  if (pfn->getRule() == PfRule::ASSUME)
  {
    // converted assumption
    Node conv = d_lnc.convert(pfn->getResult());
    AlwaysAssert(pfAssumpMap.find(conv) != pfAssumpMap.end())
        << "Original: " << pfn->getResult() << "\nConverted: " << conv;
    size_t id = pfAssumpMap.find(conv)->second;
    out << (id < d_nNewAssumptions[0]   ? "h"
            : id < d_nNewAssumptions[1] ? "r"
                                        : "a");
    out << id;
  }
  else
  {
    AlwaysAssert(pfMap.find(pfn) != pfMap.end());
    out << "s" << pfMap.find(pfn)->second;
  }
}

void LeanPrinter::printProof(std::ostream& out,
                             size_t& id,
                             uint64_t offset,
                             std::shared_ptr<ProofNode> pfn,
                             std::map<const ProofNode*, size_t>& pfMap,
                             std::map<Node, size_t>& pfAssumpMap,
                             bool firstScope)
{
  std::map<const ProofNode*, size_t>::const_iterator pfIt =
      pfMap.find(pfn.get());
  if (pfIt != pfMap.end())
  {
    return;
  }
  if (pfn->getRule() == PfRule::ASSUME)
  {
    return;
  }
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  // The result to be printed is the third argument of the LEAN_RULE
  TNode res = pfn->getArguments()[2];
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: offset " << offset << "\n";
  Trace("test-lean") << "printProof: args " << args << "\n";
  Trace("test-lean") << "printProof: rule " << rule << "\n";
  Trace("test-lean") << "printProof: result " << res << "\n-----------\n";
  if (rule == LeanRule::UNKNOWN)
  {
    // save proof step in map
    pfMap[pfn.get()] = id++;
    out << "Unhandled: " << rule << " " << args << "\n";
    return;
  }
  // we handle DSL rewrites differently because what to print depends on whether
  // it's a "list rule"
  // if (rule == LeanRule::DSL_REWRITE)
  // {

  // }
  // we handle scope differently because it starts a subproof
  if (rule == LeanRule::SCOPE)
  {
    printOffset(out, offset);
    out << "have lean_s" << id << " : ";
    // print conversion to a clause of the original scope's conclusion
    printTerm(out, res);
    out << " :=\n";
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof. To avoid clashes, we shift the assumptions numbers by
    // current pfAssumpMap' size
    size_t assumptionsShift = pfAssumpMap.size();
    std::map<Node, size_t> backupMap;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = assumptionsShift + i - 3;
      // push and print offset
      printOffset(out, ++offset);
      out << "(scope (fun lean_a" << assumptionsShift + i - 3 << " : ";
      printTerm(out, args[i]);
      out << " =>\n";
    }
    // similarly, we shift step ids by the number of current steps
    size_t newId = pfMap.size();
    // use a new proof map for subproof
    std::map<const ProofNode*, size_t> subpfMap{pfMap};
    Trace("test-lean") << pop;
    AlwaysAssert(children.size() == 1);
    printProof(out, newId, ++offset, children[0], subpfMap, pfAssumpMap);
    Trace("test-lean") << pop;
    // print conclusion of scope's child if result is not "false". For now this
    // is a redundant step because the proof can't end with "have" but rather
    // with "show", and unless the conclusion of the scope is "false" the
    // keyword used would have been "false".
    if (children[0]->getResult() != d_false)
    {
      printOffset(out, offset);
      out << "show ";
      printTerm(out, children[0]->getArguments()[2]);
      out << " from ";
      printStepId(out, children[0].get(), subpfMap, pfAssumpMap);
      out << "\n";
    }
    // now close. We have assumptions*2 parens
    std::stringstream cparens;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      offset--;
      cparens << "))";
    }
    printOffset(out, offset);
    out << cparens.str() << "\n";
    // recover assumption map
    for (const auto& p : backupMap)
    {
      pfAssumpMap[p.first] = p.second;
    }
    // save proof step in map
    pfMap[pfn.get()] = id++;
    return;
  }
  Trace("test-lean") << push;
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    printProof(out, id, offset, child, pfMap, pfAssumpMap);
  }
  Trace("test-lean") << pop;
  printOffset(out, offset);
  auto it = d_tacticRules.find(rule);
  bool isTactic = it != d_tacticRules.end();
  bool isNaryTactic = isTactic && it->second;
  // print conclusion: proof node concludes `false`, print as show ... rather
  // than have s....
  if (d_letRules.find(rule) != d_letRules.end())
  {
    out << "let lean_s" << id << " := " << (isTactic ? "by " : "by timed ") << rule;
  }
  else
  {
    Assert(!firstScope || pfn->getResult() == d_false);
    if (pfn->getResult() == d_false)
    {
      out << (firstScope ? "exact (" : "");
      out << "show False from " << (isTactic ? "by " : "by timed ") << rule;
    }
    else
    {
      out << "have lean_s" << id << " : ";
      printTerm(out, res);
      out << " := " << (isTactic ? "by " : "by timed ") << rule;
    }
  }
  std::string separator = isTactic ? ", " : " ";
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    out << (i == 0 ? (isNaryTactic ? " [" : " ") : separator);
    printStepId(out, children[i].get(), pfMap, pfAssumpMap);
  }
  out << (isNaryTactic ? "]" : "");
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    out << ((children.empty() && i == 3) ? " " : separator);
    printTerm(out, args[i]);
  }
  out << (firstScope ? ")" : "") << "\n";
  // save proof step in map
  pfMap[pfn.get()] = id++;
}

void LeanPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  if (TraceIsOn("test-lean-pf"))
  {
    std::stringstream ss;
    Trace("test-lean-pf") << "Post-processed proof ";
    pfn->printDebug(ss, true);
    Trace("test-lean-pf") << ss.str() << "\n";
  }
  // Print preamble
  out << "-- import Smt.Reconstruction.Certifying\nopen Classical\nopen "
         "Smt.Reconstruction.Certifying\n\n";
  // increase recursion depth and heartbeats
  out << "\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats "
         "500000\n\n";
  uint64_t thId;
  // The proof we will print is the one under the scope
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0];
  const std::vector<Node>& assumptions = pfn->getArguments();
  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  for (const Node& a : assumptions)
  {
    expr::getSymbols(a, syms, visited);
    thId += a.getId();
  }
  // uninterpreted sorts
  std::unordered_set<TypeNode> sts;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    std::unordered_set<TypeNode> ctypes;
    expr::getComponentTypes(st, ctypes);
    for (const TypeNode& stc : ctypes)
    {
      // ignore expression type
      if (stc == nm->sExprType())
      {
        continue;
      }
      // only collect non-predefined sorts for declaration
      if (stc.getKind() == kind::INSTANTIATED_SORT_TYPE)
      {
        Unreachable() << "Unsupported sort in Lean proofs\n";
      }
      if (stc.isUninterpretedSort() && stc.getKind() != kind::TYPE_CONSTANT)
      {
        Trace("test-lean") << "collecting sort " << stc << " with kind "
                           << stc.getKind() << "\n";
        sts.insert(stc);
      }
    }
  }
  if (!sts.empty())
  {
    out << "\nuniverse u\n";
  }
  for (const auto& s : sts)
  {
    out << "variable {";
    printSort(out, s);
    out << " : Type u} [Nonempty ";
    printSort(out, s);
    out << "]\n";
  }
  // uninterpreted functions
  for (const Node& s : syms)
  {
    // ignore symbolic stuff
    if (s.getType() == nm->sExprType())
    {
      continue;
    }
    std::string name = s.getName();
    LeanNodeConverter::cleanIdentifier(name);
    out << "variable {" << name << " : ";
    printSort(out, s.getType());
    out << "}\n";
  }

  // To provide more information, we use differente prefixes to whether the
  // added assumptions are coming from holes or from rewrites. These are the
  // first two arrays, the last is for the original assumptions
  std::vector<Node> convertedAssumptions[3];
  uint32_t nHoles =
      assumptions[3].getConst<Rational>().getNumerator().toUnsignedInt() + 4;
  uint32_t nRewrites =
      assumptions[nHoles].getConst<Rational>().getNumerator().toUnsignedInt()
      + nHoles + 1;
  d_nNewAssumptions[0] = nHoles - 4;
  d_nNewAssumptions[1] = nRewrites - 5;
  Trace("test") << "nHoles: " << nHoles - 4 << ", " << assumptions[3] << "\n";
  Trace("test") << "nRewrites: " << nRewrites - nHoles - 1 << ", "
                << assumptions[nHoles] << "\n";
  Trace("test") << "nNewASsumptions: " << d_nNewAssumptions[0] << ", "
                << d_nNewAssumptions[1] << "\n";
  size_t i = 4;
  for (; i < nHoles; ++i)
  {
    Trace("test") << "Hole: " << assumptions[i] << "\n";
    convertedAssumptions[0].push_back(assumptions[i]);
    d_lbind.process(convertedAssumptions[0].back());
  }
  // to skip the position with the number of rewrites
  ++i;
  Trace("test") << "Went from 4 to " << i << ", " << assumptions[i] << "\n";
  for (; i < nRewrites; ++i)
  {
    Trace("test") << "Rewrite: " << assumptions[i] << "\n";
    convertedAssumptions[1].push_back(assumptions[i]);
    d_lbind.process(convertedAssumptions[1].back());
  }
  Trace("test") << "Went to " << i << ", " << assumptions[i] << "\n";
  for (size_t size = assumptions.size(); i < size; ++i)
  {
    convertedAssumptions[2].push_back(d_lnc.convert(assumptions[i]));
    d_lbind.process(convertedAssumptions[2].back());
  }

  // Traverse the proof node to letify the (converted) conclusions of explicit
  // proof steps.
  ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
  updater.process(innerPf);

  // print theorem statement, which is to get proofs of all the assumptions
  // and conclude a proof of False. The assumptions are args[3..]
  // out << "\ntheorem th" << thId << " : ";
  out << "\ntheorem th0 :\n";
  // if any lets, print them for the theory statement.
  std::stringstream letList;
  printLetList(letList);
  out << letList.str();
  for (size_t j = 0; j < 3; ++j)
  {
    for (const Node& a : convertedAssumptions[j])
    {
      Assert(j >= 2 || a.getKind() == kind::SEXPR)
          << "Broke with j " << j << ", " << a;
      printTerm(out, d_lnc.convert(j < 2 ? a[0] : a));
      out << " → ";
    }
  }
  out << "False :=\n";
  // if any lets, print them again, for the proof
  out << letList.str();
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t j = 0, id = 0; j < 3; ++j)
  {
    std::string prefix = j == 0 ? "h" : j == 1 ? "r" : "a";
    for (size_t k = 0, size = convertedAssumptions[j].size(); k < size; ++k)
    {
      Node a =
          j < 2 ? convertedAssumptions[j][k][0] : convertedAssumptions[j][k];
      pfAssumpMap[a] = id;
      out << "fun lean_" << prefix << id++ << " : ";
      printTerm(out, a);
      out << " =>";
      // print reason, if there is one
      if (j < 2)
      {
        out << " -- " << convertedAssumptions[j][k][1];
      }
      // guarantee we use Lean's tactic mode by adding " by " after last
      // assertion
      out << (j == 2 && k == size - 1 ? " by" : "") << "\n";
    }
  }
  std::stringstream ss;
  ss << out.rdbuf();
  size_t id = 0;
  Trace("test-lean") << "Before getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  std::map<const ProofNode*, size_t> pfMap;
  // Handle corner case: False → False
  if (innerPf->getRule() == PfRule::ASSUME)
  {
    Assert(innerPf->getResult() == d_false);
    out << "exact show ";
    printTerm(out, d_lnc.convert(d_false));
    out << " from ";
    printStepId(out, innerPf.get(), pfMap, pfAssumpMap);
    out << "\n";
  }
  else
  {
    printProof(out, id, 0, innerPf, pfMap, pfAssumpMap, true);
  }
  ss.clear();
  ss << out.rdbuf();
  Trace("test-lean") << "After getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5::internal
