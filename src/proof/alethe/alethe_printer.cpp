/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "expr/node_algorithm.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "util/smt2_quote_string.h"

namespace cvc5::internal {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(AletheLetBinding& lbind)
    : d_lbind(lbind)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        CVC5_UNUSED const std::vector<Node>& fa,
                                        CVC5_UNUSED bool& continueUpdate)
{
  ProofRule r = pn->getRule();
  if (r == ProofRule::ASSUME)
  {
    d_lbind.process(pn->getResult());
    return false;
  }
  const std::vector<Node>& args = pn->getArguments();
  if (r == ProofRule::SCOPE)
  {
    for (size_t i = 0, size = args.size(); i < size; ++i)
    {
      d_lbind.process(args[i]);
    }
    return false;
  }
  // Letification done on the converted terms (thus from the converted
  // conclusion) and potentially on arguments, which means to ignore the first
  // two arguments (which are the Alethe rule and the original conclusion).
  AlwaysAssert(args.size() > 2)
      << "res: " << pn->getResult() << "\nid: " << pn->getRule();
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    Trace("alethe-printer") << "Process " << args[i] << std::endl;
    // We do not share s-expressions, but rather their children
    if (args[i].getKind() == Kind::SEXPR)
    {
      for (const auto& arg : args[i])
      {
        d_lbind.process(arg);
      }
      continue;
    }
    d_lbind.process(args[i]);
  }
  return false;
}

AletheProofPrinter::AletheProofPrinter(Env& env,
                                       AletheNodeConverter& anc,
                                       const AletheStepDepsMap& stepDeps)
    : EnvObj(env),
      d_stepDeps(stepDeps),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1
                                          : 0),
      d_anc(anc),
      d_cb(new LetUpdaterPfCallback(d_lbind))
{
}

std::string AletheProofPrinter::assumptionId(const Node& res, size_t lvl)
{
  for (size_t l = std::min(lvl, d_frames.size() - 1); l >= 1; --l)
  {
    auto it = d_frames[l]->d_assumeIds.find(res);
    if (it != d_frames[l]->d_assumeIds.end())
    {
      return it->second;
    }
  }
  auto it = d_assumptionIds.find(res);
  AlwaysAssert(it != d_assumptionIds.end())
      << "Assumption has not been printed yet! " << res << std::endl;
  return it->second;
}

void AletheProofPrinter::printStepId(std::ostream& out,
                                     std::shared_ptr<ProofNode> pfn,
                                     size_t lvl)
{
  if (pfn->getRule() == ProofRule::ASSUME)
  {
    Node res = d_anc.convert(pfn->getResult());
    Assert(!res.isNull());
    Trace("alethe-printer") << "... reached assumption " << res << std::endl;
    out << assumptionId(res, lvl);
    return;
  }
  auto itStep = d_stepIds.find(pfn.get());
  AlwaysAssert(itStep != d_stepIds.end())
      << "Cannot find pf of " << pfn->getResult() << " with rule "
      << getAletheRule(pfn->getArguments()[0]) << std::endl;
  out << itStep->second;
}

void AletheProofPrinter::printTerm(std::ostream& out, TNode n)
{
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  // We print lambda applications in non-curried manner
  options::ioutils::applyFlattenHOChains(ss, true);
  // Make sure we do not introduce "let" for sharing, since names will not have
  // been introduced under binders.
  options::ioutils::applyDagThresh(ss, 0);
  // Guarantee we print reals as expected
  options::ioutils::applyPrintArithLitToken(ss, true);
  ss << d_lbind.convert(nodeManager(), n, "@p_");
  out << ss.str();
}

void AletheProofPrinter::print(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const std::map<Node, std::string>& assertionNames)
{
  Trace("alethe-printer") << "- Print proof in Alethe format." << std::endl;
  // reset the printing state
  d_frames.clear();
  d_frames.push_back(std::make_unique<Frame>());
  d_stepIds.clear();
  d_stepFrames.clear();
  d_assumptionIds.clear();
  d_topOut = &out;
  // ignore outer scope
  pfn = pfn->getChildren()[0];
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0];
  Assert(innerPf);

  // print quantifier Skolems, if they are being defined
  if (options().proof.proofAletheDefineSkolems)
  {
    const std::map<Node, Node>& skolemDefs = d_anc.getSkolemDefinitions();
    const std::vector<Node>& skolemList = d_anc.getSkolemList();
    for (const auto& skolem : skolemList)
    {
      Assert(skolemDefs.find(skolem) != skolemDefs.end());
      out << "(define-fun " << skolem << " () " << skolem.getType() << " ";
      printTerm(out, skolemDefs.at(skolem));
      out << ")" << std::endl;
    }
  }
  if (options().printer.dagThresh)
  {
    // Traverse the proof node to letify the (converted) conclusions of proof
    // steps. Note that we traverse the original proof node because assumptions
    // may apper just in them (if they are not used in the rest of the proof).
    // Otherwise repeated terms *only* in assumptions would not be letified.
    ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
    Trace("alethe-printer") << "- letify." << std::endl;
    updater.process(pfn);

    std::vector<Node> letList;
    d_lbind.letify(letList);
    if (TraceIsOn("alethe-printer"))
    {
      for (TNode n : letList)
      {
        Trace("alethe-printer")
            << "Term " << n << " has id " << d_lbind.getId(n) << std::endl;
      }
    }
  }
  Trace("alethe-printer") << "- Print assumptions." << std::endl;
  const std::vector<Node>& args = pfn->getArguments();
  // Special handling for the first scope. Print assumptions and add them to the
  // list but do not print anchor.
  Assert(!args.empty());
  for (size_t i = 0, size = args.size(); i < size; i++)
  {
    // search name with original assumption rather than its conversion
    Assert(!d_anc.getOriginalAssumption(args[i]).isNull());
    Node original = d_anc.getOriginalAssumption(args[i]);
    auto it = assertionNames.find(original);
    if (it != assertionNames.end())
    {
      // Since names can be strings that were originally quoted, we must see if
      // the quotes need to be added back.
      std::string quotedName = quoteSymbol(it->second);
      out << "(assume " << quotedName << " ";
      d_assumptionIds[args[i]] = quotedName;
    }
    else
    {
      out << "(assume a" << i << " ";
      d_assumptionIds[args[i]] = "a" + std::to_string(i);
    }
    printTerm(out, args[i]);
    out << ")" << std::endl;
  }
  // Then, print the rest of the proof node and render it. The proof is
  // constructed as items first and rendered in output order at the end, so
  // that terms are converted (and shared terms are defined) in that order.
  printInternal(pfn->getChildren()[0]);
  Assert(d_frames.size() == 1);
  renderItems(out, d_frames[0]->d_items);
}

void AletheProofPrinter::renderItems(std::ostream& out,
                                     const std::vector<OutItem>& items)
{
  for (const OutItem& item : items)
  {
    renderItem(out, item);
  }
}

void AletheProofPrinter::renderItem(std::ostream& out, const OutItem& item)
{
    if (item.d_isAnchor)
    {
      out << "(anchor :step " << item.d_id;
      if (item.d_rule == AletheRule::ANCHOR_SUBPROOF)
      {
        out << ")" << std::endl;
        for (const auto& [id, term] : item.d_anchorAssumes)
        {
          out << "(assume " << id << " ";
          printTerm(out, term);
          out << ")" << std::endl;
        }
      }
      else
      {
        out << " :args (";
        for (size_t i = 0, size = item.d_args.size(); i < size; ++i)
        {
          const Node& arg = item.d_args[i];
          if (arg.getKind() == Kind::EQUAL)
          {
            out << "(:= (" << arg[0] << " " << arg[0].getType() << ") ";
            printTerm(out, arg[1]);
            out << ")" << (i != item.d_args.size() - 1 ? " " : "");
            continue;
          }
          out << "(" << arg << " " << arg.getType() << ") ";
        }
        out << "))" << std::endl;
      }
      renderItems(out, item.d_items);
      out << "(step " << item.d_id << " ";
      printTerm(out, item.d_conclusion);
      out << " :rule " << item.d_rule;
      if (item.d_rule == AletheRule::ANCHOR_SUBPROOF)
      {
        out << " :discharge (";
        for (size_t i = 0, size = item.d_anchorAssumes.size(); i < size; ++i)
        {
          out << item.d_anchorAssumes[i].first << (i < size - 1 ? " " : "");
        }
        out << ")";
      }
      out << ")" << std::endl;
      return;
    }
    out << "(step " << item.d_id << " ";
    printTerm(out, item.d_conclusion);
    out << " :rule " << item.d_rule;
    if (!item.d_premises.empty())
    {
      out << " :premises (";
      for (size_t i = 0, size = item.d_premises.size(); i < size; ++i)
      {
        out << item.d_premises[i] << (i < size - 1 ? " " : "");
      }
      out << ")";
    }
    if (!item.d_args.empty())
    {
      out << " :args (";
      for (size_t i = 0, size = item.d_args.size(); i < size; ++i)
      {
        printTerm(out, item.d_args[i]);
        out << (i < size - 1 ? " " : "");
      }
      out << ")";
    }
    out << ")" << std::endl;
}

void AletheProofPrinter::emitItem(OutItem&& item, size_t lvl)
{
  // Top-level items can be rendered as soon as they are created: items are
  // only ever appended, so append order is output order, and this way the
  // top level, which dominates large proofs, is not buffered in memory.
  if (lvl == 0)
  {
    renderItem(*d_topOut, item);
    return;
  }
  d_frames[lvl]->d_items.push_back(std::move(item));
}

size_t AletheProofPrinter::premiseLevel(const std::shared_ptr<ProofNode>& premise)
{
  auto it = d_stepFrames.find(premise.get());
  if (it != d_stepFrames.end())
  {
    for (size_t i = d_frames.size(); i-- > 0;)
    {
      if (d_frames[i].get() == it->second)
      {
        return i;
      }
    }
    // The premise was printed under a frame that does not enclose the current
    // position (it was set aside for an anchor printed below its target), so
    // its id is not visible from here: print its derivation again in the
    // current chain.
    d_stepIds.erase(premise.get());
    d_stepFrames.erase(it);
  }
  printInternal(premise);
  it = d_stepFrames.find(premise.get());
  AlwaysAssert(it != d_stepFrames.end())
      << "Premise " << premise->getResult() << " left unprinted" << std::endl;
  for (size_t i = d_frames.size(); i-- > 0;)
  {
    if (d_frames[i].get() == it->second)
    {
      return i;
    }
  }
  Unreachable() << "Premise " << premise->getResult()
                << " printed outside the active chain" << std::endl;
}

AletheProofPrinter::OutItem AletheProofPrinter::stepItem(
    const std::shared_ptr<ProofNode>& pfn,
    const std::string& stepId,
    size_t lvl)
{
  OutItem item;
  item.d_id = stepId;
  const std::vector<Node>& args = pfn->getArguments();
  item.d_rule = getAletheRule(args[0]);
  item.d_conclusion = args[2];
  item.d_args.insert(item.d_args.end(), args.begin() + 3, args.end());
  for (const std::shared_ptr<ProofNode>& child : pfn->getChildren())
  {
    if (child->getRule() == ProofRule::ASSUME)
    {
      Node res = d_anc.convert(child->getResult());
      Assert(!res.isNull());
      item.d_premises.push_back(assumptionId(res, lvl));
      continue;
    }
    auto itStep = d_stepIds.find(child.get());
    AlwaysAssert(itStep != d_stepIds.end())
        << "Cannot find pf of " << child->getResult() << std::endl;
    item.d_premises.push_back(itStep->second);
  }
  return item;
}

size_t AletheProofPrinter::targetFrame(const std::shared_ptr<ProofNode>& pfn)
{
  // with no anchor open the derivation can only be printed at the top level
  if (d_frames.size() == 1)
  {
    return 0;
  }
  // without subproof sharing each derivation is printed where the traversal
  // reaches it, i.e., within the current subproof (a shared derivation is
  // replayed in every subproof using it, as ids die with their subproof)
  if (!options().proof.proofAletheShareSubproofs)
  {
    return d_frames.size() - 1;
  }
  const auto itDeps = d_stepDeps.find(pfn.get());
  AlwaysAssert(itDeps != d_stepDeps.end())
      << "No dependencies were computed for " << pfn->getResult() << std::endl;
  const AletheStepDeps& deps = itDeps->second;
  if (deps.d_vars.empty() && deps.d_assumptions.empty())
  {
    return 0;
  }
  // The derivation must be printed at or below the deepest frame that binds
  // one of the variables it mentions: there the ambient assignments of those
  // variables are exactly the ones of its original position, so its checking
  // is unaffected (frames below only assign variables it does not mention),
  // and its variables are declared. If a variable is bound by no frame the
  // derivation stays at its original position.
  size_t target = 0;
  bool unbound = false;
  for (const Node& v : deps.d_vars)
  {
    size_t lvl = d_frames.size();
    while (lvl > 1)
    {
      lvl--;
      if (d_frames[lvl]->d_boundVars.count(v))
      {
        break;
      }
    }
    if (lvl <= 1 && (d_frames.size() < 2 || !d_frames[1]->d_boundVars.count(v)))
    {
      unbound = true;
      break;
    }
    target = std::max(target, lvl);
  }
  if (unbound)
  {
    return d_frames.size() - 1;
  }
  // Each assumption must be available at some frame at or above the target:
  // for each, the outermost frame providing it suffices (an assumption of the
  // same term is interchangeable wherever it is assumed).
  for (const Node& a : deps.d_assumptions)
  {
    size_t lvl = 1;
    for (size_t size = d_frames.size(); lvl < size; ++lvl)
    {
      if (d_frames[lvl]->d_assumptions.count(a))
      {
        break;
      }
    }
    if (lvl == d_frames.size())
    {
      // provided by no frame: stay at the original position
      return d_frames.size() - 1;
    }
    target = std::max(target, lvl);
  }
  return target;
}

void AletheProofPrinter::printInternal(std::shared_ptr<ProofNode> pfn)
{
  // assumptions are not printed when reached here because in Alethe they are
  // always printed beforehand, i.e., from the scope introducing them, or being
  // the initial assumptions.
  if (pfn->getRule() == ProofRule::ASSUME)
  {
    return;
  }
  const auto pfIt = d_stepIds.find(pfn.get());
  if (pfIt != d_stepIds.end())
  {
    Trace("alethe-printer") << "... step is already printed " << pfIt->second
                            << " " << pfn->getResult() << " "
                            << getAletheRule(pfn->getArguments()[0]) << "\n";
    return;
  }
  const std::vector<Node>& args = pfn->getArguments();
  AletheRule arule = getAletheRule(args[0]);
  Trace("alethe-printer") << "... print step " << arule << " : " << args[2]
                          << std::endl;
  // We special case printing anchors
  if (arule >= AletheRule::ANCHOR_SUBPROOF
      && arule <= AletheRule::ANCHOR_ONEPOINT)
  {
    // The anchor and its subproof are printed at the outermost frame under
    // which the derivation is well scoped (or the innermost frame, if this is
    // the concluding derivation of the anchor currently being printed).
    // Frames above the target are set aside during the printing: the
    // derivation does not depend on them, and this way the subproof steps
    // target the frames of this derivation only.
    size_t lvl = d_pinnedToInnermost == pfn.get() ? d_frames.size() - 1
                                                  : targetFrame(pfn);
    std::vector<std::unique_ptr<Frame>> saved;
    std::move(d_frames.begin() + lvl + 1,
              d_frames.end(),
              std::back_inserter(saved));
    d_frames.resize(lvl + 1);
    printAnchor(pfn, lvl);
    std::move(saved.begin(), saved.end(), std::back_inserter(d_frames));
    return;
  }
  // Print the steps for children to guarantee we will have ids for them in the
  // premises of this step
  const std::vector<std::shared_ptr<ProofNode>>& pfChildren =
      pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& pfChild : pfChildren)
  {
    Trace("alethe-printer") << push;
    printInternal(pfChild);
    Trace("alethe-printer") << pop;
  }
  // Print this step at the outermost frame under which it is well scoped,
  // unless it is the concluding derivation step of the anchor currently being
  // printed, which must stay within the subproof.
  // Since the output of open anchors is buffered until they complete, printing
  // into an outer frame places the step before the anchors that use it, and
  // its id remains available for as long as that frame is open. This avoids
  // replaying shared derivations in every subproof that uses them, which
  // could make the printed proof exponentially larger than the proof node DAG
  // being printed.
  size_t lvl = d_pinnedToInnermost == pfn.get() ? d_frames.size() - 1
                                                : targetFrame(pfn);
  // The step must not be placed above the frame of any of its premises: a
  // premise may be held by a deeper frame (e.g., pinned as the concluding
  // derivation of a subproof) whose ids die with it. A premise available in
  // no active frame (its frame was set aside for an anchor printed below its
  // target) is printed again in the current chain by premiseLevel.
  for (const std::shared_ptr<ProofNode>& pfChild : pfChildren)
  {
    if (pfChild->getRule() != ProofRule::ASSUME)
    {
      lvl = std::max(lvl, premiseLevel(pfChild));
    }
  }
  Frame& frame = *d_frames[lvl];
  std::string stepId = frame.d_prefix + "t" + std::to_string(frame.d_id++);
  d_stepIds[pfn.get()] = stepId;
  d_stepFrames[pfn.get()] = &frame;
  OutItem item = stepItem(pfn, stepId, lvl);
  frame.d_introducedSteps.push_back(pfn.get());
  emitItem(std::move(item), lvl);
}

void AletheProofPrinter::printAnchor(std::shared_ptr<ProofNode> pfn,
                                     size_t lvl)
{
  Trace("alethe-printer") << push;
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& pfChildren =
      pfn->getChildren();
  AletheRule arule = getAletheRule(args[0]);
  Assert(pfChildren.size() == 1);
  Frame& parent = *d_frames[lvl];
  // the concluding step of the anchor takes the parent frame's next id,
  // reserved eagerly: steps hoisted into the parent frame while the subproof
  // is being printed must not reuse it
  std::string stepId = parent.d_prefix + "t" + std::to_string(parent.d_id++);
  d_frames.push_back(std::make_unique<Frame>());
  Frame& frame = *d_frames.back();
  frame.d_prefix = stepId + ".";
  OutItem item;
  item.d_isAnchor = true;
  item.d_id = stepId;
  item.d_rule = arule;
  item.d_conclusion = args[2];
  item.d_args.insert(item.d_args.end(), args.begin() + 3, args.end());
  // if subproof, record assumptions, otherwise the declared variables
  if (arule == AletheRule::ANCHOR_SUBPROOF)
  {
    Assert(args.size() >= 3);
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      Trace("alethe-printer")
          << "... print assumption " << args[i] << std::endl;
      std::string aid = frame.d_prefix + "a" + std::to_string(i - 3);
      item.d_anchorAssumes.emplace_back(aid, args[i]);
      frame.d_assumeIds[args[i]] = aid;
      frame.d_assumptions.insert(args[i]);
    }
  }
  else
  {
    Assert(arule >= AletheRule::ANCHOR_BIND
           && arule <= AletheRule::ANCHOR_ONEPOINT);
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      if (args[i].getKind() == Kind::EQUAL)
      {
        Assert(args[i][0].getKind() == Kind::BOUND_VARIABLE);
        frame.d_boundVars.insert(args[i][0]);
        if (args[i][1].getKind() == Kind::BOUND_VARIABLE)
        {
          frame.d_boundVars.insert(args[i][1]);
        }
        continue;
      }
      Assert(args[i].getKind() == Kind::BOUND_VARIABLE) << args[i];
      frame.d_boundVars.insert(args[i]);
    }
  }
  // since the subproof shape relies on having at least one step inside it, if
  // the step relative to children[0] has already been printed, we should just
  // print the step again inside the subproof and be done
  if (d_stepIds.find(pfChildren[0].get()) != d_stepIds.end())
  {
    // its premises must be available from here (premiseLevel prints again any
    // whose frame does not enclose this position)
    for (const std::shared_ptr<ProofNode>& pfGChild :
         pfChildren[0]->getChildren())
    {
      if (pfGChild->getRule() != ProofRule::ASSUME)
      {
        premiseLevel(pfGChild);
      }
    }
    // emitted into the frame, after any premise premiseLevel printed there
    frame.d_items.push_back(
        stepItem(pfChildren[0],
                 frame.d_prefix + "t" + std::to_string(frame.d_id++),
                 d_frames.size() - 1));
  }
  else
  {
    const ProofNode* prevPinned = d_pinnedToInnermost;
    d_pinnedToInnermost = pfChildren[0].get();
    printInternal(pfChildren[0]);
    d_pinnedToInnermost = prevPinned;
  }
  // Close the frame: undo the ids it introduced and hand its items over. An
  // id is only undone while it still belongs to this frame: a step printed
  // again in another frame (see premiseLevel) has moved its entry there.
  Assert(&frame == d_frames.back().get());
  for (ProofNode* p : frame.d_introducedSteps)
  {
    auto itf = d_stepFrames.find(p);
    if (itf != d_stepFrames.end() && itf->second == &frame)
    {
      d_stepIds.erase(p);
      d_stepFrames.erase(itf);
    }
  }
  item.d_items.insert(item.d_items.end(),
                      std::make_move_iterator(frame.d_items.begin()),
                      std::make_move_iterator(frame.d_items.end()));
  d_frames.pop_back();
  d_stepIds[pfn.get()] = stepId;
  d_stepFrames[pfn.get()] = &parent;
  parent.d_introducedSteps.push_back(pfn.get());
  emitItem(std::move(item), lvl);
  Trace("alethe-printer") << pop;
}

}  // namespace proof
}  // namespace cvc5::internal
