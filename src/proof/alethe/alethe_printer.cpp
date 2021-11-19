/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <unordered_map>

#include "proof/alethe/alethe_proof_rule.h"

namespace cvc5 {

namespace proof {

AletheProofPrinter::AletheProofPrinter()
{
  nested_level = 0;
  step_id = 1;
  prefix = "";
  assumptions.push_back({});
  steps.push_back({});
}

void AletheProofPrinter::alethePrinter(std::ostream& out,
                                       std::shared_ptr<ProofNode> pfn)
{
  Trace("alethe-printer") << "- Print proof in Alethe format. " << std::endl;

  // Special handling for the first scope
  // Print assumptions and add them to the list but do not print anchor.
  for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
       i++)
  {
    Trace("alethe-printer")
        << "... print assumption " << pfn->getArguments()[i] << std::endl;
    out << "(assume a" << std::to_string(i - 3) << " " << pfn->getArguments()[i]
        << ")\n";
    assumptions[0][pfn->getArguments()[i]] = i - 3;
  }

  // Then, print the rest of the proof node
  alethePrinterInternal(out, pfn->getChildren()[0]);
}

std::string AletheProofPrinter::alethePrinterInternal(
    std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // Store current id in case a subproof overwrites step_id
  int current_step_id = step_id;

  // If the proof node is untranslated a problem might have occured during
  // postprocessing
  if (pfn->getArguments().size() < 3 || pfn->getRule() != PfRule::ALETHE_RULE)
  {
    Trace("alethe-printer")
        << "... printing failed! Encountered untranslated Node. "
        << pfn->getResult() << " " << toString(pfn->getRule()) << " "
        << " / " << pfn->getArguments() << std::endl;
    return "";
  }

  // Get the alethe proof rule
  AletheRule vrule =
      static_cast<AletheRule>(std::stoul(pfn->getArguments()[0].toString()));

  // In case the rule is an anchor it is printed before its children.
  if (vrule == AletheRule::ANCHOR_SUBPROOF || vrule == AletheRule::ANCHOR_BIND
      || vrule == AletheRule::ANCHOR_SKO_FORALL
      || vrule == AletheRule::ANCHOR_SKO_EX)
  {
    // Look up if subproof has already been printed
    auto it = steps[nested_level].find(pfn->getArguments()[2]);
    if (it != steps[nested_level].end())
    {
      Trace("alethe-printer")
          << "... subproof is already printed " << pfn->getResult() << " "
          << vrule << " / " << pfn->getArguments() << std::endl;
      return prefix + "t" + std::to_string(it->second);
    }

    // If not printed before, enter next level
    nested_level++;
    assumptions.push_back({});
    steps.push_back({});

    // Print anchor
    Trace("alethe-printer")
        << "... print anchor " << pfn->getResult() << " " << vrule << " "
        << " / " << pfn->getArguments() << std::endl;
    out << "(anchor :step " << prefix << "t" << step_id;

    // Append index of anchor to prefix so that all steps in the subproof use it
    prefix.append("t" + std::to_string(step_id) + ".");
    step_id++;

    // If the subproof is a bind the arguments need to be printed as
    // assignments, i.e. args=[(= v0 v1)] is printed as (:= (v0 Int) v1).
    if (vrule == AletheRule::ANCHOR_BIND)
    {
      out << " :args (";
      for (unsigned long int j = 3, size = pfn->getArguments().size(); j < size;
           j++)
      {
        out << "(:= (" << pfn->getArguments()[j][0].toString() << " "
            << pfn->getArguments()[j][0].getType().toString() << ") "
            << pfn->getArguments()[j][1].toString() << ")";
        if (j != pfn->getArguments().size() - 1)
        {
          out << " ";
        }
      }
      out << ")";
    }
    // In all other cases there are no arguments
    out << ")\n";

    // If the subproof is a genuine subproof the arguments are printed as
    // assumptions
    if (vrule == AletheRule::ANCHOR_SUBPROOF)
    {
      for (size_t i = 3, size = pfn->getArguments().size(); i < size; i++)
      {
        Trace("alethe-printer")
            << "... print assumption " << pfn->getArguments()[i] << std::endl;
        out << "(assume " << prefix << "a" << std::to_string(i - 3) << " "
            << pfn->getArguments()[i] << ")\n";
        assumptions[nested_level][pfn->getArguments()[i]] = i - 3;
      }
    }

    // Store step_id until children are printed to resume counter at current
    // position
    current_step_id = step_id;
    step_id = 1;
  }

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached.
  if (vrule == AletheRule::ASSUME)
  {
    Trace("alethe-printer")
        << "... reached assumption " << pfn->getResult() << " " << vrule << " "
        << " / " << pfn->getArguments() << std::endl;

    // While in most cases the assumption is printed at the same level than the
    // step whose premise it is, it is possible that it is from a different
    // level. Thus, the whole list needs to be traversed. Since this case is rare
    // adapting the prefix should be rarely necessary.
    for (size_t i = nested_level; i >= 0; i--)
    {
      auto it = assumptions[i].find(pfn->getArguments()[2]);
      if (it != assumptions[i].end())
      {
        std::string new_prefix = prefix;
        // get substring of prefix
        for (size_t j = 0; j < nested_level - i; j++)
        {
          new_prefix = new_prefix.substr(0, new_prefix.find_last_of("."));
          new_prefix = new_prefix.substr(0, new_prefix.find_last_of(".") + 1);
        }
        Trace("alethe-printer")
            << "... search assumption in list on level " << i << ": "
            << pfn->getArguments()[2] << "/" << assumptions[i] << "     "
            << new_prefix << std::endl;
        return new_prefix + "a" + std::to_string(it->second);
      }
    }

    Trace("alethe-printer") << "... printing failed! Encountered assumption "
                               "that has not been printed! "
                            << pfn->getArguments()[2] << "/"
                            << assumptions[nested_level] << std::endl;
    return "";
  }

  // Print children
  std::vector<std::string> child_prefixes;
  for (const std::shared_ptr<ProofNode> child : pfn->getChildren())
  {
    child_prefixes.push_back(alethePrinterInternal(out, child));
  }

  // If the rule is a subproof a final subproof step needs to be printed
  if (vrule == AletheRule::ANCHOR_SUBPROOF || vrule == AletheRule::ANCHOR_BIND)
  {
    Trace("alethe-printer")
        << "... print node " << pfn->getResult() << " " << vrule << " / "
        << pfn->getArguments() << std::endl;

    prefix.pop_back();  // Remove last .
    // print subproof or bind
    out << "(step " << prefix << " " << pfn->getArguments()[2] << " :rule "
        << vrule;

    // Discharge assumptions in the case of subproof
    if (vrule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << " :discharge (";
      for (unsigned long int j = 0; j < assumptions[nested_level].size(); j++)
      {
        out << prefix << ".a" + std::to_string(j);
        if (j != assumptions[nested_level].size() - 1)
        {
          out << " ";
        }
      }
      out << ")";
    }
    out << ")\n";

    // Set counters back to their old value before subproof was entered
    nested_level--;
    assumptions.pop_back();
    steps.pop_back();
    step_id = current_step_id;
    std::string current_t = prefix;
    prefix = prefix.substr(0, prefix.find_last_of("t"));
    return current_t;
  }

  // If the current step is already printed return its id
  auto it = steps[nested_level].find(pfn->getArguments()[2]);

  if (it != steps[nested_level].end())
  {
    Trace("alethe-printer")
        << "... step is already printed " << pfn->getResult() << " " << vrule
        << " / " << pfn->getArguments() << std::endl;
    return prefix + "t" + std::to_string(it->second);
  }

  // Print current step
  Trace("alethe-printer") << "... print node " << pfn->getResult() << " "
                          << vrule << " / " << pfn->getArguments() << std::endl;
  std::string current_t;
  current_t = "t" + std::to_string(step_id);
  steps[nested_level][pfn->getArguments()[2]] = step_id;
  out << "(step " << prefix << current_t << " ";
  out << pfn->getArguments()[2].toString() << " :rule " << vrule;
  if (pfn->getArguments().size() > 3)
  {
    out << " :args (";
    for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
         i++)
    {
      if (vrule == AletheRule::FORALL_INST)
      {
        out << "(:= " << pfn->getArguments()[i][0].toString() << " "
            << pfn->getArguments()[i][1].toString() << ")";
      }
      else
      {
        out << pfn->getArguments()[i].toString();
      }
      if (i != pfn->getArguments().size() - 1)
      {
        out << " ";
      }
    }
    out << ")";
  }
  if (pfn->getChildren().size() >= 1)
  {
    out << " :premises (";
    for (unsigned long int i = 0, size = child_prefixes.size(); i < size; i++)
    {
      out << child_prefixes[i];
      if (i != child_prefixes.size() - 1)
      {
        out << " ";
      }
    }
    out << "))\n";
  }
  else
  {
    out << ")\n";
  }
  ++step_id;
  return prefix + current_t;
}

}  // namespace proof

}  // namespace cvc5
