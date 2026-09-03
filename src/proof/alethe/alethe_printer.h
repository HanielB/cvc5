/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H

#include <optional>

#include "proof/alethe/alethe_let_binding.h"
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof_node.h"
#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace proof {

/** A callback for populating a let binder.
 *
 * This callback does not actually update the proof node, but rather just
 * considers the terms in the proof nodes for sharing. This is done in
 * `shouldUpdate`, which is called on every proof node and always returns false.
 */
class LetUpdaterPfCallback : public ProofNodeUpdaterCallback
{
 public:
  LetUpdaterPfCallback(AletheLetBinding& lbind);
  ~LetUpdaterPfCallback();
  void initializeUpdate();
  /** Analyze the given proof node and populate d_lbind with its terms.
   *
   * Always returns false. */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

 protected:
  /** The let binder populated during the update. */
  AletheLetBinding& d_lbind;
};

/**
 * The Alethe printer, which prints proof nodes in an Alethe proof, according to
 * the proof rules defined in alethe_proof_rule.h.
 *
 * It expects to print proof nodes that have been processed by the Alethe proof
 * post-processor.
 */
class AletheProofPrinter : protected EnvObj
{
 public:
  AletheProofPrinter(Env& env,
                     AletheNodeConverter& anc,
                     const AletheStepDepsMap& stepDeps);
  ~AletheProofPrinter() {}
  /**
   * Prints a proof node in the Alethe proof format
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   * @param assertionNames Mapping between assertions and names, if they were
   * given by the user.
   */
  void print(std::ostream& out,
             std::shared_ptr<ProofNode> pfn,
             const std::map<Node, std::string>& assertionNames);

 private:
  /** An element of the printed proof: a step line or an anchor block.
   *
   * The proof is first constructed as a tree of these items and only rendered
   * to text at the end, in final output order. This matters because printing
   * with sharing attaches each shared term's definition to its first printed
   * occurrence: constructing the proof out of output order (subproofs are
   * buffered while steps hoisted out of them go directly to the enclosing
   * frames) requires the conversion of terms to happen at rendering.
   */
  struct OutItem
  {
    /** Whether this is an anchor block (with a subproof) or a plain step */
    bool d_isAnchor = false;
    /** The id of the step (for anchors, of the concluding step) */
    std::string d_id;
    /** The Alethe rule */
    AletheRule d_rule;
    /** The conclusion (an s-expression) */
    Node d_conclusion;
    /** The ids of the premises */
    std::vector<std::string> d_premises;
    /** The remaining arguments */
    std::vector<Node> d_args;
    /** For anchor blocks: the assumption ids and terms of a subproof */
    std::vector<std::pair<std::string, Node>> d_anchorAssumes;
    /** For anchor blocks: the content of the subproof */
    std::vector<OutItem> d_items;
  };

  /** Renders items into out, in order. */
  void renderItems(std::ostream& out, const std::vector<OutItem>& items);

  /** Builds the step item for pfn with the given id, resolving assumption
   * premises relative to frame lvl. */
  OutItem stepItem(const std::shared_ptr<ProofNode>& pfn,
                   const std::string& stepId,
                   size_t lvl);

  /** The id of the assumption of term res, as visible from frame lvl: the
   * innermost subproof at or above lvl assuming it, or a top-level
   * assumption. */
  std::string assumptionId(const Node& res, size_t lvl);

  /** A printing frame: the top level (frame 0) or an open anchor.
   *
   * Each frame carries the id prefix and counter of its level and, for
   * anchors, a buffer holding the text of the anchor and its subproof, which
   * is flushed into the parent frame only when the subproof completes. It also
   * records what the frame makes available --- the variables its anchor
   * declares and the assumptions its subproof introduces --- as well as the
   * step and assumption ids introduced at this level, which become unavailable
   * when the frame is closed.
   */
  struct Frame
  {
    /** The prefix for step ids at this level */
    std::string d_prefix;
    /** The id counter at this level */
    size_t d_id = 0;
    /** The items of this frame, rendered when the whole proof is printed */
    std::vector<OutItem> d_items;
    /** The variables declared by this anchor's arguments */
    std::unordered_set<Node> d_boundVars;
    /** The assumptions introduced by this anchor's subproof */
    std::unordered_set<Node> d_assumptions;
    /** The ids of the assumptions introduced by this anchor's subproof */
    std::unordered_map<Node, std::string> d_assumeIds;
    /** The proof nodes whose step ids were introduced at this level */
    std::vector<ProofNode*> d_introducedSteps;

  };
  /** The chain of open frames the current derivation prints under */
  std::vector<std::unique_ptr<Frame>> d_frames;
  /** The ids of the printed steps whose frame is still open */
  std::unordered_map<ProofNode*, std::string> d_stepIds;
  /** The frame each printed step was placed in, kept alongside d_stepIds. A
   * step's id may only be referenced while its frame is active, i.e., in
   * d_frames (a frame set aside for an anchor printed below its target is
   * open but does not enclose the current position). */
  std::unordered_map<const ProofNode*, Frame*> d_stepFrames;

  /** The level of the active frame holding the printed step of premise. If no
   * active frame holds it (its frame was closed, or is set aside), the
   * premise's derivation is printed again in the current chain first. Only
   * called for non-assumption premises, after their derivations have been
   * printed at least once. */
  size_t premiseLevel(const std::shared_ptr<ProofNode>& premise);

  /** Emits an item at frame lvl: top-level items are rendered to the output
   * right away (items are only appended, so append order is output order and
   * the top level need not be buffered); items of open anchors are buffered
   * in their frame. */
  void emitItem(OutItem&& item, size_t lvl);

  /** Renders one item into out. */
  void renderItem(std::ostream& out, const OutItem& item);
  /** The ids of the printed assumptions whose frame is still open */
  std::unordered_map<Node, std::string> d_assumptionIds;
  /** The stream the top-level frame writes to */
  std::ostream* d_topOut = nullptr;
  /** A proof node whose printing is pinned to the innermost frame. This is
   * used for the direct child of an anchor, which must be printed within the
   * anchor's subproof (a subproof must contain at least one step, its
   * concluding derivation), whereas its own descendants may be printed at
   * outer frames. */
  const ProofNode* d_pinnedToInnermost = nullptr;
  /** The context dependencies of each proof node, computed at translation */
  const AletheStepDepsMap& d_stepDeps;

  /** The outermost frame of the current chain under which the derivation of
   * pfn is well scoped, i.e., all its context dependencies are available. A
   * derivation is printed at that frame, which both avoids replaying shared
   * derivations in every subproof that uses them (their step ids remain
   * available for as long as the frame is open) and can never place a step
   * deeper than the printing traversal reaches it.
   */
  size_t targetFrame(const std::shared_ptr<ProofNode>& pfn);

  /** Prints the derivation of an Alethe proof node at the outermost frame
   * under which it is well scoped (see targetFrame).
   */
  void printInternal(std::shared_ptr<ProofNode> pfn);

  /** Print term into stream
   *
   * The printing is done separately because it uses the let binder (d_lbind)
   * for converting the term before printing.
   *
   * @param out The stream to write to
   * @param n The node to be printed
   */
  void printTerm(std::ostream& out, TNode n);

  /** Print the id for the previously printed step/assumption of the given proof
   * node.
   *
   * @param out The stream to write to
   * @param pfn The proof node
   * @param assumptionsMap Map from assumptions to their ids
   * @param pfMap Map from proof nodes to their ids
   */
  void printStepId(std::ostream& out,
                   std::shared_ptr<ProofNode> pfn,
                   size_t lvl);

  /** Prints the anchor, subproof and concluding step of an anchor proof node
   * into a fresh frame stacked on top of frame lvl, flushing the text into
   * frame lvl when the subproof completes.
   */
  void printAnchor(std::shared_ptr<ProofNode> pfn, size_t lvl);

  /** The let binder for printing with sharing. */
  AletheLetBinding d_lbind;

  /** The Alethe node converter */
  AletheNodeConverter& d_anc;

  /** The callback used for computing the let binding. */
  std::unique_ptr<LetUpdaterPfCallback> d_cb;
};

}  // namespace proof

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H */
