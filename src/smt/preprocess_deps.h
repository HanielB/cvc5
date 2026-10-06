/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tracking of the input formulas that preprocessed formulas depend on.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PREPROCESS_DEPS_H
#define CVC5__SMT__PREPROCESS_DEPS_H

#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

/**
 * Tracks which input formulas each formula obtained by preprocessing depends
 * on, without producing proofs of preprocessing. It is used in place of
 * PreprocessProofGenerator with --proof-log-no-pp.
 *
 * This class maintains a DAG whose nodes are the formulas notified during
 * preprocessing, as well as auxiliary nodes, e.g., for assignments made by the
 * circuit propagator. Each node stores the nodes it was derived from. A node
 * may also depend on a prefix of the substitutions added to a substitution
 * map, which is how dependencies on substitutions are tracked: applying a
 * substitution map to a formula makes the result depend on all substitutions
 * added to the map until then (as in the proofs of TrustSubstitutionMap).
 *
 * Recording a step takes constant time. The input formulas a node depends on
 * are only computed when requested, and are cached.
 *
 * Dependencies may be over-approximated but not under-approximated. A formula
 * whose premises are not known is assumed to depend on all input formulas.
 *
 * As a proof generator, this class proves a preprocessed formula with a
 * single trusted step whose premises are the input formulas it depends on.
 */
class PreprocessDeps : protected EnvObj, public ProofGenerator
{
 public:
  /** Identifier of a node of the dependency DAG */
  using DepId = uint32_t;
  /** The node that depends on all input formulas */
  static constexpr DepId ALL = 0;

  PreprocessDeps(Env& env);
  ~PreprocessDeps();

  //-------------------------------------------------- formulas
  /** Notify that n is an input formula. */
  void notifyInput(const Node& n);
  /**
   * Notify that n is a new formula derived from premises. This has no effect
   * if n was already notified. No premises means that n is valid, e.g., a
   * definitional lemma.
   */
  void notifyNewAssert(const Node& n, std::vector<DepId>&& premises);
  /**
   * Notify that formula n was rewritten to np. If np is the result of
   * applying a substitution map to n (see notifySubstitutionApply), np also
   * depends on the substitutions of that map at the time. If all is true, np
   * depends on all input formulas. This has no effect if np was already
   * notified.
   */
  void notifyPreprocessed(const Node& n, const Node& np, bool all = false);
  /**
   * Get the node of formula n. If n was not notified, it is registered as
   * depending on all input formulas.
   */
  DepId getId(const Node& n);
  /** Make an auxiliary node with the given premises. */
  DepId mkNode(std::vector<DepId>&& premises);
  /**
   * Make an auxiliary node with the given premises, which also depends on the
   * substitutions added to map m so far.
   */
  DepId mkNode(std::vector<DepId>&& premises, size_t m);

  //-------------------------------------------------- substitution maps
  /** Register a new substitution map, returning its identifier. */
  size_t registerSubstitutionMap();
  /**
   * Set the formula that the substitutions added from now on are derived
   * from, until clearSubstitutionSource is called.
   */
  void setSubstitutionSource(const Node& n);
  /** Same as above, for the node with identifier id. */
  void setSubstitutionSource(DepId id);
  /** Clear the formula set by setSubstitutionSource. */
  void clearSubstitutionSource();
  /**
   * Notify that a substitution was added to map m. It depends on the formula
   * set by setSubstitutionSource, if any. Otherwise it depends on hint, if it
   * is a notified formula, and on all input formulas if not.
   */
  void notifySubstitution(size_t m, const Node& hint = Node::null());
  /**
   * Notify that n substitutions were added to map m, which depend on all
   * input formulas.
   */
  void notifySubstitutionsUnknown(size_t m, size_t n);
  /** Notify that all substitutions of map src were added to map dst. */
  void notifySubstitutionsMerged(size_t dst, size_t src);
  /**
   * Notify that applying the substitutions of map m to a formula resulted in
   * np, which will be notified by notifyPreprocessed. If several applications
   * resulted in np before it is notified, np depends on all of them.
   */
  void notifySubstitutionApply(size_t m, const Node& np);

  //-------------------------------------------------- dependencies
  /** Is n a notified input formula? */
  bool isInput(const Node& n) const;
  /** Get the input formulas that the notified formula n depends on. */
  std::vector<Node> getDependencies(const Node& n);
  /**
   * Get a proof of f, a notified formula that is not an input formula. This
   * is a trusted step with id TrustId::PREPROCESS_DEPS concluding f, whose
   * premises are assumptions of the input formulas that f depends on. Returns
   * nullptr if f is an input formula or was not notified.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;
  /** Is pn a step made by getProofFor? */
  static bool isDepsStep(const ProofNode* pn);

 private:
  /** Sorted identifiers of input nodes, or d_allSet. */
  using DepSet = std::shared_ptr<const std::vector<DepId>>;
  /** A prefix of a substitution map: (map, number of substitutions). */
  using SubsPrefix = std::pair<size_t, size_t>;
  /** A node of the dependency DAG. */
  struct DepNode
  {
    /** The nodes this node was derived from. */
    std::vector<DepId> d_premises;
    /** This node also depends on these prefixes of substitution maps. */
    std::vector<SubsPrefix> d_subs;
    /** Is this node an input formula? */
    bool d_isInput = false;
  };
  /** A substitution map. */
  struct SubsMap
  {
    /** The node each substitution was derived from, in order. */
    std::vector<DepId> d_sources;
    /** Cached dependencies of the prefixes of d_sources that were needed. */
    std::map<size_t, DepSet> d_prefixDeps;
  };
  /** Make a node, returning its identifier. */
  DepId mkNodeInternal(DepNode&& dn);
  /** Register formula n with node dn. */
  DepId registerFormula(const Node& n, DepNode&& dn);
  /** Compute (and cache) the dependencies of node id. */
  DepSet compute(DepId id);
  /** Get the first prefix of map m to cache, among the first size ones. */
  size_t getPrefixStart(const SubsMap& sm, size_t size) const;
  /** Compute the dependencies of node id, whose premises are computed. */
  DepSet combine(DepId id);
  /** Union of dependency sets. */
  DepSet merge(const std::vector<DepSet>& sets);
  /** The nodes of the DAG. */
  std::vector<DepNode> d_nodes;
  /** Cached dependencies of the nodes. */
  std::vector<DepSet> d_deps;
  /** The input formula of each input node, null for other nodes. */
  std::vector<Node> d_inputFormula;
  /** The node of each notified formula. */
  std::unordered_map<Node, DepId> d_formulaIds;
  /** The input nodes, in order. */
  std::vector<DepId> d_inputs;
  /** The substitution maps. */
  std::vector<SubsMap> d_maps;
  /** Pending substitution applications, by their result. */
  std::unordered_map<Node, std::vector<SubsPrefix>> d_subsApply;
  /** The node set by setSubstitutionSource, if any. */
  bool d_hasSubsSource;
  DepId d_subsSource;
  /** The dependency set of ALL. */
  DepSet d_allSet;
  /** The empty dependency set. */
  DepSet d_emptySet;
  /** Number of notified formulas. */
  IntStat d_numFormulas;
  /** Number of formulas that are assumed to depend on all inputs. */
  IntStat d_numUnknown;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
