/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Lean node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN__LEAN_NODE_CONVERTER_H
#define CVC4__PROOF__LEAN__LEAN_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace proof {

class LeanNodeConverter
{
 public:
  LeanNodeConverter();
  ~LeanNodeConverter();
  /** convert to internal */
  Node convert(Node n);

  Node mkPrintableOp(Kind k);

  Node mkPrintableOp(Node n);

  /**
   * Make or get an internal symbol with custom name. This is a BOUND_VARIABLE
   * that has a distinguished status so that it is *not* printed as (bvar ...).
   */
  Node mkInternalSymbol(const std::string& name);
  /** As above but uses the stream of n to make the symbol. */
  Node mkInternalSymbol(TNode n);

  /**
   * Make or get an internal symbol with custom name and type.
   */
  Node mkInternalSymbol(const std::string& name, TypeNode tn);

  /** Type as node */
  Node typeAsNode(TypeNode tn);

  /** The set of declared types */
  // std::unordered_set<TypeNode> d_declTypes;

  Node mkList(const std::vector<Node>& nodes,
              const std::vector<Node>& prefix = {});

  static void cleanIdentifier(std::string& s);
 private:
  /** Should we traverse n? */
  bool shouldTraverse(Node n);

  // Node mkList(const std::vector<Node>& nodes);

  Node mkInt(unsigned i);

  std::vector<Node> getOperatorIndices(Kind k, Node n);

  Node mkBinArithApp(
      Kind k, Node c0, Node c1, TypeNode retType, bool intConstArgs);

  /** Maps from internally generated symbols to the built nodes. */
  std::map<std::pair<TypeNode, std::string>, Node> d_symbolsMap;

  /** Caches for convert */
  std::unordered_map<Node, Node> d_cache;
  std::unordered_map<TypeNode, TypeNode> d_tcache;

  /** Cache for typeAsNode */
  std::map<TypeNode, Node> d_typeAsNode;

  Node d_brack[2];
  Node d_colon;
  Node d_comma;
  Node d_Arrow;
  Node d_true;
  Node d_false;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
