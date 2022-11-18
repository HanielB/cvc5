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
 * Lean node conversion utility
 */
#include "proof/lean/lean_node_converter.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "util/bitvector.h"
#include "util/string.h"

namespace cvc5::internal {
namespace proof {

std::unordered_map<Kind, std::string> s_kindToString = {
    {kind::BITVECTOR_CONCAT, "bvConcat"},
    {kind::BITVECTOR_AND, "bvAnd"},
    {kind::BITVECTOR_ADD, "bvAdd"},
    {kind::BITVECTOR_SUB, "bvSub"},
    {kind::BITVECTOR_NEG, "bvNeg"},
    {kind::BITVECTOR_ULT, "bvUlt"},
    {kind::BITVECTOR_ULE, "bvUle"},
    {kind::BITVECTOR_EXTRACT, "bvExtract"},
    {kind::BITVECTOR_REPEAT, "bvRepeat"},
    {kind::BITVECTOR_ZERO_EXTEND, "bvZeroExt"},
    {kind::BITVECTOR_SIGN_EXTEND, "bvSignExt"},
    {kind::BITVECTOR_BITOF, "bitOf"},
    {kind::BITVECTOR_BB_TERM, "bbT"},
    {kind::ITE, "ite"},
    {kind::SELECT, "select"},
    {kind::STORE, "store"},
    {kind::NOT, "Not"},
    {kind::STRING_LENGTH, "mkLength"},
    {kind::EQUAL, "Eq"},
    {kind::XOR, "xor"},
    {kind::IMPLIES, "->"},
    {kind::DISTINCT, "distinct"},
    {kind::FORALL, "forall"},
    {kind::LAMBDA, "fun"},
    {kind::WITNESS, "choice"},
};

// have underlying node converter *not* force type preservation
LeanNodeConverter::LeanNodeConverter()
{
  d_brack[0] = mkInternalSymbol("__LEAN_TMP[");
  d_brack[1] = mkInternalSymbol("__LEAN_TMP]");
  d_comma = mkInternalSymbol("__LEAN_TMP,");
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}
LeanNodeConverter::~LeanNodeConverter() {}

Node LeanNodeConverter::mkList(const std::vector<Node>& nodes,
                               const std::vector<Node>& prefix)
{
  std::vector<Node> listNodes{prefix};
  listNodes.push_back(d_brack[0]);
  for (size_t i = 0, size = nodes.size(); i < size; ++i)
  {
    listNodes.push_back(nodes[i]);
    if (i < size - 1)
    {
      listNodes.push_back(d_comma);
    }
  }
  listNodes.push_back(d_brack[1]);
  return NodeManager::currentNM()->mkNode(kind::SEXPR, listNodes);
}

Node LeanNodeConverter::mkInt(unsigned i)
{
  return mkInternalSymbol(NodeManager::currentNM()->mkConstInt(Rational(i)));
}

std::vector<Node> LeanNodeConverter::getOperatorIndices(Kind k, Node n)
{
  std::vector<Node> indices;
  switch (k)
  {
    case kind::BITVECTOR_EXTRACT:
    {
      BitVectorExtract p = n.getConst<BitVectorExtract>();
      indices.push_back(mkInt(p.d_high));
      indices.push_back(mkInt(p.d_low));
      break;
    }
    case kind::BITVECTOR_REPEAT:
    {
      indices.push_back(mkInt(n.getConst<BitVectorRepeat>().d_repeatAmount));
      break;
    }
    case kind::BITVECTOR_ZERO_EXTEND:
    {
      indices.push_back(
          mkInt(n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount));
      break;
    }
    case kind::BITVECTOR_SIGN_EXTEND:
    {
      indices.push_back(
          mkInt(n.getConst<BitVectorSignExtend>().d_signExtendAmount));
      break;
    }
    case kind::BITVECTOR_BITOF:
    {
      indices.push_back(
          mkInt(n.getConst<BitVectorBitOf>().d_bitIndex));
      break;
    }
      // case kind::BITVECTOR_ROTATE_LEFT:
      //   indices.push_back(nm->mkConst(
      //       Rational(n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount)));
      //   break;
      // case kind::BITVECTOR_ROTATE_RIGHT:
      //   indices.push_back(nm->mkConst(
      //       Rational(n.getConst<BitVectorRotateRight>().d_rotateRightAmount)));
      //   break;

    default: Unreachable(); break;
  }
  return indices;
}

bool LeanNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert bound variable list directly
  if (k == kind::BOUND_VAR_LIST)
  {
    return false;
  }
  return true;
}

Node LeanNodeConverter::convert(Node n)
{
  Trace("lean-conv") << "LeanConverter::convert: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_cache.find(cur);
    Trace("lean-conv2") << "convert " << cur << std::endl;
    Kind k = cur.getKind();
    if (it == d_cache.end())
    {
      if (!shouldTraverse(cur))
      {
        d_cache[cur] = cur;
        continue;
      }
      d_cache[cur] = Node::null();
      visit.push_back(cur);
      if (k == kind::SKOLEM || k == kind::BOOLEAN_TERM_VARIABLE)
      {
        Trace("lean-conv") << "LeanConverter: handling skolem " << cur << "\n";
        Node wi = SkolemManager::getWitnessForm(cur);
        // true skolem with witness form, just convert that
        if (!wi.isNull())
        {
          Trace("lean-conv") << "LeanNodeConverter::postConvert: skolem " << cur
                             << " has witness form " << wi << "\n";
          visit.push_back(wi);
        }
        else
        {
          // purification skolem, thus we need to build the fake choice term
          AlwaysAssert(!SkolemManager::getOriginalForm(cur).isNull());
          visit.push_back(SkolemManager::getOriginalForm(cur));
        }
        continue;
      }
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      // collect children
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        it = d_cache.find(cur.getOperator());
        AlwaysAssert(it != d_cache.end());
        AlwaysAssert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = d_cache.find(cn);
        AlwaysAssert(it != d_cache.end());
        AlwaysAssert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      // Now convert
      Node res;
      size_t nChildren = cur.getNumChildren();
      std::vector<Node> resChildren;
      Trace("lean-conv") << "LeanConverter: handling " << k << ", " << cur
                         << "\n";
      switch (k)
      {
        case kind::SKOLEM:
        case kind::BOOLEAN_TERM_VARIABLE:
        {
          Trace("lean-conv")
              << "LeanConverter: handling skolem " << cur << "\n";
          Node wi = SkolemManager::getWitnessForm(cur);
          // true skolem with witness form, just convert that
          if (!wi.isNull())
          {
            Trace("lean-conv") << "LeanNodeConverter::postConvert: skolem " << n
                               << " has witness form " << wi << "\n";
            res = d_cache[wi];
          }
          else
          {
            // purification skolem, thus we retrieve the conversion of its
            // original form
            res = d_cache[SkolemManager::getOriginalForm(cur)];
          }
          AlwaysAssert(!res.isNull());
          break;
        }
        case kind::BOUND_VARIABLE:
        {
          // don't convert internally generated
          if (d_symbols.find(cur) == d_symbols.end())
          {
            // variables are (const id type)
            resChildren.push_back(mkInternalSymbol("const"));
            resChildren.push_back(
                nm->mkConstInt(Rational(static_cast<int>(cur.getId()))));
            resChildren.push_back(typeAsNode(cur.getType()));
            res = nm->mkNode(kind::SEXPR, resChildren);
          }
          else
          {
            res = cur;
          }
          break;
        }
        case kind::CONST_BOOLEAN:
        {
          res = cur.getConst<bool>() ? mkInternalSymbol("True")
                                     : mkInternalSymbol("False");
          break;
        }
        case kind::CONST_RATIONAL:
        {
          TypeNode tn = cur.getType();
          AlwaysAssert(tn.isInteger()) << "Only support integer rationals\n";
          res = cur;
          break;
        }
        case kind::CONST_BITVECTOR:
        {
          resChildren.push_back(mkInternalSymbol("val"));
          // create list of booleans with bits, by checking if each bit is set
          // and putting top or bottom into the list
          BitVector bv = cur.getConst<BitVector>();

          std::vector<Node> bits;
          for (size_t i = 0, size = bv.getSize(); i < size; ++i)
          {
            bits.push_back(bv.isBitSet(i) ? d_true : d_false);
          }
          resChildren.push_back(nm->mkNode(
              kind::SEXPR, mkInternalSymbol("value.bitvec"), mkList(bits)));
          resChildren.push_back(typeAsNode(cur.getType()));
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        case kind::FORALL:
        case kind::LAMBDA:
        case kind::WITNESS:
        {
          AlwaysAssert(nChildren == 2);
          Node binderOp = mkInternalSymbol(s_kindToString[k]);
          size_t nVars = children[0].getNumChildren();
          // iterate over variables, from last to second, and build layered
          // binding
          Node curChild = children[1];
          Node convertedVar;
          for (size_t i = 0; i < nVars; ++i)
          {
            curChild = nm->mkNode(kind::SEXPR,
                                  binderOp,
                                  nm->mkConstInt(Rational(static_cast<int>(
                                      children[0][nVars - i - 1].getId()))),
                                  curChild);
          }
          res = curChild;
          break;
        }
        // "indexed"
        case kind::BITVECTOR_BB_TERM:
        {
          res = mkList(children, {mkInternalSymbol("mkBbT")});
          break;
        }
        case kind::BITVECTOR_EXTRACT:
        case kind::BITVECTOR_REPEAT:
        case kind::BITVECTOR_ZERO_EXTEND:
        case kind::BITVECTOR_SIGN_EXTEND:
        case kind::BITVECTOR_BITOF:
        {
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          std::vector<Node> indices = getOperatorIndices(k, children[0]);
          // when getting the children jump the operator
          resChildren.insert(
              resChildren.end(), children.begin() + 1, children.end());
          resChildren.insert(resChildren.end(), indices.begin(), indices.end());
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // requires special case for equality between Props (the Booleans here),
        // which must be represented as Iff
        case kind::EQUAL:
        {
          // resChildren.push_back(mkInternalSymbol(
          //     cur[0].getType().isBoolean() ? "Iff" : s_kindToString[k]));
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[0]);
          resChildren.push_back(children[1]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // binary operators
        case kind::XOR:
        {
          Unreachable() << "xor is not supported\n";
        }
        case kind::IMPLIES:
        {
          resChildren.push_back(children[0]);
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[1]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        case kind::BITVECTOR_CONCAT:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_ADD:
        case kind::BITVECTOR_SUB:
        case kind::BITVECTOR_ULT:
        case kind::BITVECTOR_ULE:
        case kind::DISTINCT:
        case kind::SELECT:
        {
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[0]);
          resChildren.push_back(children[1]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // unary
        case kind::NOT:
        case kind::BITVECTOR_NEG:
        case kind::STRING_LENGTH:
        {
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[0]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // ternary
        case kind::ITE:
        case kind::STORE:
        {
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[0]);
          resChildren.push_back(children[1]);
          resChildren.push_back(children[2]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // n-ary ones
        case kind::OR:
        case kind::AND:
        {
          Node newCur = children.back();
          Node connective = mkInternalSymbol(k == kind::OR? "Or" : "And");
          for (size_t i = nChildren - 1; i > 0; --i)
          {
            newCur =
                nm->mkNode(kind::SEXPR, {connective, children[i - 1], newCur});
          }
          res = newCur;
          break;
        }
        // lists
        case kind::SEXPR:
        {
          res = mkList(children);
          break;
        }
        default:
        {
          res = childChanged ? nm->mkNode(k, children) : Node(cur);
        }
      }
      d_cache[cur] = res;
      // force idempotency
      d_cache[res] = res;
    }
  } while (!visit.empty());
  Trace("lean-conv") << "LeanConverter::convert: for " << n << " returns "
                     << d_cache[n] << "\n";
  Assert(d_cache.find(n) != d_cache.end());
  Assert(!d_cache.find(n)->second.isNull());
  return d_cache[n];
}

Node LeanNodeConverter::mkPrintableOp(Node n)
{
  Kind k;
  if (!ProofRuleChecker::getKind(n, k))
  {
    // if not a kind, then it's an arbitrary term and we must convert it here
    return convert(n);
  }
  return mkPrintableOp(k);
}

Node LeanNodeConverter::mkPrintableOp(Kind k)
{
  switch (k)
  {
    case kind::NOT:
    {
      return mkInternalSymbol("Not");
    }
    case kind::EQUAL:
    {
      return mkInternalSymbol("Eq");
    }
    case kind::OR:
    {
      return mkInternalSymbol("Or");
    }
    case kind::AND:
    {
      return mkInternalSymbol("And");
    }
    case kind::XOR:
    {
      Unreachable() << "xor is not supported\n";
      return mkInternalSymbol("xorConst");
    }
    case kind::IMPLIES:
    {
      return mkInternalSymbol("Implies");
    }
    case kind::ITE:
    {
      return mkInternalSymbol("fIteConst");
    }
    case kind::ADD:
    {
      return mkInternalSymbol("plusConst");
    }
    case kind::SUB:
    {
      return mkInternalSymbol("minusConst");
    }
    case kind::SELECT:
    {
      return mkInternalSymbol("selectConst");
    }
    case kind::STORE:
    {
      return mkInternalSymbol("storeConst");
    }
    case kind::BITVECTOR_CONCAT:
    {
      return mkInternalSymbol("bvConcatConst");
    }
    case kind::BITVECTOR_AND:
    {
      return mkInternalSymbol("bvAndConst");
    }
    case kind::BITVECTOR_ADD:
    {
      return mkInternalSymbol("bvAddConst");
    }
    case kind::BITVECTOR_SUB:
    {
      return mkInternalSymbol("bvSubConst");
    }
    case kind::BITVECTOR_NEG:
    {
      return mkInternalSymbol("bvNegConst");
    }
    case kind::BITVECTOR_ULT:
    {
      return mkInternalSymbol("bvUltConst");
    }
    case kind::BITVECTOR_ULE:
    {
      return mkInternalSymbol("bvUleConst");
    }
    case kind::BITVECTOR_EXTRACT:
    {
      return mkInternalSymbol("bvExtConst");
    }
    case kind::BITVECTOR_REPEAT:
    {
      return mkInternalSymbol("bvRepeatConst");
    }
    case kind::BITVECTOR_ZERO_EXTEND:
    {
      return mkInternalSymbol("bvZeroExtConst");
    }
    case kind::BITVECTOR_SIGN_EXTEND:
    {
      return mkInternalSymbol("bvSignExtConst");
    }
    case kind::BITVECTOR_BITOF:
    {
      return mkInternalSymbol("bitOfConst");
    }
    case kind::BITVECTOR_BB_TERM:
    {
      return mkInternalSymbol("bbTConst");
    }
    default:
    {
      Trace("test-lean") << "non-handled kind " << k << "\n";
    }
  }
  return Node::null();
}

Node LeanNodeConverter::typeAsNode(TypeNode tn)
{
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tn);
  if (it != d_typeAsNode.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  // convert
  Node res;
  std::vector<Node> resChildren;
  // functional sort
  if (tn.isFunction())
  {
    // convert each argument
    size_t size = tn.getNumChildren();
    Node arrow = mkInternalSymbol("->");
    for (size_t i = 0; i < size - 1; ++i)
    {
      resChildren.push_back(typeAsNode(tn[i]));
      resChildren.push_back(arrow);
    }
    // return sort
    resChildren.push_back(typeAsNode(tn[size - 1]));
    res = nm->mkNode(kind::SEXPR, resChildren);
  }
  else if (tn.isArray())
  {
    resChildren.push_back(mkInternalSymbol("array"));
    resChildren.push_back(typeAsNode(tn.getArrayIndexType()));
    resChildren.push_back(typeAsNode(tn.getArrayConstituentType()));
    res = nm->mkNode(kind::SEXPR, resChildren);
  }
  else if (tn.isBoolean())
  {
    res = mkInternalSymbol("Prop");
  }
  else if (tn.isInteger())
  {
    res = mkInternalSymbol("Int");
  }
  else if (tn.isBitVector())
  {
    res = nm->mkNode(
        kind::SEXPR,
        mkInternalSymbol("bv"),
        mkInternalSymbol(nm->mkConstInt(Rational(tn.getBitVectorSize()))));
  }
  else
  {
    std::stringstream ss;
    options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
    tn.toStream(ss);
    res = mkInternalSymbol(ss.str());
  }
  d_typeAsNode[tn] = res;
  return res;
}

Node LeanNodeConverter::mkInternalSymbol(const std::string& name)
{
  std::unordered_map<std::string, Node>::iterator it = d_symbolsMap.find(name);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, nm->sExprType());
  d_symbols.insert(sym);
  d_symbolsMap[name] = sym;
  return sym;
}

Node LeanNodeConverter::mkInternalSymbol(TNode n)
{
  std::stringstream ss;
  if (n.getKind() == kind::CONST_RATIONAL)
  {
    ss << "__LEAN_TMP";
  }
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  n.toStream(ss);
  return mkInternalSymbol(ss.str());
}

}  // namespace proof
}  // namespace cvc5
