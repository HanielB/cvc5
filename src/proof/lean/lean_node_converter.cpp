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
    {kind::DISTINCT, "Ne"},
    {kind::XOR, "xor"},
    {kind::IMPLIES, "->"},
    {kind::EXISTS, "exists"},
    {kind::FORALL, "forall"},
    {kind::LAMBDA, "fun"},
    {kind::WITNESS, "epsilon"},
    {kind::LT, "LT.lt"},
    {kind::LEQ, "LE.le"},
    {kind::GT, "GT.gt"},
    {kind::GEQ, "GE.ge"},
    {kind::ADD, "HAdd.hAdd"},
    {kind::SUB, "HSub.hSub"},
    {kind::MULT, "HMul.hMul"},
    {kind::NONLINEAR_MULT, "HMul.hMul"},
    {kind::DIVISION, "HDiv.hDiv"},
    {kind::DIVISION_TOTAL, "HDiv.hDiv"},
    {kind::INTS_DIVISION, "HDiv.hDiv"},
    {kind::INTS_DIVISION_TOTAL, "HDiv.hDiv"},
    {kind::INTS_MODULUS, "HMod.hMod"},
    {kind::INTS_MODULUS_TOTAL, "HMod.hMod"},
};

// have underlying node converter *not* force type preservation
LeanNodeConverter::LeanNodeConverter()
{
  NodeManager* nm = NodeManager::currentNM();
  d_brack[0] = nm->mkRawSymbol("[", nm->sExprType());
  d_brack[1] = nm->mkRawSymbol("]", nm->sExprType());
  d_comma = nm->mkRawSymbol(",", nm->sExprType());
  d_colon = nm->mkRawSymbol(":", nm->sExprType());
  d_Arrow = nm->mkRawSymbol("=>", nm->sExprType());
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
      indices.push_back(mkInt(n.getConst<BitVectorBitOf>().d_bitIndex));
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
  // don't convert bound variable list directly, it'll be converted as part of
  // the binder
  if (k == kind::BOUND_VAR_LIST)
  {
    return false;
  }
  return true;
}

Node LeanNodeConverter::mkBinArithApp(
    Kind k, Node c0, Node c1, TypeNode retType, bool intConstArgs)
{
  // requires special case when the first element is an integer
  // constant... due to particularities of Lean the coercion algorithm
  // (between Nat and Int) is less powerful with (op n (+ x y)), when n
  // is a non-negative integer and x or y is an integer term, which well
  // make n a nat and not try coercing it to int. But (binrel% op n (+ x
  // y)) will do the coercion.
  NodeManager* nm = NodeManager::currentNM();
  if (intConstArgs)
  {
    TypeNode tn = c0.getType();
    c0 = nm->mkNode(kind::APPLY_UF,
                    mkInternalSymbol("Int.ofNat", nm->mkFunctionType(tn, tn)),
                    c0);
  }
  // (binrel% op c0 c1) vs (op 0 c1)
  return nm->mkNode(
      kind::APPLY_UF,
      {mkInternalSymbol(
           "binrel%",
           nm->mkFunctionType({nm->sExprType(), c0.getType(), c1.getType()},
                              retType)),
       mkInternalSymbol(s_kindToString[k]),
       c0,
       c1});
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
    Kind k = cur.getKind();
    if (it == d_cache.end())
    {
      Trace("lean-conv") << "pre visit " << cur << "\n";
      if (!shouldTraverse(cur))
      {
        Trace("lean-conv") << ".. do not traverse\n";
        d_cache[cur] = cur;
        continue;
      }
      d_cache[cur] = Node::null();
      visit.push_back(cur);
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Trace("lean-conv") << "post visit " << cur << "\n";
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
        Trace("lean-conv") << "..retrieve converted child " << cn << "\n";
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
          // skolems v print as their original forms
          // v is (skolem W) where W is the original or original form of v
          Node wi = SkolemManager::getUnpurifiedForm(cur);
          if (!wi.isNull() && wi != cur)
          {
            Trace("lean-conv")
                << "...to convert original form " << wi << std::endl;
            res = convert(wi);
            break;
          }
          // might be a skolem function. For now we only handle the function for
          // skolemization of strong quantifiers.
          SkolemManager* sm = nm->getSkolemManager();
          SkolemFunId sfi = SkolemFunId::NONE;
          Node cacheVal;
          if (!sm->isSkolemFunction(cur, sfi, cacheVal))
          {
            Unreachable() << "Fresh Skolems are not allowed\n";
          }
          // create the witness term (witness ((x_i T_i)) (exists ((x_i+1 T_i+1)
          // ... (x_n T_n)) body), where the bound variables and the body come
          // from the quantifier term which must be the first element of
          // cacheVal (which should be a list), and i the second.
          if (sfi == SkolemFunId::QUANTIFIERS_SKOLEMIZE)
          {
            Trace("lean-conv")
                << ".. to build witness with index/quant: " << cacheVal[1]
                << " / " << cacheVal[0] << "\n";
            Assert(cacheVal.getKind() == kind::SEXPR
                   && cacheVal.getNumChildren() == 2);
            Node quant = cacheVal[0];
            Assert(quant.getKind() == kind::EXISTS);
            uint32_t index;
            if (ProofRuleChecker::getUInt32(cacheVal[1], index))
            {
              Assert(index < quant[0].getNumChildren());
              Node body =
                  index == quant[0].getNumChildren() - 1
                      ? quant[1]
                      : nm->mkNode(kind::EXISTS,
                                   nm->mkNode(kind::BOUND_VAR_LIST,
                                              std::vector<Node>{
                                                  quant[0].begin() + index + 1,
                                                  quant[0].end()}),
                                   quant[1]);
              // we need to replace in the body all the free variables (i.e.,
              // from 0 to index) by their respective choice terms. To do this,
              // we get the skolems for each of these variables, retrieve their
              // conversions, and replace the variables by the conversions in
              // body
              if (index > 0)
              {
                std::vector<Node> subs;
                for (size_t i = 0; i < index; ++i)
                {
                  Node sk = sm->getSkolemForBVar(quant[0][i]);
                  Assert(!sk.isNull());
                  subs.push_back(convert(sk));
                }
                body = body.substitute(quant[0].begin(),
                                       quant[0].begin() + index,
                                       subs.begin(),
                                       subs.end());
              }
              Node witness =
                  nm->mkNode(kind::WITNESS,
                             nm->mkNode(kind::BOUND_VAR_LIST, quant[0][index]),
                             body);
              Trace("lean-conv") << ".. witness " << witness << "\n";
              res = convert(witness);
              break;
            }
          }
          Unreachable() << "Skolems function " << sfi << " conversion failed\n";
        }
        case kind::PI:
        {
          res = mkInternalSymbol("Real.pi", cur.getType());
          break;
        }
        case kind::SQRT:
        {
          Node op = mkInternalSymbol(
              "Real.sqrt",
              nm->mkFunctionType(children[0].getType(), cur.getType()));
          res = nm->mkNode(kind::APPLY_UF, op, children[0]);
          break;
        }
        case kind::VARIABLE:
        {
          res = nm->mkRawSymbol(cur.getName(), cur.getType());
          break;
        }
        case kind::BOUND_VARIABLE:
        {
          res = cur;
          break;
        }
        case kind::CONST_BOOLEAN:
        {
          res = cur.getConst<bool>()
                    ? mkInternalSymbol("True", nm->booleanType())
                    : mkInternalSymbol("False", nm->booleanType());
          break;
        }
        case kind::CONST_RATIONAL:
        {
          TypeNode tn = cur.getType();
          Rational r = cur.getConst<Rational>();
          Integer i = r.getNumerator();
          bool negative = i.strictlyNegative();
          bool fraction = !r.getDenominator().isOne();
          Node toConvert;
          std::stringstream ss;
          if (!fraction)
          {
            ss << "__LEAN_TMP" << i.abs();
            toConvert = mkInternalSymbol(ss.str(), tn);
          }
          else
          {
            toConvert = nm->mkNode(kind::DIVISION,
                                   nm->mkConstInt(i.abs()),
                                   nm->mkConstInt(r.getDenominator()));
          }
          toConvert = negative ? nm->mkNode(kind::NEG, toConvert) : toConvert;
          res = (fraction || negative) ? convert(toConvert) : toConvert;
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
        // casts
        case kind::TO_REAL:
        {
          // If argument is int, cast, otherwise, remove
          TypeNode tn = cur[0].getType();
          if (!tn.isInteger())
          {
            res = children[0];
            break;
          }
          res = nm->mkNode(
              kind::APPLY_UF,
              mkInternalSymbol("Rat.ofInt",
                               nm->mkFunctionType(tn, cur.getType())),
              children[0]);
          break;
        }
        // binary arith operators
        case kind::GEQ:
        case kind::GT:
        case kind::LEQ:
        case kind::LT:
        case kind::SUB:
        case kind::DIVISION:
        case kind::DIVISION_TOTAL:
        case kind::INTS_DIVISION:
        case kind::INTS_DIVISION_TOTAL:
        case kind::INTS_MODULUS:
        case kind::INTS_MODULUS_TOTAL:
        {
          TypeNode tn = cur[0].getType();
          res = mkBinArithApp(k,
                              children[0],
                              children[1],
                              cur.getType(),
                              cur[0].isConst() && cur[1].isConst()
                                  && (tn.isInteger()
                                      || (tn.isReal()
                                          && cur[0]
                                                 .getConst<Rational>()
                                                 .getDenominator()
                                                 .isOne()))
                                  && cur[0].getConst<Rational>().sgn() >= 0);
          break;
        }
        // n-ary arith kinds
        case kind::ADD:
        case kind::MULT:
        case kind::NONLINEAR_MULT:
        {
          TypeNode retType = cur.getType();
          size_t i = 1, size = cur.getNumChildren();
          Node newCur = children[size - 1];
          do
          {
            TypeNode tn = cur[size - 1 - i].getType();
            bool instConstArgs =
                cur[size - 1 - i].isConst() && newCur.isConst()
                && (tn.isInteger()
                    || (tn.isReal()
                        && cur[size - 1 - i]
                               .getConst<Rational>()
                               .getDenominator()
                               .isOne()))
                && cur[size - 1 - i].getConst<Rational>().sgn() >= 0;
            newCur = mkBinArithApp(
                k, children[size - 1 - i], newCur, retType, instConstArgs);
          } while (++i < size);
          res = newCur;
          break;
        }
        case kind::NEG:
        {
          Node op = mkInternalSymbol(
              "Neg.neg",
              nm->mkFunctionType(children[0].getType(), cur.getType()));
          res = nm->mkNode(kind::APPLY_UF, op, children[0]);
          break;
        }
        case kind::LAMBDA:
        {
          // Must be stratified s.t. (lambda ((x1 T1) ... (xn Tn)) F) becomes
          // (fun x1 : T1 => (fun x2 : T2 => ... => (fun xn : Tn => F) ...))
          TypeNode bodyType = cur[1].getType();
          TypeNode fType = nm->mkFunctionType(
              {nm->sExprType(), nm->sExprType(), bodyType}, bodyType);
          Node op = mkInternalSymbol("fun", fType);
          // get the converted body as the starting point
          Node vars = children[0];
          Node currBody = children[1];
          for (size_t size = vars.getNumChildren(), i = size; i > 0; --i)
          {
            currBody =
                nm->mkNode(kind::APPLY_UF,
                           {op,
                            nm->mkNode(kind::SEXPR,
                                       vars[i - 1],
                                       d_colon,
                                       typeAsNode(vars[i - 1].getType())),
                            d_Arrow,
                            currBody});
          }
          res = currBody;
          break;
        }
        case kind::WITNESS:
        {
          Assert(cur[0].getNumChildren() == 1);
          TypeNode bodyType = children[1].getType();
          Node op = mkInternalSymbol(
              "epsilon", nm->mkFunctionType(nm->sExprType(), cur.getType()));
          Node funDecl = nm->mkNode(
              kind::SEXPR, cur[0][0], d_colon, typeAsNode(cur[0][0].getType()));
          TypeNode fType = nm->mkFunctionType(
              {nm->sExprType(), nm->sExprType(), bodyType}, nm->sExprType());
          res = nm->mkNode(kind::APPLY_UF,
                           op,
                           nm->mkNode(kind::APPLY_UF,
                                      {mkInternalSymbol("fun", fType),
                                       funDecl,
                                       d_Arrow,
                                       children[1]}));
          break;
        }
        case kind::EXISTS:
        case kind::FORALL:
        {
          // we must make it to be printed with the respective kind name, so we
          // create an operator with that name and the correct type and do a
          // function application.
          //
          // Moreover, each variable must itself be converted, because the
          // expected syntax is "forall/exists (v1 : T1) ... (vn : Tn), F"
          std::vector<Node> newChildren;
          std::vector<TypeNode> childrenTypes;
          for (const Node& v : cur[0])
          {
            childrenTypes.push_back(nm->sExprType());
            newChildren.push_back(
                nm->mkNode(kind::SEXPR, v, d_colon, typeAsNode(v.getType())));
          }
          childrenTypes.push_back(nm->sExprType());
          newChildren.push_back(d_comma);

          childrenTypes.push_back(children[1].getType());
          newChildren.push_back(children[1]);
          TypeNode fType = nm->mkFunctionType(childrenTypes, cur.getType());
          Node op = mkInternalSymbol(s_kindToString[k], fType);
          newChildren.insert(newChildren.begin(), op);
          res = nm->mkNode(kind::APPLY_UF, newChildren);
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
          // requires special case for equality when the first element is an
          // integer constant... due to particularities of Lean the coercion
          // algorithm (between Nat and Int) is less powerful with (Eq n (+ x
          // y)), when n is a non-negative integer and x or y is an integer
          // term, which will make n a nat and not try coercing it to int. But
          // (binrel% Eq n (+ x y)) will do the coercion.
        case kind::EQUAL:
        case kind::DISTINCT:
        {
          // TODO: introduce casts when equality between int/real

          TypeNode childrenType = cur[0].getType();
          TypeNode fType;
          Node op;
          // when both children are non-negative integer values v, we change
          // first one to "(Int.ofNat v)". This avoids that Lean infers the
          // equality being between natural numbers.
          //
          // Note that rational constants that are integral need to pass the
          // test as well
          if (cur[0].isConst() && cur[1].isConst()
              && (childrenType.isInteger()
                  || (childrenType.isReal()
                      && cur[0].getConst<Rational>().getDenominator().isOne()))
              && cur[0].getConst<Rational>().sgn() >= 0)
          {
            children[0] =
                nm->mkNode(kind::APPLY_UF,
                           mkInternalSymbol(
                               "Int.ofNat",
                               nm->mkFunctionType(childrenType, childrenType)),
                           children[0]);
          }
          if (childrenType.isInteger() && children[0].isConst())
          {
            fType = nm->mkFunctionType(
                {nm->sExprType(), childrenType, childrenType},
                nm->booleanType());
            children.insert(children.begin(),
                            mkInternalSymbol(s_kindToString[k]));
            op = mkInternalSymbol("binrel%", fType);
          }
          else
          {
            fType = nm->mkFunctionType({childrenType, childrenType},
                                       nm->booleanType());
            op = mkInternalSymbol(s_kindToString[k], fType);
          }
          children.insert(children.begin(), op);
          res = nm->mkNode(kind::APPLY_UF, children);
          break;
        }
        case kind::IMPLIES:
        {
          TypeNode binBoolOpType = nm->mkFunctionType(
              {nm->booleanType(), nm->booleanType()}, nm->booleanType());
          Node op = mkInternalSymbol("Implies", binBoolOpType);
          res = nm->mkNode(kind::APPLY_UF, op, children[0], children[1]);
          break;
        }
        case kind::BITVECTOR_CONCAT:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_ADD:
        case kind::BITVECTOR_SUB:
        case kind::BITVECTOR_ULT:
        case kind::BITVECTOR_ULE:
        case kind::SELECT:
        case kind::XOR:
        {
          Unreachable() << "Kind " << k << " is not supported\n";
          resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
          resChildren.push_back(children[0]);
          resChildren.push_back(children[1]);
          res = nm->mkNode(kind::SEXPR, resChildren);
          break;
        }
        // unary
        case kind::NOT:
        {
          TypeNode fType =
              nm->mkFunctionType(nm->booleanType(), nm->booleanType());
          Node op = mkInternalSymbol(s_kindToString[k], fType);
          res = nm->mkNode(kind::APPLY_UF, {op, children[0]});
          break;
        }
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
        {
          TypeNode retType = cur[1].getType();
          TypeNode fType = nm->mkFunctionType(
              {nm->booleanType(), retType, retType}, retType);
          Node op = mkInternalSymbol(s_kindToString[k], fType);
          children.insert(children.begin(), op);
          res = nm->mkNode(kind::APPLY_UF, children);
          break;
        }
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
          TypeNode fType = nm->mkFunctionType(
              {nm->booleanType(), nm->booleanType()}, nm->booleanType());
          Node op = mkInternalSymbol(k == kind::OR ? "Or" : "And", fType);
          Node newCur = children.back();
          for (size_t i = nChildren - 1; i > 0; --i)
          {
            newCur = nm->mkNode(kind::APPLY_UF, op, children[i - 1], newCur);
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
          if (k == kind::APPLY_UF)
          {
            TypeNode ftn = cur.getOperator().getType();
            Assert(ftn == children[0].getType())
                << "Diff op types " << ftn << " / " << children[0].getType();
            std::vector<TypeNode> argTypes = ftn.getArgTypes();
            for (size_t i = 0, size = argTypes.size(); i < size; ++i)
            {
              Assert(argTypes[i] == children[i + 1].getType())
                  << "i : " << i << ", argType: " << argTypes[i]
                  << ", child type: " << children[i + 1].getType();
            }
          }
          res = childChanged ? nm->mkNode(k, children) : Node(cur);
        }
      }
      Trace("lean-conv") << "..result is " << res << "\n";
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
    case kind::DISTINCT:
    {
      return mkInternalSymbol("Ne");
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
      return mkInternalSymbol("ite");
    }
    case kind::ADD:
    {
      return mkInternalSymbol("HAdd.hAdd");
    }
    case kind::SUB:
    {
      return mkInternalSymbol("HSub.hSub");
    }
    case kind::NONLINEAR_MULT:
    case kind::MULT:
    {
      return mkInternalSymbol("HMul.hMul");
    }
    case kind::INTS_MODULUS:
    case kind::INTS_MODULUS_TOTAL:
    {
      return mkInternalSymbol("HMod.hMod");
    }
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_DIVISION:
    case kind::DIVISION_TOTAL:
    case kind::DIVISION:
    {
      return mkInternalSymbol("HDiv.hDiv");
    }
    case kind::GEQ:
    {
      return mkInternalSymbol("GE.ge");
    }
    case kind::GT:
    {
      return mkInternalSymbol("GT.gt");
    }
    case kind::LEQ:
    {
      return mkInternalSymbol("LE.le");
    }
    case kind::LT:
    {
      return mkInternalSymbol("LT.lt");
    }
    case kind::EXPONENTIAL:
    {
      return mkInternalSymbol("Real.exp");
    }
    case kind::SINE:
    {
      return mkInternalSymbol("Real.sin");
    }
    case kind::COSINE:
    {
      return mkInternalSymbol("Real.cos");
    }
    case kind::TANGENT:
    {
      return mkInternalSymbol("Real.tan");
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
      Trace("lean-conv") << "non-handled kind " << k << "\n";
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
  else if (tn.isReal())
  {
    res = mkInternalSymbol("Rat");
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
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
}

Node LeanNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
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
  return mkInternalSymbol(ss.str(), n.getType());
}

}  // namespace proof
}  // namespace cvc5::internal
