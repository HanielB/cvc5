/*********************                                                        */
/*! \file sygus_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SyGuS output language
 **
 ** The pretty-printer interface for the SyGuS output language.
 **/

#include "printer/sygus/sygus_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/node_manager_attributes.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "printer/dagification_visitor.h"
#include "smt/smt_engine.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/node_visitor.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace printer {
namespace sygus {

static string smtKindString(Kind k, Variant v);

void SygusPrinter::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
  if (dag != 0)
  {
    DagificationVisitor dv(dag);
    NodeVisitor<DagificationVisitor> visitor;
    visitor.run(dv, n);
    const theory::SubstitutionMap& lets = dv.getLets();
    if (!lets.empty())
    {
      theory::SubstitutionMap::const_iterator i = lets.begin();
      theory::SubstitutionMap::const_iterator i_end = lets.end();
      for (; i != i_end; ++i)
      {
        out << "(let ((";
        toStream(out, (*i).second, toDepth, types, TypeNode::null());
        out << ' ';
        toStream(out, (*i).first, toDepth, types, TypeNode::null());
        out << ")) ";
      }
    }
    Node body = dv.getDagifiedBody();
    toStream(out, body, toDepth, types, TypeNode::null());
    if (!lets.empty())
    {
      theory::SubstitutionMap::const_iterator i = lets.begin();
      theory::SubstitutionMap::const_iterator i_end = lets.end();
      for (; i != i_end; ++i)
      {
        out << ")";
      }
    }
  }
  else
  {
    toStream(out, n, toDepth, types, TypeNode::null());
  }
}

static std::string maybeQuoteSymbol(const std::string& s)
{
  // this is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  // symbols
  if (s.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
                          "0123456789~!@$%^&*_-+=<>.?/")
      != string::npos)
  {
    // need to quote it
    stringstream ss;
    ss << '|' << s << '|';
    return ss.str();
  }
  return s;
}

static bool stringifyRegexp(Node n, stringstream& ss)
{
  if (n.getKind() == kind::STRING_TO_REGEXP)
  {
    ss << n[0].getConst<String>().toString(true);
  }
  else if (n.getKind() == kind::REGEXP_CONCAT)
  {
    for (unsigned i = 0; i < n.getNumChildren(); ++i)
    {
      if (!stringifyRegexp(n[i], ss))
      {
        return false;
      }
    }
  }
  else
  {
    return false;
  }
  return true;
}

// force_nt is the type that n must have
void SygusPrinter::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           bool types,
                           TypeNode force_nt) const
{
  // null
  if (n.getKind() == kind::NULL_EXPR)
  {
    out << "null";
    return;
  }

  // constant
  if (n.getMetaKind() == kind::metakind::CONSTANT)
  {
    switch (n.getKind())
    {
      case kind::TYPE_CONSTANT:
        switch (n.getConst<TypeConstant>())
        {
          case BOOLEAN_TYPE: out << "Bool"; break;
          case REAL_TYPE: out << "Real"; break;
          case INTEGER_TYPE: out << "Int"; break;
          case STRING_TYPE: out << "String"; break;
          case ROUNDINGMODE_TYPE: out << "RoundingMode"; break;
          default:
            // fall back on whatever operator<< does on underlying type; we
            // might luck out and be SMT-LIB v2 compliant
            kind::metakind::NodeValueConstPrinter::toStream(out, n);
        }
        break;
      case kind::BITVECTOR_TYPE:
        if (d_variant == sygus_variant)
        {
          out << "(BitVec " << n.getConst<BitVectorSize>().size << ")";
        }
        else
        {
          out << "(_ BitVec " << n.getConst<BitVectorSize>().size << ")";
        }
        break;
      case kind::FLOATINGPOINT_TYPE:
        out << "(_ FloatingPoint " << n.getConst<FloatingPointSize>().exponent()
            << " " << n.getConst<FloatingPointSize>().significand() << ")";
        break;
      case kind::CONST_BITVECTOR:
      {
        const BitVector& bv = n.getConst<BitVector>();
        const Integer& x = bv.getValue();
        unsigned n = bv.getSize();
        if (d_variant == sygus_variant)
        {
          out << "#b" << bv.toString();
        }
        else
        {
          out << "(_ ";
          out << "bv" << x << " " << n;
          out << ")";
        }

        // //out << "#b";

        // while(n-- > 0) {
        //   out << (x.testBit(n) ? '1' : '0');
        // }
        break;
      }
      case kind::CONST_FLOATINGPOINT: out << n.getConst<FloatingPoint>(); break;
      case kind::CONST_ROUNDINGMODE:
        switch (n.getConst<RoundingMode>())
        {
          case roundNearestTiesToEven: out << "roundNearestTiesToEven"; break;
          case roundNearestTiesToAway: out << "roundNearestTiesToAway"; break;
          case roundTowardPositive: out << "roundTowardPositive"; break;
          case roundTowardNegative: out << "roundTowardNegative"; break;
          case roundTowardZero: out << "roundTowardZero"; break;
          default:
            Unreachable("Invalid value of rounding mode constant (%d)",
                        n.getConst<RoundingMode>());
        }
        break;
      case kind::CONST_BOOLEAN:
        // the default would print "1" or "0" for bool, that's not correct
        // for our purposes
        out << (n.getConst<bool>() ? "true" : "false");
        break;
      case kind::BUILTIN:
        out << smtKindString(n.getConst<Kind>(), d_variant);
        break;
      case kind::CHAIN_OP:
        out << smtKindString(n.getConst<Chain>().getOperator(), d_variant);
        break;
      case kind::CONST_RATIONAL:
      {
        const Rational& r = n.getConst<Rational>();
        toStreamRational(
            out, r, !force_nt.isNull() && !force_nt.isInteger(), d_variant);
        break;
      }

      case kind::CONST_STRING:
      {
        // const std::vector<unsigned int>& s = n.getConst<String>().getVec();
        std::string s = n.getConst<String>().toString(true);
        out << '"';
        for (size_t i = 0; i < s.size(); ++i)
        {
          // char c = String::convertUnsignedIntToChar(s[i]);
          char c = s[i];
          if (c == '"')
          {
            if (d_variant == sygus_0_variant)
            {
              out << "\\\"";
            }
            else
            {
              out << "\"\"";
            }
          }
          else
          {
            out << c;
          }
        }
        out << '"';
        break;
      }

      case kind::STORE_ALL:
      {
        ArrayStoreAll asa = n.getConst<ArrayStoreAll>();
        out << "((as const " << asa.getType() << ") " << asa.getExpr() << ")";
        break;
      }

      case kind::DATATYPE_TYPE:
      {
        const Datatype& dt = (NodeManager::currentNM()->getDatatypeForIndex(
            n.getConst<DatatypeIndexConstant>().getIndex()));
        if (dt.isTuple())
        {
          unsigned int n = dt[0].getNumArgs();
          if (n == 0)
          {
            out << "Tuple";
          }
          else
          {
            out << "(Tuple";
            for (unsigned int i = 0; i < n; i++)
            {
              out << " " << dt[0][i].getRangeType();
            }
            out << ")";
          }
        }
        else
        {
          out << maybeQuoteSymbol(dt.getName());
        }
        break;
      }

      case kind::UNINTERPRETED_CONSTANT:
      {
        const UninterpretedConstant& uc = n.getConst<UninterpretedConstant>();
        std::stringstream ss;
        ss << '@' << uc;
        out << maybeQuoteSymbol(ss.str());
        break;
      }

      case kind::EMPTYSET:
        out << "(as emptyset " << n.getConst<EmptySet>().getType() << ")";
        break;

      default:
        // fall back on whatever operator<< does on underlying type; we
        // might luck out and be SMT-LIB v2 compliant
        kind::metakind::NodeValueConstPrinter::toStream(out, n);
    }

    return;
  }

  if (n.getKind() == kind::SORT_TYPE)
  {
    string name;
    if (n.getNumChildren() != 0)
    {
      out << '(';
    }
    if (n.getAttribute(expr::VarNameAttr(), name))
    {
      out << maybeQuoteSymbol(name);
    }
    if (n.getNumChildren() != 0)
    {
      for (unsigned i = 0; i < n.getNumChildren(); ++i)
      {
        out << ' ';
        toStream(out, n[i], toDepth, types, TypeNode::null());
      }
      out << ')';
    }
    return;
  }

  // determine if we are printing out a type ascription, store the argument of
  // the type ascription into type_asc_arg.
  Node type_asc_arg;
  if (n.getKind() == kind::APPLY_TYPE_ASCRIPTION)
  {
    force_nt = TypeNode::fromType(
        n.getOperator().getConst<AscriptionType>().getType());
    type_asc_arg = n[0];
  }
  else if (!force_nt.isNull() && n.getType() != force_nt)
  {
    type_asc_arg = n;
  }
  if (!type_asc_arg.isNull())
  {
    if (force_nt.isReal())
    {
      // we prefer using (/ x 1) instead of (to_real x) here.
      // the reason is that (/ x 1) is SMT-LIB compliant when x is a constant
      // or the logic is non-linear, whereas (to_real x) is compliant when
      // the logic is mixed int/real. The former occurs more frequently.
      bool is_int = force_nt.isInteger();
      out << "("
          << smtKindString(is_int ? kind::TO_INTEGER : kind::DIVISION,
                           d_variant)
          << " ";
      toStream(out, type_asc_arg, toDepth, types, TypeNode::null());
      if (!is_int)
      {
        out << " 1";
      }
      out << ")";
    }
    else
    {
      // use type ascription
      out << "(as ";
      toStream(out,
               type_asc_arg,
               toDepth < 0 ? toDepth : toDepth - 1,
               types,
               TypeNode::null());
      out << " " << force_nt << ")";
    }
    return;
  }

  // variable
  if (n.isVar())
  {
    string s;
    if (n.getAttribute(expr::VarNameAttr(), s))
    {
      out << maybeQuoteSymbol(s);
    }
    else
    {
      if (n.getKind() == kind::VARIABLE)
      {
        out << "var_";
      }
      else
      {
        out << n.getKind() << '_';
      }
      out << n.getId();
    }
    if (types)
    {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, language::output::LANG_SMTLIB_V2_5);
    }

    return;
  }

  bool stillNeedToPrintParams = true;
  bool forceBinary = false;  // force N-ary to binary when outputing children
  bool parametricTypeChildren =
      false;  // parametric operators that are (op t1 ... tn) where t1...tn must
              // have same type
  bool typeChildren =
      false;  // operators (op t1...tn) where at least one of t1...tn may
              // require a type cast e.g. Int -> Real
  // operator
  if (n.getNumChildren() != 0 && n.getKind() != kind::INST_PATTERN_LIST
      && n.getKind() != kind::APPLY_TYPE_ASCRIPTION)
  {
    out << '(';
  }
  switch (Kind k = n.getKind())
  {
      // builtin theory
    case kind::APPLY: break;
    case kind::EQUAL:
    case kind::DISTINCT:
      out << smtKindString(k, d_variant) << " ";
      parametricTypeChildren = true;
      break;
    case kind::CHAIN: break;
    case kind::FUNCTION_TYPE:
      out << "->";
      for (Node nc : n)
      {
        out << " ";
        toStream(out, nc, toDepth, types, TypeNode::null());
      }
      out << ")";
      return;
    case kind::SEXPR:
      break;

      // bool theory
    case kind::NOT:
    case kind::AND:
    case kind::IMPLIES:
    case kind::OR:
    case kind::XOR:
    case kind::ITE: out << smtKindString(k, d_variant) << " "; break;

    // uf theory
    case kind::APPLY_UF: typeChildren = true; break;
    // higher-order
    case kind::HO_APPLY: break;
    case kind::LAMBDA: out << smtKindString(k, d_variant) << " "; break;

    // arith theory
    case kind::PLUS:
    case kind::MULT:
    case kind::NONLINEAR_MULT:
    case kind::EXPONENTIAL:
    case kind::SINE:
    case kind::COSINE:
    case kind::TANGENT:
    case kind::COSECANT:
    case kind::SECANT:
    case kind::COTANGENT:
    case kind::ARCSINE:
    case kind::ARCCOSINE:
    case kind::ARCTANGENT:
    case kind::ARCCOSECANT:
    case kind::ARCSECANT:
    case kind::ARCCOTANGENT:
    case kind::PI:
    case kind::SQRT:
    case kind::MINUS:
    case kind::UMINUS:
    case kind::LT:
    case kind::LEQ:
    case kind::GT:
    case kind::GEQ:
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
    case kind::INTS_DIVISION:
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS:
    case kind::INTS_MODULUS_TOTAL:
    case kind::ABS:
    case kind::IS_INTEGER:
    case kind::TO_INTEGER:
    case kind::TO_REAL:
    case kind::POW:
      parametricTypeChildren = true;
      out << smtKindString(k, d_variant) << " ";
      break;

    case kind::DIVISIBLE:
      out << "(_ divisible " << n.getOperator().getConst<Divisible>().k << ")";
      stillNeedToPrintParams = false;
      break;

      // arrays theory
    case kind::SELECT:
    case kind::STORE: typeChildren = true;
    case kind::PARTIAL_SELECT_0:
    case kind::PARTIAL_SELECT_1:
    case kind::ARRAY_TYPE: out << smtKindString(k, d_variant) << " "; break;

    // string theory
    case kind::STRING_CONCAT:
      if (d_variant == z3str_variant)
      {
        out << "Concat ";
        for (unsigned i = 0; i < n.getNumChildren(); ++i)
        {
          toStream(out, n[i], -1, types, TypeNode::null());
          if (i + 1 < n.getNumChildren())
          {
            out << ' ';
          }
          if (i + 2 < n.getNumChildren())
          {
            out << "(Concat ";
          }
        }
        for (unsigned i = 0; i < n.getNumChildren() - 1; ++i)
        {
          out << ")";
        }
        return;
      }
      out << "str.++ ";
      break;
    case kind::STRING_IN_REGEXP:
    {
      stringstream ss;
      if (d_variant == z3str_variant && stringifyRegexp(n[1], ss))
      {
        out << "= ";
        toStream(out, n[0], -1, types, TypeNode::null());
        out << " ";
        Node str = NodeManager::currentNM()->mkConst(String(ss.str()));
        toStream(out, str, -1, types, TypeNode::null());
        out << ")";
        return;
      }
      out << smtKindString(k, d_variant) << " ";
      break;
    }
    case kind::STRING_LENGTH:
    case kind::STRING_SUBSTR:
    case kind::STRING_CHARAT:
    case kind::STRING_STRCTN:
    case kind::STRING_STRIDOF:
    case kind::STRING_STRREPL:
    case kind::STRING_PREFIX:
    case kind::STRING_SUFFIX:
    case kind::STRING_LEQ:
    case kind::STRING_LT:
    case kind::STRING_ITOS:
    case kind::STRING_STOI:
    case kind::STRING_CODE:
    case kind::STRING_TO_REGEXP:
    case kind::REGEXP_CONCAT:
    case kind::REGEXP_UNION:
    case kind::REGEXP_INTER:
    case kind::REGEXP_STAR:
    case kind::REGEXP_PLUS:
    case kind::REGEXP_OPT:
    case kind::REGEXP_RANGE:
    case kind::REGEXP_LOOP:
    case kind::REGEXP_EMPTY:
    case kind::REGEXP_SIGMA: out << smtKindString(k, d_variant) << " "; break;

    case kind::CARDINALITY_CONSTRAINT: out << "fmf.card "; break;
    case kind::CARDINALITY_VALUE:
      out << "fmf.card.val ";
      break;

      // bv theory
    case kind::BITVECTOR_CONCAT:
      out << "concat ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_AND:
      out << "bvand ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_OR:
      out << "bvor ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_XOR:
      out << "bvxor ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_NOT: out << "bvnot "; break;
    case kind::BITVECTOR_NAND: out << "bvnand "; break;
    case kind::BITVECTOR_NOR: out << "bvnor "; break;
    case kind::BITVECTOR_XNOR: out << "bvxnor "; break;
    case kind::BITVECTOR_COMP: out << "bvcomp "; break;
    case kind::BITVECTOR_MULT:
      out << "bvmul ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_PLUS:
      out << "bvadd ";
      forceBinary = true;
      break;
    case kind::BITVECTOR_SUB: out << "bvsub "; break;
    case kind::BITVECTOR_NEG: out << "bvneg "; break;
    case kind::BITVECTOR_UDIV: out << "bvudiv "; break;
    case kind::BITVECTOR_UDIV_TOTAL:
      out << (isVariant_2_6(d_variant) ? "bvudiv " : "bvudiv_total ");
      break;
    case kind::BITVECTOR_UREM: out << "bvurem "; break;
    case kind::BITVECTOR_UREM_TOTAL:
      out << (isVariant_2_6(d_variant) ? "bvurem " : "bvurem_total ");
      break;
    case kind::BITVECTOR_SDIV: out << "bvsdiv "; break;
    case kind::BITVECTOR_SREM: out << "bvsrem "; break;
    case kind::BITVECTOR_SMOD: out << "bvsmod "; break;
    case kind::BITVECTOR_SHL: out << "bvshl "; break;
    case kind::BITVECTOR_LSHR: out << "bvlshr "; break;
    case kind::BITVECTOR_ASHR: out << "bvashr "; break;
    case kind::BITVECTOR_ULT: out << "bvult "; break;
    case kind::BITVECTOR_ULE: out << "bvule "; break;
    case kind::BITVECTOR_UGT: out << "bvugt "; break;
    case kind::BITVECTOR_UGE: out << "bvuge "; break;
    case kind::BITVECTOR_SLT: out << "bvslt "; break;
    case kind::BITVECTOR_SLE: out << "bvsle "; break;
    case kind::BITVECTOR_SGT: out << "bvsgt "; break;
    case kind::BITVECTOR_SGE: out << "bvsge "; break;
    case kind::BITVECTOR_TO_NAT: out << "bv2nat "; break;
    case kind::BITVECTOR_REDOR: out << "bvredor "; break;
    case kind::BITVECTOR_REDAND: out << "bvredand "; break;

    case kind::BITVECTOR_EXTRACT:
    case kind::BITVECTOR_REPEAT:
    case kind::BITVECTOR_ZERO_EXTEND:
    case kind::BITVECTOR_SIGN_EXTEND:
    case kind::BITVECTOR_ROTATE_LEFT:
    case kind::BITVECTOR_ROTATE_RIGHT:
    case kind::INT_TO_BITVECTOR:
      printBvParameterizedOp(out, n);
      out << ' ';
      stillNeedToPrintParams = false;
      break;

      // sets
    case kind::UNION:
    case kind::INTERSECTION:
    case kind::SETMINUS:
    case kind::SUBSET:
    case kind::CARD:
    case kind::JOIN:
    case kind::PRODUCT:
    case kind::TRANSPOSE:
    case kind::TCLOSURE:
      parametricTypeChildren = true;
      out << smtKindString(k, d_variant) << " ";
      break;
    case kind::MEMBER: typeChildren = true;
    case kind::INSERT:
    case kind::SET_TYPE:
    case kind::SINGLETON:
    case kind::COMPLEMENT: out << smtKindString(k, d_variant) << " "; break;
    case kind::UNIVERSE_SET:
      out << "(as univset " << n.getType() << ")";
      break;

      // fp theory
    case kind::FLOATINGPOINT_FP:
    case kind::FLOATINGPOINT_EQ:
    case kind::FLOATINGPOINT_ABS:
    case kind::FLOATINGPOINT_NEG:
    case kind::FLOATINGPOINT_PLUS:
    case kind::FLOATINGPOINT_SUB:
    case kind::FLOATINGPOINT_MULT:
    case kind::FLOATINGPOINT_DIV:
    case kind::FLOATINGPOINT_FMA:
    case kind::FLOATINGPOINT_SQRT:
    case kind::FLOATINGPOINT_REM:
    case kind::FLOATINGPOINT_RTI:
    case kind::FLOATINGPOINT_MIN:
    case kind::FLOATINGPOINT_MAX:
    case kind::FLOATINGPOINT_LEQ:
    case kind::FLOATINGPOINT_LT:
    case kind::FLOATINGPOINT_GEQ:
    case kind::FLOATINGPOINT_GT:
    case kind::FLOATINGPOINT_ISN:
    case kind::FLOATINGPOINT_ISSN:
    case kind::FLOATINGPOINT_ISZ:
    case kind::FLOATINGPOINT_ISINF:
    case kind::FLOATINGPOINT_ISNAN:
    case kind::FLOATINGPOINT_ISNEG:
    case kind::FLOATINGPOINT_ISPOS:
    case kind::FLOATINGPOINT_TO_REAL:
    case kind::FLOATINGPOINT_COMPONENT_NAN:
    case kind::FLOATINGPOINT_COMPONENT_INF:
    case kind::FLOATINGPOINT_COMPONENT_ZERO:
    case kind::FLOATINGPOINT_COMPONENT_SIGN:
    case kind::FLOATINGPOINT_COMPONENT_EXPONENT:
    case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
    case kind::ROUNDINGMODE_BITBLAST:
      out << smtKindString(k, d_variant) << ' ';
      break;

    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
    case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
    case kind::FLOATINGPOINT_TO_FP_REAL:
    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
    case kind::FLOATINGPOINT_TO_FP_GENERIC:
    case kind::FLOATINGPOINT_TO_UBV:
    case kind::FLOATINGPOINT_TO_SBV:
      printFpParameterizedOp(out, n);
      out << ' ';
      stillNeedToPrintParams = false;
      break;

    case kind::APPLY_CONSTRUCTOR:
    {
      typeChildren = true;
      const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
      if (dt.isTuple())
      {
        stillNeedToPrintParams = false;
        out << "mkTuple" << (dt[0].getNumArgs() == 0 ? "" : " ");
      }
    }

    case kind::APPLY_TESTER:
    case kind::APPLY_SELECTOR:
    case kind::APPLY_SELECTOR_TOTAL:
    case kind::PARAMETRIC_DATATYPE: break;

    // separation logic
    case kind::SEP_EMP:
    case kind::SEP_PTO:
    case kind::SEP_STAR:
    case kind::SEP_WAND: out << smtKindString(k, d_variant) << " "; break;

    case kind::SEP_NIL:
      out << "(as sep.nil " << n.getType() << ")";
      break;

      // quantifiers
    case kind::FORALL:
    case kind::EXISTS:
      if (k == kind::FORALL)
      {
        out << "forall ";
      }
      else
      {
        out << "exists ";
      }
      for (unsigned i = 0; i < 2; i++)
      {
        out << n[i] << " ";
        if (i == 0 && n.getNumChildren() == 3)
        {
          out << "(! ";
        }
      }
      if (n.getNumChildren() == 3)
      {
        out << n[2];
        out << ")";
      }
      out << ")";
      return;
      break;
    case kind::BOUND_VAR_LIST:
      // the left parenthesis is already printed (before the switch)
      for (TNode::iterator i = n.begin(), iend = n.end(); i != iend;)
      {
        out << '(';
        toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1, types, 0);
        out << ' ';
        out << (*i).getType();
        // The following code do stange things
        // (*i).getType().toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
        //                         false, language::output::LANG_SMTLIB_V2_5);
        out << ')';
        if (++i != iend)
        {
          out << ' ';
        }
      }
      out << ')';
      return;
    case kind::INST_PATTERN: break;
    case kind::INST_PATTERN_LIST:
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        if (n[i].getKind() == kind::INST_ATTRIBUTE)
        {
          if (n[i][0].getAttribute(theory::FunDefAttribute()))
          {
            out << ":fun-def";
          }
        }
        else
        {
          out << ":pattern " << n[i];
        }
      }
      return;
      break;

    default:
      // fall back on however the kind prints itself; this probably
      // won't be SMT-LIB v2 compliant, but it will be clear from the
      // output that support for the kind needs to be added here.
      out << n.getKind() << ' ';
  }
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED
      && stillNeedToPrintParams)
  {
    if (toDepth != 0)
    {
      if (n.getKind() == kind::APPLY_TESTER)
      {
        unsigned cindex = Datatype::indexOf(n.getOperator().toExpr());
        const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
        if (isVariant_2_6(d_variant))
        {
          out << "(_ is ";
          toStream(out,
                   Node::fromExpr(dt[cindex].getConstructor()),
                   toDepth < 0 ? toDepth : toDepth - 1,
                   types,
                   TypeNode::null());
          out << ")";
        }
        else
        {
          out << "is-";
          toStream(out,
                   Node::fromExpr(dt[cindex].getConstructor()),
                   toDepth < 0 ? toDepth : toDepth - 1,
                   types,
                   TypeNode::null());
        }
      }
      else
      {
        toStream(out,
                 n.getOperator(),
                 toDepth < 0 ? toDepth : toDepth - 1,
                 types,
                 TypeNode::null());
      }
    }
    else
    {
      out << "(...)";
    }
    if (n.getNumChildren() > 0)
    {
      out << ' ';
    }
  }
  stringstream parens;

  // calculate the child type casts
  std::map<unsigned, TypeNode> force_child_type;
  if (parametricTypeChildren)
  {
    if (n.getNumChildren() > 1)
    {
      TypeNode force_ct = n[0].getType();
      bool do_force = false;
      for (size_t i = 1; i < n.getNumChildren(); ++i)
      {
        TypeNode ct = n[i].getType();
        if (ct != force_ct)
        {
          force_ct = TypeNode::leastCommonTypeNode(force_ct, ct);
          do_force = true;
        }
      }
      if (do_force)
      {
        for (size_t i = 0; i < n.getNumChildren(); ++i)
        {
          force_child_type[i] = force_ct;
        }
      }
    }
    // operators that may require type casting
  }
  else if (typeChildren)
  {
    if (n.getKind() == kind::SELECT)
    {
      TypeNode indexType = TypeNode::leastCommonTypeNode(
          n[0].getType().getArrayIndexType(), n[1].getType());
      TypeNode elemType = n[0].getType().getArrayConstituentType();
      force_child_type[0] =
          NodeManager::currentNM()->mkArrayType(indexType, elemType);
      force_child_type[1] = indexType;
    }
    else if (n.getKind() == kind::STORE)
    {
      TypeNode indexType = TypeNode::leastCommonTypeNode(
          n[0].getType().getArrayIndexType(), n[1].getType());
      TypeNode elemType = TypeNode::leastCommonTypeNode(
          n[0].getType().getArrayConstituentType(), n[2].getType());
      force_child_type[0] =
          NodeManager::currentNM()->mkArrayType(indexType, elemType);
      force_child_type[1] = indexType;
      force_child_type[2] = elemType;
    }
    else if (n.getKind() == kind::MEMBER)
    {
      TypeNode elemType = TypeNode::leastCommonTypeNode(
          n[0].getType(), n[1].getType().getSetElementType());
      force_child_type[0] = elemType;
      force_child_type[1] = NodeManager::currentNM()->mkSetType(elemType);
    }
    else
    {
      // APPLY_UF, APPLY_CONSTRUCTOR, etc.
      Assert(n.hasOperator());
      TypeNode opt = n.getOperator().getType();
      if (n.getKind() == kind::APPLY_CONSTRUCTOR)
      {
        Type tn = n.getType().toType();
        // may be parametric, in which case the constructor type must be
        // specialized
        const Datatype& dt = static_cast<DatatypeType>(tn).getDatatype();
        if (dt.isParametric())
        {
          unsigned ci = Datatype::indexOf(n.getOperator().toExpr());
          opt = TypeNode::fromType(dt[ci].getSpecializedConstructorType(tn));
        }
      }
      Assert(opt.getNumChildren() == n.getNumChildren() + 1);
      for (size_t i = 0; i < n.getNumChildren(); ++i)
      {
        force_child_type[i] = opt[i];
      }
    }
  }

  for (size_t i = 0, c = 1; i < n.getNumChildren();)
  {
    if (toDepth != 0)
    {
      Node cn = n[i];
      std::map<unsigned, TypeNode>::iterator itfc = force_child_type.find(i);
      if (itfc != force_child_type.end())
      {
        toStream(
            out, cn, toDepth < 0 ? toDepth : toDepth - c, types, itfc->second);
      }
      else
      {
        toStream(out,
                 cn,
                 toDepth < 0 ? toDepth : toDepth - c,
                 types,
                 TypeNode::null());
      }
    }
    else
    {
      out << "(...)";
    }
    if (++i < n.getNumChildren())
    {
      if (forceBinary && i < n.getNumChildren() - 1)
      {
        // not going to work properly for parameterized kinds!
        Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
        out << " (" << smtKindString(n.getKind(), d_variant) << ' ';
        parens << ')';
        ++c;
      }
      else
      {
        out << ' ';
      }
    }
  }
  if (n.getNumChildren() != 0)
  {
    out << parens.str() << ')';
  }
} /* SygusPrinter::toStream(TNode) */

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);
template <class T>
static bool tryToStream(std::ostream& out, const Command* c, Variant v);

void SygusPrinter::toStream(std::ostream& out,
                           const Command* c,
                           int toDepth,
                           bool types,
                           size_t dag) const
{
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);
  expr::ExprDag::Scope dagScope(out, dag);

  if (tryToStream<AssertCommand>(out, c) || tryToStream<PushCommand>(out, c)
      || tryToStream<PopCommand>(out, c) || tryToStream<CheckSatCommand>(out, c)
      || tryToStream<CheckSatAssumingCommand>(out, c)
      || tryToStream<QueryCommand>(out, c, d_variant)
      || tryToStream<ResetCommand>(out, c)
      || tryToStream<ResetAssertionsCommand>(out, c)
      || tryToStream<QuitCommand>(out, c)
      || tryToStream<DeclarationSequence>(out, c)
      || tryToStream<CommandSequence>(out, c)
      || tryToStream<DeclareFunctionCommand>(out, c)
      || tryToStream<DeclareTypeCommand>(out, c)
      || tryToStream<DefineTypeCommand>(out, c)
      || tryToStream<DefineNamedFunctionCommand>(out, c)
      || tryToStream<DefineFunctionCommand>(out, c)
      || tryToStream<DefineFunctionRecCommand>(out, c)
      || tryToStream<SimplifyCommand>(out, c)
      || tryToStream<GetValueCommand>(out, c)
      || tryToStream<GetModelCommand>(out, c)
      || tryToStream<GetAssignmentCommand>(out, c)
      || tryToStream<GetAssertionsCommand>(out, c)
      || tryToStream<GetProofCommand>(out, c)
      || tryToStream<GetUnsatAssumptionsCommand>(out, c)
      || tryToStream<GetUnsatCoreCommand>(out, c)
      || tryToStream<SetBenchmarkStatusCommand>(out, c, d_variant)
      || tryToStream<SetBenchmarkLogicCommand>(out, c, d_variant)
      || tryToStream<SetInfoCommand>(out, c, d_variant)
      || tryToStream<GetInfoCommand>(out, c)
      || tryToStream<SetOptionCommand>(out, c)
      || tryToStream<GetOptionCommand>(out, c)
      || tryToStream<DatatypeDeclarationCommand>(out, c, d_variant)
      || tryToStream<CommentCommand>(out, c, d_variant)
      || tryToStream<EmptyCommand>(out, c)
      || tryToStream<EchoCommand>(out, c, d_variant))
  {
    return;
  }

  out << "ERROR: don't know how to print a Command of class: "
      << typeid(*c).name() << endl;

} /* SygusPrinter::toStream(Command*) */

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s, Variant v);

void SygusPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  if (tryToStream<CommandSuccess>(out, s, d_variant)
      || tryToStream<CommandFailure>(out, s, d_variant)
      || tryToStream<CommandRecoverableFailure>(out, s, d_variant)
      || tryToStream<CommandUnsupported>(out, s, d_variant)
      || tryToStream<CommandInterrupted>(out, s, d_variant))
  {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

} /* SygusPrinter::toStream(CommandStatus*) */

void SygusPrinter::toStreamSygus(std::ostream& out, TNode n) const
{
  if (n.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    TypeNode tn = n.getType();
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    if (dt.isSygus())
    {
      int cIndex = Datatype::indexOf(n.getOperator().toExpr());
      Assert(!dt[cIndex].getSygusOp().isNull());
      SygusPrintCallback* spc = dt[cIndex].getSygusPrintCallback().get();
      if (spc != nullptr && options::sygusPrintCallbacks())
      {
        spc->toStreamSygus(this, out, n.toExpr());
      }
      else
      {
        if (n.getNumChildren() > 0)
        {
          out << "(";
        }
        out << dt[cIndex].getSygusOp();
        if (n.getNumChildren() > 0)
        {
          for (Node nc : n)
          {
            out << " ";
            toStreamSygus(out, nc);
          }
          out << ")";
        }
      }
      return;
    }
  }
  else
  {
    Node p = n.getAttribute(theory::SygusPrintProxyAttribute());
    if (!p.isNull())
    {
      out << p;
    }
    else
    {
      // cannot convert term to analog, print original
      out << n;
    }
  }
}

static void toStream(std::ostream& out,
                     const SetBenchmarkLogicCommand* c,
                     Variant v)
{
  out << "(set-logic " << c->getLogic() << ")";
}

static void toStream(std::ostream& out, const ConstraintCommand* c)
{
  out << "(constraint " << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const CheckSynthCommand* c)
{
  out << "(check-synth)";
}

static void toStream(std::ostream& out, const SynthFunCommand* c)
{
  out << "(check-synth)";
}

static void toStream(std::ostream& out, const CommandSequence* c)
{
  CommandSequence::const_iterator i = c->begin();
  if (i != c->end())
  {
    for (;;)
    {
      out << *i;
      if (++i != c->end())
      {
        out << endl;
      }
      else
      {
        break;
      }
    }
  }
}

static void toStream(std::ostream& out, const DeclareVarCommand* c)
{
  Type type = c->getType();
  out << "(declare-fun " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  if (type.isFunction())
  {
    FunctionType ft = type;
    const vector<Type> argTypes = ft.getArgTypes();
    if (argTypes.size() > 0)
    {
      copy(argTypes.begin(),
           argTypes.end() - 1,
           ostream_iterator<Type>(out, " "));
      out << argTypes.back();
    }
    type = ft.getRangeType();
  }

  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const DeclarePrimedVarCommand* c)
{
  Type type = c->getType();
  out << "(declare-fun " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  if (type.isFunction())
  {
    FunctionType ft = type;
    const vector<Type> argTypes = ft.getArgTypes();
    if (argTypes.size() > 0)
    {
      copy(argTypes.begin(),
           argTypes.end() - 1,
           ostream_iterator<Type>(out, " "));
      out << argTypes.back();
    }
    type = ft.getRangeType();
  }

  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c)
{
  Type type = c->getType();
  out << "(declare-fun " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  if (type.isFunction())
  {
    FunctionType ft = type;
    const vector<Type> argTypes = ft.getArgTypes();
    if (argTypes.size() > 0)
    {
      copy(argTypes.begin(),
           argTypes.end() - 1,
           ostream_iterator<Type>(out, " "));
      out << argTypes.back();
    }
    type = ft.getRangeType();
  }

  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const Datatype& d)
{
  for (Datatype::const_iterator ctor = d.begin(), ctor_end = d.end();
       ctor != ctor_end;
       ++ctor)
  {
    if (ctor != d.begin()) out << " ";
    out << "(" << maybeQuoteSymbol(ctor->getName());

    for (DatatypeConstructor::const_iterator arg = ctor->begin(),
                                             arg_end = ctor->end();
         arg != arg_end;
         ++arg)
    {
      out << " (" << arg->getSelector() << " "
          << static_cast<SelectorType>(arg->getType()).getRangeType() << ")";
    }
    out << ")";
  }
}


}  // namespace sygus
}  // namespace printer
}  // namespace CVC4
