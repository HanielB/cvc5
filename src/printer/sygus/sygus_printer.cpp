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
#include "util/smt2_quote_string.h"

namespace CVC4 {
namespace printer {
namespace sygus {

void SygusPrinter::toStream(
    std::ostream& out, TNode n, int toDepth, bool types, size_t dag) const
{
  // check whether sygus printing
  if (n.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    TypeNode tn = n.getType();
    const Datatype& dt = tn.getDatatype();
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
          for (const Node& nc : n)
          {
            out << " ";
            out << nc;
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
      n = p;
    }
  }
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
        d_termLangPrinter->toStream(out, (*i).second, toDepth, types, 0);
        out << ' ';
        d_termLangPrinter->toStream(out, (*i).first, toDepth, types, 0);
        out << ")) ";
      }
    }
    Node body = dv.getDagifiedBody();
    d_termLangPrinter->toStream(out, body, toDepth, types, 0);
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
    d_termLangPrinter->toStream(out, n, toDepth, types, 0);
  }
}

void SygusPrinter::toStreamSygus(std::ostream& out, TNode n) const
{
  out << n;
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);

void SygusPrinter::toStream(std::ostream& out,
                            const Command* c,
                            int toDepth,
                            bool types,
                            size_t dag) const
{
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);
  expr::ExprDag::Scope dagScope(out, dag);

  if (tryToStream<SetBenchmarkLogicCommand>(out, c)
      || tryToStream<CommandSequence>(out, c)
      || tryToStream<DeclareVarCommand>(out, c)
      || tryToStream<DeclarePrimedVarCommand>(out, c)
      || tryToStream<DeclareFunctionCommand>(out, c)
      || tryToStream<DefineFunctionCommand>(out, c)
      || tryToStream<SynthFunCommand>(out, c)
      || tryToStream<ConstraintCommand>(out, c)
      || tryToStream<InvConstraintCommand>(out, c)
      || tryToStream<CheckSynthCommand>(out, c))
  {
    return;
  }

  out << "ERROR: don't know how to print a Command of class: "
      << typeid(*c).name() << "\n";

}

void SygusPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}

static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c)
{
  c->toStream(out, language::output::LANG_SMTLIB_V2_5);
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
        out << std::endl;
      }
      else
      {
        break;
      }
    }
  }
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c)
{
  c->toStream(out, language::output::LANG_SMTLIB_V2_5);
}

static void toStream(std::ostream& out, const DefineFunctionCommand* c)
{
  c->toStream(out, language::output::LANG_SMTLIB_V2_5);
}

static void toStream(std::ostream& out, const DeclareVarCommand* c)
{
  out << "(declare-var " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  Type type = c->getType();
  Assert(!type.isFunction());
  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const DeclarePrimedVarCommand* c)
{
  out << "(declare-primed-var " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  Type type = c->getType();
  Assert(!type.isFunction());
  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const SynthFunCommand* c)
{
  out << "(synth-" << (c->isInv() ? "inv" : "fun") << " "
      << CVC4::quoteSymbol(c->getSymbol()) << " ";
  Type type = c->getFunction().getType();
  const std::vector<Expr>& vars = c->getVars();
  Assert(!type.isFunction() || !vars.empty());
  if (type.isFunction())
  {
    // print variable list
    std::vector<Expr>::const_iterator i = vars.begin(), i_end = vars.end();
    Assert(i != i_end);
    out << "(";
    do
    {
      out << "(" << *i << " " << (*i).getType() << ")";
      if (++i != i_end)
      {
        out << " ";
      }
    } while (i != i_end);
    out << ")";
    FunctionType ft = type;
    type = ft.getRangeType();
  }
  // if not invariant-to-synthesize, print return type
  if (!c->isInv())
  {
    out << " " << type;
  }
  // print grammar, if any
  Type sygusType = c->getSygusType();
  if (sygusType.isDatatype()
      && static_cast<DatatypeType>(sygusType).getDatatype().isSygus())
  {
    out << "\n(";
    std::set<Type> grammarTypes;
    std::list<Type> typesToPrint;
    grammarTypes.insert(sygusType);
    typesToPrint.push_back(sygusType);
    // for each datatype in grammar
    //   name
    //   sygus type
    //   constructors in order
    do
    {
      Type curr = typesToPrint.front();
      typesToPrint.pop_front();
      Assert(curr.isDatatype()
             && static_cast<DatatypeType>(curr).getDatatype().isSygus());
      const Datatype& dt = static_cast<DatatypeType>(curr).getDatatype();
      // TODO make the first guys be "Start"
      out << "(" << dt.getName() << " " << dt.getSygusType() << "\n(";
      if (dt.getSygusAllowConst())
      {
        out << "(Constant " << dt.getSygusType() << ") ";
      }
      for (const DatatypeConstructor& cons : dt)
      {
        DatatypeConstructor::const_iterator i = cons.begin(),
                                            i_end = cons.end();
        if (i != i_end)
        {
          out << "(";
          // TODO use sygusprintcallback
          out << cons.getSygusOp();
          do
          {
            Type argType = (*i).getRangeType();
            // print argument type
            out << " " << argType;
            // if fresh type, store it for later processing
            if (grammarTypes.insert(argType).second)
            {
              typesToPrint.push_back(argType);
            }
          } while (++i != i_end);
          out << ")";
        }
        else
        {
          // TODO use sygusprintcallback
          out << cons.getSygusOp();
        }
        out << "\n";
      }
      out << "))\n";
    } while (!typesToPrint.empty());

    out << ")";
  }
  out << ")";
}

static void toStream(std::ostream& out, const ConstraintCommand* c)
{
  out << "(constraint " << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const InvConstraintCommand* c)
{
  out << "(inv-constraint";
  const std::vector<Expr>& place_holders = c->getPlaceHolders();
  for (const Expr& e : place_holders)
  {
    out << " " << e;
  }
  out << ")";
}

static void toStream(std::ostream& out, const CheckSynthCommand* c)
{
  out << "(check-synth)";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c)
{
  if (typeid(*c) == typeid(T))
  {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

}  // namespace sygus
}  // namespace printer
}  // namespace CVC4
