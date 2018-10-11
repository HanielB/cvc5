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

use namespace kind;

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
  OutputLanguage term_lang = language::output::LANG_SMTLIB_V2_5;
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
        Printer::getPrinter(term_lang)->toStream(out, (*i).second, toDepth, types, 0);
        out << ' ';
        Printer::getPrinter(term_lang)->toStream(out, (*i).first, toDepth, types, 0);
        out << ")) ";
      }
    }
    Node body = dv.getDagifiedBody();
    Printer::getPrinter(term_lang)->toStream(out, body, toDepth, types, 0);
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
    Printer::getPrinter(term_lang)->toStream(out, n, toDepth, types, 0);
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
      << typeid(*c).name() << endl;

} /* SygusPrinter::toStream(Command*) */

void SygusPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}

static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c)
{
  out << "(set-logic " << c->getLogic() << ")";
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

static void toStream(std::ostream& out, const CommentCommand* c)
{
  string s = c->getComment();
  size_t pos = 0;
  while((pos = s.find_first_of('"', pos)) != string::npos) {
    s.replace(pos, 1, (v == z3str_variant || v == smt2_0_variant) ? "\\\"" : "\"\"");
    pos += 2;
  }
  out << "(set-info :notes \"" << s << "\")";
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

static void toStream(std::ostream& out, const DefineFunctionCommand* c)
{
  Expr func = c->getFunction();
  const std::vector<Expr>* formals = &c->getFormals();
  out << "(define-fun " << func << " (";
  Type type = func.getType();
  Expr formula = c->getFormula();
  NodeManager* nm = NodeManager::currentNM();
  if (type.isFunction())
  {
    std::vector<Expr> f;
    if (formals->empty())
    {
      const std::vector<Type>& params = FunctionType(type).getArgTypes();
      for (const Type& type : params)
      {
        f.push_back(nm->mkSkolem("a",
                                 TypeNode::fromType(type),
                                 "",
                                 NodeManager::SKOLEM_NO_NOTIFY)
                        .toExpr());
      }
      formula = nm->toExprManager()->mkExpr(APPLY_UF, formula, f);
      formals = &f;
    }
    vector<Expr>::const_iterator i = formals->begin();
    for (;;)
    {
      out << "(" << (*i) << " " << (*i).getType() << ")";
      ++i;
      if (i != formals->end())
      {
        out << " ";
      }
      else
      {
        break;
      }
    }
    type = FunctionType(type).getRangeType();
  }
  out << ") " << type << " " << formula << ")";
}

static void toStream(std::ostream& out, const DeclareVarCommand* c)
{
  out << "(declare-var " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  Type type = c->getType();
  Assert(!type.isFunction()));
  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const DeclarePrimedVarCommand* c)
{
  out << "(declare-primed-var " << CVC4::quoteSymbol(c->getSymbol()) << " (";
  Type type = c->getType();
  Assert(!type.isFunction()));
  out << ") " << type << ")";
}

static void toStream(std::ostream& out, const SynthFunCommand* c)
{
  out << "(synth-" << (c->isInv() ? "inv" : "fun")
      << CVC4::quoteSymbol(c->getSymbol()) << " (";
  Type type = c->getType();
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
  out << ") " << type;
  // print grammar, if any
  //
  // for each datatype in grammar
  //   name
  //   sygus type
  //   constructors in order
  out << ")";
}

static void toStream(std::ostream& out, const ConstraintCommand* c)
{
  out << "(constraint " << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const InvConstraintCommand* c)
{
  out << "(inv-constraint";
  const Expr& place_holders = c->getPlaceHolders();
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

}  // namespace sygus
}  // namespace printer
}  // namespace CVC4
