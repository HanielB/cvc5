/*********************                                                        */
/*! \file sygus_printer.h
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

#include "cvc4_private.h"

#ifndef __CVC4__PRINTER__SYGUS_PRINTER_H
#define __CVC4__PRINTER__SYGUS_PRINTER_H

#include <iostream>

#include "printer/printer.h"

namespace CVC4 {
namespace printer {
namespace sygus {

class SygusPrinter : public CVC4::Printer
{
 public:
  using CVC4::Printer::toStream;

  void toStream(std::ostream& out,
                TNode n,
                int toDepth,
                bool types,
                size_t dag) const override;

  void toStream(std::ostream& out,
                const Command* c,
                int toDepth,
                bool types,
                size_t dag) const override;

  void toStream(std::ostream& out, const CommandStatus* s) const override;

  void toStreamSygus(std::ostream& out, TNode n) const override;

 private:
  void toStream(std::ostream& out, const SExpr& sexpr) const;
}; /* class SygusPrinter */

}  // namespace sygus
}  // namespace printer
}  // namespace CVC4

#endif /* __CVC4__PRINTER__SYGUS_PRINTER_H */
