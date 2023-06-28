/*********************                                                        */
/*! \file lean_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF_LEAN_RULES_H
#define CVC4__PROOF_LEAN_RULES_H

#include <iostream>

#include "expr/node.h"

namespace cvc5::internal {
namespace proof {

enum class LeanRule : uint32_t
{
  // base
  SCOPE,
  LIFT_OR_N_TO_IMP,
  LIFT_OR_N_TO_NEG,
  // boolean
  R0,
  R0_PARTIAL,
  R1,
  R1_PARTIAL,
  FACTORING,
  REORDER,
  EQ_RESOLVE,
  MODUS_PONENS,
  NOT_NOT_ELIM,
  CONTRADICTION,
  // cnf
  AND_ELIM,
  AND_INTRO,
  AND_INTRO_PARTIAL,
  NOT_OR_ELIM,
  IMPLIES_ELIM,
  NOT_IMPLIES1,
  NOT_IMPLIES2,
  EQUIV_ELIM1,
  EQUIV_ELIM2,
  NOT_EQUIV_ELIM1,
  NOT_EQUIV_ELIM2,
  XOR_ELIM1,
  XOR_ELIM2,
  NOT_XOR_ELIM1,
  NOT_XOR_ELIM2,
  ITE_ELIM1,
  ITE_ELIM2,
  NOT_ITE_ELIM1,
  NOT_ITE_ELIM2,
  NOT_AND,
  // tseitin
  CNF_AND_POS,
  CNF_AND_NEG,
  CNF_OR_POS,
  CNF_OR_NEG,
  CNF_IMPLIES_POS,
  CNF_IMPLIES_NEG1,
  CNF_IMPLIES_NEG2,
  CNF_EQUIV_POS1,
  CNF_EQUIV_POS2,
  CNF_EQUIV_NEG1,
  CNF_EQUIV_NEG2,
  CNF_XOR_POS1,
  CNF_XOR_POS2,
  CNF_XOR_NEG1,
  CNF_XOR_NEG2,
  CNF_ITE_POS1,
  CNF_ITE_POS2,
  CNF_ITE_POS3,
  CNF_ITE_NEG1,
  CNF_ITE_NEG2,
  CNF_ITE_NEG3,
  // euf
  CONG,
  CONG_PARTIAL,
  CONG_ARG,
  CONG_ARG_PARTIAL,
  CONG_ITE,
  CONG_ADD,
  CONG_ADD_PARTIAL,
  REFL,
  TRANS,
  TRANS_PARTIAL,
  SYMM,
  NEG_SYMM,
  TRUE_INTRO,
  TRUE_ELIM,
  FALSE_INTRO,
  FALSE_ELIM,
  // quant
  INST_FORALL_PARTIAL,
  INST_FORALL,
  SKOLEMIZE_PARTIAL,
  // skolems
  SKOLEM_INTRO,
  ITE_INTRO,
  // arith
  SUM_BOUNDS,
  ARITH_MULT_POS,
  ARITH_MULT_NEG,
  ARITH_MULT_SIGN,
  TRICHOTOMY,
  INT_TIGHT_UB,
  INT_TIGHT_LB,
  // arrays
  READ_OVER_WRITE,
  READ_OVER_WRITE_CONTRA,
  READ_OVER_WRITE_ID,
  ARRAY_EXT,
  // bv
  BITBLAST_VAL,
  BITBLAST_VAR,
  BITBLAST_EQ,
  BITBLAST_EQ_VAL,
  BITBLAST_AND,
  BITBLAST_AND_VAL,
  BITBLAST_ULT,
  BITBLAST_ULT_VAL,
  BITBLAST_ADD,
  BITBLAST_CONCAT,
  BITBLAST_EXTRACT,

  // quants
  BIND,
  BIND_PARTIAL,
  BIND_LAMBDA,
  BIND_LAMBDA_PARTIAL,
  // RARE
  RARE_REWRITE,

  // holes
  TRUST,
  TH_TRUST,
  TH_TRUST_VALID,

  UNKNOWN
};

/**
 * Converts a Lean rule to a string.
 * @param id The Lean rule
 * @return The name of the Lean rule
 */
const char* toString(LeanRule id);

/**
 * Writes a Lean rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The Lean rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LeanRule id);

/** Convert a CVC4 Node holding an id to the corresponding LeanRule */
LeanRule getLeanRule(Node n);

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC4__PROOF_LEAN_RULES_H */
