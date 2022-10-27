/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Lean rules and related utilities.
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF_LEAN_RULES_H
#define CVC4__PROOF_LEAN_RULES_H

#include <iostream>

#include "expr/node.h"

namespace cvc5::internal {
namespace proof {

/**
 * Lean rules. The enum below contains the Lean rules to represent cvc5's
 * internal proof calculus. These rules are either theorems or tactics in Lean.
 */
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
  REFL,
  IFF_REFL,
  TRANS,
  TRANS_PARTIAL,
  IFF_TRANS,
  IFF_TRANS_PARTIAL,
  SYMM,
  IFF_SYMM,
  NEG_SYMM,
  TRUE_INTRO,
  TRUE_ELIM,
  FALSE_INTRO,
  FALSE_ELIM,
  // skolems
  SKOLEM_INTRO,
  ITE_INTRO,

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

/** Converts a node holding an id in the enum above to the corresponding
 *  LeanRule. */
LeanRule getLeanRule(Node n);

}  // namespace proof
}  // namespace cvc5::internal

#endif
