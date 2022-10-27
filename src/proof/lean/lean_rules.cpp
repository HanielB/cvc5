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
 * Implementation for the Lean rules and related utilities.
 */

#include "proof/lean/lean_rules.h"

#include <iostream>

#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace proof {

const char* toString(LeanRule id)
{
  switch (id)
  {
    case LeanRule::SCOPE: return "scope";
    case LeanRule::LIFT_OR_N_TO_IMP: return "liftOrNToImp";
    case LeanRule::LIFT_OR_N_TO_NEG: return "liftOrNToNeg";

    case LeanRule::R0: return "R1";
    case LeanRule::R0_PARTIAL: return "R1";
    case LeanRule::R1: return "R2";
    case LeanRule::R1_PARTIAL: return "R2";

    case LeanRule::FACTORING: return "factor";
    case LeanRule::REORDER: return "permutateOr";
    case LeanRule::EQ_RESOLVE: return "eqResolve";
    case LeanRule::MODUS_PONENS: return "modusPonens";
    case LeanRule::NOT_NOT_ELIM: return "notNotElim";
    case LeanRule::CONTRADICTION: return "contradiction";
    case LeanRule::AND_ELIM: return "andElim";
    case LeanRule::NOT_OR_ELIM: return "notOrElim";
    case LeanRule::AND_INTRO: return "And.intro";
    case LeanRule::AND_INTRO_PARTIAL: return "And.intro";
    case LeanRule::IMPLIES_ELIM: return "impliesElim";
    case LeanRule::NOT_IMPLIES1: return "notImplies1";
    case LeanRule::NOT_IMPLIES2: return "notImplies2";
    case LeanRule::EQUIV_ELIM1: return "equivElim1";
    case LeanRule::EQUIV_ELIM2: return "equivElim2";
    case LeanRule::NOT_EQUIV_ELIM1: return "notEquivElim1";
    case LeanRule::NOT_EQUIV_ELIM2: return "notEquivElim2";
    case LeanRule::XOR_ELIM1: return "xorElim1";
    case LeanRule::XOR_ELIM2: return "xorElim2";
    case LeanRule::NOT_XOR_ELIM1: return "notXorElim1";
    case LeanRule::NOT_XOR_ELIM2: return "notXorElim2";
    case LeanRule::ITE_ELIM1: return "iteElim1";
    case LeanRule::ITE_ELIM2: return "iteElim2";
    case LeanRule::NOT_ITE_ELIM1: return "notIteElim1";
    case LeanRule::NOT_ITE_ELIM2: return "notIteElim2";
    case LeanRule::NOT_AND: return "notAnd";
    case LeanRule::CNF_AND_POS: return "@cnfAndPos";
    case LeanRule::CNF_AND_NEG: return "cnfAndNeg";
    case LeanRule::CNF_OR_POS: return "@cnfOrPos";
    case LeanRule::CNF_OR_NEG: return "@cnfOrNeg";

    case LeanRule::CNF_IMPLIES_POS: return "cnfImpliesPos";
    case LeanRule::CNF_IMPLIES_NEG1: return "cnfImpliesNeg1";
    case LeanRule::CNF_IMPLIES_NEG2: return "cnfImpliesNeg2";
    case LeanRule::CNF_EQUIV_POS1: return "cnfEquivPos1";
    case LeanRule::CNF_EQUIV_POS2: return "cnfEquivPos2";
    case LeanRule::CNF_EQUIV_NEG1: return "cnfEquivNeg1";
    case LeanRule::CNF_EQUIV_NEG2: return "cnfEquivNeg2";
    case LeanRule::CNF_XOR_POS1: return "cnfXorPos1";
    case LeanRule::CNF_XOR_POS2: return "cnfXorPos2";
    case LeanRule::CNF_XOR_NEG1: return "cnfXorNeg1";
    case LeanRule::CNF_XOR_NEG2: return "cnfXorNeg2";
    case LeanRule::CNF_ITE_POS1: return "cnfItePos1";
    case LeanRule::CNF_ITE_POS2: return "cnfItePos2";
    case LeanRule::CNF_ITE_POS3: return "cnfItePos3";
    case LeanRule::CNF_ITE_NEG1: return "cnfIteNeg1";
    case LeanRule::CNF_ITE_NEG2: return "cnfIteNeg2";
    case LeanRule::CNF_ITE_NEG3: return "cnfIteNeg3";
    case LeanRule::TRUST: return "trust";
    case LeanRule::TH_TRUST: return "thTrust";
    case LeanRule::TH_TRUST_VALID: return "simp";

    case LeanRule::CONG: return "smtCong";
    case LeanRule::CONG_PARTIAL: return "smtCong";
    case LeanRule::REFL: return "rfl";
    case LeanRule::IFF_REFL: return "Iff.rfl";
    case LeanRule::TRANS: return "Eq.trans";
    case LeanRule::TRANS_PARTIAL: return "Eq.trans";
    case LeanRule::IFF_TRANS: return "Iff.trans";
    case LeanRule::IFF_TRANS_PARTIAL: return "Iff.trans";
    case LeanRule::SYMM: return "Eq.symm";
    case LeanRule::IFF_SYMM: return "Iff.symm";
    case LeanRule::NEG_SYMM: return "negSymm";

    case LeanRule::TRUE_INTRO: return "trueIntro";
    case LeanRule::TRUE_ELIM: return "trueElim";
    case LeanRule::FALSE_INTRO: return "falseIntro";
    case LeanRule::FALSE_ELIM: return "falseElim";

    case LeanRule::SKOLEM_INTRO: return "skolemIntro";
    case LeanRule::ITE_INTRO: return "iteIntro";

    case LeanRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, LeanRule id)
{
  out << toString(id);
  return out;
}

LeanRule getLeanRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<LeanRule>(id);
  }
  return LeanRule::UNKNOWN;
}

}  // namespace proof
}  // namespace cvc5::internal
