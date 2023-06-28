/*********************                                                        */
/*! \file lean_rules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of lean rules
 **/

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
    case LeanRule::NOT_AND: return "flipNotAnd";
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
    case LeanRule::TRUST: return "sorry";

    case LeanRule::RARE_REWRITE: return "rareRewrite";

    case LeanRule::CONG: return "congr";
    case LeanRule::CONG_PARTIAL: return "congr";
    case LeanRule::CONG_ARG: return "flipCongrArg";
    case LeanRule::CONG_ARG_PARTIAL: return "flipCongrArg";
    case LeanRule::CONG_ITE: return "congrIte";
    case LeanRule::CONG_ADD: return "congrHAdd";
    case LeanRule::CONG_ADD_PARTIAL: return "congrHAdd";
    case LeanRule::REFL: return "rfl";
    case LeanRule::TRANS: return "Eq.trans";
    case LeanRule::TRANS_PARTIAL: return "Eq.trans";
    case LeanRule::SYMM: return "Eq.symm";
    case LeanRule::NEG_SYMM: return "negSymm";

    case LeanRule::TRUE_INTRO: return "trueIntro";
    case LeanRule::TRUE_ELIM: return "trueElim";
    case LeanRule::FALSE_INTRO: return "falseIntro";
    case LeanRule::FALSE_ELIM: return "falseElim";

    case LeanRule::INST_FORALL_PARTIAL: return "flipInstForall";
    case LeanRule::INST_FORALL: return "flipInstForall";
    case LeanRule::SKOLEMIZE_PARTIAL: return "smtSkolem";

    case LeanRule::SKOLEM_INTRO: return "skolemIntro";
    case LeanRule::ITE_INTRO: return "iteIntro";

    case LeanRule::SUM_BOUNDS: return "sumBounds";
    case LeanRule::ARITH_MULT_POS: return "arithMulPos";
    case LeanRule::ARITH_MULT_NEG: return "arithMulNeg";
    case LeanRule::ARITH_MULT_SIGN: return "arithMulSign";
    case LeanRule::TRICHOTOMY: return "trichotomy";
    case LeanRule::INT_TIGHT_UB: return "intTightUb";
    case LeanRule::INT_TIGHT_LB: return "intTightLb";

    case LeanRule::READ_OVER_WRITE: return "readOverWrite";
    case LeanRule::READ_OVER_WRITE_CONTRA: return "readOverWriteContra";
    case LeanRule::READ_OVER_WRITE_ID: return "readOverWriteIdentity";
    case LeanRule::ARRAY_EXT: return "arrayExt";

    case LeanRule::BITBLAST_VAL: return "bbBvVal";
    case LeanRule::BITBLAST_VAR: return "bbBvVar";
    case LeanRule::BITBLAST_EQ: return "bbBvEq";
    case LeanRule::BITBLAST_EQ_VAL: return "bbBvEqVal";
    case LeanRule::BITBLAST_AND: return "bbBvAnd";
    case LeanRule::BITBLAST_AND_VAL: return "bbBvAndVal";
    case LeanRule::BITBLAST_ADD: return "bbBvAdd";
    case LeanRule::BITBLAST_ULT: return "bbBvUlt";
    case LeanRule::BITBLAST_ULT_VAL: return "bbBvUltVal";
    case LeanRule::BITBLAST_CONCAT: return "bbBvConcat";
    case LeanRule::BITBLAST_EXTRACT: return "bbBvExtract";

    case LeanRule::BIND: return "bind";
    case LeanRule::BIND_PARTIAL: return "bind";
    case LeanRule::BIND_LAMBDA: return "bindLambda";
    case LeanRule::BIND_LAMBDA_PARTIAL: return "bindLambda";

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
  // Trace("test-lean") << "getLeanRule::converting " << n;
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    // Trace("test-lean") << ", getting rule " << static_cast<LeanRule>(id)
    //                    << "\n";
    return static_cast<LeanRule>(id);
  }
  // Trace("test-lean") << ", failed get  int\n";
  return LeanRule::UNKNOWN;
}

}  // namespace proof
}  // namespace cvc5::internal
