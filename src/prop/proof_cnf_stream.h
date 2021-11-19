/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Dejan Jovanovic, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof-producing CNF stream.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PROOF_CNF_STREAM_H
#define CVC5__PROP__PROOF_CNF_STREAM_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "prop/sat_proof_manager.h"

namespace cvc5 {
namespace prop {

class SatProofManager;

/**
 * A proof generator for CNF transformation. It is a layer on top of CNF stream,
 * tracking the justifications for clauses added into the underlying SAT solver
 * in a user-context dependent manner in a lazy context-dependent (LazyCDProof)
 * object. The proof is lazy because formulas asserted to this class may also
 * take proof generators (which is the case, for example, for theory lemmas), so
 * that getting the proof of a clausified formula will also extend to its
 * registered proof generator.
 */
class ProofCnfStream : public ProofGenerator
{
 public:
  ProofCnfStream(context::UserContext* u,
                 CnfStream& cnfStream,
                 SatProofManager* satPM,
                 ProofNodeManager* pnm);

  /** Invokes getProofFor of the underlying LazyCDProof */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Whether there is a concrete step or a generator associated with f in the
   * underlying LazyCDProof. */
  bool hasProofFor(Node f) override;
  /** identify */
  std::string identify() const override;
  /**
   * Converts a formula into CNF into CNF and asserts the generated clauses into
   * the underlying SAT solver of d_cnfStream. Every transformation the formula
   * goes through is saved as a concrete step in d_proof.
   *
   * The given formula has arbitrary Boolean structure via kinds AND, OR, EQUAL,
   * XOR, IMPLIES. ITE and NOT. The conversion is done polynomially via Tseitin
   * transformation, with the children of non-conjunctive kinds being abstracted
   * as new literals, which are clausified with the respective "handle" methods
   * below.

   * @param node formula to convert and assert
   * @param negated whether we are asserting the node negated
   * @param removable whether the SAT solver can choose to remove the clauses
   * @param pg a proof generator for node
   */
  void convertAndAssert(TNode node,
                        bool negated,
                        bool removable,
                        ProofGenerator* pg);

  /**
   * Clausifies the given propagation lemma *without* registering the resoluting
   * clause in the SAT solver, as this is handled internally by the SAT
   * solver. The clausification steps and the generator within the trust node
   * are saved in d_proof if we are producing proofs in the theory engine. */
  void convertPropagation(TrustNode ttn);
  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it.  The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n);

  /**
   * Blocks a proof, so that it is not further updated by a post processor of
   * this class's proof. */
  void addBlocked(std::shared_ptr<ProofNode> pfn);

  /**
   * Whether a given proof is blocked for further updates.  An example of a
   * blocked proof node is one integrated into this class via an external proof
   * generator. */
  bool isBlocked(std::shared_ptr<ProofNode> pfn);

  void notifyOptPropagation(int explLevel);

  context::Context* getContext() { return d_userContext; }

 private:
  /**
   * Same as above, except that uses the saved d_removable flag. It calls the
   * dedicated converter for the possible formula kinds.
   */
  void convertAndAssert(TNode node, bool negated);
  /** Specific converters for each formula kind. */
  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);
  /**
   * Transforms the node into CNF recursively and yields a literal
   * definitionally equal to it.
   *
   * This method also populates caches, kept in d_cnfStream, between formulas
   * and literals to avoid redundant work and to retrieve formulas from literals
   * and vice-versa.
   *
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);
  /**
   * Specific clausifiers, based on the formula kinds, that clausify a formula,
   * by calling toCNF into each of the formula's children under the respective
   * kind, and introduce a literal definitionally equal to it. */
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  /** Normalizes a clause node and registers it in the SAT proof manager.
   *
   * Normalization (factoring, reordering, double negation elimination) is done
   * via the TheoryProofStepBuffer of this class, which will register the
   * respective steps, if any. This normalization is necessary so that the
   * resulting clauses of the clausification process are synchronized with the
   * clauses used in the underlying SAT solver, which automatically performs the
   * above normalizations on all added clauses.
   *
   * @param clauseNode The clause node to be normalized.
   * @return The normalized clause node.
   */
  Node normalizeAndRegister(TNode clauseNode);

  /** Reference to the underlying cnf stream. */
  CnfStream& d_cnfStream;
  /** The proof manager of underlying SAT solver associated with this stream. */
  SatProofManager* d_satPM;
  /** The proof node manager. */
  ProofNodeManager* d_pnm;
  /** The user-context-dependent proof object. */
  LazyCDProof d_proof;

  context::UserContext* d_userContext;
  /** An accumulator of steps that may be applied to normalize the clauses
   * generated during clausification. */
  TheoryProofStepBuffer d_psb;
  /** Blocked proofs.
   *
   * These are proof nodes added to this class by external generators. */
  context::CDHashSet<std::shared_ptr<ProofNode>, ProofNodeHashFunction>
      d_blocked;

  class OptimizedPropagationsManager : context::ContextNotifyObj
  {
   public:
    OptimizedPropagationsManager(
        context::Context* context,
        std::map<int, std::vector<std::shared_ptr<ProofNode>>>& optProofs, LazyCDProof* parentProof)
        : context::ContextNotifyObj(context),
          d_context(context),
          d_optProofs(optProofs),
          d_parentProof(parentProof)
    {
    }

   protected:
    void contextNotifyPop() override
    {
      int newLvl = d_context->getLevel();
      Trace("cnf") << "contextNotifyPop: called with lvl " << newLvl << "\n"
                   << push;
      // the increment is handled inside the loop, so that we can erase as we go
      for (auto it = d_optProofs.cbegin(); it != d_optProofs.cend();)
      {
        if (it->first <= newLvl)
        {
          Trace("cnf") << "Should re-add pfs of [" << it->first << "]:\n";
          for (const auto& pf : it->second)
          {
            Node processedPropgation = pf->getResult();
            Trace("cnf") << "\t- " << processedPropgation << "\n\t\t"
                         << *pf.get() << "\n";
            // Note that this proof may have already been added in a previous
            // pop. For example, if a proof associated with level 1 was added
            // when going down from 2 to 1, but then we went up to 2 again, when
            // we go back to 1 the proof will still be there. Note that if say
            // we had a proof of level 1 that was added at level 2 when we were
            // going down from 3, we'd still need to add it again when going to
            // level 1, since it'd be popped in that case.
            if (!d_parentProof->hasStep(processedPropgation))
            {
              Trace("cnf") << "\t..skipped since already added\n";
              d_parentProof->addProof(pf);
            }
          }
          ++it;
          continue;
        }
        Trace("cnf") << "Should remove from map pfs of [" << it->first
                     << "]:\n";
        for (const auto& pf : it->second)
        {
          Trace("cnf") << "\t- " << pf->getResult() << "\n";
        }
        it = d_optProofs.erase(it);
      }
      Trace("cnf") << pop;
    }

   private:
    context::Context* d_context;
    std::map<int, std::vector<std::shared_ptr<ProofNode>>>& d_optProofs;
    LazyCDProof* d_parentProof;
  };

  Node d_currPropagationProccessed;
  std::map<int, std::vector<std::shared_ptr<ProofNode>>> d_optPropagations;
  OptimizedPropagationsManager d_optPropagationsManager;
};

}  // namespace prop
}  // namespace cvc5

#endif
