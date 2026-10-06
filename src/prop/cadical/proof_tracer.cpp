/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CaDiCaL proof tracer.
 *
 * Implementation of a CaDiCaL proof tracer.
 */

#include "prop/cadical/proof_tracer.h"

#include <unordered_set>

#include "proof/proof_node.h"
#include "prop/cadical/cadical.h"
#include "prop/cadical/cdclt_propagator.h"
#include "prop/prop_proof_manager.h"

namespace cvc5::internal::prop::cadical {

namespace {

Node toNode(NodeManager* nm, TheoryProxy* proxy, const SatClause& clause)
{
  if (clause.empty())
  {
    return nm->mkConst(false);
  }
  std::vector<Node> lits;
  for (const auto& lit : clause)
  {
    lits.push_back(proxy->getNode(lit));
  }
  // Sat clause is sorted by literal id. Ensure that node-level clause is
  // sorted by node ids. Also factor duplicate literals to match the
  // normalization done by PropPfManager when registering CNF clause proofs.
  std::sort(lits.begin(), lits.end());
  lits.erase(std::unique(lits.begin(), lits.end()), lits.end());
  return lits.size() == 1 ? lits[0] : nm->mkNode(Kind::OR, lits);
}

/**
 * Normalize a unary CaDiCaL derivation to a proof of conclusion.
 *
 * CaDiCaL's LRUP trace can contain derived clauses with exactly one
 * antecedent. These steps are not resolution chains; they typically remove
 * duplicate literals from the antecedent and may leave the node-level clause
 * order different from the normalized conclusion expected by cvc5.
 *
 * Since CHAIN_M_RESOLUTION needs at least two premises, this builds the proof
 * with the smaller Boolean proof rules instead:
 * - reuse the child if it already proves conclusion,
 * - use FACTORING when duplicate literals are removed,
 * - add REORDERING when the factored clause has the right literals in a
 *   different order,
 * - or use REORDERING directly if no factoring is required.
 */
std::shared_ptr<ProofNode> normalizeDerivedClause(
    ProofNodeManager* pnm,
    const std::shared_ptr<ProofNode>& child,
    const Node& conclusion)
{
  Node childConclusion = child->getResult();
  if (childConclusion == conclusion)
  {
    return child;
  }

  std::vector<std::shared_ptr<ProofNode>> children{child};
  std::shared_ptr<ProofNode> factored =
      pnm->mkNode(ProofRule::FACTORING, children, {}, conclusion);
  if (factored != nullptr)
  {
    return factored;
  }

  factored = pnm->mkNode(ProofRule::FACTORING, children, {});
  if (factored != nullptr)
  {
    if (factored->getResult() == conclusion)
    {
      return factored;
    }
    return pnm->mkNode(
        ProofRule::REORDERING, {factored}, {conclusion}, conclusion);
  }

  return pnm->mkNode(ProofRule::REORDERING, children, {conclusion}, conclusion);
}

}  // namespace

ProofTracer::ProofTracer(const CadicalPropagator& propagator)
    : d_propagator(propagator)
{
}

void ProofTracer::enableLogging(NodeManager* nm,
                                TheoryProxy* proxy,
                                PropPfManager* ppm)
{
  d_nm = nm;
  d_proxy = proxy;
  d_ppm = ppm;
}

void ProofTracer::add_original_clause(uint64_t clause_id,
                                      CVC5_UNUSED bool redundant,
                                      const std::vector<int>& clause,
                                      CVC5_UNUSED bool restored)
{
  ClauseType ctype =
      d_propagator.in_search() ? ClauseType::THEORY : ClauseType::INPUT;
  d_clauses.emplace(clause_id, ClauseInfo(clause_id, ctype, clause));
  Trace("cadical::prooftracer") << d_clauses.at(clause_id) << std::endl;
}

void ProofTracer::add_derived_clause(CVC5_UNUSED uint64_t clause_id,
                                     bool redundant,
                                     const std::vector<int>& clause,
                                     const std::vector<uint64_t>& antecedents)
{
  (void)redundant;
  auto it =
      d_clauses
          .emplace(
              clause_id,
              ClauseInfo(clause_id, ClauseType::DERIVED, clause, antecedents))
          .first;
  Trace("cadical::prooftracer") << it->second << std::endl;
  if (d_ppm != nullptr)
  {
    logDerivedClause(it->second);
  }
}

Node ProofTracer::mkLoggedClause(
    const std::unordered_set<int64_t>& activation_literals,
    const std::vector<int32_t>& lits) const
{
  std::vector<Node> nodes;
  for (const SatLiteral& lit : toSatClause(activation_literals, lits))
  {
    nodes.push_back(d_proxy->getNode(lit));
  }
  // CaDiCaL clauses added by cvc5 may contain duplicate literals, which are
  // not in the clauses logged for them
  std::sort(nodes.begin(), nodes.end());
  nodes.erase(std::unique(nodes.begin(), nodes.end()), nodes.end());
  return d_nm->mkNode(Kind::SEXPR, nodes);
}

void ProofTracer::logDerivedClause(const ClauseInfo& ci)
{
  std::unordered_set<int64_t> alits;
  for (const auto& lit : d_propagator.activation_literals())
  {
    alits.insert(lit.getSatVariable());
  }
  // The antecedents are stored in the order they were resolved, so we list
  // them in reverse order, as for the chain resolution step built for the
  // proof (see chain_resolution_step).
  std::vector<Node> premises;
  for (size_t i = ci.antecedents.size(); i > 0; --i)
  {
    const ClauseInfo& ai = d_clauses.at(ci.antecedents[i - 1]);
    premises.push_back(mkLoggedClause(alits, ai.literals));
  }
  // Every antecedent is given when the clause is derived, so no premise is
  // explained lazily.
  d_ppm->logSatClause(mkLoggedClause(alits, ci.literals), premises);
}

void ProofTracer::add_assumption_clause(
    uint64_t clause_id,
    const std::vector<int>& clause,
    const std::vector<uint64_t>& antecedents)
{
  // Assumption clauses are the negation of the core of failed/unsat
  // assumptions.
  auto it =
      d_clauses
          .emplace(clause_id,
                   ClauseInfo(
                       clause_id, ClauseType::ASSUMPTION, clause, antecedents))
          .first;
  Trace("cadical::prooftracer") << it->second << std::endl;
  if (d_ppm != nullptr)
  {
    logAssumptionClause(it->second);
  }
}

void ProofTracer::logAssumptionClause(const ClauseInfo& ci)
{
  std::unordered_set<int64_t> alits;
  for (const auto& lit : d_propagator.activation_literals())
  {
    alits.insert(lit.getSatVariable());
  }
  SatClause satClause = toSatClause(alits, ci.literals);
  if (satClause.empty())
  {
    // only activation literals, the last derived clause is already empty
    return;
  }
  // log the clause, which is derived from its antecedents
  logDerivedClause(ci);
  // log the empty clause, derived from it and the unit clauses of the
  // assumptions
  std::vector<Node> premises{mkLoggedClause(alits, ci.literals)};
  for (const SatLiteral& lit : satClause)
  {
    premises.push_back(d_nm->mkNode(Kind::SEXPR, d_proxy->getNode(~lit)));
  }
  d_ppm->logSatClause(d_nm->mkNode(Kind::SEXPR, std::vector<Node>{}), premises);
}

void ProofTracer::conclude_unsat(CVC5_UNUSED CaDiCaL::ConclusionType type,
                                 const std::vector<uint64_t>& clause_ids)
{
  // Store final clause ids that concluded unsat.
  d_final_clauses = clause_ids;
}

void ProofTracer::compute_proof_core(std::vector<uint64_t>& core) const
{
  std::vector<uint64_t> visit{d_final_clauses};
  std::unordered_set<uint64_t> visited;

  // Trace back from final clause ids (empty clause) to original clauses.
  while (!visit.empty())
  {
    const uint64_t clause_id = visit.back();
    visit.pop_back();

    if (visited.insert(clause_id).second)
    {
      core.push_back(clause_id);
      const auto& antecedents = d_clauses.at(clause_id).antecedents;
      visit.insert(visit.end(), antecedents.begin(), antecedents.end());
    }
  }

  if (TraceIsOn("cadical::prooftracer"))
  {
    Trace("cadical::prooftracer") << "proof core:" << std::endl;
    for (const auto& cid : core)
    {
      const auto& clause = d_clauses.at(cid);
      Trace("cadical::prooftracer") << clause << std::endl;
    }
  }
}

std::shared_ptr<ProofNode> ProofTracer::get_chain_resolution_proof(
    ProofNodeManager* pnm, NodeManager* nm, TheoryProxy* proxy)
{
  std::vector<uint64_t> core;
  compute_proof_core(core);
  // Sort core clause ids in ascending order to construct proof steps
  // starting from the original clauses.
  std::sort(core.begin(), core.end());

  std::unordered_set<int64_t> alits;
  for (const auto& lit : d_propagator.activation_literals())
  {
    alits.insert(lit.getSatVariable());
  }

  std::unordered_map<uint64_t, std::shared_ptr<ProofNode>> steps;
  for (const uint64_t cid : core)
  {
    const auto& clause = d_clauses.at(cid);
    if (clause.type == ClauseType::DERIVED)
    {
      Assert(!clause.antecedents.empty());
      steps.emplace(cid,
                    chain_resolution_step(cid, proxy, pnm, nm, steps, alits));
    }
    else
    {
      SatClause sat_clause = toSatClause(alits, clause.literals);
      if (clause.type == ClauseType::ASSUMPTION)
      {
        Assert(cid == core.back());
        // Empty antecedents for assumption clauses only happen with constraint
        // feature (CaDiCaL's constrain method), which we don't use. The main
        // application is model checking.
        Assert(!clause.antecedents.empty());
        if (sat_clause.empty())
        {
          // The clause only has activation literals, hence the previous
          // clause of the core is already the empty clause.
          steps.emplace(cid, steps.at(core[core.size() - 2]));
        }
        else
        {
          // The clause is the negation of failed assumptions, e.g., the
          // preprocessed assertions when computing unsat cores by solving
          // under assumptions.
          steps.emplace(
              cid,
              assumption_refutation_step(cid, proxy, pnm, nm, steps, alits));
        }
      }
      else
      {
        Node assump = toNode(nm, proxy, sat_clause);
        steps.emplace(cid, pnm->mkAssume(assump));
      }
    }
  }
  // Last clause id corresponds to empty clause.
  auto pf = steps.at(core.back());
  return pf;
}

std::shared_ptr<ProofNode> ProofTracer::assumption_refutation_step(
    uint64_t cid,
    TheoryProxy* proxy,
    ProofNodeManager* pnm,
    NodeManager* nm,
    const std::unordered_map<uint64_t, std::shared_ptr<ProofNode>>& steps,
    const std::unordered_set<int64_t>& activation_literals)
{
  // the proof of the clause from its antecedents
  std::vector<std::shared_ptr<ProofNode>> children{
      chain_resolution_step(cid, proxy, pnm, nm, steps, activation_literals)};
  // resolve it with the unit clause of each assumption, i.e., the negation of
  // each of its literals
  std::vector<Node> polarities, literals;
  for (const SatLiteral& lit :
       toSatClause(activation_literals, d_clauses.at(cid).literals))
  {
    SatLiteral alit = ~lit;
    children.push_back(pnm->mkAssume(proxy->getNode(alit)));
    // the pivot occurs positively in the clause iff the assumption is
    // negative
    literals.push_back(proxy->getNode(SatLiteral(alit.getSatVariable())));
    polarities.push_back(nm->mkConst(alit.isNegated()));
  }
  std::vector<Node> args{nm->mkConst(false)};
  args.push_back(nm->mkNode(Kind::SEXPR, polarities));
  args.push_back(nm->mkNode(Kind::SEXPR, literals));
  return pnm->mkNode(ProofRule::CHAIN_M_RESOLUTION, children, args);
}

bool ProofTracer::mark_var(std::unordered_map<int32_t, uint8_t>& marked_vars,
                           int32_t lit)
{
  int32_t var = std::abs(lit);
  uint8_t mask = (lit < 0) ? 2 : 1;
  uint8_t marked = marked_vars[var];
  if (!(marked & mask))
  {
    marked_vars[var] |= mask;
  }
  return marked & ~mask;
}

std::shared_ptr<ProofNode> ProofTracer::chain_resolution_step(
    uint64_t cid,
    TheoryProxy* proxy,
    ProofNodeManager* pnm,
    NodeManager* nm,
    const std::unordered_map<uint64_t, std::shared_ptr<ProofNode>>& steps,
    const std::unordered_set<int64_t>& activation_literals)
{
  const auto& cl = d_clauses.at(cid);
  SatClause expected_cl = toSatClause(activation_literals, cl.literals);
  Node conclusion = toNode(nm, proxy, expected_cl);
  const auto& antecedents = cl.antecedents;
  // Handle unary derivations separately; see normalizeDerivedClause.
  if (antecedents.size() == 1)
  {
    auto it = steps.find(antecedents[0]);
    Assert(it != steps.end());
    return normalizeDerivedClause(pnm, it->second, conclusion);
  }
  std::vector<std::shared_ptr<ProofNode>> children;
  std::vector<Node> polarities, literals;
  std::unordered_map<int32_t, uint8_t> marked_vars;
  // Create chain resolution step for each derived clause
  for (size_t i = 0, size = antecedents.size(); i < size; ++i)
  {
    // Antecedants are stored in the order they were resolved. Thus, we have
    // to process them in reverse order, starting from the last id.
    size_t idx = size - i - 1;
    uint64_t aid = antecedents[idx];
    const auto& clause = d_clauses.at(aid);
    for (int32_t lit : clause.literals)
    {
      if (!mark_var(marked_vars, lit))
      {
        continue;
      }
      // Found pivot literal
      literals.push_back(proxy->getNode(toSatLiteral(std::abs(lit))));
      // Polarity of pivot literal in this antecedent
      polarities.push_back(nm->mkConst(!(lit > 0)));
    }

    auto it = steps.find(aid);
    Assert(it != steps.end());
    children.push_back(it->second);
  }
  std::vector<Node> args{conclusion};
  args.push_back(nm->mkNode(Kind::SEXPR, polarities));
  args.push_back(nm->mkNode(Kind::SEXPR, literals));
  return pnm->mkNode(ProofRule::CHAIN_M_RESOLUTION, children, args);
}

std::ostream& operator<<(std::ostream& os, const ProofTracer::ClauseInfo& ci)
{
  char ct = ' ';
  switch (ci.type)
  {
    case ProofTracer::ClauseType::DERIVED: ct = 'd'; break;
    case ProofTracer::ClauseType::INPUT: ct = 'i'; break;
    case ProofTracer::ClauseType::THEORY: ct = 't'; break;
    case ProofTracer::ClauseType::ASSUMPTION: ct = 'a'; break;
  }

  os << ci.clause_id << " " << ct << ": ( ";
  for (const auto lit : ci.literals)
  {
    os << lit << " ";
  }
  os << ")";
  os << " [ ";
  for (const auto lit : ci.antecedents)
  {
    os << lit << " ";
  }
  os << "] ";
  return os;
}

}  // namespace cvc5::internal::prop::cadical
