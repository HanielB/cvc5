#include "proof/alethe/alethe_util.h"

#include "util/rational.h"

namespace cvc5::internal {
namespace proof {

bool addAletheStepFromClause(AletheRule rule,
                             Node res,
                             const std::vector<Node>& conclusionLits,
                             const std::vector<Node>& children,
                             const std::vector<Node>& args,
                             CDProof& cdp,
                             NodeManager* nm,
                             proof::AletheNodeConverter* anc,
                             bool ensureChildren)
{
  std::vector<Node> newArgs{
      nm->mkConstInt(Rational(static_cast<uint32_t>(rule)))};
  newArgs.push_back(res);
  std::vector<Node> convertedLits{anc->getCl()};
  for (const Node& lit : conclusionLits)
  {
    convertedLits.push_back(anc->maybeConvert(lit));
    if (convertedLits.back().isNull())
    {
      return false;
    }
  }
  newArgs.push_back(nm->mkNode(Kind::SEXPR, convertedLits));
  for (const Node& arg : args)
  {
    Node conv = anc->maybeConvert(arg);
    if (conv.isNull())
    {
      return false;
    }
    newArgs.push_back(conv);
  }
  return cdp.addStep(
      res, ProofRule::ALETHE_RULE, children, newArgs, ensureChildren);
}

bool addAletheStep(AletheRule rule,
                   Node res,
                   Node conclusion,
                   const std::vector<Node>& children,
                   const std::vector<Node>& args,
                   CDProof& cdp,
                   NodeManager* nm,
                   proof::AletheNodeConverter* anc,
                   bool ensureChildren)
{
  std::vector<Node> newArgs{
      nm->mkConstInt(Rational(static_cast<uint32_t>(rule)))};
  newArgs.push_back(res);
  conclusion = anc->maybeConvert(conclusion);
  if (conclusion.isNull())
  {
    return false;
  }
  newArgs.push_back(conclusion);
  for (const Node& arg : args)
  {
    Node conv = anc->maybeConvert(arg);
    if (conv.isNull())
    {
      return false;
    }
    newArgs.push_back(conv);
  }
  return cdp.addStep(
      res, ProofRule::ALETHE_RULE, children, newArgs, ensureChildren);
}
}  // namespace proof
}  // namespace cvc5::internal
