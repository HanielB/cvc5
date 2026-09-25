/******************************************************************************
 * Learn-time instrumentation for guided proof compression (external).
 *
 * Records, per learned clause / theory lemma, a monotonic learn-index and a
 * wall-clock time (ms since the first stamp). Keyed by the clause's *original*
 * (pre-Alethe-conversion) conclusion Node, which is exactly what the Alethe
 * step carries in its result / args[1], so the printer can look it up and emit
 * :learn-index / :learn-time attributes.
 *
 * Entirely opt-in and zero-overhead unless the environment variable
 * CVC5_LEARN_STAMP is set, so normal solving is unaffected.
 ******************************************************************************/

#include "cvc5_private.h"

#ifndef CVC5__PROOF__LEARN_STAMP_H
#define CVC5__PROOF__LEARN_STAMP_H

#include <chrono>
#include <cstdint>
#include <unordered_map>
#include <utility>

#include "expr/node.h"

namespace cvc5::internal {

class LearnStamp
{
 public:
  /** Process-wide singleton (one proof generation per cvc5 process). */
  static LearnStamp& get();

  /** True only when CVC5_LEARN_STAMP is set; gates all work. */
  bool enabled() const { return d_enabled; }

  /** Record (index, time) for `conclusion` the first time it is learned. */
  void stamp(const Node& conclusion);

  /** Look up a previously stamped conclusion. */
  bool lookup(const Node& conclusion, uint64_t& index, double& millis) const;

 private:
  LearnStamp();

  bool d_enabled;
  uint64_t d_counter;
  std::chrono::steady_clock::time_point d_start;
  std::unordered_map<Node, std::pair<uint64_t, double>> d_map;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__LEARN_STAMP_H */
