/******************************************************************************
 * Learn-time instrumentation for guided proof compression (external).
 ******************************************************************************/

#include "proof/learn_stamp.h"

#include <cstdlib>

namespace cvc5::internal {

LearnStamp::LearnStamp()
    : d_enabled(std::getenv("CVC5_LEARN_STAMP") != nullptr),
      d_counter(0),
      d_start(std::chrono::steady_clock::now())
{
}

LearnStamp& LearnStamp::get()
{
  static LearnStamp s;
  return s;
}

void LearnStamp::stamp(const Node& conclusion)
{
  if (!d_enabled || conclusion.isNull())
  {
    return;
  }
  double millis = std::chrono::duration<double, std::milli>(
                      std::chrono::steady_clock::now() - d_start)
                      .count();
  // First stamp wins: a clause is learned once, so keep the earliest time.
  if (d_map.emplace(conclusion, std::make_pair(d_counter + 1, millis)).second)
  {
    ++d_counter;
  }
}

bool LearnStamp::lookup(const Node& conclusion,
                        uint64_t& index,
                        double& millis) const
{
  auto it = d_map.find(conclusion);
  if (it == d_map.end())
  {
    return false;
  }
  index = it->second.first;
  millis = it->second.second;
  return true;
}

}  // namespace cvc5::internal
