/*
 * File:  term_tuple_enumerator_utils.cpp
 * Author:  mikolas
 * Created on:  Wed May 12 12:49:46 CEST 2021
 * Copyright (C) 2021, Mikolas Janota
 */
#include "theory/quantifiers/term_tuple_enumerator_utils.h"

#include <iterator>
#include <ostream>

#include "base/check.h"
namespace cvc5 {

/** Tracing purposes, printing a masked vector of indices. */
void traceMaskedVector(const char* trace,
                       const char* name,
                       const std::vector<bool>& mask,
                       const std::vector<size_t>& values)
{
  Assert(mask.size() == values.size());
  Trace(trace) << name << " [ ";
  for (size_t variableIx = 0; variableIx < mask.size(); variableIx++)
  {
    if (mask[variableIx])
    {
      Trace(trace) << values[variableIx] << " ";
    }
    else
    {
      Trace(trace) << "_ ";
    }
  }
  Trace(trace) << "]" << std::endl;
}

}  // namespace cvc5
