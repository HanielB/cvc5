/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Declares C++ types that represent a DRAT proof.
 * Defines serialization for these types.
 *
 * You can find an introduction to DRAT in the drat-trim paper:
 *    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
 */

#include "proof/drat/drat_proof.h"

#include <algorithm>
#include <bitset>
#include <iostream>

namespace cvc5::internal {
namespace proof {

// helper functions for parsing the binary DRAT format.

/**
 * Parses a binary literal which starts at `start` and must not go beyond `end`
 *
 * Leaves the iterator one past the last byte that is a part of the clause.
 *
 * If the literal overruns `end`, then raises a `InvalidDratProofException`.
 */
prop::SatLiteral parse_binary_literal(std::string::const_iterator& start,
                                const std::string::const_iterator& proof_end)
{
  // lit is encoded as uint represented by a variable-length byte sequence
  uint64_t literal_represented_as_uint = 0;
  for (uint8_t shift = 0; start != proof_end; ++start, shift += 7)
  {
    // Check whether shift is so large that we're going to lose some
    // information
    std::cout << "\nshift " << shift << ".";
    std::cout << "\nstart " << *start << ".";
    std::cout << "\nproof_end " << *proof_end << ".";
    if (shift + 7 >= 64)
    {
      throw InvalidDratProofException(
          "While parsing a DRAT proof, encountered a literal that was too "
          "long");
    }
    unsigned char byte = *start;
    // The MSB of the byte is an indicator of whether the sequence continues
    bool continued = (byte >> 7) & 1;
    uint64_t numeric_part = byte & 0x7f;
    literal_represented_as_uint |= numeric_part << shift;
    if (!continued)
    {
      // LSB of `literal_represented_as_uint` indicates negation.
      bool negated = literal_represented_as_uint & 1;
      // Rest is the literal number
      prop::SatVariable var_number = literal_represented_as_uint >> 1;
      ++start;
      // Internal clauses start at 0, external ones start at 1.
      return prop::SatLiteral(var_number - 1, negated);
    }
  }
  throw InvalidDratProofException(
      "Literal in DRAT proof was not done when "
      "EOF was encountered");
}

/**
 * Parses a binary clause which starts at `start` and must not go beyond `end`
 *
 * Leaves the iterator one past the last byte that is a part of the clause.
 * That is, one past the null byte.
 *
 * If the clause overruns `end`, then raises a `InvalidDratProofException`.
 */
prop::SatClause parse_binary_clause(std::string::const_iterator& start,
                              const std::string::const_iterator& proof_end)
{
  prop::SatClause clause;
  // A clause is a 0-terminated sequence of literals
  while (start != proof_end)
  {
    // Is the clause done?
    if (*start == 0)
    {
      ++start;
      return clause;
    }
    else
    {
      // If not, parse another literal
      clause.emplace_back(parse_binary_literal(start, proof_end));
    }
  }
  // We've overrun the end of the byte stream.
  throw InvalidDratProofException(
      "Clause in DRAT proof was not done when "
      "EOF was encountered");
}

/**
 * Writes this SAT literal in the textual DIMACS format. i.e. as a non-zero
 * integer.
 *
 * Since internally +0 and -0 are valid literals, we add one to each
 * literal's number (SAT variable) when outputtting it.
 *
 * @param os the stream to write to
 * @param l the literal to write
 */
void outputLiteralAsDimacs(std::ostream& os, prop::SatLiteral l)
{
  if (l.isNegated())
  {
    os << '-';
  }
  // add 1 to  convert between internal literals and their DIMACS
  // representaations.
  os << l.getSatVariable() + 1;
}

// DratInstruction implementation

DratInstruction::DratInstruction(DratInstructionKind kind, prop::SatLiteral literal)
    : d_kind(kind), d_literal(literal)
// DratInstruction::DratInstruction(DratInstructionKind kind, prop::SatClause clause)
//     : d_kind(kind), d_clause(clause)
{
  // All intialized
}

// DratProof implementation

DratProof::DratProof() : d_instructions() {}

// See the "binary format" section of
// https://www.cs.utexas.edu/~marijn/drat-trim/
DratProof DratProof::fromBinary(const std::string& s)
{
  DratProof dratProof;

  // For each instruction
  std::cout << s;
  for (auto i = s.cbegin(), end = s.cend(); i != end;)
  {
    std::cout << "\n begin: " << *i << " " << std::bitset<8>(*i);
    std::cout << "\n empty: " << std::bitset<8>(' ') << ".";
    switch (*i)
    {
      case 'd':
      {
        ++i;
        // dratProof.d_instructions.emplace_back(DELETION,
        //                                   parse_binary_clause(i, end));
        break;
      }
      case 'a':
      case ' ':
      {
        ++i;
        // dratProof.d_instructions.emplace_back(ADDITION,
        //                                   parse_binary_clause(i, end));
        break;
      }
      default:
      {
        std::ostringstream errmsg;
        errmsg << "Invalid instruction in Drat proof. Instruction bits: "
               << std::bitset<8>(*i)
               << ". Expected 'a' (01100001) or 'd' "
                  "(01100100).";
        throw InvalidDratProofException(errmsg.str());
      }
    }
  }

  return dratProof;
};

std::vector<std::string> splitString(std::string s, std::string splitter) {
    std::vector<std::string> lines;
    size_t pos = 0;
    std::string token;
    while ((pos = s.find(splitter)) != std::string::npos)
    {
        token = s.substr(0, pos);
        s.erase(0, pos + splitter.length());
        if (token.length() > 0)
        {
            lines.push_back(token);
        }
    }
    token = s.substr(0, pos);
    if (token.length() > 0) {
        lines.push_back(token);
    }
    return lines;
}

void insertSatLiteral(std::vector<DratInstruction>* instructions, DratInstructionKind kind,
                      const std::vector<std::string> columns, int literalIndex) {
  int literal = stoi(columns[literalIndex]);
  bool negated = literal < 0;
  if (literal < 0)
  {
    literal *= -1;
  }
  instructions->emplace_back(kind, prop::SatLiteral((uint64_t)literal, negated));
}

// See the "binary format" section of
// https://www.cs.utexas.edu/~marijn/drat-trim/
DratProof DratProof::fromPlain(const std::string& s)
{
  DratProof dratProof;
  std::string dratLineSplitter = "\n";
  std::vector<std::string> lines = splitString(s, dratLineSplitter);

  for (const std::string line : lines)
  {
    std::string dratColumnSplitter = " ";
    std::vector<std::string> columns = splitString(line, dratColumnSplitter);
    // last line, false derivation
    if (line == lines[lines.size()-1] && columns.size() == 1 && columns[0] == "0")
    {
      dratProof.d_instructions.emplace_back(ADDITION, prop::SatLiteral(0));
      break;
    }
    // derived literal
    int literalIndex = -1;
    DratInstructionKind kind = ADDITION;
    if (columns.size() == 2)
    {
      // last but one column is the literal, last column is 0
      literalIndex = 0;
    }
    // deleted literal
    if (columns.size() == 5 && columns[0] == "d")
    {
      // last but one column is the literal, last column is 0
      literalIndex = 3;
      kind = DELETION;
    }
    if (literalIndex != -1)
    {
      insertSatLiteral(&dratProof.d_instructions, kind, columns, literalIndex);
      continue;
    }
    std::ostringstream errmsg;
    errmsg << "Invalid line in Drat proof: \""
            << line
            << "\"";
    throw InvalidDratProofException(errmsg.str());
  }

  return dratProof;
};

const std::vector<DratInstruction>& DratProof::getInstructions() const
{
  return d_instructions;
};

}  // namespace proof
}  // namespace cvc5::internal
