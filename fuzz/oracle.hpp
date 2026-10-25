// spvbind as a function: the compiled Lean code of the `Spvbind` library, linked in, with its runtime.
#pragma once

#include <cstddef>
#include <string>

namespace spvbind_fuzz {

/// What `spvbind --locations` prints for the bytes of a module, or `error: ` and the message. Initializes the Lean
/// runtime on first use.
std::string oracleLocations(const void* data, std::size_t size);

/// Whether `oracleLocations` returned a rejection.
bool oracleRejected(const std::string& output);

}  // namespace spvbind_fuzz
