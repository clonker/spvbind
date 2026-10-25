// SPIRV-Reflect's view of a module's push constant blocks, in the format of `spvbind --locations`.
#pragma once

#include <cstddef>
#include <string>

namespace spvbind_fuzz {

struct Reflection {
    bool ok = false;      // SPIRV-Reflect accepted the module
    std::string text;     // the locations, or the error
    bool inconsistent = false;  // a nested member's absolute offset is not its parent's plus its own
};

/// One scalar per line, tab-separated: variable id; struct names, member indices and member names along the path,
/// each joined with `/`; absolute byte offset; the scalar as `i`, `u` or `f` and its width. A member that is neither a
/// scalar nor a struct prints as `unsupported` with its type flags. Lines starting with `!` are inconsistencies in
/// SPIRV-Reflect's own output.
Reflection reflectLocations(const void* data, std::size_t size);

}  // namespace spvbind_fuzz
