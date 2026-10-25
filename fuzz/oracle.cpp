#include "oracle.hpp"

#include <lean/lean.h>

#include <cstdlib>
#include <cstring>
#include <mutex>
#include <thread>

extern "C" {
// The initializer of the Lean module `Spvbind` of package `spvbind`, as Lean names it; it initializes the runtime and
// the imported modules too. And the exported function, and the runtime's per-thread setup, which lean.h does not
// declare.
lean_object* initialize_spvbind_Spvbind(uint8_t builtin);
lean_object* spvbind_locations(lean_object* bytes);  // Spvbind.oracleLocations, @[export] in Spvbind/Oracle.lean
void lean_initialize_thread(void);
}

namespace spvbind_fuzz {
namespace {

std::thread::id mainThread;

void initialize() {
    lean_object* result = initialize_spvbind_Spvbind(1 /* builtin */);
    if (!lean_io_result_is_ok(result)) {
        lean_io_result_show_error(result);
        std::abort();
    }
    lean_dec_ref(result);
    lean_io_mark_end_initialization();
    mainThread = std::this_thread::get_id();
}

void initializeThread() {
    static thread_local bool done = false;
    if (done) return;
    done = true;
    if (std::this_thread::get_id() != mainThread) lean_initialize_thread();
}

}  // namespace

std::string oracleLocations(const void* data, std::size_t size) {
    static std::once_flag once;
    std::call_once(once, initialize);
    initializeThread();
    lean_object* bytes = lean_alloc_sarray(1, size, size);
    std::memcpy(lean_sarray_cptr(bytes), data, size);
    lean_object* result = spvbind_locations(bytes);  // consumes `bytes`
    std::string out(lean_string_cstr(result), lean_string_size(result) - 1);
    lean_dec_ref(result);
    return out;
}

bool oracleRejected(const std::string& output) { return output.compare(0, 7, "error: ") == 0; }

}  // namespace spvbind_fuzz
