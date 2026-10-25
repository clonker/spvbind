// Prints the push constant blocks of a SPIR-V module as SPIRV-Reflect sees them, in the format of
// `spvbind --locations`; see reflect_locations.hpp. Exit codes: 0 printed; 1 SPIRV-Reflect rejected the module
// (message on stderr); 2 usage or I/O error.

#include "reflect_locations.hpp"

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>

int main(int argc, char** argv) {
    if (argc != 2) {
        std::fprintf(stderr, "usage: reflect_dump <module.spv>\n");
        return 2;
    }
    std::ifstream file(argv[1], std::ios::binary);
    if (!file) {
        std::perror(argv[1]);
        return 2;
    }
    std::string data((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());
    auto r = spvbind_fuzz::reflectLocations(data.data(), data.size());
    if (!r.ok) {
        std::fprintf(stderr, "%s: %s\n", argv[1], r.text.c_str());
        return 1;
    }
    std::fputs(r.text.c_str(), stdout);
    return 0;
}
