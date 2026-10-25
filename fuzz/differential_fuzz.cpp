// Coverage-guided differential fuzzing of SPIRV-Reflect against spvbind, with FuzzTest. See README.md.
//
// Both run in this process: SPIRV-Reflect from spirv_reflect.c, spvbind as its compiled Lean code (oracle.hpp). In
// fuzzing mode both are instrumented, so the fuzzer is guided by what paths the module takes through either.
//
// The property: if spvbind accepts a module, SPIRV-Reflect accepts it and prints the same scalars. A crash of
// SPIRV-Reflect is caught by the sanitizers. A failing input is written to SPVBIND_FUZZ_FINDINGS (or fuzz/findings)
// as a .spv with both outputs, besides FuzzTest's own reproducer; so is every module the bytes target saw SPIRV-Reflect
// reject, as `rejected-<hash>.spv`, to be classified with spirv-val (differential.py does that automatically).

#include "oracle.hpp"
#include "reflect_locations.hpp"

#include <fuzztest/fuzztest.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

// Lean's runtime keeps its persistent objects until the process ends, which LeakSanitizer would report at exit. A
// failed huge allocation returns null instead of aborting: SPIRV-Reflect sizes a struct's member arrays by the largest
// member index any decoration names, so one bogus index asks for hundreds of gigabytes, which it then reports as
// ALLOC_FAILED (a rejection, recorded by the bytes target) rather than ending the run.
extern "C" const char* __asan_default_options() { return "detect_leaks=0:allocator_may_return_null=1"; }

namespace {

using spvbind_fuzz::oracleLocations;
using spvbind_fuzz::oracleRejected;
using spvbind_fuzz::reflectLocations;

std::vector<std::string> sortedLines(const std::string& text) {
    std::vector<std::string> lines;
    std::istringstream in(text);
    for (std::string line; std::getline(in, line);)
        if (!line.empty()) lines.push_back(line);
    std::sort(lines.begin(), lines.end());
    return lines;
}

std::string join(const std::vector<std::string>& lines) {
    std::string out;
    for (const auto& l : lines) out += "  " + l + '\n';
    return out;
}

// FNV-1a, to name findings.
std::string digest(const std::string& data) {
    uint64_t h = 1469598103934665603ull;
    for (unsigned char c : data) h = (h ^ c) * 1099511628211ull;
    char buffer[17];
    std::snprintf(buffer, sizeof buffer, "%016llx", (unsigned long long)h);
    return buffer;
}

void saveFinding(const std::string& module, const std::string& oracle, const std::string& reflect,
                 const char* kind = "mismatch") {
    const char* env = std::getenv("SPVBIND_FUZZ_FINDINGS");
    std::filesystem::path dir = env ? env : SPVBIND_FUZZ_FINDINGS_DEFAULT;
    dir /= "fuzztest";
    std::error_code ec;
    std::filesystem::create_directories(dir, ec);
    std::string name = std::string(kind) + '-' + digest(module);
    std::ofstream(dir / (name + ".spv"), std::ios::binary) << module;
    std::ofstream(dir / (name + ".spvbind.txt")) << oracle;
    std::ofstream(dir / (name + ".reflect.txt")) << reflect;
    std::fprintf(stderr, "finding saved as %s\n", (dir / (name + ".spv")).c_str());
}

/// The property, for a module given as bytes. SPIRV-Reflect rejecting a module spvbind accepts is a failure if
/// `rejectionFails`; the bytes target only records it, because it mostly happens on invalid SPIR-V (a decoration of an
/// undefined id, a member index past the end), which spvbind ignores and which only spirv-val can tell apart here, and
/// FuzzTest ends at the first failure.
void check(const std::string& module, bool rejectionFails) {
    // A crash leaves no time to save the module; with SPVBIND_FUZZ_DUMP=<file>, replaying FuzzTest's reproducer writes
    // it as a .spv before SPIRV-Reflect sees it.
    if (const char* dump = std::getenv("SPVBIND_FUZZ_DUMP")) std::ofstream(dump, std::ios::binary) << module;
    std::string oracle = oracleLocations(module.data(), module.size());
    auto r = reflectLocations(module.data(), module.size());  // always: a crash here is a finding by itself
    if (oracleRejected(oracle)) return;                       // the oracle is silent
    if (!r.ok) {
        saveFinding(module, oracle, r.text, "rejected");
        if (rejectionFails) FAIL() << "spvbind accepted the module, SPIRV-Reflect rejected it: " << r.text;
        return;
    }
    auto expected = sortedLines(oracle);
    auto actual = sortedLines(r.text);
    if (r.inconsistent || expected != actual) {
        saveFinding(module, oracle, r.text);
        if (r.inconsistent) ADD_FAILURE() << "SPIRV-Reflect contradicts itself:\n" << r.text;
        EXPECT_EQ(expected, actual) << "spvbind:\n" << join(expected) << "SPIRV-Reflect:\n" << join(actual);
    }
}

// --- Arbitrary bytes, seeded with real modules -------------------------------------------------------------------

std::vector<std::tuple<std::string>> seeds() { return fuzztest::ReadFilesFromDirectory(SPVBIND_FUZZ_SEEDS); }

void OracleAgreesOnBytes(const std::string& module) { check(module, /*rejectionFails=*/false); }
FUZZ_TEST(Differential, OracleAgreesOnBytes).WithDomains(fuzztest::Arbitrary<std::string>()).WithSeeds(seeds);

// --- Random interfaces, written as SPIR-V word by word ---------------------------------------------------------------
//
// A structured domain: the fuzzer mutates the interface, not the bytes, so every input is a well-formed module and
// most are valid SPIR-V that spvbind accepts; coverage then guides it to the layouts that matter.

struct Member {
    uint8_t kind;  // < 10: a scalar (kScalars); otherwise an earlier struct, by (kind - 10) % their number
    uint8_t gap;   // extra alignments of padding before the member
};
struct StructDesc {
    std::vector<Member> members;
};
struct Interface {
    std::vector<StructDesc> structs;  // in dependency order; the last is the push constant block
    uint8_t flags;                    // kFlag*
    uint16_t salt;                    // chooses ids and the order of names and decorations
};

enum : uint8_t {
    kFlagScalarLayout = 1,    // structs end with their last member, as in the scalar block layout
    kFlagAnonymous = 2,       // the variable has an empty name, as glslc gives anonymous blocks
    kFlagNoBlock = 4,         // no Block decoration (invalid for Vulkan; spvbind does not care)
    kFlagSecondVariable = 8,  // a second push constant variable of the same type
    kFlagDecoy = 16,          // a storage buffer variable of the same struct
    kFlagShuffle = 32,        // names and decorations in an order glslc never produces
    kFlagSwapOffsets = 64,    // the block's first two members have their offsets swapped (valid; spvbind rejects)
};

struct ScalarKind {
    char kind;
    uint32_t width;
};
constexpr ScalarKind kScalars[10] = {{'f', 32}, {'f', 64}, {'i', 32}, {'u', 32}, {'i', 8}, {'u', 8}, {'i', 16}, {'u', 16},
                                     {'i', 64}, {'u', 64}};

constexpr uint32_t kMagic = 0x07230203;
enum Op : uint32_t {
    OpName = 5, OpMemberName = 6, OpMemoryModel = 14, OpEntryPoint = 15, OpExecutionMode = 16, OpCapability = 17,
    OpTypeVoid = 19, OpTypeInt = 21, OpTypeFloat = 22, OpTypeStruct = 30, OpTypePointer = 32, OpTypeFunction = 33,
    OpFunction = 54, OpFunctionEnd = 56, OpVariable = 59, OpDecorate = 71, OpMemberDecorate = 72, OpLabel = 248,
    OpReturn = 253,
};
enum Capability : uint32_t {
    CapShader = 1, CapFloat64 = 10, CapInt64 = 11, CapInt16 = 22, CapInt8 = 39, CapStoragePushConstant16 = 4435,
    CapStoragePushConstant8 = 4450,
};
constexpr uint32_t kDecorationBlock = 2, kDecorationOffset = 35, kPushConstant = 9, kStorageBuffer = 12;

using Words = std::vector<uint32_t>;

Words op(uint32_t opcode, std::initializer_list<uint32_t> operands) {
    Words w{((uint32_t)(operands.size() + 1) << 16) | opcode};
    w.insert(w.end(), operands.begin(), operands.end());
    return w;
}
void append(Words& to, const Words& from) { to.insert(to.end(), from.begin(), from.end()); }
Words literal(const std::string& s) {
    std::string bytes = s + '\0';
    while (bytes.size() % 4) bytes += '\0';
    Words w;
    for (size_t i = 0; i < bytes.size(); i += 4)
        w.push_back((uint8_t)bytes[i] | (uint8_t)bytes[i + 1] << 8 | (uint8_t)bytes[i + 2] << 16 | (uint8_t)bytes[i + 3] << 24);
    return w;
}
uint32_t alignUp(uint32_t n, uint32_t a) { return (n + a - 1) / a * a; }

struct Lcg {
    uint32_t state;
    uint32_t next() { return state = state * 1664525u + 1013904223u; }
};

std::string encode(const Interface& interface) {
    const bool scalarLayout = interface.flags & kFlagScalarLayout;
    Lcg rng{interface.salt * 2654435761u + 1};

    // Ids: a permutation of 1..n, so that definition order and numbering are unrelated.
    uint32_t nextId = 1;
    std::vector<uint32_t> ids;
    auto fresh = [&] { ids.push_back(nextId); return nextId++; };
    const size_t nStructs = interface.structs.size();
    std::vector<uint32_t> scalarIds(10, 0);
    std::vector<uint32_t> structIds(nStructs);
    for (auto& s : structIds) s = fresh();
    uint32_t pointer = fresh(), variable = fresh(), main = fresh(), voidType = fresh(), fnType = fresh(), label = fresh();
    uint32_t other = fresh(), decoyPointer = fresh(), decoyVariable = fresh();
    // Resolve member kinds and collect the scalars used.
    struct Resolved { bool isStruct; uint32_t index; };
    std::vector<std::vector<Resolved>> resolved(nStructs);
    for (size_t i = 0; i < nStructs; ++i)
        for (const Member& m : interface.structs[i].members) {
            if (m.kind >= 10 && i > 0) resolved[i].push_back({true, (uint32_t)((m.kind - 10) % i)});
            else {
                uint32_t k = m.kind % 10;
                resolved[i].push_back({false, k});
                if (!scalarIds[k]) scalarIds[k] = fresh();
            }
        }
    for (uint32_t i = 1; i < nextId; ++i) std::swap(ids[i - 1], ids[rng.next() % i]);  // shuffle 1..n
    auto id = [&](uint32_t sequential) { return ids[sequential - 1]; };

    Words capabilities{CapShader};
    Words types, debug, annotations;
    std::vector<Words> debugList, annotationList;
    for (uint32_t k = 0; k < 10; ++k) {
        if (!scalarIds[k]) continue;
        const ScalarKind& s = kScalars[k];
        if (s.kind == 'f') {
            append(types, op(OpTypeFloat, {id(scalarIds[k]), s.width}));
            if (s.width == 64) capabilities.push_back(CapFloat64);
        } else {
            append(types, op(OpTypeInt, {id(scalarIds[k]), s.width, s.kind == 'i' ? 1u : 0u}));
            if (s.width == 64) capabilities.push_back(CapInt64);
            if (s.width == 16) capabilities.push_back(CapInt16);
            if (s.width == 8) capabilities.push_back(CapInt8);
        }
        if (s.width == 8) capabilities.push_back(CapStoragePushConstant8);
        if (s.width == 16) capabilities.push_back(CapStoragePushConstant16);
    }
    std::vector<std::pair<uint32_t, uint32_t>> placed(nStructs);  // (alignment, size) of each struct as laid out
    for (size_t i = 0; i < nStructs; ++i) {
        const bool isBlock = i + 1 == nStructs;
        Words structOp{0, id(structIds[i])};
        uint32_t cursor = 0, align = 1;
        std::vector<uint32_t> offsets;
        for (size_t j = 0; j < resolved[i].size(); ++j) {
            const Resolved& m = resolved[i][j];
            uint32_t a, size;
            if (m.isStruct) { a = placed[m.index].first; size = placed[m.index].second; structOp.push_back(id(structIds[m.index])); }
            else { a = size = kScalars[m.index].width / 8; structOp.push_back(id(scalarIds[m.index])); }
            uint32_t offset = alignUp(cursor, a) + a * interface.structs[i].members[j].gap;
            offsets.push_back(offset);
            cursor = offset + size;
            align = std::max(align, a);
        }
        placed[i] = {align, scalarLayout ? cursor : alignUp(cursor, align)};
        structOp[0] = ((uint32_t)structOp.size() << 16) | OpTypeStruct;
        append(types, structOp);
        std::string name = isBlock ? "Params" : "S" + std::to_string(i);
        debugList.push_back(op(OpName, {id(structIds[i])}));
        append(debugList.back(), literal(name));
        debugList.back()[0] = ((uint32_t)debugList.back().size() << 16) | OpName;
        if (isBlock && (interface.flags & kFlagSwapOffsets) && offsets.size() >= 2) std::swap(offsets[0], offsets[1]);
        for (size_t j = 0; j < offsets.size(); ++j) {
            Words n = op(OpMemberName, {id(structIds[i]), (uint32_t)j});
            append(n, literal("m" + std::to_string(j)));
            n[0] = ((uint32_t)n.size() << 16) | OpMemberName;
            debugList.push_back(n);
            annotationList.push_back(op(OpMemberDecorate, {id(structIds[i]), (uint32_t)j, kDecorationOffset, offsets[j]}));
        }
    }
    const uint32_t block = id(structIds[nStructs - 1]);
    if (!(interface.flags & kFlagNoBlock)) annotationList.push_back(op(OpDecorate, {block, kDecorationBlock}));
    append(types, op(OpTypePointer, {id(pointer), kPushConstant, block}));
    Words variables = op(OpVariable, {id(pointer), id(variable), kPushConstant});
    {
        Words n = op(OpName, {id(variable)});
        append(n, literal(interface.flags & kFlagAnonymous ? "" : "pc"));
        n[0] = ((uint32_t)n.size() << 16) | OpName;
        debugList.push_back(n);
    }
    if (interface.flags & kFlagSecondVariable) append(variables, op(OpVariable, {id(pointer), id(other), kPushConstant}));
    if (interface.flags & kFlagDecoy) {
        append(types, op(OpTypePointer, {id(decoyPointer), kStorageBuffer, block}));
        append(variables, op(OpVariable, {id(decoyPointer), id(decoyVariable), kStorageBuffer}));
    }
    if (interface.flags & kFlagShuffle) {
        for (size_t i = debugList.size(); i > 1; --i) std::swap(debugList[i - 1], debugList[rng.next() % i]);
        for (size_t i = annotationList.size(); i > 1; --i) std::swap(annotationList[i - 1], annotationList[rng.next() % i]);
    }
    for (const auto& d : debugList) append(debug, d);
    for (const auto& a : annotationList) append(annotations, a);

    Words words{kMagic, 0x00010600, 0, nextId, 0};
    std::sort(capabilities.begin(), capabilities.end());
    capabilities.erase(std::unique(capabilities.begin(), capabilities.end()), capabilities.end());
    for (uint32_t c : capabilities) append(words, op(OpCapability, {c}));
    append(words, op(OpMemoryModel, {0, 1}));
    {
        Words e = op(OpEntryPoint, {5, id(main)});
        append(e, literal("main"));
        e.push_back(id(variable));
        e[0] = ((uint32_t)e.size() << 16) | OpEntryPoint;
        append(words, e);
    }
    append(words, op(OpExecutionMode, {id(main), 17, 1, 1, 1}));
    {
        Words n = op(OpName, {id(main)});
        append(n, literal("main"));
        n[0] = ((uint32_t)n.size() << 16) | OpName;
        append(words, n);
    }
    append(words, debug);
    append(words, annotations);
    append(words, op(OpTypeVoid, {id(voidType)}));
    append(words, op(OpTypeFunction, {id(fnType), id(voidType)}));
    append(words, types);
    append(words, variables);
    append(words, op(OpFunction, {id(voidType), id(main), 0, id(fnType)}));
    append(words, op(OpLabel, {id(label)}));
    append(words, op(OpReturn, {}));
    append(words, op(OpFunctionEnd, {}));

    std::string bytes(words.size() * 4, '\0');
    for (size_t i = 0; i < words.size(); ++i)
        for (int b = 0; b < 4; ++b) bytes[4 * i + b] = (char)(words[i] >> (8 * b));
    return bytes;
}

auto InterfaceDomain() {
    using namespace fuzztest;
    auto member = StructOf<Member>(Arbitrary<uint8_t>(), InRange<uint8_t>(0, 8));
    auto structDesc = StructOf<StructDesc>(VectorOf(member).WithMinSize(1).WithMaxSize(8));
    return StructOf<Interface>(VectorOf(structDesc).WithMinSize(1).WithMaxSize(6), Arbitrary<uint8_t>(),
                               Arbitrary<uint16_t>());
}

void OracleAgreesOnInterfaces(const Interface& interface) { check(encode(interface), /*rejectionFails=*/true); }
FUZZ_TEST(Differential, OracleAgreesOnInterfaces).WithDomains(InterfaceDomain());

// The encoder itself: with the plain flags, every interface is a module spvbind accepts.
void PlainInterfacesAreAccepted(const Interface& interface) {
    Interface plain = interface;
    plain.flags &= (uint8_t)(kFlagAnonymous | kFlagSecondVariable | kFlagDecoy | kFlagShuffle);
    std::string module = encode(plain);
    std::string oracle = oracleLocations(module.data(), module.size());
    EXPECT_FALSE(oracleRejected(oracle)) << oracle;
}
FUZZ_TEST(Encoder, PlainInterfacesAreAccepted).WithDomains(InterfaceDomain());

TEST(Oracle, AgreesWithTheExample) {
    std::ifstream file(std::string(SPVBIND_FUZZ_SEEDS) + "/params.spv", std::ios::binary);
    ASSERT_TRUE(file.good()) << "no params.spv among the seeds";
    std::string module((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());
    std::string oracle = oracleLocations(module.data(), module.size());
    ASSERT_FALSE(oracleRejected(oracle)) << oracle;
    EXPECT_NE(oracle.find("Params/Range\t2/1\trange/hi\t20\tf32"), std::string::npos) << oracle;
    check(module, /*rejectionFails=*/true);
}

}  // namespace
