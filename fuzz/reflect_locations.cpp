#include "reflect_locations.hpp"

#include "spirv_reflect.h"

#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

namespace spvbind_fuzz {
namespace {

constexpr unsigned kMaxDepth = 64;

struct Path {
    std::vector<const char*> structs;
    std::vector<std::string> members;  // a member's name, with `[i]` for each element index taken inside it
    std::vector<unsigned> indices;
};

const char* orEmpty(const char* s) { return s ? s : ""; }

void appendPath(std::string& out, const Path& path, uint32_t var) {
    out += std::to_string(var) + '\t';
    for (size_t i = 0; i < path.structs.size(); ++i) out += (i ? "/" : "") + std::string(orEmpty(path.structs[i]));
    out += '\t';
    for (size_t i = 0; i < path.indices.size(); ++i) out += (i ? "/" : "") + std::to_string(path.indices[i]);
    out += '\t';
    for (size_t i = 0; i < path.members.size(); ++i) out += (i ? "/" : "") + path.members[i];
    out += '\t';
}

void dump(Reflection& r, uint32_t var, const SpvReflectBlockVariable& parent, Path& path, uint32_t base, bool inArray);

/// A value of `member`'s type without its array dimensions, at absolute byte `offset`: a scalar, a vector's components,
/// or a struct's members.
void dumpElement(Reflection& r, uint32_t var, const SpvReflectBlockVariable& member, SpvReflectTypeFlags flags,
                 Path& path, uint32_t offset, bool inArray) {
    // A struct member of a Block carries EXTERNAL_BLOCK too; every other external flag is an opaque type.
    constexpr SpvReflectTypeFlags composite = SPV_REFLECT_TYPE_FLAG_MATRIX | SPV_REFLECT_TYPE_FLAG_ARRAY |
        SPV_REFLECT_TYPE_FLAG_REF | (SPV_REFLECT_TYPE_FLAG_EXTERNAL_MASK & ~SPV_REFLECT_TYPE_FLAG_EXTERNAL_BLOCK);
    constexpr SpvReflectTypeFlags numeric = SPV_REFLECT_TYPE_FLAG_INT | SPV_REFLECT_TYPE_FLAG_FLOAT;
    constexpr SpvReflectTypeFlags notScalar = composite | SPV_REFLECT_TYPE_FLAG_STRUCT | SPV_REFLECT_TYPE_FLAG_BOOL |
        SPV_REFLECT_TYPE_FLAG_VECTOR;
    char kind = (flags & SPV_REFLECT_TYPE_FLAG_FLOAT) ? 'f' : (member.numeric.scalar.signedness ? 'i' : 'u');
    uint32_t width = member.numeric.scalar.width;
    if ((flags & SPV_REFLECT_TYPE_FLAG_STRUCT) && !(flags & (composite | SPV_REFLECT_TYPE_FLAG_VECTOR))) {
        dump(r, var, member, path, offset, inArray);
    } else if ((flags & numeric) && !(flags & notScalar)) {
        appendPath(r.text, path, var);
        r.text += std::to_string(offset) + '\t' + kind + std::to_string(width) + '\n';
    } else if ((flags & numeric) && (flags & SPV_REFLECT_TYPE_FLAG_VECTOR) &&
               !(flags & (notScalar & ~SPV_REFLECT_TYPE_FLAG_VECTOR))) {
        // A vector: one line per component, each the component's size further on.
        std::string name = path.members.back();
        for (uint32_t k = 0; k < member.numeric.vector.component_count; ++k) {
            path.members.back() = name + "[" + std::to_string(k) + "]";
            appendPath(r.text, path, var);
            r.text += std::to_string(offset + k * (width / 8)) + '\t' + kind + std::to_string(width) + '\n';
        }
        path.members.back() = name;
    } else {
        char buffer[64];
        std::snprintf(buffer, sizeof buffer, "%u\tunsupported flags=0x%08x\n", offset, (unsigned)flags);
        appendPath(r.text, path, var);
        r.text += buffer;
    }
}

/// The members of `parent`, a struct starting at absolute byte `base`. Offsets are summed from the relative ones here;
/// SPIRV-Reflect's own `absolute_offset` is compared with that, except inside an array of structs, where it leaves it
/// at 0 (`inArray`).
void dump(Reflection& r, uint32_t var, const SpvReflectBlockVariable& parent, Path& path, uint32_t base, bool inArray) {
    const SpvReflectTypeDescription* type = parent.type_description;
    const char* structName = type ? type->type_name : nullptr;
    if (path.structs.size() == kMaxDepth) {
        r.text += "!depth\t" + std::to_string(var) + "\tnesting deeper than " + std::to_string(kMaxDepth) + '\n';
        return;
    }
    for (uint32_t i = 0; i < parent.member_count; ++i) {
        const SpvReflectBlockVariable& member = parent.members[i];
        const SpvReflectTypeDescription* memberType = member.type_description;
        path.structs.push_back(structName);
        path.indices.push_back(i);
        path.members.push_back(orEmpty(member.name));
        uint32_t offset = base + member.offset;
        if (!inArray && member.absolute_offset != offset) {
            appendPath(r.text, path, var);
            r.text += "!offset absolute " + std::to_string(member.absolute_offset) + " != parent " +
                std::to_string(base) + " + relative " + std::to_string(member.offset) + '\n';
            r.inconsistent = true;
        }
        SpvReflectTypeFlags flags = memberType ? memberType->type_flags : SPV_REFLECT_TYPE_FLAG_UNDEFINED;
        if (flags & SPV_REFLECT_TYPE_FLAG_ARRAY) {
            // Element i at i times the stride. For an array of arrays SPIRV-Reflect keeps the dimensions, outermost
            // first, and one stride, the innermost's; what its users compute from that is the element at the row-major
            // index times that stride, which is the layout when every outer stride is its inner count of strides, as
            // in std430 and std140. An element's members' absolute offsets are not SPIRV-Reflect's to check.
            uint32_t total = member.array.dims_count ? 1 : 0;
            for (uint32_t d = 0; d < member.array.dims_count; ++d) total *= member.array.dims[d];
            std::string name = path.members.back();
            for (uint32_t linear = 0; linear < total; ++linear) {
                std::string suffix;
                for (uint32_t d = 0, rest = linear, span = total; d < member.array.dims_count; ++d) {
                    span /= member.array.dims[d];
                    suffix += "[" + std::to_string(rest / span) + "]";
                    rest %= span;
                }
                path.members.back() = name + suffix;
                dumpElement(r, var, member, flags & ~SPV_REFLECT_TYPE_FLAG_ARRAY, path,
                    offset + linear * member.array.stride, /*inArray=*/true);
            }
            path.members.back() = name;
        } else {
            dumpElement(r, var, member, flags, path, offset, inArray);
        }
        path.structs.pop_back();
        path.indices.pop_back();
        path.members.pop_back();
    }
}

}  // namespace

Reflection reflectLocations(const void* data, std::size_t size) {
    Reflection r;
    SpvReflectShaderModule module;
    SpvReflectResult result = spvReflectCreateShaderModule2(SPV_REFLECT_MODULE_FLAG_NO_COPY, size, data, &module);
    if (result != SPV_REFLECT_RESULT_SUCCESS) {
        r.text = "SPIRV-Reflect result " + std::to_string((int)result);
        return r;
    }
    uint32_t count = 0;
    result = spvReflectEnumeratePushConstantBlocks(&module, &count, nullptr);
    std::vector<SpvReflectBlockVariable*> blocks(count);
    if (result == SPV_REFLECT_RESULT_SUCCESS)
        result = spvReflectEnumeratePushConstantBlocks(&module, &count, blocks.data());
    if (result != SPV_REFLECT_RESULT_SUCCESS) {
        r.text = "SPIRV-Reflect result " + std::to_string((int)result) + " enumerating push constant blocks";
        spvReflectDestroyShaderModule(&module);
        return r;
    }
    for (uint32_t i = 0; i < count; ++i) {
        const SpvReflectBlockVariable& block = *blocks[i];
        const SpvReflectTypeDescription* type = block.type_description;
        if (!type || !(type->type_flags & SPV_REFLECT_TYPE_FLAG_STRUCT) || block.member_count == 0) {
            char buffer[96];
            std::snprintf(buffer, sizeof buffer, "%u\t\t\t\t0\tunsupported flags=0x%08x members=%u\n", block.spirv_id,
                (unsigned)(type ? type->type_flags : 0), block.member_count);
            r.text += buffer;
            continue;
        }
        Path path;
        dump(r, block.spirv_id, block, path, 0, false);
    }
    spvReflectDestroyShaderModule(&module);
    r.ok = true;
    return r;
}

}  // namespace spvbind_fuzz
