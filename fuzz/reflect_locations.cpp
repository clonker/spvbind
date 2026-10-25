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
    std::vector<const char*> structs, members;
    std::vector<unsigned> indices;
};

const char* orEmpty(const char* s) { return s ? s : ""; }

void appendPath(std::string& out, const Path& path, uint32_t var) {
    out += std::to_string(var) + '\t';
    for (size_t i = 0; i < path.structs.size(); ++i) out += (i ? "/" : "") + std::string(orEmpty(path.structs[i]));
    out += '\t';
    for (size_t i = 0; i < path.indices.size(); ++i) out += (i ? "/" : "") + std::to_string(path.indices[i]);
    out += '\t';
    for (size_t i = 0; i < path.members.size(); ++i) out += (i ? "/" : "") + std::string(orEmpty(path.members[i]));
    out += '\t';
}

void dump(Reflection& r, uint32_t var, const SpvReflectBlockVariable& parent, Path& path) {
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
        path.members.push_back(member.name);

        // The root block's own absolute offset is not meaningful (SPIRV-Reflect sets its `offset` to the lowest member
        // offset), so only nested members are checked for consistency.
        if (path.structs.size() > 1 && member.absolute_offset != parent.absolute_offset + member.offset) {
            appendPath(r.text, path, var);
            r.text += "!offset absolute " + std::to_string(member.absolute_offset) + " != parent " +
                std::to_string(parent.absolute_offset) + " + relative " + std::to_string(member.offset) + '\n';
            r.inconsistent = true;
        }

        SpvReflectTypeFlags flags = memberType ? memberType->type_flags : SPV_REFLECT_TYPE_FLAG_UNDEFINED;
        // A struct member of a Block carries EXTERNAL_BLOCK too; every other external flag is an opaque type.
        SpvReflectTypeFlags composite = SPV_REFLECT_TYPE_FLAG_VECTOR | SPV_REFLECT_TYPE_FLAG_MATRIX |
            SPV_REFLECT_TYPE_FLAG_ARRAY | SPV_REFLECT_TYPE_FLAG_REF |
            (SPV_REFLECT_TYPE_FLAG_EXTERNAL_MASK & ~SPV_REFLECT_TYPE_FLAG_EXTERNAL_BLOCK);
        if ((flags & SPV_REFLECT_TYPE_FLAG_STRUCT) && !(flags & composite)) {
            dump(r, var, member, path);
        } else if ((flags & (SPV_REFLECT_TYPE_FLAG_INT | SPV_REFLECT_TYPE_FLAG_FLOAT)) &&
                   !(flags & (composite | SPV_REFLECT_TYPE_FLAG_STRUCT | SPV_REFLECT_TYPE_FLAG_BOOL))) {
            appendPath(r.text, path, var);
            char kind = (flags & SPV_REFLECT_TYPE_FLAG_FLOAT) ? 'f' : (member.numeric.scalar.signedness ? 'i' : 'u');
            r.text += std::to_string(member.absolute_offset) + '\t' + kind + std::to_string(member.numeric.scalar.width) + '\n';
        } else {
            char buffer[64];
            std::snprintf(buffer, sizeof buffer, "%u\tunsupported flags=0x%08x\n", member.absolute_offset, (unsigned)flags);
            appendPath(r.text, path, var);
            r.text += buffer;
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
        dump(r, block.spirv_id, block, path);
    }
    spvReflectDestroyShaderModule(&module);
    r.ok = true;
    return r;
}

}  // namespace spvbind_fuzz
