# spvbind

Typed C++ interfaces for Vulkan shaders generated from SPIR-V.

## Example

The push constant block of [`examples/params.comp`](examples/params.comp):

```glsl
struct Range
{
    float lo;
    float hi;
};

layout(push_constant) uniform Params
{
    uint count;
    double scale;
    Range range;
};
```

```sh
glslc --target-env=vulkan1.3 -o params.spv params.comp
spvbind params.spv > params.hpp
```

becomes, in [`examples/params.hpp`](examples/params.hpp):

```cpp
struct Params
{
    std::uint32_t count;
    std::array<std::byte, 4> spvbindPadding0{};
    double scale;
    Range range;
};
static_assert(offsetof(Params, count) == 0);
static_assert(offsetof(Params, scale) == 8);
static_assert(offsetof(Params, range) == 16);
static_assert(std::is_integral_v<decltype(Params::count)> && std::is_unsigned_v<decltype(Params::count)> && sizeof(decltype(Params::count)) == 4);
static_assert(std::is_floating_point_v<decltype(Params::scale)> && std::numeric_limits<decltype(Params::scale)>::is_iec559 && sizeof(decltype(Params::scale)) == 8);
static_assert(sizeof(Params) == 24);
static_assert(alignof(Params) == 8);
```

and likewise `Range`. `Guarantees.generate_correct` proves that the generator emits one C++ type for each push
constant variable of the module and for no other variable, and that, in spvbind's model of C++ layout, every scalar of
each sits at the offset the shader's `Offset` decorations give it; the `static_assert`s make the C++ compiler check
every offset, scalar type, size and alignment of that model. Padding is explicit. A struct filled from C++ can be
pushed as is:

```cpp
Params params{.count = n, .scale = 2.0, .range = {.lo = 0.0f, .hi = 1.0f}};
vkCmdPushConstants(commandBuffer, layout, VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(params), &params);
```

## Layout

| Library   | Contents                                                                        | Imports               |
|-----------|---------------------------------------------------------------------------------|-----------------------|
| `Spec`    | Definitions transcribed from the specifications, close to their text; no proofs | Nothing               |
| `Spvbind` | The implementation; the `spvbind` executable is `Main.lean`                     | `Spec`, for its types |
| `Proofs`  | Theorems relating `Spvbind` to `Spec`                                           | Both                  |

`Guarantees.lean` restates the theorems that matter, proven in `Proofs`, and the build fails if they depend on
anything but Lean's standard axioms.
Crucial is the `Spec` directory, and the few parts outside the theorems:
- the printer (`Spvbind/Print.lean`),
- the axiom check (`Guarantees/Axioms.lean`),
- and `Main.lean`.

## Specifications

| Specification                                                                             | Version         | Used in                                                         |
|-------------------------------------------------------------------------------------------|-----------------|-----------------------------------------------------------------|
| [SPIR-V](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html)                   | 1.6, revision 8 | `Spec/Binary.lean`, `Spec/Instruction.lean`, `Spec/Layout.lean` |
| [Vulkan](https://docs.vulkan.org/spec/latest/chapters/interfaces.html), Shader Interfaces | latest          | `Spec/Layout.lean`                                              |

`Spec/Cpp.lean` is not a specification but a model of C++ layout.

## Building

Requires [elan](https://github.com/leanprover/elan); the Lean version is pinned in `lean-toolchain`.

```sh
lake build                                        # the executable and all proofs
.lake/build/bin/spvbind shader.spv > shader.hpp   # the push constant blocks, as C++ structs
.lake/build/bin/spvbind --locations shader.spv    # every scalar with its path, offset and type, for comparing
```

The module must be compiled without optimization (`glslc` without `-O`), which would remove the names, and be SPIR-V
1.4 or later (`--target-env=vulkan1.2` or later). For now only push constant blocks of integers, floats, vectors,
arrays whose stride is their element's size, matrices whose MatrixStride is a column's (or, row-major, a row's) size
(all as `std::array`, indexed in memory order) and nested structs are supported, with members in offset order; anything
else, a `vec3[N]` or `mat3` with their padded strides for one, is rejected with a message naming the member.

## Tests

Proofs show that the generator matches `Spec`; tests cover what they do not, and need `glslc`, `spirv-as` and a C++
compiler:

```sh
tests/run.py                              # headers and locations of GLSL cases, rejections, raw bytes, big-endian
tests/grammar.py spirv.core.grammar.json  # Spec/Instruction.lean against SPIRV-Headers' grammar
```

## spvbind as an oracle

`--locations` prints exactly what `generate_correct` is about, so another reflection library can be fuzzed against it:
generate a module, ask both where every scalar of every push constant block is, and compare. `fuzz/` does this for
[SPIRV-Reflect](https://github.com/KhronosGroup/SPIRV-Reflect) in two ways: a Python driver with random GLSL, random
SPIR-V written word by word and mutations, and a coverage-guided [FuzzTest](https://github.com/google/fuzztest) binary
that links spvbind's compiled Lean code and SPIRV-Reflect into one instrumented process; see
[`fuzz/README.md`](fuzz/README.md).
