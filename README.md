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
static_assert(sizeof(Params) == 24);
static_assert(alignof(Params) == 8);
```

and likewise `Range`. `Guarantees.generate_correct` proves that the generator emits one C++ type for each push
constant variable of the module and for no other variable, and that, in spvbind's model of C++ layout, every scalar of
each sits at the offset the shader's `Offset` decorations give it; the `static_assert`s make the C++ compiler check
every offset, size and alignment of that model. Padding is explicit. A struct filled from C++ can be pushed as is:

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
- reading the file (`words`),
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
lake build                            # the executable and all proofs
.lake/build/bin/spvbind shader.spv > shader.hpp  # the push constant blocks, as C++ structs
```

The module must be compiled without optimization (`glslc` without `-O`), which would remove the names. For now only
push constant blocks of integers, floats and nested structs are supported.
