# spvbind

Typed C++ interfaces for Vulkan shaders generated from SPIR-V.

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
