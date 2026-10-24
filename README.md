# spvbind

Typed C++ interfaces for Vulkan shaders generated from SPIR-V.

## Layout

| Library   | Contents                                                                        | Imports               |
|-----------|---------------------------------------------------------------------------------|-----------------------|
| `Spec`    | Definitions transcribed from the specifications, close to their text; no proofs | Nothing               |
| `Spvbind` | The implementation; the `spvbind` executable is `Main.lean`                     | `Spec`, for its types |
| `Proofs`  | Theorems relating `Spvbind` to `Spec`                                           | Both                  |

## Specifications

| Specification                                                           | Version         | Used in            |
|-------------------------------------------------------------------------|-----------------|--------------------|
| [SPIR-V](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html) | 1.6, revision 8 | `Spec/Binary.lean` |

## Building

Requires [elan](https://github.com/leanprover/elan); the Lean version is pinned in `lean-toolchain`.

```sh
lake build                            # the executable and all proofs
.lake/build/bin/spvbind shader.spv
```
