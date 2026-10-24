# spvbind

Typed C++ interfaces for Vulkan shaders generated from SPIR-V.

## Layout

| Library   | Contents                                                                        | Imports               |
|-----------|---------------------------------------------------------------------------------|-----------------------|
| `Spec`    | Definitions transcribed from the specifications, close to their text; no proofs | Nothing               |
| `Spvbind` | The implementation; the `spvbind` executable is `Main.lean`                     | `Spec`, for its types |
| `Proofs`  | Theorems relating `Spvbind` to `Spec`                                           | Both                  |

Besides `Spec`, only `Guarantees.lean` needs review: it restates the theorems that matter, proven in `Proofs`, and
the build fails if they depend on anything but Lean's standard axioms (no `sorry`, `native_decide` or `bv_decide`).

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
