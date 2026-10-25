# Differential fuzzing with spvbind as the oracle

`Guarantees.generate_correct` says that what spvbind prints for a module is exactly what the module's decorations say,
for every scalar of every push constant block. That makes spvbind an oracle for other reflection libraries: generate a
module, ask both where every scalar is, and compare. The subject here is [SPIRV-Reflect](https://github.com/KhronosGroup/SPIRV-Reflect).

## The format

`spvbind --locations module.spv` prints one line per scalar, tab-separated: the variable's id; the struct names, member
indices and member names along the path, each joined with `/`, a vector component as `[k]` after its member's name; the
byte offset from the start of the block; the scalar as `i`, `u` or `f` and its width.

```
22	Params	0	count	0	u32
22	Params	1	scale	8	f64
22	Params/Range	2/0	range/lo	16	f32
22	Params/Range	2/1	range/hi	20	f32
```

`reflect_locations.cpp` (and `reflect_dump`, its command line) prints the same from SPIRV-Reflect's `SpvReflectBlockVariable`s (`absolute_offset`, `numeric.scalar`,
`type_description->type_name`). A member that is not a scalar or a struct prints as `unsupported`, so that a module
spvbind accepts never agrees by accident. Any other library can be a subject by printing this format.

## Running

Two ways to run it: `differential.py`, a black-box driver that generates modules in Python and runs both tools as
processes, which needs only a C++ compiler for `reflect_dump` (Clang for the sanitizers); and `spvbind_fuzz`,
coverage-guided with FuzzTest, below.

```sh
lake build                                                             # the oracle
cmake -S fuzz -B fuzz/build -DSPVBIND_FUZZ_SANITIZE=ON -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
cmake --build fuzz/build                                               # reflect_dump, fetching SPIRV-Reflect main
fuzz/differential.py -n 5000                                           # glsl, spirv and mutate modes, alternating
fuzz/differential.py --mode spirv --exotic 0.3 -n 20000 --seed 7       # reproducible
```

`-DSPIRV_REFLECT_SOURCE_DIR=path` uses a checkout instead of fetching, `-DSPIRV_REFLECT_GIT_TAG=` pins a revision.
Needs `glslc` for the glsl mode, and `spirv-val` and `spirv-dis` to classify and disassemble findings (both from
SPIRV-Tools; skipped if absent).

## Coverage-guided, with FuzzTest

`spvbind_fuzz` links SPIRV-Reflect and spvbind's compiled Lean code (`Spvbind/Oracle.lean` exports
`spvbind_locations` to C; `oracle.cpp` runs Lean's runtime) into one [FuzzTest](https://github.com/google/fuzztest)
binary. In fuzzing mode both are built with coverage instrumentation and AddressSanitizer, so the fuzzer is guided by
the paths a module takes through either of them, and a crash of SPIRV-Reflect is a sanitizer report.

```sh
lake build                                   # the Lean code, compiled to C under .lake/build/ir
CC=clang CXX=clang++ cmake -S fuzz -B fuzz/build-fuzztest -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DSPVBIND_FUZZTEST=ON -DFUZZTEST_FUZZING_MODE=ON      # fetches FuzzTest, Abseil, RE2, GoogleTest; takes a while
cmake --build fuzz/build-fuzztest --target spvbind_fuzz
fuzz/build-fuzztest/spvbind_fuzz                           # unit-test mode: every test for a second
export FUZZTEST_REPRODUCERS_OUT_DIR=fuzz/findings/fuzztest
fuzz/build-fuzztest/spvbind_fuzz --fuzz=Differential.OracleAgreesOnInterfaces --fuzz_for=10m
fuzz/build-fuzztest/spvbind_fuzz --fuzz=Differential.OracleAgreesOnBytes --fuzz_for=10m --corpus_database=fuzz/corpus
```

Two fuzz tests, in `differential_fuzz.cpp`:

- **`Differential.OracleAgreesOnInterfaces`**: a structured domain, an `Interface` of structs whose members are scalars
  or earlier structs with padding gaps, plus flags for the scalar block layout, anonymous blocks, a missing `Block`
  decoration, a second variable, a decoy storage buffer, shuffled names and decorations, and swapped offsets. The
  fuzzer mutates the interface, not the bytes, so every input is a well-formed module and most are valid SPIR-V that
  spvbind accepts; coverage then steers it towards new layouts. About 2,500 modules/s.
- **`Differential.OracleAgreesOnBytes`**: arbitrary bytes, seeded with `examples/params.spv` and the compiled
  `tests/accepted` cases. This is where the malformed modules come from, and where SPIRV-Reflect crashes: FuzzTest
  stops at the first failure, so without `-DSPVBIND_FUZZ_PATCH_SPIRV_REFLECT=ON`, which applies
  `patches/spirv-reflect-known-crashes.patch` (null checks in the cleanup after a failed parse and in
  `OpSourceContinued`, a depth limit in `ParseType`, member indices checked against the struct) to the fetched
  SPIRV-Reflect, this target finds one of the known segfaults within a second and ends; with it, the next unpatched
  finding (see `reproducers/`) ends the run after about half a minute. `--time_limit_per_input=10s` turns a hang into
  a finding too. Here SPIRV-Reflect rejecting a module spvbind accepts is not a failure but is
  recorded as `rejected-<hash>.spv`: on arbitrary bytes it almost always means invalid SPIR-V that spvbind ignores (a
  decoration of an undefined id, a member index past the end), which only spirv-val can tell apart, and `differential.py`
  does that. About 1,800 modules/s.

`Encoder.PlainInterfacesAreAccepted` checks the structured domain's encoder: without the exotic flags, spvbind accepts
every interface. `Oracle.AgreesWithTheExample` checks the oracle on `params.spv`.

A failing input is written to `fuzz/findings/fuzztest/` (or `SPVBIND_FUZZ_FINDINGS`) as `mismatch-<hash>.spv` with
both outputs, besides FuzzTest's reproducer in `FUZZTEST_REPRODUCERS_OUT_DIR`. A crash leaves no time for that, so a
reproducer is replayed with the module dumped first:

```sh
SPVBIND_FUZZ_DUMP=crash.spv FUZZTEST_REPLAY=<reproducer> fuzz/build-fuzztest/spvbind_fuzz --gtest_filter=Differential.OracleAgreesOnBytes
spirv-val --target-env vulkan1.3 crash.spv; fuzz/build-fuzztest/reflect_dump crash.spv   # the sanitizer report with lines
```

`--corpus_database=<dir>` keeps the corpus between runs; `--jobs=N` runs N processes; `--stack_limit_kb` and
`--rss_limit_mb` bound the code under test. The binary sets `detect_leaks=0` (Lean's runtime never frees its persistent
objects) and `allocator_may_return_null=1` (see `reproducers/README.md`) for AddressSanitizer. FuzzTest's own flags are
in its documentation.

For the whole chain in one process, the Lean side is `oracle.cpp` and the C that Lake wrote to `.lake/build/ir`;
`lake build` must have run, and the Lean toolchain's `libleanshared.so` is linked by path.

## Properties and findings

| Kind                   | Meaning                                                                                      |
|------------------------|----------------------------------------------------------------------------------------------|
| `mismatch`             | spvbind and the subject accept the module and disagree on a scalar                           |
| `reflect-rejects`      | spvbind accepts, the subject rejects                                                         |
| `reflect-crash`        | the subject crashed, timed out, or a sanitizer reported (built with `SPVBIND_FUZZ_SANITIZE`) |
| `reflect-inconsistent` | the subject's absolute offsets are not its relative offsets summed                           |
| `spvbind-crash`        | spvbind exited with anything but 0 or 1: a totality bug                                      |

Each finding is saved once under `findings/<kind>/<valid|invalid>/<hash>/` with the module, its disassembly, the GLSL
if there was one, both outputs, spirv-val's verdict and a `README.txt` with the diff and how the module was made.
`valid` findings are the interesting ones: a disagreement on valid SPIR-V is a bug in the subject, or a gap in
spvbind's `Spec` (which review of `Spec` is for). `invalid` ones are robustness: crashes matter, rejections usually do
not.

When spvbind rejects a module the oracle is silent; the summary tallies why, so that the generators can be aimed at what
spvbind accepts. spvbind rejects more than SPIRV-Reflect does: every member needs an Offset and a name, members must be
in offset order and aligned for C++, and only scalars and structs are supported.

## Generators

- **glsl**: a random push constant interface (nested structs, every supported scalar and vectors of them, explicit
  offsets with gaps, occasionally a name that spvbind must reject) as GLSL, compiled with `glslc --target-env=vulkan1.3`.
  The realistic input; about 15 modules/s, bounded by glslc.
- **spirv**: the same interfaces written word by word, with what glslc never produces: random ids, shuffled names and
  decorations, gaps inside nested structs, the scalar block layout; and with probability `--exotic` each of: huge
  offsets, offsets out of member order, no `Block`, a nameless struct or member, a member without an Offset or with two,
  member names and decorations past the last member, a second push constant variable, a storage buffer of the same
  struct, an unused struct of the same name, a vector in an unused struct, a decoration of an undefined id. These are
  listed in each finding.
- **mutate**: a module that both tools agreed on (or one from `--corpus`), with one to three changes aimed at the
  instructions spvbind reads: an Offset moved, an operand replaced, a bit flipped, an instruction deleted or
  duplicated, a word count or opcode changed, the module truncated, a header word changed.

## Findings so far

The first 4000 modules (seed 42, all three modes, SPIRV-Reflect `563dc9a`): spvbind accepted 2150, SPIRV-Reflect
agreed on all of them but three, all valid SPIR-V with one wrong result (nested absolute offsets wrap at 2^32); and
97 malformed modules made SPIRV-Reflect segfault, in three ways (a struct that contains itself, and two null-pointer
frees in the cleanup after a failed parse). One module of each is kept in [`reproducers/`](reproducers/README.md), which is also the default
corpus of the mutate mode.

The FuzzTest bytes target then found, each within a minute once the previous one was patched: a fourth segfault
(`OpSourceContinued` without an `OpSource`), the unbounded allocation from a member index known from the earlier C++
fuzzing, a hang quadratic in that member index, and a heap buffer overflow writing past the array of functions; all in
`reproducers/`, all on invalid SPIR-V. It also found something about spvbind: its decoders recursed once per word, which
under AddressSanitizer exceeded FuzzTest's 128 KiB stack limit on a 3 KB module. They now run iteratively, through
`@[csimp]` twins that Lean checks against the originals (`Spvbind/Binary.lean`). The structured target ran 450,000
modules in five minutes without a disagreement.
