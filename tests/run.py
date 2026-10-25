#!/usr/bin/env python3
"""Tests of the spvbind executable: the parts no theorem covers.

- accepted/<name>.comp: GLSL compiled with glslc. The header must be accepted/<name>.hpp and the locations
  accepted/<name>.locations; the header must compile with every C++ compiler found; the module with its bytes swapped
  (big-endian) must give the same header.
- rejected/<name>.spvasm: SPIR-V assembly, assembled with spirv-as (the first lines may give `; target-env: <env>`).
  spvbind must exit with 1 and the message in rejected/<name>.err; if rejected/<name>.locations exists, `--locations`
  must succeed with that output instead of failing with the same message.
- Modules built here from raw words, which no assembler would produce: bad sizes, magic, schema, word counts, strings.
- The exit codes of usage errors.

`--update` rewrites the expected outputs from what spvbind prints; review the diff.
"""

from __future__ import annotations

import argparse
import pathlib
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent


def words(ws: list[int]) -> bytes:
    return struct.pack(f'<{len(ws)}I', *ws)


def inst(opcode: int, *operands: int) -> list[int]:
    return [((len(operands) + 1) << 16) | opcode, *operands]


HEADER = [0x07230203, 0x00010600, 0, 100, 0]
OP_NAME, OP_TYPE_INT = 5, 21

# Raw modules: name, bytes, the expected message.
RAW = [
    ('empty', b'', '0 words is shorter than the header'),
    ('three_bytes', b'\x03\x02\x23', 'size 3 is not a multiple of 4'),
    ('odd_size', words(HEADER) + b'\x01', 'size 21 is not a multiple of 4'),
    ('four_words', words(HEADER[:4]), '4 words is shorter than the header'),
    ('bad_magic', words([0x07230204] + HEADER[1:]), 'no SPIR-V magic number'),
    ('schema', words(HEADER[:4] + [1]), 'unknown schema 1'),
    ('word_count_0', words(HEADER + [0x00000005, 1]), 'instruction with opcode enumerant 5 has word count 0'),
    ('truncated', words(HEADER + [(3 << 16) | OP_NAME, 1]),
     'instruction with opcode enumerant 5 has word count 3, past the end of the module'),
    ('past_the_end', words(HEADER + [(9 << 16) | OP_NAME, 1, 0x61]),
     'instruction with opcode enumerant 5 has word count 9, past the end of the module'),
    ('duplicate_id', words(HEADER + inst(OP_TYPE_INT, 7, 32, 0) + inst(OP_TYPE_INT, 7, 32, 1)),
     'an id is defined by more than one instruction'),
    ('string_not_padded', words(HEADER + inst(OP_NAME, 1, 0x00010061)), 'literal string not padded with 0'),
    ('string_without_nul', words(HEADER + inst(OP_NAME, 1, 0x64636261)),
     'literal string without nul-termination character'),
    ('string_not_utf8', words(HEADER + inst(OP_NAME, 1, 0x000000FF)), 'literal string is not valid UTF-8'),
    ('name_with_extra_operand', words(HEADER + inst(OP_NAME, 1, 0x61, 2)), 'OpName has operands after its name'),
    ('typeint_two_operands', words(HEADER + inst(OP_TYPE_INT, 7, 32)), 'OpTypeInt without exactly three operands'),
]


class Runner:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.failures: list[str] = []
        self.count = 0
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix='spvbind-tests-'))
        self.compilers = [c for c in args.cxx if shutil.which(c)]

    def spvbind(self, module: pathlib.Path, *flags: str) -> subprocess.CompletedProcess[str]:
        # Run from the module's directory, so that the header's first line names only the file.
        return subprocess.run([self.args.spvbind, *flags, module.name], cwd=module.parent, capture_output=True,
                              text=True)

    def check(self, name: str, condition: bool, detail: str = '') -> None:
        self.count += 1
        if not condition:
            self.failures.append(f'{name}: {detail}')
            print(f'FAIL {name}: {detail}')

    def expect(self, name: str, actual: str, expected: pathlib.Path) -> None:
        """`actual` equals the file's content, or rewrites it with --update."""
        if self.args.update:
            expected.write_text(actual)
            return
        if not expected.exists():
            self.check(name, False, f'{expected.name} does not exist; run with --update')
            return
        text = expected.read_text()
        if actual != text:
            diff = subprocess.run(['diff', '-u', str(expected), '-'], input=actual, capture_output=True, text=True)
            self.check(name, False, f'{expected.name} differs:\n{diff.stdout}')
        else:
            self.check(name, True)

    # --- Cases ------------------------------------------------------------------------------------------------------

    def accepted(self, source: pathlib.Path) -> None:
        name = source.stem
        directory = self.tmp / 'accepted' / name
        directory.mkdir(parents=True)
        module = directory / f'{name}.spv'
        glslc = subprocess.run([self.args.glslc, '--target-env=vulkan1.3', '-o', str(module), str(source)],
                               capture_output=True, text=True)
        if glslc.returncode != 0:
            self.check(f'accepted/{name}', False, f'glslc failed:\n{glslc.stderr}')
            return
        header = self.spvbind(module)
        self.check(f'accepted/{name} exit code', header.returncode == 0, f'{header.returncode}: {header.stderr}')
        if header.returncode == 0:
            self.expect(f'accepted/{name} header', header.stdout, source.with_suffix('.hpp'))
        locations = self.spvbind(module, '--locations')
        self.check(f'accepted/{name} --locations exit code', locations.returncode == 0, locations.stderr)
        if locations.returncode == 0:
            self.expect(f'accepted/{name} locations', locations.stdout, source.with_suffix('.locations'))

        # The same module stored big-endian.
        swapped = self.tmp / 'big-endian' / name
        swapped.mkdir(parents=True)
        data = module.read_bytes()
        (swapped / module.name).write_bytes(b''.join(data[i:i + 4][::-1] for i in range(0, len(data), 4)))
        big = self.spvbind(swapped / module.name)
        self.check(f'accepted/{name} big-endian', big.returncode == 0 and big.stdout == header.stdout,
                   big.stderr or 'different output')

        # The header compiles, so its static_asserts hold.
        if header.returncode == 0:
            header_file = directory / f'{name}.hpp'
            header_file.write_text(header.stdout)
            for cxx in self.compilers:
                p = subprocess.run([cxx, '-std=c++20', '-Wall', '-Wextra', '-Werror', '-fsyntax-only', '-I',
                                    str(directory), '-x', 'c++', '-'], input=f'#include "{name}.hpp"\n',
                                   capture_output=True, text=True)
                self.check(f'accepted/{name} compiles with {cxx}', p.returncode == 0, p.stderr)

    def rejected(self, source: pathlib.Path) -> None:
        name = source.stem
        directory = self.tmp / 'rejected' / name
        directory.mkdir(parents=True)
        module = directory / f'{name}.spv'
        env = 'vulkan1.3'
        for line in source.read_text().splitlines()[:3]:
            if line.startswith('; target-env:'):
                env = line.split(':', 1)[1].strip()
        assembled = subprocess.run([self.args.spirv_as, '--target-env', env, '-o', str(module), str(source)],
                                   capture_output=True, text=True)
        if assembled.returncode != 0:
            self.check(f'rejected/{name}', False, f'spirv-as failed:\n{assembled.stderr}')
            return
        self.rejection(f'rejected/{name}', module, source.with_suffix('.err'))
        locations_file = source.with_suffix('.locations')
        locations = self.spvbind(module, '--locations')
        if self.args.update and locations.returncode == 0:
            locations_file.write_text(locations.stdout)
        if locations_file.exists():
            self.check(f'rejected/{name} --locations exit code', locations.returncode == 0, locations.stderr)
            if locations.returncode == 0:
                self.expect(f'rejected/{name} locations', locations.stdout, locations_file)
        else:
            header = self.spvbind(module)
            self.check(f'rejected/{name} --locations', locations.returncode == 1 and locations.stderr == header.stderr,
                       f'exit {locations.returncode}: {locations.stderr}')

    def rejection(self, name: str, module: pathlib.Path, expected: pathlib.Path) -> None:
        p = self.spvbind(module)
        self.check(f'{name} exit code', p.returncode == 1 and p.stdout == '', f'exit {p.returncode}, stdout {p.stdout!r}')
        prefix = f'{module.name}: '
        self.check(f'{name} message names the file', p.stderr.startswith(prefix), repr(p.stderr))
        self.expect(f'{name} message', p.stderr.removeprefix(prefix), expected)

    def raw(self) -> None:
        for name, data, message in RAW:
            directory = self.tmp / 'raw' / name
            directory.mkdir(parents=True)
            module = directory / f'{name}.spv'
            module.write_bytes(data)
            p = self.spvbind(module)
            self.check(f'raw/{name}', p.returncode == 1 and p.stderr == f'{module.name}: {message}\n',
                       f'exit {p.returncode}: {p.stderr!r}')
        # A large module: a million one-word instructions (OpNop), which the decoders must take in constant stack.
        directory = self.tmp / 'raw' / 'large'
        directory.mkdir(parents=True)
        module = directory / 'large.spv'
        module.write_bytes(words(HEADER) + struct.pack('<I', 0x00010000) * 1_000_000)
        p = self.spvbind(module, '--locations')
        self.check('raw/large', p.returncode == 0 and p.stdout == '', f'exit {p.returncode}: {p.stderr!r}')

    def usage(self) -> None:
        for flags in ([], ['--locations'], ['a.spv', 'b.spv'], ['--bogus', 'a.spv']):
            p = subprocess.run([self.args.spvbind, *flags], capture_output=True, text=True)
            self.check(f'usage {flags}', p.returncode == 2 and p.stderr.startswith('usage:') and p.stdout == '',
                       f'exit {p.returncode}: {p.stderr!r}')
        p = subprocess.run([self.args.spvbind, str(self.tmp / 'missing.spv')], capture_output=True, text=True)
        self.check('missing file', p.returncode != 0 and p.stdout == '', f'exit {p.returncode}')

    def run(self) -> int:
        try:
            for source in sorted((HERE / 'accepted').glob('*.comp')):
                self.accepted(source)
            for source in sorted((HERE / 'rejected').glob('*.spvasm')):
                self.rejected(source)
            self.raw()
            self.usage()
        finally:
            shutil.rmtree(self.tmp, ignore_errors=True)
        compilers = ', '.join(self.compilers) or 'no C++ compiler'
        print(f'{self.count - len(self.failures)}/{self.count} checks passed ({compilers})')
        return 1 if self.failures else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--spvbind', default=str(HERE.parent / '.lake/build/bin/spvbind'))
    parser.add_argument('--glslc', default='glslc')
    parser.add_argument('--spirv-as', default='spirv-as')
    parser.add_argument('--cxx', nargs='*', default=['g++', 'clang++'], help='compilers to check the headers with')
    parser.add_argument('--update', action='store_true', help='rewrite the expected outputs')
    args = parser.parse_args()
    for tool in (args.spvbind, args.glslc, args.spirv_as):
        if not shutil.which(tool):
            print(f'{tool} not found', file=sys.stderr)
            return 2
    return Runner(args).run()


if __name__ == '__main__':
    sys.exit(main())
