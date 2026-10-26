#!/usr/bin/env python3
"""Checks Spec/Instruction.lean against spirv.core.grammar.json, the machine-readable grammar of SPIR-V.

The Lean file is transcribed from the specification by hand; the JSON is what SPIRV-Tools and others are generated
from. The two must agree on the opcode and enumerant values, and the operands of each modelled instruction, read here
from `MODEL`, must be the grammar's. `MODEL` is a second transcription, to be compared with `Spec.Instruction` by eye:
it is short.

    tests/grammar.py path/to/spirv.core.grammar.json

The JSON is in SPIRV-Headers, include/spirv/unified1/spirv.core.grammar.json.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent / 'Spec' / 'Instruction.lean'

# The operands of each modelled instruction as `Spec.Instruction` has them, with the grammar's kinds and quantifiers
# (`?` optional, `*` any number).
MODEL = {
    'OpName': ['IdRef', 'LiteralString'],
    'OpMemberName': ['IdRef', 'LiteralInteger', 'LiteralString'],
    'OpTypeInt': ['IdResult', 'LiteralInteger', 'LiteralInteger'],
    'OpTypeFloat': ['IdResult', 'LiteralInteger'],
    'OpTypeVector': ['IdResult', 'IdRef', 'LiteralInteger'],
    'OpTypeArray': ['IdResult', 'IdRef', 'IdRef'],
    'OpConstant': ['IdResultType', 'IdResult', 'LiteralContextDependentNumber'],
    'OpDecorate': ['IdRef', 'Decoration'],
    'OpTypeStruct': ['IdResult', 'IdRef*'],
    'OpTypePointer': ['IdResult', 'StorageClass', 'IdRef'],
    'OpVariable': ['IdResultType', 'IdResult', 'StorageClass', 'IdRef?'],
    'OpMemberDecorate': ['IdRef', 'LiteralInteger', 'Decoration'],
}
# Optional operands the model leaves out on purpose: an instruction that has them is a decode error.
OMITTED = {'OpTypeFloat': ['FPEncoding?']}
# Enumerants modelled as values of `Word`, with their operand kind and, for decorations, their parameters.
ENUMERANTS = {'PushConstant': ('StorageClass', []), 'Offset': ('Decoration', ['LiteralInteger']),
              'ArrayStride': ('Decoration', ['LiteralInteger'])}


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    grammar = json.loads(pathlib.Path(sys.argv[1]).read_text())
    lean = LEAN.read_text()
    print(f'grammar {grammar["major_version"]}.{grammar["minor_version"]} revision {grammar["revision"]}')
    problems: list[str] = []

    instructions = {i['opname']: i for i in grammar['instructions']}
    opcodes = {m.group(1): int(m.group(2)) for m in re.finditer(r'^def (Op\w+) : UInt16 := (\d+)', lean, re.M)}
    if set(opcodes) != set(MODEL):
        problems.append(f'the Lean opcodes {sorted(opcodes)} are not those of MODEL {sorted(MODEL)}')
    for name, value in opcodes.items():
        if name not in instructions:
            problems.append(f'{name} is not in the grammar')
            continue
        if instructions[name]['opcode'] != value:
            problems.append(f'{name} is {instructions[name]["opcode"]} in the grammar, {value} in Lean')
        expected = [o['kind'] + o.get('quantifier', '') for o in instructions[name].get('operands', [])]
        model = MODEL.get(name, []) + OMITTED.get(name, [])
        if expected != model:
            problems.append(f'{name} has operands {expected} in the grammar, {model} in the model')

    kinds = {k['kind']: k for k in grammar['operand_kinds']}
    for name, (kind, parameters) in ENUMERANTS.items():
        match = re.search(rf'^def {name} : Word := (\d+)', lean, re.M)
        if not match:
            problems.append(f'def {name} not found in {LEAN.name}')
            continue
        enumerant = next((e for e in kinds[kind]['enumerants'] if e['enumerant'] == name), None)
        if enumerant is None:
            problems.append(f'{kind} {name} is not in the grammar')
            continue
        if int(enumerant['value']) != int(match.group(1)):
            problems.append(f'{kind} {name} is {enumerant["value"]} in the grammar, {match.group(1)} in Lean')
        expected = [p['kind'] + p.get('quantifier', '') for p in enumerant.get('parameters', [])]
        if expected != parameters:
            problems.append(f'{kind} {name} has parameters {expected} in the grammar, {parameters} here')

    # The modelled lists in Lean must name exactly the modelled constructors' enumerants.
    modelled = re.search(r'^def modelled : List UInt16 :=\n\s*\[([^\]]*)\]', lean, re.M)
    if not modelled or set(x.strip() for x in modelled.group(1).split(',')) != set(opcodes):
        problems.append('`modelled` does not list exactly the Op* definitions')
    if not re.search(r'^def modelledDecorations : List Word := \[ArrayStride, Offset\]', lean, re.M):
        problems.append('`modelledDecorations` is not [ArrayStride, Offset]')

    for p in problems:
        print(f'PROBLEM: {p}')
    checked = len(opcodes) + len(ENUMERANTS)
    print(f'{checked} opcodes and enumerants checked, {len(problems)} problems')
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
