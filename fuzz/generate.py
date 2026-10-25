"""Random SPIR-V modules with push constant blocks, for differential.py.

Three sources:
- glsl: a random push constant interface as GLSL, for glslc to compile. This is what users write, and the layout is the
  one glslc chooses.
- spirv: a random module written word by word, with the freedom glslc never uses: any ids, any order of names and
  decorations, aligned offsets with gaps at every level, and with a probability (`exotic`) constructs that are invalid,
  that spvbind rejects, or that only a reflection library would get wrong.
- mutate: an existing module with a few words changed, mostly in the instructions spvbind reads.

The interface is described by `Scalar` and `Struct`; `layout` gives its std430 layout, which glslc uses for push
constants and which is also the C++ layout spvbind emits.
"""

from __future__ import annotations

import random
import struct
from dataclasses import dataclass, field

# --- The interface ----------------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Scalar:
    kind: str  # 'i', 'u' or 'f'
    width: int  # bits

    @property
    def glsl(self) -> str:
        return {
            ('f', 16): 'float16_t', ('f', 32): 'float', ('f', 64): 'double',
            ('i', 8): 'int8_t', ('i', 16): 'int16_t', ('i', 32): 'int', ('i', 64): 'int64_t',
            ('u', 8): 'uint8_t', ('u', 16): 'uint16_t', ('u', 32): 'uint', ('u', 64): 'uint64_t',
        }[(self.kind, self.width)]

    @property
    def bytes(self) -> int:
        return self.width // 8


@dataclass(frozen=True)
class Vector:
    scalar: Scalar
    count: int  # 2 to 4

    @property
    def glsl(self) -> str:
        prefix = {('f', 16): 'f16', ('f', 32): '', ('f', 64): 'd', ('i', 8): 'i8', ('i', 16): 'i16', ('i', 32): 'i',
                  ('i', 64): 'i64', ('u', 8): 'u8', ('u', 16): 'u16', ('u', 32): 'u', ('u', 64): 'u64'}
        return f'{prefix[(self.scalar.kind, self.scalar.width)]}vec{self.count}'


@dataclass
class Struct:
    name: str
    members: list[tuple[str, Scalar | Vector | Struct]] = field(default_factory=list)


Type = Scalar | Vector | Struct

# spvbind supports these; weights favour the common ones.
SUPPORTED = [
    (Scalar('f', 32), 6), (Scalar('f', 64), 2), (Scalar('i', 32), 4), (Scalar('u', 32), 4),
    (Scalar('i', 8), 1), (Scalar('u', 8), 1), (Scalar('i', 16), 1), (Scalar('u', 16), 1),
    (Scalar('i', 64), 1), (Scalar('u', 64), 1),
]
# spvbind rejects this one; glslc accepts it.
UNSUPPORTED_SCALARS = [Scalar('f', 16)]

# Names valid in GLSL that spvbind must reject or that are easy to get wrong.
CPP_KEYWORDS = [
    'new', 'delete', 'virtual', 'char', 'auto', 'register', 'catch', 'try', 'throw', 'friend', 'operator', 'private',
    'protected', 'explicit', 'mutable', 'wchar_t', 'decltype', 'constexpr', 'nullptr', 'alignas', 'alignof', 'concept',
    'requires', 'export', 'co_await', 'co_return', 'co_yield', 'char8_t', 'char16_t', 'char32_t', 'thread_local',
    'static_assert', 'consteval', 'constinit', 'dynamic_cast', 'reinterpret_cast', 'static_cast', 'const_cast',
    'typeid', 'typename', 'signed', 'and', 'or', 'not', 'xor', 'bitand', 'bitor', 'compl', 'and_eq', 'or_eq', 'xor_eq',
    'not_eq', 'contract_assert', 'bool',
]
WEIRD_NAMES = CPP_KEYWORDS + ['spvbindPadding0', 'spvbind', '_x', 'x_', 'x__y', 'offsetof', 'std', 'int32_t', 'size_t',
                              'Params', 'main', 'NULL', 'EOF', 'errno', 'assert', 'INT_MAX']


def align_up(n: int, a: int) -> int:
    return (n + a - 1) // a * a


def layout(t: Type, scalar_block: bool = False) -> tuple[int, int, list[int]]:
    """The std430 (alignment, size, member offsets) of `t`; with `scalar_block`, the scalar block layout, where a struct
    is aligned like its most aligned scalar and ends with its last member."""
    if isinstance(t, Scalar):
        return t.bytes, t.bytes, []
    if isinstance(t, Vector):
        # std430: a two-component vector is aligned to twice its component, three or four to four times.
        align = t.scalar.bytes if scalar_block else t.scalar.bytes * (2 if t.count == 2 else 4)
        return align, t.count * t.scalar.bytes, []
    align, cursor, offsets = 1, 0, []
    for _, member in t.members:
        a, size, _ = layout(member, scalar_block)
        cursor = align_up(cursor, a)
        offsets.append(cursor)
        cursor += size
        align = max(align, a)
    return align, (cursor if scalar_block else align_up(cursor, align)), offsets


def structs_of(t: Type, out: list[Struct] | None = None) -> list[Struct]:
    """The structs `t` uses, each once, each after the ones it uses."""
    out = [] if out is None else out
    if isinstance(t, Struct):
        for _, member in t.members:
            structs_of(member, out)
        if all(s is not t for s in out):
            out.append(t)
    return out


def scalars_of(t: Type) -> set[Scalar]:
    if isinstance(t, Scalar):
        return {t}
    if isinstance(t, Vector):
        return {t.scalar}
    return set().union(*(scalars_of(m) for _, m in t.members)) if t.members else set()


def vectors_of(t: Type) -> set[Vector]:
    if isinstance(t, Vector):
        return {t}
    if isinstance(t, Struct) and t.members:
        return set().union(*(vectors_of(m) for _, m in t.members))
    return set()


@dataclass
class Config:
    max_depth: int = 3
    max_members: int = 6
    p_struct: float = 0.3  # a member is a nested struct
    p_vector: float = 0.35  # otherwise, a member is a vector
    p_reuse: float = 0.3  # a nested struct member reuses an existing struct type
    p_weird_name: float = 0.005  # a name from WEIRD_NAMES
    p_gap: float = 0.25  # a member gets an explicit offset with a gap before it
    exotic: float = 0.0  # probability of each exotic construct in `spirv`


class Names:
    def __init__(self, rng: random.Random, cfg: Config):
        self.rng, self.cfg, self.count = rng, cfg, 0

    def __call__(self, prefix: str) -> str:
        self.count += 1
        if self.rng.random() < self.cfg.p_weird_name:
            return self.rng.choice(WEIRD_NAMES)
        return f'{prefix}{self.count}'


def random_struct(rng: random.Random, cfg: Config, names: Names, existing: list[Struct], depth: int,
                  scalars: list[Scalar]) -> Struct:
    s = Struct(names('S'))
    for _ in range(rng.randint(1, cfg.max_members)):
        if depth < cfg.max_depth and rng.random() < cfg.p_struct:
            if existing and rng.random() < cfg.p_reuse:
                member: Type = rng.choice(existing)
            else:
                member = random_struct(rng, cfg, names, existing, depth + 1, scalars)
                existing.append(member)
        elif rng.random() < cfg.p_vector:
            member = Vector(rng.choice(scalars), rng.choice([2, 3, 4]))
        else:
            member = rng.choice(scalars)
        s.members.append((names('m'), member))
    return s


def random_interface(rng: random.Random, cfg: Config, exotic_scalars: bool = False) -> Struct:
    """A push constant block."""
    scalars = [s for s, w in SUPPORTED for _ in range(w)]
    if exotic_scalars:
        scalars += UNSUPPORTED_SCALARS
    names = Names(rng, cfg)
    block = random_struct(rng, cfg, names, [], 1, scalars)
    block.name = names('Block') if rng.random() < 0.3 else 'Params'
    return block


# --- GLSL ------------------------------------------------------------------------------------------------------------


def to_glsl(block: Struct, rng: random.Random, cfg: Config) -> str:
    scalars = scalars_of(block)
    lines = ['#version 460']
    if any(s.width != 32 for s in scalars):
        lines.append('#extension GL_EXT_shader_explicit_arithmetic_types : require')
    if any(s.width == 8 for s in scalars):
        lines.append('#extension GL_EXT_shader_8bit_storage : require')
    if any(s.width == 16 for s in scalars):
        lines.append('#extension GL_EXT_shader_16bit_storage : require')
    lines.append('layout(local_size_x = 1) in;')
    for s in structs_of(block)[:-1]:
        lines.append(f'struct {s.name}\n{{')
        lines += [f'    {m.name if isinstance(m, Struct) else m.glsl} {name};' for name, m in s.members]
        lines.append('};')
    # Explicit offsets are only allowed on block members, where glslc requires them to be aligned and in order.
    _, _, offsets = layout(block)
    lines.append(f'layout(push_constant) uniform {block.name}\n{{')
    cursor = 0
    for (name, m), natural in zip(block.members, offsets):
        a, size, _ = layout(m)
        offset = align_up(cursor, a)  # the natural offset, once earlier gaps have moved the member
        if rng.random() < cfg.p_gap:
            offset += a * rng.choice([1, 1, 2, 3, 4, 8])
        cursor = offset + size
        qualifier = f'layout(offset = {offset}) ' if offset != natural or rng.random() < 0.1 else ''
        lines.append(f'    {qualifier}{m.name if isinstance(m, Struct) else m.glsl} {name};')
    lines.append('}' + (' pc;' if rng.random() < 0.5 else ';'))
    lines.append('layout(set = 0, binding = 0) buffer Out\n{\n    uint words[];\n};')
    lines.append('void main()\n{\n    words[0] = 1u;\n}')
    return '\n'.join(lines) + '\n'


# --- SPIR-V, word by word ---------------------------------------------------------------------------------------------

MAGIC = 0x07230203
OP = dict(Source=3, Name=5, MemberName=6, MemoryModel=14, EntryPoint=15, ExecutionMode=16, Capability=17, TypeVoid=19,
          TypeBool=20, TypeInt=21, TypeFloat=22, TypeVector=23, TypeArray=28, TypeStruct=30, TypePointer=32,
          TypeFunction=33, Constant=43, Function=54, FunctionEnd=56, Variable=59, Decorate=71, MemberDecorate=72,
          Label=248, Return=253)
CAP = dict(Shader=1, Float16=9, Float64=10, Int64=11, Int16=22, Int8=39, StoragePushConstant16=4435,
           StoragePushConstant8=4450)
BLOCK, OFFSET = 2, 35
PUSH_CONSTANT, STORAGE_BUFFER = 9, 12


def op(opcode: int, *operands: int) -> list[int]:
    return [((len(operands) + 1) << 16) | opcode, *operands]


def literal(s: str) -> list[int]:
    data = s.encode() + b'\0'
    data += b'\0' * (-len(data) % 4)
    return list(struct.unpack(f'<{len(data) // 4}I', data))


def to_bytes(words: list[int]) -> bytes:
    return struct.pack(f'<{len(words)}I', *(w & 0xFFFFFFFF for w in words))


def from_bytes(data: bytes) -> list[int]:
    return list(struct.unpack(f'<{len(data) // 4}I', data[:len(data) // 4 * 4]))


class Module:
    """A module under construction: ids are drawn at random, sections are shuffled where the logical layout allows."""

    def __init__(self, rng: random.Random):
        self.rng = rng
        self.ids: list[int] = []
        self.capabilities: set[int] = {CAP['Shader']}
        self.debug: list[list[int]] = []
        self.annotations: list[list[int]] = []
        self.types: list[list[int]] = []  # in dependency order
        self.variables: list[list[int]] = []
        self.interface: list[int] = []

    def fresh(self) -> int:
        while True:
            i = self.rng.randint(1, 4000)
            if i not in self.ids:
                self.ids.append(i)
                return i

    def words(self, exotic: float = 0.0) -> list[int]:
        rng = self.rng
        main, void, fn, label = self.fresh(), self.fresh(), self.fresh(), self.fresh()
        bound = max(self.ids) + 1
        if rng.random() < exotic:
            bound += rng.randint(1, 1000)
        header = [MAGIC, 0x00010600, rng.choice([0, 0, 0x00080001, rng.getrandbits(32)]), bound, 0]
        preamble = [op(OP['Capability'], c) for c in sorted(self.capabilities)]
        preamble.append(op(OP['MemoryModel'], 0, 1))
        preamble.append(op(OP['EntryPoint'], 5, main, *literal('main'), *self.interface))
        preamble.append(op(OP['ExecutionMode'], main, 17, 1, 1, 1))
        debug = [op(OP['Name'], main, *literal('main'))] + self.debug
        annotations = list(self.annotations)
        rng.shuffle(debug)
        rng.shuffle(annotations)
        if rng.random() < 0.5:
            debug.insert(0, op(OP['Source'], 2, 460))
        types = [op(OP['TypeVoid'], void), op(OP['TypeFunction'], fn, void)] + self.types + self.variables
        function = [op(OP['Function'], void, main, 0, fn), op(OP['Label'], label), op(OP['Return']), op(OP['FunctionEnd'])]
        return header + sum(preamble + debug + annotations + types + function, [])


def to_spirv(block: Struct, rng: random.Random, cfg: Config) -> tuple[bytes, list[str]]:
    """`block` as a module, with the exotic constructs chosen (each with probability `cfg.exotic`) listed."""
    m = Module(rng)
    exotic: list[str] = []

    def choose(name: str) -> bool:
        if rng.random() < cfg.exotic:
            exotic.append(name)
            return True
        return False

    scalar_ids: dict[Scalar, int] = {}
    for s in sorted(scalars_of(block), key=lambda s: (s.kind, s.width)):
        scalar_ids[s] = m.fresh()
        if s.kind == 'f':
            m.types.append(op(OP['TypeFloat'], scalar_ids[s], s.width))
            if s.width == 64:
                m.capabilities.add(CAP['Float64'])
            if s.width == 16:
                m.capabilities.add(CAP['Float16'])
        else:
            m.types.append(op(OP['TypeInt'], scalar_ids[s], s.width, 1 if s.kind == 'i' else 0))
            if s.width == 64:
                m.capabilities.add(CAP['Int64'])
            if s.width == 16:
                m.capabilities.add(CAP['Int16'])
            if s.width == 8:
                m.capabilities.add(CAP['Int8'])
        if s.width == 8:
            m.capabilities.add(CAP['StoragePushConstant8'])
        if s.width == 16:
            m.capabilities.add(CAP['StoragePushConstant16'])
    vector_ids: dict[Vector, int] = {}
    for v in sorted(vectors_of(block), key=lambda v: (v.scalar.kind, v.scalar.width, v.count)):
        vector_ids[v] = m.fresh()
        m.types.append(op(OP['TypeVector'], vector_ids[v], scalar_ids[v.scalar], v.count))

    huge = choose('huge offsets')
    unordered = choose('unordered offsets')
    scalar_layout = choose('scalar block layout')
    struct_ids: dict[int, int] = {}
    placed: dict[int, tuple[int, int]] = {}  # (alignment, size) of each struct as laid out here, gaps included

    def placement(t: Type) -> tuple[int, int]:
        if isinstance(t, Struct):
            return placed[id(t)]
        align, size, _ = layout(t, scalar_layout)
        return align, size

    for s in structs_of(block):
        sid = m.fresh()
        struct_ids[id(s)] = sid
        member_ids = [scalar_ids[t] if isinstance(t, Scalar) else vector_ids[t] if isinstance(t, Vector)
                      else struct_ids[id(t)] for _, t in s.members]
        m.types.append(op(OP['TypeStruct'], sid, *member_ids))
        if not (s is block and choose('nameless struct')):
            m.debug.append(op(OP['Name'], sid, *literal(s.name)))
        cursor, align = 0, 1
        for index, (name, t) in enumerate(s.members):
            a, size = placement(t)
            offset = align_up(cursor, a)
            if rng.random() < cfg.p_gap:
                offset += a * rng.choice([1, 1, 2, 3, 4, 8, 64])
            cursor = offset + size
            align = max(align, a)
            if huge and s is block:
                offset = (0xFFFFFFFF - rng.randint(0, 3) * 16) // a * a - (len(s.members) - index) * 16
            if not (index == 0 and s is block and choose('nameless member')):
                m.debug.append(op(OP['MemberName'], sid, index, *literal(name)))
            if not (index == 0 and s is block and choose('member without Offset')):
                m.annotations.append(op(OP['MemberDecorate'], sid, index, OFFSET, offset))
            if index == 0 and s is block and choose('two Offsets'):
                m.annotations.append(op(OP['MemberDecorate'], sid, index, OFFSET, offset + a))
        placed[id(s)] = (align, cursor if scalar_layout else align_up(cursor, align))
        if unordered and s is block and len(s.members) >= 2:
            # Swap the offsets of the first two members: valid SPIR-V, which spvbind does not support.
            decorations = [a for a in m.annotations if a[0] & 0xFFFF == OP['MemberDecorate'] and a[1] == sid and a[2] in (0, 1)]
            if len(decorations) == 2:
                decorations[0][4], decorations[1][4] = decorations[1][4], decorations[0][4]
        if s is block and choose('member index past the end'):
            m.annotations.append(op(OP['MemberDecorate'], sid, len(s.members) + rng.choice([0, 1, 100, 2 ** 20]), OFFSET, 0))
        if s is block and choose('member name past the end'):
            m.debug.append(op(OP['MemberName'], sid, len(s.members) + rng.choice([0, 1, 100]), *literal('ghost')))
    top = struct_ids[id(block)]
    if not choose('no Block decoration'):
        m.annotations.append(op(OP['Decorate'], top, BLOCK))

    pointer = m.fresh()
    m.types.append(op(OP['TypePointer'], pointer, PUSH_CONSTANT, top))
    variable = m.fresh()
    m.variables.append(op(OP['Variable'], pointer, variable, PUSH_CONSTANT))
    m.interface.append(variable)
    m.debug.append(op(OP['Name'], variable, *literal(rng.choice(['', '', 'pc', 'params', '_']))))

    if choose('second variable of the same type'):
        other = m.fresh()
        m.variables.append(op(OP['Variable'], pointer, other, PUSH_CONSTANT))
        m.debug.append(op(OP['Name'], other, *literal('other')))
    if choose('storage buffer with the same struct'):
        sb_pointer, sb_variable = m.fresh(), m.fresh()
        m.types.append(op(OP['TypePointer'], sb_pointer, STORAGE_BUFFER, top))
        m.variables.append(op(OP['Variable'], sb_pointer, sb_variable, STORAGE_BUFFER))
        m.debug.append(op(OP['Name'], sb_variable, *literal('buffer')))
    if choose('unused struct with the same name'):
        decoy = m.fresh()
        m.types.append(op(OP['TypeStruct'], decoy, *([scalar_ids[t] for t in scalar_ids][:1] * 2)))
        m.debug.append(op(OP['Name'], decoy, *literal(block.name)))
        m.debug.append(op(OP['MemberName'], decoy, 0, *literal('a')))
        m.debug.append(op(OP['MemberName'], decoy, 1, *literal('b')))
        m.annotations.append(op(OP['MemberDecorate'], decoy, 0, OFFSET, 0))
        m.annotations.append(op(OP['MemberDecorate'], decoy, 1, OFFSET, 4))
    if choose('vector member in an unused struct'):
        vec, holder = m.fresh(), m.fresh()
        f32 = scalar_ids.get(Scalar('f', 32))
        if f32 is None:
            f32 = m.fresh()
            scalar_ids[Scalar('f', 32)] = f32
            m.types.append(op(OP['TypeFloat'], f32, 32))
        m.types.append(op(OP['TypeVector'], vec, f32, 4))
        m.types.append(op(OP['TypeStruct'], holder, vec))
        m.debug.append(op(OP['Name'], holder, *literal('Holder')))
        m.debug.append(op(OP['MemberName'], holder, 0, *literal('v')))
        m.annotations.append(op(OP['MemberDecorate'], holder, 0, OFFSET, 0))
    if choose('decoration of an undefined id'):
        m.annotations.append(op(OP['MemberDecorate'], max(m.ids) + 1, 0, OFFSET, 0))
    return to_bytes(m.words(cfg.exotic)), exotic


# --- Mutation ---------------------------------------------------------------------------------------------------------

READ_OPCODES = {5, 6, 21, 22, 30, 32, 59, 72}  # the instructions spvbind reads


def instructions(words: list[int]) -> list[tuple[int, int]]:
    """(start, length) of each instruction after the header, as the word counts say; a bad count ends the list."""
    out, i = [], 5
    while i < len(words):
        n = words[i] >> 16
        if n == 0 or i + n > len(words):
            break
        out.append((i, n))
        i += n
    return out


def mutate(rng: random.Random, data: bytes) -> tuple[bytes, list[str]]:
    """`data` with one to three mutations, described."""
    words = from_bytes(data)
    done: list[str] = []
    for _ in range(rng.choice([1, 1, 1, 2, 3])):
        insts = instructions(words)
        if len(words) < 6 or not insts:
            words = words + [rng.getrandbits(32)]
            done.append('append word')
            continue
        # Prefer the instructions spvbind reads.
        read = [x for x in insts if words[x[0]] & 0xFFFF in READ_OPCODES]
        start, n = rng.choice(read) if read and rng.random() < 0.8 else rng.choice(insts)
        opcode = words[start] & 0xFFFF
        choice = rng.random()
        if choice < 0.35 and n > 1:
            k = start + rng.randint(1, n - 1)
            if opcode == 72 and n == 5 and rng.random() < 0.7:
                k = start + 4  # the Offset
                delta = rng.choice([1, -1, 2, 4, -4, 8, -8, 16, 2 ** 31, 2 ** 32 - 1])
                words[k] = (words[k] + delta) & 0xFFFFFFFF
                done.append(f'offset {delta:+}')
            else:
                words[k] = rng.choice([0, 1, 2, 3, 4, 8, 9, 16, 32, 64, 0xFFFFFFFF, rng.getrandbits(32),
                                       words[rng.randrange(len(words))]])
                done.append(f'operand {k - start} of opcode {opcode} := {words[k]}')
        elif choice < 0.5:
            k = rng.randrange(len(words))
            words[k] ^= 1 << rng.randrange(32)
            done.append(f'bit flip in word {k}')
        elif choice < 0.6:
            del words[start:start + n]
            done.append(f'delete opcode {opcode}')
        elif choice < 0.7:
            words[start + n:start + n] = words[start:start + n]
            done.append(f'duplicate opcode {opcode}')
        elif choice < 0.78:
            words[start] = (words[start] & 0xFFFF) | ((n + rng.choice([-1, 1, 1, 2, 1000])) & 0xFFFF) << 16
            done.append(f'word count of opcode {opcode} changed')
        elif choice < 0.85:
            words[start] = ((n << 16) | rng.choice(list(READ_OPCODES) + [rng.randrange(1, 500)])) & 0xFFFFFFFF
            done.append(f'opcode {opcode} -> {words[start] & 0xFFFF}')
        elif choice < 0.9:
            words.append(rng.choice([rng.getrandbits(32), words[start]]))
            done.append('append word')
        elif choice < 0.95:
            cut = rng.randrange(5, len(words))
            words = words[:cut]
            done.append(f'truncate to {cut} words')
        else:
            k = rng.randrange(5)
            words[k] = rng.choice([0, 0x00010000, 0x00010300, 0x00010400, MAGIC, 0x03022307, rng.getrandbits(32)])
            done.append(f'header word {k} := {words[k]:#x}')
    out = to_bytes(words)
    if rng.random() < 0.05:
        out = out[:rng.randrange(len(out) + 1)]
        done.append('truncate to a byte boundary')
    return out, done
