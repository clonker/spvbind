/-!
# The SPIR-V binary format: words and header

SPIR-V specification, version 1.6, revision 8 (https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html):
2.2 Terms, 2.3 Physical Layout of a SPIR-V Module and Instruction, 3.1 Magic Number.
-/

namespace Spec

/-- 2.2 Terms: a word is 32 bits. -/
abbrev Word := UInt32

/-- Technically not one of the terms in 2.2 -/
abbrev Byte := UInt8

/-- Magic Number (3.1) -/
def magic : Word := 0x07230203

/-- The words of 2.3, Table 1 that differ between modules. -/
structure Header where
  version : Word
  generator : Word
  bound : Word
  deriving Repr, DecidableEq

/-- 2.3, Table 1. First Words of Physical Layout; word 5 is the first word of the instruction stream. -/
def Header.words (h : Header) : List Word :=
  [magic,
   h.version,    -- 1: Version number; the bytes are, high-order to low-order: 0 | Major Number | Minor Number | 0
   h.generator,  -- 2: Generator's magic number; it does not affect any semantics, and is allowed to be 0
   h.bound,      -- 3: Bound; all ids in the module satisfy 0 < id < Bound
   0]            -- 4: 0 (Reserved for instruction schema, if needed)

/-- The second-highest byte of the version number (2.3, Table 1). -/
def Header.major (h : Header) : Byte := (h.version >>> 16).toUInt8

/-- The second-lowest byte of the version number (2.3, Table 1). -/
def Header.minor (h : Header) : Byte := (h.version >>> 8).toUInt8

end Spec
