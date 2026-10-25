/-!
# The SPIR-V binary format: words, header and literal strings

SPIR-V specification, version 1.6, revision 8 (https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html):
2.2 Terms, 2.3 Physical Layout of a SPIR-V Module and Instruction, 3.1 Magic Number (and Endianness).
-/

namespace Spec

/-- 2.2 Terms: a word is 32 bits. -/
abbrev Word := UInt32

/-- Technically not one of the terms in 2.2 -/
abbrev Byte := UInt8

/-- 2.2 Terms: an <id> is a numerical name, and always consumes one word. -/
abbrev Id := Word

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

/-- Four octets as a word, the first in the lowest-order 8 bits (2.2.1, Literal). -/
def wordOfOctets (b0 b1 b2 b3 : Byte) : Word :=
  b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24

/-- The four octets of a word, the first from the lowest-order 8 bits (2.2.1, Literal). -/
def octets (w : Word) : List Byte :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- 3.1, Endianness: a module is a stream of words, and when it is stored as bytes each word is four octets in the byte
order of the system that stored it. Little-endian: the lowest-order octet of each word first. -/
def littleEndianBytes (ws : List Word) : List Byte := ws.flatMap octets

/-- Big-endian: the highest-order octet of each word first. "The magic number is used to detect endianness." -/
def bigEndianBytes (ws : List Word) : List Byte := ws.flatMap fun w => (octets w).reverse

/-- Octets "packed four per word", the final word padded with 0 (2.2.1, Literal). -/
def packOctets : List Byte → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => wordOfOctets b0 b1 b2 b3 :: packOctets rest
  | [b0, b1, b2] => [wordOfOctets b0 b1 b2 0]
  | [b0, b1] => [wordOfOctets b0 b1 0 0]
  | [b0] => [wordOfOctets b0 0 0 0]
  | [] => []

/-- A string literal (2.2.1, Literal): "a nul-terminated stream of characters", in "Unicode in the UTF-8 encoding
scheme". -/
structure LiteralString where
  value : String
  /-- None of its UTF-8 octets is the nul-termination character. -/
  noNul : 0 ∉ value.toUTF8.data.toList

/-- 2.2.1, Literal: "The final word contains the string's nul-termination character (0), and all contents past the
end of the string in the final word are padded with 0." -/
def LiteralString.words (s : LiteralString) : List Word :=
  packOctets (s.value.toUTF8.data.toList ++ [0])

end Spec
