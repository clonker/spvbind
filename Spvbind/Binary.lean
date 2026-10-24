import Spec.Binary

/-!
# Decoding words and the header of a module
-/

namespace Spvbind

open Spec (Word Byte magic Header)

/-- The word with its four bytes in reverse order. -/
def byteReverse (w : Word) : Word :=
  (w >>> 24) ||| ((w >>> 8) &&& (0xff00 : Word)) ||| ((w <<< 8) &&& (0xff0000 : Word)) ||| (w <<< 24)

/-- The little-endian words of `bytes`, if its size is a multiple of 4. -/
def littleEndianWords (bytes : ByteArray) : Option (Array Word) :=
  if bytes.size % 4 = 0 then
    some <| Array.ofFn fun (i : Fin (bytes.size / 4)) =>
      let byte (k : Fin 4) : Word := (bytes[4 * i.val + k.val]'(by omega) : Byte).toUInt32
      byte 0 ||| byte 1 <<< 8 ||| byte 2 <<< 16 ||| byte 3 <<< 24
  else
    none

/-- The words of a module stored as bytes, in the byte order its magic number is in. A module is a stream of words,
not of bytes; how to store it is only a tip (3.1, Endianness). Whether there is a magic number at all is left to
`decodeHeader`. -/
def words (bytes : ByteArray) : Except String (List Word) := do
  let some ws := littleEndianWords bytes
    | throw s!"size {bytes.size} is not a multiple of 4"
  if ws[0]? = some (byteReverse magic) then return (ws.map byteReverse).toList
  else return ws.toList

/-- The header and the words after it. -/
def decodeHeader : List Word → Except String (Header × List Word)
  | m :: version :: generator :: bound :: schema :: rest =>
    if m ≠ magic then throw "no SPIR-V magic number"
    else if schema ≠ 0 then throw s!"unknown schema {schema}"
    else return ({ version, generator, bound }, rest)
  | ws => throw s!"{ws.length} words is shorter than the header"

end Spvbind
