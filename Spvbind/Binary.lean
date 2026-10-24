/-!
# The SPIR-V binary format: words and header

A module is a stream of 32-bit words in either byte order, detected from the magic number; the header is the first
five words, followed by the instructions (SPIR-V specification, 2.3 Physical Layout of a SPIR-V Module).
-/

namespace Spvbind

def magic : UInt32 := 0x07230203

def UInt32.byteSwap (w : UInt32) : UInt32 :=
  (w >>> 24) ||| ((w >>> 8) &&& (0xff00 : UInt32)) ||| ((w <<< 8) &&& (0xff0000 : UInt32)) ||| (w <<< 24)

/-- The little-endian 32-bit words of `bytes`, if its size is a multiple of 4. -/
def littleEndianWords (bytes : ByteArray) : Option (Array UInt32) :=
  if bytes.size % 4 = 0 then
    some <| Array.ofFn fun (i : Fin (bytes.size / 4)) =>
      let byte (k : Nat) (_ : k < 4) : UInt32 := (bytes[4 * i.val + k]'(by have := i.isLt; omega)).toUInt32
      byte 0 (by decide) ||| byte 1 (by decide) <<< 8 ||| byte 2 (by decide) <<< 16 ||| byte 3 (by decide) <<< 24
  else
    none

/-- The words of a module, in the byte order its magic number is in. -/
def words (bytes : ByteArray) : Except String (Array UInt32) := do
  let some ws := littleEndianWords bytes
    | throw s!"size {bytes.size} is not a multiple of 4"
  match ws[0]? with
  | some w =>
    if w = magic then return ws
    else if w = UInt32.byteSwap magic then return ws.map UInt32.byteSwap
    else throw "no SPIR-V magic number"
  | none => throw "empty"

structure Header where
  /-- `0 | major | minor | 0`, from the most to the least significant byte. -/
  version : UInt32
  generator : UInt32
  /-- Every result id is less than the bound. -/
  bound : UInt32
  deriving Repr, DecidableEq

def Header.major (h : Header) : UInt32 := (h.version >>> 16) &&& (0xff : UInt32)

def Header.minor (h : Header) : UInt32 := (h.version >>> 8) &&& (0xff : UInt32)

/-- The header and the index of the first instruction word. -/
def Header.decode (ws : Array UInt32) : Except String (Header × Nat) :=
  match ws[0]?, ws[1]?, ws[2]?, ws[3]?, ws[4]? with
  | some m, some version, some generator, some bound, some schema =>
    if m ≠ magic then throw "no SPIR-V magic number"
    else if schema ≠ 0 then throw s!"unknown schema {schema}"
    else return ({ version, generator, bound }, 5)
  | _, _, _, _, _ => throw s!"{ws.size} words is shorter than the header"

end Spvbind
