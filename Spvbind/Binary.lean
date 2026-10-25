import Spec.Binary

/-!
# Decoding the words and the header of a module
-/

namespace Spvbind

open Spec (Word Byte magic Header wordOfOctets packOctets LiteralString)

/-- The word with its four octets in reverse order. -/
def byteReverse (w : Word) : Word :=
  wordOfOctets (w >>> 24).toUInt8 (w >>> 16).toUInt8 (w >>> 8).toUInt8 w.toUInt8

/-- The words whose octets, each word's lowest-order octet first, are `bytes`, if there are four per word. -/
def wordsOfOctets : List Byte → Option (List Word)
  | b0 :: b1 :: b2 :: b3 :: rest => (wordsOfOctets rest).map (wordOfOctets b0 b1 b2 b3 :: ·)
  | [] => some []
  | [_] | [_, _] | [_, _, _] => none

/-! The recursion of `wordsOfOctets`, of `decodeInstructions` (in `Spvbind/Instruction.lean`) and of
`Spec.packOctets` is as deep as the input is long, which is how the specification reads but not how an oracle should
treat untrusted input. Each gets a twin with an accumulator that the compiler uses instead (`@[csimp]`); the theorems
are about the originals, and Lean checks that the twins agree. -/

/-- `wordsOfOctets`, iteratively. -/
def wordsOfOctetsTR (bs : List Byte) : Option (List Word) := go bs #[]
where
  go : List Byte → Array Word → Option (List Word)
    | b0 :: b1 :: b2 :: b3 :: rest, acc => go rest (acc.push (wordOfOctets b0 b1 b2 b3))
    | [], acc => some acc.toList
    | [_], _ | [_, _], _ | [_, _, _], _ => none

theorem wordsOfOctetsTR_go (bs : List Byte) (acc : Array Word) :
    wordsOfOctetsTR.go bs acc = (wordsOfOctets bs).map (acc.toList ++ ·) := by
  fun_induction wordsOfOctetsTR.go bs acc with
  | case1 b0 b1 b2 b3 rest acc ih =>
    rw [ih]
    simp only [wordsOfOctets]
    cases wordsOfOctets rest <;> simp
  | _ => simp [wordsOfOctets]

@[csimp] theorem wordsOfOctets_eq_wordsOfOctetsTR : @wordsOfOctets = @wordsOfOctetsTR := by
  funext bs
  cases h : wordsOfOctets bs <;> simp [wordsOfOctetsTR, wordsOfOctetsTR_go, h]

/-- `Spec.packOctets`, iteratively. -/
def packOctetsTR (bs : List Byte) : List Word := go bs #[]
where
  go : List Byte → Array Word → List Word
    | b0 :: b1 :: b2 :: b3 :: rest, acc => go rest (acc.push (wordOfOctets b0 b1 b2 b3))
    | [b0, b1, b2], acc => (acc.push (wordOfOctets b0 b1 b2 0)).toList
    | [b0, b1], acc => (acc.push (wordOfOctets b0 b1 0 0)).toList
    | [b0], acc => (acc.push (wordOfOctets b0 0 0 0)).toList
    | [], acc => acc.toList

theorem packOctetsTR_go (bs : List Byte) (acc : Array Word) :
    packOctetsTR.go bs acc = acc.toList ++ packOctets bs := by
  fun_induction packOctetsTR.go bs acc with
  | case1 b0 b1 b2 b3 rest acc ih => simp [ih, packOctets]
  | _ => simp [packOctets]

/-- `Spec.LiteralString.words`, iteratively; the compiled code of `Spec` itself is not affected, only calls from here. -/
def literalStringWordsTR (s : LiteralString) : List Word := packOctetsTR (s.value.toUTF8.data.toList ++ [0])

@[csimp] theorem literalString_words_eq_literalStringWordsTR : @LiteralString.words = @literalStringWordsTR := by
  funext s
  simp [LiteralString.words, literalStringWordsTR, packOctetsTR, packOctetsTR_go]

/-- The words of a module stored as bytes, in the byte order its magic number is in: little-endian, unless the first
word read that way is the magic number with its octets reversed. A module is a stream of words, not of bytes; how to
store it is only a tip (3.1, Endianness). Whether there is a magic number at all is left to `decodeHeader`. -/
def words (bytes : ByteArray) : Except String (List Word) :=
  match wordsOfOctets bytes.toList with
  | none => .error s!"size {bytes.size} is not a multiple of 4"
  | some ws => if ws.head? = some (byteReverse magic) then .ok (ws.map byteReverse) else .ok ws

/-- The header and the words after it. -/
def decodeHeader : List Word → Except String (Header × List Word)
  | m :: version :: generator :: bound :: schema :: rest =>
    if m ≠ magic then throw "no SPIR-V magic number"
    else if schema ≠ 0 then throw s!"unknown schema {schema}"
    else return ({ version, generator, bound }, rest)
  | ws => throw s!"{ws.length} words is shorter than the header"

/-- spvbind reads modules from SPIR-V 1.4 on, whose entry points list every global variable they use, in every
storage class (3.3, `OpEntryPoint`). -/
def checkVersion (h : Header) : Except String Unit :=
  if h.major < 1 ∨ (h.major = 1 ∧ h.minor < 4) then
    throw s!"SPIR-V {h.major}.{h.minor} is not supported, only 1.4 and later"
  else pure ()

end Spvbind
