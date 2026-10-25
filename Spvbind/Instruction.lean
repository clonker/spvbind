import Spec.Instruction
import Spvbind.Binary

/-!
# Decoding literal strings, instructions and modules
-/

namespace Spvbind

open Spec (Word Byte LiteralString Offset modelledDecorations Decoration OpName OpMemberName OpTypeInt OpTypeFloat
  OpTypeStruct OpTypePointer OpVariable OpMemberDecorate modelled Instruction Module)

/-- The four octets of a word, the first from the lowest-order 8 bits. -/
def octets (w : Word) : List Byte :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- A literal string at the start of `ws`, and the words after it. The octets up to the first 0 are the string; the
words it was read from must be exactly the string's words, which also checks the padding. -/
def decodeString (ws : List Word) : Except String (LiteralString × List Word) :=
  let os := ws.flatMap octets
  let bytes := os.takeWhile (· != 0)
  if bytes.length = os.length then .error "literal string without nul-termination character"
  else if valid : ByteArray.IsValidUTF8 ⟨bytes.toArray⟩ then
    let s : LiteralString := ⟨.ofByteArray ⟨bytes.toArray⟩ valid, fun h => by
      have := List.all_eq_true.mp (List.all_takeWhile (p := (· != 0)) (l := os)) 0
        (by simpa [String.toUTF8_eq_toByteArray, bytes] using h)
      simp at this⟩
    if ws.take s.words.length = s.words then .ok (s, ws.drop s.words.length)
    else .error "literal string not padded with 0"
  else .error "literal string is not valid UTF-8"

/-- The decoration a decoration's enumerant and extra operands encode. -/
def decodeDecoration : List Word → Except String Decoration
  | [] => .error "decoration without enumerant"
  | e :: ops =>
    if e = Offset then
      match ops with
      | [byteOffset] => .ok (.offset byteOffset)
      | _ => .error "Offset decoration without exactly one operand"
    else if h : e ∈ modelledDecorations then .error s!"decoration {e} is modelled but not decoded"
    else .ok (.other e ops h)

/-- The instruction with opcode enumerant `e` and operands `ops`. -/
def decodeOperands (e : UInt16) (ops : List Word) : Except String Instruction :=
  if e = OpName then
    match ops with
    | target :: rest =>
      match decodeString rest with
      | .ok (s, []) => .ok (.name target s)
      | .ok (_, _ :: _) => .error "OpName has operands after its name"
      | .error e => .error e
    | [] => .error "OpName without operands"
  else if e = OpMemberName then
    match ops with
    | type :: member :: rest =>
      match decodeString rest with
      | .ok (s, []) => .ok (.memberName type member s)
      | .ok (_, _ :: _) => .error "OpMemberName has operands after its name"
      | .error e => .error e
    | _ => .error "OpMemberName with fewer than three operands"
  else if e = OpTypeInt then
    match ops with
    | [result, width, signedness] => .ok (.typeInt result width signedness)
    | _ => .error "OpTypeInt without exactly three operands"
  else if e = OpTypeFloat then
    match ops with
    | [result, width] => .ok (.typeFloat result width)
    | _ => .error "OpTypeFloat without exactly two operands; the Floating Point Encoding operand is not supported"
  else if e = OpTypeStruct then
    match ops with
    | result :: members => .ok (.typeStruct result members)
    | [] => .error "OpTypeStruct without operands"
  else if e = OpTypePointer then
    match ops with
    | [result, storageClass, type] => .ok (.typePointer result storageClass type)
    | _ => .error "OpTypePointer without exactly three operands"
  else if e = OpVariable then
    match ops with
    | [resultType, result, storageClass] => .ok (.var resultType result storageClass none)
    | [resultType, result, storageClass, initializer] => .ok (.var resultType result storageClass (some initializer))
    | _ => .error "OpVariable without three or four operands"
  else if e = OpMemberDecorate then
    match ops with
    | type :: member :: rest =>
      match decodeDecoration rest with
      | .ok d => .ok (.memberDecorate type member d)
      | .error e => .error e
    | _ => .error "OpMemberDecorate with fewer than three operands"
  else if h : e ∈ modelled then .error s!"opcode enumerant {e} is modelled but not decoded"
  else .ok (.other e ops h)

/-- The instructions a stream of words consists of. The words left are not counted, which would take time quadratic in
the size of the module; only the operands taken are. -/
def decodeInstructions : List Word → Except String (List Instruction)
  | [] => .ok []
  | w :: ws =>
    if (w >>> 16).toNat = 0 then .error s!"instruction with opcode enumerant {w.toUInt16} has word count 0"
    else if (ws.take ((w >>> 16).toNat - 1)).length < (w >>> 16).toNat - 1 then
      .error s!"instruction with opcode enumerant {w.toUInt16} has word count {(w >>> 16).toNat}, past the end of \
        the module"
    else
      match decodeOperands w.toUInt16 (ws.take ((w >>> 16).toNat - 1)) with
      | .ok i => (i :: ·) <$> decodeInstructions (ws.drop ((w >>> 16).toNat - 1))
      | .error e => .error e
termination_by ws => ws.length

/-- The module a stream of words consists of. -/
def decode (ws : List Word) : Except String Module := do
  let (header, rest) ← decodeHeader ws
  return { header, instructions := ← decodeInstructions rest }

end Spvbind
