import Spec.Instruction
import Spvbind.Binary

/-!
# Decoding literal strings, instructions and modules
-/

namespace Spvbind

open Spec (Word Byte octets LiteralString RowMajor ColMajor ArrayStride MatrixStride Offset modelledDecorations
  Decoration OpName OpMemberName OpTypeInt OpTypeFloat OpTypeVector OpTypeMatrix OpTypeArray OpTypeStruct OpTypePointer
  OpConstant OpVariable OpDecorate OpMemberDecorate modelled Instruction Module)

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
    if e = RowMajor then
      match ops with
      | [] => .ok .rowMajor
      | _ => .error "RowMajor decoration with operands"
    else if e = ColMajor then
      match ops with
      | [] => .ok .colMajor
      | _ => .error "ColMajor decoration with operands"
    else if e = ArrayStride then
      match ops with
      | [stride] => .ok (.arrayStride stride)
      | _ => .error "ArrayStride decoration without exactly one operand"
    else if e = MatrixStride then
      match ops with
      | [stride] => .ok (.matrixStride stride)
      | _ => .error "MatrixStride decoration without exactly one operand"
    else if e = Offset then
      match ops with
      | [byteOffset] => .ok (.offset byteOffset)
      | _ => .error "Offset decoration without exactly one operand"
    else if h : e ∈ modelledDecorations then .error s!"decoration {e} is modelled but not decoded"
    else .ok (.other e ops h)

/-! The operands of each modelled instruction, one function each, so that `decodeOperands` stays a chain of small
branches that proofs can split. -/

def decodeName : List Word → Except String Instruction
  | target :: rest =>
    match decodeString rest with
    | .ok (s, []) => .ok (.name target s)
    | .ok (_, _ :: _) => .error "OpName has operands after its name"
    | .error e => .error e
  | [] => .error "OpName without operands"

def decodeMemberName : List Word → Except String Instruction
  | type :: member :: rest =>
    match decodeString rest with
    | .ok (s, []) => .ok (.memberName type member s)
    | .ok (_, _ :: _) => .error "OpMemberName has operands after its name"
    | .error e => .error e
  | _ => .error "OpMemberName with fewer than three operands"

def decodeTypeInt : List Word → Except String Instruction
  | [result, width, signedness] => .ok (.typeInt result width signedness)
  | _ => .error "OpTypeInt without exactly three operands"

def decodeTypeFloat : List Word → Except String Instruction
  | [result, width] => .ok (.typeFloat result width)
  | _ => .error "OpTypeFloat without exactly two operands; the Floating Point Encoding operand is not supported"

def decodeTypeVector : List Word → Except String Instruction
  | [result, componentType, componentCount] => .ok (.typeVector result componentType componentCount)
  | _ => .error "OpTypeVector without exactly three operands"

def decodeTypeMatrix : List Word → Except String Instruction
  | [result, columnType, columnCount] => .ok (.typeMatrix result columnType columnCount)
  | _ => .error "OpTypeMatrix without exactly three operands"

def decodeTypeArray : List Word → Except String Instruction
  | [result, elementType, length] => .ok (.typeArray result elementType length)
  | _ => .error "OpTypeArray without exactly three operands"

def decodeTypeStruct : List Word → Except String Instruction
  | result :: members => .ok (.typeStruct result members)
  | [] => .error "OpTypeStruct without operands"

def decodeTypePointer : List Word → Except String Instruction
  | [result, storageClass, type] => .ok (.typePointer result storageClass type)
  | _ => .error "OpTypePointer without exactly three operands"

def decodeConstant : List Word → Except String Instruction
  | resultType :: result :: value :: more => .ok (.constant resultType result value more)
  | _ => .error "OpConstant with fewer than three operands"

def decodeVariable : List Word → Except String Instruction
  | [resultType, result, storageClass] => .ok (.var resultType result storageClass none)
  | [resultType, result, storageClass, initializer] => .ok (.var resultType result storageClass (some initializer))
  | _ => .error "OpVariable without three or four operands"

def decodeDecorate : List Word → Except String Instruction
  | target :: rest =>
    match decodeDecoration rest with
    | .ok d => .ok (.decorate target d)
    | .error e => .error e
  | [] => .error "OpDecorate without operands"

def decodeMemberDecorate : List Word → Except String Instruction
  | type :: member :: rest =>
    match decodeDecoration rest with
    | .ok d => .ok (.memberDecorate type member d)
    | .error e => .error e
  | _ => .error "OpMemberDecorate with fewer than three operands"

/-- The instruction with opcode enumerant `e` and operands `ops`. -/
def decodeOperands (e : UInt16) (ops : List Word) : Except String Instruction :=
  if e = OpName then decodeName ops
  else if e = OpMemberName then decodeMemberName ops
  else if e = OpTypeInt then decodeTypeInt ops
  else if e = OpTypeFloat then decodeTypeFloat ops
  else if e = OpTypeVector then decodeTypeVector ops
  else if e = OpTypeMatrix then decodeTypeMatrix ops
  else if e = OpTypeArray then decodeTypeArray ops
  else if e = OpTypeStruct then decodeTypeStruct ops
  else if e = OpTypePointer then decodeTypePointer ops
  else if e = OpConstant then decodeConstant ops
  else if e = OpVariable then decodeVariable ops
  else if e = OpDecorate then decodeDecorate ops
  else if e = OpMemberDecorate then decodeMemberDecorate ops
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

/-- `decodeInstructions`, iteratively, which the compiler uses instead (`@[csimp]`, see `Spvbind/Binary.lean`). -/
def decodeInstructionsTR (ws : List Word) : Except String (List Instruction) := go ws #[]
where
  go : List Word → Array Instruction → Except String (List Instruction)
    | [], acc => .ok acc.toList
    | w :: ws, acc =>
      if (w >>> 16).toNat = 0 then .error s!"instruction with opcode enumerant {w.toUInt16} has word count 0"
      else if (ws.take ((w >>> 16).toNat - 1)).length < (w >>> 16).toNat - 1 then
        .error s!"instruction with opcode enumerant {w.toUInt16} has word count {(w >>> 16).toNat}, past the end of \
          the module"
      else
        match decodeOperands w.toUInt16 (ws.take ((w >>> 16).toNat - 1)) with
        | .ok i => go (ws.drop ((w >>> 16).toNat - 1)) (acc.push i)
        | .error e => .error e
  termination_by ws _ => ws.length

theorem decodeInstructionsTR_go (ws : List Word) (acc : Array Instruction) :
    decodeInstructionsTR.go ws acc = (acc.toList ++ ·) <$> decodeInstructions ws := by
  fun_induction decodeInstructionsTR.go ws acc with
  | case1 acc => simp [decodeInstructions, Functor.map, Except.map]
  | case2 w ws acc h0 => rw [decodeInstructions]; simp only [h0, ↓reduceIte, Functor.map, Except.map]
  | case3 w ws acc h0 hlen => rw [decodeInstructions]; simp only [h0, hlen, ↓reduceIte, Functor.map, Except.map]
  | case4 w ws acc h0 hlen i hop ih =>
    rw [decodeInstructions]
    simp only [h0, hlen, hop, ↓reduceIte, ih]
    cases decodeInstructions (ws.drop ((w >>> 16).toNat - 1)) <;> simp [Functor.map, Except.map]
  | case5 w ws acc h0 hlen e he => rw [decodeInstructions]; simp only [h0, hlen, he, ↓reduceIte, Functor.map, Except.map]

@[csimp] theorem decodeInstructions_eq_decodeInstructionsTR : @decodeInstructions = @decodeInstructionsTR := by
  funext ws
  cases h : decodeInstructions ws <;> simp [decodeInstructionsTR, decodeInstructionsTR_go, h, Functor.map, Except.map]

/-- The module a stream of words consists of. -/
def decode (ws : List Word) : Except String Module := do
  let (header, rest) ← decodeHeader ws
  return { header, instructions := ← decodeInstructions rest }

end Spvbind
