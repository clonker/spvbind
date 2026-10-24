import Spec.Binary

/-!
# Instructions and modules

SPIR-V specification, version 1.6, revision 8 (https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html):
2.3 Physical Layout of a SPIR-V Module and Instruction, 3.3 Instructions.
-/

namespace Spec

/-- Opcode enumerants (3.3.2, Debug Instructions). -/
def OpName : UInt16 := 5
def OpMemberName : UInt16 := 6

/-- The opcode enumerants of the instructions modelled by `Instruction`. -/
def modelled : List UInt16 := [OpName, OpMemberName]

/-- 3.3 Instructions: those spvbind reads, with their operands, and every other instruction. -/
inductive Instruction
  /-- OpName (3.3.2): "Assign a name string to another instruction's Result <id>." -/
  | name (target : Id) (name : LiteralString)
  /-- OpMemberName (3.3.2): "Assign a name string to a member of a structure type." -/
  | memberName (type : Id) (member : Word) (name : LiteralString)
  /-- An instruction with any other opcode enumerant, its operands as words. -/
  | other (enumerant : UInt16) (operands : List Word) (unmodelled : enumerant ∉ modelled)

def Instruction.enumerant : Instruction → UInt16
  | .name .. => OpName
  | .memberName .. => OpMemberName
  | .other enumerant .. => enumerant

/-- The words after the first (2.3, Table 2), in the order 3.3 gives them. -/
def Instruction.operands : Instruction → List Word
  | .name target s => target :: s.words
  | .memberName type member s => type :: member :: s.words
  | .other _ operands _ => operands

/-- The WordCount, which counts all words of the instruction, is 16 bits (2.3, Table 2). -/
def Instruction.Fits (i : Instruction) : Prop := i.operands.length + 1 < 2 ^ 16

/-- 2.3, Table 2. Instruction Physical Layout. -/
def Instruction.words (i : Instruction) : List Word :=
  -- 0: Opcode: the 16 high-order bits are the WordCount of the instruction, the 16 low-order bits are the opcode
  -- enumerant
  ((i.operands.length + 1).toUInt32 <<< 16 ||| i.enumerant.toUInt32) :: i.operands

/-- 2.3: a module is a single linear stream of words, the first words of Table 1 followed by a linear sequence of
instructions. -/
structure Module where
  header : Header
  instructions : List Instruction

def Module.words (m : Module) : List Word :=
  m.header.words ++ m.instructions.flatMap Instruction.words

end Spec
