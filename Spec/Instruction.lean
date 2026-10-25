import Spec.Binary

/-!
# Instructions and modules

SPIR-V specification, version 1.6, revision 8 (https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html):
2.3 Physical Layout of a SPIR-V Module and Instruction, 3.2 Enumerants, 3.3 Instructions.
-/

namespace Spec

/-- Opcode enumerants (3.3.2, Debug Instructions; 3.3.3, Annotation Instructions; 3.3.6, Type-Declaration
Instructions; 3.3.8, Memory Instructions). -/
def OpName : UInt16 := 5
def OpMemberName : UInt16 := 6
def OpTypeInt : UInt16 := 21
def OpTypeFloat : UInt16 := 22
def OpTypeStruct : UInt16 := 30
def OpTypePointer : UInt16 := 32
def OpVariable : UInt16 := 59
def OpMemberDecorate : UInt16 := 72

/-- The opcode enumerants of the instructions modelled by `Instruction`. -/
def modelled : List UInt16 :=
  [OpName, OpMemberName, OpTypeInt, OpTypeFloat, OpTypeStruct, OpTypePointer, OpVariable, OpMemberDecorate]

/-- Storage class enumerants (3.2.6, Storage Class). -/
def PushConstant : Word := 9

/-- Decoration enumerants (3.2.19, Decoration). -/
def Offset : Word := 35

/-- The decoration enumerants modelled by `Decoration`. -/
def modelledDecorations : List Word := [Offset]

/-- 3.2.19 Decoration: those spvbind reads, with their extra operands, and every other decoration. -/
inductive Decoration
  /-- Offset: "It dictates the byte offset of the member relative to the beginning of the structure." -/
  | offset (byteOffset : Word)
  /-- A decoration with any other enumerant, its extra operands as words. -/
  | other (enumerant : Word) (operands : List Word) (unmodelled : enumerant ∉ modelledDecorations)

/-- The decoration's enumerant followed by its extra operands (3.2.19). -/
def Decoration.words : Decoration → List Word
  | .offset byteOffset => [Offset, byteOffset]
  | .other enumerant operands _ => enumerant :: operands

/-- 3.3 Instructions: those spvbind reads, with their operands, and every other instruction. -/
inductive Instruction
  /-- OpName (3.3.2): "Assign a name string to another instruction's Result <id>." -/
  | name (target : Id) (name : LiteralString)
  /-- OpMemberName (3.3.2): "Assign a name string to a member of a structure type." -/
  | memberName (type : Id) (member : Word) (name : LiteralString)
  /-- OpTypeInt (3.3.6): "Declare a new integer type." Signedness "0 indicates unsigned, or no signedness
  semantics; 1 indicates signed semantics". -/
  | typeInt (result : Id) (width : Word) (signedness : Word)
  /-- OpTypeFloat (3.3.6): "Declare a new floating-point type." Without its optional Floating Point Encoding
  operand, which spvbind does not model, so that a module using it is not decoded. -/
  | typeFloat (result : Id) (width : Word)
  /-- OpTypeStruct (3.3.6): "Declare a new structure type. Member N type is the type of member N of the
  structure." -/
  | typeStruct (result : Id) (members : List Id)
  /-- OpTypePointer (3.3.6): "Declare a new pointer type." -/
  | typePointer (result : Id) (storageClass : Word) (type : Id)
  /-- OpVariable (3.3.8): "Allocate an object in memory, resulting in a pointer to it." Initializer is optional. -/
  | var (resultType : Id) (result : Id) (storageClass : Word) (initializer : Option Id)
  /-- OpMemberDecorate (3.3.3): "Add a Decoration to a member of a structure type." -/
  | memberDecorate (structureType : Id) (member : Word) (decoration : Decoration)
  /-- An instruction with any other opcode enumerant, its operands as words. -/
  | other (enumerant : UInt16) (operands : List Word) (unmodelled : enumerant ∉ modelled)

def Instruction.enumerant : Instruction → UInt16
  | .name .. => OpName
  | .memberName .. => OpMemberName
  | .typeInt .. => OpTypeInt
  | .typeFloat .. => OpTypeFloat
  | .typeStruct .. => OpTypeStruct
  | .typePointer .. => OpTypePointer
  | .var .. => OpVariable
  | .memberDecorate .. => OpMemberDecorate
  | .other enumerant .. => enumerant

/-- The words after the first (2.3, Table 2), in the order 3.3 gives them. -/
def Instruction.operands : Instruction → List Word
  | .name target s => target :: s.words
  | .memberName type member s => type :: member :: s.words
  | .typeInt result width signedness => [result, width, signedness]
  | .typeFloat result width => [result, width]
  | .typeStruct result members => result :: members
  | .typePointer result storageClass type => [result, storageClass, type]
  | .var resultType result storageClass initializer => [resultType, result, storageClass] ++ initializer.toList
  | .memberDecorate structureType member decoration => structureType :: member :: decoration.words
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
