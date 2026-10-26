import Spec.Binary

/-!
# Instructions and modules

SPIR-V specification, version 1.6, revision 8 (https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html):
2.3 Physical Layout of a SPIR-V Module and Instruction, 3.2 Enumerants, 3.3 Instructions.
-/

namespace Spec

/-- Opcode enumerants (3.3.2, Debug Instructions; 3.3.3, Annotation Instructions; 3.3.6, Type-Declaration
Instructions; 3.3.7, Constant-Creation Instructions; 3.3.8, Memory Instructions). -/
def OpName : UInt16 := 5
def OpMemberName : UInt16 := 6
def OpTypeInt : UInt16 := 21
def OpTypeFloat : UInt16 := 22
def OpTypeVector : UInt16 := 23
def OpTypeArray : UInt16 := 28
def OpTypeStruct : UInt16 := 30
def OpTypePointer : UInt16 := 32
def OpConstant : UInt16 := 43
def OpVariable : UInt16 := 59
def OpDecorate : UInt16 := 71
def OpMemberDecorate : UInt16 := 72

/-- The opcode enumerants of the instructions modelled by `Instruction`. -/
def modelled : List UInt16 :=
  [OpName, OpMemberName, OpTypeInt, OpTypeFloat, OpTypeVector, OpTypeArray, OpTypeStruct, OpTypePointer, OpConstant,
   OpVariable, OpDecorate, OpMemberDecorate]

/-- Storage class enumerants (3.2.6, Storage Class). -/
def PushConstant : Word := 9

/-- Decoration enumerants (3.2.19, Decoration). -/
def ArrayStride : Word := 6
def Offset : Word := 35

/-- The decoration enumerants modelled by `Decoration`. -/
def modelledDecorations : List Word := [ArrayStride, Offset]

/-- 3.2.19 Decoration: those spvbind reads, with their extra operands, and every other decoration. -/
inductive Decoration
  /-- ArrayStride: "Apply to an array type to specify the stride, in bytes, of the array's elements." -/
  | arrayStride (stride : Word)
  /-- Offset: "It dictates the byte offset of the member relative to the beginning of the structure." -/
  | offset (byteOffset : Word)
  /-- A decoration with any other enumerant, its extra operands as words. -/
  | other (enumerant : Word) (operands : List Word) (unmodelled : enumerant ∉ modelledDecorations)

/-- The decoration's enumerant followed by its extra operands (3.2.19). -/
def Decoration.words : Decoration → List Word
  | .arrayStride stride => [ArrayStride, stride]
  | .offset byteOffset => [Offset, byteOffset]
  | .other enumerant operands _ => enumerant :: operands

/-- The value of the words of an OpConstant (3.3.7): "Types 32 bits wide or smaller take one word. Larger types take
multiple words, with low-order words appearing first." -/
def wordsValue (value : Word) : List Word → Nat
  | [] => value.toNat
  | w :: ws => value.toNat + 2 ^ 32 * wordsValue w ws

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
  /-- OpTypeVector (3.3.6): "Declare a new vector type. Component Type is the type of each component in the resulting
  type. It must be a scalar type. Component Count is the number of components in the resulting type. It must be at
  least 2." -/
  | typeVector (result : Id) (componentType : Id) (componentCount : Word)
  /-- OpTypeArray (3.3.6): "Declare a new array type: a dynamically-indexable ordered aggregate of elements all having
  the same type. Element Type is the type of each element in the array. ... Length is the number of elements in the
  array. It must be an <id> of a constant instruction of scalar integer type, with a value of at least 1." -/
  | typeArray (result : Id) (elementType : Id) (length : Id)
  /-- OpTypeStruct (3.3.6): "Declare a new structure type. Member N type is the type of member N of the
  structure." -/
  | typeStruct (result : Id) (members : List Id)
  /-- OpTypePointer (3.3.6): "Declare a new pointer type." -/
  | typePointer (result : Id) (storageClass : Word) (type : Id)
  /-- OpConstant (3.3.7): "Declare a new integer-type or floating-point-type scalar constant. ... Value is the bit
  pattern for the constant." One word at least, see `wordsValue`. -/
  | constant (resultType : Id) (result : Id) (value : Word) (more : List Word)
  /-- OpVariable (3.3.8): "Allocate an object in memory, resulting in a pointer to it." Initializer is optional. -/
  | var (resultType : Id) (result : Id) (storageClass : Word) (initializer : Option Id)
  /-- OpDecorate (3.3.3): "Add a Decoration to another <id>." -/
  | decorate (target : Id) (decoration : Decoration)
  /-- OpMemberDecorate (3.3.3): "Add a Decoration to a member of a structure type." -/
  | memberDecorate (structureType : Id) (member : Word) (decoration : Decoration)
  /-- An instruction with any other opcode enumerant, its operands as words. -/
  | other (enumerant : UInt16) (operands : List Word) (unmodelled : enumerant ∉ modelled)

def Instruction.enumerant : Instruction → UInt16
  | .name .. => OpName
  | .memberName .. => OpMemberName
  | .typeInt .. => OpTypeInt
  | .typeFloat .. => OpTypeFloat
  | .typeVector .. => OpTypeVector
  | .typeArray .. => OpTypeArray
  | .typeStruct .. => OpTypeStruct
  | .typePointer .. => OpTypePointer
  | .constant .. => OpConstant
  | .var .. => OpVariable
  | .decorate .. => OpDecorate
  | .memberDecorate .. => OpMemberDecorate
  | .other enumerant .. => enumerant

/-- The words after the first (2.3, Table 2), in the order 3.3 gives them. -/
def Instruction.operands : Instruction → List Word
  | .name target s => target :: s.words
  | .memberName type member s => type :: member :: s.words
  | .typeInt result width signedness => [result, width, signedness]
  | .typeFloat result width => [result, width]
  | .typeVector result componentType componentCount => [result, componentType, componentCount]
  | .typeArray result elementType length => [result, elementType, length]
  | .typeStruct result members => result :: members
  | .typePointer result storageClass type => [result, storageClass, type]
  | .constant resultType result value more => resultType :: result :: value :: more
  | .var resultType result storageClass initializer => [resultType, result, storageClass] ++ initializer.toList
  | .decorate target decoration => target :: decoration.words
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
