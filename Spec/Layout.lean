import Spec.Instruction

/-!
# Where each scalar of a block is

Vulkan specification, Shader Interfaces (https://docs.vulkan.org/spec/latest/chapters/interfaces.html): push constant
blocks must be "laid out explicitly using the Offset, ArrayStride, and MatrixStride decorations as specified in Offset
and Stride Assignment" (Push Constant Interface). So where each scalar is follows from the decorations alone; the
layout rules (std430 and the others) only constrain which decorations are valid.

SPIR-V specification, version 1.6, revision 8: 3.2.19 Decoration, Offset: "It dictates the byte offset of the member
relative to the beginning of the structure."
-/

namespace Spec

/-- The scalar types spvbind places: integers (OpTypeInt) and floating-point numbers (OpTypeFloat) of a width in
bits. -/
inductive Scalar
  | int (width : Word) (signed : Bool)
  | float (width : Word)
  deriving DecidableEq, Repr

/-- One step of a path: member `index` of a structure, with the structure's name (OpName) and the member's
(OpMemberName). Names are only debug information to SPIR-V (2.15), but they are how C++ reaches each scalar, so a
location includes them. -/
structure Step where
  struct : String
  index : Nat
  member : String
  deriving DecidableEq, Repr

/-- A scalar in a value: `path` selects it, one step per level, and it is `offset` bytes from the start of the
value. -/
structure Location where
  path : List Step
  offset : Nat
  scalar : Scalar
  deriving DecidableEq, Repr

/-- `Located m type l`: in a value of `type`, the scalar that `l.path` selects has type `l.scalar` and is `l.offset`
bytes from the start of the value. -/
inductive Located (m : Module) : Id → Location → Prop
  /-- An integer type with Signedness 0 is an unsigned scalar, at the start of the value. -/
  | unsigned {type width : Word} :
      .typeInt type width 0 ∈ m.instructions → Located m type ⟨[], 0, .int width false⟩
  /-- An integer type with Signedness 1 is a signed scalar, at the start of the value. -/
  | signed {type width : Word} :
      .typeInt type width 1 ∈ m.instructions → Located m type ⟨[], 0, .int width true⟩
  /-- A floating-point type is a scalar, at the start of the value. -/
  | float {type width : Word} :
      .typeFloat type width ∈ m.instructions → Located m type ⟨[], 0, .float width⟩
  /-- Member `member` of a structure is `byteOffset` bytes from the start of the structure (Offset), and so is every
  scalar in it, relative to where it is in the member. The step is named by the structure's OpName and the member's
  OpMemberName. -/
  | member {type memberType : Id} {members : List Id} {member byteOffset : Word} {structName memberName : LiteralString}
      {l : Location} :
      .typeStruct type members ∈ m.instructions → members[member.toNat]? = some memberType →
      .memberDecorate type member (.offset byteOffset) ∈ m.instructions →
      .name type structName ∈ m.instructions → .memberName type member memberName ∈ m.instructions →
      Located m memberType l →
      Located m type
        ⟨⟨structName.value, member.toNat, memberName.value⟩ :: l.path, byteOffset.toNat + l.offset, l.scalar⟩

/-- `VariableLocated m v l`: the same, in the object that variable `v` points to. OpVariable (3.3.8): "Result Type
must be an OpTypePointer. Its Type operand is the type of object in memory." -/
inductive VariableLocated (m : Module) (v : Id) (l : Location) : Prop
  | mk {pointer type : Id} {storageClass pointerStorageClass : Word} {initializer : Option Id} :
      .var pointer v storageClass initializer ∈ m.instructions →
      .typePointer pointer pointerStorageClass type ∈ m.instructions → Located m type l → VariableLocated m v l

/-- `PushConstantVariable m v`: `v` is a variable "for holding push-constant memory" (3.2.6, Storage Class,
PushConstant), an OpVariable with storage class PushConstant. -/
def PushConstantVariable (m : Module) (v : Id) : Prop :=
  ∃ (pointer : Id) (initializer : Option Id), .var pointer v PushConstant initializer ∈ m.instructions

end Spec
