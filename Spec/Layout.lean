import Spec.Instruction

/-!
# Where each scalar of a block is

Vulkan specification, Shader Interfaces (https://docs.vulkan.org/spec/latest/chapters/interfaces.html): push constant
blocks must be "laid out explicitly using the Offset, ArrayStride, and MatrixStride decorations as specified in Offset
and Stride Assignment" (Push Constant Interface). So where each scalar is follows from the decorations alone; the
layout rules (std430 and the others) only constrain which decorations are valid.

SPIR-V specification, version 1.6, revision 8: 3.2.19 Decoration, Offset: "It dictates the byte offset of the member
relative to the beginning of the structure." ArrayStride: "the stride, in bytes, of the array's elements" (Vulkan: "Any
ArrayStride ... decoration must be a multiple of the alignment of the array"). Vectors have no decoration: their
components follow each other, each the size of the component type (Vulkan, Offset and Stride Assignment: a vector "has
a scalar alignment equal to that of its component type"). Matrices are laid out by decorations of the structure member
they are in, through any arrays: MatrixStride, "the stride of the rows in a RowMajor-decorated matrix or columns in a
ColMajor-decorated matrix" (3.2.19), where (Vulkan, Offset and Stride Assignment) "A column-major matrix with C columns
and R rows is equivalent to a C element array of vectors with R components. A row-major matrix with C columns and R rows
is equivalent to an R element array of vectors with C components."
-/

namespace Spec

/-- The scalar types spvbind places: integers (OpTypeInt) and floating-point numbers (OpTypeFloat) of a width in
bits. -/
inductive Scalar
  | int (width : Word) (signed : Bool)
  | float (width : Word)
  deriving DecidableEq, Repr

/-- The size of a scalar in bytes, its width in bits divided by 8 (Vulkan, Offset and Stride Assignment: "A scalar of
size N"). -/
def Scalar.bytes : Scalar → Nat
  | .int width _ => width.toNat / 8
  | .float width => width.toNat / 8

/-- One step of a path: member `index` of a structure, with the structure's name (OpName) and the member's
(OpMemberName), or element `index` of a vector. Names are only debug information to SPIR-V (2.15), but they are how C++
reaches each scalar, so a location includes them. -/
inductive Step
  | member (struct : String) (index : Nat) (name : String)
  | element (index : Nat)
  deriving DecidableEq, Repr

/-- A scalar in a value: `path` selects it, one step per level, and it is `offset` bytes from the start of the
value. -/
structure Location where
  path : List Step
  offset : Nat
  scalar : Scalar
  deriving DecidableEq, Repr

/-- How the matrices of a structure member are laid out (3.2.19): the MatrixStride, and whether it is the stride of
rows (RowMajor) or of columns (ColMajor). -/
structure MatrixLayout where
  stride : Word
  rowMajor : Bool
  deriving DecidableEq, Repr

/-- `MemberLayout m type member layout`: the decorations of member `member` of structure `type` give its matrices the
layout `layout`: none without a MatrixStride, otherwise the stride with RowMajor or with ColMajor. -/
inductive MemberLayout (m : Module) (type : Id) (member : Word) : Option MatrixLayout → Prop
  | none : (∀ stride, .memberDecorate type member (.matrixStride stride) ∉ m.instructions) →
      MemberLayout m type member none
  | rowMajor {stride : Word} :
      .memberDecorate type member (.matrixStride stride) ∈ m.instructions →
      .memberDecorate type member .rowMajor ∈ m.instructions → MemberLayout m type member (some ⟨stride, true⟩)
  | colMajor {stride : Word} :
      .memberDecorate type member (.matrixStride stride) ∈ m.instructions →
      .memberDecorate type member .colMajor ∈ m.instructions → MemberLayout m type member (some ⟨stride, false⟩)

/-- `Located m layout type l`: in a value of `type` whose matrices, if any, are laid out as `layout` says (that of the
structure member the value is in, through any arrays), the scalar that `l.path` selects has type `l.scalar` and is
`l.offset` bytes from the start of the value. -/
inductive Located (m : Module) : Option MatrixLayout → Id → Location → Prop
  /-- An integer type with Signedness 0 is an unsigned scalar, at the start of the value. -/
  | unsigned {layout : Option MatrixLayout} {type width : Word} :
      .typeInt type width 0 ∈ m.instructions → Located m layout type ⟨[], 0, .int width false⟩
  /-- An integer type with Signedness 1 is a signed scalar, at the start of the value. -/
  | signed {layout : Option MatrixLayout} {type width : Word} :
      .typeInt type width 1 ∈ m.instructions → Located m layout type ⟨[], 0, .int width true⟩
  /-- A floating-point type is a scalar, at the start of the value. -/
  | float {layout : Option MatrixLayout} {type width : Word} :
      .typeFloat type width ∈ m.instructions → Located m layout type ⟨[], 0, .float width⟩
  /-- Member `member` of a structure is `byteOffset` bytes from the start of the structure (Offset), and so is every
  scalar in it, relative to where it is in the member, whose matrices the member's own decorations lay out. The step
  is named by the structure's OpName and the member's OpMemberName. -/
  | member {layout memberLayout : Option MatrixLayout} {type memberType : Id} {members : List Id}
      {member byteOffset : Word} {structName memberName : LiteralString} {l : Location} :
      .typeStruct type members ∈ m.instructions → members[member.toNat]? = some memberType →
      .memberDecorate type member (.offset byteOffset) ∈ m.instructions →
      .name type structName ∈ m.instructions → .memberName type member memberName ∈ m.instructions →
      MemberLayout m type member memberLayout → Located m memberLayout memberType l →
      Located m layout type
        ⟨.member structName.value member.toNat memberName.value :: l.path, byteOffset.toNat + l.offset, l.scalar⟩
  /-- Component `component` of a vector is a scalar of the component type, `component` times its size from the start
  of the vector. -/
  | component {layout : Option MatrixLayout} {type componentType : Id} {count component : Word} {s : Scalar} :
      .typeVector type componentType count ∈ m.instructions → component < count →
      Located m layout componentType ⟨[], 0, s⟩ →
      Located m layout type ⟨[.element component.toNat], component.toNat * s.bytes, s⟩
  /-- Element `i` of an array, for `i` below its Length, a constant, is `i` times the array's ArrayStride from the
  start of the array, and so is every scalar in it, relative to where it is in the element. -/
  | element {layout : Option MatrixLayout} {type elementType length lengthType : Id} {value stride : Word}
      {more : List Word} {i : Nat} {l : Location} :
      .typeArray type elementType length ∈ m.instructions →
      .constant lengthType length value more ∈ m.instructions → i < wordsValue value more →
      .decorate type (.arrayStride stride) ∈ m.instructions →
      Located m layout elementType l →
      Located m layout type ⟨.element i :: l.path, i * stride.toNat + l.offset, l.scalar⟩
  /-- A column-major matrix is an array of its columns, `stride` apart, each a vector of the rows: component `row` of
  column `column` is a scalar of the column vector's component type, at `column` strides plus `row` scalar sizes.
  The path takes the column first, as the memory does. -/
  | colMajor {type columnType componentType : Id} {columns rows column row stride : Word} {s : Scalar} :
      .typeMatrix type columnType columns ∈ m.instructions → column < columns →
      .typeVector columnType componentType rows ∈ m.instructions → row < rows →
      Located m (some ⟨stride, false⟩) componentType ⟨[], 0, s⟩ →
      Located m (some ⟨stride, false⟩) type
        ⟨[.element column.toNat, .element row.toNat], column.toNat * stride.toNat + row.toNat * s.bytes, s⟩
  /-- A row-major matrix is an array of its rows, `stride` apart, each a vector of the columns: component `column` of
  row `row` is at `row` strides plus `column` scalar sizes. The path takes the row first, as the memory does. -/
  | rowMajor {type columnType componentType : Id} {columns rows column row stride : Word} {s : Scalar} :
      .typeMatrix type columnType columns ∈ m.instructions → column < columns →
      .typeVector columnType componentType rows ∈ m.instructions → row < rows →
      Located m (some ⟨stride, true⟩) componentType ⟨[], 0, s⟩ →
      Located m (some ⟨stride, true⟩) type
        ⟨[.element row.toNat, .element column.toNat], row.toNat * stride.toNat + column.toNat * s.bytes, s⟩

/-- `VariableLocated m v l`: the same, in the object that variable `v` points to, which is in no structure member.
OpVariable (3.3.8): "Result Type must be an OpTypePointer. Its Type operand is the type of object in memory." -/
inductive VariableLocated (m : Module) (v : Id) (l : Location) : Prop
  | mk {pointer type : Id} {storageClass pointerStorageClass : Word} {initializer : Option Id} :
      .var pointer v storageClass initializer ∈ m.instructions →
      .typePointer pointer pointerStorageClass type ∈ m.instructions → Located m none type l → VariableLocated m v l

/-- `PushConstantVariable m v`: `v` is a variable "for holding push-constant memory" (3.2.6, Storage Class,
PushConstant), an OpVariable with storage class PushConstant. -/
def PushConstantVariable (m : Module) (v : Id) : Prop :=
  ∃ (pointer : Id) (initializer : Option Id), .var pointer v PushConstant initializer ∈ m.instructions

end Spec
