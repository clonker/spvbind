import Std.Data.HashMap
import Std.Data.HashSet
import Spec.Cpp
import Spvbind.Instruction

/-!
# The C++ types of the push constant blocks of a module

Types are resolved in one pass over the instructions, in order: a type's operands are "declared before being used"
(2.4, Logical Layout of a Module), so the C++ types of a struct's members are known when the struct is reached, and a
type cannot contain itself. Every id spvbind reads must be defined once, and every id and member have at most one
Offset, OpName and OpMemberName, so that each id and member means one thing.
-/

namespace Spvbind

open Spec (Word Id Scalar Instruction Module Decoration PushConstant MatrixLayout)
open Spec.Cpp (Ty Member)
open Std (HashMap HashSet)

/-- Whether the elements of `xs` are distinct, in expected linear time. -/
def distinct {α : Type} [BEq α] [Hashable α] (xs : List α) : Bool := go ∅ xs
where
  go (seen : HashSet α) : List α → Bool
    | [] => true
    | x :: xs => !seen.contains x && go (seen.insert x) xs

/-- The id an instruction spvbind reads defines. -/
def result? : Instruction → Option Id
  | .typeInt result .. | .typeFloat result .. | .typeVector result .. | .typeMatrix result .. | .typeArray result ..
  | .typeStruct result .. | .typePointer result .. => some result
  | .constant _ result .. | .var _ result .. => some result
  | _ => none

/-- The Offset an instruction gives a member, by structure type and member. -/
def offset? : Instruction → Option ((Id × Word) × Word)
  | .memberDecorate type member (.offset byteOffset) => some ((type, member), byteOffset)
  | _ => none

/-- The MatrixStride an instruction gives a member. -/
def matrixStride? : Instruction → Option ((Id × Word) × Word)
  | .memberDecorate type member (.matrixStride stride) => some ((type, member), stride)
  | _ => none

/-- The member an instruction decorates RowMajor. -/
def rowMajor? : Instruction → Option ((Id × Word) × Unit)
  | .memberDecorate type member .rowMajor => some ((type, member), ())
  | _ => none

/-- The member an instruction decorates ColMajor. -/
def colMajor? : Instruction → Option ((Id × Word) × Unit)
  | .memberDecorate type member .colMajor => some ((type, member), ())
  | _ => none

/-- The ArrayStride an instruction gives a type. -/
def arrayStride? : Instruction → Option (Id × Word)
  | .decorate type (.arrayStride stride) => some (type, stride)
  | _ => none

/-- The value of a constant, by its id. -/
def constant? : Instruction → Option (Id × Nat)
  | .constant _ result value more => some (result, Spec.wordsValue value more)
  | _ => none

/-- The component type and count of a vector type, by its id. -/
def vector? : Instruction → Option (Id × (Id × Word))
  | .typeVector result componentType count => some (result, (componentType, count))
  | _ => none

/-- The type a pointer type points to. -/
def pointer? : Instruction → Option (Id × Id)
  | .typePointer result _ type => some (result, type)
  | _ => none

/-- A push constant variable, and its type. -/
def pushConstant? : Instruction → Option (Id × Id)
  | .var resultType result storageClass _ => if storageClass = PushConstant then some (result, resultType) else none
  | _ => none

def name? : Instruction → Option (Id × String)
  | .name target s => some (target, s.value)
  | _ => none

def memberName? : Instruction → Option ((Id × Word) × String)
  | .memberName type member s => some ((type, member), s.value)
  | _ => none

/-- C++ keywords and alternative tokens (lex.key, lex.digraph), which cannot be identifiers. -/
def keywords : List String :=
  ["alignas", "alignof", "and", "and_eq", "asm", "auto", "bitand", "bitor", "bool", "break", "case", "catch", "char",
   "char8_t", "char16_t", "char32_t", "class", "compl", "concept", "const", "consteval", "constexpr", "constinit",
   "const_cast", "continue", "contract_assert", "co_await", "co_return", "co_yield", "decltype", "default", "delete",
   "do", "double", "dynamic_cast", "else", "enum", "explicit", "export", "extern", "false", "float", "for", "friend",
   "goto", "if", "inline", "int", "long", "mutable", "namespace", "new", "noexcept", "not", "not_eq", "nullptr",
   "operator", "or", "or_eq", "private", "protected", "public", "register", "reinterpret_cast", "requires", "return",
   "short", "signed", "sizeof", "static", "static_assert", "static_cast", "struct", "switch", "template", "this",
   "thread_local", "throw", "true", "try", "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual",
   "void", "volatile", "wchar_t", "while", "xor", "xor_eq"]

/-- Whether a name from the module can name a struct or member in the header: ASCII letters, digits and underscores,
not starting with a digit, not a keyword, not reserved (lex.name: no `__`, not starting with `_`), and not starting
with `spvbind`, which the header uses for padding. -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    c.isAlpha && cs.all (fun c => c.isAlphanum || c == '_') && (s.splitOn "__").length == 1 &&
      !keywords.contains s && !s.startsWith "spvbind"

/-- The maps the generator looks up instructions in. -/
structure Context where
  offsets : HashMap (Id × Word) Word
  names : HashMap Id String
  memberNames : HashMap (Id × Word) String
  strides : HashMap Id Word
  constants : HashMap Id Nat
  matrixStrides : HashMap (Id × Word) Word
  rowMajors : HashMap (Id × Word) Unit
  colMajors : HashMap (Id × Word) Unit
  vectors : HashMap Id (Id × Word)

/-- A type in messages: its name, or its id if it has none. -/
def Context.describe (ctx : Context) (type : Id) : String :=
  match ctx.names[type]? with
  | some name => if name.isEmpty then s!"%{type}" else name
  | none => s!"%{type}"

/-- The matrix layout the decorations give member `member` of `type`: none without any, otherwise MatrixStride with
exactly one of RowMajor and ColMajor. -/
def memberLayout (ctx : Context) (type : Id) (member : Word) : Except String (Option MatrixLayout) :=
  match ctx.matrixStrides[(type, member)]?, ctx.rowMajors[(type, member)]?, ctx.colMajors[(type, member)]? with
  | none, none, none => .ok none
  | some stride, some (), none => .ok (some ⟨stride, true⟩)
  | some stride, none, some () => .ok (some ⟨stride, false⟩)
  | _, _, _ => .error "MatrixStride without exactly one of RowMajor and ColMajor, or one of those without MatrixStride"

/-- The C++ type of each type defined so far, given the matrix layout of the member it is in, if any, or why there is
none. -/
abbrev Types := HashMap Id (Option MatrixLayout → Except String Ty)

/-- An integer type, in C++ `std::intN_t` or `std::uintN_t`. -/
def int (width signedness : Word) : Except String Ty :=
  if width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64 then
    if signedness = 0 then .ok (.scalar (.int width false))
    else if signedness = 1 then .ok (.scalar (.int width true))
    else .error s!"integer type with Signedness {signedness}"
  else .error s!"{width}-bit integers are not supported"

/-- A floating-point type, in C++ `float` or `double`. -/
def float (width : Word) : Except String Ty :=
  if width = 32 ∨ width = 64 then .ok (.scalar (.float width))
  else .error s!"{width}-bit floating-point numbers are not supported"

/-- A vector type, in C++ a `std::array` of its component type, which must be a scalar. -/
def vector (types : Types) (componentType : Id) (count : Word) (layout : Option MatrixLayout) : Except String Ty :=
  match types[componentType]? with
  | some f =>
    match f layout with
    | .ok (.scalar s) =>
      if 2 ≤ count then .ok (.array (.scalar s) count.toNat) else .error s!"a vector of {count} components"
    | .ok _ => .error "a vector whose component type is not a scalar"
    | .error e => .error s!"vector component: {e}"
  | none => .error "a vector of a type spvbind does not support"

/-- A matrix type, in C++ an array of its columns (ColMajor) or of its rows (RowMajor), each an array of the scalar,
if the member's MatrixStride is the size of a column or row; a larger stride would need padding, which is not
supported yet. Outside a member with MatrixStride and RowMajor or ColMajor a matrix has no layout. -/
def matrix (ctx : Context) (types : Types) (columnType : Id) (columns : Word) (layout : Option MatrixLayout) :
    Except String Ty :=
  match layout with
  | none => .error "a matrix outside a member with MatrixStride and RowMajor or ColMajor"
  | some ⟨stride, rowMajor⟩ =>
    match ctx.vectors[columnType]? with
    | none => .error "a matrix whose column type is not a vector"
    | some (componentType, rows) =>
      match types[componentType]? with
      | none => .error "a matrix of a type spvbind does not support"
      | some f =>
        match f layout with
        | .ok (.scalar s) =>
          if rowMajor then
            if 2 ≤ columns ∧ 2 ≤ rows ∧ stride.toNat = columns.toNat * s.bytes then
              .ok (.array (.array (.scalar s) columns.toNat) rows.toNat)
            else .error s!"a row-major matrix of {rows} rows of {columns} components with MatrixStride {stride}; the \
              stride must be the size of a row and both counts at least 2"
          else
            if 2 ≤ columns ∧ 2 ≤ rows ∧ stride.toNat = rows.toNat * s.bytes then
              .ok (.array (.array (.scalar s) rows.toNat) columns.toNat)
            else .error s!"a column-major matrix of {columns} columns of {rows} components with MatrixStride {stride}; \
              the stride must be the size of a column and both counts at least 2"
        | .ok _ => .error "a matrix whose component type is not a scalar"
        | .error e => .error s!"matrix component: {e}"

/-- An array type, in C++ a `std::array` of its element type, if its ArrayStride is the element's C++ size and its
Length a constant of at least 1. A larger stride would need a padded element type, which is not supported yet. -/
def array (ctx : Context) (types : Types) (type elementType length : Id) (layout : Option MatrixLayout) :
    Except String Ty :=
  match types[elementType]?, ctx.constants[length]?, ctx.strides[type]? with
  | some f, some n, some stride =>
    match f layout with
    | .ok e =>
      if stride.toNat = e.size ∧ 0 < n then .ok (.array e n)
      else .error s!"an array of {n} elements with stride {stride} whose elements have C++ size {e.size}; the stride \
        must be the size and the length at least 1"
    | .error e => .error s!"array element: {e}"
  | none, _, _ => .error "an array of a type spvbind does not support"
  | some _, none, _ => .error "an array whose length is not a constant"
  | some _, some _, none => .error "an array without ArrayStride"

/-- The members of struct `type` from member `index` on, whose types are `memberTypes`, starting at byte `start`.
Each is placed at its Offset, after explicit padding, with its matrices laid out as its own decorations say; one that
overlaps the member before it, or whose Offset is not aligned for its C++ type, is an error. -/
def members (ctx : Context) (types : Types) (type : Id) (index start : Nat) :
    List Id → Except String (List Member)
  | [] => .ok []
  | memberType :: memberTypes =>
    if index < 2 ^ 32 then
      match types[memberType]?, ctx.offsets[(type, index.toUInt32)]?, ctx.memberNames[(type, index.toUInt32)]? with
      | some f, some byteOffset, some name =>
        if !isIdentifier name then
          .error s!"member {index} of {ctx.describe type} is named {name}, which is not a valid C++ name"
        else
          match memberLayout ctx type index.toUInt32 with
          | .error e => .error s!"member {index} of {ctx.describe type}: {e}"
          | .ok layout =>
            match f layout with
            | .error e => .error s!"member {index} of {ctx.describe type}: {e}"
            | .ok c =>
              if start ≤ byteOffset.toNat ∧ byteOffset.toNat % c.align = 0 then
                match members ctx types type (index + 1) (byteOffset.toNat + c.size) memberTypes with
                | .ok rest => .ok (.mk name (byteOffset.toNat - start) c :: rest)
                | .error e => .error e
              else .error s!"member {name} of {ctx.describe type} is at offset {byteOffset}, which overlaps the member \
                before it or is not aligned for C++"
      | none, _, _ => .error s!"member {index} of {ctx.describe type} has a type spvbind does not support"
      | some _, none, _ => .error s!"member {index} of {ctx.describe type} has no Offset"
      | some _, some _, none =>
        .error s!"member {index} of {ctx.describe type} has no name; was the module optimized?"
    else .error s!"{ctx.describe type} has more than 2^32 members"

/-- A struct type, in C++ a struct of the same name. Empty structs are not supported, since C++ gives them a size of
1. -/
def struct (ctx : Context) (types : Types) (type : Id) (memberTypes : List Id) : Except String Ty :=
  match ctx.names[type]? with
  | none => .error s!"%{type} has no name; was the module optimized?"
  | some name =>
    if !isIdentifier name then .error s!"%{type} is named {name}, which is not a valid C++ name"
    else if memberTypes = [] then .error s!"{name} has no members"
    else
      match members ctx types type 0 0 memberTypes with
      | .ok ms => .ok (.struct name ms)
      | .error e => .error e

/-- `types`, with the type an instruction defines. A struct is resolved once, here; the others on use, since a matrix's
C++ type depends on the member it is in. -/
def addType (ctx : Context) (types : Types) : Instruction → Types
  | .typeInt result width signedness => types.insert result fun _ => int width signedness
  | .typeFloat result width => types.insert result fun _ => float width
  | .typeVector result componentType count => types.insert result (vector types componentType count)
  | .typeMatrix result columnType columns => types.insert result (matrix ctx types columnType columns)
  | .typeArray result elementType length => types.insert result (array ctx types result elementType length)
  | .typeStruct result memberTypes =>
    let resolved := struct ctx types result memberTypes
    types.insert result fun _ => resolved
  | _ => types

/-- The C++ type of each variable in `vars`, given with its pointer type. -/
def blocks (types : Types) (pointers : HashMap Id Id) : List (Id × Id) → Except String (List (Id × Ty))
  | [] => .ok []
  | (v, pointer) :: vars =>
    match pointers[pointer]? with
    | none => .error s!"the type of %{v} is not a pointer"
    | some type =>
      match types[type]? with
      | none => .error s!"%{v} points to a type spvbind does not support"
      | some f =>
        match f none with
        | .error e => .error e
        | .ok c =>
          match blocks types pointers vars with
          | .ok rest => .ok ((v, c) :: rest)
          | .error e => .error e

/-- The C++ type of each push constant variable of the module the words encode, with the variable. -/
def generate (ws : List Word) : Except String (List (Id × Ty)) := do
  let m ← decode ws
  checkVersion m.header
  unless distinct (m.instructions.filterMap result?) do
    throw "an id is defined by more than one instruction"
  unless distinct ((m.instructions.filterMap offset?).map Prod.fst) do
    throw "a member has more than one Offset decoration"
  unless distinct ((m.instructions.filterMap name?).map Prod.fst) do
    throw "an id has more than one OpName"
  unless distinct ((m.instructions.filterMap memberName?).map Prod.fst) do
    throw "a member has more than one OpMemberName"
  unless distinct ((m.instructions.filterMap arrayStride?).map Prod.fst) do
    throw "an array has more than one ArrayStride decoration"
  unless distinct ((m.instructions.filterMap matrixStride?).map Prod.fst) do
    throw "a member has more than one MatrixStride decoration"
  unless distinct ((m.instructions.filterMap rowMajor?).map Prod.fst) do
    throw "a member has more than one RowMajor decoration"
  unless distinct ((m.instructions.filterMap colMajor?).map Prod.fst) do
    throw "a member has more than one ColMajor decoration"
  let ctx : Context := {
    offsets := .ofList (m.instructions.filterMap offset?)
    names := .ofList (m.instructions.filterMap name?)
    memberNames := .ofList (m.instructions.filterMap memberName?)
    strides := .ofList (m.instructions.filterMap arrayStride?)
    constants := .ofList (m.instructions.filterMap constant?)
    matrixStrides := .ofList (m.instructions.filterMap matrixStride?)
    rowMajors := .ofList (m.instructions.filterMap rowMajor?)
    colMajors := .ofList (m.instructions.filterMap colMajor?)
    vectors := .ofList (m.instructions.filterMap vector?) }
  let types := m.instructions.foldl (addType ctx) ∅
  blocks types (.ofList (m.instructions.filterMap pointer?)) (m.instructions.filterMap pushConstant?)

end Spvbind
