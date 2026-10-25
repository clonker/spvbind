import Std.Data.HashMap
import Std.Data.HashSet
import Spec.Cpp
import Spvbind.Instruction

/-!
# The C++ types of the push constant blocks of a module

Types are resolved in one pass over the instructions, in order: a type's operands are "declared before being used"
(2.4, Logical Layout of a Module), so the C++ types of a struct's members are known when the struct is reached, and a
type cannot contain itself. Every id spvbind reads must be defined once and every member have at most one Offset, so
that each id and member means one thing.
-/

namespace Spvbind

open Spec (Word Id Scalar Instruction Module Decoration PushConstant)
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
  | .typeInt result .. | .typeFloat result .. | .typeStruct result .. | .typePointer result .. => some result
  | .var _ result .. => some result
  | _ => none

/-- The Offset an instruction gives a member, by structure type and member. -/
def offset? : Instruction → Option ((Id × Word) × Word)
  | .memberDecorate type member (.offset byteOffset) => some ((type, member), byteOffset)
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

/-- A type in messages: its name, or its id if it has none. -/
def Context.describe (ctx : Context) (type : Id) : String :=
  match ctx.names[type]? with
  | some name => if name.isEmpty then s!"%{type}" else name
  | none => s!"%{type}"

/-- The C++ type of each type defined so far, or why there is none. -/
abbrev Types := HashMap Id (Except String Ty)

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

/-- The members of struct `type` from member `index` on, whose types are `memberTypes`, starting at byte `start`.
Each is placed at its Offset, after explicit padding; one that overlaps the member before it, or whose Offset is not
aligned for its C++ type, is an error. -/
def members (ctx : Context) (types : Types) (type : Id) (index start : Nat) :
    List Id → Except String (List Member)
  | [] => .ok []
  | memberType :: memberTypes =>
    if index < 2 ^ 32 then
      match types[memberType]?, ctx.offsets[(type, index.toUInt32)]?, ctx.memberNames[(type, index.toUInt32)]? with
      | some (.ok c), some byteOffset, some name =>
        if !isIdentifier name then
          .error s!"member {index} of {ctx.describe type} is named {name}, which is not a valid C++ name"
        else if start ≤ byteOffset.toNat ∧ byteOffset.toNat % c.align = 0 then
          match members ctx types type (index + 1) (byteOffset.toNat + c.size) memberTypes with
          | .ok rest => .ok (.mk name (byteOffset.toNat - start) c :: rest)
          | .error e => .error e
        else .error s!"member {name} of {ctx.describe type} is at offset {byteOffset}, which overlaps the member \
          before it or is not aligned for C++"
      | some (.error e), _, _ => .error s!"member {index} of {ctx.describe type}: {e}"
      | none, _, _ => .error s!"member {index} of {ctx.describe type} has a type spvbind does not support"
      | some (.ok _), none, _ => .error s!"member {index} of {ctx.describe type} has no Offset"
      | some (.ok _), some _, none =>
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
      | .ok ms => .ok (.struct type name ms)
      | .error e => .error e

/-- `types`, with the type an instruction defines. -/
def addType (ctx : Context) (types : Types) : Instruction → Types
  | .typeInt result width signedness => types.insert result (int width signedness)
  | .typeFloat result width => types.insert result (float width)
  | .typeStruct result memberTypes => types.insert result (struct ctx types result memberTypes)
  | _ => types

/-- The C++ type of each variable in `vars`, given with its pointer type. -/
def blocks (types : Types) (pointers : HashMap Id Id) : List (Id × Id) → Except String (List (Id × Ty))
  | [] => .ok []
  | (v, pointer) :: vars =>
    match pointers[pointer]? with
    | none => .error s!"the type of %{v} is not a pointer"
    | some type =>
      match types[type]? with
      | some (.ok c) =>
        match blocks types pointers vars with
        | .ok rest => .ok ((v, c) :: rest)
        | .error e => .error e
      | some (.error e) => .error e
      | none => .error s!"%{v} points to a type spvbind does not support"

/-- The C++ type of each push constant variable of the module the words encode, with the variable. -/
def generate (ws : List Word) : Except String (List (Id × Ty)) := do
  let m ← decode ws
  checkVersion m.header
  unless distinct (m.instructions.filterMap result?) do
    throw "an id is defined by more than one instruction"
  unless distinct ((m.instructions.filterMap offset?).map Prod.fst) do
    throw "a member has more than one Offset decoration"
  let ctx : Context := {
    offsets := .ofList (m.instructions.filterMap offset?)
    names := .ofList (m.instructions.filterMap name?)
    memberNames := .ofList (m.instructions.filterMap memberName?) }
  let types := m.instructions.foldl (addType ctx) ∅
  blocks types (.ofList (m.instructions.filterMap pointer?)) (m.instructions.filterMap pushConstant?)

end Spvbind
