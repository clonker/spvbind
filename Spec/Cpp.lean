import Spec.Layout

/-!
# The C++ types spvbind emits, and where their scalars are

Not a specification: the C++ standard leaves layout to the implementation. This is a model of what compilers do, and
every header checks it with a `static_assert` on every offset, size and alignment it gives, so that a compiler where
it does not hold rejects the header. Padding is always explicit, as `std::array<std::byte, N>`, which has alignment 1;
each member is placed where its alignment puts it after that padding. A scalar's size and alignment are its size in
bytes (`std::int8_t` to `std::int64_t`, `std::uint8_t` to `std::uint64_t`, `float` and `double`); a `std::array<T, N>`
is its `N` elements and nothing else, aligned like `T`.
-/

namespace Spec.Cpp

mutual
/-- A C++ type: a scalar, a `std::array<element, count>`, or a struct. -/
inductive Ty where
  | scalar (s : Scalar)
  | array (element : Ty) (count : Nat)
  | struct (name : String) (members : List Member)

/-- A member of a struct, after `padding` bytes of explicit padding (none if 0). -/
inductive Member where
  | mk (name : String) (padding : Nat) (type : Ty)
end

/-- The smallest multiple of `a` that is at least `n`. -/
def alignUp (n a : Nat) : Nat := if n % a = 0 then n else n + (a - n % a)

mutual
/-- `alignof`: a struct is aligned like its most aligned member. -/
def Ty.align : Ty → Nat
  | .scalar s => Scalar.bytes s
  | .array element _ => element.align
  | .struct _ members => Members.align members

def Members.align : List Member → Nat
  | [] => 1
  | .mk _ _ type :: members => max type.align (Members.align members)
end

mutual
/-- `sizeof`: a struct ends after its last member, rounded up to its alignment. -/
def Ty.size : Ty → Nat
  | .scalar s => Scalar.bytes s
  | .array element count => count * element.size
  | .struct _ members => alignUp (Members.end 0 members) (Members.align members)

/-- Where `members` end, if they start at byte `start`. -/
def Members.end (start : Nat) : List Member → Nat
  | [] => start
  | .mk _ padding type :: members => Members.end (alignUp (start + padding) type.align + type.size) members
end

/-- The offset of each of `members`, if they start at byte `start`; what the header asserts with `offsetof`. -/
def Members.offsets (start : Nat) : List Member → List Nat
  | [] => []
  | .mk _ padding type :: members =>
    alignUp (start + padding) type.align :: Members.offsets (alignUp (start + padding) type.align + type.size) members

mutual
/-- Every scalar of a value of the type, with its path and offset. -/
def Ty.locations : Ty → List Location
  | .scalar s => [⟨[], 0, s⟩]
  | .array element count =>
    let ls := element.locations
    (List.range count).flatMap fun i => ls.map fun l => ⟨.element i :: l.path, i * element.size + l.offset, l.scalar⟩
  | .struct name members => Members.locations name 0 0 members

/-- Every scalar of `members` of the struct named `struct`, numbered from `index` and starting at byte `start`. -/
def Members.locations (struct : String) (index start : Nat) : List Member → List Location
  | [] => []
  | .mk name padding type :: members =>
    type.locations.map (fun l =>
        ⟨.member struct index name :: l.path, alignUp (start + padding) type.align + l.offset, l.scalar⟩) ++
      Members.locations struct (index + 1) (alignUp (start + padding) type.align + type.size) members
end

end Spec.Cpp
