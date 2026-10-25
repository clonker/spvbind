import Spec
import Spvbind
import Proofs
import Guarantees.Axioms

/-!
# What spvbind guarantees

Together with the definitions in `Spec`, the statements in this file are all that needs review. Each is proven in
`Proofs`, which needs no review, and is checked here to depend only on Lean's standard axioms.
-/

namespace Guarantees

open Spec Spvbind

/-- The decoder accepts exactly the words of a module whose instructions' word counts fit in 16 bits, and returns
that module. -/
theorem decode_eq_ok (ws : List Word) (m : Module) :
    decode ws = .ok m ↔ ws = m.words ∧ ∀ i ∈ m.instructions, i.Fits :=
  Proofs.decode_eq_ok ws m

#assert_standard_axioms decode_eq_ok

/-- Reading the bytes of a file and decoding them, as `Main.lean` does, accepts exactly the little-endian or the
big-endian storage of a module whose instructions' word counts fit in 16 bits, and returns that module. -/
theorem words_decode_eq_ok (bytes : ByteArray) (m : Module) :
    (words bytes >>= decode) = .ok m ↔
      (bytes.toList = littleEndianBytes m.words ∨ bytes.toList = bigEndianBytes m.words) ∧
        ∀ i ∈ m.instructions, i.Fits :=
  Proofs.words_decode_eq_ok bytes m

#assert_standard_axioms words_decode_eq_ok

/-- If the generator succeeds, the input is a module `m`, and the output has one C++ type for each push constant
variable of `m` and for nothing else; and each type has exactly the scalars of the object its variable points to,
each with the same path, type and offset. -/
theorem generate_correct (ws : List Word) (out : List (Id × Cpp.Ty)) (h : generate ws = .ok out) :
    ∃ m : Module, ws = m.words ∧
      (out.map Prod.fst).Nodup ∧
      (∀ v, v ∈ out.map Prod.fst ↔ PushConstantVariable m v) ∧
      ∀ v c, (v, c) ∈ out → ∀ l, l ∈ c.locations ↔ VariableLocated m v l :=
  Proofs.generate_correct ws out h

#assert_standard_axioms generate_correct

/-- The same for the bytes of a file, as `Main.lean` runs the generator: the file is the little-endian or big-endian
storage of the module. -/
theorem generate_correct_of_bytes (bytes : ByteArray) (out : List (Id × Cpp.Ty))
    (h : (words bytes >>= generate) = .ok out) :
    ∃ m : Module, (bytes.toList = littleEndianBytes m.words ∨ bytes.toList = bigEndianBytes m.words) ∧
      (out.map Prod.fst).Nodup ∧
      (∀ v, v ∈ out.map Prod.fst ↔ PushConstantVariable m v) ∧
      ∀ v c, (v, c) ∈ out → ∀ l, l ∈ c.locations ↔ VariableLocated m v l :=
  Proofs.generate_correct_of_bytes bytes out h

#assert_standard_axioms generate_correct_of_bytes

end Guarantees
