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

end Guarantees
