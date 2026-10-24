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

end Guarantees
