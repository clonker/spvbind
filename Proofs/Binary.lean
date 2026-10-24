import Spec.Binary
import Spvbind.Binary

namespace Proofs

open Spvbind

/-- The decoder accepts exactly the words the specification gives a header, followed by anything. -/
theorem decodeHeader_eq_ok (ws : List Spec.Word) (h : Spec.Header) (rest : List Spec.Word) :
    decodeHeader ws = .ok (h, rest) ↔ ws = h.words ++ rest := by
  constructor
  · intro hd
    unfold decodeHeader at hd
    split at hd
    · split at hd
      · contradiction
      · split at hd
        · contradiction
        · cases hd
          simp_all [Spec.Header.words]
    · contradiction
  · rintro rfl
    simp [decodeHeader, Spec.Header.words]; rfl

end Proofs
