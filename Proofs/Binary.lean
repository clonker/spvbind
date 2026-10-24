import Spec.Binary
import Spvbind.Binary

namespace Proofs

open Spvbind

/-- The header is decoded from the words the specification gives it, and what follows is left as it is. -/
theorem decodeHeader_words (h : Spec.Header) (rest : List Spec.Word) :
    decodeHeader (h.words ++ rest) = .ok (h, rest) := by
  simp [decodeHeader, Spec.Header.words]; rfl

end Proofs
