import Spec.Binary
import Spvbind.Binary

/-!
# Reading words from bytes, and the header: the decoders accept exactly the specification's encodings
-/

namespace Proofs

open Spvbind
open Spec (Word Byte magic wordOfOctets octets littleEndianBytes bigEndianBytes)

/-! Octets of a word. -/

theorem toNat_wordOfOctets (b0 b1 b2 b3 : Byte) :
    (wordOfOctets b0 b1 b2 b3).toNat = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [wordOfOctets, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
    Nat.reduceMod]
  have m1 : b1.toNat <<< 8 % 2 ^ 32 = b1.toNat <<< 8 := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  have m2 : b2.toNat <<< 16 % 2 ^ 32 = b2.toNat <<< 16 := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  have m3 : b3.toNat <<< 24 % 2 ^ 32 = b3.toNat <<< 24 := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  have e1 : b0.toNat ||| b1.toNat <<< 8 = b1.toNat * 2 ^ 8 + b0.toNat := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h0, Nat.shiftLeft_eq]
  have e2 : b1.toNat * 2 ^ 8 + b0.toNat ||| b2.toNat <<< 16 = b2.toNat * 2 ^ 16 + (b1.toNat * 2 ^ 8 + b0.toNat) := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  have e3 : b2.toNat * 2 ^ 16 + (b1.toNat * 2 ^ 8 + b0.toNat) ||| b3.toNat <<< 24 =
      b3.toNat * 2 ^ 24 + (b2.toNat * 2 ^ 16 + (b1.toNat * 2 ^ 8 + b0.toNat)) := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  rw [m1, m2, m3, e1, e2, e3]
  omega

theorem octets_wordOfOctets (b0 b1 b2 b3 : Byte) : octets (wordOfOctets b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h := toNat_wordOfOctets b0 b1 b2 b3
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [octets, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow, h] <;> omega

theorem wordOfOctets_octets (w : Word) :
    wordOfOctets w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toNat_inj.mp
  have := w.toNat_lt
  rw [toNat_wordOfOctets]
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow]
  omega

theorem octets_byteReverse (w : Word) : octets (byteReverse w) = (octets w).reverse := by
  rw [byteReverse, octets_wordOfOctets]
  simp [octets]

theorem byteReverse_byteReverse (w : Word) : byteReverse (byteReverse w) = w := by
  have h := octets_byteReverse w
  simp only [octets, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.cons.injEq,
    and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  show wordOfOctets (byteReverse w >>> 24).toUInt8 (byteReverse w >>> 16).toUInt8 (byteReverse w >>> 8).toUInt8
    (byteReverse w).toUInt8 = w
  rw [h3, h2, h1, h0]
  exact wordOfOctets_octets w

theorem map_byteReverse_map_byteReverse (ws : List Word) : (ws.map byteReverse).map byteReverse = ws := by
  simp [List.map_map, Function.comp_def, byteReverse_byteReverse]

theorem littleEndianBytes_map_byteReverse (ws : List Word) :
    littleEndianBytes (ws.map byteReverse) = bigEndianBytes ws := by
  simp [littleEndianBytes, bigEndianBytes, List.flatMap_map, octets_byteReverse]

theorem magic_ne_byteReverse : magic ≠ byteReverse magic := by decide

/-! Words from bytes. -/

/-- The reader of words accepts exactly the little-endian storage of a list of words, four octets each. -/
theorem wordsOfOctets_eq_some (bs : List Byte) (ws : List Word) :
    wordsOfOctets bs = some ws ↔ bs = littleEndianBytes ws := by
  constructor
  · intro h
    fun_induction wordsOfOctets bs generalizing ws with
    | case1 b0 b1 b2 b3 rest ih =>
      cases hr : wordsOfOctets rest with
      | none => rw [hr] at h; cases h
      | some ws' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih ws' hr]
        simp [littleEndianBytes, octets_wordOfOctets]
    | case2 => cases h; rfl
    | case3 | case4 | case5 => cases h
  · rintro rfl
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [littleEndianBytes, octets, wordsOfOctets, wordOfOctets_octets] at ih ⊢; simp [ih]

/-- `words` accepts exactly a little-endian storage whose first word is not the magic number with its octets reversed,
or a big-endian storage whose first word is the magic number. -/
theorem words_eq_ok (bytes : ByteArray) (ws : List Word) :
    words bytes = .ok ws ↔
      (bytes.toList = littleEndianBytes ws ∧ ws.head? ≠ some (byteReverse magic)) ∨
      (bytes.toList = bigEndianBytes ws ∧ ws.head? = some magic) := by
  unfold words
  constructor
  · intro h
    split at h
    · cases h
    rename_i ws' hws'
    rw [wordsOfOctets_eq_some] at hws'
    split at h
    · rename_i hhead
      cases h
      right
      refine ⟨?_, ?_⟩
      · rw [hws', ← littleEndianBytes_map_byteReverse, map_byteReverse_map_byteReverse]
      · rw [List.head?_map, hhead, Option.map_some, byteReverse_byteReverse]
    · rename_i hhead
      cases h
      exact .inl ⟨hws', hhead⟩
  · rintro (⟨hb, hhead⟩ | ⟨hb, hhead⟩)
    · rw [hb, (wordsOfOctets_eq_some _ _).mpr rfl]
      simp [hhead]
    · have hw : wordsOfOctets bytes.toList = some (ws.map byteReverse) := by
        rw [wordsOfOctets_eq_some, hb, littleEndianBytes_map_byteReverse]
      have hh : (ws.map byteReverse).head? = some (byteReverse magic) := by rw [List.head?_map, hhead]; rfl
      rw [hw]
      simp [hh, Function.comp_def, byteReverse_byteReverse]

/-! The header. -/

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
