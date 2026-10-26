import Spec
import Spvbind
import Proofs.Binary

/-!
# Decoding literal strings, instructions and modules: the decoders accept exactly the specification's encodings
-/

namespace Proofs

open Spvbind
open Spec (Word Byte octets LiteralString wordOfOctets packOctets Decoration modelledDecorations ArrayStride Offset
  OpName OpMemberName OpTypeInt OpTypeFloat OpTypeVector OpTypeArray OpTypeStruct OpTypePointer OpConstant OpVariable
  OpDecorate OpMemberDecorate modelled Instruction Module)

/-! Literal strings. -/

theorem octets_packOctets (bs : List Byte) :
    ∃ z, (packOctets bs).flatMap octets = bs ++ z ∧ ∀ x ∈ z, x = 0 := by
  fun_induction packOctets bs with
  | case1 b0 b1 b2 b3 rest ih =>
    obtain ⟨z, hz, h0⟩ := ih
    exact ⟨z, by simp [octets_wordOfOctets, hz], h0⟩
  | case2 b0 b1 b2 => exact ⟨[0], by simp [octets_wordOfOctets], by simp⟩
  | case3 b0 b1 => exact ⟨[0, 0], by simp [octets_wordOfOctets], by simp⟩
  | case4 b0 => exact ⟨[0, 0, 0], by simp [octets_wordOfOctets], by simp⟩
  | case5 => exact ⟨[], by simp, by simp⟩


theorem decodeString_words (s : LiteralString) (rest : List Word) :
    decodeString (s.words ++ rest) = .ok (s, rest) := by
  obtain ⟨value, noNul⟩ := s
  obtain ⟨z, hz, hz0⟩ := octets_packOctets (value.toUTF8.data.toList ++ [0])
  have hos : (LiteralString.words ⟨value, noNul⟩ ++ rest).flatMap octets =
      value.toUTF8.data.toList ++ 0 :: (z ++ rest.flatMap octets) := by
    simp only [LiteralString.words, List.flatMap_append, hz]
    simp
  have htw : ((LiteralString.words ⟨value, noNul⟩ ++ rest).flatMap octets).takeWhile (· != 0) =
      value.toUTF8.data.toList := by
    rw [hos, List.takeWhile_append_of_pos]
    · simp
    · intro a ha
      have : a ≠ 0 := fun h => noNul (h ▸ ha)
      simpa using this
  unfold decodeString
  simp only [htw]
  simp only [hos]
  simp [Array.toArray_toList, String.toUTF8_eq_toByteArray]
  split
  · rfl
  · exact absurd value.isValidUTF8 ‹_›


theorem eq_append_drop_of_take {α : Type} {l p : List α} (h : l.take p.length = p) : l = p ++ l.drop p.length := by
  conv => lhs; rw [← List.take_append_drop p.length l]
  rw [h]

theorem words_of_decodeString (ws : List Word) (s : LiteralString) (rest : List Word)
    (h : decodeString ws = .ok (s, rest)) : ws = s.words ++ rest := by
  unfold decodeString at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i htake
        cases h
        exact eq_append_drop_of_take htake
      · cases h
    · cases h

theorem decodeString_eq_ok (ws : List Word) (s : LiteralString) (rest : List Word) :
    decodeString ws = .ok (s, rest) ↔ ws = s.words ++ rest :=
  ⟨words_of_decodeString ws s rest, fun h => h ▸ decodeString_words s rest⟩

theorem decodeDecoration_eq_ok (ws : List Word) (d : Decoration) : decodeDecoration ws = .ok d ↔ d.words = ws := by
  constructor
  · intro h
    unfold decodeDecoration at h
    repeat' split at h
    all_goals first | cases h; done | cases h; simp_all [Decoration.words]
  · rintro rfl
    cases d with
    | arrayStride => simp [decodeDecoration, Decoration.words]
    | offset => simp [decodeDecoration, Decoration.words, ArrayStride, Offset]
    | other e ops h =>
      have h' := h
      simp only [modelledDecorations, List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
      simp [decodeDecoration, Decoration.words, h'.1, h'.2, h]

theorem decodeOperands_eq_ok (e : UInt16) (ops : List Word) (i : Instruction) :
    decodeOperands e ops = .ok i ↔ i.enumerant = e ∧ i.operands = ops := by
  constructor
  · intro h
    -- Which branch of `decodeOperands` applies follows from `e`; `split` cannot take the chain of tests apart, `simp`
    -- can, once `e` is known.
    by_cases hm : e ∈ modelled
    · have hm' := hm
      simp only [modelled, List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp [decodeOperands, OpName, OpMemberName, OpTypeInt, OpTypeFloat, OpTypeVector, OpTypeArray, OpTypeStruct,
          OpTypePointer, OpConstant, OpVariable, OpDecorate, OpMemberDecorate] at h
        first
          | unfold decodeName at h | unfold decodeMemberName at h | unfold decodeTypeInt at h
          | unfold decodeTypeFloat at h | unfold decodeTypeVector at h | unfold decodeTypeArray at h
          | unfold decodeTypeStruct at h | unfold decodeTypePointer at h | unfold decodeConstant at h
          | unfold decodeVariable at h | unfold decodeDecorate at h | unfold decodeMemberDecorate at h
        repeat' split at h
        all_goals first
          | (cases h; done)
          | (cases h; simp_all [Instruction.enumerant, Instruction.operands, decodeString_eq_ok,
              decodeDecoration_eq_ok])
    · have hm' := hm
      simp only [modelled, List.mem_cons, List.not_mem_nil, or_false, not_or] at hm'
      simp only [decodeOperands, hm', hm, ↓reduceIte, ↓reduceDIte, Except.ok.injEq] at h
      subst h
      simp [Instruction.enumerant, Instruction.operands]
  · rintro ⟨rfl, rfl⟩
    have hs (s : LiteralString) : decodeString s.words = .ok (s, []) := by simpa using decodeString_words s []
    have hd (d : Decoration) : decodeDecoration d.words = .ok d := (decodeDecoration_eq_ok _ _).mpr rfl
    cases i with
    | var resultType result storageClass initializer =>
      cases initializer <;> simp [decodeOperands, decodeVariable, Instruction.enumerant, Instruction.operands, OpName,
        OpMemberName, OpTypeInt, OpTypeFloat, OpTypeVector, OpTypeArray, OpTypeStruct, OpTypePointer, OpConstant,
        OpVariable]
    | other e ops h =>
      have h' := h
      simp only [modelled, List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
      simp [decodeOperands, Instruction.enumerant, Instruction.operands, h', h]
    | _ => simp [decodeOperands, decodeName, decodeMemberName, decodeTypeInt, decodeTypeFloat, decodeTypeVector,
        decodeTypeArray, decodeTypeStruct, decodeTypePointer, decodeConstant, decodeDecorate, decodeMemberDecorate,
        Instruction.enumerant, Instruction.operands, OpName, OpMemberName, OpTypeInt, OpTypeFloat, OpTypeVector,
        OpTypeArray, OpTypeStruct, OpTypePointer, OpConstant, OpVariable, OpDecorate, OpMemberDecorate, hs, hd]


/-! The first word of an instruction: its 16 high-order bits and its 16 low-order bits. -/

theorem join_high_low (w : Word) : (w >>> 16) <<< 16 ||| w.toUInt16.toUInt32 = w := by
  apply UInt32.toNat_inj.mp
  have := w.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, UInt16.toNat_toUInt32,
    UInt32.toNat_toUInt16, UInt32.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem high_join (n : Word) (o : UInt16) (h : n.toNat < 2 ^ 16) : (n <<< 16 ||| o.toUInt32) >>> 16 = n := by
  apply UInt32.toNat_inj.mp
  have := o.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, UInt16.toNat_toUInt32,
    UInt32.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem low_join (n : Word) (o : UInt16) (h : n.toNat < 2 ^ 16) : (n <<< 16 ||| o.toUInt32).toUInt16 = o := by
  apply UInt16.toNat_inj.mp
  have := o.toNat_lt
  rw [UInt32.toNat_toUInt16, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32]
  have hs : n.toNat <<< ((16 : UInt32).toNat % 32) % 2 ^ 32 = n.toNat <<< 16 := by
    rw [show (16 : UInt32).toNat % 32 = 16 from rfl]
    exact Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  rw [hs, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem high_lt (w : Word) : (w >>> 16).toNat < 2 ^ 16 := by
  have := w.toNat_lt
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp only [UInt32.reduceToNat, Nat.reduceMod]
  omega

/-! Instructions and modules. -/

theorem decodeInstructions_words (is : List Instruction) (hf : ∀ i ∈ is, i.Fits) :
    decodeInstructions (is.flatMap Instruction.words) = .ok is := by
  induction is with
  | nil => simp [decodeInstructions]
  | cons i is ih =>
    have hfi : i.Fits := hf i (by simp)
    have hrest := ih (fun j hj => hf j (by simp [hj]))
    unfold Instruction.Fits at hfi
    have hn : (i.operands.length + 1).toUInt32.toNat = i.operands.length + 1 :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    have hc := high_join (i.operands.length + 1).toUInt32 i.enumerant (by rw [hn]; exact hfi)
    have ho := low_join (i.operands.length + 1).toUInt32 i.enumerant (by rw [hn]; exact hfi)
    have hop : decodeOperands i.enumerant i.operands = .ok i := (decodeOperands_eq_ok _ _ _).mpr ⟨rfl, rfl⟩
    simp only [List.flatMap_cons, Instruction.words, List.cons_append]
    rw [decodeInstructions]
    simp only [hc, ho, hn]
    simp [hop, hrest]
    rfl

theorem words_of_decodeInstructions (ws : List Word) (is : List Instruction)
    (h : decodeInstructions ws = .ok is) : ws = is.flatMap Instruction.words ∧ ∀ i ∈ is, i.Fits := by
  fun_induction decodeInstructions ws generalizing is with
  | case1 => cases h; simp
  | case2 => cases h
  | case3 => cases h
  | case4 w ws h0 hlen i hop ih =>
    cases hr : decodeInstructions (ws.drop ((w >>> 16).toNat - 1)) with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨hws, hfs⟩ := ih r hr
      obtain ⟨he, hops⟩ := (decodeOperands_eq_ok _ _ _).mp hop
      have hcount : i.operands.length + 1 = (w >>> 16).toNat := by
        rw [hops]; simp only [List.length_take] at hlen ⊢; omega
      have hfirst : (i.operands.length + 1).toUInt32 <<< 16 ||| i.enumerant.toUInt32 = w := by
        rw [hcount, he, Nat.toUInt32_eq, UInt32.ofNat_toNat, join_high_low]
      refine ⟨?_, ?_⟩
      · simp only [List.flatMap_cons, Instruction.words, hfirst]
        simp only [hops, ← hws, List.cons_append, List.take_append_drop]
      · intro j hj
        simp only [List.mem_cons] at hj
        rcases hj with rfl | hj
        · unfold Instruction.Fits; have := high_lt w; omega
        · exact hfs j hj
  | case5 w ws h0 hlen e he => cases h

/-- The decoder accepts exactly the words of a sequence of instructions whose word counts fit. -/
theorem decodeInstructions_eq_ok (ws : List Word) (is : List Instruction) :
    decodeInstructions ws = .ok is ↔ ws = is.flatMap Instruction.words ∧ ∀ i ∈ is, i.Fits :=
  ⟨words_of_decodeInstructions ws is, fun ⟨h, hf⟩ => h ▸ decodeInstructions_words is hf⟩


/-- The decoder accepts exactly the words of a module whose instructions' word counts fit. -/
theorem decode_eq_ok (ws : List Word) (m : Module) :
    decode ws = .ok m ↔ ws = m.words ∧ ∀ i ∈ m.instructions, i.Fits := by
  constructor
  · intro h
    cases hh : decodeHeader ws with
    | error e => simp only [decode, hh, bind, Except.bind] at h; cases h
    | ok p =>
      obtain ⟨header, rest⟩ := p
      cases hi : decodeInstructions rest with
      | error e => simp only [decode, hh, hi, bind, Except.bind] at h; cases h
      | ok is =>
        simp only [decode, hh, hi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hrest, hf⟩ := (decodeInstructions_eq_ok rest is).mp hi
        exact ⟨by rw [(decodeHeader_eq_ok ws header rest).mp hh, hrest]; rfl, hf⟩
  · rintro ⟨rfl, hf⟩
    simp only [decode, Module.words, (decodeHeader_eq_ok _ m.header _).mpr rfl,
      decodeInstructions_words _ hf, bind, Except.bind, pure, Except.pure]

theorem bind_eq_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- Reading a file and decoding it accepts exactly the little-endian or big-endian storage of a module whose
instructions' word counts fit. -/
theorem words_decode_eq_ok (bytes : ByteArray) (m : Module) :
    (words bytes >>= decode) = .ok m ↔
      (bytes.toList = Spec.littleEndianBytes m.words ∨ bytes.toList = Spec.bigEndianBytes m.words) ∧
        ∀ i ∈ m.instructions, i.Fits := by
  rw [bind_eq_ok]
  constructor
  · rintro ⟨ws, hw, hd⟩
    obtain ⟨rfl, hf⟩ := (decode_eq_ok ws m).mp hd
    refine ⟨?_, hf⟩
    rcases (words_eq_ok bytes m.words).mp hw with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact .inl hb
    · exact .inr hb
  · rintro ⟨hb, hf⟩
    refine ⟨m.words, ?_, (decode_eq_ok _ _).mpr ⟨rfl, hf⟩⟩
    have hhead : m.words.head? = some Spec.magic := by simp [Module.words, Spec.Header.words]
    rw [words_eq_ok]
    rcases hb with hb | hb
    · exact .inl ⟨hb, by rw [hhead]; simpa using magic_ne_byteReverse⟩
    · exact .inr ⟨hb, hhead⟩

end Proofs
