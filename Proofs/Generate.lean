import Spec
import Spvbind
import Proofs.Instruction

/-!
# The generator puts every scalar where the decorations say
-/

namespace Proofs

open Spvbind
open Spec (Word Id Instruction Module LiteralString Location Located VariableLocated MatrixLayout MemberLayout)
open Spec.Cpp (Ty Member alignUp)
open Std (HashMap HashSet)

/-! Distinct elements, and what they make unique. -/

theorem distinct_go_eq_true {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (seen : HashSet α) (xs : List α) :
    distinct.go seen xs = true ↔ xs.Nodup ∧ ∀ x ∈ xs, seen.contains x = false := by
  induction xs generalizing seen with
  | nil => simp [distinct.go]
  | cons x xs ih =>
    simp only [distinct.go, Bool.and_eq_true, Bool.not_eq_true', ih, HashSet.contains_insert, List.nodup_cons,
      List.mem_cons, forall_eq_or_imp, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun hx => (h3 x hx).1 rfl, h2⟩, h1, fun y hy => (h3 y hy).2⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h2, fun y hy => ⟨fun h => h1 (h ▸ hy), h4 y hy⟩⟩

theorem distinct_eq_true {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (xs : List α) :
    distinct xs = true ↔ xs.Nodup := by
  simp [distinct, distinct_go_eq_true]

/-- Two elements that `f` maps to the same value are the same, if the values are distinct. -/
theorem eq_of_nodup_filterMap {α β : Type} {f : α → Option β} {l : List α} (h : (l.filterMap f).Nodup)
    {a b : α} {x : β} (ha : a ∈ l) (hb : b ∈ l) (hfa : f a = some x) (hfb : f b = some x) : a = b := by
  induction l with
  | nil => cases ha
  | cons c l ih =>
    rw [List.filterMap_cons] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · rw [hfa] at h
      exact absurd (List.mem_filterMap.mpr ⟨b, hb, hfb⟩) (List.nodup_cons.mp h).1
    · rw [hfb] at h
      exact absurd (List.mem_filterMap.mpr ⟨a, ha, hfa⟩) (List.nodup_cons.mp h).1
    · cases hc : f c with
      | none => rw [hc] at h; exact ih h ha hb
      | some y => rw [hc] at h; exact ih (List.nodup_cons.mp h).2 ha hb

theorem filterMap_sublist_filterMap {α β : Type} {f g : α → Option β} (hgf : ∀ a b, g a = some b → f a = some b)
    (l : List α) : (l.filterMap g).Sublist (l.filterMap f) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.filterMap_cons, List.filterMap_cons]
    cases hg : g c with
    | none =>
      cases f c with
      | none => exact ih
      | some _ => exact ih.cons _
    | some b => rw [hgf c b hg]; exact ih.cons_cons _

/-- A map built from pairs with distinct keys has exactly those pairs. -/
theorem getElem?_ofList_eq_some {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    {l : List (α × β)} (h : (l.map Prod.fst).Nodup) {k : α} {v : β} :
    (HashMap.ofList l)[k]? = some v ↔ (k, v) ∈ l := by
  have hd : l.Pairwise (fun a b => (a.1 == b.1) = false) := by
    rw [List.Nodup, List.pairwise_map] at h
    exact h.imp fun hne => beq_eq_false_iff_ne.mpr hne
  constructor
  · intro hk
    by_cases hc : (l.map Prod.fst).contains k = true
    · obtain ⟨⟨k', v'⟩, hm, hk'⟩ : ∃ p ∈ l, p.1 = k := by simpa using hc
      simp only at hk'
      subst hk'
      rw [HashMap.getElem?_ofList_of_mem BEq.rfl hd hm] at hk
      cases hk
      exact hm
    · rw [HashMap.getElem?_ofList_of_contains_eq_false (by simpa using hc)] at hk
      cases hk
  · exact HashMap.getElem?_ofList_of_mem BEq.rfl hd

/-! Where the scalars of a type are, given that each id is defined once. -/

section
variable {m : Module} (hnd : (m.instructions.filterMap result?).Nodup)
include hnd

theorem located_of_typeInt {t w s : Word} (hi : .typeInt t w s ∈ m.instructions) (layout : Option MatrixLayout)
    (l : Location) :
    Located m layout t l ↔ (s = 0 ∧ l = ⟨[], 0, .int w false⟩) ∨ (s = 1 ∧ l = ⟨[], 0, .int w true⟩) := by
  constructor
  · intro h
    cases h with
    | unsigned hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl; simp
    | signed hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl; simp
    | float hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl
    | member hs => cases eq_of_nodup_filterMap hnd hs hi rfl rfl
    | component hv => cases eq_of_nodup_filterMap hnd hv hi rfl rfl
    | element ha => cases eq_of_nodup_filterMap hnd ha hi rfl rfl
    | colMajor hm => cases eq_of_nodup_filterMap hnd hm hi rfl rfl
    | rowMajor hm => cases eq_of_nodup_filterMap hnd hm hi rfl rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .unsigned hi
    · exact .signed hi

theorem located_of_typeFloat {t w : Word} (hi : .typeFloat t w ∈ m.instructions) (layout : Option MatrixLayout)
    (l : Location) : Located m layout t l ↔ l = ⟨[], 0, .float w⟩ := by
  constructor
  · intro h
    cases h with
    | unsigned hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl
    | signed hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl
    | float hi' => cases eq_of_nodup_filterMap hnd hi' hi rfl rfl; rfl
    | member hs => cases eq_of_nodup_filterMap hnd hs hi rfl rfl
    | component hv => cases eq_of_nodup_filterMap hnd hv hi rfl rfl
    | element ha => cases eq_of_nodup_filterMap hnd ha hi rfl rfl
    | colMajor hm => cases eq_of_nodup_filterMap hnd hm hi rfl rfl
    | rowMajor hm => cases eq_of_nodup_filterMap hnd hm hi rfl rfl
  · rintro rfl
    exact .float hi

theorem located_of_typeStruct {t : Id} {all : List Id} (hs : .typeStruct t all ∈ m.instructions)
    (layout : Option MatrixLayout) (l : Location) :
    Located m layout t l ↔ ∃ (member byteOffset : Word) (u : Id) (l' : Location) (structName memberName : LiteralString)
      (memberLayout : Option MatrixLayout),
      all[member.toNat]? = some u ∧ .memberDecorate t member (.offset byteOffset) ∈ m.instructions ∧
      .name t structName ∈ m.instructions ∧ .memberName t member memberName ∈ m.instructions ∧
      MemberLayout m t member memberLayout ∧ Located m memberLayout u l' ∧
      l = ⟨.member structName.value member.toNat memberName.value :: l'.path, byteOffset.toNat + l'.offset,
        l'.scalar⟩ := by
  constructor
  · intro h
    cases h with
    | unsigned hi => cases eq_of_nodup_filterMap hnd hi hs rfl rfl
    | signed hi => cases eq_of_nodup_filterMap hnd hi hs rfl rfl
    | float hi => cases eq_of_nodup_filterMap hnd hi hs rfl rfl
    | member hs' hu hd hn hmn hml hl =>
      cases eq_of_nodup_filterMap hnd hs' hs rfl rfl
      exact ⟨_, _, _, _, _, _, _, hu, hd, hn, hmn, hml, hl, rfl⟩
    | component hv => cases eq_of_nodup_filterMap hnd hv hs rfl rfl
    | element ha => cases eq_of_nodup_filterMap hnd ha hs rfl rfl
    | colMajor hm => cases eq_of_nodup_filterMap hnd hm hs rfl rfl
    | rowMajor hm => cases eq_of_nodup_filterMap hnd hm hs rfl rfl
  · rintro ⟨member, byteOffset, u, l', structName, memberName, memberLayout, hu, hd, hn, hmn, hml, hl, rfl⟩
    exact .member hs hu hd hn hmn hml hl

theorem located_of_typeVector {t ct : Id} {n : Word} (hv : .typeVector t ct n ∈ m.instructions)
    (layout : Option MatrixLayout) (l : Location) :
    Located m layout t l ↔ ∃ (k : Word) (s : Spec.Scalar), k < n ∧ Located m layout ct ⟨[], 0, s⟩ ∧
      l = ⟨[.element k.toNat], k.toNat * s.bytes, s⟩ := by
  constructor
  · intro h
    cases h with
    | unsigned hi => cases eq_of_nodup_filterMap hnd hi hv rfl rfl
    | signed hi => cases eq_of_nodup_filterMap hnd hi hv rfl rfl
    | float hi => cases eq_of_nodup_filterMap hnd hi hv rfl rfl
    | member hs => cases eq_of_nodup_filterMap hnd hs hv rfl rfl
    | component hv' hk hl =>
      cases eq_of_nodup_filterMap hnd hv' hv rfl rfl
      exact ⟨_, _, hk, hl, rfl⟩
    | element ha => cases eq_of_nodup_filterMap hnd ha hv rfl rfl
    | colMajor hm => cases eq_of_nodup_filterMap hnd hm hv rfl rfl
    | rowMajor hm => cases eq_of_nodup_filterMap hnd hm hv rfl rfl
  · rintro ⟨k, s, hk, hl, rfl⟩
    exact .component hv hk hl

theorem located_of_typeArray {t et len : Id} (ha : .typeArray t et len ∈ m.instructions)
    (layout : Option MatrixLayout) (l : Location) :
    Located m layout t l ↔ ∃ (i : Nat) (lt : Id) (value stride : Word) (more : List Word) (l' : Location),
      .constant lt len value more ∈ m.instructions ∧ i < Spec.wordsValue value more ∧
      .decorate t (.arrayStride stride) ∈ m.instructions ∧ Located m layout et l' ∧
      l = ⟨.element i :: l'.path, i * stride.toNat + l'.offset, l'.scalar⟩ := by
  constructor
  · intro h
    cases h with
    | unsigned hi => cases eq_of_nodup_filterMap hnd hi ha rfl rfl
    | signed hi => cases eq_of_nodup_filterMap hnd hi ha rfl rfl
    | float hi => cases eq_of_nodup_filterMap hnd hi ha rfl rfl
    | member hs => cases eq_of_nodup_filterMap hnd hs ha rfl rfl
    | component hv => cases eq_of_nodup_filterMap hnd hv ha rfl rfl
    | element ha' hc hi hd hl =>
      cases eq_of_nodup_filterMap hnd ha' ha rfl rfl
      exact ⟨_, _, _, _, _, _, hc, hi, hd, hl, rfl⟩
    | colMajor hm => cases eq_of_nodup_filterMap hnd hm ha rfl rfl
    | rowMajor hm => cases eq_of_nodup_filterMap hnd hm ha rfl rfl
  · rintro ⟨i, lt, value, stride, more, l', hc, hi, hd, hl, rfl⟩
    exact .element ha hc hi hd hl

theorem located_of_typeMatrix {t ct : Id} {n : Word} (hm : .typeMatrix t ct n ∈ m.instructions)
    (layout : Option MatrixLayout) (l : Location) :
    Located m layout t l ↔ ∃ (componentType : Id) (rows column row stride : Word) (s : Spec.Scalar),
      .typeVector ct componentType rows ∈ m.instructions ∧ column < n ∧ row < rows ∧
      Located m layout componentType ⟨[], 0, s⟩ ∧
      ((layout = some ⟨stride, false⟩ ∧
          l = ⟨[.element column.toNat, .element row.toNat], column.toNat * stride.toNat + row.toNat * s.bytes, s⟩) ∨
        (layout = some ⟨stride, true⟩ ∧
          l = ⟨[.element row.toNat, .element column.toNat], row.toNat * stride.toNat + column.toNat * s.bytes, s⟩)) := by
  constructor
  · intro h
    cases h with
    | unsigned hi => cases eq_of_nodup_filterMap hnd hi hm rfl rfl
    | signed hi => cases eq_of_nodup_filterMap hnd hi hm rfl rfl
    | float hi => cases eq_of_nodup_filterMap hnd hi hm rfl rfl
    | member hs => cases eq_of_nodup_filterMap hnd hs hm rfl rfl
    | component hv => cases eq_of_nodup_filterMap hnd hv hm rfl rfl
    | element ha => cases eq_of_nodup_filterMap hnd ha hm rfl rfl
    | colMajor hm' hc hv hr hs =>
      cases eq_of_nodup_filterMap hnd hm' hm rfl rfl
      exact ⟨_, _, _, _, _, _, hv, hc, hr, hs, .inl ⟨rfl, rfl⟩⟩
    | rowMajor hm' hc hv hr hs =>
      cases eq_of_nodup_filterMap hnd hm' hm rfl rfl
      exact ⟨_, _, _, _, _, _, hv, hc, hr, hs, .inr ⟨rfl, rfl⟩⟩
  · rintro ⟨componentType, rows, column, row, stride, s, hv, hc, hr, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact .colMajor hm hc hv hr hs
    · exact .rowMajor hm hc hv hr hs

end

/-! The invariant of the pass over the types: every C++ type has exactly the scalars of its SPIR-V type. -/

/-- What the generator relies on about the maps it looks instructions up in. -/
structure Facts (m : Module) (ctx : Context) : Prop where
  results : (m.instructions.filterMap result?).Nodup
  offsets : ∀ t k o, ctx.offsets[(t, k)]? = some o ↔ .memberDecorate t k (.offset o) ∈ m.instructions
  names : ∀ t n, ctx.names[t]? = some n ↔ ∃ s, .name t s ∈ m.instructions ∧ s.value = n
  memberNames : ∀ t k n, ctx.memberNames[(t, k)]? = some n ↔ ∃ s, .memberName t k s ∈ m.instructions ∧ s.value = n
  strides : ∀ t s, ctx.strides[t]? = some s ↔ .decorate t (.arrayStride s) ∈ m.instructions
  constants : ∀ k n, ctx.constants[k]? = some n ↔
    ∃ (lt : Id) (value : Word) (more : List Word), .constant lt k value more ∈ m.instructions ∧
      Spec.wordsValue value more = n
  matrixStrides : ∀ t k s, ctx.matrixStrides[(t, k)]? = some s ↔ .memberDecorate t k (.matrixStride s) ∈ m.instructions
  rowMajors : ∀ t k, ctx.rowMajors[(t, k)]? = some () ↔ .memberDecorate t k .rowMajor ∈ m.instructions
  colMajors : ∀ t k, ctx.colMajors[(t, k)]? = some () ↔ .memberDecorate t k .colMajor ∈ m.instructions
  vectors : ∀ v ct n, ctx.vectors[v]? = some (ct, n) ↔ .typeVector v ct n ∈ m.instructions

def Correct (m : Module) (types : Types) : Prop :=
  ∀ t f, types[t]? = some f → ∀ (layout : Option MatrixLayout) c, f layout = .ok c →
    ∀ l, l ∈ c.locations ↔ Located m layout t l

theorem toNat_toUInt32 {k : Nat} (h : k < 2 ^ 32) : k.toUInt32.toNat = k :=
  UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)

/-- The layout the generator gives a member is what its decorations say. -/
theorem memberLayout_sound {m : Module} {ctx : Context} (hf : Facts m ctx) {t : Id} {k : Word}
    {layout : Option MatrixLayout} (h : memberLayout ctx t k = .ok layout) : MemberLayout m t k layout := by
  unfold memberLayout at h
  split at h
  case h_1 hs _ _ =>
    cases h
    exact .none fun stride hm => by
      have := (hf.matrixStrides t k stride).mpr hm
      rw [hs] at this
      cases this
  case h_2 stride hs hr _ =>
    cases h
    exact .rowMajor ((hf.matrixStrides _ _ _).mp hs) ((hf.rowMajors _ _).mp hr)
  case h_3 stride hs _ hc =>
    cases h
    exact .colMajor ((hf.matrixStrides _ _ _).mp hs) ((hf.colMajors _ _).mp hc)
  case h_4 => cases h

/-- And it is the only layout the decorations say. -/
theorem memberLayout_unique {m : Module} {ctx : Context} (hf : Facts m ctx) {t : Id} {k : Word}
    {layout layout' : Option MatrixLayout} (h : memberLayout ctx t k = .ok layout) (h' : MemberLayout m t k layout') :
    layout' = layout := by
  cases h' with
  | none hno =>
    unfold memberLayout at h
    split at h
    case h_1 => cases h; rfl
    case h_2 stride hs _ _ => exact absurd ((hf.matrixStrides _ _ _).mp hs) (hno stride)
    case h_3 stride hs _ _ => exact absurd ((hf.matrixStrides _ _ _).mp hs) (hno stride)
    case h_4 => cases h
  | rowMajor hs hr =>
    have hs' := (hf.matrixStrides _ _ _).mpr hs
    have hr' := (hf.rowMajors _ _).mpr hr
    unfold memberLayout at h
    rw [hs', hr'] at h
    split at h <;> cases h <;> simp_all
  | colMajor hs hc =>
    have hs' := (hf.matrixStrides _ _ _).mpr hs
    have hc' := (hf.colMajors _ _).mpr hc
    unfold memberLayout at h
    rw [hs', hc'] at h
    split at h <;> cases h <;> simp_all

theorem locations_members {m : Module} {ctx : Context} {types : Types} {t : Id} {all : List Id} {sn : String}
    (hf : Facts m ctx) (hc : Correct m types) (hsn : ctx.names[t]? = some sn) :
    ∀ (us : List Id) (k start : Nat) (ms : List Member), all.drop k = us →
      members ctx types t k start us = .ok ms →
      ∀ l, l ∈ Spec.Cpp.Members.locations sn k start ms ↔
        ∃ (member byteOffset : Word) (u : Id) (l' : Location) (structName memberName : LiteralString)
          (memberLayout : Option MatrixLayout),
          k ≤ member.toNat ∧ all[member.toNat]? = some u ∧
          .memberDecorate t member (.offset byteOffset) ∈ m.instructions ∧ .name t structName ∈ m.instructions ∧
          .memberName t member memberName ∈ m.instructions ∧ MemberLayout m t member memberLayout ∧
          Located m memberLayout u l' ∧
          l = ⟨.member structName.value member.toNat memberName.value :: l'.path, byteOffset.toNat + l'.offset,
            l'.scalar⟩ := by
  intro us
  induction us with
  | nil =>
    intro k start ms hdrop h l
    simp only [members, Except.ok.injEq] at h
    subst h
    simp only [Spec.Cpp.Members.locations, List.not_mem_nil, false_iff, not_exists, not_and]
    intro member _ u _ _ _ _ hk hu
    have h1 := List.drop_eq_nil_iff.mp hdrop
    have h2 := (List.getElem?_eq_some_iff.mp hu).1
    omega
  | cons u us ih =>
    intro k start ms hdrop h l
    have hu : all[k]? = some u := by
      have := congrArg (·[0]?) hdrop
      simpa [List.getElem?_drop] using this
    have hdrop' : all.drop (k + 1) = us := by
      rw [← List.drop_drop, hdrop]; rfl
    unfold members at h
    split at h
    case isFalse => cases h
    rename_i hk32
    split at h
    case h_1 f byteOffset name hft hoff hmn =>
      split at h
      · cases h
      split at h
      case h_1 => cases h
      rename_i layout hlay
      split at h
      case h_1 => cases h
      rename_i c hfc
      split at h
      case isFalse => cases h
      rename_i hle
      split at h
      case h_2 => cases h
      rename_i rest hrest
      cases h
      have hkk := toNat_toUInt32 hk32
      have ha : alignUp (start + (byteOffset.toNat - start)) c.align = byteOffset.toNat := by
        rw [Nat.add_sub_cancel' hle.1]
        simp [alignUp, hle.2]
      simp only [Spec.Cpp.Members.locations, ha, List.mem_append, List.mem_map,
        ih (k + 1) (byteOffset.toNat + c.size) rest hdrop' hrest l]
      constructor
      · rintro (⟨l', hl', rfl⟩ | ⟨member, byteOffset', u', l', sName, mName, lay, hk, hu', hd, hn, hmn', hml, hl, rfl⟩)
        · obtain ⟨sName, hn, hsv⟩ := (hf.names _ _).mp hsn
          obtain ⟨mName, hmn', hmv⟩ := (hf.memberNames _ _ _).mp hmn
          refine ⟨k.toUInt32, byteOffset, u, l', sName, mName, layout, by omega, by rw [hkk]; exact hu,
            (hf.offsets _ _ _).mp hoff, hn, hmn', memberLayout_sound hf hlay, (hc u f hft layout c hfc l').mp hl',
            by rw [hkk, hsv, hmv]⟩
        · exact ⟨member, byteOffset', u', l', sName, mName, lay, by omega, hu', hd, hn, hmn', hml, hl, rfl⟩
      · rintro ⟨member, byteOffset', u', l', sName, mName, lay, hk, hu', hd, hn, hmn', hml, hl, rfl⟩
        by_cases hm : member.toNat = k
        · have hmk : member = k.toUInt32 := UInt32.toNat_inj.mp (by rw [hm, hkk])
          subst hmk
          rw [hkk, hu] at hu'
          cases hu'
          have ho := (hf.offsets _ _ _).mpr hd
          rw [hoff] at ho
          cases ho
          have hs := (hf.names _ _).mpr ⟨_, hn, rfl⟩
          rw [hsn] at hs
          cases hs
          have hms := (hf.memberNames _ _ _).mpr ⟨_, hmn', rfl⟩
          rw [hmn] at hms
          cases hms
          cases memberLayout_unique hf hlay hml
          exact .inl ⟨l', (hc u f hft layout c hfc l').mpr hl, by rw [hkk]⟩
        · exact .inr ⟨member, byteOffset', u', l', sName, mName, lay, by omega, hu', hd, hn, hmn', hml, hl, rfl⟩
    all_goals cases h

theorem locations_struct {m : Module} {ctx : Context} {types : Types} {t : Id} {all : List Id} {c : Ty}
    (hf : Facts m ctx) (hc : Correct m types) (hs : .typeStruct t all ∈ m.instructions)
    (h : struct ctx types t all = .ok c) (layout : Option MatrixLayout) (l : Location) :
    l ∈ c.locations ↔ Located m layout t l := by
  unfold struct at h
  split at h
  · cases h
  rename_i name hname
  split at h
  · cases h
  split at h
  · cases h
  split at h
  case h_2 => cases h
  rename_i ms hms
  cases h
  simp only [Ty.locations, locations_members hf hc hname all 0 0 ms (List.drop_zero) hms l,
    located_of_typeStruct hf.results hs layout l, Nat.zero_le, true_and]

/-- The scalars of an array of arrays of a scalar: the only shape matrices take. -/
theorem mem_locations_array_array (s : Spec.Scalar) (inner outer : Nat) (l : Location) :
    l ∈ (Ty.array (Ty.array (.scalar s) inner) outer).locations ↔
      ∃ o i, o < outer ∧ i < inner ∧ l = ⟨[.element o, .element i], o * (inner * s.bytes) + i * s.bytes, s⟩ := by
  simp only [Ty.locations, Ty.size, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨o, ho, l', ⟨i, hi, l'', rfl, rfl⟩, rfl⟩
    exact ⟨o, i, ho, hi, by simp⟩
  · rintro ⟨o, i, ho, hi, rfl⟩
    exact ⟨o, ho, _, ⟨i, hi, _, rfl, rfl⟩, by simp⟩

theorem correct_addType {m : Module} {ctx : Context} {types : Types} {i : Instruction} (hf : Facts m ctx)
    (hc : Correct m types) (hi : i ∈ m.instructions) : Correct m (addType ctx types i) := by
  intro t f ht layout c hfc l
  cases i
  case typeInt r w s =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    simp only at hfc
    rw [located_of_typeInt hf.results hi layout l]
    unfold int at hfc
    split at hfc
    case isFalse => cases hfc
    split at hfc
    · cases hfc; simp_all [Ty.locations]
    split at hfc
    · cases hfc; simp_all [Ty.locations]
    · cases hfc
  case typeFloat r w =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    simp only at hfc
    rw [located_of_typeFloat hf.results hi layout l]
    unfold float at hfc
    split at hfc
    · cases hfc; simp [Ty.locations]
    · cases hfc
  case typeStruct r all =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    simp only at hfc
    exact locations_struct hf hc hi hfc layout l
  case typeVector r ct n =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    rw [located_of_typeVector hf.results hi layout l]
    unfold vector at hfc
    split at hfc
    case h_1 g hg =>
      split at hfc
      case h_1 s hgs =>
        split at hfc
        case isFalse => cases hfc
        cases hfc
        have hs : ∀ s', Located m layout ct ⟨[], 0, s'⟩ ↔ s' = s := fun s' => by
          rw [← hc ct g hg layout (.scalar s) hgs]
          simp [Ty.locations]
        have hn := n.toNat_lt
        simp only [Ty.locations, Ty.size, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_singleton, hs]
        constructor
        · rintro ⟨i, hi, l', rfl, rfl⟩
          exact ⟨i.toUInt32, s, UInt32.lt_iff_toNat_lt.mpr (by rw [toNat_toUInt32 (by omega)]; exact hi), rfl,
            by rw [toNat_toUInt32 (by omega)]; simp⟩
        · rintro ⟨k, _, hk, rfl, rfl⟩
          exact ⟨k.toNat, UInt32.lt_iff_toNat_lt.mp hk, _, rfl, by simp⟩
      all_goals cases hfc
    all_goals cases hfc
  case typeArray r et len =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    rw [located_of_typeArray hf.results hi layout l]
    unfold array at hfc
    split at hfc
    case h_1 g n stride hg hlen hstride =>
      split at hfc
      case h_1 e hge =>
        split at hfc
        case isFalse => cases hfc
        rename_i hok
        cases hfc
        have hcn : ∀ lt value more, .constant lt len value more ∈ m.instructions → Spec.wordsValue value more = n := by
          intro lt value more hm
          have := (hf.constants len _).mpr ⟨lt, value, more, hm, rfl⟩
          rw [hlen] at this
          cases this
          rfl
        have hsn : ∀ s', .decorate r (.arrayStride s') ∈ m.instructions → s' = stride := by
          intro s' hm
          have := (hf.strides r s').mpr hm
          rw [hstride] at this
          cases this
          rfl
        obtain ⟨lt, value, more, hm, hv⟩ := (hf.constants len n).mp hlen
        have hsm := (hf.strides r stride).mp hstride
        simp only [Ty.locations, List.mem_flatMap, List.mem_range, List.mem_map]
        constructor
        · rintro ⟨i, hi, l', hl', rfl⟩
          exact ⟨i, lt, value, stride, more, l', hm, hv ▸ hi, hsm, (hc et g hg layout e hge l').mp hl',
            by rw [hok.1]⟩
        · rintro ⟨i, lt', value', stride', more', l', hm', hi, hsm', hl', rfl⟩
          rw [hcn lt' value' more' hm'] at hi
          rw [hsn stride' hsm']
          exact ⟨i, hi, l', (hc et g hg layout e hge l').mpr hl', by rw [hok.1]⟩
      all_goals cases hfc
    all_goals cases hfc
  case typeMatrix r ct n =>
    simp only [addType, HashMap.getElem?_insert, beq_iff_eq] at ht
    split at ht
    case isFalse => exact hc t f ht layout c hfc l
    rename_i hrt
    subst hrt
    simp only [Option.some.injEq] at ht
    subst ht
    rw [located_of_typeMatrix hf.results hi layout l]
    unfold matrix at hfc
    split at hfc
    case h_1 => cases hfc
    rename_i stride rowMajor
    split at hfc
    case h_1 => cases hfc
    rename_i componentType rows hvec
    split at hfc
    case h_1 => cases hfc
    rename_i g hg
    split at hfc
    case h_1 s hgs =>
      have hv := (hf.vectors _ _ _).mp hvec
      have hvu : ∀ ct' rows', .typeVector ct ct' rows' ∈ m.instructions → ct' = componentType ∧ rows' = rows := by
        intro ct' rows' h'
        cases eq_of_nodup_filterMap hf.results h' hv rfl rfl
        exact ⟨rfl, rfl⟩
      have hs : ∀ s', Located m (some ⟨stride, rowMajor⟩) componentType ⟨[], 0, s'⟩ ↔ s' = s := fun s' => by
        rw [← hc componentType g hg _ (.scalar s) hgs]
        simp [Ty.locations]
      have hn := n.toNat_lt
      have hr := rows.toNat_lt
      split at hfc
      · -- row-major: rows of columns
        rename_i hrm
        subst hrm
        split at hfc
        case isFalse => cases hfc
        rename_i hok
        cases hfc
        rw [mem_locations_array_array]
        constructor
        · rintro ⟨o, i, ho, hi, rfl⟩
          refine ⟨componentType, rows, i.toUInt32, o.toUInt32, stride, s, hv,
            UInt32.lt_iff_toNat_lt.mpr (by rw [toNat_toUInt32 (by omega)]; exact hi),
            UInt32.lt_iff_toNat_lt.mpr (by rw [toNat_toUInt32 (by omega)]; exact ho), (hs s).mpr rfl, .inr ⟨rfl, ?_⟩⟩
          rw [toNat_toUInt32 (by omega), toNat_toUInt32 (by omega), hok.2.2]
        · rintro ⟨ct', rows', column, row, stride', s', hv', hcol, hrow, hs', ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩
          · cases h1
          · obtain ⟨rfl, rfl⟩ := hvu ct' rows' hv'
            cases (hs s').mp hs'
            simp only [Option.some.injEq, MatrixLayout.mk.injEq, and_true] at h1
            subst h1
            exact ⟨row.toNat, column.toNat, UInt32.lt_iff_toNat_lt.mp hrow, UInt32.lt_iff_toNat_lt.mp hcol,
              by rw [hok.2.2]⟩
      · -- column-major: columns of rows
        rename_i hrm
        simp only [Bool.not_eq_true] at hrm
        subst hrm
        split at hfc
        case isFalse => cases hfc
        rename_i hok
        cases hfc
        rw [mem_locations_array_array]
        constructor
        · rintro ⟨o, i, ho, hi, rfl⟩
          refine ⟨componentType, rows, o.toUInt32, i.toUInt32, stride, s, hv,
            UInt32.lt_iff_toNat_lt.mpr (by rw [toNat_toUInt32 (by omega)]; exact ho),
            UInt32.lt_iff_toNat_lt.mpr (by rw [toNat_toUInt32 (by omega)]; exact hi), (hs s).mpr rfl, .inl ⟨rfl, ?_⟩⟩
          rw [toNat_toUInt32 (by omega), toNat_toUInt32 (by omega), hok.2.2]
        · rintro ⟨ct', rows', column, row, stride', s', hv', hcol, hrow, hs', ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩
          · obtain ⟨rfl, rfl⟩ := hvu ct' rows' hv'
            cases (hs s').mp hs'
            simp only [Option.some.injEq, MatrixLayout.mk.injEq, and_true] at h1
            subst h1
            exact ⟨column.toNat, row.toNat, UInt32.lt_iff_toNat_lt.mp hcol, UInt32.lt_iff_toNat_lt.mp hrow,
              by rw [hok.2.2]⟩
          · cases h1
    all_goals cases hfc
  all_goals exact hc t f ht layout c hfc l

theorem correct_foldl {m : Module} {ctx : Context} (hf : Facts m ctx) :
    ∀ (is : List Instruction) (types : Types), (∀ i ∈ is, i ∈ m.instructions) → Correct m types →
      Correct m (is.foldl (addType ctx) types) := by
  intro is
  induction is with
  | nil => intro types _ hc; exact hc
  | cons i is ih =>
    intro types hm hc
    exact ih _ (fun j hj => hm j (by simp [hj])) (correct_addType hf hc (hm i (by simp)))

theorem correct_empty (m : Module) : Correct m ∅ := by
  intro t f ht
  simp at ht

theorem mem_blocks {types : Types} {pointers : HashMap Id Id} {v : Id} {c : Ty} :
    ∀ (vars : List (Id × Id)) (out : List (Id × Ty)), blocks types pointers vars = .ok out → (v, c) ∈ out →
      ∃ p t f, (v, p) ∈ vars ∧ pointers[p]? = some t ∧ types[t]? = some f ∧ f none = .ok c := by
  intro vars
  induction vars with
  | nil => intro out h hm; simp only [blocks, Except.ok.injEq] at h; subst h; cases hm
  | cons var vars ih =>
    intro out h hm
    obtain ⟨v', p⟩ := var
    unfold blocks at h
    split at h
    · cases h
    rename_i t hp
    split at h
    case h_1 => cases h
    rename_i f hf
    split at h
    case h_1 => cases h
    rename_i c' hfc
    split at h
    case h_2 => cases h
    rename_i rest hrest
    cases h
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact ⟨p, t, f, by simp, hp, hf, hfc⟩
    · obtain ⟨p', t', f', hv, hp', hf', hfc'⟩ := ih rest hrest h
      exact ⟨p', t', f', by simp [hv], hp', hf', hfc'⟩

theorem map_fst_blocks {types : Types} {pointers : HashMap Id Id} :
    ∀ (vars : List (Id × Id)) (out : List (Id × Ty)), blocks types pointers vars = .ok out →
      out.map Prod.fst = vars.map Prod.fst := by
  intro vars
  induction vars with
  | nil => intro out h; simp only [blocks, Except.ok.injEq] at h; subst h; rfl
  | cons var vars ih =>
    intro out h
    obtain ⟨v, p⟩ := var
    unfold blocks at h
    split at h
    · cases h
    split at h
    case h_1 => cases h
    split at h
    case h_1 => cases h
    split at h
    case h_2 => cases h
    rename_i rest hrest
    cases h
    simp [ih rest hrest]

/-! The generator. -/

theorem pushConstant?_eq_some (i : Instruction) (v p : Id) :
    pushConstant? i = some (v, p) ↔ ∃ initializer, i = .var p v Spec.PushConstant initializer := by
  cases i <;> simp only [pushConstant?, reduceCtorEq, false_iff, not_exists, not_false_eq_true, implies_true]
  case var resultType result storageClass initializer =>
    split <;> simp_all [and_comm, eq_comm]

theorem offset?_eq_some (i : Instruction) (t k o : Word) :
    offset? i = some ((t, k), o) ↔ i = .memberDecorate t k (.offset o) := by
  cases i <;> simp [offset?]
  case memberDecorate d => cases d <;> simp [and_assoc]

theorem matrixStride?_eq_some (i : Instruction) (t k s : Word) :
    matrixStride? i = some ((t, k), s) ↔ i = .memberDecorate t k (.matrixStride s) := by
  cases i <;> simp [matrixStride?]
  case memberDecorate d => cases d <;> simp [and_assoc]

theorem rowMajor?_eq_some (i : Instruction) (t k : Word) :
    rowMajor? i = some ((t, k), ()) ↔ i = .memberDecorate t k .rowMajor := by
  cases i <;> simp [rowMajor?]
  case memberDecorate d => cases d <;> simp

theorem colMajor?_eq_some (i : Instruction) (t k : Word) :
    colMajor? i = some ((t, k), ()) ↔ i = .memberDecorate t k .colMajor := by
  cases i <;> simp [colMajor?]
  case memberDecorate d => cases d <;> simp

theorem generate_correct (ws : List Word) (out : List (Id × Ty)) (h : generate ws = .ok out) :
    ∃ m : Module, ws = m.words ∧ (out.map Prod.fst).Nodup ∧
      (∀ v, v ∈ out.map Prod.fst ↔ Spec.PushConstantVariable m v) ∧
      ∀ v c, (v, c) ∈ out → ∀ l, l ∈ c.locations ↔ VariableLocated m v l := by
  cases hd : decode ws with
  | error e => simp [generate, hd, bind, Except.bind] at h
  | ok m =>
    refine ⟨m, ((decode_eq_ok ws m).mp hd).1, ?_⟩
    cases hv : checkVersion m.header with
    | error e => simp [generate, hd, hv, bind, Except.bind] at h
    | ok _ =>
    cases hr : distinct (m.instructions.filterMap result?) with
    | false => simp [generate, hd, hv, hr, bind, Except.bind] at h
    | true =>
    cases ho : distinct ((m.instructions.filterMap offset?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, bind, Except.bind] at h
    | true =>
    cases hn : distinct ((m.instructions.filterMap name?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, bind, Except.bind] at h
    | true =>
    cases hmn : distinct ((m.instructions.filterMap memberName?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, hmn, bind, Except.bind] at h
    | true =>
    cases hst : distinct ((m.instructions.filterMap arrayStride?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, hmn, hst, bind, Except.bind] at h
    | true =>
    cases hms : distinct ((m.instructions.filterMap matrixStride?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, hmn, hst, hms, bind, Except.bind] at h
    | true =>
    cases hrm : distinct ((m.instructions.filterMap rowMajor?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, hmn, hst, hms, hrm, bind, Except.bind] at h
    | true =>
    cases hcm : distinct ((m.instructions.filterMap colMajor?).map Prod.fst) with
    | false => simp [generate, hd, hv, hr, ho, hn, hmn, hst, hms, hrm, hcm, bind, Except.bind] at h
    | true =>
    simp only [generate, hd, hv, hr, ho, hn, hmn, hst, hms, hrm, hcm, bind, Except.bind, ↓reduceIte] at h
    have hnd := (distinct_eq_true _).mp hr
    have hno := (distinct_eq_true _).mp ho
    have hck : ((m.instructions.filterMap constant?).map Prod.fst).Nodup := by
      rw [List.map_filterMap]
      exact hnd.sublist (filterMap_sublist_filterMap (fun i x hx => by cases i <;> simp_all [constant?, result?]) _)
    have hvk : ((m.instructions.filterMap vector?).map Prod.fst).Nodup := by
      rw [List.map_filterMap]
      exact hnd.sublist (filterMap_sublist_filterMap (fun i x hx => by cases i <;> simp_all [vector?, result?]) _)
    have hf : Facts m ⟨.ofList (m.instructions.filterMap offset?), .ofList (m.instructions.filterMap name?),
        .ofList (m.instructions.filterMap memberName?), .ofList (m.instructions.filterMap arrayStride?),
        .ofList (m.instructions.filterMap constant?), .ofList (m.instructions.filterMap matrixStride?),
        .ofList (m.instructions.filterMap rowMajor?), .ofList (m.instructions.filterMap colMajor?),
        .ofList (m.instructions.filterMap vector?)⟩ := by
      refine ⟨hnd, fun t k o => ?_, fun t n => ?_, fun t k n => ?_, fun t s => ?_, fun k n => ?_, fun t k s => ?_,
        fun t k => ?_, fun t k => ?_, fun v ct n => ?_⟩
      · rw [getElem?_ofList_eq_some hno, List.mem_filterMap]
        simp [offset?_eq_some]
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hn), List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hni⟩
          cases i <;> simp only [name?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hni
          obtain ⟨rfl, rfl⟩ := hni
          exact ⟨_, hi, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨_, hs, rfl⟩
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hmn), List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hni⟩
          cases i <;> simp only [memberName?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hni
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hni
          exact ⟨_, hi, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨_, hs, rfl⟩
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hst), List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hsi⟩
          cases i <;> simp only [arrayStride?, reduceCtorEq] at hsi
          rename_i d
          cases d <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hsi
          obtain ⟨rfl, rfl⟩ := hsi
          exact hi
        · intro hi
          exact ⟨_, hi, rfl⟩
      · rw [getElem?_ofList_eq_some hck, List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hci⟩
          cases i <;> simp only [constant?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hci
          obtain ⟨rfl, rfl⟩ := hci
          exact ⟨_, _, _, hi, rfl⟩
        · rintro ⟨lt, value, more, hm, rfl⟩
          exact ⟨_, hm, rfl⟩
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hms), List.mem_filterMap]
        simp [matrixStride?_eq_some]
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hrm), List.mem_filterMap]
        simp [rowMajor?_eq_some]
      · rw [getElem?_ofList_eq_some ((distinct_eq_true _).mp hcm), List.mem_filterMap]
        simp [colMajor?_eq_some]
      · rw [getElem?_ofList_eq_some hvk, List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hvi⟩
          cases i <;> simp only [vector?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hvi
          obtain ⟨rfl, rfl, rfl⟩ := hvi
          exact hi
        · intro hi
          exact ⟨_, hi, rfl⟩
    have hc := correct_foldl hf m.instructions ∅ (fun _ h => h) (correct_empty m)
    have hpk : ((m.instructions.filterMap pointer?).map Prod.fst).Nodup := by
      rw [List.map_filterMap]
      exact hnd.sublist (filterMap_sublist_filterMap (fun i x hx => by cases i <;> simp_all [pointer?, result?]) _)
    have hfst := map_fst_blocks _ _ h
    refine ⟨?_, fun v => ?_, ?_⟩
    · rw [hfst, List.map_filterMap]
      refine hnd.sublist (filterMap_sublist_filterMap (fun i x hx => ?_) _)
      cases i <;> simp only [pushConstant?, Option.map_none, reduceCtorEq] at hx
      split at hx <;> simp_all [result?]
    · rw [hfst, List.mem_map]
      constructor
      · rintro ⟨⟨v', p⟩, hm, rfl⟩
        obtain ⟨i, hi, hpi⟩ := List.mem_filterMap.mp hm
        obtain ⟨initializer, rfl⟩ := (pushConstant?_eq_some _ _ _).mp hpi
        exact ⟨p, initializer, hi⟩
      · rintro ⟨p, initializer, hi⟩
        exact ⟨(v, p), List.mem_filterMap.mpr ⟨_, hi, (pushConstant?_eq_some _ _ _).mpr ⟨initializer, rfl⟩⟩, rfl⟩
    intro v c hm l
    obtain ⟨p, t, f, hv, hp, ht, hfc⟩ := mem_blocks _ _ h hm
    rw [hc t f ht none c hfc l]
    obtain ⟨iv, hiv, hpv⟩ := List.mem_filterMap.mp hv
    obtain ⟨ip, hip, hpp⟩ := List.mem_filterMap.mp ((getElem?_ofList_eq_some hpk).mp hp)
    cases iv <;> simp only [pushConstant?, reduceCtorEq] at hpv
    split at hpv
    case isFalse => cases hpv
    cases hpv
    cases ip <;> simp only [pointer?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hpp
    obtain ⟨rfl, rfl⟩ := hpp
    constructor
    · exact fun hl => .mk hiv hip hl
    · rintro ⟨hvar, hptr, hl⟩
      cases eq_of_nodup_filterMap hnd hvar hiv rfl rfl
      cases eq_of_nodup_filterMap hnd hptr hip rfl rfl
      exact hl

/-- `generate_correct` for the bytes of a file, as `Main.lean` runs it: the input is the little-endian or big-endian
storage of the module. -/
theorem generate_correct_of_bytes (bytes : ByteArray) (out : List (Id × Ty))
    (h : (words bytes >>= generate) = .ok out) :
    ∃ m : Module, (bytes.toList = Spec.littleEndianBytes m.words ∨ bytes.toList = Spec.bigEndianBytes m.words) ∧
      (out.map Prod.fst).Nodup ∧
      (∀ v, v ∈ out.map Prod.fst ↔ Spec.PushConstantVariable m v) ∧
      ∀ v c, (v, c) ∈ out → ∀ l, l ∈ c.locations ↔ VariableLocated m v l := by
  obtain ⟨ws, hw, hg⟩ := (bind_eq_ok _ _ _).mp h
  obtain ⟨m, rfl, h1, h2, h3⟩ := generate_correct ws out hg
  refine ⟨m, ?_, h1, h2, h3⟩
  rcases (words_eq_ok bytes m.words).mp hw with ⟨hb, _⟩ | ⟨hb, _⟩
  · exact .inl hb
  · exact .inr hb

end Proofs
