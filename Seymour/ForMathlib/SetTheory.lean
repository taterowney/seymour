import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.SymmDiff
import Mathlib.Tactic

/-!
This provides lemmas about sets (mostly dealing with disjointness) that are missing in Mathlib.
We do not use out custom notation here because this file is higher than `Basic.lean` in the import hierarchy.
-/

variable {α : Type}


section Other

/-- todo: desc -/
lemma setminus_inter_union_eq_union {X Y : Set α} : X \ (X ∩ Y) ∪ Y = X ∪ Y := by
  ext a
  constructor
  · intro ha
    cases ha with
    | inl ha' =>
      left
      exact Set.mem_of_mem_diff ha'
    | inr haY =>
      right
      exact haY
  · simp

/-- todo: desc -/
lemma nonempty_inter_not_ssubset_empty_inter {A B E : Set α} (hA : (A ∩ E).Nonempty) (hB : B ∩ E = ∅) :
    ¬(A ⊂ B) := by
  by_contra hAB
  obtain ⟨hAsubB, _hnBsubA⟩ := hAB
  obtain ⟨x, hxAE⟩  := hA
  have hxBE : x ∈ B ∩ E := (Set.inter_subset_inter hAsubB fun ⦃a⦄ a => a) hxAE
  rw [hB] at hxBE
  tauto

/-- todo: desc -/
lemma ssubset_self_union_other_elem {a : α} {X : Set α} (ha : a ∉ X) :
    X ⊂ X ∪ {a} := by
  constructor
  · exact Set.subset_union_left
  · by_contra hX
    rw [Set.union_subset_iff] at hX
    obtain ⟨_, haa⟩ := hX
    tauto

/-- todo: desc -/
lemma singleton_union_ssubset_union_iff {a : α} {A B : Set α} (haA : a ∉ A) (haB : a ∉ B) :
    A ∪ {a} ⊂ B ∪ {a} ↔ A ⊂ B := by
  constructor
  · intro hAB
    obtain ⟨hABl, hABr⟩ := hAB
    constructor
    · intro x hx
      apply ne_of_mem_of_not_mem hx at haA
      cases hABl (Set.mem_union_left {a} hx) <;> tauto
    · by_contra hBA
      apply Set.union_subset_union_left {a} at hBA
      tauto
  · intro hAB
    obtain ⟨hABl, hABr⟩ := hAB
    constructor
    · exact Set.union_subset_union_left {a} hABl
    · by_contra hBA
      rw [Set.union_singleton, Set.union_singleton] at hBA
      apply (Set.insert_subset_insert_iff haB).mp at hBA
      tauto

/-- todo: desc -/
lemma ssub_parts_ssub {A B E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) (hB : B ⊆ E₁ ∪ E₂) : (A ∩ E₁ ⊂ B ∩ E₁) ∧ (A ∩ E₂ ⊂ B ∩ E₂) → A ⊂ B := by
  intro ⟨hAB₁, hAB₂⟩
  constructor
  · obtain ⟨hE₁, _⟩ := hAB₁
    obtain ⟨hE₂, _⟩ := hAB₂
    apply Set.union_subset_union hE₁ at hE₂
    rw [←Set.inter_union_distrib_left, ←Set.inter_union_distrib_left] at hE₂
    rw [←Set.left_eq_inter.mpr, ←Set.left_eq_inter.mpr] at hE₂
    exact hE₂
    exact hB
    exact hA
  · by_contra hBA
    obtain ⟨_, hE₁⟩ := hAB₁
    obtain ⟨x, hxBE₁, hxnAE₁⟩ := Set.not_subset.mp hE₁
    have hxB : x ∈ B := Set.mem_of_mem_inter_left hxBE₁
    have hxE₁ : x ∈ E₁ := Set.mem_of_mem_inter_right hxBE₁
    tauto

/-- todo: desc -/
lemma sub_parts_eq {A E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) : (A ∩ E₁) ∪ (A ∩ E₂) = A :=
  ((subset_of_subset_of_eq
    (Set.subset_inter (fun _ => id) hA)
    (Set.inter_union_distrib_left A E₁ E₂)).antisymm
  (Set.union_subset Set.inter_subset_left Set.inter_subset_left)).symm

/-- todo: desc -/
lemma elem_notin_set_minus_singleton (a : α) (X : Set α) : a ∉ X \ {a} := Set.not_mem_diff_of_mem rfl

/-- todo: desc -/
lemma sub_union_diff_sub_union {A B C : Set α} (hA : A ⊆ B \ C) : A ⊆ B :=
  fun _ hA' => Set.diff_subset (hA hA')

/-- todo: desc -/
lemma singleton_inter_subset_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by
  have haXY : a ∈ X ∩ Y := by rw [ha]; rfl
  have haX : a ∈ X := Set.mem_of_mem_inter_left haXY
  rwa [←Set.singleton_subset_iff] at haX

/-- todo: desc -/
lemma singleton_inter_subset_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by
  rw [Set.inter_comm] at ha
  exact singleton_inter_subset_left ha

/-- Being a subset is preserved under subtracting sets. -/
lemma diff_subset_parent {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ \ X₂ ⊆ E :=
  Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₁E X₂)

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_left {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ ∩ X₂ ⊆ E :=
  (Set.inter_subset_inter_left X₂ hX₁E).trans Set.inter_subset_left

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_right {X₁ X₂ E : Set α} (hX₂E : X₂ ⊆ E) :
    X₁ ∩ X₂ ⊆ E := by
  rw [Set.inter_comm]
  exact inter_subset_parent_left hX₂E

/-- Intersection of two sets is subset of their union. -/
lemma inter_subset_union {X₁ X₂ : Set α} :
    X₁ ∩ X₂ ⊆ X₁ ∪ X₂ := by
  exact inter_subset_parent_left Set.subset_union_left

/-- todo: desc -/
lemma subset_diff_empty_eq {A B : Set α}
    (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B :=
  Set.union_empty A ▸ hBA ▸ Set.union_diff_cancel hAB

end Other


section Disjoint

/-- todo: desc -/
lemma Disjoint.ni_of_in {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ X) :
    a ∉ Y := by
  intro ha'
  simpa [hXY.inter_eq] using Set.mem_inter ha ha'

/-- todo: desc -/
lemma disjoint_of_singleton_inter_left_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) Y := by
  rw [Set.disjoint_iff_forall_ne]
  intro u huXa v hvY huv
  have hua : u ≠ a
  · aesop
  have huX : u ∈ X
  · aesop
  have huXY := Set.mem_inter huX (huv ▸ hvY)
  rw [hXY, Set.mem_singleton_iff] at huXY
  exact hua huXY

/-- todo: desc -/
lemma disjoint_of_singleton_inter_right_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint X (Y \ {a}) := by
  rw [disjoint_comm]
  rw [Set.inter_comm] at hXY
  exact disjoint_of_singleton_inter_left_wo hXY

/-- todo: desc -/
lemma disjoint_of_singleton_inter_both_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    Disjoint (X \ {a}) (Y \ {a}) :=
  Disjoint.disjoint_sdiff_left (disjoint_of_singleton_inter_right_wo hXY)

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_left {X Y Z : Set α} {a : α} (hXY : X ∩ Y = {a}) (hZ : Z ⊆ X) (haZ : a ∉ Z) :
    Disjoint Z Y := by
  have hYeq : (Y \ {a}) ∪ {a} = Y := (Set.diff_union_of_subset (singleton_inter_subset_right hXY))
  rw [←hYeq, Set.disjoint_union_right]
  constructor
  · exact Set.disjoint_of_subset_left hZ (disjoint_of_singleton_inter_right_wo hXY)
  · exact Set.disjoint_singleton_right.mpr haZ

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_right {X Y Z : Set α} {a : α} (hXY : X ∩ Y = {a}) (hZ : Z ⊆ Y) (haZ : a ∉ Z) :
    Disjoint X Z := by
  rw [Set.inter_comm] at hXY
  rw [disjoint_comm]
  exact disjoint_of_singleton_inter_subset_left hXY hZ haZ

/-- todo: desc -/
lemma disjoint_nonempty_not_subset {A B : Set α} (hAB : Disjoint A B) (hA : A.Nonempty) :
    ¬(A ⊆ B) := by
  intro contr
  simp [Disjoint.eq_bot_of_le hAB, contr] at hA

/-- todo: desc -/
lemma disjoint_nonempty_not_ssubset {A B : Set α} (hAB : Disjoint A B) (hA : A.Nonempty) :
    ¬(A ⊂ B) := by
  apply disjoint_nonempty_not_subset hAB at hA
  intro ⟨_, _⟩
  tauto

/-- todo: desc -/
lemma ssubset_union_disjoint_nonempty {X Y : Set α} (hXY : Disjoint X Y) (hY : Y.Nonempty) :
    X ⊂ X ∪ Y := by
  constructor
  · exact Set.subset_union_left
  · by_contra hX
    apply Set.diff_subset_diff_left at hX
    rw [Set.union_diff_cancel_left (Set.disjoint_iff.mp hXY), Set.diff_self] at hX
    exact Set.not_nonempty_empty (Set.eq_empty_of_subset_empty hX ▸ hY)

/-- todo: desc -/
lemma union_ssubset_union_iff {A B X : Set α} (hAX : Disjoint A X) (hBX : Disjoint B X) :
    A ∪ X ⊂ B ∪ X ↔ A ⊂ B := by
  constructor
  · intro hAB
    rw [Set.ssubset_iff_subset_ne] at hAB ⊢
    constructor
    · have hXX : X ⊆ X := Set.Subset.rfl
      have hAXXBXX := Set.diff_subset_diff hAB.1 hXX
      rwa [Set.union_diff_cancel_right, Set.union_diff_cancel_right] at hAXXBXX
      · rwa [Set.disjoint_iff] at hBX
      · rwa [Set.disjoint_iff] at hAX
    · intro
      simp_all
  · intro hAB
    have hAB' : A ⊆ B := hAB.subset
    rw [Set.ssubset_iff_of_subset hAB'] at hAB
    obtain ⟨x, hx⟩ := hAB
    rw [Set.ssubset_iff_of_subset (Set.union_subset_union_left X hAB')]
    refine ⟨x, Set.mem_union_left X hx.1, fun hx' => ?_⟩
    rw [Set.mem_union] at hx'
    cases hx' with
    | inl hA => exact hx.2 hA
    | inr hX => exact Disjoint.ni_of_in hBX hx.1 hX

/-- todo: desc -/
lemma union_subset_union_iff {A B X : Set α} (hAX : Disjoint A X) (hBX : Disjoint B X) :
    A ∪ X ⊆ B ∪ X ↔ A ⊆ B := by
  constructor
  · intro hABX
    have hXX : (A ∪ X) \ X ⊆ (B ∪ X) \ X := Set.diff_subset_diff_left hABX
    have hXA : (A ∪ X) \ X = A := Set.union_diff_cancel_right (Set.disjoint_iff.mp hAX)
    have hXB : (B ∪ X) \ X = B := Set.union_diff_cancel_right (Set.disjoint_iff.mp hBX)
    rwa [hXA, hXB] at hXX
  · exact Set.union_subset_union_left X

lemma ssubset_disjoint_union_nonempty {X₁ X₂ : Set α} (hXX : Disjoint X₁ X₂) (hX₂ : X₂.Nonempty) :
    X₁ ⊂ X₁ ∪ X₂ := by
  rw [Set.ssubset_iff_of_subset Set.subset_union_left]
  obtain ⟨x, hx⟩ := hX₂
  exact ⟨x, Set.mem_union_right X₁ hx, Disjoint.ni_of_in hXX.symm hx⟩

lemma ssubset_disjoint_nonempty_union {X₁ X₂ : Set α} (hXX : Disjoint X₁ X₂) (hX₁ : X₁.Nonempty) :
    X₂ ⊂ X₁ ∪ X₂ := by
  rw [disjoint_comm] at hXX
  rw [Set.union_comm]
  exact ssubset_disjoint_union_nonempty hXX hX₁

end Disjoint


section symmDiff

/-- Symmetric difference of two sets is their union minus their intersection. -/
lemma symmDiff_eq_alt (X Y : Set α) : symmDiff X Y = (X ∪ Y) \ (X ∩ Y) := by
  rw [Set.symmDiff_def, Set.union_diff_distrib,
      Set.diff_inter, Set.diff_self, Set.empty_union,
      Set.diff_inter, Set.diff_self, Set.union_empty]

/-- Symmetric difference of two sets is disjoint with their intersection. -/
lemma symmDiff_disjoint_inter (X Y : Set α) : Disjoint (symmDiff X Y) (X ∩ Y) := by
  rw [symmDiff_eq_alt]
  exact Set.disjoint_sdiff_left

/-- todo: desc -/
lemma symmDiff_empty_eq (X : Set α) : symmDiff X ∅ = X := by
  rw [symmDiff_eq_alt, Set.union_empty, Set.inter_empty, Set.diff_empty]

/-- todo: desc -/
lemma empty_symmDiff_eq (X : Set α) : symmDiff ∅ X = X := by
  rw [symmDiff_eq_alt, Set.empty_union, Set.empty_inter, Set.diff_empty]

/-- todo: desc -/
lemma symmDiff_subset_ground_right {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : X ⊆ E) : Y ⊆ E := by
  rw [symmDiff_eq_alt, Set.diff_subset_iff, Set.union_eq_self_of_subset_left (inter_subset_parent_left hX),
    Set.union_subset_iff] at hE
  exact hE.right

/-- todo: desc -/
lemma symmDiff_subset_ground_left {X Y E : Set α} (hE : symmDiff X Y ⊆ E) (hX : Y ⊆ E) : X ⊆ E :=
  symmDiff_subset_ground_right (symmDiff_comm X Y ▸ hE) hX

end symmDiff
