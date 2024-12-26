import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.SymmDiff
import Mathlib.Tactic


/-!
This provides lemmas about sets (mostly dealing with disjointness) that are missing in Mathlib.
We do not use out custom notation here because this file is higher than `Basic.lean` in the import hierarchy.
-/

section Other

/-- todo: desc -/
lemma setminus_inter_union_eq_union {α : Type*} {X Y : Set α} : X \ (X ∩ Y) ∪ Y = X ∪ Y := by
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
lemma nonempty_inter_not_ssubset_empty_inter {α : Type*} {A B E : Set α}
    (hA : (A ∩ E).Nonempty) (hB : B ∩ E = ∅) : ¬(A ⊂ B) := by
  by_contra hAB
  obtain ⟨hAsubB, _hnBsubA⟩ := hAB
  obtain ⟨x, hxAE⟩  := hA
  have hxBE : x ∈ B ∩ E := (Set.inter_subset_inter hAsubB fun ⦃a⦄ a => a) hxAE
  rw [hB] at hxBE
  tauto

/-- todo: desc -/
lemma ssubset_self_union_other_elem {α : Type*} {a : α} {X : Set α}
    (ha : a ∉ X) : X ⊂ X ∪ {a} := by
  constructor
  · exact Set.subset_union_left
  · by_contra hX
    rw [Set.union_subset_iff] at hX
    obtain ⟨_, haa⟩ := hX
    tauto

/-- todo: desc -/
lemma singleton_union_ssubset_union_iff {α : Type*} {a : α} {A B : Set α}
    (haA : a ∉ A) (haB : a ∉ B) : A ∪ {a} ⊂ B ∪ {a} ↔ A ⊂ B := by
  constructor
  · intro hAB
    obtain ⟨hABl, hABr⟩ := hAB
    constructor
    · intro x hx
      specialize hABl (Set.mem_union_left {a} hx)
      apply ne_of_mem_of_not_mem hx at haA
      cases hABl with
      | inl h => exact h
      | inr h => tauto
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
lemma ssub_parts_ssub {α : Type*} {A B E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) (hB : B ⊆ E₁ ∪ E₂) : (A ∩ E₁ ⊂ B ∩ E₁) ∧ (A ∩ E₂ ⊂ B ∩ E₂) → A ⊂ B := by
  intro hAB
  obtain ⟨hAB₁, hAB₂⟩ := hAB
  constructor
  · obtain ⟨h₁, _⟩ := hAB₁
    obtain ⟨h₂, _⟩ := hAB₂
    apply Set.union_subset_union h₁ at h₂
    rw [←Set.inter_union_distrib_left, ←Set.inter_union_distrib_left] at h₂
    rw [←Set.left_eq_inter.mpr, ←Set.left_eq_inter.mpr] at h₂
    exact h₂
    exact hB
    exact hA
  · by_contra hBA
    obtain ⟨_, h₁⟩ := hAB₁
    obtain ⟨x, ⟨hxBE₁, hxnAE₁⟩⟩ := Set.not_subset.mp h₁
    have hxB : x ∈ B := Set.mem_of_mem_inter_left hxBE₁
    have hxE₁ : x ∈ E₁ := Set.mem_of_mem_inter_right hxBE₁
    have _hxnA : x ∉ A := by tauto
    tauto

/-- todo: desc -/
lemma sub_parts_eq {α : Type*} {A E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) : (A ∩ E₁) ∪ (A ∩ E₂) = A := by
  have t1 : (A ∩ E₁) ∪ (A ∩ E₂) ⊆ A := Set.union_subset Set.inter_subset_left Set.inter_subset_left
  have t2 : A ⊆ (A ∩ E₁) ∪ (A ∩ E₂) := subset_of_subset_of_eq
    (Set.subset_inter (fun ⦃a⦄ a => a) hA)
    (Set.inter_union_distrib_left A E₁ E₂)
  exact Eq.symm (Set.Subset.antisymm t2 t1)

/-- todo: desc -/
lemma elem_notin_set_minus_singleton {α : Type*} (a : α) (X : Set α) : a ∉ X \ {a} := Set.not_mem_diff_of_mem rfl

/-- todo: desc -/
lemma sub_union_diff_sub_union {α : Type*} {A B C : Set α}
    (hA : A ⊆ B \ C) : A ⊆ B := fun ⦃_a⦄ a_1 => Set.diff_subset (hA a_1)

/-- todo: desc -/
lemma singleton_inter_subset_left {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by
  have haXY : a ∈ X ∩ Y := by rw [ha]; rfl
  have haX : a ∈ X := Set.mem_of_mem_inter_left haXY
  exact Set.singleton_subset_iff.mpr haX

/-- todo: desc -/
lemma singleton_inter_subset_right {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by
  have haXY : a ∈ X ∩ Y := by rw [ha]; rfl
  have haY : a ∈ Y := Set.mem_of_mem_inter_right haXY
  exact Set.singleton_subset_iff.mpr haY

/-- Being a subset is preserved under subtracting sets. -/
lemma diff_subset_parent {α : Type*} {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ \ X₂ ⊆ E := by
  rw [Set.diff_subset_iff]
  exact Set.subset_union_of_subset_right hX₁E X₂

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_left {α : Type*} {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ ∩ X₂ ⊆ E :=
  (Set.inter_subset_inter_left X₂ hX₁E).trans Set.inter_subset_left

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_right {α : Type*} {X₁ X₂ E : Set α} (hX₂E : X₂ ⊆ E) :
    X₁ ∩ X₂ ⊆ E := by
  rw [Set.inter_comm]
  exact inter_subset_parent_left hX₂E

/-- Intersection of two sets is subset of their union. -/
lemma inter_subset_union {α : Type*} {X₁ X₂ : Set α} :
    X₁ ∩ X₂ ⊆ X₁ ∪ X₂ := by
  exact inter_subset_parent_left Set.subset_union_left

/-- todo: desc -/
lemma subset_diff_empty_eq {α : Type*} {A B : Set α}
    (hAB : A ⊆ B) (hBdiffA : B \ A = ∅) : A = B :=
  Set.union_empty A ▸ hBdiffA ▸ Set.union_diff_cancel hAB


section Disjoint

/-- todo: desc -/
lemma Disjoint.ni_of_in {α : Type*} {X Y : Set α} {a : α}
    (hXY : Disjoint X Y) (ha : a ∈ X) : a ∉ Y := by
  intro ha'
  simpa [hXY.inter_eq] using Set.mem_inter ha ha'

/-- todo: desc -/
lemma disjoint_of_singleton_inter_left_wo {α : Type*} {X Y : Set α} {a : α}
    (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) Y := by
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
lemma disjoint_of_singleton_inter_right_wo {α : Type*} {X Y : Set α} {a : α}
    (hXY : X ∩ Y = {a}) : Disjoint X (Y \ {a}) := by
  rw [disjoint_comm]
  rw [Set.inter_comm] at hXY
  exact disjoint_of_singleton_inter_left_wo hXY

/-- todo: desc -/
lemma disjoint_of_singleton_inter_both_wo {α : Type*} {X Y : Set α} {a : α}
    (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) (Y \ {a}) :=
  Disjoint.disjoint_sdiff_left (disjoint_of_singleton_inter_right_wo hXY)

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_left {α : Type*} {X Y Z : Set α} {a : α}
    (hXY : X ∩ Y = {a}) (hZ : Z ⊆ X) (haniZ : a ∉ Z) : Disjoint Z Y := by
  have hYeq : (Y \ {a}) ∪ {a} = Y := (Set.diff_union_of_subset (singleton_inter_subset_right hXY))
  rw [←hYeq, Set.disjoint_union_right]
  constructor
  · exact Set.disjoint_of_subset_left hZ (disjoint_of_singleton_inter_right_wo hXY)
  · exact Set.disjoint_singleton_right.mpr haniZ

/-- todo: desc -/
lemma disjoint_of_singleton_inter_subset_right {α : Type*} {X Y Z : Set α} {a : α}
    (hXY : X ∩ Y = {a}) (hZ : Z ⊆ Y) (haniZ : a ∉ Z) : Disjoint X Z := by
  have hXeq : (X \ {a}) ∪ {a} = X := (Set.diff_union_of_subset (singleton_inter_subset_left hXY))
  rw [←hXeq, Set.disjoint_union_left]
  constructor
  · exact Set.disjoint_of_subset_right hZ (disjoint_of_singleton_inter_left_wo hXY)
  · exact Set.disjoint_singleton_left.mpr haniZ

/-- todo: desc -/
lemma disjoint_nonempty_not_subset {α : Type*} {A B : Set α}
    (hAB : Disjoint A B) (hA : A.Nonempty) : ¬(A ⊆ B) := by
  by_contra hAsubB
  apply Disjoint.eq_bot_of_le hAB at hAsubB
  rw [hAsubB] at hA
  unfold Set.Nonempty at hA
  tauto

/-- todo: desc -/
lemma disjoint_nonempty_not_ssubset {α : Type*} {A B : Set α}
    (hAB : Disjoint A B) (hA : A.Nonempty) : ¬(A ⊂ B) := by
  apply disjoint_nonempty_not_subset hAB at hA
  by_contra hAssubB
  obtain ⟨hAsubB, _hnBsubA⟩ := hAssubB
  tauto

/-- todo: desc -/
lemma ssubset_union_disjoint_nonempty {α : Type*} {X Y : Set α}
    (hXY : Disjoint X Y) (hY : Y.Nonempty) : X ⊂ X ∪ Y := by
  constructor
  · exact Set.subset_union_left
  · by_contra h
    apply Set.diff_subset_diff_left at h
    rw [Set.union_diff_cancel_left (Set.disjoint_iff.mp hXY), Set.diff_self] at h
    apply Set.eq_empty_of_subset_empty at h
    exact Set.not_nonempty_empty (h ▸ hY)

/-- todo: desc -/
lemma union_ssubset_union_iff {α : Type*} {A B X : Set α}
    (hAX : Disjoint A X) (hBX : Disjoint B X) : A ∪ X ⊂ B ∪ X ↔ A ⊂ B := by
  constructor
  · intro h
    rw [Set.ssubset_iff_subset_ne] at h ⊢
    constructor
    · have hXsubX : X ⊆ X := Set.Subset.rfl
      have hAsubBpmX := Set.diff_subset_diff h.1 hXsubX
      rw [Set.union_diff_cancel_right, Set.union_diff_cancel_right] at hAsubBpmX
      exact hAsubBpmX
      exact Set.disjoint_iff.mp hBX
      exact Set.disjoint_iff.mp hAX
    · by_contra hAeqB
      rw [hAeqB] at h
      exact h.2 rfl
  · intro h
    have h1 : A ⊆ B := subset_of_ssubset h
    rw [Set.ssubset_iff_of_subset h1] at h
    obtain ⟨x, hx⟩ := h
    rw [Set.ssubset_iff_of_subset (Set.union_subset_union_left X h1)]
    use x
    constructor
    · exact Set.mem_union_left X hx.1
    · intro h
      rw [Set.mem_union] at h
      cases h with
      | inl hA => exact hx.2 hA
      | inr hX => exact (Disjoint.ni_of_in hBX hx.1) hX

/-- todo: desc -/
lemma union_subset_union_iff {α : Type*} {A B X : Set α}
    (hAX : Disjoint A X) (hBX : Disjoint B X) : A ∪ X ⊆ B ∪ X ↔ A ⊆ B := by
  constructor
  · intro hABX
    have t3 : (A ∪ X) \ X ⊆ (B ∪ X) \ X := Set.diff_subset_diff_left hABX
    have t1 : (A ∪ X) \ X = A := Set.union_diff_cancel_right (Set.disjoint_iff.mp hAX)
    have t2 : (B ∪ X) \ X = B := Set.union_diff_cancel_right (Set.disjoint_iff.mp hBX)
    rw [t1, t2] at t3
    exact t3
  · intro hAB
    exact Set.union_subset_union_left X hAB


section symmDiff

/-- Symmetric difference of two sets is their union minus their intersection. -/
lemma symmDiff_def_alt {α : Type*} (X₁ X₂ : Set α) :
    symmDiff X₁ X₂ = (X₁ ∪ X₂) \ (X₁ ∩ X₂) := by
  rw [Set.symmDiff_def, Set.union_diff_distrib,
      Set.diff_inter, Set.diff_self, Set.empty_union,
      Set.diff_inter, Set.diff_self, Set.union_empty]

/-- Symmetric difference of two sets is disjoint with their intersection. -/
lemma symmDiff_disjoint_inter {α : Type*} (X₁ X₂ : Set α) :
    Disjoint (symmDiff X₁ X₂) (X₁ ∩ X₂) := by
  rw [symmDiff_def_alt]
  exact Set.disjoint_sdiff_left

/-- todo: desc -/
lemma symmDiff_empty_eq {α : Type*} (X : Set α) : X = symmDiff X ∅ := by
  rw [symmDiff_def_alt, Set.union_empty, Set.inter_empty, Set.diff_empty]

/-- todo: desc -/
lemma empty_symmDiff_eq {α : Type*} (X : Set α) : X = symmDiff ∅ X := by
  rw [symmDiff_def_alt, Set.empty_union, Set.empty_inter, Set.diff_empty]
