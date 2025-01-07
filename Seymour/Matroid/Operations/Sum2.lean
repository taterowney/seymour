import Mathlib.Data.Set.Card
import Mathlib.Data.Matroid.Dual

import Seymour.ForMathlib.SetTheory
import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Notions.Connectivity

/-!
This file defines 2-sum of two (general) matroids `M₁` and `M₂`, denoted as `M₁ ⊕₂ M₂`.
-/

variable {α : Type}


section MainDefinitions

/-- `M₁ ⊕₂ M₂` is defined if `M₁` and `M₂` satisfy the following assumptions -/
structure Matroid.TwoSum.Assumptions (M₁ M₂ : Matroid α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁fin : M₁.Finite
  hM₂fin : M₂.Finite
  -- question: can avoid this assumption?
  /-- `M₁` and `M₂` contain at least 2 elements -/
  hM₁card : M₁.E.encard ≥ 2
  hM₂card : M₂.E.encard ≥ 2
  /-- `M₁` and `M₂` have exactly one element in common -/
  hInter : (M₁.E ∩ M₂.E).encard = 1
  /-- common element of `M₁` and `M₂` is not a separator in either of them -/
  hM₁sep : ¬M₁.Separator (M₁.E ∩ M₂.E)
  hM₂sep : ¬M₂.Separator (M₁.E ∩ M₂.E)

/-- Ground set of `M₁ ⊕₂ M₂` -/
def Matroid.TwoSum.E (M₁ M₂ : Matroid α) :=
  (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)

/-- Type 1 of circuits in `M₁ ⊕₂ M₂`: circuits of `M₁` that are disjoint with `M₁.E ∩ M₂.E` -/
def Matroid.TwoSum.CircuitType1 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₁.Circuit C ∧ Disjoint C (M₁.E ∩ M₂.E)

/-- Type 2 of circuits in `M₁ ⊕₂ M₂`: circuits of `M₂` that are disjoint with `M₁.E ∩ M₂.E` -/
def Matroid.TwoSum.CircuitType2 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₂.Circuit C ∧ Disjoint C (M₁.E ∩ M₂.E)

/-- Type 3 of circuits in `M₁ ⊕₂ M₂`:
    sets `(C₁ ∪ C₂) \ (M₁.E ∩ M₂.E)` where `C₁` and `C₂` are circuits in `M₁` and M₂`, respectively,
    and `M₁.E ∩ M₂.E ⊆ C₁` and `M₁.E ∩ M₂.E ⊆ C₂` -/
def Matroid.TwoSum.CircuitType3 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₁.Circuit ((C ∩ M₁.E) ∪ (M₁.E ∩ M₂.E)) ∧ M₂.Circuit ((C ∩ M₂.E) ∪ (M₁.E ∩ M₂.E)) ∧ C ⊆ Matroid.TwoSum.E M₁ M₂

/-- Circuit predicate of `M₁ ⊕₂ M₂`, which defines 2-sum as `CircuitMatroid` -/
def Matroid.TwoSum.CircuitPred (M₁ M₂ : Matroid α) : CircuitPredicate α :=
  fun C =>
    Matroid.TwoSum.CircuitType1 M₁ M₂ C ∨
    Matroid.TwoSum.CircuitType2 M₁ M₂ C ∨
    Matroid.TwoSum.CircuitType3 M₁ M₂ C

end MainDefinitions


section PropertiesAssumptions

/-- 2-sum assumptions are symmetric -/
def Matroid.TwoSum.Assumptions.symm {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) :
    Matroid.TwoSum.Assumptions M₂ M₁ :=
  ⟨
    Assumptions.hM₂fin,
    Assumptions.hM₁fin,
    Assumptions.hM₂card,
    Assumptions.hM₁card,
    Set.inter_comm M₁.E M₂.E ▸ Assumptions.hInter,
    Set.inter_comm M₁.E M₂.E ▸ Assumptions.hM₂sep,
    Set.inter_comm M₁.E M₂.E ▸ Assumptions.hM₁sep,
  ⟩

/-- Intersection of ground sets is nonempty -/
lemma Matroid.TwoSum.Assumptions.inter_nonempty {M₁ M₂ : Matroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) : (M₁.E ∩ M₂.E).Nonempty :=
  Set.one_le_encard_iff_nonempty.mp (le_of_eq Assumptions.hInter.symm)

/-- Intersection of ground sets is a singleton set -/
lemma Matroid.TwoSum.Assumptions.inter_singleton {M₁ M₂ : Matroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) : ∃ p, M₁.E ∩ M₂.E = {p} :=
  Set.encard_eq_one.mp Assumptions.hInter

/-- Singleton element in intersection of ground sets in a member of `M₁.E` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_mem_M₁ {M₁ M₂ : Matroid α} {p : α}
    (hp : M₁.E ∩ M₂.E = {p}) : p ∈ M₁.E :=
  Set.mem_of_mem_inter_left (hp.symm.subset rfl)

/-- Singleton element in intersection of ground sets in a member of `M₂.E` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_mem_M₂ {M₁ M₂ : Matroid α} {p : α}
    (hp : M₁.E ∩ M₂.E = {p}) : p ∈ M₂.E :=
  Set.mem_of_mem_inter_right (hp.symm.subset rfl)

/-- Singleton element in intersection of ground sets in not a loop in `M₁` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_not_loop_M₁ {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) : ¬M₁.Loop p :=
  fun h => (hp ▸ Assumptions.hM₁sep) (Matroid.separator_loop h)

/-- Singleton element in intersection of ground sets in not a coloop in `M₁` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_not_coloop_M₁ {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) : ¬M₁.Coloop p :=
  fun h => (hp ▸ Assumptions.hM₁sep) (Matroid.separator_coloop h)

/-- Singleton element in intersection of ground sets in not a loop in `M₂` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_not_loop_M₂ {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) : ¬M₂.Loop p :=
  fun h => (hp ▸ Assumptions.hM₂sep) (Matroid.separator_loop h)

/-- Singleton element in intersection of ground sets in not a coloop in `M₂` -/
lemma Matroid.TwoSum.Assumptions.inter_singleton_not_coloop_M₂ {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) : ¬M₂.Coloop p :=
  fun h => (hp ▸ Assumptions.hM₂sep) (Matroid.separator_coloop h)

end PropertiesAssumptions


section PropertiesGroundSet

/-- Ground set of 2-sum is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.E.disjoint_inter (M₁ M₂ : Matroid α) :
    Disjoint (Matroid.TwoSum.E M₁ M₂) (M₁.E ∩ M₂.E) :=
  Set.disjoint_sdiff_left

/-- Ground sets minus their intersection are disjoint sets -/
lemma Matroid.TwoSum.disjoint_grounds_diff_inter (M₁ M₂ : Matroid α) :
    Disjoint (M₁.E \ (M₁.E ∩ M₂.E)) (M₂.E \ (M₁.E ∩ M₂.E)) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff

end PropertiesGroundSet


section PropertiesCircuitType1

/-- Circuit of type 1 is a circuit in `M₁` -/
lemma Matroid.TwoSum.CircuitType1.circuit_M₁ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : M₁.Circuit C := hC.1

/-- Circuit of type 1 is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.CircuitType1.disjoint_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : Disjoint C (M₁.E ∩ M₂.E) := hC.2

/-- Circuit of type 1 lies in `M₁.E ∪ M₂.E` -/
lemma Matroid.TwoSum.CircuitType1.subset_union {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_left hC.circuit_M₁.subset_ground M₂.E

/-- Circuit of type 1 lies in ground set of `M₁ ⊕₂ M₂` -/
lemma Matroid.TwoSum.CircuitType1.subset_ground {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : C ⊆ Matroid.TwoSum.E M₁ M₂ :=
  Set.subset_diff.mpr ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of type 1 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma Matroid.TwoSum.CircuitType1.subset_M₁_diff_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : C ⊆ M₁.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.mpr ⟨hC.circuit_M₁.subset_ground, hC.disjoint_inter⟩

/-- Circuit of type 1 is disjoint with `M₂.E` -/
lemma Matroid.TwoSum.CircuitType1.disjoint_M₂ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType1 M₁ M₂ C) : Disjoint C M₂.E := by
  have hMM := Matroid.TwoSum.disjoint_grounds_diff_inter M₁ M₂
  have hCM₂ := Set.disjoint_of_subset_left hC.subset_M₁_diff_inter hMM
  have hCM₂ := Set.disjoint_union_right.mpr ⟨hCM₂, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_right] at hCM₂
  exact hCM₂

end PropertiesCircuitType1


section PropertiesCircuitType2

/-- Circuit of type 2 is a circuit in `M₂` -/
lemma Matroid.TwoSum.CircuitType2.circuit_M₂ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : M₂.Circuit C := hC.1

/-- Circuit of type 2 is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.CircuitType2.disjoint_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : Disjoint C (M₁.E ∩ M₂.E) := hC.2

/-- Circuit of type 2 lies in `M₁.E ∪ M₂.E` -/
lemma Matroid.TwoSum.CircuitType2.subset_union {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_right hC.circuit_M₂.subset_ground M₁.E

/-- Circuit of type 2 lies in ground set of `M₁ ⊕₂ M₂` -/
lemma Matroid.TwoSum.CircuitType2.subset_ground {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : C ⊆ Matroid.TwoSum.E M₁ M₂ :=
  Set.subset_diff.mpr ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of type 2 lies in `M₂.E \ (M₁.E ∩ M₂.E)` -/
lemma Matroid.TwoSum.CircuitType2.subset_M₂_diff_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : C ⊆ M₂.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.mpr ⟨hC.circuit_M₂.subset_ground, hC.disjoint_inter⟩

/-- Circuit of type 2 is disjoint with `M₁.E` -/
lemma Matroid.TwoSum.CircuitType2.disjoint_M₁ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType2 M₁ M₂ C) : Disjoint C M₁.E := by
  have hMM := Matroid.TwoSum.disjoint_grounds_diff_inter M₁ M₂
  have hCM₁ := (Set.disjoint_of_subset_right hC.subset_M₂_diff_inter hMM).symm
  have hCM₁ := Set.disjoint_union_right.mpr ⟨hCM₁, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_left] at hCM₁
  exact hCM₁

end PropertiesCircuitType2


section PropertiesCircuitType3

/-- Circuit of type 3 yields a circuit in `M₁` after intersecting it with `M₁.E` and adding `M₁.E ∩ M₂.E` -/
def Matroid.TwoSum.CircuitType3.to_circuit_M₁ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : M₁.Circuit ((C ∩ M₁.E) ∪ (M₁.E ∩ M₂.E)) := hC.1

/-- Circuit of type 3 yields a circuit in `M₂` after intersecting it with `M₁.E` and adding `M₁.E ∩ M₂.E` -/
def Matroid.TwoSum.CircuitType3.to_circuit_M₂ {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : M₂.Circuit ((C ∩ M₂.E) ∪ (M₁.E ∩ M₂.E)) := hC.2.1

/-- Circuit of type 3 is subset of ground set of `M₁ ⊕₂ M₂` -/
def Matroid.TwoSum.CircuitType3.subset_ground {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : C ⊆ Matroid.TwoSum.E M₁ M₂ := hC.2.2

/-- Circuit of type 3 lies in `M₁.E ∪ M₂.E` -/
lemma Matroid.TwoSum.CircuitType3.subset_union {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  sub_union_diff_sub_union hC.subset_ground

/-- Circuit of type 3 is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.CircuitType3.disjoint_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : Disjoint C (M₁.E ∩ M₂.E) :=
  Set.disjoint_of_subset_left hC.subset_ground (Matroid.TwoSum.E.disjoint_inter M₁ M₂)

/-- Circuit of type 3 intersected with `M₁.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.CircuitType3.disjoint_inter_M₁_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : Disjoint (C ∩ M₁.E) (M₁.E ∩ M₂.E) :=
  hC.disjoint_inter.inter_left M₁.E

/-- Circuit of type 3 intersected with `M₂.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma Matroid.TwoSum.CircuitType3.disjoint_inter_M₂_inter {M₁ M₂ : Matroid α} {C : Set α}
    (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : Disjoint (C ∩ M₂.E) (M₁.E ∩ M₂.E) :=
  hC.disjoint_inter.inter_left M₂.E

/-- Circuit of type 3 has nonempty intersection with `M₁.E` -/
lemma Matroid.TwoSum.CircuitType3.inter_M₁_nonempty {M₁ M₂ : Matroid α} {C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : (C ∩ M₁.E).Nonempty := by
  by_contra hCM₁empty
  push_neg at hCM₁empty
  have hCM₁ := hC.to_circuit_M₁
  have ⟨p, hp⟩ := Assumptions.inter_singleton
  rw [hCM₁empty, Set.empty_union, hp, ←Matroid.Loop.iff_circuit M₁] at hCM₁
  have hpM₁ := Assumptions.inter_singleton_not_loop_M₁ hp
  exact hpM₁ hCM₁

/-- Circuit of type 3 has nonempty intersection with `M₂.E` -/
lemma Matroid.TwoSum.CircuitType3.inter_M₂_nonempty {M₁ M₂ : Matroid α} {C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) (hC : Matroid.TwoSum.CircuitType3 M₁ M₂ C) : (C ∩ M₂.E).Nonempty := by
  by_contra hCM₂empty
  push_neg at hCM₂empty
  have hCM₂ := hC.to_circuit_M₂
  have ⟨p, hp⟩ := Assumptions.inter_singleton
  rw [hCM₂empty, Set.empty_union, hp, ←Matroid.Loop.iff_circuit M₂] at hCM₂
  have hpM₂ := Assumptions.inter_singleton_not_loop_M₂ hp
  exact hpM₂ hCM₂

end PropertiesCircuitType3


section PropertiesCircuitTypePairs1

/-- Circuit of type 1 is not a strict subset of any circuit of type 1 -/
lemma Matroid.TwoSum.CircuitType1.not_ssubset_circuit_type_1 {M₁ M₂ : Matroid α} {C₁ C₁' : Set α}
    (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) (hC₁' : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁') :
    ¬C₁ ⊂ C₁' :=
  hC₁.circuit_M₁.not_ssubset_circuit hC₁'.circuit_M₁

/-- Circuit of type 1 is disjoint with any circuit of type 2 -/
lemma Matroid.TwoSum.CircuitType1.disjoint_circuit_type_2 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) :
    Disjoint C₁ C₂ := by
  have hC₁M₁ := hC₁.subset_M₁_diff_inter
  have hC₂M₂ := hC₂.subset_M₂_diff_inter
  have hMM := Matroid.TwoSum.disjoint_grounds_diff_inter M₁ M₂
  exact Set.disjoint_of_subset hC₁M₁ hC₂M₂ hMM

/-- Circuit of type 1 is not a strict subset of any circuit of type 2 -/
lemma Matroid.TwoSum.CircuitType1.not_ssubset_circuit_type_2 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) :
    ¬C₁ ⊂ C₂ :=
  disjoint_nonempty_not_ssubset (hC₁.disjoint_circuit_type_2 hC₂) hC₁.circuit_M₁.nonempty

/-- Circuit of type 1 is not a strict subset of any circuit of type 3 -/
lemma Matroid.TwoSum.CircuitType1.not_ssubset_circuit_type_3 {M₁ M₂ : Matroid α} {C₁ C₃ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) :
    ¬C₁ ⊂ C₃ := by
  by_contra hC₁C₃
  have hC₁C₃ := Set.subset_inter hC₁C₃.1 hC₁.circuit_M₁.subset_ground
  apply Set.union_subset_union_left (M₁.E ∩ M₂.E) at hC₁C₃
  have hC₁ssubunioninter := ssubset_union_disjoint_nonempty hC₁.disjoint_inter Assumptions.inter_nonempty
  apply Set.ssubset_of_ssubset_of_subset hC₁ssubunioninter at hC₁C₃
  exact hC₁.circuit_M₁.not_ssubset_circuit hC₃.to_circuit_M₁ hC₁C₃

/-- Circuit of type 1 is not a strict subset of any other circuit -/
lemma Matroid.TwoSum.CircuitType1.not_ssubset_circuit {M₁ M₂ : Matroid α} {C₁ C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) (hC : Matroid.TwoSum.CircuitPred M₁ M₂ C) :
    ¬C₁ ⊂ C := by
  cases hC with
  | inl hC => exact hC₁.not_ssubset_circuit_type_1 hC
  | inr hC => cases hC with
    | inl hC => exact hC₁.not_ssubset_circuit_type_2 hC
    | inr hC => exact hC₁.not_ssubset_circuit_type_3 Assumptions hC

end PropertiesCircuitTypePairs1


section PropertiesCircuitTypePairs2

/-- Circuits of type 2 are disjoint with circuits of type 1 -/
lemma Matroid.TwoSum.CircuitType2.disjoint_circuit_type_1 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) :
    Disjoint C₂ C₁ :=
  (hC₁.disjoint_circuit_type_2 hC₂).symm

/-- Circuit of type 2 is not a strict subset of any circuit of type 1 -/
lemma Matroid.TwoSum.CircuitType2.not_ssubset_circuit_type_1 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) :
    ¬C₂ ⊂ C₁ :=
  disjoint_nonempty_not_ssubset (hC₂.disjoint_circuit_type_1 hC₁) hC₂.circuit_M₂.nonempty

/-- Circuit of type 2 is not a strict subset of any circuit of type 2 -/
lemma Matroid.TwoSum.CircuitType2.not_ssubset_circuit_type_2 {M₁ M₂ : Matroid α} {C₂ C₂' : Set α}
    (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) (hC₂' : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂') :
    ¬C₂ ⊂ C₂' :=
  hC₂.circuit_M₂.not_ssubset_circuit hC₂'.circuit_M₂

/-- Circuit of type 2 is not a strict subset of any circuit of type 3 -/
lemma Matroid.TwoSum.CircuitType2.not_ssubset_circuit_type_3 {M₁ M₂ : Matroid α} {C₂ C₃ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) :
    ¬C₂ ⊂ C₃ := by
  by_contra hC₂C₃
  have hC₂C₃ := Set.subset_inter hC₂C₃.1 hC₂.circuit_M₂.subset_ground
  apply Set.union_subset_union_left (M₁.E ∩ M₂.E) at hC₂C₃
  have hC₂ssubunioninter := ssubset_union_disjoint_nonempty hC₂.disjoint_inter Assumptions.inter_nonempty
  apply Set.ssubset_of_ssubset_of_subset hC₂ssubunioninter at hC₂C₃
  exact hC₂.circuit_M₂.not_ssubset_circuit hC₃.to_circuit_M₂ hC₂C₃

/-- Circuit of type 2 is not a strict subset of any other circuit -/
lemma Matroid.TwoSum.CircuitType2.not_ssubset_circuit {M₁ M₂ : Matroid α} {C₂ C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) (hC : Matroid.TwoSum.CircuitPred M₁ M₂ C) :
    ¬C₂ ⊂ C := by
  cases hC with
  | inl hC => exact hC₂.not_ssubset_circuit_type_1 hC
  | inr hC => cases hC with
    | inl hC => exact hC₂.not_ssubset_circuit_type_2 hC
    | inr hC => exact hC₂.not_ssubset_circuit_type_3 Assumptions hC

end PropertiesCircuitTypePairs2


section PropertiesCircuitTypePairs3

/-- Circuit of type 3 is not a strict subset of any circuit of type 1 -/
lemma Matroid.TwoSum.CircuitType3.not_ssubset_circuit_type_1 {M₁ M₂ : Matroid α} {C₁ C₃ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) (hC₁ : Matroid.TwoSum.CircuitType1 M₁ M₂ C₁) :
    ¬C₃ ⊂ C₁ :=
  nonempty_inter_not_ssubset_empty_inter (hC₃.inter_M₂_nonempty Assumptions) hC₁.disjoint_M₂.inter_eq

/-- Circuit of type 3 is not a strict subset of any circuit of type 2 -/
lemma Matroid.TwoSum.CircuitType3.not_ssubset_circuit_type_2 {M₁ M₂ : Matroid α} {C₂ C₃ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) (hC₂ : Matroid.TwoSum.CircuitType2 M₁ M₂ C₂) :
    ¬C₃ ⊂ C₂ :=
  nonempty_inter_not_ssubset_empty_inter (hC₃.inter_M₁_nonempty Assumptions) hC₂.disjoint_M₁.inter_eq

/-- Circuit of type 3 is not a strict subset of any circuit of type 3 -/
lemma Matroid.TwoSum.CircuitType3.not_ssubset_circuit_type_3 {M₁ M₂ : Matroid α} {C₃ C₃' : Set α}
    (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) (hC₃' : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃') :
    ¬C₃ ⊂ C₃' := by
  intro ⟨hC₃C₃', hnC₃'C₃⟩

  have hM₁circ_sub := Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.inter_subset_inter_left M₁.E hC₃C₃')
  have hM₁circ_nssub := Set.ssubset_def ▸ hC₃.to_circuit_M₁.not_ssubset_circuit hC₃'.to_circuit_M₁
  push_neg at hM₁circ_nssub
  have hDisjM₁ := hC₃.disjoint_inter_M₁_inter
  have hDisjM₁' := hC₃'.disjoint_inter_M₁_inter
  have hM₁circ'_sub := (union_subset_union_iff hDisjM₁' hDisjM₁).mp (hM₁circ_nssub hM₁circ_sub)

  have hM₂circ_sub := Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.inter_subset_inter_left M₂.E hC₃C₃')
  have hM₂circ_nssub := Set.ssubset_def ▸ hC₃.to_circuit_M₂.not_ssubset_circuit hC₃'.to_circuit_M₂
  push_neg at hM₂circ_nssub
  have hDisjM₂ := hC₃.disjoint_inter_M₂_inter
  have hDisjM₂' := hC₃'.disjoint_inter_M₂_inter
  have hM₂circ'_sub := (union_subset_union_iff hDisjM₂' hDisjM₂).mp (hM₂circ_nssub hM₂circ_sub)

  have hC₃'C₃ := Set.union_subset_union hM₁circ'_sub hM₂circ'_sub
  rw [sub_parts_eq hC₃.subset_union, sub_parts_eq hC₃'.subset_union] at hC₃'C₃
  exact hnC₃'C₃ hC₃'C₃

/-- Circuit of type 3 is not a strict subset of any other circuit -/
lemma Matroid.TwoSum.CircuitType3.not_ssubset_circuit {M₁ M₂ : Matroid α} {C₃ C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂)
    (hC₃ : Matroid.TwoSum.CircuitType3 M₁ M₂ C₃) (hC : Matroid.TwoSum.CircuitPred M₁ M₂ C) :
    ¬C₃ ⊂ C := by
  cases hC with
  | inl hC => exact hC₃.not_ssubset_circuit_type_1 Assumptions hC
  | inr hC => cases hC with
    | inl hC => exact hC₃.not_ssubset_circuit_type_2 Assumptions hC
    | inr hC => exact hC₃.not_ssubset_circuit_type_3 hC

end PropertiesCircuitTypePairs3


section PropertiesCircuitPred

/-- In definition of 2-sum, empty set is not a circuit -/
lemma Matroid.TwoSum.CircuitPred.not_circuit_empty {M₁ M₂ : Matroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) : (Matroid.TwoSum.CircuitPred M₁ M₂).not_circuit_empty := by
  unfold CircuitPredicate.not_circuit_empty Matroid.TwoSum.CircuitPred
  push_neg
  constructor
  · intro h
    exact h.circuit_M₁.nonempty.ne_empty rfl
  · constructor
    · intro h
      exact h.circuit_M₂.nonempty.ne_empty rfl
    · intro ⟨hpM₁, hpM₂, hE⟩
      have ⟨p, hp⟩ := Assumptions.inter_singleton
      rw [Set.empty_inter, Set.empty_union, hp, ←Loop.iff_circuit M₁] at hpM₁
      exact (hp ▸ Assumptions.hM₁sep) (Matroid.separator_loop hpM₁)

/-- In definition of 2-sum, no circuit is a strict subset of another -/
lemma Matroid.TwoSum.CircuitPred.circuit_not_ssubset {M₁ M₂ : Matroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) : (Matroid.TwoSum.CircuitPred M₁ M₂).circuit_not_ssubset := by
  intro C₁ C₂ hC₁ hC₂
  cases hC₂ with
  | inl hC₂ => exact hC₂.not_ssubset_circuit Assumptions hC₁
  | inr hC₂ => cases hC₂ with
    | inl hC₂ => exact hC₂.not_ssubset_circuit Assumptions hC₁
    | inr hC₂ => exact hC₂.not_ssubset_circuit Assumptions hC₁

-- todo: remaining circuit axioms

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitPred.subset_ground (M₁ M₂ : Matroid α) :
    (Matroid.TwoSum.CircuitPred M₁ M₂).subset_ground (Matroid.TwoSum.E M₁ M₂) := by
  intro C hC
  cases hC with
  | inl hC => exact hC.subset_ground
  | inr hC => cases hC with
    | inl hC => exact hC.subset_ground
    | inr hC => exact hC.subset_ground

end PropertiesCircuitPred


section TwoSumDefinition

/-- `CircuitMatroid` defining `M₁ ⊕₂ M₂` -/
def Matroid.TwoSum.CircuitMatroid {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) :
    CircuitMatroid α where
  E := Matroid.TwoSum.E M₁ M₂
  CircuitPred := Matroid.TwoSum.CircuitPred M₁ M₂
  not_circuit_empty := CircuitPred.not_circuit_empty Assumptions
  circuit_not_ssubset := CircuitPred.circuit_not_ssubset Assumptions
  circuit_c3 := sorry -- todo: should simplify in finite case
  circuit_maximal := sorry -- todo: should simplify in finite case
  subset_ground := CircuitPred.subset_ground M₁ M₂

/-- todo: desc -/
def Matroid.TwoSum.matroid {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) : Matroid α :=
  (Matroid.TwoSum.CircuitMatroid Assumptions).matroid

@[simp]
lemma Matroid.TwoSum.E_eq {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) :
    (Matroid.TwoSum.matroid Assumptions).E = (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) := rfl

@[simp]
lemma Matroid.TwoSum.CircuitPred_iff {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) :
  (Matroid.TwoSum.CircuitMatroid Assumptions).CircuitPred = Matroid.TwoSum.CircuitPred M₁ M₂ := rfl

@[simp]
lemma Matroid.TwoSum.circuit_iff {M₁ M₂ : Matroid α} (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) {C : Set α} :
    (Matroid.TwoSum.matroid Assumptions).Circuit C ↔ C ⊆ Matroid.TwoSum.E M₁ M₂ ∧ Matroid.TwoSum.CircuitPred M₁ M₂ C := by
  unfold matroid
  rw [CircuitMatroid.circuit_iff]
  rfl

end TwoSumDefinition

-- todo: properties of 2-sum: Proposition 7.1.21, 22, 23, etc. from Oxley
