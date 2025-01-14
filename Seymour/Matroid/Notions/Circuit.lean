import Mathlib.Data.Matroid.Basic
import Seymour.Basic


variable {α : Type}

/-- Circuit is minimal dependent subset. -/
def Matroid.Circuit (M : Matroid α) (C : Set α) : Prop :=
  Minimal M.Dep C

/-- Every circuit is dependent. -/
lemma Matroid.Circuit.dep (M : Matroid α) {C : Set α} (hC : M.Circuit C) : M.Dep C :=
  hC.left

/-- Every circuit is a subset of the ground set. -/
lemma Matroid.Circuit.subset_ground (M : Matroid α) {C : Set α} (hC : M.Circuit C) : C ⊆ M.E :=
  hC.left.right

/-- Equivalence with explicit definition of circuits. -/
lemma Matroid.circuit_iff_def (M : Matroid α) (C : Set α) :
    M.Circuit C ↔ M.Dep C ∧ ∀ C' : Set α, M.Dep C' → C' ⊆ C → C ⊆ C' :=
  rfl.to_iff

/-- Every strict subset of a circuit is independent. -/
lemma Matroid.Circuit.indep_ssub {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    M.Indep C' := by
  by_contra notIndep_M_C'
  have C'_sub_C : C' ⊆ C := subset_of_ssubset hC'
  have C_sub_ME : C ⊆ M.E := hC.subset_ground
  have C'_sub_ME : C' ⊆ M.E := hC'.subset.trans C_sub_ME
  exact hC'.ne.symm ((hC.right (M.dep_of_not_indep notIndep_M_C' C'_sub_ME) C'_sub_C).antisymm C'_sub_C)

/-- Deleting one element from a circuit produces an independent set. -/
lemma Matroid.Circuit.indep_diff_singleton {M : Matroid α} {C : Set α} {a : α} (hC : M.Circuit C) (ha : a ∈ C) :
    M.Indep (C \ {a}) :=
  Matroid.Circuit.indep_ssub hC (Set.diff_singleton_sSubset.mpr ha)

/-- Empty set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_empty (M : Matroid α) : ¬(M.Circuit ∅) :=
  (·.left.left M.empty_indep)

/-- Every circuit is nonempty. -/
lemma Matroid.Circuit.nonempty {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra! C_empty
  rw [C_empty] at hC
  exact hC.not_circuit_empty

/-- Independent set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_indep {M : Matroid α} {I : Set α} (hI : M.Indep I) : ¬(M.Circuit I) :=
  (·.left.left hI)

/-- No circuit is a subset of another circuit -/
lemma Matroid.Circuit.not_ssubset_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : M.Circuit C') :
    ¬(C ⊂ C') :=
  fun hCC => hCC.right (hC'.right hC.left hCC.le)

/-- Strict subset of a circuit is not a circuit. -/
lemma Matroid.Circuit.ssubset_not_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    ¬(M.Circuit C') :=
  (Matroid.Circuit.not_ssubset_circuit · hC hC')

/-- A set is dependent iff it contains a circuit. -/
lemma Matroid.Circuit.dep_iff_has_circuit {M : Matroid α} {D : Set α} :
    M.Dep D ↔ ∃ C, M.Circuit C ∧ C ⊆ D := by
  constructor
  · sorry
  · sorry

/-- todo: desc -/
lemma Matroid.Circuit.indep_ext_dep_has_circuit_w_ext {M : Matroid α} {I : Set α} {a : α}
    (hI : M.Indep I) (hIa : M.Dep (a ᕃ I)) :
    ∃ C, M.Circuit C ∧ C ⊆ a ᕃ I ∧ a ∈ C := by
  obtain ⟨C, hC, hCIa⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hIa
  exact ⟨C, hC, hCIa, by
    by_contra haC
    exact hC.left.left (hI.subset ((Set.disjoint_singleton_right.mpr haC).subset_right_of_subset_union hCIa))
  ⟩

/-- If two matroids have the same ground sets and sets of circuits, then they are equal. -/
theorem Matroid.ext_circuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (hC : ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C) :
    M₁ = M₂ := by
  -- TODO bump Mathlib
  sorry

/-- Two matroids are equal iff they have the same ground sets and sets of circuits. -/
theorem Matroid.ext_iff_circuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C :=
  ⟨by aesop, fun hM => Matroid.ext_circuit hM.left hM.right⟩
