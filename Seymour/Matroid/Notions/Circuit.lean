import Mathlib.Data.Matroid.Basic


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
lemma Matroid.Circuit.circuit_iff_def {M : Matroid α} {C : Set α} :
    M.Circuit C ↔ M.Dep C ∧ ∀ C', M.Dep C' → C' ⊆ C → C ⊆ C' :=
  rfl.to_iff

/-- Every strict subset of a circuit is independent. -/
lemma Matroid.Circuit.indep_ssub {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    M.Indep C' := by
  by_contra h
  have hC'subC : C' ⊆ C := subset_of_ssubset hC'
  have hCsubE : C ⊆ M.E := hC.subset_ground
  have hC'subE : C' ⊆ M.E := hC'subC.trans hCsubE
  have hCmin_dep := (Matroid.Circuit.circuit_iff_def.mpr hC).2
  specialize hCmin_dep (Matroid.dep_of_not_indep h hC'subE) hC'subC
  exact (ne_of_lt hC').symm (Set.Subset.antisymm hCmin_dep hC'subC)

/-- Deleting one element from a circuit produces an independent set. -/
lemma Matroid.Circuit.indep_diff_singleton {M : Matroid α} {C : Set α} {a : α}
    (hC : M.Circuit C) (ha : a ∈ C) : M.Indep (C \ {a}) :=
  Matroid.Circuit.indep_ssub hC (Set.diff_singleton_sSubset.mpr ha)

/-- Empty set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_empty (M : Matroid α) : ¬M.Circuit ∅ :=
  fun h => h.1.1 M.empty_indep

/-- Every circuit is nonempty. -/
lemma Matroid.Circuit.nonempty {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra hC'
  push_neg at hC'
  rw [hC'] at hC
  apply Matroid.Circuit.not_circuit_empty at hC
  exact hC

/-- Independent set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_indep {M : Matroid α} {I : Set α} (hI : M.Indep I) : ¬M.Circuit I :=
  fun h => h.1.1 hI

/-- No circuit is a subset of another circuit -/
lemma Matroid.Circuit.not_ssubset_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : M.Circuit C') :
    ¬C ⊂ C' :=
  fun h => h.2 (hC'.2 hC.1 (le_of_lt h))

/-- Strict subset of a circuit is not a circuit. -/
lemma Matroid.Circuit.ssubset_not_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    ¬M.Circuit C' := by
  intro h
  exact Matroid.Circuit.not_ssubset_circuit h hC hC'

/-- A set is dependent iff it contains a circuit. -/
lemma Matroid.Circuit.dep_iff_has_circuit {M : Matroid α} {D : Set α} :
    M.Dep D ↔ ∃ C, M.Circuit C ∧ C ⊆ D := by
  constructor
  · sorry
  · sorry

/-- todo: desc -/
lemma Matroid.Circuit.indep_ext_dep_has_circuit_w_ext {M : Matroid α} {I : Set α} {a : α}
    (hI : M.Indep I) (hIa : M.Dep (insert a I)) :
    ∃ C, M.Circuit C ∧ C ⊆ insert a I ∧ a ∈ C := by
  obtain ⟨C, hC, hCIa⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hIa
  use C
  exact ⟨
    hC,
    hCIa,
    by
      by_contra h
      exact hC.1.1 (Indep.subset hI (Disjoint.subset_right_of_subset_union hCIa (Set.disjoint_singleton_right.mpr h)))
  ⟩

/-- If two matroids have the same ground sets and sets of circuits, then they are equal. -/
theorem Matroid.eq_if_eq_all_circuits {M₁ M₂ : Matroid α}
    (hE : M₁.E = M₂.E) (h : ∀ C ⊆ M₁.E, (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  sorry

/-- Two matroids are equal iff they have the same ground sets and sets of circuits. -/
theorem Matroid.eq_iff_eq_all_circuits {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ C ⊆ M₁.E, (M₁.Circuit C ↔ M₂.Circuit C) :=
  ⟨fun h ↦ by (subst h; simp), fun h ↦ Matroid.eq_if_eq_all_circuits h.1 h.2⟩
