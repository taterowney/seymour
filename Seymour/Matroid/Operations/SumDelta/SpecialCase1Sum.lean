import Mathlib.Data.Matroid.Sum

import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.Matroid.Operations.SumDelta.CircuitForms


variable {α : Type} [DecidableEq α]


section CircuitFormsProperties

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.disjoint_circuit_pred {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) (hMM : M₁.E ⫗ M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁.subset_ground hX₂.subset_ground hMM).inter_eq, Set.diff_empty] at hXX
    have X₂_empty : X₂ = ∅ := Set.subset_eq_empty
      (Set.disjoint_of_subset_left (hCC'.trans hC.subset_ground) hMM (Set.subset_union_right.trans hXX.symm.subset)
        hX₂.subset_ground) rfl
    rw [X₂_empty, Set.union_empty] at hXX
    rw [hXX] at hCC' C'_nonempty ⊢
    exact hC.right (hX₁.nonempty_dep C'_nonempty) hCC'

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.disjoint_circuit_pred {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) (hMM : M₁.E ⫗ M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁.subset_ground hX₂.subset_ground hMM).inter_eq, Set.diff_empty] at hXX
    have X₁_empty : X₁ = ∅ := Set.subset_eq_empty
      ((Set.disjoint_of_subset_right (hCC'.trans hC.subset_ground) hMM).symm (Set.subset_union_left.trans hXX.symm.subset)
        hX₁.subset_ground) rfl
    rw [X₁_empty, Set.empty_union] at hXX
    rw [hXX] at hCC' C'_nonempty ⊢
    exact hC.right (hX₂.nonempty_dep C'_nonempty) hCC'

end CircuitFormsProperties


section disjointSumProperties

/-- Dependent set in disjoint sum is depenent in one of summand matroids -/
lemma Matroid.disjointSum_dep_iff {M N : Matroid α} {hE : M.E ⫗ N.E} {D : Set α} :
    (M.disjointSum N hE).Dep D ↔ (M.Dep (D ∩ M.E) ∨ N.Dep (D ∩ N.E)) ∧ D ⊆ M.E ∪ N.E := by
  constructor
  · intro hD
    constructor
    · have hDE := Matroid.disjointSum_ground_eq ▸ hD.subset_ground
      have hD' := hD.not_indep
      rw [Matroid.disjointSum_indep_iff] at hD'
      push_neg at hD'
      if hDM : M.Indep (D ∩ M.E) then
      if hDN : N.Indep (D ∩ N.E) then
      exact (hD' hDM hDN hDE).elim
      else exact Or.inr ⟨hDN, Set.inter_subset_right⟩
      else exact Or.inl ⟨hDM, Set.inter_subset_right⟩
    · exact Matroid.disjointSum_ground_eq ▸ hD.subset_ground
  · intro ⟨hD, hDE⟩
    cases hD with
    | inl hDM => exact ⟨
        fun hD => (hDM.not_indep (Matroid.disjointSum_indep_iff.→ hD).left).elim,
        Matroid.disjointSum_ground_eq ▸ hDE⟩
    | inr hDN => exact ⟨
        fun hD => (hDN.not_indep (Matroid.disjointSum_indep_iff.→ hD).right.left).elim,
        Matroid.disjointSum_ground_eq ▸ hDE⟩

/-- Circuit in disjoint sum is circuit in one of summand matroids -/
lemma Matroid.disjointSum_circuit_iff (M N : Matroid α) (hE : M.E ⫗ N.E) {C : Set α} :
    (M.disjointSum N hE).Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨dep_C, min_C⟩
    have ⟨hC, hCE⟩ := Matroid.disjointSum_dep_iff.→ dep_C
    cases hC with
    | inl hCM =>
      have hCMM : C ∩ M.E ∩ M.E = C ∩ M.E := Set.inter_eq_left.← Set.inter_subset_right
      have C_inter_ME_dep : (M.disjointSum N hE).Dep (C ∩ M.E) := Matroid.disjointSum_dep_iff.← ⟨Or.inl (hCMM.symm ▸ hCM),
        inter_subset_parent_left hCE⟩
      have hCM' : C = C ∩ M.E := Set.Subset.antisymm (min_C C_inter_ME_dep Set.inter_subset_left) Set.inter_subset_left
      left
      constructor
      · exact hCM' ▸ hCM
      · intro D hD hDC
        have hDM : D = D ∩ M.E :=
          (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCM'.symm))).antisymm Set.inter_subset_left
        have dep_D : (M.disjointSum N hE).Dep D := Matroid.disjointSum_dep_iff.← ⟨Or.inl (hDM ▸ hD), hDC.trans hCE⟩
        exact min_C dep_D hDC
    | inr hCN =>
      have C_inter_N_dep : (M.disjointSum N hE).Dep (C ∩ N.E) :=
        Matroid.disjointSum_dep_iff.← ⟨Or.inr ((Set.inter_eq_left.← Set.inter_subset_right).symm ▸ hCN),
          inter_subset_parent_left hCE⟩
      have hCN' : C = C ∩ N.E := Set.Subset.antisymm (min_C C_inter_N_dep Set.inter_subset_left) Set.inter_subset_left
      right
      constructor
      · exact hCN' ▸ hCN
      · intro D hD hDC
        have hDN : D = D ∩ N.E :=
          (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCN'.symm))).antisymm Set.inter_subset_left
        have dep_D : (M.disjointSum N hE).Dep D := Matroid.disjointSum_dep_iff.← ⟨Or.inr (hDN ▸ hD), hDC.trans hCE⟩
        exact min_C dep_D hDC
  · intro hC
    cases hC with
    | inl hCM =>
        have hCM' : C = C ∩ M.E := Set.left_eq_inter.← hCM.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inl (hCM' ▸ hCM.dep), (hCM.subset_ground).trans Set.subset_union_left⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          replace ⟨hD, _⟩ := hD
          have D_eq : D = D ∩ M.E :=
            (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCM'.symm))).antisymm Set.inter_subset_left
          rw [←D_eq, (Set.disjoint_of_subset_left (Set.inter_eq_left.→ D_eq.symm) hE).inter_eq] at hD
          cases hD with
          | inl hD => exact hCM.right hD hDC
          | inr hD => exact (hD.nonempty.ne_empty rfl).elim
    | inr hCN =>
        have hCN' : C = C ∩ N.E := Set.left_eq_inter.← hCN.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inr (hCN' ▸ hCN.dep), (hCN.subset_ground).trans Set.subset_union_right⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          replace ⟨hD, _⟩ := hD
          have D_eq : D = D ∩ N.E :=
            (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCN'.symm))).antisymm Set.inter_subset_left
          rw [←D_eq, (Set.disjoint_of_subset_left (Set.inter_eq_left.→ D_eq.symm) hE.symm).inter_eq] at hD
          cases hD with
          | inl hD => exact (hD.nonempty.ne_empty rfl).elim
          | inr hD => exact hCN.right hD hDC

end disjointSumProperties


section Equivalence

/-- If `M₁.E ∩ M₂.E = ∅`, then `M₁ Δ M₂ = M₁ ⊕ M₂` -/
lemma BinaryMatroid.DeltaSum.SpecialCase1Sum {M₁ M₂ : BinaryMatroid α}
    (hE : M₁.E ⫗ M₂.E) : Matroid.disjointSum M₁.toMatroid M₂.toMatroid hE = BinaryMatroid.DeltaSum.toMatroid M₁ M₂ := by
  apply Matroid.ext_circuit
  · rewrite [Matroid.disjointSum_ground_eq, VectorMatroid.toMatroid_E, VectorMatroid.toMatroid_E,
      BinaryMatroid.DeltaSum.E_eq, hE.inter_eq, Set.diff_empty]
    rfl
  · intro C hCE
    rw [Matroid.disjointSum_ground_eq, VectorMatroid.toMatroid_E, VectorMatroid.toMatroid_E] at hCE
    rw [Matroid.disjointSum_circuit_iff, BinaryMatroid.DeltaSum.circuit_iff]
    constructor
    · intro hC
      cases hC with
      | inl hCM₁ =>
        have hC₁ : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C := ⟨hCM₁, disjoint_inter_disjoint C hE⟩
        exact hC₁.disjoint_circuit_pred hE
      | inr hCM₂ =>
        have hC₂ : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C := ⟨hCM₂, disjoint_inter_disjoint C hE⟩
        exact hC₂.disjoint_circuit_pred hE
    · intro hC
      have ⟨⟨hCnempty, hCE, X₁, X₂, hXX, hX₁, hX₂⟩, min_C⟩ := hC
      if X₂_empty : X₂ = ∅ then
          left
          rw [X₂_empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hXX
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ hC (hXX ▸ hX₁)
      else
        if X₁_empty : X₁ = ∅ then
          right
          rw [X₁_empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hXX
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ hC (hXX ▸ hX₂)
        else
          apply Set.nonempty_iff_ne_empty.← at X₁_empty
          apply Set.nonempty_iff_ne_empty.← at X₂_empty
          have X₁_subset_E : X₁ ⊆ BinaryMatroid.DeltaSum.E M₁ M₂
          · rw [BinaryMatroid.DeltaSum.E, hE.inter_eq, Set.diff_empty]
            exact Set.subset_union_of_subset_left hX₁.subset_ground M₂.E
          have hXX' := Set.disjoint_of_subset hX₁.subset_ground hX₂.subset_ground hE
          rw [hXX'.inter_eq, Set.diff_empty] at hXX
          specialize min_C (BinaryMatroid.DeltaSum.CircuitForm_left X₁_empty X₁_subset_E hX₁) (hXX.symm ▸ Set.subset_union_left)
          exact ((Set.ssubset_of_ssubset_of_subset (hXX ▸ ssubset_disjoint_union_nonempty hXX' X₂_empty) min_C).ne rfl).elim

end Equivalence
