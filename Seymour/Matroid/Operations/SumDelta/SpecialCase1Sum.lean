import Mathlib.Data.Matroid.Sum

import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.Matroid.Operations.SumDelta.CircuitForms


variable {α : Type}


section CircuitFormsProperties

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.disjoint_circuit_pred {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) (hMM : Disjoint M₁.E M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, _, X₁, X₂, hCXX, hX₁udc, hX₂udc⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hMM).inter_eq, Set.diff_empty] at hCXX

    have hC'M₁ : C' ⊆ M₁.E := hCC'.trans hC.subset_ground
    have hC'M₂ := Set.disjoint_of_subset_left hC'M₁ hMM
    have hX₂C' : X₂ ⊆ C' := Set.subset_union_right.trans hCXX.symm.subset
    have hX₂empty : X₂ = ∅ := Set.subset_eq_empty (hC'M₂ hX₂C' hX₂udc.subset_ground) rfl
    rw [hX₂empty, Set.union_empty] at hCXX

    rw [hCXX] at hCC' hC'nempty ⊢

    have hX₁dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₁.matroid X₁) hX₁udc hC'nempty
    exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₁ hX₁dep hCC'

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.disjoint_circuit_pred {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) (hMM : Disjoint M₁.E M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, _, X₁, X₂, hCXX, hX₁udc, hX₂udc⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hMM).inter_eq, Set.diff_empty] at hCXX

    have hC'M₂ : C' ⊆ M₂.E := hCC'.trans hC.subset_ground
    have hC'M₁ := Set.disjoint_of_subset_right hC'M₂ hMM
    have hX₁C' : X₁ ⊆ C' := Set.subset_union_left.trans hCXX.symm.subset
    have hX₁empty : X₁ = ∅ := Set.subset_eq_empty (hC'M₁.symm hX₁C' hX₁udc.subset_ground) rfl
    rw [hX₁empty, Set.empty_union] at hCXX

    rw [hCXX] at hCC' hC'nempty ⊢

    have hX₂dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid X₂) hX₂udc hC'nempty
    exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₂ hX₂dep hCC'

end CircuitFormsProperties


section disjointSumProperties

/-- Dependent set in disjoint sum is depenent in one of summand matroids -/
lemma Matroid.disjointSum_dep_iff {M N : Matroid α} {h : M.E ⫗ N.E} {D : Set α} :
    (M.disjointSum N h).Dep D ↔ (M.Dep (D ∩ M.E) ∨ N.Dep (D ∩ N.E)) ∧ D ⊆ M.E ∪ N.E := by
  constructor
  · intro hD
    constructor
    · have hDE := Matroid.disjointSum_ground_eq ▸ hD.subset_ground
      apply Matroid.Dep.not_indep at hD
      rw [Matroid.disjointSum_indep_iff] at hD
      push_neg at hD
      if hDM : M.Indep (D ∩ M.E) then
        if hDN : N.Indep (D ∩ N.E) then
          exact False.elim (hD hDM hDN hDE)
        else
          exact Or.inr ⟨hDN, Set.inter_subset_right⟩
      else
        exact Or.inl ⟨hDM, Set.inter_subset_right⟩
    · exact Matroid.disjointSum_ground_eq ▸ hD.subset_ground
  · intro ⟨hD, hDE⟩
    cases hD with
    | inl hDM => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDM) (Matroid.disjointSum_indep_iff.mp hD).1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩
    | inr hDN => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDN) (Matroid.disjointSum_indep_iff.mp hD).2.1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩

/-- Circuit in disjoint sum is circuit in one of summand matroids -/
lemma Matroid.disjointSum_circuit_iff (M N : Matroid α) (h : Disjoint M.E N.E) {C : Set α} :
    (M.disjointSum N h).Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨hCdep, hCmin⟩
    have ⟨hC, hCE⟩ := Matroid.disjointSum_dep_iff.mp hCdep
    cases hC with
    | inl hCM =>
        have hCMMeq : C ∩ M.E ∩ M.E = C ∩ M.E := Set.inter_eq_left.mpr Set.inter_subset_right
        have hCinterM : (M.disjointSum N h).Dep (C ∩ M.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inl (hCMMeq.symm ▸ hCM),
          inter_subset_parent_left hCE
        ⟩
        have hCMeq : C = C ∩ M.E := Set.Subset.antisymm (hCmin hCinterM Set.inter_subset_left) Set.inter_subset_left

        left
        constructor
        · exact hCMeq ▸ hCM
        · intro D hD hDC
          have hDM : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDM : D = D ∩ M.E := Set.Subset.antisymm hDM Set.inter_subset_left
          have hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inl (hDM ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
    | inr hCN =>
        have hCNNeq : C ∩ N.E ∩ N.E = C ∩ N.E := Set.inter_eq_left.mpr Set.inter_subset_right
        have hCinterN : (M.disjointSum N h).Dep (C ∩ N.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inr (hCNNeq.symm ▸ hCN),
          inter_subset_parent_left hCE
        ⟩
        have hCMeq : C = C ∩ N.E := Set.Subset.antisymm (hCmin hCinterN Set.inter_subset_left) Set.inter_subset_left

        right
        constructor
        · exact hCMeq ▸ hCN
        · intro D hD hDC
          have hDN : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDN : D = D ∩ N.E := Set.Subset.antisymm hDN Set.inter_subset_left
          have hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inr (hDN ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
  · intro hC
    cases hC with
    | inl hCM =>
        have hCMeq : C = C ∩ M.E := Set.left_eq_inter.mpr hCM.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inl (hCMeq ▸ hCM.dep), (hCM.subset_ground).trans Set.subset_union_left⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          have ⟨hD, hDE⟩ := hD
          have hDMeq : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDMeq : D = D ∩ M.E := Set.Subset.antisymm hDMeq Set.inter_subset_left
          have hDNeq : D ∩ N.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDMeq.symm) h)
          rw [←hDMeq, hDNeq] at hD
          cases hD with
          | inl hD => exact hCM.2 hD hDC
          | inr hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
    | inr hCN =>
        have hCNeq : C = C ∩ N.E := Set.left_eq_inter.mpr hCN.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inr (hCNeq ▸ hCN.dep), (hCN.subset_ground).trans Set.subset_union_right⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          have ⟨hD, hDE⟩ := hD
          have hDNeq : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCNeq.symm))
          have hDNeq : D = D ∩ N.E := Set.Subset.antisymm hDNeq Set.inter_subset_left
          have hDMeq : D ∩ M.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDNeq.symm) h.symm)
          rw [←hDNeq, hDMeq] at hD
          cases hD with
          | inl hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
          | inr hD => exact hCN.2 hD hDC

end disjointSumProperties


section Equivalence

/-- If two sets are disjoint, then any set is disjoint with their intersection -/
lemma disjoint_inter_disjoint {A B : Set α} (C : Set α) (h : Disjoint A B) : Disjoint C (A ∩ B) := by
  rw [h.inter_eq]
  exact Set.disjoint_empty C
-- TODO move?

/-- If `M₁.E ∩ M₂.E = ∅`, then `M₁ Δ M₂ = M₁ ⊕ M₂` -/
lemma BinaryMatroid.DeltaSum.SpecialCase1Sum [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hMM : Disjoint M₁.E M₂.E) : Matroid.disjointSum M₁.matroid M₂.matroid hMM = BinaryMatroid.DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_eq_all_circuits]
  constructor
  · rw [Matroid.disjointSum_ground_eq,
        VectorMatroid.E_eq, VectorMatroid.E_eq,
        BinaryMatroid.DeltaSum.E_eq, hMM.inter_eq, Set.diff_empty]
  · intro C hCE
    rw [Matroid.disjointSum_ground_eq, VectorMatroid.E_eq, VectorMatroid.E_eq] at hCE
    rw [Matroid.disjointSum_circuit_iff, BinaryMatroid.DeltaSum.circuit_iff]
    constructor
    · intro hCcirc
      cases hCcirc with
      | inl hCM₁ =>
          have hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C := ⟨hCM₁, disjoint_inter_disjoint C hMM⟩
          exact hC.disjoint_circuit_pred hMM
      | inr hCM₂ =>
          have hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C := ⟨hCM₂, disjoint_inter_disjoint C hMM⟩
          exact hC.disjoint_circuit_pred hMM
    · intro hC
      have ⟨⟨hCnempty, hCE, X₁, X₂, hCX₁X₂, hX₁udc, hX₂udc⟩, hCmin⟩ := hC
      if hX₂empty : X₂ = ∅ then
          left
          rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCX₁X₂
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ hC (hCX₁X₂ ▸ hX₁udc)
      else
        if hX₁empty : X₁ = ∅ then
          right
          rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCX₁X₂
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ hC (hCX₁X₂ ▸ hX₂udc)
        else
          apply Set.nonempty_iff_ne_empty.mpr at hX₁empty
          apply Set.nonempty_iff_ne_empty.mpr at hX₂empty

          have hX₁E : X₁ ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ := by
            rw [BinaryMatroid.DeltaSum.E, hMM.inter_eq, Set.diff_empty]
            exact Set.subset_union_of_subset_left hX₁udc.subset_ground M₂.E

          have hX₁X₂ := Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hMM
          rw [hX₁X₂.inter_eq, Set.diff_empty] at hCX₁X₂

          specialize hCmin (BinaryMatroid.DeltaSum.CircuitForm_left hX₁empty hX₁E hX₁udc)
          specialize hCmin (hCX₁X₂.symm ▸ Set.subset_union_left)
          apply Set.ssubset_of_ssubset_of_subset (hCX₁X₂ ▸ ssubset_disjoint_union_nonempty hX₁X₂ hX₂empty) at hCmin
          exact False.elim ((HasSSubset.SSubset.ne hCmin) rfl)

end Equivalence
