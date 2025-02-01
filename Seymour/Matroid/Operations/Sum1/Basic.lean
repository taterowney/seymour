import Seymour.Basic
import Seymour.ForMathlib.SetTheory
import Mathlib.Data.Matroid.Sum
import Seymour.Matroid.Notions.Circuit


variable {α : Type}

/-- The main way of creating a 1-sum of any matroids. -/
abbrev Disjoint.build1sum {M₁ M₂ : Matroid α} (hE : M₁.E ⫗ M₂.E) : Matroid α :=
  Matroid.disjointSum M₁ M₂ hE

/-- The 1-sum is commutative. -/
lemma Disjoint.build1sum_comm {M₁ M₂ : Matroid α} (hE : M₁.E ⫗ M₂.E) : hE.symm.build1sum = hE.build1sum :=
  Matroid.disjointSum_comm

lemma Disjoint.build1sum_dep_iff {M N : Matroid α} (hE : M.E ⫗ N.E) {D : Set α} :
    hE.build1sum.Dep D ↔ (M.Dep (D ∩ M.E) ∨ N.Dep (D ∩ N.E)) ∧ D ⊆ M.E ∪ N.E := by
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

lemma Matroid.build1sum_circuit_iff (M N : Matroid α) (hE : M.E ⫗ N.E) {C : Set α} :
    hE.build1sum.Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨dep_C, min_C⟩
    have ⟨hC, hCE⟩ := hE.build1sum_dep_iff.→ dep_C
    cases hC with
    | inl hCM =>
      have hCMM : C ∩ M.E ∩ M.E = C ∩ M.E := Set.inter_eq_left.← Set.inter_subset_right
      have C_inter_ME_dep : hE.build1sum.Dep (C ∩ M.E) := hE.build1sum_dep_iff.← ⟨Or.inl (hCMM.symm ▸ hCM),
        inter_subset_parent_left hCE⟩
      have hCM' : C = C ∩ M.E := Set.Subset.antisymm (min_C C_inter_ME_dep Set.inter_subset_left) Set.inter_subset_left
      left
      constructor
      · exact hCM' ▸ hCM
      · intro D hD hDC
        have hDM : D = D ∩ M.E :=
          (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCM'.symm))).antisymm Set.inter_subset_left
        have dep_D : hE.build1sum.Dep D := hE.build1sum_dep_iff.← ⟨Or.inl (hDM ▸ hD), hDC.trans hCE⟩
        exact min_C dep_D hDC
    | inr hCN =>
      have C_inter_N_dep : hE.build1sum.Dep (C ∩ N.E) :=
        hE.build1sum_dep_iff.← ⟨Or.inr ((Set.inter_eq_left.← Set.inter_subset_right).symm ▸ hCN),
          inter_subset_parent_left hCE⟩
      have hCN' : C = C ∩ N.E := Set.Subset.antisymm (min_C C_inter_N_dep Set.inter_subset_left) Set.inter_subset_left
      right
      constructor
      · exact hCN' ▸ hCN
      · intro D hD hDC
        have hDN : D = D ∩ N.E :=
          (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCN'.symm))).antisymm Set.inter_subset_left
        have dep_D : hE.build1sum.Dep D := hE.build1sum_dep_iff.← ⟨Or.inr (hDN ▸ hD), hDC.trans hCE⟩
        exact min_C dep_D hDC
  · intro hC
    cases hC with
    | inl hCM =>
      have hCM' : C = C ∩ M.E := Set.left_eq_inter.← hCM.subset_ground
      constructor
      · rw [hE.build1sum_dep_iff]
        exact ⟨Or.inl (hCM' ▸ hCM.dep), (hCM.subset_ground).trans Set.subset_union_left⟩
      · intro D hD hDC
        rw [hE.build1sum_dep_iff] at hD
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
      · rw [hE.build1sum_dep_iff]
        exact ⟨Or.inr (hCN' ▸ hCN.dep), (hCN.subset_ground).trans Set.subset_union_right⟩
      · intro D hD hDC
        rw [hE.build1sum_dep_iff] at hD
        replace ⟨hD, _⟩ := hD
        have D_eq : D = D ∩ N.E :=
          (Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.→ hCN'.symm))).antisymm Set.inter_subset_left
        rw [←D_eq, (Set.disjoint_of_subset_left (Set.inter_eq_left.→ D_eq.symm) hE.symm).inter_eq] at hD
        cases hD with
        | inl hD => exact (hD.nonempty.ne_empty rfl).elim
        | inr hD => exact hCN.right hD hDC
