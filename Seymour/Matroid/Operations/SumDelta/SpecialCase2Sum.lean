import Seymour.Matroid.Operations.Sum2
import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.Matroid.Operations.SumDelta.CircuitForms


variable {α : Type} {M₁ M₂ : BinaryMatroid α}


section CircuitFormsProperties

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.sum2_circuit_pred {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) (hMM : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, _, X₁, X₂, hCXX, hX₁udc, hX₂udc⟩ := hC'

    cases hX₂udc.dep_or_empty with
    | inl hX₂dep =>
      have hX₂eq : X₂ = M₁.E ∩ M₂.E := by
        have hSDsubM₁ := (symmDiff_eq_alt X₁ X₂ ▸ hCXX) ▸ (hCC'.trans hC.subset_ground)
        have hX₂M₁ := M₁.toMatroid_E ▸ symmDiff_subset_ground_right hSDsubM₁ hX₁udc.subset_ground
        have hX₂sub_inter := Set.subset_inter hX₂M₁ hX₂dep.subset_ground
        have hInterFinite := Set.finite_of_encard_eq_coe hMM.interSingleton
        have hEncardInterLeX₂ := le_of_eq_of_le hMM.interSingleton (Set.one_le_encard_iff_nonempty.mpr hX₂dep.nonempty)
        exact Set.Finite.eq_of_subset_of_encard_le hInterFinite hX₂sub_inter hEncardInterLeX₂
      have ⟨p, hp⟩ := hMM.inter_singleton
      have hX₂loop : M₂.toMatroid.Loop p := ⟨singleton_inter_in_right hp, hp ▸ hX₂eq ▸ hX₂dep⟩
      exfalso
      exact hMM.inter_singleton_not_loop_M₂ hp hX₂loop
    | inr hX₂empty =>
      rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCXX
      rw [hCXX] at hCC' hC'nempty ⊢
      have hX₁dep := hX₁udc.nonempty_dep hC'nempty
      exact (Matroid.Circuit.circuit_iff_def.mp hC).right X₁ hX₁dep hCC'

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.sum2_circuit_pred {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) (hMM : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, _, X₁, X₂, hCXX, hX₁udc, hX₂udc⟩ := hC'

    cases hX₁udc.dep_or_empty with
    | inl hX₁dep =>
      have hX₁eq : X₁ = M₁.E ∩ M₂.E := by
        have hSDsubM₂ := (symmDiff_eq_alt X₁ X₂ ▸ hCXX) ▸ hCC'.trans hC.subset_ground
        have hX₁M₂ := M₂.toMatroid_E ▸ symmDiff_subset_ground_left hSDsubM₂ hX₂udc.subset_ground
        have hX₁sub_inter := Set.subset_inter hX₁dep.subset_ground hX₁M₂
        have hInterFinite := Set.finite_of_encard_eq_coe hMM.interSingleton
        have hEncardInterLeX₁ := le_of_eq_of_le hMM.interSingleton (Set.one_le_encard_iff_nonempty.mpr hX₁dep.nonempty)
        exact Set.Finite.eq_of_subset_of_encard_le hInterFinite hX₁sub_inter hEncardInterLeX₁
      obtain ⟨p, hp⟩ := hMM.inter_singleton
      have hX₁loop : M₁.toMatroid.Loop p := ⟨singleton_inter_in_left hp, hp ▸ hX₁eq ▸ hX₁dep⟩
      exfalso
      exact hMM.inter_singleton_not_loop_M₁ hp hX₁loop
    | inr hX₁empty =>
      rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCXX
      rw [hCXX] at hCC' hC'nempty ⊢
      have hX₂dep := hX₂udc.nonempty_dep hC'nempty
      exact (Matroid.Circuit.circuit_iff_def.mp hC).right X₂ hX₂dep hCC'

/-- Under 2-sum assumptions, `{p}` in definition of circuits of form 3 is exactly `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.sum2_singleton_eq {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hMM : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    M₁.E ∩ M₂.E = {p} := by
  have hInterCard := M₁.toMatroid_E ▸ M₂.toMatroid_E ▸ hMM.interSingleton
  have hInterFinite := Set.finite_of_encard_eq_coe hInterCard
  have hInterCardLeSingleton := ((Set.encard_singleton p).symm ▸ hInterCard).le
  exact (Set.Finite.eq_of_subset_of_encard_le hInterFinite hC.singleton_subset_inter hInterCardLeSingleton).symm

/-- Circuit of form 3 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.sum2_circuit_pred {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hMM : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  have hp := hC.sum2_singleton_eq hMM
  have hCnempty := (hMM.inter_singleton_not_loop_M₁ hp)
  rw [Matroid.Loop.iff_circuit M₁.toMatroid] at hCnempty
  apply hC.inter_M₁_nonempty at hCnempty
  apply Set.Nonempty.left at hCnempty

  constructor
  · exact hC.circuit_form hCnempty
  · intro D hD hDC
    have ⟨hDnempty, hDE, X₁, X₂, ⟨hDX₁X₂, hX₁udc, hX₂udc⟩⟩ := hD
    have ⟨hCM₁p, hCM₂p, hCE⟩ := hC

    have hX₁X₂ := Set.inter_subset_inter hX₁udc.subset_ground hX₂udc.subset_ground
    rw [M₁.toMatroid_E, M₂.toMatroid_E, hp] at hX₁X₂

    have hX₁C₁ : X₁ ⊆ C ∩ M₁.E ∪ {p} := by
      rw [(Set.diff_union_inter X₁ X₂).symm]
      rw [←symmDiff_eq_alt, symmDiff_def] at hDX₁X₂
      simp only [Set.sup_eq_union] at hDX₁X₂
      have hX₁mX₂C := (hDX₁X₂ ▸ Set.subset_union_left).trans hDC
      have hX₁mX₂M₁ := Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₁udc.subset_ground X₂)
      have hX₁mX₂CiM₁ := Set.subset_inter hX₁mX₂C hX₁mX₂M₁
      exact Set.union_subset_union hX₁mX₂CiM₁ hX₁X₂

    have hX₂C₂ : X₂ ⊆ C ∩ M₂.E ∪ {p} := by
      rw [(Set.diff_union_inter X₂ X₁).symm]
      rw [←symmDiff_eq_alt, symmDiff_def] at hDX₁X₂
      simp only [Set.sup_eq_union] at hDX₁X₂
      have hX₂mX₁C := (hDX₁X₂ ▸ Set.subset_union_right).trans hDC
      have hX₂mX₁M₂ := Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₂udc.subset_ground X₁)
      have hX₁mX₂CiM₁ := Set.subset_inter hX₂mX₁C hX₂mX₁M₂
      exact Set.union_subset_union hX₁mX₂CiM₁ (Set.inter_comm X₁ X₂ ▸ hX₁X₂)

    cases hX₁udc.dep_or_empty with
    | inl hX₁dep =>
      have hX₁C₁ := (Matroid.Circuit.circuit_iff_def.mp hCM₁p).right X₁ hX₁dep hX₁C₁
      cases hX₂udc.dep_or_empty with
      | inl hX₂dep =>
        have hX₂C₂ := (Matroid.Circuit.circuit_iff_def.mp hCM₂p).right X₂ hX₂dep hX₂C₂
        have hX₁X₂p : X₁ ∩ X₂ = {p} := by
          apply Set.Subset.antisymm hX₁X₂
          exact Set.subset_inter (Set.union_subset_iff.mp hX₁C₁).right (Set.union_subset_iff.mp hX₂C₂).right
        have hCD := Set.union_subset_union hX₁C₁ hX₂C₂
        have hCD : (C ∩ M₁.E ∪ {p} ∪ (C ∩ M₂.E ∪ {p})) \ {p} ⊆ (X₁ ∪ X₂) \ {p} := Set.diff_subset_diff_left hCD
        rw [Set.union_diff_distrib, Set.union_diff_right, Set.union_diff_right,
            Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₁_inter),
            Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₂_inter),
            sub_parts_eq hC.subset_union, ←hX₁X₂p, ←hDX₁X₂] at hCD
        exact hCD
      | inr hX₂empty =>
        rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hDX₁X₂
        rw [hDX₁X₂] at hDnempty
        have hpX₁ := hDX₁X₂ ▸ (Set.union_subset_iff.mp hX₁C₁).right
        have hZ₁p := hp ▸ Set.disjoint_of_subset_left hDE (BinaryMatroid.DeltaSum.E.disjoint_inter M₁ M₂)
        exact False.elim (hZ₁p hpX₁ Set.Subset.rfl rfl)
    | inr hX₁empty =>
      rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hDX₁X₂
      have hX₂dep := hX₂udc.nonempty_dep (hDX₁X₂ ▸ hDnempty)
      have hX₂C₂ := (Matroid.Circuit.circuit_iff_def.mp hCM₂p).right X₂ hX₂dep hX₂C₂
      have hpX₂ := hDX₁X₂ ▸ (Set.union_subset_iff.mp hX₂C₂).right
      have hZ₁p := hp ▸ Set.disjoint_of_subset_left hDE (BinaryMatroid.DeltaSum.E.disjoint_inter M₁ M₂)
      exact False.elim (hZ₁p hpX₂ Set.Subset.rfl rfl)

end CircuitFormsProperties


section Equivalence

/-- If `M₁` and `M₂` satisfy the 2-sum assumptions, then `M₁ Δ M₂ = M₁ ⊕₂ M₂` -/
lemma BinaryMatroid.DeltaSum.SpecialCase2Sum
    (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    assumptions.build2sum = BinaryMatroid.DeltaSum.matroid M₁ M₂ := by
  apply Matroid.ext_circuit (by rfl)
  intro C hCE
  rw [assumptions.build2sum_circuit, BinaryMatroid.DeltaSum.circuit_iff]
  unfold twoSumGround
  rw [assumptions.build2sum_E] at hCE
  rw [VectorMatroid.toMatroid_E, VectorMatroid.toMatroid_E] at hCE ⊢
  constructor
  · intro ⟨_hCE, hC⟩
    unfold TwoSumCircuitPred at hC
    cases hC with
    | inl hC => exact CircuitForm1.sum2_circuit_pred hC assumptions
    | inr hC => cases hC with
      | inl hC => exact CircuitForm2.sum2_circuit_pred hC assumptions
      | inr hC =>
          obtain ⟨p, hp⟩ := assumptions.inter_singleton
          have hCcf3 : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p := ⟨
            M₁.toMatroid_E ▸ hp ▸ hC.to_circuit_M₁,
            M₂.toMatroid_E ▸ hp ▸ hC.to_circuit_M₂,
            hCE⟩
          exact hCcf3.sum2_circuit_pred assumptions
  · intro hC
    constructor
    · exact hCE
    · have ⟨⟨hCnempty, _, X₁, X₂, hCX₁X₂, hX₁udc, hX₂udc⟩, hCmin⟩ := hC
      if hX₂empty : X₂ = ∅ then
        left
        rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCX₁X₂
        exact ⟨BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ hC (hCX₁X₂ ▸ hX₁udc), (Set.subset_diff.mp hCE).right⟩
      else
        right
        if hX₁empty : X₁ = ∅ then
          left
          rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCX₁X₂
          exact ⟨BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ hC (hCX₁X₂ ▸ hX₂udc), (Set.subset_diff.mp hCE).right⟩
        else
          right
          apply Set.nonempty_iff_ne_empty.mpr at hX₁empty
          apply Set.nonempty_iff_ne_empty.mpr at hX₂empty
          have hX₁dep := hX₁udc.nonempty_dep hX₁empty
          have hX₂dep := hX₂udc.nonempty_dep hX₂empty

          obtain ⟨p, hp⟩ := M₁.toMatroid_E ▸ M₂.toMatroid_E ▸ assumptions.inter_singleton
          have hX₁X₂p := hp ▸ Set.inter_subset_inter hX₁udc.subset_ground hX₂udc.subset_ground

          have hpX₁ : {p} ⊆ X₁ := by
            -- todo: clean up
            by_contra hnpX₁
            rw [Set.singleton_subset_iff] at hnpX₁
            have hX₁p : X₁ ⫗ {p} := Set.disjoint_singleton_right.mpr hnpX₁
            have hpInter : p ∉ X₁ ∩ X₂ := fun h => hnpX₁ (Set.mem_of_mem_inter_left h)
            have hpInter2 : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl hpInter).symm
            have hX₁X₂ : X₁ ∩ X₂ = ∅ := by
              by_contra h
              cases Set.subset_singleton_iff_eq.mp hX₁X₂p with
              | inl t => exact h t
              | inr t => exact hpInter2 t
            have hX₁inter : X₁ ⫗ M₁.E ∩ M₂.E := hp ▸ hX₁p
            have hX₁C : X₁ ⊆ C := (Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂) ▸ Set.subset_union_left
            have ⟨Y₁, hY₁, hY₁X₁⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hX₁dep
            have hY₁inter := Set.disjoint_of_subset_left hY₁X₁ hX₁inter
            have hY₁cf1 : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ Y₁ := ⟨hY₁, hY₁inter⟩
            specialize hCmin hY₁cf1.circuit_form (hY₁X₁.trans hX₁C)
            have hCeq : C = X₁ := Set.Subset.antisymm (hCmin.trans hY₁X₁) hX₁C
            have hCeq2 := Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂
            have hX₁X₂ : X₁ ⫗ X₂ := Set.disjoint_iff_inter_eq_empty.mpr hX₁X₂
            rw [hCeq] at hCeq2
            have hX₂ := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.mp hCeq2.symm)).mp hX₁X₂.symm
            exact Set.not_nonempty_empty (hX₂ ▸ hX₂empty)

          have hpX₂ : {p} ⊆ X₂ := by
            -- todo: clean up
            by_contra hnpX₂
            rw [Set.singleton_subset_iff] at hnpX₂
            have hX₂p : X₂ ⫗ {p} := Set.disjoint_singleton_right.mpr hnpX₂
            have hpInter : p ∉ X₁ ∩ X₂ := fun h => hnpX₂ (Set.mem_of_mem_inter_right h)
            have hpInter2 : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl hpInter).symm
            have hX₁X₂ : X₁ ∩ X₂ = ∅ := by
              by_contra h
              cases Set.subset_singleton_iff_eq.mp hX₁X₂p with
              | inl t => exact h t
              | inr t => exact hpInter2 t
            have hX₂inter : X₂ ⫗ M₁.E ∩ M₂.E := hp ▸ hX₂p
            have hX₂C : X₂ ⊆ C := (Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂) ▸ Set.subset_union_right
            have ⟨Y₂, hY₂, hY₂X₂⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hX₂dep
            have hY₂inter := Set.disjoint_of_subset_left hY₂X₂ hX₂inter
            have hY₂cf1 : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ Y₂ := ⟨hY₂, hY₂inter⟩
            specialize hCmin hY₂cf1.circuit_form (hY₂X₂.trans hX₂C)
            have hCeq : C = X₂ := Set.Subset.antisymm (hCmin.trans hY₂X₂) hX₂C
            have hCeq2 := Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂
            rw [hCeq, Set.union_comm] at hCeq2
            have hX₁X₂ : X₁ ⫗ X₂ := Set.disjoint_iff_inter_eq_empty.mpr hX₁X₂
            have hX₁ := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.mp hCeq2.symm)).mp hX₁X₂
            exact Set.not_nonempty_empty (hX₁ ▸ hX₁empty)

          have hpX₁X₂ : X₁ ∩ X₂ = {p} := Set.Subset.antisymm hX₁X₂p (Set.subset_inter hpX₁ hpX₂)

          have hX₁C₁ : X₁ ⊆ C ∩ M₁.E ∪ {p} := by
            -- todo: neat, but unused
            rw [(Set.diff_union_inter X₁ X₂).symm]
            rw [←symmDiff_eq_alt, symmDiff_def] at hCX₁X₂
            simp only [Set.sup_eq_union] at hCX₁X₂
            have hX₁mX₂C := hCX₁X₂ ▸ Set.subset_union_left
            have hX₁mX₂M₁ := M₁.toMatroid_E ▸ Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₁udc.subset_ground X₂)
            have hX₁mX₂CiM₁ := Set.subset_inter hX₁mX₂C hX₁mX₂M₁
            exact Set.union_subset_union hX₁mX₂CiM₁ hX₁X₂p

          have hX₂C₂ : X₂ ⊆ C ∩ M₂.E ∪ {p} := by
            -- todo: neat, but unused
            rw [(Set.diff_union_inter X₂ X₁).symm]
            rw [←symmDiff_eq_alt, symmDiff_def] at hCX₁X₂
            simp only [Set.sup_eq_union] at hCX₁X₂
            have hX₂mX₁C := hCX₁X₂ ▸ Set.subset_union_right
            have hX₂mX₁M₂ := M₂.toMatroid_E ▸ Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₂udc.subset_ground X₁)
            have hX₁mX₂CiM₁ := Set.subset_inter hX₂mX₁C hX₂mX₁M₂
            exact Set.union_subset_union hX₁mX₂CiM₁ (Set.inter_comm X₁ X₂ ▸ hX₁X₂p)

          have hC₁eqX₁ : C ∩ M₁.E ∪ {p} = X₁ := by
            -- todo: clean up
            rw [hpX₁X₂] at hCX₁X₂
            have t1 : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congrFun (congrArg Union.union hCX₁X₂) {p}
            rw [Set.diff_union_self] at t1
            have t2 : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
            rw [Set.union_eq_left.mpr t2] at t1

            have a2 : (C ∪ {p}) ∩ M₁.E = (X₁ ∪ X₂) ∩ M₁.E := congrFun (congrArg Inter.inter t1) M₁.E
            have a3 : (X₁ ∪ X₂) ∩ M₁.E = X₁ ∩ M₁.E ∪ X₂ ∩ M₁.E := Set.union_inter_distrib_right X₁ X₂ M₁.E
            have a4 : X₁ ∩ M₁.E = X₁ := (Set.left_eq_inter.mpr hX₁udc.subset_ground).symm
            have a5 : X₂ ∩ M₁.E ⊆ M₂.E ∩ M₁.E := Set.inter_subset_inter_left M₁.E hX₂udc.subset_ground
            have a5' := (Set.inter_comm M₁.E M₂.E) ▸ a5
            have a6 : M₁.E ∩ M₂.E ⊆ X₁ := hp ▸ hpX₁
            have a7 : X₂ ∩ M₁.E ⊆ X₁ := a5'.trans a6

            have b : X₁ ∪ X₂ ∩ M₁.E = X₁ := Set.union_eq_self_of_subset_right a7

            have t3 : (C ∪ {p}) ∩ M₁.E = C ∩ M₁.E ∪ {p} ∩ M₁.E := Set.union_inter_distrib_right C {p} M₁.E
            have t4 : {p} ⊆ M₁.E := singleton_inter_subset_left hp
            have t5 : {p} ∩ M₁.E = {p} := (Set.left_eq_inter.mpr t4).symm
            rw [t5] at t3

            rw [←t3, a2, a3, a4, b]

          have hC₂eqX₂ : C ∩ M₂.E ∪ {p} = X₂ := by
            -- todo: clean up
            rw [hpX₁X₂] at hCX₁X₂
            have t1 : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congrFun (congrArg Union.union hCX₁X₂) {p}
            -- todo : use Set.diff_union_of_subset
            rw [Set.diff_union_self] at t1
            have t2 : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
            rw [Set.union_eq_left.mpr t2] at t1

            have a2 : (C ∪ {p}) ∩ M₂.E = (X₁ ∪ X₂) ∩ M₂.E := congrFun (congrArg Inter.inter t1) M₂.E
            have a3 : (X₁ ∪ X₂) ∩ M₂.E = X₁ ∩ M₂.E ∪ X₂ ∩ M₂.E := Set.union_inter_distrib_right X₁ X₂ M₂.E
            have a4 : X₂ ∩ M₂.E = X₂ := (Set.left_eq_inter.mpr hX₂udc.subset_ground).symm
            have a5 : X₁ ∩ M₂.E ⊆ M₁.E ∩ M₂.E := Set.inter_subset_inter_left M₂.E hX₁udc.subset_ground
            have a6 : M₁.E ∩ M₂.E ⊆ X₂ := hp ▸ hpX₂
            have a7 : X₁ ∩ M₂.E ⊆ X₂ := a5.trans a6

            have b : X₁ ∩ M₂.E ∪ X₂ = X₂ := Set.union_eq_self_of_subset_left a7

            have t3 : (C ∪ {p}) ∩ M₂.E = C ∩ M₂.E ∪ {p} ∩ M₂.E := Set.union_inter_distrib_right C {p} M₂.E
            have t4 : {p} ⊆ M₂.E := singleton_inter_subset_right hp
            have t5 : {p} ∩ M₂.E = {p} := (Set.left_eq_inter.mpr t4).symm
            rw [t5] at t3

            rw [←t3, a2, a3, a4, b]

          -- todo: make lemma in Sum2
          have hpncircM₁ : ¬(M₁.toMatroid.Circuit {p}) := by
            by_contra hpcircM₁
            have hpnloopM₁ := assumptions.inter_singleton_not_loop_M₁ hp
            exact hpnloopM₁ ((Matroid.Loop.iff_circuit M₁.toMatroid).mpr hpcircM₁)

          -- todo: make lemma in Sum2
          have hpncircM₂ : ¬(M₂.toMatroid.Circuit {p}) := by
            by_contra hpcircM₂
            have hpnloopM₂ := assumptions.inter_singleton_not_loop_M₂ hp
            exact hpnloopM₂ ((Matroid.Loop.iff_circuit M₂.toMatroid).mpr hpcircM₂)

          have hX₁p : ¬(X₁ ⊆ {p}) := by
            by_contra hX₁p
            have hpcircM₁ : M₁.toMatroid.Circuit {p} := ⟨
              hX₁dep.superset hX₁p (singleton_inter_subset_left hp),
              by
                intro Q hQ hQp
                simp only [Set.le_eq_subset] at hQp
                rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                exact le_of_eq_of_le hQp.symm (by rfl)
            ⟩
            exact hpncircM₁ hpcircM₁

          have hX₂p : ¬(X₂ ⊆ {p}) := by
            by_contra hX₂p
            have hpcircM₂ : M₂.toMatroid.Circuit {p} := ⟨
              hX₂dep.superset hX₂p (singleton_inter_subset_right hp),
              by
                intro Q hQ hQp
                simp only [Set.le_eq_subset] at hQp
                rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                exact le_of_eq_of_le hQp.symm (by rfl)
            ⟩
            exact hpncircM₂ hpcircM₂

          have hdisjX₁X₂dp : X₁ \ {p} ⫗ X₂ \ {p} := disjoint_of_singleton_inter_both_wo hpX₁X₂

          have hCinterM₁ : (C ∩ M₁.E).Nonempty := by
            rw [hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_inter_distrib_right]
            rw [←Set.diff_nonempty] at hX₁p
            have t1 : {p} ⊆ M₁.E := singleton_inter_subset_left hp
            have t2 : X₁ ⊆ M₁.E := hX₁dep.subset_ground
            have t3 : X₁ \ {p} ⊆ M₁.E := diff_subset_parent t2
            have t4 : X₁ \ {p} ∩ M₁.E = X₁ \ {p} := (Set.left_eq_inter.mpr t3).symm
            exact Set.Nonempty.inl (t4.symm ▸ hX₁p)

          have hCinterM₂ : (C ∩ M₂.E).Nonempty := by
            rw [hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_inter_distrib_right]
            rw [←Set.diff_nonempty] at hX₂p
            have t1 : {p} ⊆ M₂.E := singleton_inter_subset_right hp
            have t2 : X₂ ⊆ M₂.E := hX₂dep.subset_ground
            have t3 : X₂ \ {p} ⊆ M₂.E := diff_subset_parent t2
            have t4 : X₂ \ {p} ∩ M₂.E = X₂ \ {p} := (Set.left_eq_inter.mpr t3).symm
            exact Set.Nonempty.inr (t4.symm ▸ hX₂p)

          have hX₁circ : M₁.toMatroid.Circuit X₁ := by
            constructor
            · exact hX₁dep
            · intro Y₁ hY₁ hY₁X₁
              have ⟨Z₁, hZ₁, hZ₁Y₁⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hY₁
              have hZ₁X₁ : Z₁ ⊆ X₁ := hZ₁Y₁.trans hY₁X₁

              if hpZ₁ : {p} ⊆ Z₁ then
                have hpZ₁X₂ : Z₁ ∩ X₂ = {p} := by
                  apply Set.Subset.antisymm
                  exact (Set.inter_subset_inter_left X₂ hZ₁X₁).trans hpX₁X₂.subset
                  exact Set.subset_inter hpZ₁ hpX₂
                have hZ₁dp : (Z₁ \ {p}).Nonempty := by
                  by_contra! hZ₁dp
                  have hZ₁eqp : Z₁ = {p} := Set.Subset.antisymm (Set.diff_eq_empty.mp hZ₁dp) hpZ₁
                  exact hpncircM₁ (hZ₁eqp ▸ hZ₁)
                have hCC' : ((Z₁ ∪ X₂) \ (Z₁ ∩ X₂)) ⊆ C := by
                  rw [hpZ₁X₂, hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_diff_distrib]
                  exact Set.union_subset_union (Set.diff_subset_diff_left hZ₁X₁) (by rfl)
                have hZ₁sdX₂cf : CircuitForm M₁ M₂ ((Z₁ ∪ X₂) \ (Z₁ ∩ X₂)) := by
                  constructor
                  · rw [hpZ₁X₂, Set.union_diff_distrib]
                    exact Set.Nonempty.inl hZ₁dp
                  constructor
                  · exact hCC'.trans hCE
                  use Z₁, X₂
                  exact ⟨rfl, hZ₁.isUnionDisjointCircuits, hX₂udc⟩
                specialize hCmin hZ₁sdX₂cf hCC'
                have hX₁Z₁ : X₁ ⊆ Z₁ := by
                  rw [hpZ₁X₂, hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_diff_distrib] at hCmin
                  simp only [Set.le_eq_subset] at hCmin
                  have hX₁union := (Set.union_subset_iff.mp hCmin).left
                  have hX₁Z₁dp : X₁ \ {p} ⊆ Z₁ \ {p} := Disjoint.subset_left_of_subset_union hX₁union hdisjX₁X₂dp
                  rw [Set.diff_subset_iff, Set.union_comm, Set.diff_union_of_subset hpZ₁] at hX₁Z₁dp
                  exact hX₁Z₁dp
                exact hX₁Z₁.trans hZ₁Y₁
              else
                rw [Set.singleton_subset_iff] at hpZ₁
                have hZ₁p : Z₁ ⫗ {p} := Set.disjoint_singleton_right.mpr hpZ₁
                have hZ₁cf1 : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ Z₁ := ⟨hZ₁, hp ▸ hZ₁p⟩
                have hZ₁C : Z₁ ⊆ C := by
                  have hZ₁X₁X₂ : Z₁ ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_left hZ₁X₁ X₂
                  have hZ₁X₁X₂p : Z₁ ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hZ₁X₁X₂ hpZ₁
                  exact hCX₁X₂ ▸ hpX₁X₂ ▸ hZ₁X₁X₂p
                specialize hCmin hZ₁cf1.circuit_form hZ₁C
                have hCeqZ₁ := Set.Subset.antisymm hCmin hZ₁C
                exact False.elim (Set.not_nonempty_empty (hZ₁cf1.disjoint_M₂.inter_eq ▸ hCeqZ₁ ▸ hCinterM₂))

          have hX₂circ : M₂.toMatroid.Circuit X₂ := by
            constructor
            · exact hX₂dep
            · intro Y₂ hY₂ hY₂X₂
              have ⟨Z₂, hZ₂, hZ₂Y₂⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hY₂
              have hZ₂X₂ : Z₂ ⊆ X₂ := hZ₂Y₂.trans hY₂X₂

              if hpZ₂ : {p} ⊆ Z₂ then
                have hpX₁Z₂ : X₁ ∩ Z₂ = {p} := by
                  apply Set.Subset.antisymm
                  exact (Set.inter_subset_inter_right X₁ hZ₂X₂).trans hpX₁X₂.subset
                  exact Set.subset_inter hpX₁ hpZ₂
                have hZ₂dp : (Z₂ \ {p}).Nonempty := by
                  by_contra! hZ₂dp
                  have hZ₂eqp : Z₂ = {p} := Set.Subset.antisymm (Set.diff_eq_empty.mp hZ₂dp) hpZ₂
                  exact hpncircM₂ (hZ₂eqp ▸ hZ₂)
                have hCC' : ((X₁ ∪ Z₂) \ (X₁ ∩ Z₂)) ⊆ C := by
                  rw [hpX₁Z₂, hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_diff_distrib]
                  exact Set.union_subset_union (by rfl) (Set.diff_subset_diff_left hZ₂X₂)
                have hZ₂sdX₂cf : CircuitForm M₁ M₂ ((X₁ ∪ Z₂) \ (X₁ ∩ Z₂)) := by
                  constructor
                  · rw [hpX₁Z₂, Set.union_diff_distrib]
                    exact Set.Nonempty.inr hZ₂dp
                  constructor
                  · exact hCC'.trans hCE
                  use X₁, Z₂
                  exact ⟨rfl, hX₁udc, hZ₂.isUnionDisjointCircuits⟩
                specialize hCmin hZ₂sdX₂cf hCC'
                have hX₂Z₂ : X₂ ⊆ Z₂ := by
                  rw [hpX₁Z₂, hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_diff_distrib] at hCmin
                  simp only [Set.le_eq_subset] at hCmin
                  have hX₂union := (Set.union_subset_iff.mp hCmin).right
                  have hX₂Z₂dp : X₂ \ {p} ⊆ Z₂ \ {p} := Disjoint.subset_right_of_subset_union hX₂union hdisjX₁X₂dp.symm
                  rw [Set.diff_subset_iff, Set.union_comm, Set.diff_union_of_subset hpZ₂] at hX₂Z₂dp
                  exact hX₂Z₂dp
                exact hX₂Z₂.trans hZ₂Y₂
              else
                rw [Set.singleton_subset_iff] at hpZ₂
                have hZ₂p : Z₂ ⫗ {p} := Set.disjoint_singleton_right.mpr hpZ₂
                have hZ₂cf1 : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ Z₂ := ⟨hZ₂, hp ▸ hZ₂p⟩
                have hZ₂C : Z₂ ⊆ C := by
                  have hZ₂X₁X₂ : Z₂ ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hZ₂X₂ X₁
                  have hZ₂X₁X₂p : Z₂ ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hZ₂X₁X₂ hpZ₂
                  exact hCX₁X₂ ▸ hpX₁X₂ ▸ hZ₂X₁X₂p
                specialize hCmin hZ₂cf1.circuit_form hZ₂C
                have hCeqZ₂ := Set.Subset.antisymm hCmin hZ₂C
                exact False.elim (Set.not_nonempty_empty (hZ₂cf1.disjoint_M₁.inter_eq ▸ hCeqZ₂ ▸ hCinterM₁))

          exact ⟨hp ▸ hC₁eqX₁ ▸ hX₁circ, hp ▸ hC₂eqX₂ ▸ hX₂circ, hCE⟩

end Equivalence
