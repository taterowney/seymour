import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Notions.Loop


variable {α : Type}

/-- Coloop is a loop in the dual matroid. -/
def Matroid.Coloop (M : Matroid α) (a : α) : Prop :=
  M.dual.Loop a

/-- An element is a coloop iff it belongs to no circuit. -/
lemma Matroid.Coloop.iff_in_no_circuit (M : Matroid α) {a : α} :
    M.Coloop a ↔ a ∈ M.E ∧ ∀ C, M.Circuit C → a ∉ C := by
  constructor
  · intro ⟨haE, hanIndep⟩
    constructor
    · exact haE
    · intro C hC haC
      have hCmaIndep : M.Indep (C \ {a}) := Matroid.Circuit.indep_diff_singleton hC haC
      apply Matroid.Indep.exists_base_superset at hCmaIndep
      obtain ⟨B, hB, hCmaB⟩ := hCmaIndep
      have haB := (Matroid.dual_dep_iff_forall.mp hanIndep).1
      specialize haB B hB
      have hBdep : M.Dep B  := by
        rw [Matroid.Circuit.dep_iff_has_circuit]
        use C
        have hCsubB : C \ {a} ∪ {a} ⊆ B := Set.union_subset hCmaB
          (Set.singleton_subset_iff.mpr (Set.singleton_inter_nonempty.mp haB))
        have hCeq : C \ {a} ∪ {a} = C := Set.diff_union_of_subset (Set.singleton_subset_iff.mpr haC)
        exact ⟨hC, hCeq ▸ hCsubB⟩
      exact Matroid.Dep.not_indep hBdep (Matroid.Base.indep hB)
  · intro ⟨haE, haC⟩
    constructor
    · exact haE
    · rw [Matroid.dual_dep_iff_forall]
      constructor
      · intro B hB
        by_contra haB
        push_neg at haB
        have haBdep : M.Dep (insert a B) := Base.dep_of_insert hB (Set.singleton_inter_eq_empty.mp haB) haE
        obtain ⟨C', hC', hC'aB, haC'⟩ := Matroid.Circuit.indep_ext_dep_has_circuit_w_ext (Matroid.Base.indep hB) haBdep
        exact haC C' hC' haC'
      · exact Set.singleton_subset_iff.mpr haE
