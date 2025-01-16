import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Notions.Loop


variable {α : Type}


/-- Coloop is a loop in the dual matroid. -/
def Matroid.Coloop (M : Matroid α) (a : α) : Prop :=
  M✶.Loop a

/-- An element is a coloop iff it belongs to no circuit. -/
lemma Matroid.coloop_iff_in_no_circuit (M : Matroid α) {a : α} :
    M.Coloop a ↔ a ∈ M.E ∧ ∀ C, M.Circuit C → a ∉ C := by
  constructor
  · intro ⟨haE, M_dual_Dep_a⟩
    refine ⟨haE, fun C hC haC => ?_⟩
    obtain ⟨B, hB, hCaB⟩ := (hC.indep_diff_singleton haC).exists_base_superset
    have haB := (Matroid.dual_dep_iff_forall.→ M_dual_Dep_a).left B hB
    have hMB : M.Dep B
    · rw [Matroid.dep_iff_has_circuit]
      exact ⟨C, hC, Set.diff_union_of_subset (Set.singleton_subset_iff.← haC) ▸ Set.union_subset hCaB
        (Set.singleton_subset_iff.← (Set.singleton_inter_nonempty.→ haB))⟩
    exact hMB.not_indep hB.indep
  · intro ⟨haE, haC⟩
    constructor
    · exact haE
    · rw [Matroid.dual_dep_iff_forall]
      constructor
      · intro B hB
        by_contra! haB
        obtain ⟨C', hC', hC'aB, haC'⟩ := hB.indep.circuit_of_insert_dep
          (hB.dep_of_insert (Set.singleton_inter_eq_empty.→ haB) haE)
        exact haC C' hC' haC'
      · rwa [Set.singleton_subset_iff]
