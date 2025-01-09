import Mathlib.Data.Matroid.Basic
import Seymour.Matroid.Notions.Circuit


variable {α : Type}

/-- Loop is an element of the ground set that is not independent when viewed as a singleton set. -/
def Matroid.Loop (M : Matroid α) (a : α) : Prop :=
  a ∈ M.E ∧ M.Dep {a}

/-- An element is a loop iff its singleton set is a circuit. -/
lemma Matroid.Loop.iff_circuit (M : Matroid α) {a : α} :
    M.Loop a ↔ M.Circuit {a} :=
  ⟨
    fun ha => ⟨
      ha.right,
      fun T dT hTa => by cases Set.subset_singleton_iff_eq.mp hTa with
        | inl hT => exact False.elim ((Matroid.Dep.not_indep (hT ▸ dT)) M.empty_indep)
        | inr hT => exact le_of_eq_of_le hT.symm Set.Subset.rfl
      ⟩,
    fun ha => ⟨ha.left.right rfl, Matroid.Circuit.dep M ha⟩
  ⟩
