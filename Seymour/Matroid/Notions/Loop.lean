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
      fun _ hM hMa => (Set.subset_singleton_iff_eq.→ hMa).casesOn
        (· ▸ hM |>.not_indep M.empty_indep |>.elim)
        (·.symm.subset)
      ⟩,
    fun ha => ⟨ha.left.right rfl, ha.dep⟩
  ⟩
