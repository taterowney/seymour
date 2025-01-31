import Mathlib.Data.Matroid.Sum

import Seymour.Matroid.Classes.Regular


variable {α : Type} [DecidableEq α] {M₁ M₂ : Matroid α}

section Composition

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepresented_repr {R X₁ X₂ : Type} {A₁ : Matrix X₁ M₁.E R} {A₂ : Matrix X₂ M₂.E R}
    [Ring R] [∀ a, Decidable (a ∈ M₁.E)] [∀ a, Decidable (a ∈ M₂.E)]
    (hE : M₁.E ⫗ M₂.E) (hA₁ : M₁.IsRepresentedBy A₁) (hA₂ : M₂.IsRepresentedBy A₂) :
    (M₁.disjointSum M₂ hE).IsRepresentedBy
      ((Matrix.fromBlocksSetUnion A₁ 0 0 A₂).castColsSetUnion Matroid.disjointSum_ground_eq.symm) := by
  sorry

end Composition


section Decomposition

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepr₁ {X R : Type} [Ring R] (hM₁M₂ : M₁.E ⫗ M₂.E) {A : Matrix X (M₁.disjointSum M₂ hM₁M₂).E R}
    (hA : (M₁.disjointSum M₂ hM₁M₂).IsRepresentedBy A) :
    ∃ X₁ : Type, ∃ A₁ : Matrix X₁ M₁.E R, M₁.IsRepresentedBy A₁ :=
  sorry

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepr₂ {X R : Type} [Ring R] (hM₁M₂ : M₁.E ⫗ M₂.E) {A : Matrix X (M₁.disjointSum M₂ hM₁M₂).E R}
    (hA : (M₁.disjointSum M₂ hM₁M₂).IsRepresentedBy A) :
    ∃ X₂ : Type, ∃ A₂ : Matrix X₂ M₂.E R, M₂.IsRepresentedBy A₂ :=
  sorry

/-- todo: desc-/
lemma Matroid.disjointSum.of_IsRegular₁ (hM₁M₂ : M₁.E ⫗ M₂.E) (hM : (M₁.disjointSum M₂ hM₁M₂).IsRegular) :
    M₁.IsRegular := by
  sorry

/-- todo: desc-/
lemma Matroid.disjointSum.of_IsRegular₂ (hM₁M₂ : M₁.E ⫗ M₂.E) (hM : (M₁.disjointSum M₂ hM₁M₂).IsRegular) :
    M₂.IsRegular := by
  sorry

/-- todo: desc-/
lemma Matroid.disjointSum.of_IsRegular_IsRegular_both (hM₁M₂ : M₁.E ⫗ M₂.E) (hM : (M₁.disjointSum M₂ hM₁M₂).IsRegular) :
    M₁.IsRegular ∧ M₂.IsRegular :=
  ⟨Matroid.disjointSum.of_IsRegular₁ hM₁M₂ hM, Matroid.disjointSum.of_IsRegular₂ hM₁M₂ hM⟩

end Decomposition
