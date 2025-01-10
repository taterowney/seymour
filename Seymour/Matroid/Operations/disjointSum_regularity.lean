import Mathlib.Data.Matroid.Sum

import Seymour.ForMathlib.MatrixManip
import Seymour.Matroid.Classes.Regular


variable {α : Type}
variable [∀ T : Set α, ∀ a, Decidable (a ∈ T)]
variable {M₁ M₂ : Matroid α}

section Composition

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepresented_repr {R : Type} [Ring R] {X₁ X₂ : Set α} {A₁ : Matrix X₁ M₁.E R} {A₂ : Matrix X₂ M₂.E R}
    [∀ a, Decidable (a ∈ X₁)] [∀ a, Decidable (a ∈ X₂)] [∀ a, Decidable (a ∈ M₁.E)] [∀ a, Decidable (a ∈ M₂.E)]
    (hM₁M₂ : M₁.E ⫗ M₂.E) (hA₁ : M₁.IsRepresentedBy A₁) (hA₂ : M₂.IsRepresentedBy A₂) :
    (M₁.disjointSum M₂ hM₁M₂).IsRepresentedBy
      ((Matrix.setUnion_fromBlocks A₁ 0 0 A₂).setUnion_castCols (Matroid.disjointSum_ground_eq.symm)) :=
  sorry
-- Could we make it work with `{X₁ X₂ : Type}` instead?

/-- todo: desc-/
lemma Matroid.disjointSum.IsRegular_of_IsRegular (hM₁M₂ : M₁.E ⫗ M₂.E)
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) : (M₁.disjointSum M₂ hM₁M₂).IsRegular := by
  sorry
  -- todo: implement following this outline:
  -- * fix any field F
  -- * take matrix representations A₁ and A₂ of M₁ and M₂ over F
  -- * M₁ ⊕₁ M₂ can be represented by block-diagonal matrix with A₁ and A₂ and on the diagonal
  -- * thus M₁ ⊕₁ M₂ is representable over any field, so it is regular

end Composition


section Decomposition

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepr₁ {X R : Type} [Ring R] (hM₁M₂ : M₁.E ⫗ M₂.E) {A : Matrix X (M₁.disjointSum M₂ hM₁M₂).E R}
    (hA : (M₁.disjointSum M₂ hM₁M₂).IsRepresentedBy A) :
    ∃ X₁, ∃ A₁ : Matrix X₁ M₁.E R, M₁.IsRepresentedBy A₁ :=
  sorry

/-- todo: desc-/
lemma Matroid.disjointSum.ofRepr₂ {X R : Type} [Ring R] (hM₁M₂ : M₁.E ⫗ M₂.E) {A : Matrix X (M₁.disjointSum M₂ hM₁M₂).E R}
    (hA : (M₁.disjointSum M₂ hM₁M₂).IsRepresentedBy A) :
    ∃ X₂, ∃ A₂ : Matrix X₂ M₂.E R, M₂.IsRepresentedBy A₂ :=
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
