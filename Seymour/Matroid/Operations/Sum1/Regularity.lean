import Seymour.Matroid.Operations.Sum1.Basic
import Seymour.Matroid.Classes.Regular


variable {α : Type} [DecidableEq α] {M₁ M₂ : Matroid α}

section Composition

-- lemma Matroid.disjointSum.ofRepresented_repr {R X₁ X₂ : Type} {A₁ : Matrix X₁ M₁.E R} {A₂ : Matrix X₂ M₂.E R}
--     [Ring R] [∀ a, Decidable (a ∈ M₁.E)] [∀ a, Decidable (a ∈ M₂.E)]
--     (hE : M₁.E ⫗ M₂.E) (hA₁ : M₁.IsRepresentedBy A₁) (hA₂ : M₂.IsRepresentedBy A₂) :
--     hE.build1sum.IsRepresentedBy
--       ((Matrix.fromBlocksSetUnion A₁ 0 0 A₂).castColsSetUnion Matroid.disjointSum_ground_eq.symm) := by
--   sorry

end Composition


section Decomposition

/-- todo: desc-/
lemma Matroid.oneSum.ofRepr₁ {X R : Type} [Ring R] (hE : M₁.E ⫗ M₂.E) {A : Matrix X hE.build1sum.E R}
    (hA : hE.build1sum.IsRepresentedBy A) :
    ∃ X₁ : Type, ∃ A₁ : Matrix X₁ M₁.E R, M₁.IsRepresentedBy A₁ :=
  sorry

/-- todo: desc-/
lemma Matroid.oneSum.ofRepr₂ {X R : Type} [Ring R] (hE : M₁.E ⫗ M₂.E) {A : Matrix X hE.build1sum.E R}
    (hA : hE.build1sum.IsRepresentedBy A) :
    ∃ X₂ : Type, ∃ A₂ : Matrix X₂ M₂.E R, M₂.IsRepresentedBy A₂ :=
  sorry

/-- If a regular matroid is a 1-sum of binary matroids, the left summand is regular. -/
lemma Disjoint.decomposition_isRegular_left (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₁.IsRegular := by
  sorry

/-- If a regular matroid is a 1-sum of binary matroids, the right summand is regular. -/
lemma Disjoint.decomposition_isRegular_right (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₂.IsRegular := by
  sorry

/-- If a regular matroid is a 1-sum of binary matroids, both summand matroids are regular. -/
lemma Disjoint.decomposition_isRegular_both (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₁.IsRegular ∧ M₂.IsRegular :=
  ⟨hE.decomposition_isRegular_left regularity, hE.decomposition_isRegular_right regularity⟩

end Decomposition
