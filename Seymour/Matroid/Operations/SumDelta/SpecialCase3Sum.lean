import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.Matroid.Classes.Regular


variable {α : Type} [DecidableEq α]

section Definition

/-- Assumptions for Δ-sum in the 3-sum case. -/
structure ThreeSumAssumptions (M₁ M₂ : BinaryMatroid α) where
  /-- `M₁` is finite -/
  M₁_finite : M₁.E.Finite
  /-- `M₂` is finite -/
  M₂_finite : M₂.E.Finite
  /-- `M₁` contains at least 7 elements -/
  M₁_card : M₁.E.encard ≥ 7
  /-- `M₂` contains at least 7 elements -/
  M₂_card : M₂.E.encard ≥ 7
  -- `M₁` and `M₂` meet at a set `T` that is a triangle in both
  Triangle_inter : (M₁.E ∩ M₂.E).encard = 3
  Triangle_in_M₁ : M₁.toMatroid.Circuit (M₁.E ∩ M₂.E)
  Triangle_in_M₂ : M₂.toMatroid.Circuit (M₁.E ∩ M₂.E)
  /-- Neither `M₁` nor `M₂` has a cocircuit contained in `T` -/
  Triangle_no_cocircuit : ∀ T' ⊆ M₁.E ∩ M₂.E, ¬(M₁.toMatroid✶.Circuit T') ∧ ¬(M₂.toMatroid✶.Circuit T')

set_option linter.unusedVariables false in
/-- The main way of creating a 3-sum of binary matroids. -/
def ThreeSumAssumptions.build3sum {M₁ M₂ : BinaryMatroid α} (assumptions : ThreeSumAssumptions M₁ M₂) : Matroid α :=
  BinaryMatroid.DeltaSum.toMatroid M₁ M₂

end Definition


section Properties

-- todo: probably need properties of cocircuits
-- todo: Lemma 9.3.3 from Oxley
-- todo: Lemma 9.3.4 from Oxley

end Properties


section Representation

-- todo: if M is representable and contains a triangle, then it can be represented by (8.5.2.left) from Truemper
-- optional: if M is representable and contains a triangle, then it can be represented by (8.5.2.right) from Truemper
-- todo: if M is representable and contains a triangle, then it can be represented by (8.5.3) from Truemper
-- todo: compose (8.5.2) and (8.5.3) into (8.5.1) from Truemper
-- todo: etc, see Sum2

end Representation


section Regularity

/-- Any 3-sum of regular matroids is regular. -/
lemma ThreeSumAssumptions.composition_isRegular {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (regularity₁ : M₁.toMatroid.IsRegular) (regularity₂ : M₂.toMatroid.IsRegular) :
    assumptions.build3sum.IsRegular :=
  sorry

/-- If a regular matroid is a 3-sum of binary matroids, the left summand is regular. -/
lemma ThreeSumAssumptions.decomposition_isRegular_left {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (regularity : assumptions.build3sum.IsRegular) :
    M₁.toMatroid.IsRegular :=
  sorry

/-- If a regular matroid is a 3-sum of binary matroids, the right summand is regular. -/
lemma ThreeSumAssumptions.decomposition_isRegular_right {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (regularity : assumptions.build3sum.IsRegular) :
    M₂.toMatroid.IsRegular :=
  sorry

/-- If a regular matroid is a 3-sum of binary matroids, both summands are regular. -/
lemma ThreeSumAssumptions.decomposition_isRegular_both {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (regularity : assumptions.build3sum.IsRegular) :
    M₁.toMatroid.IsRegular ∧ M₂.toMatroid.IsRegular :=
  ⟨assumptions.decomposition_isRegular_left regularity, assumptions.decomposition_isRegular_right regularity⟩

end Regularity
