import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.Matroid.Classes.Regular


variable {α : Type} [DecidableEq α]

section Definition

/-- Assumptions for Δ-sum  -/
structure ThreeSumAssumptions (M₁ M₂ : BinaryMatroid α) where
  /-- `M₁` is finite -/
  hM₁_finite : M₁.E.Finite
  /-- `M₂` is finite -/
  hM₂_finite : M₂.E.Finite
  /-- `M₁` contains at least 7 elements -/
  hM₁_card : M₁.E.encard ≥ 7
  /-- `M₂` contains at least 7 elements -/
  hM₂_card : M₂.E.encard ≥ 7
  -- `M₁` and `M₂` meet at a set `T` that is a triangle in both
  hT : (M₁.E ∩ M₂.E).encard = 3
  hTM₁ : M₁.toMatroid.Circuit (M₁.E ∩ M₂.E)
  hTM₂ : M₂.toMatroid.Circuit (M₁.E ∩ M₂.E)
  /-- Neither `M₁` nor `M₂` has a cocircuit contained in `T` -/
  hT_no_sub_cocircuit : ∀ T' ⊆ M₁.E ∩ M₂.E, ¬(M₁.toMatroid✶.Circuit T') ∧ ¬(M₂.toMatroid✶.Circuit T')

/-- todo: desc -/
def ThreeSumAssumptions.build3sum {M₁ M₂ : BinaryMatroid α} (assumptions : ThreeSumAssumptions M₁ M₂) : Matroid α :=
  BinaryMatroid.DeltaSum.matroid M₁ M₂

/-- 3-sum of two matroids -/
def BinaryMatroid.threeSum (M₁ M₂ : BinaryMatroid α) (assumptions : ThreeSumAssumptions M₁ M₂) : Matroid α :=
  assumptions.build3sum

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

/-- todo: desc -/
lemma BinaryMatroid.ThreeSum.IsRegular_of_IsRegular {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (hM₁ : M₁.toMatroid.IsRegular) (hM₂ : M₂.toMatroid.IsRegular) :
    (M₁.threeSum M₂ assumptions).IsRegular :=
  sorry

/-- todo: desc -/
lemma BinaryMatroid.ThreeSum.of_IsRegular₁ {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (h : (M₁.threeSum M₂ assumptions).IsRegular) :
    M₁.toMatroid.IsRegular :=
  sorry

/-- todo: desc -/
lemma BinaryMatroid.ThreeSum.of_IsRegular₂ {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (h : (M₁.threeSum M₂ assumptions).IsRegular) :
    M₂.toMatroid.IsRegular :=
  sorry

/-- todo: desc -/
lemma BinaryMatroid.ThreeSum.of_IsRegular_both {M₁ M₂ : BinaryMatroid α}
    (assumptions : ThreeSumAssumptions M₁ M₂) (h : (M₁.threeSum M₂ assumptions).IsRegular) :
    M₁.toMatroid.IsRegular ∧ M₂.toMatroid.IsRegular :=
  ⟨BinaryMatroid.ThreeSum.of_IsRegular₁ assumptions h, BinaryMatroid.ThreeSum.of_IsRegular₂ assumptions h⟩

end Regularity
