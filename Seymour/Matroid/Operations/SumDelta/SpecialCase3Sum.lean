import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Operations.SumDelta.Basic


/-- Assumptions for Δ-sum  -/
structure BinaryMatroid.DeltaSum.ThreeSumAssumptions {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁_finite : M₁.E.Finite
  hM₂_finite : M₂.E.Finite
  /-- `M₁` and `M₂` contain at least 7 elements -/
  hM₁_card : M₁.E.encard ≥ 7
  hM₂_card : M₂.E.encard ≥ 7
  /-- `M₁` and `M₂` meet at a set `T` that is a triangle in both -/
  hT : (M₁.E ∩ M₂.E).encard = 3
  hTM₁ : M₁.toMatroid.Circuit (M₁.E ∩ M₂.E)
  hTM₂ : M₂.toMatroid.Circuit (M₁.E ∩ M₂.E)
  /-- Neither `M₁` nor `M₂` has a cocircuit contained in `T` -/
  hT_no_sub_cocircuit : ∀ T' ⊆ M₁.E ∩ M₂.E, ¬(M₁.toMatroid.dual.Circuit T') ∧ ¬(M₂.toMatroid.dual.Circuit T')

-- todo: probably need properties of cocircuits
-- todo: Lemma 9.3.3 from Oxley
-- todo: Lemma 9.3.4 from Oxley
