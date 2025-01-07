import Seymour.Matroid.Classes.IsRegular
import Seymour.Matroid.Operations.SumDelta.SpecialCase1Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase2Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase3Sum

/-!
This file states the "easy" (composition) direction of the Seymour decomposition theorem.
-/

variable {α : Type}

theorem easySeymour.Sum1 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (hMM : Disjoint M₁.E M₂.E) :
    (Matroid.disjointSum M₁ M₂ hMM).IsRegular := by
  sorry

theorem easySeymour.Sum2 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular)
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂) :
    (Matroid.TwoSum.matroid Assumptions).IsRegular := by
  sorry

theorem easySeymour.Sum3 [DecidableEq α] {M₁ M₂ : BinaryMatroid α} (hM₁ : M₁.toMatroid.IsRegular) (hM₂ : M₂.toMatroid.IsRegular)
    (Assumptions : BinaryMatroid.DeltaSum.ThreeSumAssumptions M₁ M₂) :
    (BinaryMatroid.DeltaSum.matroid M₁ M₂).IsRegular := by
  sorry
