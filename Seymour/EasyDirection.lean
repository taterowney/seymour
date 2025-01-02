import Mathlib.Data.Matroid.Map

import Seymour.Matroid.Classes.IsRegular
import Seymour.Matroid.Classes.IsGraphic
import Seymour.Matroid.Classes.IsCographic
import Seymour.Matroid.Constructors.ConcreteInstances
import Seymour.Matroid.Operations.SumDelta

/-!
This file states the "easy" (composition) direction of the Seymour decomposition theorem.
-/

theorem easySeymour.Sum1 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (hM₁M₂ : Disjoint M₁.E M₂.E) :
    (Matroid.disjointSum M₁.matroid M₂.matroid hM₁M₂).IsRegular := by
  sorry

theorem easySeymour.Sum2 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α} {p : α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) :
    (Matroid.TwoSum.matroid Assumptions).IsRegular := by
  sorry

theorem easySeymour.Sum3 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (Assumptions : DeltaSum.ThreeSumAssumptions M₁ M₂) :
    (DeltaSum.matroid M₁ M₂).IsRegular := by
  sorry
