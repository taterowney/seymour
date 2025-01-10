import Seymour.Matroid.Classes.Regular
import Seymour.Matroid.Operations.SumDelta.SpecialCase1Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase2Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase3Sum
import Seymour.Matroid.Operations.disjointSum_regularity

/-!
This file states the "easy" (composition) direction of the Seymour decomposition theorem.
-/

variable {α : Type} [DecidableEq α]

theorem easySeymour.Sum1 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (hMM : M₁.E ⫗ M₂.E) :
    (Matroid.disjointSum M₁ M₂ hMM).IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, hM₁⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, hM₂⟩ := hM₂ F hF
  --dsimp only [VectorMatroid.toMatroid_E] at hMM
  --use ⟨X₁ ⊕ X₂, E₁ ∪ E₂, Matrix.fromBlocks A₁ 0 0 A₂⟩ -- TODO change the 2nd argument of `VectorMatroid` to `Type`
  --use ((Matrix.setUnion_fromBlocks A₁ 0 0 A₂).setUnion_castCols (Matroid.disjointSum_ground_eq.symm))
  --specialize hM₁ F hF
  --specialize hM₂ F hF
  --unfold Matroid.IsRepresentableOver at hM₁
  have hE₁ : M₁.E = E₁ := by rw [←hM₁, VectorMatroid.toMatroid_E]
  have hE₂ : M₂.E = E₂ := by rw [←hM₂, VectorMatroid.toMatroid_E]
  -- `HEq` hell ahead
  have hMA₁ : M₁.IsRepresentedBy (hE₁ ▸ A₁) := hE₁ ▸ hM₁.symm
  have hMA₂ : M₂.IsRepresentedBy (hE₂ ▸ A₂) := hE₂ ▸ hM₂.symm
  --have := Matroid.disjointSum.ofRepresented_repr hMM hMA₁ hMA₂
  sorry

theorem easySeymour.Sum2 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular)
    (assumptions : TwoSumAssumptions M₁ M₂) :
    assumptions.build2sum.IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, rfl⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, rfl⟩ := hM₂ F hF
  sorry

theorem easySeymour.Sum3 [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁ : M₁.toMatroid.IsRegular) (hM₂ : M₂.toMatroid.IsRegular)
    (assumptions : ThreeSumAssumptions M₁ M₂) :
    (BinaryMatroid.DeltaSum.matroid M₁ M₂).IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, hA₁⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, hA₂⟩ := hM₂ F hF
  sorry
