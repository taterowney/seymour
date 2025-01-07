import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Restrict

import Seymour.Matroid.Operations.SumDelta.Basic


variable {α : Type} [DecidableEq α]

/-- Sets that are circuits in `M₁` or `M₂` -/
def BinaryMatroid.JointCircuits (M₁ M₂ : BinaryMatroid α) :=
  { C : Set α // M₁.toMatroid.Circuit C ∨ M₂.toMatroid.Circuit C }

/-- Matrix whose rows are incidence vectors of all circuits in `M₁` and `M₂` -/
def BinaryMatroid.JointCircuitMatrix [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)] (M₁ M₂ : BinaryMatroid α) :
    Matrix { C : Set α // M₁.toMatroid.Circuit C ∨ M₂.toMatroid.Circuit C } (M₁.E ∪ M₂.E : Set α) Z2 :=
  Matrix.of fun C e => (if (e : α) ∈ (C : Set α) then 1 else 0)
  -- todo: use `M₁.JointCircuitRows M₂` as first dimension of matrix;
  -- compiler doesn't "see through" definition and complains about form mismatch

/-- If `A` is a matrix over `Z2` whose columns are indexed by the elements of `M₁.E ∪ M₂.E` and
    whose rows consist of the incidence vectors of all the circuits of `M₁` and all the circuits of `M₂`
    then `M₁ Δ M₂ = (M[A])* \ (M₁.E ∩ M₂.E)` -/
lemma BinaryMatroid.DeltaSum.matrix_eq [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)] (M₁ M₂ : BinaryMatroid α) :
    BinaryMatroid.DeltaSum.matroid M₁ M₂ =
    (M₁.JointCircuitMatrix M₂).toVectorMatroid.toMatroid.dual.restrict (BinaryMatroid.DeltaSum.E M₁ M₂) := by
  sorry -- see Lemma 9.3.1 in Oxley
