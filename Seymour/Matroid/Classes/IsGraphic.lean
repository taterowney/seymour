import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid


/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column: 1x "+1", 1x "-1", and 0 elsewhere
def Matrix.IsGraphic {m n R : Type} [CommRing R] (A : Matrix m n R) : Prop :=
  ∀ y, ∃ x₁ x₂, (A x₁ y = 1) ∧ (A x₂ y = -1) ∧ (∀ x, x ≠ x₁ → x ≠ x₂ → A x y = 0)

/-- todo: desc -/
def VectorMatroid.IsGraphic {α R : Type} [CommRing R] (M : VectorMatroid α R) : Prop :=
  M.A.IsGraphic

/-- todo: desc -/
def Matroid.IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ R : Type, ∃ _ : CommRing R, ∃ X E : Set α, ∃ A : Matrix X E R,
  A.IsGraphic ∧ M = (⟨X, E, A⟩ : VectorMatroid α R).matroid

/-- todo: desc -/
def VectorMatroid.IsCographic {α R : Type} [CommRing R] (M : VectorMatroid α R) : Prop :=
  M.A.transpose.IsGraphic

/-- todo: desc -/
def Matroid.IsCographic {α : Type} (M : Matroid α) : Prop :=
  ∃ R : Type, ∃ _ : CommRing R, ∃ X E : Set α, ∃ A : Matrix X E R,
  A.transpose.IsGraphic ∧ M = (⟨X, E, A⟩ : VectorMatroid α R).matroid

/-- todo: desc -/
lemma Matroid.IsGraphic_iff {α : Type} (M : Matroid α) : M.IsGraphic ↔ M.dual.IsCographic := by sorry

/-- todo: desc -/
lemma Matroid.IsCoraphic_iff {α : Type} (M : Matroid α) : M.IsCographic ↔ M.dual.IsGraphic := by sorry

-- /-- todo: desc -/
-- def Matroid.IsPlanar {α : Type} (M : Matroid α) : Prop := M.IsGraphic ∧ M.IsCoraphic
