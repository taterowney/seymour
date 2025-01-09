import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Regular


section IsGraphic

/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0

/-- todo: desc -/
def Matroid.IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E ℚ, M.IsRepresentedBy A ∧ A.IsGraphic

/-- todo: desc -/
lemma Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic {α X : Type} {M : Matroid α} {A : Matrix X M.E ℚ}
    (hMA : M.IsRepresentedBy A) (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  sorry

/-- todo: desc -/
lemma Matroid.IsGraphic.isRegular {α : Type} {M : Matroid α} (hM : M.IsGraphic) : M.IsRegular := by
  rw [Matroid.isRegular_iff_hasTuRepr]
  obtain ⟨X, A, hMA, hA⟩ := hM
  exact ⟨X, A, hMA.isTotallyUnimodular_of_isGraphic hA, hMA⟩

end IsGraphic


section IsCographic

/-- todo: desc -/
def Matroid.IsCographic {α : Type} (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- todo: desc -/
lemma Matroid.IsCographic.is_regular {α : Type} {M : Matroid α} (hM : M.IsCographic) : M.IsRegular :=
  M.isRegular_iff_dual_isRegular.mpr hM.isRegular

end IsCographic
