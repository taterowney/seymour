import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.IsRepresentable
import Seymour.Matroid.Classes.IsRegular


section IsGraphic

/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column: 1x "+1", 1x "-1", and 0 elsewhere
-- todo: change R to Z3 or ℚ?
def Matrix.IsGraphic {m n R : Type} [CommRing R] (A : Matrix m n R) : Prop :=
  ∀ y, ∃ x₁ x₂, (A x₁ y = 1) ∧ (A x₂ y = -1) ∧ (∀ x, x ≠ x₁ → x ≠ x₂ → A x y = 0)

/-- todo: desc -/
def Matroid.IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ X R : Type, ∀ hR : CommRing R, ∃ A : Matrix X M.E R, M.IsRepresentedBy A ∧ A.IsGraphic

-- todo: if M is graphic, M is regular


section IsCographic

/-- todo: desc -/
def VectorMatroid.IsCographic {α R : Type} [CommRing R] (M : VectorMatroid α R) : Prop :=
  M.matroid.dual.IsGraphic

/-- todo: desc -/
def Matroid.IsCographic {α : Type} (M : Matroid α) : Prop :=
  M.dual.IsGraphic

-- todo: if M is cographic, M is regular

-- /-- todo: desc -/
-- def Matroid.IsPlanar {α : Type} (M : Matroid α) : Prop := M.IsGraphic ∧ M.IsCoraphic
