import Seymour.Basic
import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Representable


variable {α : Type}

section Definitions

/-- Binary matroid is vector matroid of matrix over `Z2`. -/
abbrev BinaryMatroid (α : Type) := VectorMatroid α Z2

/-- Matroid `M` is binary if it is representable over `Z2` -/
def Matroid.IsBinary [DecidableEq α] (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2

/-- `Matroid` is binary iff it can be constructed from a `BinaryMatroid`. -/
lemma Matroid.isBinary_iff [DecidableEq α] (M : Matroid α) : M.IsBinary ↔ ∃ B : BinaryMatroid α, B.toMatroid = M := by
  rfl

/-- Every `BinaryMatroid` is binary. -/
lemma BinaryMatroid.isBinary [DecidableEq α] (M : BinaryMatroid α) : M.toMatroid.IsBinary := by
  use M

/-- The dual of a binary matroid is binary -/
lemma BinaryMatroid.dual_isBinary [DecidableEq α] (M : BinaryMatroid α) : M.toMatroid✶.IsBinary :=
  have ⟨S, hS⟩ := M.dual_exists_standardRepr
  ⟨S.toVectorMatroid, hS.symm⟩

end Definitions
