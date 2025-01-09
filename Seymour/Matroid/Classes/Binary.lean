import Seymour.Basic
import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Representable


variable {α : Type}

section Definitions

/-- Binary matroid is vector matroid of matrix over `Z2`. -/
abbrev BinaryMatroid (α : Type) := VectorMatroid α Z2

/-- Matroid `M` is binary if it is representable over `Z2` -/
def Matroid.IsBinary (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2

/-- Every `BinaryMatroid` is representable over Z2 -/
lemma BinaryMatroid.IsBinary (M : BinaryMatroid α) : M.toMatroid.IsBinary := by use M

/-- The dual of a binary matroid is binary -/
lemma BinaryMatroid.dual_isBinary [DecidableEq α] (M : BinaryMatroid α) : M.toMatroid✶.IsBinary :=
  have ⟨S, hS⟩ := M.dual_exists_standardRepr
  ⟨S.toVectorMatroid, hS.symm⟩

end Definitions
