import Mathlib.Data.Matroid.Dual

import Seymour.Basic
import Seymour.Matroid.Classes.Representable
import Seymour.Matroid.Classes.Binary


variable {α : Type}

section TUSigning

/-- Matrix `S` is a TU signing of `U` if `S` is TU and its entries are the same as in `U` up to signs. -/
def Matrix.IsTUSigningOf {X Y : Type} (S : Matrix X Y ℚ) (U : Matrix X Y Z2) : Prop :=
  S.IsTotallyUnimodular ∧ ∀ i j, |S i j| = (U i j).val

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.HasTUSigning {X Y : Type} (A : Matrix X Y Z2) : Prop :=
  ∃ A' : Matrix X Y ℚ, A'.IsTUSigningOf A

end TUSigning


section Definitions

/-- Matroid `M` is regular iff it can be represented over any field -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∀ F : Type, ∀ _hF : Field F, M.IsRepresentableOver F

/-- Matroid `M` that can be represented by a matrix over `Z2` that has a TU signing -/
def Matroid.HasTUSigning {α : Type} (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E Z2, A.HasTUSigning ∧ M.IsRepresentedBy A

/-- Matroid `M` that can be represented by a TU matrix -/
def Matroid.HasTURepr (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E ℚ, A.IsTotallyUnimodular ∧ M.IsRepresentedBy A

/-- Matroid `M` that can be represented over `Z2` and `Z3` -/
def Matroid.HasZ2Z3Repr (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2 ∧ M.IsRepresentableOver Z3

end Definitions


section EquivalenceOfDefinitions

-- todo: prove equivalence of definitions above; see theorem 6.6.3 in Oxley

lemma Matroid.IsRegular_iff_HasTURepr {M : Matroid α} : M.IsRegular ↔ M.HasTURepr := by sorry

end EquivalenceOfDefinitions


section Corollaries

-- note: if M is regular, every minor of M is regular. however, matroid minors are not currently in mathlib

lemma Matroid.IsRegular.Z2_repr_HasTuSigning {X : Type} {M : Matroid α} {A : Matrix X M.E Z2}
    (hM : M.IsRegular) (hMA : M.IsRepresentedBy A) :
    A.HasTUSigning := by
  sorry

/-- todo: desc -/
def Matroid.isRegular_iff_dual_isRegular (M : Matroid α) :
    M.IsRegular ↔ M✶.IsRegular := by
  sorry -- prop 2.2.22 in Oxley

-- todo: binary matroid is regular iff its standard representation matrix has a TU signing

end Corollaries
