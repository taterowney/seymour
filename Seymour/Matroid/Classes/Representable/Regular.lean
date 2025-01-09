import Mathlib.Data.Matroid.Dual

import Seymour.Basic
import Seymour.Matroid.Classes.Representable.Basic
import Seymour.Matroid.Classes.Representable.Binary


variable {α : Type}

section Definitions

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.HasTotallyUnimodularSigning {X Y : Type} (A : Matrix X Y Z2) : Prop :=
  ∃ A' : Matrix X Y ℚ, -- signed version of `A`
    A'.IsTotallyUnimodular ∧ -- signed matrix is TU
    ∀ i : X, ∀ j : Y, if A i j = 0 then A' i j = 0 else A' i j = 1 ∨ A' i j = -1 -- `|A'| = |A|`

/-- Matroid `M` can be represented by a matrix that has a TU signing. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E Z2, A.HasTotallyUnimodularSigning ∧ M.IsRepresentedBy A

/-- Matroid `M` can be represented by a TU matrix. -/
def Matroid.HasTotallyUnimodularRepr (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E ℚ, A.IsTotallyUnimodular ∧ M.IsRepresentedBy A

end Definitions

section Characterizations

-- todo: see theorem 6.6.3 in Oxley

/-- Matroid is represented by a totally unimodular matrix `A` over `ℚ` iff it can be represented over any field `F`. -/
lemma Matroid.hasTotallyUnimodularRepr_iff {M : Matroid α} :
    M.HasTotallyUnimodularRepr ↔ ∀ F : Type, ∀ hF : Field F, M.IsRepresentableOver F := by
  sorry

/-- todo: descs -/
lemma Matroid.isRegular_iff_hasTotallyUnimodularRepr {M : Matroid α} :
    M.IsRegular ↔ M.HasTotallyUnimodularRepr := by
  sorry

lemma Matroid.isRegular_iff_isRepresentableOver_any_field {M : Matroid α} :
    M.IsRegular ↔ ∀ F : Type, ∀ hF : Field F, M.IsRepresentableOver F := by
  sorry

lemma Matroid.isRegular_iff_isRepresentableOver_Z2_and_Z3 {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ M.IsRepresentableOver Z3 := by
  sorry

lemma Matroid.isRegular_iff_isRepresentableOver_Z3 {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z3 ∧
      (∀ X : Type, ∀ A : Matrix X M.E Z3, M.IsRepresentedBy A → A.IsTotallyUnimodular) := by
  sorry

lemma Matroid.isRegular_iff_isRepresentableOver_Z2_and_gt2 {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ (∃ F : Type, ∃ hF : Field F, ringChar F > 2 ∧ M.IsRepresentableOver F) := by
  sorry

end Characterizations


section Corollaries

lemma Matroid.IsRegular.Z2_representation_regular {X : Type} {M : Matroid α} {A : Matrix X M.E Z2}
    (hM : M.IsRegular) (hMA : M.IsRepresentedBy A) :
    A.HasTotallyUnimodularSigning := by
  sorry

-- note: if M is regular, every minor of M is regular. however, matroid minors are not currently in mathlib

/-- todo: desc -/
def Matroid.isRegular_iff_dual_isRegular (M : Matroid α) :
    M.IsRegular ↔ M.dual.IsRegular := by
  sorry -- prop 2.2.22 in Oxley

-- todo: binary matroid is regular iff its standard representation matrix has a TU signing?

end Corollaries
