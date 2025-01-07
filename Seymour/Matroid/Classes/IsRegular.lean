import Mathlib.Data.Matroid.Dual
import Seymour.Basic
import Seymour.Matroid.Classes.IsRepresentable


section Definitions

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.IsRegular {X Y : Type} (A : Matrix X Y Z2) : Prop :=
  ∃ A' : Matrix X Y ℚ, -- signed version of `A`
    A'.IsTotallyUnimodular ∧ -- signed matrix is TU
    ∀ i j, if A i j = 0 then A' i j = 0 else A' i j = 1 ∨ A' i j = -1 -- `|A'| = |A|`

/-- Matroid `M` is regular iff it can be represented by a matrix that has a TU signing. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E Z2, A.IsRegular ∧ M.IsRepresentedBy A

end Definitions


section Characterizations

-- todo: see theorem 6.6.3 in Oxley

/-- Matroid `M` is TU representable iff it can be represented by a TU matrix. -/
def Matroid.IsTURepresentable {α : Type} (M : Matroid α) : Prop :=
  ∃ X : Type, ∃ A : Matrix X M.E ℚ, A.IsTotallyUnimodular ∧ M.IsRepresentedBy A

/-- If matroid is represented by a totally unimodular matrix `A` over `ℚ`, then it is represented by `A` over any field `F`. -/
lemma Matroid.IsTURepresentable.iff_representable_over_any_field {α : Type} {M : Matroid α} :
    M.IsTURepresentable ↔ ∀ F : Type, ∀ hF : Field F, M.IsRepresentableOver F := by
  sorry

/-- todo: descs -/
lemma Matroid.IsRegular.iff_TU_representable {α : Type} {M : Matroid α} :
    M.IsRegular ↔ M.IsTURepresentable := by
  sorry

lemma Matroid.IsRegular.iff_representable_over_any_field {α : Type} {M : Matroid α} :
    M.IsRegular ↔ ∀ F : Type, ∀ _ : Field F, M.IsRepresentableOver F := by
  rw [Matroid.IsRegular.iff_TU_representable, Matroid.IsTURepresentable.iff_representable_over_any_field]

lemma Matroid.IsRegular.iff_representable_over_Z2_Z3 {α : Type} {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ M.IsRepresentableOver Z3 := by
  sorry

lemma Matroid.IsRegular.iff_representable_over_Z3 {α : Type} {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z3 ∧
    (∀ X : Type, ∀ A : Matrix X M.E Z3, M.IsRepresentedBy A → A.IsTotallyUnimodular) := by
  sorry

lemma Matroid.IsRegular.iff_representable_over_Z2_F {α : Type} {M : Matroid α} : -- ??
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ (∃ F : Type, ∀ hF : Field F, ringChar F > 2 ∧ M.IsRepresentableOver F) := by
  sorry

end Characterizations


section Corollaries

lemma Matroid.IsRegular.Z2_representation_regular {α X : Type} {M : Matroid α} {A : Matrix X M.E Z2}
    (h : M.IsRepresentedBy A) : A.IsRegular := by
  sorry

-- note: if M is regular, every minor of M is regular. however, matroid minors are not currently in mathlib

/-- todo: desc -/
def Matroid.IsRegular.iff_dual_IsRegular {α : Type} (M : Matroid α) :
    M.IsRegular ↔ M.dual.IsRegular := by
  sorry -- prop 2.2.22 in Oxley

-- todo: binary matroid is regular iff its standard representation matrix has a TU signing?

end Corollaries

-- question: implement regular matroid constructor from binary matroid + regularity prop?
